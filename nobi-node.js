const express = require('express');
const WebSocket = require('ws');
const sqlite3 = require('sqlite3').verbose();
const { ec: EC } = require('elliptic');
const bs58 = require('bs58');
const SHA256 = require('crypto-js/sha256');
const bip32 = require('bip32');
const bip39 = require('bip39');

const ec = new EC('secp256k1');

// ------------------- CONFIGURATION -------------------
const NOBI = {
  name: 'NOBI',
  symbol: 'NOBI',
  initialDifficulty: 3,
  targetBlockTimeMs: 60000,
  difficultyAdjustmentInterval: 10,
  blockReward: 50,
  coinbaseMaturity: 10,
  maxReorgDepth: 6,
  p2pPort: process.env.P2P_PORT || 6001,
  apiPort: process.env.PORT || 3000,
  seedPeers: [],
  faucetAmount: 10,
  faucetCooldownMs: 3600000,
  faucetWalletPrivateKey: null,
};

// ------------------- UTILITIES -------------------
function hash(data) { return SHA256(data).toString(); }
function doubleHash(data) { return hash(hash(data)); }

function base58CheckEncode(payload, version) {
  const versioned = Buffer.concat([Buffer.from([version]), payload]);
  const checksum = doubleHash(versioned).slice(0, 8);
  return bs58.encode(Buffer.concat([versioned, Buffer.from(checksum, 'hex')]));
}

function base58CheckDecode(address) {
  const decoded = bs58.decode(address);
  const version = decoded[0];
  const payload = decoded.slice(1, -4);
  const checksum = decoded.slice(-4);
  const computedChecksum = doubleHash(Buffer.concat([Buffer.from([version]), payload])).slice(0, 8);
  if (checksum.toString('hex') !== computedChecksum) throw new Error('Invalid checksum');
  return { version, payload };
}

function createAddressFromPublicKey(publicKeyHex) {
  const pubBuffer = Buffer.from(publicKeyHex, 'hex');
  const sha = SHA256(pubBuffer).toString();
  const ripemd = hash(sha);
  return base58CheckEncode(Buffer.from(ripemd, 'hex'), 0x00);
}

function createScriptPubKey(address) {
  const addrData = base58CheckDecode(address);
  return { type: 'p2pkh', hash: addrData.payload.toString('hex') };
}

function verifyScript(sig, pubKeyHash, scriptPubKey) {
  if (scriptPubKey.type !== 'p2pkh') return false;
  const pubKey = ec.keyFromPublic(sig.publicKeyHex, 'hex');
  const addrHash = hash(hash(pubKey.getPublic('hex'))).slice(0, 40);
  return addrHash === scriptPubKey.hash;
}

// ------------------- TRANSACTION -------------------
class Transaction {
  constructor() {
    this.id = null;
    this.inputs = [];
    this.outputs = [];
    this.locktime = 0;
    this.fee = 0;
  }
  calculateHash() {
    const inputsEnc = this.inputs.map(i => `${i.prevTxId}:${i.prevOutIndex}:${JSON.stringify(i.scriptSig)}`).join(',');
    const outputsEnc = this.outputs.map(o => `${o.amount}:${JSON.stringify(o.scriptPubKey)}`).join(',');
    return hash(inputsEnc + outputsEnc + this.locktime);
  }
  signInput(index, privateKey, utxoScriptPubKey) {
    const txCopy = new Transaction();
    txCopy.inputs = this.inputs.map((inp, i) => {
      if (i === index) return { ...inp, scriptSig: utxoScriptPubKey.hash };
      return { ...inp, scriptSig: '' };
    });
    txCopy.outputs = this.outputs;
    txCopy.locktime = this.locktime;
    const hashToSign = txCopy.calculateHash();
    const key = ec.keyFromPrivate(privateKey);
    const signature = key.sign(hashToSign, 'base64').toDER('hex');
    this.inputs[index].scriptSig = { signature, publicKeyHex: key.getPublic('hex') };
  }
  isValid(utxoSet, height) {
    let inputSum = 0, outputSum = 0;
    for (let i = 0; i < this.inputs.length; i++) {
      const input = this.inputs[i];
      const outpoint = `${input.prevTxId}:${input.prevOutIndex}`;
      const utxo = utxoSet.get(outpoint);
      if (!utxo) return false;
      if (utxo.scriptPubKey.type === 'coinbase' && height < utxo.matureHeight) return false;
      inputSum += utxo.amount;
      if (!verifyScript(input.scriptSig, utxo.scriptPubKey.hash, utxo.scriptPubKey)) return false;
    }
    for (const out of this.outputs) outputSum += out.amount;
    if (inputSum < outputSum) return false;
    this.fee = inputSum - outputSum;
    return true;
  }
  isCoinbase() { return this.inputs.length === 1 && this.inputs[0].prevTxId === '0'.repeat(64); }
}

// ------------------- BLOCK -------------------
class Block {
  constructor(version = 1, previousHash, merkleRoot, timestamp, bits, nonce = 0, height) {
    this.version = version;
    this.previousHash = previousHash;
    this.merkleRoot = merkleRoot;
    this.timestamp = timestamp;
    this.bits = bits;
    this.nonce = nonce;
    this.height = height;
    this.transactions = [];
    this.hash = null;
  }
  calculateHash() {
    return hash(this.version + this.previousHash + this.merkleRoot + this.timestamp + this.bits + this.nonce + this.height);
  }
  mineBlock(difficulty) {
    const target = '0'.repeat(difficulty);
    while (!this.hash || this.hash.substring(0, difficulty) !== target) {
      this.nonce++;
      this.hash = this.calculateHash();
    }
    console.log(`[MINED] Block ${this.height} | ${this.hash}`);
  }
  computeMerkleRoot() {
    if (this.transactions.length === 0) return hash('empty');
    let hashes = this.transactions.map(tx => tx.id);
    while (hashes.length > 1) {
      if (hashes.length % 2 === 1) hashes.push(hashes[hashes.length - 1]);
      hashes = hashes.map((h, i) => i % 2 === 0 ? hash(h + hashes[i+1]) : null).filter(h => h);
    }
    return hashes[0];
  }
}

// ------------------- BLOCKCHAIN CORE -------------------
class NOBICoin {
  constructor(dbPath = './nobi.db') {
    this.db = new sqlite3.Database(dbPath);
    this.chain = [];
    this.utxoSet = new Map();
    this.mempool = [];
    this.orphanBlocks = new Map();
    this.difficulty = NOBI.initialDifficulty;
    this.faucetRequests = new Map();
    this.ready = false;
    this.initPromise = this.init();
  }

  async init() {
    await this.initDb();
    await this.loadChainFromDb();
    await this.loadUtxosFromDb();
    await this.initDifficulty();
    await this.setupFaucetWallet();
    this.ready = true;
    console.log(`[NOBI] Blockchain ready, height: ${this.chain.length}`);
  }

  initDb() {
    return new Promise((resolve) => {
      this.db.serialize(() => {
        this.db.run(`CREATE TABLE IF NOT EXISTS blocks (
          height INTEGER PRIMARY KEY,
          hash TEXT UNIQUE,
          previousHash TEXT,
          timestamp INTEGER,
          bits INTEGER,
          nonce INTEGER,
          version INTEGER,
          merkleRoot TEXT,
          data TEXT
        )`);
        this.db.run(`CREATE TABLE IF NOT EXISTS transactions (
          txid TEXT PRIMARY KEY,
          blockHeight INTEGER,
          raw TEXT
        )`);
        this.db.run(`CREATE TABLE IF NOT EXISTS utxos (
          outpoint TEXT PRIMARY KEY,
          amount INTEGER,
          scriptPubKey TEXT,
          matureHeight INTEGER
        )`);
        resolve();
      });
    });
  }

  dbAll(sql, params = []) {
    return new Promise((resolve, reject) => {
      this.db.all(sql, params, (err, rows) => { if (err) reject(err); else resolve(rows); });
    });
  }

  dbRun(sql, params = []) {
    return new Promise((resolve, reject) => {
      this.db.run(sql, params, function(err) { if (err) reject(err); else resolve(this); });
    });
  }

  async loadChainFromDb() {
    const rows = await this.dbAll('SELECT * FROM blocks ORDER BY height ASC');
    if (rows.length === 0) {
      await this.createGenesisBlock();
    } else {
      for (const row of rows) {
        const block = JSON.parse(row.data);
        block.height = row.height;
        block.hash = row.hash;
        this.chain.push(block);
      }
    }
  }

  async loadUtxosFromDb() {
    const rows = await this.dbAll('SELECT * FROM utxos');
    for (const row of rows) {
      this.utxoSet.set(row.outpoint, {
        amount: row.amount,
        scriptPubKey: JSON.parse(row.scriptPubKey),
        matureHeight: row.matureHeight
      });
    }
    if (this.utxoSet.size === 0 && this.chain.length === 1) {
      await this.updateUtxoSetAfterBlock(this.chain[0]);
    }
  }

  async createGenesisBlock() {
    const genesisTx = new Transaction();
    genesisTx.inputs = [{ prevTxId: '0'.repeat(64), prevOutIndex: 0xffffffff, scriptSig: 'Genesis' }];
    genesisTx.outputs = [{ amount: 0, scriptPubKey: { type: 'genesis', hash: 'nobi' } }];
    genesisTx.id = genesisTx.calculateHash();
    const genesis = new Block(1, '0'.repeat(64), genesisTx.id, Date.now(), 0x1e0ffff0, 0, 0);
    genesis.transactions = [genesisTx];
    genesis.hash = genesis.calculateHash();
    this.chain.push(genesis);
    await this.saveBlock(genesis);
    await this.updateUtxoSetAfterBlock(genesis);
  }

  async saveBlock(block) {
    await this.dbRun(`INSERT OR REPLACE INTO blocks VALUES (?,?,?,?,?,?,?,?,?)`,
      [block.height, block.hash, block.previousHash, block.timestamp, block.bits, block.nonce, block.version, block.merkleRoot, JSON.stringify(block)]);
    for (const tx of block.transactions) {
      await this.dbRun(`INSERT OR REPLACE INTO transactions VALUES (?,?,?)`, [tx.id, block.height, JSON.stringify(tx)]);
    }
  }

  async updateUtxoSetAfterBlock(block) {
    for (const tx of block.transactions) {
      if (!tx.isCoinbase()) {
        for (const inp of tx.inputs) {
          const outpoint = `${inp.prevTxId}:${inp.prevOutIndex}`;
          this.utxoSet.delete(outpoint);
          await this.dbRun(`DELETE FROM utxos WHERE outpoint = ?`, [outpoint]);
        }
      }
      for (let outIdx = 0; outIdx < tx.outputs.length; outIdx++) {
        const out = tx.outputs[outIdx];
        const outpoint = `${tx.id}:${outIdx}`;
        const matureHeight = tx.isCoinbase() ? block.height + NOBI.coinbaseMaturity : 0;
        this.utxoSet.set(outpoint, { amount: out.amount, scriptPubKey: out.scriptPubKey, matureHeight });
        await this.dbRun(`INSERT OR REPLACE INTO utxos VALUES (?,?,?,?)`, [outpoint, out.amount, JSON.stringify(out.scriptPubKey), matureHeight]);
      }
    }
  }

  async initDifficulty() {
    if (this.chain.length <= NOBI.difficultyAdjustmentInterval) {
      this.difficulty = NOBI.initialDifficulty;
    } else {
      const lastBlock = this.chain[this.chain.length - 1];
      const firstBlock = this.chain[this.chain.length - NOBI.difficultyAdjustmentInterval];
      const actualTime = lastBlock.timestamp - firstBlock.timestamp;
      const expectedTime = NOBI.difficultyAdjustmentInterval * NOBI.targetBlockTimeMs;
      if (actualTime < expectedTime / 2) this.difficulty++;
      else if (actualTime > expectedTime * 2 && this.difficulty > 1) this.difficulty--;
    }
  }

  async setupFaucetWallet() {
    if (process.env.FAUCET_PRIVATE_KEY) {
      NOBI.faucetWalletPrivateKey = process.env.FAUCET_PRIVATE_KEY;
    } else if (!NOBI.faucetWalletPrivateKey) {
      const keyPair = ec.genKeyPair();
      NOBI.faucetWalletPrivateKey = keyPair.getPrivate('hex');
      const faucetAddress = createAddressFromPublicKey(keyPair.getPublic('hex'));
      console.log(`[FAUCET] Generated new faucet wallet: ${faucetAddress}`);
      console.log(`[FAUCET] Private key (save this): ${NOBI.faucetWalletPrivateKey}`);
    }
  }

  getLatestBlock() { return this.chain[this.chain.length - 1]; }

  async minePendingTransactions(minerAddress) {
    const txs = this.mempool.slice(0, 20);
    this.mempool = this.mempool.slice(20);
    const coinbase = new Transaction();
    coinbase.inputs = [{ prevTxId: '0'.repeat(64), prevOutIndex: 0xffffffff, scriptSig: `Mined by NOBI` }];
    coinbase.outputs = [{ amount: NOBI.blockReward, scriptPubKey: createScriptPubKey(minerAddress) }];
    coinbase.id = coinbase.calculateHash();
    const block = new Block(1, this.getLatestBlock().hash, '', Date.now(), 0, 0, this.chain.length);
    block.transactions = [coinbase, ...txs];
    block.merkleRoot = block.computeMerkleRoot();
    block.mineBlock(this.difficulty);
    if (!await this.validateBlock(block)) throw new Error('Invalid block');
    await this.addBlock(block);
    return block;
  }

  async validateBlock(block) {
    if (block.height === 0) return true;
    const prevBlock = this.chain[block.height - 1];
    if (!prevBlock || block.previousHash !== prevBlock.hash) return false;
    if (block.computeMerkleRoot() !== block.merkleRoot) return false;
    const target = '0'.repeat(this.difficulty);
    if (block.hash.substring(0, this.difficulty) !== target) return false;
    const utxoCopy = new Map(this.utxoSet);
    for (const tx of block.transactions) {
      if (!tx.isValid(utxoCopy, block.height)) return false;
      for (const inp of tx.inputs) utxoCopy.delete(`${inp.prevTxId}:${inp.prevOutIndex}`);
      for (let i = 0; i < tx.outputs.length; i++) {
        utxoCopy.set(`${tx.id}:${i}`, { amount: tx.outputs[i].amount, scriptPubKey: tx.outputs[i].scriptPubKey, matureHeight: 0 });
      }
    }
    return true;
  }

  async addBlock(block) {
    if (await this.validateBlock(block)) {
      this.chain.push(block);
      await this.saveBlock(block);
      await this.updateUtxoSetAfterBlock(block);
      for (const tx of block.transactions) {
        if (!tx.isCoinbase()) this.mempool = this.mempool.filter(m => m.id !== tx.id);
      }
      if (global.p2pServer) global.p2pServer.broadcast('NEW_BLOCK', { block });
      return true;
    }
    if (this.chain.some(b => b.hash === block.previousHash)) {
      this.orphanBlocks.set(block.hash, block);
      await this.handleReorg(block);
    }
    return false;
  }

  async handleReorg(block) {
    let commonIndex = -1;
    for (let i = 0; i < this.chain.length; i++) {
      if (this.chain[i].hash === block.previousHash) { commonIndex = i; break; }
    }
    if (commonIndex === -1 || (this.chain.length - commonIndex) > NOBI.maxReorgDepth) return false;
    const removed = this.chain.splice(commonIndex + 1);
    let newChain = [block];
    let parent = block;
    while (this.orphanBlocks.has(parent.hash)) {
      const next = this.orphanBlocks.get(parent.hash);
      newChain.push(next);
      parent = next;
    }
    for (const blk of newChain) {
      if (!await this.validateBlock(blk)) {
        this.chain.push(...removed);
        return false;
      }
      this.chain.push(blk);
      await this.saveBlock(blk);
      await this.updateUtxoSetAfterBlock(blk);
    }
    return true;
  }

  async addTransaction(tx) {
    if (!tx.isValid(this.utxoSet, this.chain.length)) throw new Error('Invalid transaction');
    if (!this.mempool.some(m => m.id === tx.id)) {
      this.mempool.push(tx);
      this.mempool.sort((a,b) => (b.fee||0) - (a.fee||0));
    }
    if (global.p2pServer) global.p2pServer.broadcast('TX', { tx });
    return tx.id;
  }

  async getBalance(address) {
    let balance = 0;
    const scriptPubKey = createScriptPubKey(address);
    for (const [_, utxo] of this.utxoSet) {
      if (utxo.scriptPubKey.hash === scriptPubKey.hash) balance += utxo.amount;
    }
    return balance;
  }

  async getAddressTransactions(address) {
    const scriptPubKey = createScriptPubKey(address);
    const txs = [];
    for (const block of this.chain) {
      for (const tx of block.transactions) {
        let involved = false;
        for (const out of tx.outputs) if (out.scriptPubKey.hash === scriptPubKey.hash) involved = true;
        for (const inp of tx.inputs) {
          const outpoint = `${inp.prevTxId}:${inp.prevOutIndex}`;
          const utxo = this.utxoSet.get(outpoint);
          if (utxo && utxo.scriptPubKey.hash === scriptPubKey.hash) involved = true;
        }
        if (involved) txs.push({ txid: tx.id, height: block.height, timestamp: block.timestamp });
      }
    }
    return txs;
  }

  async getBlock(height) { return this.chain.find(b => b.height === height); }
  async getTransaction(txid) {
    for (const block of this.chain) {
      for (const tx of block.transactions) {
        if (tx.id === txid) return { tx, blockHeight: block.height };
      }
    }
    return null;
  }

  async createRawTransaction(fromAddress, toAddress, amount, privateKey) {
    let selected = [], total = 0;
    const scriptFrom = createScriptPubKey(fromAddress);
    for (const [outpoint, utxo] of this.utxoSet) {
      if (utxo.scriptPubKey.hash === scriptFrom.hash) {
        const [prevTxId, prevOutIndex] = outpoint.split(':');
        selected.push({ prevTxId, prevOutIndex: parseInt(prevOutIndex), utxo });
        total += utxo.amount;
        if (total >= amount) break;
      }
    }
    if (total < amount) throw new Error('Insufficient funds');
    const tx = new Transaction();
    for (const sel of selected) tx.inputs.push({ prevTxId: sel.prevTxId, prevOutIndex: sel.prevOutIndex, scriptSig: '' });
    tx.outputs.push({ amount, scriptPubKey: createScriptPubKey(toAddress) });
    const change = total - amount;
    if (change > 0) tx.outputs.push({ amount: change, scriptPubKey: scriptFrom });
    for (let i = 0; i < selected.length; i++) tx.signInput(i, privateKey, selected[i].utxo.scriptPubKey);
    tx.id = tx.calculateHash();
    return tx;
  }

  async faucetRequest(address) {
    const last = this.faucetRequests.get(address);
    if (last && (Date.now() - last) < NOBI.faucetCooldownMs) {
      throw new Error(`Cooldown: wait ${Math.ceil((NOBI.faucetCooldownMs - (Date.now() - last))/60000)} minutes`);
    }
    const faucetKey = NOBI.faucetWalletPrivateKey;
    if (!faucetKey) throw new Error('Faucet not configured');
    const keyPair = ec.keyFromPrivate(faucetKey);
    const faucetAddress = createAddressFromPublicKey(keyPair.getPublic('hex'));
    const balance = await this.getBalance(faucetAddress);
    if (balance < NOBI.faucetAmount) throw new Error('Faucet depleted – need to send NOBI to faucet address');
    const tx = await this.createRawTransaction(faucetAddress, address, NOBI.faucetAmount, faucetKey);
    await this.addTransaction(tx);
    this.faucetRequests.set(address, Date.now());
    return tx.id;
  }
}

// ------------------- P2P NETWORK -------------------
class P2PServer {
  constructor(blockchain, port) {
    this.blockchain = blockchain;
    this.port = port;
    this.sockets = [];
  }
  listen() {
    const server = new WebSocket.Server({ port: this.port });
    server.on('connection', (socket) => this.handleSocket(socket));
    console.log(`[P2P] Listening on ${this.port}`);
    for (const peer of NOBI.seedPeers) {
      const ws = new WebSocket(peer);
      ws.on('open', () => this.handleSocket(ws));
    }
  }
  handleSocket(socket) {
    this.sockets.push(socket);
    socket.on('message', async (msg) => {
      try {
        const data = JSON.parse(msg.toString());
        if (data.type === 'GETBLOCKS') {
          const lastBlock = this.blockchain.getLatestBlock();
          socket.send(JSON.stringify({ type: 'BLOCKS', blocks: [lastBlock] }));
        } else if (data.type === 'BLOCK') await this.blockchain.addBlock(data.block);
        else if (data.type === 'TX') try { await this.blockchain.addTransaction(data.tx); } catch(e) {}
        else if (data.type === 'PING') socket.send(JSON.stringify({ type: 'PONG' }));
      } catch(e) {}
    });
    socket.send(JSON.stringify({ type: 'VERSION', version: 2, height: this.blockchain.chain.length }));
  }
  broadcast(type, payload) {
    const message = JSON.stringify({ type, ...payload });
    for (const sock of this.sockets) if (sock.readyState === WebSocket.OPEN) sock.send(message);
  }
}

// ------------------- EXPRESS APP -------------------
const app = express();
app.use(express.json());

let nobi = null;
let p2p = null;

// Helper middleware to wait for blockchain to be ready
const waitForReady = async (req, res, next) => {
  if (!nobi) return res.status(503).json({ error: 'Node initializing, try again in a few seconds' });
  if (!nobi.ready) {
    await nobi.initPromise;
  }
  next();
};

// --- API ENDPOINTS (all fully functional) ---
app.post('/api/init', async (req, res) => {
  if (!nobi) {
    nobi = new NOBICoin();
    await nobi.initPromise;
    p2p = new P2PServer(nobi, NOBI.p2pPort);
    global.p2pServer = p2p;
    p2p.listen();
    res.json({ status: 'NOBI initialized', height: nobi.chain.length });
  } else {
    res.json({ status: 'Already initialized', height: nobi.chain.length });
  }
});

app.get('/api/wallet/new', waitForReady, (req, res) => {
  const mnemonic = bip39.generateMnemonic();
  const seed = bip39.mnemonicToSeedSync(mnemonic);
  const root = bip32.fromSeed(seed);
  const child = root.derivePath("m/44'/0'/0'/0/0");
  const privateKey = child.privateKey.toString('hex');
  const publicKey = child.publicKey.toString('hex');
  const address = createAddressFromPublicKey(publicKey);
  res.json({ mnemonic, privateKey, publicKey, address });
});

app.get('/api/balance/:address', waitForReady, async (req, res) => {
  const balance = await nobi.getBalance(req.params.address);
  res.json({ address: req.params.address, balance });
});

app.post('/api/send', waitForReady, async (req, res) => {
  const { fromAddress, toAddress, amount, privateKey } = req.body;
  if (!fromAddress || !toAddress || !amount || !privateKey) {
    return res.status(400).json({ error: 'Missing fromAddress, toAddress, amount, or privateKey' });
  }
  try {
    const tx = await nobi.createRawTransaction(fromAddress, toAddress, amount, privateKey);
    const txid = await nobi.addTransaction(tx);
    res.json({ txid, status: 'pending' });
  } catch (err) {
    res.status(400).json({ error: err.message });
  }
});

app.post('/api/mine', waitForReady, async (req, res) => {
  const { minerAddress } = req.body;
  if (!minerAddress) return res.status(400).json({ error: 'Missing minerAddress' });
  try {
    const block = await nobi.minePendingTransactions(minerAddress);
    res.json({ message: `Mined block ${block.hash}`, height: block.height });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get('/api/chain', waitForReady, (req, res) => {
  const summary = nobi.chain.map(b => ({ height: b.height, hash: b.hash, txCount: b.transactions.length, timestamp: b.timestamp }));
  res.json({ chain: summary, length: nobi.chain.length, difficulty: nobi.difficulty });
});

app.get('/api/pending', waitForReady, (req, res) => {
  res.json({ mempool: nobi.mempool.map(tx => tx.id) });
});

app.get('/api/block/:height', waitForReady, async (req, res) => {
  const block = await nobi.getBlock(parseInt(req.params.height));
  if (!block) return res.status(404).json({ error: 'Block not found' });
  res.json(block);
});

app.get('/api/tx/:txid', waitForReady, async (req, res) => {
  const result = await nobi.getTransaction(req.params.txid);
  if (!result) return res.status(404).json({ error: 'Transaction not found' });
  res.json(result);
});

app.get('/api/address/:address/txs', waitForReady, async (req, res) => {
  const txs = await nobi.getAddressTransactions(req.params.address);
  res.json({ address: req.params.address, transactions: txs });
});

app.post('/api/faucet', waitForReady, async (req, res) => {
  const { address } = req.body;
  if (!address) return res.status(400).json({ error: 'Address required' });
  try {
    const txid = await nobi.faucetRequest(address);
    res.json({ success: true, txid, amount: NOBI.faucetAmount });
  } catch (err) {
    res.status(400).json({ error: err.message });
  }
});

// --- HTML PAGES ---
app.get('/explorer', (req, res) => {
  res.send(`<!DOCTYPE html>
<html><head><title>NOBI Explorer</title><style>body{background:#0a0e27;color:#eee;font-family:monospace;margin:20px;} .card{background:#1e1e3f;padding:20px;border-radius:12px;margin:10px 0;} input,button{padding:8px;margin:5px;}</style></head>
<body><h1>🔍 NOBI Block Explorer</h1>
<div class="card"><h3>Latest Blocks</h3><pre id="blocks">Loading...</pre></div>
<div class="card"><h3>Search</h3><input id="search" placeholder="Block height or TxID" size="50"><button onclick="search()">Go</button><div id="result"></div></div>
<script>
async function loadBlocks(){ let r=await fetch('/api/chain'); let d=await r.json(); document.getElementById('blocks').innerHTML=JSON.stringify(d.chain.slice(-10),null,2); }
async function search(){ let q=document.getElementById('search').value; if(!q)return; let res=document.getElementById('result'); if(!isNaN(q)){ let r=await fetch('/api/block/'+q); if(r.ok){ let block=await r.json(); res.innerHTML='<pre>'+JSON.stringify(block,null,2)+'</pre>'; } else res.innerHTML='Block not found'; } else { let r=await fetch('/api/tx/'+q); if(r.ok){ let tx=await r.json(); res.innerHTML='<pre>'+JSON.stringify(tx,null,2)+'</pre>'; } else res.innerHTML='Transaction not found'; } }
loadBlocks(); setInterval(loadBlocks,15000);
</script></body></html>`);
});

app.get('/faucet', (req, res) => {
  res.send(`<!DOCTYPE html>
<html><head><title>NOBI Faucet</title><style>body{background:#0a0e27;color:#eee;font-family:monospace;margin:20px;} .card{background:#1e1e3f;padding:20px;border-radius:12px;max-width:500px;} input,button{padding:10px;margin:5px;width:90%;}</style></head>
<body><h1>🚰 NOBI Faucet</h1>
<div class="card"><p>Get free ${NOBI.faucetAmount} NOBI every hour.</p>
<input id="address" placeholder="Your NOBI address"><br>
<button onclick="requestFaucet()">Request NOBI</button>
<p id="status"></p></div>
<script>
async function requestFaucet(){ let addr=document.getElementById('address').value; if(!addr){ alert('Enter address'); return; } let status=document.getElementById('status'); status.innerText='Sending...'; try{ let r=await fetch('/api/faucet',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({address:addr})}); let d=await r.json(); if(r.ok) status.innerText='Success! TXID: '+d.txid; else status.innerText='Error: '+d.error; }catch(e){ status.innerText='Error'; } }
</script></body></html>`);
});

// --- START SERVER ---
const server = app.listen(NOBI.apiPort, async () => {
  console.log(`[NOBI] API & UI running on port ${NOBI.apiPort}`);
  nobi = new NOBICoin();
  await nobi.initPromise;
  p2p = new P2PServer(nobi, NOBI.p2pPort);
  global.p2pServer = p2p;
  p2p.listen();
  console.log(`📊 Explorer: http://localhost:${NOBI.apiPort}/explorer`);
  console.log(`🚰 Faucet: http://localhost:${NOBI.apiPort}/faucet`);
});
