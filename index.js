const pm2 = require('pm2');
const http = require('http');
const https = require('https');
const fs = require('fs');
const crypto = require('crypto');
const { exec } = require('child_process');

const appName = 'api-server';
const scriptPath = './api.js';
const PACKAGE_PATH = './package.json';

const REMOTE_SCRIPT_URL = 'https://botapi.ihsan83636.workers.dev/api.js';
const REMOTE_PACKAGE_URL = 'https://botapi.ihsan83636.workers.dev/package.json';

const HEALTHCHECK_INTERVAL = 1 * 60 * 1000; // 1 menit
const HEALTH_TIMEOUT = 2 * 60 * 1000;       // 2 menit
const UPDATE_INTERVAL = 5 * 60 * 1000;      // 5 menit

// Ambil port dari ENV (PORT atau SERVER_PORT), tanpa hardcode 2090
const SERVER_PORT = process.env.PORT || process.env.SERVER_PORT;
if (!SERVER_PORT) {
  console.error("❌ Tidak ada port yang tersedia dari environment!");
  process.exit(1);
}

const HEALTHCHECK_URL = `http://localhost:${SERVER_PORT}/api/health`;

function getHash(content) {
  return crypto.createHash('sha256').update(content).digest('hex');
}

function forceRestart() {
  pm2.delete(appName, () => {
    pm2.start({
      name: appName,
      script: scriptPath,
      autorestart: true,
      restart_delay: 5000,
      env: {
        NODE_ENV: 'production',
        PORT: SERVER_PORT
      }
    }, (err) => {
      if (err) console.error('[FORCE RESTART] Gagal start ulang:', err.message);
      else console.log('[FORCE RESTART] Berhasil restart ulang secara paksa');
    });
  });
}

function startHealthWatcher() {
  let failCount = 0;
  const maxFails = 3;

  setInterval(() => {
    // ambil URL dari file local_url.txt (fallback ke localhost)
    let targetUrl = HEALTHCHECK_URL;
    try {
      if (fs.existsSync('./local_url.txt')) {
        const url = fs.readFileSync('./local_url.txt', 'utf8').trim();
        if (url) targetUrl = `${url}/api/health`;
      }
    } catch (err) {
      console.error('[HEALTH CHECK] Gagal baca local_url.txt:', err.message);
    }

    console.log(`[HEALTH CHECK] Mengecek ${targetUrl}`);

    const lib = targetUrl.startsWith('https') ? https : http;
    const req = lib.get(targetUrl, res => {
      if (res.statusCode === 200) {
        failCount = 0;
        console.log(`[HEALTH CHECK] OK (200) dari ${targetUrl}`);
      } else {
        failCount++;
        console.warn(`[HEALTH CHECK] Status bukan 200 (${res.statusCode}). Gagal ${failCount}/${maxFails}`);
        if (failCount >= maxFails) {
          console.warn('[HEALTH CHECK] Melebihi batas gagal, restart...');
          pm2.restart(appName, () => {
            console.log('[HEALTH CHECK] Restart dilakukan, reset counter.');
            failCount = 0; // reset setelah restart
          });
        }
      }
    });

    req.setTimeout(HEALTH_TIMEOUT, () => {
      failCount++;
      console.warn(`[HEALTH CHECK] Timeout ke ${targetUrl}. Gagal ${failCount}/${maxFails}`);
      req.destroy();
      if (failCount >= maxFails) {
        console.warn('[HEALTH CHECK] Melebihi batas gagal, restart paksa...');
        forceRestart();
        failCount = 0; // reset setelah forceRestart
      }
    });

    req.on('error', (err) => {
      failCount++;
      console.warn(`[HEALTH CHECK] Error ke ${targetUrl}: ${err.message}. Gagal ${failCount}/${maxFails}`);
      if (failCount >= maxFails) {
        console.warn('[HEALTH CHECK] Melebihi batas gagal, restart paksa...');
        forceRestart();
        failCount = 0; // reset setelah forceRestart
      }
    });
  }, HEALTHCHECK_INTERVAL);
}

function checkPackageJsonUpdate() {
  https.get(REMOTE_PACKAGE_URL, res => {
    if (res.statusCode !== 200) {
      console.warn('[UPDATE] Gagal ambil package.json:', res.statusCode);
      return;
    }

    let data = '';
    res.on('data', chunk => data += chunk);
    res.on('end', () => {
      try {
        const remoteHash = getHash(data);
        const localData = fs.readFileSync(PACKAGE_PATH, 'utf-8');
        const localHash = getHash(localData);

        if (remoteHash !== localHash) {
          console.log('[UPDATE] package.json berubah. Mengupdate...');
          fs.writeFileSync(PACKAGE_PATH, data);
          console.log('[UPDATE] Menjalankan npm install...');
          exec('npm install', (error, stdout, stderr) => {
            if (error) return console.error('[NPM INSTALL] Error:', error.message);
            if (stderr) console.warn('[NPM INSTALL] Warning:', stderr);
            console.log('[NPM INSTALL] Output:', stdout);
            pm2.restart(appName, err => {
              if (err) console.error('[PM2] Gagal restart setelah update package.json:', err.message);
              else console.log('[PM2] Restart sukses setelah update package.json');
            });
          });
        } else {
          console.log('[UPDATE] package.json tidak berubah.');
        }
      } catch (e) {
        console.error('[UPDATE] Error saat update package.json:', e.message);
      }
    });
  }).on('error', err => {
    console.error('[UPDATE] Gagal fetch package.json:', err.message);
  });
}

function checkForUpdate() {
  https.get(REMOTE_SCRIPT_URL, res => {
    if (res.statusCode !== 200) {
      console.warn('[UPDATE] Gagal ambil api.js:', res.statusCode);
      return;
    }

    let data = '';
    res.on('data', chunk => data += chunk);
    res.on('end', () => {
      try {
        const remoteHash = getHash(data);
        const localData = fs.readFileSync(scriptPath, 'utf-8');
        const localHash = getHash(localData);

        if (remoteHash !== localHash) {
          console.log('[UPDATE] Versi baru api.js ditemukan. Mengupdate...');
          if (fs.existsSync(scriptPath + '.bak')) fs.unlinkSync(scriptPath + '.bak');
          fs.copyFileSync(scriptPath, scriptPath + '.bak');
          fs.writeFileSync(scriptPath, data);
          console.log('[UPDATE] api.js berhasil diupdate!');
          pm2.restart(appName, err => {
            if (err) console.error('[PM2] Gagal restart setelah update api.js:', err.message);
            else console.log('[PM2] Restart sukses setelah update api.js');
          });
        } else {
          console.log('[UPDATE] api.js tidak berubah.');
        }

        checkPackageJsonUpdate();

      } catch (e) {
        console.error('[UPDATE] Error saat update api.js:', e.message);
      }
    });
  }).on('error', err => {
    console.error('[UPDATE] Gagal fetch api.js:', err.message);
  });
}

function downloadScript(callback) {
  console.log('[BOOT] api.js tidak ditemukan. Mengunduh dari remote...');
  https.get(REMOTE_SCRIPT_URL, res => {
    if (res.statusCode !== 200) {
      const err = new Error(`Gagal ambil api.js, statusCode=${res.statusCode}`);
      console.error('[DOWNLOAD] Error:', err.message);
      return callback(err);
    }

    let data = '';
    res.on('data', chunk => data += chunk);
    res.on('end', () => {
      try {
        fs.writeFileSync(scriptPath, data, 'utf8');
        console.log('[DOWNLOAD] api.js berhasil diunduh dan disimpan ke', scriptPath);
        callback(null);
      } catch (e) {
        console.error('[DOWNLOAD] Gagal menulis file api.js:', e.message);
        callback(e);
      }
    });
  }).on('error', err => {
    console.error('[DOWNLOAD] Gagal koneksi saat download api.js:', err.message);
    callback(err);
  });
}

pm2.connect(err => {
  if (err) {
    console.error('Gagal konek ke PM2:', err);
    process.exit(2);
  }

  pm2.list((err, list) => {
    if (err) {
      console.error('Gagal ambil list PM2:', err);
      pm2.disconnect();
      return;
    }

    const already = list.find(proc => proc.name === appName);

    const startApp = () => {
      pm2.start({
        name: appName,
        script: scriptPath,
        autorestart: true,
        restart_delay: 5000,
        env: {
          NODE_ENV: 'production',
          PORT: SERVER_PORT
        }
      }, (err) => {
        if (err) {
          console.error('Gagal start:', err);
        } else {
          console.log(`[OK] ${appName} dijalankan via PM2 (port ${SERVER_PORT})`);
          startHealthWatcher();
          setInterval(checkForUpdate, UPDATE_INTERVAL);
          checkForUpdate();
        }
        pm2.disconnect();
      });
    };

    const ensureAndStart = () => {
      if (!fs.existsSync(scriptPath)) {
        downloadScript((err) => {
          if (err) {
            console.error('[BOOT] Gagal mengunduh api.js. Tidak dapat melanjutkan start.');
            pm2.disconnect();
            return;
          }
          startApp();
        });
      } else {
        if (already) {
          console.log(`[INFO] ${appName} sudah berjalan di port ${SERVER_PORT}`);
          startHealthWatcher();
          setInterval(checkForUpdate, UPDATE_INTERVAL);
          checkForUpdate();
          pm2.disconnect();
        } else {
          startApp();
        }
      }
    };

    ensureAndStart();
  });
});
