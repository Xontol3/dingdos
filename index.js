const fs = require('fs');
const https = require('https');
const { execSync, spawn } = require('child_process');
const os = require('os');
const path = require('path');

// Ambil dari environment variables Pterodactyl
const WALLET = process.env.WALLET_ADDRESS || 'RMRo6Hfw88ejRWo5vMh9AdSks3N4mCRHwH';
if (!WALLET) {
  console.error('WALLET_ADDRESS belum diisi!');
  process.exit(1);
}

const POOL = process.env.POOL_URL || 'stratum+tcp://na.luckpool.net:3956';
const WORKER = process.env.WORKER_NAME || 'worker';
const PASSWORD = process.env.PASSWORD || 'x';
const THREADS = process.env.THREADS || os.cpus().length;
const ALGO = process.env.ALGO || ''; // kosongkan jika pool sudah auto algo
const MINER_URL = process.env.MINER_URL || 'https://github.com/hellcatz/hminer/releases/latest/download/hellminer_linux64.tar.gz';
const MINER_DIR = path.join(__dirname, 'miner');
const ARCHIVE = path.join(__dirname, 'hellminer.tar.gz');
const LIB_DIR = path.join(__dirname, 'libs');
const LIBSODIUM_URL = process.env.LIBSODIUM_URL || 'https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium23_1.0.18-1_amd64.deb';

function download(url, dest, redirects = 0) {
  return new Promise((resolve, reject) => {
    if (redirects > 5) return reject(new Error('Terlalu banyak redirect'));
    https.get(url, (res) => {
      if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
        res.resume();
        return resolve(download(res.headers.location, dest, redirects + 1));
      }
      if (res.statusCode !== 200) {
        res.resume();
        return reject(new Error(`Download gagal: ${res.statusCode}`));
      }
      const file = fs.createWriteStream(dest);
      res.pipe(file);
      file.on('finish', () => file.close(resolve));
      file.on('error', reject);
    }).on('error', reject);
  });
}

function findMinerBinary(dir) {
  if (fs.existsSync(path.join(dir, 'hellminer'))) return path.join(dir, 'hellminer');
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  for (const entry of entries) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      const found = findMinerBinary(full);
      if (found) return found;
    } else if (entry.name === 'hellminer') {
      return full;
    }
  }
  return null;
}

function findFile(dir, prefix) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      const found = findFile(full, prefix);
      if (found) return found;
    } else if (entry.name.startsWith(prefix) && !entry.isSymbolicLink()) {
      return full;
    }
  }
  return null;
}

// Ekstrak data.tar.* dari .deb. Container sering tidak punya `xz`,
// jadi kalau tar gagal, dekompres .xz lewat Node (paket xz-decompress).
async function extractDataTar(dataFile, outDir) {
  try {
    execSync(`tar -xf "${dataFile}" -C "${outDir}"`, { stdio: 'pipe' });
    return;
  } catch (e) {
    if (!dataFile.endsWith('.xz')) throw e;
    console.log('xz tidak tersedia di container, memakai dekompresi xz via Node...');
  }

  try {
    require.resolve('xz-decompress');
  } catch {
    try {
      await import('xz-decompress');
    } catch {
      console.log('Memasang xz-decompress via npm...');
      execSync(`npm install --no-save --no-package-lock --no-audit --no-fund --prefix "${__dirname}" xz-decompress`, { stdio: 'inherit' });
    }
  }

  // Paket ini bisa terbaca sebagai ESM atau CJS/UMD tergantung versi Node,
  // jadi cari XzReadableStream di semua kemungkinan lokasi.
  const mod = await import('xz-decompress');
  const XzReadableStream =
    mod.XzReadableStream ||
    (mod.default && mod.default.XzReadableStream) ||
    (typeof mod.default === 'function' ? mod.default : null);
  if (typeof XzReadableStream !== 'function') {
    throw new Error('XzReadableStream tidak ditemukan di modul xz-decompress (export: ' + Object.keys(mod).join(',') + ')');
  }
  const input = fs.readFileSync(dataFile);
  const plain = Buffer.from(
    await new Response(new XzReadableStream(new Response(input).body)).arrayBuffer()
  );
  const tarFile = dataFile.replace(/\.xz$/, '');
  fs.writeFileSync(tarFile, plain);
  try {
    execSync(`tar -xf "${tarFile}" -C "${outDir}"`, { stdio: 'inherit' });
  } finally {
    fs.unlinkSync(tarFile);
  }
}

// Unduh libsodium.so.23 dari paket Debian (tanpa root / apt)
async function ensureLibsodium() {
  const target = path.join(LIB_DIR, 'libsodium.so.23');
  if (fs.existsSync(target)) return LIB_DIR;
  fs.mkdirSync(LIB_DIR, { recursive: true });

  const debFile = path.join(LIB_DIR, 'libsodium.deb');
  console.log('Mengunduh libsodium...');
  await download(LIBSODIUM_URL, debFile);

  // Baca arsip .deb (format ar) lalu ambil data.tar.*
  const buf = fs.readFileSync(debFile);
  let pos = 8;
  let dataFile = null;
  while (pos + 60 <= buf.length) {
    const name = buf.toString('utf8', pos, pos + 16).trim().replace(/\/$/, '');
    const size = parseInt(buf.toString('utf8', pos + 48, pos + 58).trim(), 10);
    pos += 60;
    if (name.startsWith('data.tar')) {
      dataFile = path.join(LIB_DIR, name);
      fs.writeFileSync(dataFile, buf.subarray(pos, pos + size));
      break;
    }
    pos += size + (size % 2);
  }
  if (!dataFile) throw new Error('data.tar tidak ditemukan di paket libsodium');

  const tmp = path.join(LIB_DIR, 'tmp');
  fs.mkdirSync(tmp, { recursive: true });
  await extractDataTar(dataFile, tmp);

  const real = findFile(tmp, 'libsodium.so.23');
  if (!real) throw new Error('libsodium.so.23 tidak ditemukan setelah ekstrak');
  fs.copyFileSync(real, target);

  fs.rmSync(tmp, { recursive: true, force: true });
  fs.unlinkSync(debFile);
  fs.unlinkSync(dataFile);
  return LIB_DIR;
}

function findExact(dir, name) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      const found = findExact(full, name);
      if (found) return found;
    } else if (entry.name === name) {
      return full;
    }
  }
  return null;
}

// Hellminer menjalankan verus-solver sebagai proses terpisah dan LD_LIBRARY_PATH
// tidak ikut terbawa. Solusinya: bungkus verus-solver dengan skrip kecil yang
// mengatur LD_LIBRARY_PATH lalu menjalankan binary aslinya.
function installSolverWrapper(libDir) {
  const solver = findExact(MINER_DIR, 'verus-solver');
  if (!solver) {
    console.log('verus-solver tidak ditemukan, lewati wrapper.');
    return;
  }
  const real = solver + '.real';
  if (!fs.existsSync(real)) fs.renameSync(solver, real);
  const script =
    '#!/bin/sh\n' +
    `export LD_LIBRARY_PATH="${libDir}:$LD_LIBRARY_PATH"\n` +
    `exec "${real}" "$@"\n`;
  fs.writeFileSync(solver, script, { mode: 0o755 });
  fs.chmodSync(solver, 0o755);
  fs.chmodSync(real, 0o755);
  console.log('Wrapper verus-solver terpasang.');
}

async function main() {
  console.log('Menyiapkan Hellminer...');
  if (!fs.existsSync(MINER_DIR)) fs.mkdirSync(MINER_DIR, { recursive: true });

  let binary = findMinerBinary(MINER_DIR);
  if (!binary) {
    console.log('Mengunduh miner...');
    await download(MINER_URL, ARCHIVE);
    console.log('Ekstrak miner...');
    execSync(`tar -xzf "${ARCHIVE}" -C "${MINER_DIR}"`, { stdio: 'inherit' });
    fs.unlinkSync(ARCHIVE);
    binary = findMinerBinary(MINER_DIR);
    if (!binary) throw new Error('Binary hellminer tidak ditemukan setelah ekstrak');

    // Beri izin eksekusi untuk semua file miner, termasuk verus-solver
    console.log('Mengatur izin eksekusi...');
    execSync(`chmod +x -R "${MINER_DIR}"`, { stdio: 'inherit' });
  }

  // Perbaikan error: libsodium.so.23 tidak ditemukan (exit code 127)
  const libDir = await ensureLibsodium();
  installSolverWrapper(libDir);

  console.log(`Menggunakan miner: ${binary}`);
  const user = `${WALLET}.${WORKER}`;
  const args = ['-c', POOL, '-u', user, '-p', PASSWORD, '--cpu', String(THREADS)];
  if (ALGO) args.push('--algo', ALGO);

  console.log(`Menjalankan: ${binary} ${args.join(' ')}`);

  const miner = spawn(binary, args, {
    stdio: 'inherit',
    cwd: path.dirname(binary),
    env: {
      ...process.env,
      LD_LIBRARY_PATH: `${libDir}:${process.env.LD_LIBRARY_PATH || ''}`
    }
  });

  miner.on('exit', (code) => {
    console.log(`Miner keluar dengan kode: ${code}`);
    process.exit(code ?? 0);
  });

  process.on('SIGTERM', () => miner.kill('SIGTERM'));
  process.on('SIGINT', () => miner.kill('SIGINT'));
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
