import * as nobleEd25519 from './noble-ed25519.js';

const ED25519_ORDER = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3edn;
const RESERVED_PREFIXES = new Set(['00', 'FF']);
const HASH_WORKER_SCRIPT = `
self.onmessage = async (event) => {
  const { type, batchSize } = event.data;
  if (type !== 'generate') return;

  const scalarWords = new Uint32Array(batchSize * 8);
  const suffixes = new Uint8Array(batchSize * 32);

  for (let index = 0; index < batchSize; index += 1) {
    const seed = crypto.getRandomValues(new Uint8Array(32));
    const digest = new Uint8Array(await crypto.subtle.digest('SHA-512', seed));
    const wordOffset = index * 8;
    const suffixOffset = index * 32;
    const clamped0 = digest[0] & 248;
    const clamped31 = (digest[31] & 63) | 64;

    scalarWords[wordOffset] = clamped0 | (digest[1] << 8) | (digest[2] << 16) | (digest[3] << 24);
    scalarWords[wordOffset + 1] = digest[4] | (digest[5] << 8) | (digest[6] << 16) | (digest[7] << 24);
    scalarWords[wordOffset + 2] = digest[8] | (digest[9] << 8) | (digest[10] << 16) | (digest[11] << 24);
    scalarWords[wordOffset + 3] = digest[12] | (digest[13] << 8) | (digest[14] << 16) | (digest[15] << 24);
    scalarWords[wordOffset + 4] = digest[16] | (digest[17] << 8) | (digest[18] << 16) | (digest[19] << 24);
    scalarWords[wordOffset + 5] = digest[20] | (digest[21] << 8) | (digest[22] << 16) | (digest[23] << 24);
    scalarWords[wordOffset + 6] = digest[24] | (digest[25] << 8) | (digest[26] << 16) | (digest[27] << 24);
    scalarWords[wordOffset + 7] = digest[28] | (digest[29] << 8) | (digest[30] << 16) | (clamped31 << 24);

    for (let byte = 0; byte < 32; byte += 1) suffixes[suffixOffset + byte] = digest[32 + byte];
  }

  self.postMessage(
    { type: 'results', scalarWords: scalarWords.buffer, suffixes: suffixes.buffer },
    [scalarWords.buffer, suffixes.buffer]
  );
};
`;

const state = {
  running: false,
  attempts: 0,
  startedAt: 0,
  result: null,
  progressTimer: null,
  wasmWorkers: [],
  hashWorkers: [],
  hashWorkerUrl: null,
  hashWorkerCount: 0,
  activeSearch: null,
  gpuScanner: null,
  gpuAvailable: false,
  watchlistMatches: []
};

const form = document.getElementById('keygenForm');
const targetPrefixInput = document.getElementById('targetPrefix');
const patternModeInput = document.getElementById('patternMode');
const watchlistInput = document.getElementById('watchlistInput');
const maxKeysInput = document.getElementById('maxKeys');
const maxTimeInput = document.getElementById('maxTime');
const generateBtn = document.getElementById('generateBtn');
const stopBtn = document.getElementById('stopBtn');
const gpuToggleContainer = document.getElementById('gpuToggleContainer');
const gpuAccelerationToggle = document.getElementById('gpuAccelerationToggle');
const gpuAccelerationHint = document.getElementById('gpuAccelerationHint');
const wasmWorkerCountInput = document.getElementById('wasmWorkerCount');
const wasmBatchSizeInput = document.getElementById('wasmBatchSize');
const gpuBatchSizeInput = document.getElementById('gpuBatchSize');
const gpuHashWorkerCountInput = document.getElementById('gpuHashWorkerCount');
const jsBatchSizeInput = document.getElementById('jsBatchSize');
const progressContainer = document.getElementById('progressContainer');
const progressText = document.getElementById('progressText');
const progressFill = document.getElementById('progressFill');
const resultContainer = document.getElementById('resultContainer');
const errorContainer = document.getElementById('errorContainer');
const downloadBtn = document.getElementById('downloadBtn');
const importInfoBtn = document.getElementById('importInfoBtn');
const importModal = document.getElementById('importModal');
const closeModal = document.getElementById('closeModal');

function toHex(bytes) {
  return Array.from(bytes, (value) => value.toString(16).padStart(2, '0')).join('').toUpperCase();
}

function fromHex(hex) {
  const pairs = hex.match(/.{1,2}/g) || [];
  return Uint8Array.from(pairs.map((pair) => parseInt(pair, 16)));
}

function scalarBytesToBigInt(bytes) {
  let value = 0n;
  for (let i = 0; i < bytes.length; i += 1) value |= BigInt(bytes[i]) << BigInt(i * 8);
  return value % ED25519_ORDER;
}

function derivePublicKeyBytes(clampedScalar) {
  const scalar = scalarBytesToBigInt(clampedScalar);
  if (scalar === 0n) throw new Error('Derived scalar reduced to zero');
  return nobleEd25519.Point.BASE.multiply(scalar).toBytes();
}

async function generateMeshCoreKeypair() {
  const seed = crypto.getRandomValues(new Uint8Array(32));
  const digest = new Uint8Array(await crypto.subtle.digest('SHA-512', seed));
  const clamped = digest.slice(0, 32);
  clamped[0] &= 248;
  clamped[31] &= 63;
  clamped[31] |= 64;

  const privateBytes = new Uint8Array(64);
  privateBytes.set(clamped, 0);
  privateBytes.set(digest.slice(32), 32);

  return {
    publicKey: toHex(derivePublicKeyBytes(clamped)),
    privateKey: toHex(privateBytes)
  };
}

function validateKeypair(privateKeyHex, publicKeyHex) {
  const privateBytes = fromHex(privateKeyHex);
  const publicBytes = fromHex(publicKeyHex);
  if (privateBytes.length !== 64) return { valid: false, error: 'Private key must be 64 bytes' };
  if (publicBytes.length !== 32) return { valid: false, error: 'Public key must be 32 bytes' };
  const clamped = privateBytes.slice(0, 32);
  if ((clamped[0] & 7) !== 0) return { valid: false, error: 'Scalar clamp low bits are invalid' };
  if ((clamped[31] & 192) !== 64) return { valid: false, error: 'Scalar clamp high bits are invalid' };
  const derived = toHex(derivePublicKeyBytes(clamped));
  return derived === publicKeyHex
    ? { valid: true }
    : { valid: false, error: 'Private key does not derive the public key' };
}

function parseMagnitude(value, unitMap, defaultUnit = 1) {
  const text = value.trim().toUpperCase();
  if (!text) return null;
  const match = text.match(/^(\d+(?:\.\d+)?)([A-Z]*)$/);
  if (!match) throw new Error(`Invalid limit: ${value}`);
  const unit = match[2] || '';
  const multiplier = unitMap[unit] ?? defaultUnit;
  if (!multiplier) throw new Error(`Unsupported limit unit: ${unit}`);
  return Math.floor(Number(match[1]) * multiplier);
}

function parseTuningNumber(value, fallback, label, min = 1, max = Number.MAX_SAFE_INTEGER) {
  if (/^(auto|default)$/i.test(value.trim())) return fallback;
  const parsed = parseMagnitude(value, { K: 1e3, M: 1e6 }, 1);
  const effective = parsed ?? fallback;
  if (!Number.isFinite(effective) || effective < min || effective > max) {
    throw new Error(`${label} must be between ${min.toLocaleString()} and ${max.toLocaleString()}.`);
  }
  return Math.floor(effective);
}

function parseWatchlist(text) {
  return text.split(/\r?\n/).map((line, index) => {
    const clean = line.trim();
    if (!clean || clean.startsWith('#')) return null;
    const [rawPattern, rawDescription = ''] = clean.split('|');
    const pattern = rawPattern.trim().toUpperCase();
    if (!pattern.includes('...')) throw new Error(`Watchlist line ${index + 1} must use FIRST...LAST`);
    const [first, last] = pattern.split('...');
    if (!first || !last || !/^[0-9A-F]+$/.test(first + last)) {
      throw new Error(`Watchlist line ${index + 1} must contain hex on both sides`);
    }
    return {
      pattern,
      description: rawDescription.trim(),
      first,
      last
    };
  }).filter(Boolean);
}

function modeConfig(mode, prefix) {
  const vanityMatch = mode.match(/(?:prefix-)?pattern-(2|4|6|8)$/);
  const hasPrefix = mode === 'prefix' || mode === 'simple' || mode.startsWith('prefix-pattern');
  return {
    mode,
    prefix,
    hasPrefix,
    vanityLength: vanityMatch ? Number(vanityMatch[1]) : 0
  };
}

function matchesVanity(publicKey, length) {
  if (!length) return true;
  const first = publicKey.slice(0, length);
  const last = publicKey.slice(-length);
  return first === last || first === [...last].reverse().join('');
}

function matchesPrimary(publicKey, config) {
  if (RESERVED_PREFIXES.has(publicKey.slice(0, 2))) return false;
  if (config.hasPrefix && !publicKey.startsWith(config.prefix)) return false;
  return matchesVanity(publicKey, config.vanityLength);
}

function findWatchlistMatches(publicKey, patterns) {
  return patterns.filter((pattern) => publicKey.startsWith(pattern.first) && publicKey.endsWith(pattern.last));
}

function estimateAttempts(config) {
  const prefixNibbles = config.hasPrefix ? config.prefix.length : 0;
  const vanityNibbles = config.vanityLength;
  if (!vanityNibbles) return 16 ** prefixNibbles;
  return 16 ** (prefixNibbles + vanityNibbles);
}

function formatCount(value) {
  if (value >= 1e12) return `${(value / 1e12).toFixed(1)} trillion`;
  if (value >= 1e9) return `${(value / 1e9).toFixed(1)} billion`;
  if (value >= 1e6) return `${(value / 1e6).toFixed(1)} million`;
  if (value >= 1e3) return `${(value / 1e3).toFixed(1)} thousand`;
  return Math.max(1, Math.round(value)).toLocaleString();
}

function formatDuration(seconds) {
  if (seconds >= 31536000) return `${(seconds / 31536000).toFixed(1)} years`;
  if (seconds >= 86400) return `${(seconds / 86400).toFixed(1)} days`;
  if (seconds >= 3600) return `${(seconds / 3600).toFixed(1)} hours`;
  if (seconds >= 60) return `${(seconds / 60).toFixed(1)} minutes`;
  return `${Math.max(1, Math.round(seconds))} seconds`;
}

function updateDifficultyEstimate() {
  const prefixInfo = document.getElementById('prefixInfo');
  const prefixDifficulty = document.getElementById('prefixDifficulty');
  const prefix = targetPrefixInput.value.trim().toUpperCase();
  const mode = patternModeInput.value;
  if ((mode.includes('prefix') || mode === 'simple') && !prefix) {
    prefixInfo.style.display = 'none';
    return;
  }
  const config = modeConfig(mode, prefix);
  const expected = estimateAttempts(config);
  const elapsed = Math.max((Date.now() - state.startedAt) / 1000, 0.001);
  const liveRate = state.running && state.attempts ? state.attempts / elapsed : 100000;
  prefixDifficulty.innerHTML = `
    <div style="margin-bottom: 8px;"><strong>${formatCount(expected)}</strong> expected attempts</div>
    <div style="font-size: 13px; color: var(--muted);">Estimated time: ~${formatDuration(expected / liveRate)} at ${Math.round(liveRate).toLocaleString()} keys/sec</div>
    <div style="font-size: 13px; color: var(--muted);">Mode: ${mode.replaceAll('-', ' ')}</div>
  `;
  prefixInfo.style.display = 'block';
}

function showError(message) {
  errorContainer.textContent = message;
  errorContainer.style.display = 'block';
}

function hideError() {
  errorContainer.style.display = 'none';
}

function setRunning(isRunning) {
  state.running = isRunning;
  generateBtn.disabled = isRunning;
  stopBtn.disabled = !isRunning;
  gpuAccelerationToggle.disabled = isRunning || !state.gpuAvailable;
  wasmWorkerCountInput.disabled = isRunning;
  wasmBatchSizeInput.disabled = isRunning;
  gpuBatchSizeInput.disabled = isRunning;
  gpuHashWorkerCountInput.disabled = isRunning;
  jsBatchSizeInput.disabled = isRunning;
  progressContainer.style.display = isRunning ? 'block' : 'none';
}

function startProgress(config, backend) {
  state.startedAt = Date.now();
  state.attempts = 0;
  const expected = estimateAttempts(config);
  clearInterval(state.progressTimer);
  state.progressTimer = setInterval(() => {
    const elapsed = Math.max((Date.now() - state.startedAt) / 1000, 0.001);
    const rate = state.attempts / elapsed;
    document.getElementById('attemptsCount').textContent = state.attempts.toLocaleString();
    document.getElementById('timeElapsed').textContent = `${elapsed.toFixed(1)}s`;
    document.getElementById('keysPerSecond').textContent = Math.round(rate).toLocaleString();
    progressText.textContent = `${state.attempts.toLocaleString()} attempts | ${Math.round(rate).toLocaleString()} keys/sec | ${elapsed.toFixed(1)}s elapsed [${backend}]`;
    progressFill.style.width = `${Math.min((state.attempts / expected) * 100, 99)}%`;
    updateDifficultyEstimate();
  }, 150);
}

function stopSearch() {
  state.running = false;
  for (const worker of state.wasmWorkers) worker.postMessage({ type: 'stop' });
}

function ensureWasmWorkers(count) {
  if (state.wasmWorkers.length === count) return;
  for (const worker of state.wasmWorkers) worker.terminate();
  state.wasmWorkers = [];
  for (let i = 0; i < count; i += 1) {
    state.wasmWorkers.push(new Worker('./wasm/worker.js', { type: 'module' }));
  }
}

function runWasmPrefixSearch(config, limits, watchlist, tuning) {
  ensureWasmWorkers(tuning.wasmWorkers);
  return new Promise((resolve, reject) => {
    const search = { done: false, stopped: 0 };
    state.activeSearch = search;
    const jobId = Date.now();
    const onMessage = (event) => {
      const data = event.data;
      if (data.jobId !== jobId || search.done) return;
      if (data.type === 'progress') state.attempts += data.attemptedDelta || 0;
      if (data.type === 'match') {
        state.attempts += data.attemptedDelta || 0;
        search.done = true;
        stopSearch();
        resolve({ ...data.result, validation: validateKeypair(data.result.privateKey, data.result.publicKey), watchlistMatches: [] });
      }
      if (data.type === 'stopped') {
        search.stopped += 1;
        if (search.stopped >= state.wasmWorkers.length && !search.done) resolve(null);
      }
      if (limits.maxKeys && state.attempts >= limits.maxKeys) stopSearch();
      if (limits.maxTimeMs && Date.now() - state.startedAt >= limits.maxTimeMs) stopSearch();
    };
    const onError = (error) => {
      search.done = true;
      reject(error);
    };
    for (const worker of state.wasmWorkers) {
      worker.onmessage = onMessage;
      worker.onerror = onError;
      worker.postMessage({
        type: 'start',
        jobId,
        targetPrefix: config.prefix,
        batchSize: tuning.wasmBatchSize,
        adaptiveBatching: true,
        targetBatchMs: 20,
        minBatchSize: 512,
        maxBatchSize: Math.max(65536, tuning.wasmBatchSize),
        progressIntervalMs: 150
      });
    }
    if (watchlist.length) console.warn('Watchlist monitoring is available in pro JS/GPU modes; pure WASM prefix mode stops at first prefix match.');
  });
}

async function ensureGpuScanner(tuning = null) {
  if (state.gpuScanner?.initialized) return state.gpuScanner;
  const gpuModule = globalThis.MeshCoreGpuModule;
  if (!gpuModule?.isUsableWebGpuModule?.()) return null;
  const scanner = new gpuModule.WebGpuEd25519Scanner();
  const ready = await scanner.initialize();
  if (!ready) return null;
  await scanner.autotuneWorkgroupSize(tuning?.gpuBatchSize ?? 131072);
  state.gpuScanner = scanner;
  return scanner;
}

function ensureHashWorkers(count) {
  if (state.hashWorkers.length === count && state.hashWorkerCount === count) return;
  for (const worker of state.hashWorkers) worker.terminate();
  state.hashWorkers = [];
  state.hashWorkerCount = count;
  if (state.hashWorkerUrl) URL.revokeObjectURL(state.hashWorkerUrl);
  state.hashWorkerUrl = URL.createObjectURL(new Blob([HASH_WORKER_SCRIPT], { type: 'application/javascript' }));
  for (let i = 0; i < count; i += 1) {
    state.hashWorkers.push(new Worker(state.hashWorkerUrl));
  }
}

function prefixToBytes(prefix) {
  const bytes = [];
  for (let i = 0; i < prefix.length; i += 2) bytes.push(parseInt(prefix.slice(i, i + 2).padEnd(2, '0'), 16));
  return bytes;
}

function packScalarWords(clampedScalars) {
  const words = new Uint32Array(clampedScalars.length * 8);
  clampedScalars.forEach((scalar, index) => {
    for (let word = 0; word < 8; word += 1) {
      const offset = word * 4;
      words[index * 8 + word] = scalar[offset] | (scalar[offset + 1] << 8) | (scalar[offset + 2] << 16) | (scalar[offset + 3] << 24);
    }
  });
  return words;
}

function unpackScalarWords(words, index) {
  const bytes = new Uint8Array(32);
  for (let word = 0; word < 8; word += 1) {
    const value = words[index * 8 + word];
    bytes[word * 4] = value & 255;
    bytes[word * 4 + 1] = (value >>> 8) & 255;
    bytes[word * 4 + 2] = (value >>> 16) & 255;
    bytes[word * 4 + 3] = (value >>> 24) & 255;
  }
  return bytes;
}

async function generateCandidateBatch(size) {
  const scalars = [];
  const suffixes = new Uint8Array(size * 32);
  for (let i = 0; i < size; i += 1) {
    const seed = crypto.getRandomValues(new Uint8Array(32));
    const digest = new Uint8Array(await crypto.subtle.digest('SHA-512', seed));
    const clamped = digest.slice(0, 32);
    clamped[0] &= 248;
    clamped[31] &= 63;
    clamped[31] |= 64;
    scalars.push(clamped);
    suffixes.set(digest.slice(32), i * 32);
  }
  return { scalarWords: packScalarWords(scalars), suffixes };
}

async function generateGpuCandidateBatch(size, workerCount) {
  ensureHashWorkers(workerCount);
  const activeWorkers = state.hashWorkers.slice(0, workerCount);
  if (!activeWorkers.length) throw new Error('No GPU hash workers are available.');
  const perWorker = Math.ceil(size / activeWorkers.length);
  const batches = await Promise.all(activeWorkers.map((worker) => new Promise((resolve, reject) => {
    const timeout = setTimeout(() => {
      worker.removeEventListener('message', onMessage);
      worker.removeEventListener('error', onError);
      reject(new Error('GPU hash worker timed out.'));
    }, 30000);
    const onMessage = (event) => {
      if (event.data.type !== 'results') return;
      clearTimeout(timeout);
      worker.removeEventListener('message', onMessage);
      worker.removeEventListener('error', onError);
      resolve({
        scalarWords: new Uint32Array(event.data.scalarWords),
        suffixes: new Uint8Array(event.data.suffixes)
      });
    };
    const onError = (event) => {
      clearTimeout(timeout);
      worker.removeEventListener('message', onMessage);
      worker.removeEventListener('error', onError);
      reject(event instanceof ErrorEvent ? event.error || new Error(event.message) : event);
    };
    worker.addEventListener('message', onMessage);
    worker.addEventListener('error', onError);
    worker.postMessage({ type: 'generate', batchSize: perWorker });
  })));

  const scalarWords = new Uint32Array(batches.reduce((sum, batch) => sum + batch.scalarWords.length, 0));
  const suffixes = new Uint8Array(batches.reduce((sum, batch) => sum + batch.suffixes.length, 0));
  let wordOffset = 0;
  let suffixOffset = 0;
  for (const batch of batches) {
    scalarWords.set(batch.scalarWords, wordOffset);
    suffixes.set(batch.suffixes, suffixOffset);
    wordOffset += batch.scalarWords.length;
    suffixOffset += batch.suffixes.length;
  }
  return { scalarWords, suffixes };
}

async function runJsProSearch(config, limits, watchlist, useGpu, tuning) {
  const scanner = useGpu && config.hasPrefix ? await ensureGpuScanner(tuning) : null;
  const batchSize = scanner ? tuning.gpuBatchSize : tuning.jsBatchSize;
  const prefixBytes = prefixToBytes(config.prefix);
  const queueGpuBatch = () => generateGpuCandidateBatch(batchSize, tuning.gpuHashWorkers)
    .catch((error) => {
      if (state.running) throw error;
      return null;
    });
  let nextGpuBatch = scanner ? queueGpuBatch() : null;

  while (state.running) {
    const batch = scanner ? await nextGpuBatch : await generateCandidateBatch(batchSize);
    if (!batch) break;
    if (!state.running) break;
    if (scanner) nextGpuBatch = queueGpuBatch();
    const candidateCount = batch.scalarWords.length / 8;
    let indexes = [...Array(candidateCount).keys()];
    if (scanner && config.hasPrefix) {
      indexes = await scanner.scanBatchMatches(batch.scalarWords, prefixBytes, config.prefix.length);
    }
    state.attempts += candidateCount;

    for (const index of indexes) {
      const clamped = unpackScalarWords(batch.scalarWords, index);
      const privateBytes = new Uint8Array(64);
      privateBytes.set(clamped, 0);
      privateBytes.set(batch.suffixes.slice(index * 32, index * 32 + 32), 32);
      const keypair = {
        publicKey: toHex(derivePublicKeyBytes(clamped)),
        privateKey: toHex(privateBytes)
      };
      const matches = findWatchlistMatches(keypair.publicKey, watchlist);
      if (matches.length) state.watchlistMatches.push({ ...keypair, patterns: matches });
      if (matchesPrimary(keypair.publicKey, config)) {
        state.running = false;
        return { ...keypair, validation: validateKeypair(keypair.privateKey, keypair.publicKey), watchlistMatches: state.watchlistMatches };
      }
    }

    if (limits.maxKeys && state.attempts >= limits.maxKeys) return null;
    if (limits.maxTimeMs && Date.now() - state.startedAt >= limits.maxTimeMs) return null;
    await new Promise((resolve) => setTimeout(resolve, 0));
  }
  return null;
}

function renderWatchlist(matches) {
  document.getElementById('watchlistResult')?.remove();
  if (!matches?.length) return;
  const element = document.createElement('div');
  element.id = 'watchlistResult';
  element.className = 'key-display';
  element.innerHTML = `
    <div class="key-label">Watchlist Matches:</div>
    <div class="key-value">${matches.map((match) => `${match.publicKey.slice(0, 8)}...${match.publicKey.slice(-8)} (${match.patterns.map((p) => p.description || p.pattern).join(', ')})`).join('<br>')}</div>
  `;
  document.querySelector('.stats').before(element);
}

function displayResult(result) {
  state.result = result;
  document.getElementById('publicKey').textContent = result.publicKey;
  document.getElementById('privateKey').textContent = result.privateKey;
  document.getElementById('attemptsCount').textContent = state.attempts.toLocaleString();
  document.getElementById('timeElapsed').textContent = `${((Date.now() - state.startedAt) / 1000).toFixed(1)}s`;
  const elapsed = Math.max((Date.now() - state.startedAt) / 1000, 0.001);
  document.getElementById('keysPerSecond').textContent = Math.round(state.attempts / elapsed).toLocaleString();
  renderWatchlist(result.watchlistMatches);
  resultContainer.style.display = 'block';
  resultContainer.scrollIntoView({ behavior: 'smooth' });
}

function readConfig() {
  const mode = patternModeInput.value;
  const prefix = targetPrefixInput.value.trim().toUpperCase();
  const needsPrefix = mode === 'prefix' || mode === 'simple' || mode.startsWith('prefix-pattern');
  const maxPrefixLength = mode === 'simple' ? 2 : 64;
  if (needsPrefix && !prefix) throw new Error('Please enter a target prefix.');
  if (needsPrefix && (prefix.length < 1 || prefix.length > maxPrefixLength)) throw new Error(`Prefix must be 1-${maxPrefixLength} hex characters.`);
  if (prefix && !/^[0-9A-F]+$/.test(prefix)) throw new Error('Prefix must contain only hexadecimal characters.');
  if (mode === 'simple' && prefix.length !== 2) throw new Error('Simple first-two mode requires exactly 2 hex characters.');
  if (prefix.length >= 2 && RESERVED_PREFIXES.has(prefix.slice(0, 2))) throw new Error('Prefixes starting with 00 or FF are reserved by MeshCore.');
  return modeConfig(mode, prefix);
}

function readTuning() {
  const hardwareThreads = Math.max(1, navigator.hardwareConcurrency || 4);
  return {
    wasmWorkers: parseTuningNumber(wasmWorkerCountInput.value, hardwareThreads, 'WASM workers', 1, Math.max(64, hardwareThreads * 2)),
    wasmBatchSize: parseTuningNumber(wasmBatchSizeInput.value, 4096, 'WASM batch size', 512, 1000000),
    gpuBatchSize: parseTuningNumber(gpuBatchSizeInput.value, 131072, 'GPU batch size', 128, 1000000),
    gpuHashWorkers: parseTuningNumber(gpuHashWorkerCountInput.value, Math.min(6, hardwareThreads), 'GPU hash workers', 1, Math.max(64, hardwareThreads * 2)),
    jsBatchSize: parseTuningNumber(jsBatchSizeInput.value, 192, 'JS batch size', 16, 100000)
  };
}

async function initializeGpuOption() {
  const scanner = await ensureGpuScanner();
  state.gpuAvailable = Boolean(scanner);
  gpuToggleContainer.hidden = false;
  gpuAccelerationToggle.disabled = !state.gpuAvailable;
  gpuAccelerationHint.textContent = state.gpuAvailable
    ? 'GPU acceleration available for prefix and prefix + cosmetic searches up to 64 hex characters.'
    : 'GPU acceleration is not available in this browser.';
}

form.addEventListener('submit', async (event) => {
  event.preventDefault();
  hideError();
  resultContainer.style.display = 'none';
  state.watchlistMatches = [];
  try {
    const config = readConfig();
    const tuning = readTuning();
    const watchlist = parseWatchlist(watchlistInput.value);
    const limits = {
      maxKeys: parseMagnitude(maxKeysInput.value, { K: 1e3, M: 1e6, B: 1e9 }, 1),
      maxTimeMs: parseMagnitude(maxTimeInput.value, { S: 1000, M: 60000, H: 3600000 }, 1000)
    };
    setRunning(true);
    const useGpu = gpuAccelerationToggle.checked && state.gpuAvailable && config.hasPrefix;
    const useWasm = config.mode === 'prefix' || config.mode === 'simple';
    startProgress(config, useGpu ? `webgpu pro | batch ${tuning.gpuBatchSize.toLocaleString()} | ${tuning.gpuHashWorkers} hash workers` : useWasm ? `${tuning.wasmWorkers} wasm workers | batch ${tuning.wasmBatchSize.toLocaleString()}` : `js pro | batch ${tuning.jsBatchSize.toLocaleString()}`);
    const result = useWasm && !watchlist.length && !useGpu
      ? await runWasmPrefixSearch(config, limits, watchlist, tuning)
      : await runJsProSearch(config, limits, watchlist, useGpu, tuning);
    if (result) displayResult(result);
    else showError(state.running ? 'No matching key found before the configured limit.' : 'Key generation was stopped.');
  } catch (error) {
    console.error(error);
    showError(error.message);
  } finally {
    clearInterval(state.progressTimer);
    setRunning(false);
  }
});

stopBtn.addEventListener('click', stopSearch);

downloadBtn.addEventListener('click', () => {
  if (!state.result) return;
  const payload = {
    public_key: state.result.publicKey,
    private_key: state.result.privateKey,
    metadata: {
      mode: patternModeInput.value,
      prefix: targetPrefixInput.value.trim().toUpperCase(),
      watchlist_matches: state.result.watchlistMatches?.map((match) => ({
        public_key: match.publicKey,
        private_key: match.privateKey,
        patterns: match.patterns
      })) || []
    }
  };
  const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const anchor = document.createElement('a');
  anchor.href = url;
  anchor.download = `meshcore_${targetPrefixInput.value.trim().toUpperCase() || patternModeInput.value}_${Date.now()}.json`;
  document.body.appendChild(anchor);
  anchor.click();
  document.body.removeChild(anchor);
  URL.revokeObjectURL(url);
});

targetPrefixInput.addEventListener('input', () => {
  targetPrefixInput.value = targetPrefixInput.value.toUpperCase().replace(/[^0-9A-F]/g, '');
  updateDifficultyEstimate();
});
patternModeInput.addEventListener('change', updateDifficultyEstimate);

importInfoBtn.addEventListener('click', () => { importModal.style.display = 'block'; });
closeModal.addEventListener('click', () => { importModal.style.display = 'none'; });
window.addEventListener('click', (event) => {
  if (event.target === importModal) importModal.style.display = 'none';
});
document.addEventListener('keydown', (event) => {
  if (event.key === 'Escape' && importModal.style.display === 'block') importModal.style.display = 'none';
});

const urlParams = new URLSearchParams(window.location.search);
const urlPrefix = urlParams.get('prefix');
const urlMode = urlParams.get('mode');
if (urlMode && [...patternModeInput.options].some((option) => option.value === urlMode)) patternModeInput.value = urlMode;
if (urlPrefix && /^[0-9A-Fa-f]+$/.test(urlPrefix) && urlPrefix.length <= 64) targetPrefixInput.value = urlPrefix.toUpperCase();
updateDifficultyEstimate();
targetPrefixInput.focus();
initializeGpuOption().catch((error) => console.warn('GPU availability check failed:', error));
