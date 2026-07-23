const { Worker, isMainThread, parentPort, workerData } = require('worker_threads');
const os = require('os');
const fs = require('fs');

const V = 167;
const HALF = 83;
const PATTERNS = [
  [15, 15, 13, 7], [17, 17, 9, 3], [19, 15, 9, 1], [19, 17, 3, 3],
  [21, 11, 9, 5], [21, 13, 7, 3], [21, 15, 1, 1], [23, 9, 7, 3],
  [23, 11, 3, 3], [25, 5, 3, 3],
];

function rng(seed) {
  let x = Number(BigInt(seed) & 0xffffffffn) >>> 0;
  if (x === 0) x = 0x9e3779b9;
  return () => {
    x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
    return (x >>> 0) / 0x100000000;
  };
}

function shuffle(a, random) {
  for (let i = a.length - 1; i > 0; --i) {
    const j = Math.floor(random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
}

function initialSequence(sum, random) {
  const negatives = (V - sum) / 2;
  const a = new Int8Array(V); a.fill(1);
  const indices = Array.from({length: V}, (_, i) => i);
  shuffle(indices, random);
  for (let i = 0; i < negatives; i++) a[indices[i]] = -1;
  return a;
}

function combinedPaf(sequences) {
  const s = new Int16Array(HALF + 1);
  for (let d = 1; d <= HALF; d++) {
    let total = 0;
    for (const a of sequences) for (let i = 0; i < V; i++) total += a[i] * a[(i + d) % V];
    s[d] = total;
  }
  return s;
}

function energy(s) {
  let e = 0;
  for (let d = 1; d <= HALF; d++) e += s[d] * s[d];
  return e;
}

function l1(s) {
  let e = 0;
  for (let d = 1; d <= HALF; d++) e += Math.abs(s[d]);
  return e;
}

function flip(a, p, s) {
  const xp = a[p];
  for (let d = 1; d <= HALF; d++) {
    const plus = p + d < V ? p + d : p + d - V;
    const minus = p - d >= 0 ? p - d : p - d + V;
    s[d] += -2 * xp * (a[plus] + a[minus]);
  }
  a[p] = -xp;
}

function pickSign(a, sign, random) {
  for (;;) {
    const p = Math.floor(random() * V);
    if (a[p] === sign) return p;
  }
}

function verify(sequences) {
  const s = combinedPaf(sequences);
  return energy(s) === 0;
}

function search() {
  const random = rng(workerData.seed);
  const deadline = Date.now() + workerData.runtimeMs;
  let bestEnergy = Infinity;
  let bestSequences = null;
  let iterations = 0;
  let restarts = 0;
  while (Date.now() < deadline) {
    const pattern = PATTERNS[(workerData.workerId + restarts * workerData.workers) % PATTERNS.length];
    const sequences = pattern.map(sum => initialSequence(sum, random));
    const s = combinedPaf(sequences);
    const useL1 = (workerData.workerId & 1) === 1;
    let current = useL1 ? l1(s) : energy(s);
    const steps = 750000;
    for (let step = 0; step < steps && Date.now() < deadline; step++, iterations++) {
      const moves = [];
      const moveCount = random() < 0.08 ? 2 : 1;
      for (let m = 0; m < moveCount; m++) {
        const which = Math.floor(random() * 4);
        const a = sequences[which];
        const p = pickSign(a, 1, random);
        const q = pickSign(a, -1, random);
        flip(a, p, s); flip(a, q, s);
        moves.push([a, p, q]);
      }
      const next = useL1 ? l1(s) : energy(s);
      const phase = step / steps;
      const temperature = (useL1 ? 30 : 700) * Math.pow(0.0001, phase) + 0.02;
      if (next <= current || random() < Math.exp((current - next) / temperature)) {
        current = next;
      } else {
        for (let m = moves.length - 1; m >= 0; m--) {
          const [a, p, q] = moves[m];
          flip(a, q, s); flip(a, p, s);
        }
      }
      const exactEnergy = energy(s);
      if (exactEnergy < bestEnergy) {
        bestEnergy = exactEnergy;
        bestSequences = sequences.map(x => Array.from(x));
        parentPort.postMessage({type:'best', workerId:workerData.workerId, seed:String(workerData.seed), pattern, objective:useL1?'l1':'l2', energy:bestEnergy, iterations, restarts});
        if (bestEnergy === 0) {
          if (!verify(sequences)) throw new Error('incremental state disagrees with exact verification');
          parentPort.postMessage({type:'found', workerId:workerData.workerId, seed:String(workerData.seed), pattern, energy:0, iterations, restarts, sequences:bestSequences});
          return;
        }
      }
    }
    restarts++;
  }
  parentPort.postMessage({type:'done', workerId:workerData.workerId, seed:String(workerData.seed), energy:bestEnergy, iterations, restarts, sequences:bestSequences});
}

if (!isMainThread) {
  search();
} else {
  const runtimeMs = Number(process.argv[2] || 300000);
  const workerCount = Math.min(Number(process.argv[3] || os.availableParallelism()), 12);
  const started = new Date().toISOString();
  let active = workerCount;
  let globalBest = Infinity;
  let bestRecord = null;
  let solved = false;
  const workers = [];
  for (let i = 0; i < workerCount; i++) {
    const seed = BigInt(Date.now()) * 1000n + BigInt(i + 1);
    const worker = new Worker(__filename, {workerData:{workerId:i, workers:workerCount, runtimeMs, seed:String(seed)}});
    workers.push(worker);
    worker.on('message', message => {
      if (message.energy < globalBest || (message.type === 'done' && message.energy === globalBest)) {
        globalBest = message.energy;
        bestRecord = message;
        const printable = {...message, elapsedMs:Date.now()-Date.parse(started)};
        delete printable.sequences;
        process.stdout.write(JSON.stringify(printable) + '\n');
      }
      if (message.type === 'found' && !solved) {
        solved = true;
        fs.writeFileSync('Find a Hadamard matrix of order 668/gs_167_candidate.json', JSON.stringify({...message, started, finished:new Date().toISOString()}, null, 2));
        for (const w of workers) if (w !== worker) w.terminate();
      }
      if (message.type === 'done' || message.type === 'found') {
        active--;
        if (active === 0 || solved) {
          fs.writeFileSync('Find a Hadamard matrix of order 668/gs_167_search_summary.json', JSON.stringify({started, finished:new Date().toISOString(), runtimeMs, workerCount, solved, globalBest, bestRecord}, null, 2));
        }
      }
    });
  }
}
