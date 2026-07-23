const fs = require('fs');
const crypto = require('crypto');

const N = 107;
const TURYN_HEX = '060989975b685d8fc80750b21c0212eceb26';

function decodeTurynType(hex) {
  const seqs = [[], [], [], []];
  for (const c of hex.slice(0, -1)) {
    const bits = Number.parseInt(c, 16).toString(2).padStart(4, '0');
    for (let s = 0; s < 4; s++) seqs[s].push(bits[s] === '0' ? 1 : -1);
  }
  const last = Number.parseInt(hex.at(-1), 16).toString(2).padStart(3, '0');
  for (let s = 0; s < 3; s++) seqs[s].push(last[s] === '0' ? 1 : -1);
  return seqs;
}

function tSequences() {
  const [x, y, z, w] = decodeTurynType(TURYN_HEX);
  const a = z.concat(w);
  const b = z.concat(w.map(v => -v));
  const c = x;
  const d = y;
  const halfSum = (u, v) => u.map((value, i) => (value + v[i]) / 2);
  const halfDiff = (u, v) => u.map((value, i) => (value - v[i]) / 2);
  const zeros = length => Array(length).fill(0);
  return [
    halfSum(a, b).concat(zeros(36)),
    halfDiff(a, b).concat(zeros(36)),
    zeros(71).concat(halfSum(c, d)),
    zeros(71).concat(halfDiff(c, d)),
  ];
}

function circulant(firstRow) {
  return Array.from({length: N}, (_, i) =>
    Array.from({length: N}, (_, j) => firstRow[(j - i + N) % N]));
}

function transpose(a) {
  return a[0].map((_, j) => a.map(row => row[j]));
}

function negate(a) {
  return a.map(row => row.map(v => -v));
}

function timesR(a) {
  return a.map(row => row.toReversed());
}

function goethalsSeidel(a, b, c, d) {
  const bt = transpose(b);
  const ct = transpose(c);
  const dt = transpose(d);
  const blocks = [
    [a, timesR(b), timesR(c), timesR(d)],
    [negate(timesR(b)), a, negate(timesR(dt)), timesR(ct)],
    [negate(timesR(c)), timesR(dt), a, negate(timesR(bt))],
    [negate(timesR(d)), negate(timesR(ct)), timesR(bt), a],
  ];
  return Array.from({length: 4 * N}, (_, i) =>
    Array.from({length: 4 * N}, (_, j) => blocks[Math.floor(i / N)][Math.floor(j / N)][i % N][j % N]));
}

function addMatrices(matrices) {
  return matrices[0].map((row, i) => row.map((_, j) => matrices.reduce((sum, m) => sum + m[i][j], 0)));
}

function construct() {
  const [s1, s2, s3, s4] = tSequences();
  const [x1, x2, x3, x4] = [s1, s2, s3, s4].map(circulant);
  return addMatrices([
    goethalsSeidel(x1, x2, x3, x4),
    goethalsSeidel(x2, negate(x1), x4, negate(x3)),
    goethalsSeidel(x3, negate(x4), negate(x1), x2),
    goethalsSeidel(x4, x3, negate(x2), negate(x1)),
  ]);
}

function constructPrecombined() {
  const [s1, s2, s3, s4] = tSequences();
  const combined = [
    s1.map((_, i) => s1[i] + s2[i] + s3[i] + s4[i]),
    s1.map((_, i) => -s1[i] + s2[i] + s3[i] - s4[i]),
    s1.map((_, i) => -s1[i] - s2[i] + s3[i] + s4[i]),
    s1.map((_, i) => -s1[i] + s2[i] - s3[i] + s4[i]),
  ].map(circulant);
  return goethalsSeidel(...combined);
}

function verify(h) {
  if (h.length !== 428 || h.some(row => row.length !== 428)) throw new Error('wrong dimensions');
  if (h.some(row => row.some(v => v !== 1 && v !== -1))) throw new Error('entry outside {-1,+1}');
  for (let i = 0; i < 428; i++) {
    for (let j = i; j < 428; j++) {
      let dot = 0;
      for (let k = 0; k < 428; k++) dot += h[i][k] * h[j][k];
      const expected = i === j ? 428 : 0;
      if (dot !== expected) throw new Error(`bad dot product (${i}, ${j}): ${dot}`);
    }
  }
}

const matrix = construct();
const proofSearchMatrix = constructPrecombined();
if (matrix.some((row, i) => row.some((v, j) => v !== proofSearchMatrix[i][j]))) {
  throw new Error('CSV construction differs from the precombined Proof Search witness');
}
verify(matrix);
const csv = matrix.map(row => row.join(',')).join('\n') + '\n';
fs.writeFileSync('hadamard_428.csv', csv, 'utf8');
const sha256 = crypto.createHash('sha256').update(csv).digest('hex');
console.log(JSON.stringify({rows: 428, columns: 428, entries: [-1, 1], verified: true, sha256}, null, 2));
