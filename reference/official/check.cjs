// Differential and self-consistency test for omegay.cjs.
//
// Usage:
//   node check.cjs [--oracle PATH/script.js] [--copies 1,2,3] [--random COUNT,MAXLEN,MAXVAL,SEED]
//                  [--legal MAXLEN,MAXVAL] [--save FILE] [--coverage] [SAMPLE.json ...]
//
// Inputs: sample files (JSON arrays of sequences), all legal sequences (1,a_1,...,a_k)
// with k+1 <= MAXLEN and a_i <= MAXVAL (--legal), and random legal sequences (--random).
// Sequences ending in 1 are skipped (the expansion only deletes the last entry).
//
// --coverage prints how often each branch of the rule (notes/03-official-rule.md) ran:
// plain / lifted / lifted-ib / clean at each region level, and the two ways of
// counting generations.
//
// Checks for every expansion s[n]:
//   (a) the mountain built by the expansion equals the canonical mountain of the output
//       (rows and parent positions of every node);
//   (b) s[n] < s in the lexicographic order;
//   (c) with --oracle: the values agree with the definition, Naruyoko's program
//       StudyAndExpandSequence (https://github.com/Naruyoko/StudyAndExpandSequence).
//       Pass the path of its script.js in a local clone. It is only executed as a black
//       box in a sandbox; nothing of it is part of this repository. Expansions whose
//       official values reach 2^53 are skipped (that program uses floating point).
//       An input on which both programs throw counts as agreement (oracleError).
'use strict';
const fs = require('fs'), vm = require('vm');
const O = require('./omegay.cjs');

const args = process.argv.slice(2);
const opt = {copies: [1, 2, 3], files: []};
for (let a = 0; a < args.length; a++) {
  const k = args[a];
  if (k === '--oracle') opt.oracle = args[++a];
  else if (k === '--copies') opt.copies = args[++a].split(',').map(Number);
  else if (k === '--random') opt.random = args[++a].split(',').map(Number);
  else if (k === '--legal') opt.legal = args[++a].split(',').map(Number);
  else if (k === '--save') opt.save = args[++a];
  else if (k === '--coverage') opt.coverage = true;
  else opt.files.push(k);
}

function loadOracle(path) {
  const el = {value: '', checked: false, textContent: '', innerHTML: '', addEventListener() {}, style: {}};
  const box = {document: {getElementById: () => el}, window: {}, console: {log() {}, warn() {}, clear() {}}};
  vm.createContext(box);
  vm.runInContext(fs.readFileSync(path, 'utf8') + '\n;this.__expand = expand;', box);
  return (seq, n) => { const t = box.__expand(seq.join(','), n, false, true); return t === '' ? [] : t.split(',').map(Number); };
}
const oracle = opt.oracle ? loadOracle(opt.oracle) : null;

const inputs = [];
for (const f of opt.files) for (const s of JSON.parse(fs.readFileSync(f, 'utf8'))) inputs.push(s);
if (opt.legal) {
  const [K, V] = opt.legal;
  const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
  rec([1]);
}
if (opt.random) {
  let [count, maxLen, maxVal, seed] = opt.random;
  const rnd = () => { // mulberry32
    seed = (seed + 0x6D2B79F5) | 0; let t = seed;
    t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  for (let t = 0; t < count; t++) {
    const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1];
    while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal));
    inputs.push(s);
  }
}
if (opt.save) fs.writeFileSync(opt.save, JSON.stringify(inputs));

const lexLess = (a, b) => { for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] < b[i]; return a.length < b.length; };
function sameMountain(A, B) {
  if (A.length !== B.length) return false;
  for (let c = 0; c < A.length; c++) {
    if (A[c].length !== B[c].length) return false;
    for (let k = 0; k < A[c].length; k++) {
      const a = A[c][k], b = B[c][k];
      if (!O.eq(a.row, b.row) || a.pc !== b.pc) return false;
      if (a.pc >= 0 && !O.eq(A[a.pc][a.pk].row, B[b.pc][b.pk].row)) return false;
    }
  }
  return true;
}

const stat = {expansions: 0, error: 0, mountain: 0, lex: 0, oracleAgree: 0, oracleDiffer: 0, oracleSkipped: 0, oracleError: 0};
const fails = [];
const seen = new Set();
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of opt.copies) {
    stat.expansions++;
    let R, N = null, nerr = null;
    if (oracle) { try { N = oracle(s, n); } catch (e) { nerr = e; } }
    try { R = O.expandMountain(s, n).R; } catch (e) {
      stat.error++;
      if (nerr) stat.oracleError++; else fails.push(`(${s})[${n}] error: ${e.message}`);
      continue;
    }
    const out = R.map(col => col[0].value);
    if (sameMountain(R, O.mountain(out))) stat.mountain++; else fails.push(`(${s})[${n}] built mountain is not canonical`);
    if (lexLess(out, s.map(BigInt))) stat.lex++; else fails.push(`(${s})[${n}] not smaller`);
    if (oracle) {
      if (nerr) { stat.oracleError++; fails.push(`(${s})[${n}] official program fails, ours succeeds`); continue; }
      if (N.some(v => !(v < 2 ** 53))) stat.oracleSkipped++;
      else if (N.join(',') === out.join(',')) stat.oracleAgree++;
      else { stat.oracleDiffer++; fails.push(`(${s})[${n}] official ${N} ours ${out}`); }
    }
  }
}
console.log(JSON.stringify({sequences: seen.size, ...stat}));
if (opt.coverage) console.log(JSON.stringify(Object.fromEntries(Object.entries(O.counters).sort())));
for (const f of fails.slice(0, 20)) console.log(f);
process.exit(fails.length ? 1 : 0);
