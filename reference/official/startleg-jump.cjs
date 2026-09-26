// Numerical tests of the statements of
// OmegaY/Official/Classification/Proofs/ChainCorrStartLegJump.lean.
//
// Usage: node startleg-jump.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                               [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md). Rows are official
// rows (the bottom row is 0). Notation: x0 the last column, t its top, cr the root column
// (the leg of t), w = x0 - cr; a node u of an output column X = x + w i (block i >= 1) has an
// origin o (Trace.lean); the leg of a node is the column of its left end (x - 1 for a bottom
// node); SameRow(A, c, r): column c of A has a node at row r.
//  LegBelowTop          : every node of a column cr < c <= x0 of M(s) with row < row(t) has
//                         its leg >= cr (a fact about M(s) alone).
//  LegRowMatchRootLower : u with a plain or clean (b = 0) origin o whose leg is cr:
//                         SameRow(M, cr, row o) => SameRow(R, cr + w i, row u).
//                         Also counted: row u = row o in that case ("fixed row").
//  StepJump             : u = (X, k), k >= 2 (not bottom) with a non-cut origin o that is not a
//                         bottom node: jump(row u, row u-) <= jump(row o, row o-)
//                         (proved in Lean: stepJump_general).
//  Low                  : the same pairs, in the form used by the proof: the lowest nonzero
//                         coefficient of row u is at most that of row o (for a lower origin).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {mountain, cmp, jump, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3];
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--legal') {
    const [K, V] = args[++a].split(',').map(Number);
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  } else if (args[a] === '--random') {
    let [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
    for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
  } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
}

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hasRow = (A, c, row) => A[c].some(q => cmp(q.row, row) === 0);
const low = r => { for (let k = 0; k < r.length; k++) if (r[k]) return k; return Infinity; };
const isCut = v => v.prov.kind === 'clean' && v.prov.ib;
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  let M;
  try { M = mountain(s); } catch (e) { continue; }
  const x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc;
  if (cr < 0) continue;
  for (let x = cr + 1; x <= x0; x++) for (const nd of M[x]) if (cmp(nd.row, t.row) < 0) {
    const ok = leg(nd) >= cr;
    bump(ok ? 'LegBelowTop ok' : 'FAIL LegBelowTop', ok ? null : `(${s}) x=${x} ${show(nd.row)}`);
  }
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {R} = r, w = x0 - cr;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      if (v.i === 0 || isCut(v)) continue;
      const o = v.prov.src, where = `(${s})[${n}] X=${X} u=${show(v.row)}`;
      if (v.prov.kind !== 'upper' && leg(o) === cr && hasRow(M, cr, o.row)) {
        const ok = hasRow(R, cr + w * v.i, v.row);
        bump(ok ? 'LegRowMatchRootLower ok' : 'FAIL LegRowMatchRootLower', ok ? null : where);
        bump(cmp(v.row, o.row) === 0 ? '  (fixed row: row u = row o)' : '  (row u != row o)');
      }
      if (v.k > 0 && o.k > 0) {
        const a = jump(v.row, R[X][v.k - 1].row), b = jump(o.row, M[o.c][o.k - 1].row);
        bump(a <= b ? 'StepJump ok' : 'FAIL StepJump', a <= b ? null : where);
        if (v.prov.kind !== 'upper') {
          const okL = low(v.row) <= low(o.row);
          bump(okL ? 'Low ok' : 'FAIL Low', okL ? null : where);
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
