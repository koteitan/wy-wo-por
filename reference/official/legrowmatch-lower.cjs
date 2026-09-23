// Numerical tests of the statements of
// OmegaY/Official/Classification/Proofs/LegRowMatchLower.lean.
//
// Usage: node legrowmatch-lower.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                   [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md). Rows are official
// rows (the bottom row is 0). x0 the last column, t its top (row tau), cr the root column,
// w = x0 - cr; the boundary column of block i >= 1 is cr + w i (the copy of x0 by block i - 1).
//  RowFixed         : a node u of an output column (block i >= 1) whose origin o is plain or a
//                     non-cut clean copy, and whose origin row is a row of cr, has row u = row o
//                     (proved: RowFix.emitsT_fixed).
//  BoundaryRootRows : for every block i >= 1 and every node of cr with row < tau, the boundary
//                     column cr + w i has a node at that row.
//  TopAboveRoot     : for every region S (level d >= 2) below tau containing a node of cr, the
//                     top of x0 in S is strictly higher (height = coefficient d - 2) than the
//                     top of cr in S (a fact about M(s) alone).
//  LegRowMatchRootLower : the statement of ChainCorrStartLegJump.lean (tested as there).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {mountain, cmp, show, expandMountain, addPow, norm} = O;

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
const coef = (a, k) => a[k] || 0;
const inRegion = (row, d, b) => { for (let k = d - 1; k < Math.max(row.length, b.length) + 1; k++) if (coef(row, k) !== coef(b, k)) return false; return true; };
const hasRow = (A, c, row) => A[c].some(q => cmp(q.row, row) === 0);
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  let M;
  try { M = mountain(s); } catch (e) { continue; }
  const x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, tau = t.row;
  if (cr < 0) continue;
  // TopAboveRoot
  for (const q of M[cr]) {
    if (cmp(q.row, tau) >= 0) continue;
    for (let d = 2; d <= Math.max(q.row.length, tau.length) + 2; d++) {
      const base = norm(q.row.map((v, k) => k < d - 1 ? 0 : v));
      if (cmp(addPow(base, d - 1), tau) > 0) continue;
      const topOf = c => { let b = null; for (const n of M[c]) if (inRegion(n.row, d, base)) b = n; return b; };
      const rho = topOf(cr), kap = topOf(x0);
      const ok = kap && coef(kap.row, d - 2) > coef(rho.row, d - 2);
      bump(ok ? 'TopAboveRoot ok' : 'FAIL TopAboveRoot', ok ? null : `(${s}) d=${d} base=${show(base)}`);
    }
  }
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {R} = r, w = x0 - cr;
    for (let i = 1; i <= n; i++) {
      const B = cr + w * i;
      if (B >= R.length) continue;
      for (const q of M[cr]) if (cmp(q.row, tau) < 0) {
        const ok = hasRow(R, B, q.row);
        bump(ok ? 'BoundaryRootRows ok' : 'FAIL BoundaryRootRows', ok ? null : `(${s})[${n}] i=${i} ${show(q.row)}`);
      }
    }
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      if (v.i === 0 || v.prov.kind === 'upper' || (v.prov.kind === 'clean' && v.prov.ib)) continue;
      const o = v.prov.src, where = `(${s})[${n}] X=${X} u=${show(v.row)}`;
      if (hasRow(M, cr, o.row)) {
        const ok = cmp(v.row, o.row) === 0;
        bump(ok ? 'RowFixed ok' : 'FAIL RowFixed', ok ? null : where);
        if (leg(o) === cr) {
          const ok2 = hasRow(R, cr + w * v.i, v.row);
          bump(ok2 ? 'LegRowMatchRootLower ok' : 'FAIL LegRowMatchRootLower', ok2 ? null : where);
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
