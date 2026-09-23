// Numerical test of the open statements of OmegaY/Official/Recon/JumpLawLower*.lean.
//
// Usage: node jump-law-lower.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md). For every new
// column X = x + w*i of a block i >= 1:
//   LowerLegGe : every node of the lower part (rows below tau) with a leg has leg >= c_r,
//                i.e. its parent is read in a column Y >= x0 (a new column).
// For every pair of consecutive nodes (lambda, theta) of the lower part, theta = bump(lambda, e),
// with parent column Y (the column phi_i(leg of theta)) and T the region of level e + 1 of
// lambda (rows that agree with lambda at the exponents >= e):
//   LowerRowsCopy     (Y = copy of the leg l > c_r in block i)
//   LowerRowsBoundary (Y = c_r + w*i, the copy of x0 in block i - 1)
// both assert RowsConclusion: Y has a node of its lower part in T, and (e >= 1) every such
// node has coefficient e - 1 below that of lambda (for e = 0, T = {lambda}).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {jump, cmp, expandMountain} = O;
const coef = (a, k) => a[k] || 0;

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
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    const {M, R} = r, x0 = s.length - 1;
    if (R.length <= x0) continue;
    expansions++;
    const tc = M[x0][M[x0].length - 1], cr = tc.pc, w = x0 - cr;
    for (let X = x0; X < R.length; X++) {
      const col = R[X], i = col[0].i;
      if (i === 0) continue;
      const lower = col.filter(nd => nd.prov.kind !== 'upper');
      for (const nd of lower) {
        if (nd.pc < 0) continue; // bottom node without a leg
        const ok = nd.pc >= x0;
        bump(`LowerLegGe${ok ? '' : ' FAIL'}`, ok ? null : `(${s})[${n}] X=${X} k=${nd.k}`);
      }
      for (let k = 1; k < lower.length; k++) {
        const lo = lower[k - 1], up = lower[k];
        const e = jump(lo.row, up.row) - 1, Y = up.pc;
        if (Y < x0) continue; // excluded by LowerLegGe
        const kind = Y === cr + w * i ? 'LowerRowsBoundary' : 'LowerRowsCopy';
        const inT = R[Y].filter(nd => nd.prov && nd.prov.kind !== 'upper' && jump(nd.row, lo.row) <= e);
        const ok = inT.length > 0 && (e === 0 || inT.every(nd => coef(nd.row, e - 1) < coef(lo.row, e - 1)));
        bump(`${kind} e${e === 0 ? '=0' : '>=1'}${ok ? '' : ' FAIL'}`, ok ? null : `(${s})[${n}] X=${X} k=${k} Y=${Y}`);
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) {
  console.log(String(stat[k]).padStart(9), k);
  for (const m of ex[k] || []) console.log('            e.g.', m);
}
