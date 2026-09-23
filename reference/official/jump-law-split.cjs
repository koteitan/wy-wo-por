// Numerical test of the jump law of the new columns, split as in
// OmegaY/Official/Recon/JumpLaw*.lean.
//
// Usage: node jump-law-split.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md). For every new
// column X >= x0 and every pair of consecutive nodes (lower, upper) of X (lower real), with
// upper = lower + w^e and p the node read as the parent of upper (the highest node of the
// column phi_i(leg) below upper), it checks jump(row lower, row p) = e (RowLaw.JumpLawHolds)
// and counts the pair in the case of the Lean proof:
//   block0     : X = x0 (block 0)                            proved (colJump_block0)
//   upper      : upper in the upper part, not the seam at tau proved (colJump_upper)
//   seamTau    : upper is the first upper node and row tau   proved (seamTauHolds)
//   lowerPairs : both nodes in the lower part, block >= 1     open   (LowerPairsHolds)
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {jump, eq, expandMountain} = O;

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
    const tau = M[x0][M[x0].length - 1].row;
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      const nLower = col.filter(nd => nd.prov.kind !== 'upper').length;
      for (let k = 1; k < col.length; k++) {
        const lo = col[k - 1], up = col[k], p = R[up.pc][up.pk];
        const e = jump(lo.row, up.row) - 1;
        let cat;
        if (col[0].i === 0) cat = 'block0';
        else if (k < nLower) cat = 'lowerPairs';
        else if (k === nLower && eq(up.row, tau)) cat = 'seamTau';
        else cat = 'upper';
        const ok = jump(lo.row, p.row) === e;
        bump(`${cat}${ok ? '' : ' FAIL'}`, ok ? null : `(${s})[${n}] X=${X} k=${k}`);
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
let total = 0;
for (const k of Object.keys(stat).sort()) {
  if (k !== 'expansion error') total += stat[k];
  console.log(String(stat[k]).padStart(9), k);
  for (const m of ex[k] || []) console.log('            e.g.', m);
}
console.log(String(total).padStart(9), 'pairs');
