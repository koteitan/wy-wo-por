// Numerical test of MALeg, a statement about M(s) alone: (MA) (FactMA of CopyShapeItems.lean)
// fails only at nodes whose leg is left of the root column.
//
// Usage: node ma-leg.cjs [--legal MAXLEN,MAXVAL] [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// Let cr be the root column, x0 the last column, tau the top row of x0. For a column x in
// (cr, x0] and a node u of x below tau, the regions of u that the rule reaches are the regions
// S_d(u) (level d, the rows that agree with row u at the exponents >= d - 1) for 2 <= d <= k + 1,
// where k is the highest exponent at which row u and tau differ (then row u < tau there; the
// region of level k + 1 is a lower item). u is an (MA) failure when for such a d, the root
// column has a node in S_d(u) (rho = its top), row u > row rho, and x does not ascend in S_d(u).
//  MALeg        every (MA) failure u has leg column < cr (leg = column of the left end of u,
//               x - 1 for the bottom node).
//  MALegBelow   (equivalent form) no (MA) failure lies at or below a node of x with leg >= cr.
//  MAfail       (information) the number of (MA) failures.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, mountain, nodeAt, rowParent, norm} = O;

const args = process.argv.slice(2);
const inputs = [];
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--legal') {
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
const bump = (k, ok, msg) => { const key = (ok ? '' : 'FAIL ') + k; stat[key] = (stat[key] || 0) + 1; if (!ok && msg && (ex[key] = ex[key] || []).length < 3) ex[key].push(msg); };
const coef = (a, k) => a[k] || 0;
const legOf = nd => nd.pc >= 0 ? nd.pc : nd.c - 1;
const inRegion = (row, d, b) => { for (let k = d - 1; k < Math.max(row.length, b.length); k++) if (coef(row, k) !== coef(b, k)) return false; return true; };
const topIn = (M, c, d, b) => { let best = null; for (const n of M[c] || []) if (inRegion(n.row, d, b)) best = n; return best; };
const seen = new Set();
let legal = 0, nodes = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  let M;
  try { M = mountain(s); } catch (e) { continue; }
  legal++;
  const x0 = s.length - 1, tc = M[x0][M[x0].length - 1];
  if (tc.pc < 0) continue;
  const cr = tc.pc, tau = tc.row;
  for (let x = cr + 1; x <= x0; x++) {
    const bad = M[x].map(() => false);
    M[x].forEach((u, k) => {
      if (cmp(u.row, tau) >= 0) return;
      nodes++;
      let kk = Math.max(u.row.length, tau.length) - 1;
      while (kk >= 0 && coef(u.row, kk) === coef(tau, kk)) kk--;
      for (let d = 2; d <= kk + 1; d++) {
        const b = norm(u.row.map((v, j) => j < d - 1 ? 0 : v));
        const rho = topIn(M, cr, d, b);
        if (!rho || cmp(u.row, rho.row) <= 0) continue;
        const ref = coef(rho.row, 0) > 0 ? norm([coef(rho.row, 0) - 1, ...rho.row.slice(1)]) : rho.row;
        let a = nodeAt(M, x, ref);
        while (a && a.c > cr) a = rowParent(M, a);
        if (!!a && a.c === cr) continue;
        bad[k] = true;
        bump('MAfail', true);
        bump('MALeg', legOf(u) < cr, `(${s}) u=(${x},${show(u.row)}) d=${d} rho=${show(rho.row)} leg=${legOf(u)} cr=${cr}`);
        break;
      }
    });
    // MALegBelow: no failure at or below a node with leg >= cr
    let seenGe = false;
    for (let k = M[x].length - 1; k >= 0; k--) {
      if (legOf(M[x][k]) >= cr) seenGe = true;
      if (bad[k]) bump('MALegBelow', !seenGe, `(${s}) u=(${x},${show(M[x][k].row)})`);
    }
  }
}
console.log(`inputs ${seen.size}, legal ${legal}, nodes below tau ${nodes}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(11), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
