// Numerical test of AscLeg, a statement about M(s) alone (used for NonCutOrderLeg,
// OmegaY/Official/Classification/Proofs/CopyShapeProfileLeg*.lean).
//
// Usage: node asc-leg.cjs [--legal MAXLEN,MAXVAL] [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// cr = root column, x0 = last column, tau = top row of x0. For a column x in (cr, x0], a node v
// of x (the bottom node included) with leg column l (column of the left end of v, x - 1 for the
// bottom node), cr <= l, a node u of x at or below v with row u < tau, and a region S = S_d(u)
// (2 <= d <= k + 1, k the highest exponent where row u and tau differ) whose root-column top rho
// is below u:
//  AscLeg      x ascends in S iff l ascends in S.
//  AscLegGt    the same, restricted to cr < l.
//  AscLegEq    the same, restricted to l = cr.
//  (information) AscLegOwn: the same with u = v or leg(u) = l (the case of ascAgree).
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
const asc = (M, x, cr, rho) => {
  const ref = coef(rho.row, 0) > 0 ? norm([coef(rho.row, 0) - 1, ...rho.row.slice(1)]) : rho.row;
  let a = nodeAt(M, x, ref);
  while (a && a.c > cr) a = rowParent(M, a);
  return !!a && a.c === cr;
};
const seen = new Set();
let legal = 0;
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
    M[x].forEach((v, kv) => {
      const l = legOf(v);
      if (l < cr) return;
      for (let ku = 0; ku <= kv; ku++) {
        const u = M[x][ku];
        if (cmp(u.row, tau) >= 0) continue;
        let kk = Math.max(u.row.length, tau.length) - 1;
        while (kk >= 0 && coef(u.row, kk) === coef(tau, kk)) kk--;
        for (let d = 2; d <= kk + 1; d++) {
          const b = norm(u.row.map((c, j) => j < d - 1 ? 0 : c));
          const rho = topIn(M, cr, d, b);
          if (!rho || cmp(u.row, rho.row) <= 0) continue;
          const ok = asc(M, x, cr, rho) === asc(M, l, cr, rho);
          const msg = `(${s}) v=(${x},${show(v.row)}) l=${l} u=${show(u.row)} d=${d} rho=${show(rho.row)} asc(x)=${asc(M, x, cr, rho)}`;
          bump('AscLeg', ok, msg);
          bump(l > cr ? 'AscLegGt' : 'AscLegEq', ok, msg);
          if (ku === kv || legOf(u) === l) bump('AscLegOwn', ok, msg);
        }
      }
    });
  }
}
console.log(`inputs ${seen.size}, legal ${legal}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(11), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
