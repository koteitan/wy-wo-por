// Numerical test of the reduction of CrossLexFor IsUpper (OmegaY/Official/Recon/CrossUpper.lean).
//
// Usage: node cross-upper.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                             [--random COUNT,MAXLEN,MAXVAL,SEED] [-v N] [SAMPLE.json ...]
//
// For every node u of a new column X = x + w*i whose upper neighbour u+ has an upper origin,
// with p = the stored parent of u+ and q = Q u in another column than p (the cross case):
//   N  = the node of the column x' (x' = x, or c_r for x = x0) of M(s) copied to u+,
//   n0 = the node below N in M(s), np = the stored parent of N, qM = Q_M(n0),
//   f  = shiftCol c_r w i (c -> c + w*i for c >= c_r).
// The cases of crossLexFor_upper:
//   * row u >= tau and every node of the chain qM -> ... -> np (except np) is copied
//     (left of c_r, or at a row >= tau): proved (chain_transport). The test checks that the
//     chain of R from q reaches the node below the copy of cM+ (as the proof builds it).
//   * x = x0 and row u < tau: SeamLastHolds, proved for i = 0 (seamLast_block0,
//     CrossUpperSeam.lean), open for i >= 1 (SeamLastPosHolds). The chain from q reaches a
//     node c whose upper node cp is in the column c_r + w*i at the row of u+.
//   * x != x0, and row u < tau or the chain of M is not copied: InnerHolds. The chain of M
//     from qM reaches cM with stored parent np, and the chain of R from q reaches a node c
//     whose upper node cp is in the column f(col cM) at the row of u+.
// It also checks the facts the proof derives: the stored parent of c+ is p, and Lex(u+, c+).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], verbose = 0;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '-v') verbose = +args[++a];
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

const same = (a, b) => !!a && !!b && a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const parentOf = (A, v) => v.pc >= 0 ? A[v.pc][v.pk] : null; // stored left end of v
const rawParent = (A, z) => { const v = above(A, z); return v ? parentOf(A, v) : null; };
function Qof(A, u) {
  const lc = u.k === 0 ? u.c - 1 : u.pc, col = A[lc];
  let k = u.k === 0 ? -1 : u.pk;
  while (k + 1 < col.length && cmp(col[k + 1].row, u.row) <= 0) k++;
  return k < 0 ? null : col[k];
}
function lex(A, z, w) {
  for (;;) {
    const zu = above(A, z); if (!zu) return true;
    const wu = above(A, w); if (!wu) return false;
    const a = parentOf(A, zu), b = parentOf(A, wu);
    if (a.c < b.c) return true;
    if (!(same(a, b) && cmp(zu.row, wu.row) === 0)) return false;
    z = zu; w = wu;
  }
}
// the nodes of the chain of stored parents from a, in order, while the column is >= lo
function chainFrom(A, a, lo) { const out = []; let z = a; while (z && z.c >= lo) { out.push(z); z = rawParent(A, z); } return out; }

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < verbose) ex[k].push(msg); };
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    const {R, M, root} = r, x0 = s.length - 1;
    if (!root) continue;
    expansions++;
    const cr = root.c, w = x0 - cr, tau = M[x0][M[x0].length - 1].row;
    for (let X = x0; X < R.length; X++) for (let k = 0; k + 1 < R[X].length; k++) {
      const u = R[X][k], up = R[X][k + 1];
      if (up.prov.kind !== 'upper') continue;
      const p = parentOf(R, up), q = Qof(R, u);
      if (q.c === p.c) continue;
      const x = up.x, i = up.i, f = c => c >= cr ? c + w * i : c;
      const where = `(${s})[${n}] X=${X} i=${i} u=${show(u.row)} u+=${show(up.row)} tau=${show(tau)}`;
      const N = M[up.prov.src.c][up.prov.src.k], n0 = M[N.c][N.k - 1], np = parentOf(M, N), qM = Qof(M, n0);
      if (X !== x + w * i || N.c !== (x === x0 ? cr : x) || cmp(N.row, up.row) !== 0) { bump('FAIL setup', where); continue; }
      const uUpper = cmp(u.row, tau) >= 0;
      // the chain of M from qM to np
      const mch = chainFrom(M, qM, np.c);
      const cMidx = mch.findIndex(z => same(rawParent(M, z), np));
      const cM = cMidx >= 0 ? mch[cMidx] : null;
      const copied = cM !== null && mch.slice(0, cMidx + 1).every(z => z.c < cr || cmp(z.row, tau) >= 0);
      let kind, col;
      if (uUpper && copied) { kind = x === x0 ? 'proved: x = x0, row u >= tau' : 'proved: x != x0, row u >= tau, chain copied'; col = cM ? f(cM.c) : null; }
      else if (x === x0 && !uUpper) { kind = i === 0 ? 'proved: seam of block 0 (seamLast_block0)' : 'open SeamLastPosHolds'; col = cr + w * i; }
      else if (x !== x0) { kind = 'open InnerHolds'; col = cM ? f(cM.c) : null; }
      else { bump('FAIL no case (x = x0, u upper, chain not copied)', where); continue; }
      if (col === null) { bump(`FAIL ${kind}: no cM on the chain of M`, where); continue; }
      // the chain of R from q, down to the column of the copy of cM+
      const rch = chainFrom(R, q, col);
      const c = rch.find(z => { const zp = above(R, z); return zp && zp.c === col && cmp(zp.row, up.row) === 0; });
      if (!c) { bump(`FAIL ${kind}`, where); continue; }
      const cp = above(R, c);
      const derived = same(parentOf(R, cp), p) && lex(R, up, cp);
      bump(derived ? `ok ${kind}` : `FAIL ${kind}: parent or Lex`, derived ? null : where);
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
