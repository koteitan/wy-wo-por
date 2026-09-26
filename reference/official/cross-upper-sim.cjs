// Numerical test of the open statements of OmegaY/Official/Recon/CrossUpperSim*.lean.
//
// Usage: node cross-upper-sim.cjs [--trace] [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//          [--legal-sample LEN,MAXVAL,COUNT,SEED] [--shard K/N] [--random COUNT,MAXLEN,MAXVAL,SEED]
//          [--max-cells N] [--max-mountain N] [--progress K] [-v N] [SAMPLE.json ...]
// --max-mountain skips the inputs whose mountain M(s) has more than N nodes (before expanding);
// --max-cells skips the expansions with more than N nodes; both are reported as skipped.
//
// Block i >= 1 of the expansion s[n], w = x0 - c_r, f(c) = c + w*i for c >= c_r.
// A copy of a node z of M(s) in a column X = y + w*i (y a column of block i) is a node of X whose
// origin (plain, clean, cut or upper) has the source z. The top copy of z is the highest one.
// The relation Cp(Z, z) (Z of the output R, z of M(s)):
//   z.c <  c_r      : Z is z (same column, same row);
//   z.c =  c_r      : Z is in the column c_r + w*i; if the node z+ above z has a row >= tau,
//                     then the node Z+ above Z has the row of z+; and if z has a stored parent b
//                     (the stored parent of z+, left of c_r), the chain of stored parents of R
//                     from Z reaches b;
//   c_r < z.c < x0  : Z is in the column f(z.c); if row z >= tau, row Z = row z; if row z < tau,
//                     Z is the top copy of z.
// Checked statements:
//   Emitted       (LowerPB.Emitted on the existing columns) every node of y below tau is the
//                 origin of a non-cut lower copy in X = y + w*i.
//   CopyTop       the top node of the lower part (rows < tau) of a column X = y + w*i of block i
//                 is the top copy of the top node of the lower part of y.
//   CopyStepLower (split by the row of z+; the case z+ < tau is CopyStepLow)
//                 for a top copy Z of a node z with row < tau, c_r < z.c < x0, and a = the stored
//                 parent of z+ in M(s): the stored parent A of Z+ exists and Cp(A, a).
//   CopyQLower    for a top copy U of a real node z with row < tau, c_r < z.c <= x0, whose upper
//                 node z+ has a row >= tau: Q_R(U) and Q_M(z) both exist and Cp(Q_R(U), Q_M(z)).
//                 (Reported also for the other z, where it fails: Q_R(U) can be the first copy
//                 of Q_M(z) instead of the top copy.)
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let trace = false, copies = [1, 2, 3], verbose = 2, maxCells = Infinity, maxMountain = Infinity, progress = 0, shardK = 0, shardN = 1;
const rng = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '-v') verbose = +args[++a];
  else if (args[a] === '--trace') trace = true;
  else if (args[a] === '--max-cells') maxCells = +args[++a];
  else if (args[a] === '--max-mountain') maxMountain = +args[++a];
  else if (args[a] === '--progress') progress = +args[++a];
  else if (args[a] === '--shard') [shardK, shardN] = args[++a].split('/').map(Number);
  else if (args[a] === '--legal') {
    const [K, V] = args[++a].split(',').map(Number);
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  } else if (args[a] === '--legal-sample') {
    // COUNT sequences drawn uniformly from the sequences (1, a_1, ..., a_{LEN-1}), a_j <= MAXVAL
    const [K, V, count, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const s = [1]; while (s.length < K) s.push(1 + Math.floor(rnd() * V)); inputs.push(s); }
  } else if (args[a] === '--random') {
    const [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
  } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
}

const same = (a, b) => !!a && !!b && a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const parentOf = (A, v) => v.pc >= 0 ? A[v.pc][v.pk] : null; // stored left end of v
const rawParent = (A, z) => { const v = above(A, z); return v ? parentOf(A, v) : null; };
function Qof(A, u) {
  const lc = u.k === 0 ? u.c - 1 : u.pc;
  if (lc < 0) return null;
  const col = A[lc];
  let k = u.k === 0 ? -1 : u.pk;
  while (k + 1 < col.length && cmp(col[k + 1].row, u.row) <= 0) k++;
  return k < 0 ? null : col[k];
}
const nm = z => z ? `(${z.c},${show(z.row)}${z.prov ? '|' + z.prov.kind[0] + (z.prov.ib ? '!' : '') + z.prov.src.c + ':' + show(z.prov.src.row) : ''})` : 'null';
function chainFrom(A, a, lo) { const out = []; let z = a; while (z && z.c >= lo) { out.push(z); z = rawParent(A, z); } return out; }

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < verbose) ex[k].push(msg); };
const seen = new Set();
let expansions = 0, skipped = 0;
let seq = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  if ((seq++) % shardN !== shardK) continue;
  if (progress && seq % progress === 0) console.error(`progress ${seq} ${key}`);
  if (maxMountain < Infinity) { let c = 0; for (const col of O.mountain(s)) c += col.length; if (c > maxMountain) { skipped++; continue; } }
  for (const n of copies) {
    if (trace) console.error(`start ${key} [${n}]`);
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}] ${err.message}`); continue; }
    const {R, M, root} = r, x0 = s.length - 1;
    if (!root) continue;
    let cells = 0; for (const col of R) cells += col.length;
    if (cells > maxCells) { skipped++; continue; }
    expansions++;
    const cr = root.c, w = x0 - cr, tau = M[x0][M[x0].length - 1].row;
    const low = z => cmp(z.row, tau) < 0;
    const src = Z => Z.prov ? M[Z.prov.src.c][Z.prov.src.k] : null;
    const lastCopy = new Map(); // column -> (source key -> index of the highest copy)
    const topCopy = (Z, z) => {
      if (!Z || !z || !Z.prov || !same(src(Z), z)) return false;
      let m = lastCopy.get(Z.c);
      if (!m) { m = new Map(); for (const V of R[Z.c]) if (V.prov) m.set(V.prov.src.c + ':' + V.prov.src.k, V.k); lastCopy.set(Z.c, m); }
      return m.get(z.c + ':' + z.k) === Z.k;
    };
    const Cp = (i, Z, z) => {
      if (!Z || !z) return false;
      if (z.c < cr) return same(Z, z);
      if (z.c === cr) {
        if (Z.c !== cr + w * i) return false;
        const zp = above(M, z);
        if (zp && !low(zp)) { const Zp = above(R, Z); if (!Zp || cmp(Zp.row, zp.row) !== 0) return false; }
        const b = rawParent(M, z);
        if (b) { let B = Z; while (B && B.c > b.c) B = rawParent(R, B); if (!same(B, b)) return false; }
        return true;
      }
      if (z.c >= x0 || Z.c !== z.c + w * i) return false;
      return low(z) ? topCopy(Z, z) : cmp(Z.row, z.row) === 0;
    };
    const where = `(${s})[${n}]`;
    for (let i = 1; i <= n; i++) {
      for (let y = cr + 1; y <= x0; y++) {
        if (y === x0 && i === n) continue;
        const X = y + w * i, colX = R[X];
        // CopyTop
        let k = colX.length - 1; while (k >= 0 && !low(colX[k])) k--;
        let ky = M[y].length - 1; while (ky >= 0 && !low(M[y][ky])) ky--;
        const okTop = k >= 0 && ky >= 0 && topCopy(colX[k], M[y][ky]);
        bump(`CopyTop ${y === x0 ? 'x0' : 'inner'} ${okTop}`, okTop ? null : `${where} i=${i} X=${X}`);
        // Emitted (LowerPB.Emitted, on the existing columns): every node of y below tau is the
        // origin of a non-cut lower copy in X.
        for (const z of M[y]) {
          if (!low(z)) continue;
          const okE = colX.some(V => low(V) && V.prov && same(src(V), z) && !(V.prov.kind === 'clean' && V.prov.ib));
          bump(`Emitted ${y === x0 ? 'x0' : 'inner'} ${okE}`, okE ? null : `${where} i=${i} X=${X} z=${nm(z)}`);
        }
        for (const Z of colX) {
          if (!low(Z)) continue;
          const z = src(Z);
          if (!topCopy(Z, z) || !low(z)) continue;
          // CopyQLower
          const a = Qof(M, z), A = Qof(R, Z);
          const okQ = !!a && Cp(i, A, a);
          const zTop = !!above(M, z) && !low(above(M, z));
          bump(`CopyQLower ${zTop ? '' : '(not asked: z+ missing or below tau) '} ${y === x0 ? 'x0' : 'inner'} ${Z.prov.kind}${Z.prov.ib ? '!' : ''} Q_M ${!a ? 'none' : a.c < cr ? '<cr' : a.c === cr ? '=cr' : '>cr'} ${okQ}`,
            okQ ? null : `${where} i=${i} Z=${nm(Z)} z=${nm(z)} Q_M=${nm(a)} Q_R=${nm(A)}`);
          // CopyStepLower
          if (y === x0) continue;
          const b = rawParent(M, z), B = rawParent(R, Z);
          if (!b) { bump(`CopyStepLower top (no stored parent in M)`); continue; }
          const okS = !!B && Cp(i, B, b);
          const zpLow = !!above(M, z) && low(above(M, z));
          bump(`CopyStepLower ${zpLow ? '(CopyStepLow: z+ < tau)' : '(z+ >= tau, proved)'} ${Z.prov.kind}${Z.prov.ib ? '!' : ''} a ${b.c < cr ? '<cr' : b.c === cr ? '=cr' : '>cr'} ${okS}`,
            okS ? null : `${where} i=${i} Z=${nm(Z)} z=${nm(z)} a=${nm(b)} A=${nm(B)}`);
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}${skipped ? `, skipped (too many cells) ${skipped}` : ''}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
