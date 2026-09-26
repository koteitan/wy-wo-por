// Numerical test of the simulation form of `PosImgR` (OmegaY/Official/Recon/CrossPlainPosSim*.lean).
//
// Usage: node cross-plain-pos-sim.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//          [--random COUNT,MAXLEN,MAXVAL,SEED] [--family COUNT,MAXVAL,SEED] [--maxnodes N]
//          [--max-mountain N] [--progress K] [--shard K/N] [-v N] [SAMPLE.json ...]
// --maxnodes N skips the expansions whose output has more than N nodes; --max-mountain N skips
// the inputs whose mountain M(s) has more than N nodes (before expanding); both are counted.
// --family draws inputs (1,3,a,b,c,d) with a,b,c,d <= MAXVAL (the family where MA fails).
//
// Setting (the cross case of `CrossLexPos K`, K = plain or clean without the cut flag): a node u
// of a new column X > x0 of block i >= 1 whose upper node u+ has an origin of kind K with the
// source N (a node of M(s) in the column x), p = the stored parent of u+, q = Q u, and q, p in
// different columns. uM = the node below N, pM = the stored parent of N, qM = Q_M uM, cM = the
// node of the chain of stored parents of M(s) from qM with stored parent pM.
//
// The relation Cp(Z, z) is the one of OmegaY/Official/Recon/CrossUpperSimDefs.lean:
//   z.c <  c_r      : Z is z;
//   z.c =  c_r      : Z is in the column c_r + w*i; if z+ has a row >= tau then Z+ has the row of
//                     z+; if z has a stored parent b, the chain of stored parents of R from Z
//                     reaches b;
//   c_r < z.c < x0  : Z is in the column z.c + w*i; row Z = row z if row z >= tau, and Z is the
//                     top copy of z if row z < tau.
//
// Checked:
//   TopU      u is the top copy of uM (u has the source uM and no copy of uM is above u);
//   QCp       Cp(Q u, qM);
//   QCopy     for qM right of c_r: which copy of qM the node Q u is (top / first / other);
//   ChainCp   along the chain qM -> ... -> cM of M(s), every node z has a node Z of the chain of R
//             from Q u with Cp(Z, z), in order (the simulation of CrossUpperSimStep.cp_chain);
//   EndCp     the node C with Cp(C, cM) given by ChainCp, and the node c of the chain of R with
//             stored parent p: for cM right of c_r, c = C; for cM in c_r, c is below C in the
//             chain of R (C -> ... -> c -> p) and c is cM itself (an old column);
//             for cM left of c_r, c = C = cM;
//   EndUp     c+ has the row of u+ and is the image of cM+: cM+ itself for cM at or left of c_r, a
//             copy of cM+ of kind plain or clean (not cut) in the column cM.c + w*i otherwise.
//             The kind of c+ can differ from the kind of u+ (e.g. (1,3,27,11,22,30), n = 1: u+ plain,
//             c+ clean), so the image asks only for a plain or clean origin.
//   Pair      for N (the source of u+) and every node B of M(s) left of N with the stored parent
//             and the row of N: if B is right of c_r, the node above the top copy of B- is a
//             plain or clean copy of B with the row of u+ (PairAbove); if B is at or left of c_r,
//             row u+ = row N (PairOld). Reported with and without Lex(N, B).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], verbose = 0, maxNodes = Infinity, maxMountain = Infinity, progress = 0, shardK = 0, shardN = 1;
const rng = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '-v') verbose = +args[++a];
  else if (args[a] === '--maxnodes') maxNodes = +args[++a];
  else if (args[a] === '--max-mountain') maxMountain = +args[++a];
  else if (args[a] === '--progress') progress = +args[++a];
  else if (args[a] === '--shard') [shardK, shardN] = args[++a].split('/').map(Number);
  else if (args[a] === '--legal') {
    const [K, V] = args[++a].split(',').map(Number);
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  } else if (args[a] === '--random') {
    const [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
  } else if (args[a] === '--family') {
    const [count, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const s = [1, 3]; while (s.length < 6) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
  } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
}

const same = (a, b) => !!a && !!b && a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const parentOf = (A, v) => v.pc >= 0 ? A[v.pc][v.pk] : null;
const rawParent = (A, z) => { const v = above(A, z); return v ? parentOf(A, v) : null; };
function Qof(A, u) {
  const lc = u.k === 0 ? u.c - 1 : u.pc;
  if (lc < 0) return null;
  const col = A[lc];
  let k = u.k === 0 ? -1 : u.pk;
  while (k + 1 < col.length && cmp(col[k + 1].row, u.row) <= 0) k++;
  return k < 0 ? null : col[k];
}
function chainTo(A, a, p) {
  let c = a;
  for (;;) {
    const b = rawParent(A, c);
    if (!b || b.c < p.c) return null;
    if (same(b, p)) return c;
    c = b;
  }
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
const kindOf = v => v.prov.kind === 'clean' ? (v.prov.ib ? 'cut' : 'clean') : v.prov.kind;
const lowK = v => !!v && !!v.prov && (kindOf(v) === 'plain' || kindOf(v) === 'clean');
const nm = z => z ? `(${z.c},${show(z.row)}${z.prov ? '|' + kindOf(z) + ' ' + z.prov.src.c + ':' + z.prov.src.k : ''})` : 'null';

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < verbose) ex[k].push(msg); };
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  if (seen.size % shardN !== shardK) continue;
  if (progress && seen.size % progress === 0) console.error(`progress ${seen.size} ${key}`);
  if (maxMountain < Infinity) { let c = 0; for (const col of O.mountain(s)) c += col.length; if (c > maxMountain) { bump('skipped (M(s) larger than --max-mountain)'); continue; } }
  let tooBig = false; // R(s[n]) is a prefix of R(s[n+1]): once too big, every larger n is too
  for (const n of [...copies].sort((a, b) => a - b)) {
    if (tooBig) { bump('skipped (output larger than --maxnodes)'); continue; }
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {R, M} = r, x0 = s.length - 1;
    if (!r.root || R.length <= x0) continue;
    if (R.reduce((a, col) => a + col.length, 0) > maxNodes) { tooBig = true; bump('skipped (output larger than --maxnodes)'); continue; }
    const cr = r.root.c, w = x0 - cr, tau = M[x0][M[x0].length - 1].row;
    const low = z => cmp(z.row, tau) < 0;
    const isCopy = (Z, z) => !!Z && !!z && !!Z.prov && Z.prov.src.c === z.c && Z.prov.src.k === z.k;
    const copiesOf = (X, z) => (R[X] || []).filter(V => isCopy(V, z));
    const topCopy = (Z, z) => { const cs = copiesOf(Z.c, z); return cs.length > 0 && same(cs[cs.length - 1], Z); };
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
    const side = z => z.c < cr ? '<cr' : z.c === cr ? '=cr' : '>cr';
    for (let X = x0 + 1; X < R.length; X++) for (let k = 0; k + 1 < R[X].length; k++) {
      const u = R[X][k], up = R[X][k + 1];
      const K = kindOf(up);
      if (K !== 'plain' && K !== 'clean') continue;
      const p = parentOf(R, up), q = Qof(R, u);
      if (!q || q.c === p.c) continue;
      const where = `(${s})[${n}] X=${X} u=${nm(u)} u+=${nm(up)}`;
      const i = up.i, N = M[up.prov.src.c][up.prov.src.k];
      if (N.k === 0) { bump('FAIL origin is a bottom node', where); continue; }
      const uM = M[N.c][N.k - 1], pM = rawParent(M, uM), qM = Qof(M, uM);
      bump(`TopU ${topCopy(u, uM)}`, topCopy(u, uM) ? null : where);
      if (!qM || qM.c === pM.c) { bump('FAIL M(s) not in the cross case', where); continue; }
      // QCp, QCopy
      const okQ = Cp(i, q, qM);
      bump(`QCp ${K} qM ${side(qM)} ${okQ}`, okQ ? null : `${where} qM=${nm(qM)} q=${nm(q)}`);
      if (qM.c > cr) {
        const cs = copiesOf(qM.c + w * i, qM);
        const which = !cs.length ? 'no copy' : same(cs[cs.length - 1], q) ? 'top' : same(cs[0], q) ? 'first' : cs.some(V => same(V, q)) ? 'other' : 'not a copy';
        bump(`QCopy ${K} ${qM.c < x0 ? 'inner' : 'x0'} q is ${which} copy${cs.length === 1 ? " (the only copy)" : ""}`);
      }
      // ChainCp
      const chainM = []; { let z = qM; while (z) { chainM.push(z); if (same(rawParent(M, z), pM)) break; z = rawParent(M, z); if (z && z.c < pM.c) { z = null; } } }
      const cM = chainM[chainM.length - 1];
      if (!same(rawParent(M, cM), pM)) { bump('FAIL no chain in M(s)', where); continue; }
      const chainR = []; { let z = q; while (z && z.c >= p.c) { chainR.push(z); if (same(z, p)) break; z = rawParent(R, z); } }
      let pos = 0, okC = true, Cidx = -1;
      for (const z of chainM) {
        while (pos < chainR.length && !Cp(i, chainR[pos], z)) pos++;
        if (pos >= chainR.length) { okC = false; break; }
        Cidx = pos;
      }
      bump(`ChainCp ${K} ${okC}`, okC ? null : `${where} chainM=${chainM.map(nm).join('>')} chainR=${chainR.map(nm).join('>')}`);
      if (!okC) continue;
      const C = chainR[Cidx];
      const c = chainTo(R, q, p);
      if (!c) { bump('FAIL no chain in R', where); continue; }
      let endOK, endKind = side(cM);
      if (cM.c > cr || cM.c < cr) endOK = same(c, C);
      else endOK = chainR.indexOf(chainR.find(z => same(z, c))) >= Cidx && same(c, R[cM.c][cM.k]);
      bump(`EndCp ${K} cM ${endKind} ${endOK}`, endOK ? null : `${where} C=${nm(C)} c=${nm(c)} cM=${nm(cM)} chainR=${chainR.map(nm).join('>')}`);
      const cp = above(R, c), cMp = above(M, cM);
      const img = cM.c <= cr ? same(cp, cMp) : (cp.c === cM.c + w * i && lowK(cp) && isCopy(cp, cMp));
      if (cM.c > cr && img) bump(`EndUp ${K} cM >cr: kind of c+ ${kindOf(cp) === K ? 'same as' : 'differs from'} the kind of u+`, kindOf(cp) === K ? null : where);
      const firstCopy = cM.c > cr ? same(copiesOf(cp.c, cMp)[0], cp) : null;
      const rowOK = cmp(cp.row, up.row) === 0;
      bump(`EndUp ${K} cM ${endKind} img=${img} row=${rowOK}${cM.c > cr ? ' c+ first copy of cM+=' + firstCopy : ''}`, img && rowOK ? null : where);
    }
    // RootPassGen: every Cp(Z, z) with z in the column c_r (z real, with a stored parent)
    for (let i = 1; i <= n; i++) {
      const Y = cr + w * i;
      if (!R[Y]) continue;
      for (const z of M[cr]) {
        if (z.k === 0 || !rawParent(M, z)) continue;
        for (const Z of R[Y]) {
          if (!Cp(i, Z, z)) continue;
          let B = Z; while (B && B.c > z.c) B = rawParent(R, B);
          const ok = same(B, z);
          bump(`RootPassGen (any Cp(Z, z), z in c_r) ${ok}`, ok ? null : `(${s})[${n}] i=${i} Z=${nm(Z)} z=${nm(z)}`);
        }
      }
    }
    // QGen and Pairs: every node u of a new column whose upper node u+ has an origin of kind K
    for (let X = x0 + 1; X < R.length; X++) for (let k = 0; k + 1 < R[X].length; k++) {
      const u = R[X][k], up = R[X][k + 1];
      const K = kindOf(up);
      if (K !== 'plain' && K !== 'clean') continue;
      const where = `(${s})[${n}] X=${X} u=${nm(u)} u+=${nm(up)}`;
      const i = up.i, A = M[up.prov.src.c][up.prov.src.k];
      if (A.k === 0) continue;
      const uM = M[A.c][A.k - 1], q = Qof(R, u), qM = Qof(M, uM), p = parentOf(R, up), pA = parentOf(M, A);
      const cross = !!q && !!p && q.c !== p.c;
      if (qM) { const ok = Cp(i, q, qM); bump(`QGen ${K} ${cross ? 'cross' : 'not cross'} qM ${side(qM)} ${ok}`, ok ? null : `${where} qM=${nm(qM)} q=${nm(q)}`); }
      else bump(`QGen ${K} no Q_M`);
      if (!pA) continue;
      for (let y = pA.c + 1; y < A.c; y++) for (const B of M[y]) {
        if (!same(parentOf(M, B), pA) || cmp(B.row, A.row) !== 0) continue;
        const lx = lex(M, A, B) ? 'Lex' : 'noLex';
        if (B.c > cr) {
          const Bm = M[B.c][B.k - 1], cs = copiesOf(B.c + w * i, Bm), T = cs[cs.length - 1];
          const Tp = T ? above(R, T) : null;
          const okCopy = !!Tp && isCopy(Tp, B) && lowK(Tp), okRow = !!Tp && cmp(Tp.row, up.row) === 0;
          bump(`Pair ${K} ${lx} B >cr: above top copy of B- is a plain/clean copy of B ${okCopy}, row u+ ${okRow}`, okCopy && okRow ? null : `${where} B=${nm(B)} T=${nm(T)} T+=${nm(Tp)}`);
          if (okCopy) bump(`Pair ${K} ${lx} B >cr: kind of T+ ${kindOf(Tp) === K ? 'same as' : 'differs from'} the kind of u+`, kindOf(Tp) === K ? null : `${where} B=${nm(B)} T+=${nm(Tp)}`);
        } else {
          const okRow = cmp(up.row, A.row) === 0;
          bump(`Pair ${K} ${lx} B ${side(B)}: row u+ = row A ${okRow}`, okRow ? null : `${where} B=${nm(B)}`);
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
