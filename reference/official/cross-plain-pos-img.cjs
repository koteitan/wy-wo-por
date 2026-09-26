// Numerical test of the open statements of OmegaY/Official/Recon/CrossPlainPos.lean
// (CrossLexPos IsPlain / IsClean, blocks i >= 1).
//
// Usage: node cross-plain-pos-img.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//          [--random COUNT,MAXLEN,MAXVAL,SEED] [--maxnodes N] [-v N] [SAMPLE.json ...]
// --maxnodes N skips (and counts) the expansions whose output has more than N nodes.
//
// For every node u of a new column X > x0 whose upper node u+ has origin plain or clean
// (not cut), with p = the stored parent of u+ and q = Q u in different columns (the cross
// case), let N = the origin (source node of M(s)) of u+. The test checks:
//
//   PosChainImg (strong form):
//     * N is not the bottom node of its column: uM = the node below N is real;
//     * pM = the stored parent of uM, qM = Q_M uM: qM and pM are in different columns
//       (M(s) is in the cross case at uM), and the chain of stored parents of M(s) from qM
//       reaches a node cM with stored parent pM;
//     * the chain of stored parents of R from q reaches a node c with stored parent p, and
//       c+ = Img(cM+) with row(c+) = row(u+), where Img(B) for a node B of M(s) in column y:
//         - y <= c_r: the node B itself (the same column and index of R);
//         - y >  c_r: the node of column y + w*i whose origin has the kind of u+ and the
//                     source B.
//       The kind of the image is plain or clean (not cut); it can differ from the kind of u+
//       (e.g. (1,3,27,11,22,30), n = 1: u+ plain, c+ clean). The first version of this test and
//       of `ImgAt` asked for the kind of u+; that form is false.
//   PosLexAt: Lex(u+, c+) in R.
//
// and, on every emit of every new column X > x0 (OmegaY/Official/Recon/CrossPlainPosColumn.lean):
//   BelowSrc:   an emit k >= 1 of kind plain / clean (not cut) with origin N has N above the
//               bottom row, and the emit k - 1 has the origin N- (the node below N);
//   EmitBelow:  for such an emit with N above the bottom row, N- is the origin of some emit;
//   CleanFirst: an emit of kind clean (not cut) is the first emit of its origin;
//   LexImg:     (OmegaY/Official/Recon/CrossPlainPosLex.lean) for such an emit z with origin A
//               above the bottom row, and every node B of M(s) left of A with the stored parent
//               and the row of A and Lex(A, B) in M(s), every image W of B in block i
//               (Img as above, of kind plain or clean) has Lex(z, W) in R.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], verbose = 0, maxNodes = Infinity;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '-v') verbose = +args[++a];
  else if (args[a] === '--maxnodes') maxNodes = +args[++a];
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
const parentOf = (A, v) => v.pc >= 0 ? A[v.pc][v.pk] : null;
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
// the node of the chain of stored parents from a whose stored parent is p (null if none)
function chainTo(A, a, p) {
  let c = a;
  for (;;) {
    const b = rawParent(A, c);
    if (!b || b.c < p.c) return null;
    if (same(b, p)) return c;
    c = b;
  }
}
const lowK = v => !!v && !!v.prov && (kindOf(v) === 'plain' || kindOf(v) === 'clean');
const kindOf = v => v.prov.kind === 'clean' ? (v.prov.ib ? 'cut' : 'clean') : v.prov.kind;

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
    expansions++;
    const {R, M} = r, x0 = s.length - 1;
    if (!r.root || R.length <= x0) continue;
    if (R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes)'); continue; }
    const cr = r.root.c, w = x0 - cr;
    for (let X = x0 + 1; X < R.length; X++) {
      const col = R[X];
      for (let k = 0; k < col.length; k++) {
        const v = col[k], K = kindOf(v);
        if (K !== 'plain' && K !== 'clean') continue;
        const N = v.prov.src, where = `(${s})[${n}] X=${X} k=${k}`;
        if (K === 'clean') {
          let first = true;
          for (let j = 0; j < k; j++) if (same(col[j].prov.src, N)) first = false;
          if (first) bump('CleanFirst: ok'); else bump('FAIL CleanFirst', where);
        }
        if (N.k >= 1) {
          const Nm = M[N.c][N.k - 1];
          if (col.some(z => same(z.prov.src, Nm))) bump(`EmitBelow ${K}: ok`); else bump(`FAIL EmitBelow ${K}`, where);
        }
        if (N.k >= 1) {
          const i = v.i, pA = parentOf(M, N);
          for (let y = pA.c + 1; y < N.c; y++) for (const B of M[y]) {
            if (!same(parentOf(M, B), pA) || cmp(B.row, N.row) !== 0 || !lex(M, N, B)) continue;
            const Ws = y <= cr ? [R[y][B.k]]
              : (R[y + w * i] || []).filter(W => W.prov && lowK(W) && same(W.prov.src, B));
            if (!Ws.length) bump(`LexImg ${K}: B has no image`);
            for (const W of Ws) if (lex(R, v, W)) bump(`LexImg ${K}: ok`); else bump(`FAIL LexImg ${K}`, where);
          }
        }
        if (k >= 1) {
          const ok = N.k >= 1 && same(col[k - 1].prov.src, M[N.c][N.k - 1]);
          if (ok) bump(`BelowSrc ${K}: ok`); else bump(`FAIL BelowSrc ${K}`, where);
        }
      }
    }
    for (let X = x0 + 1; X < R.length; X++) for (let k = 0; k + 1 < R[X].length; k++) {
      const u = R[X][k], up = R[X][k + 1];
      const K = kindOf(up);
      if (K !== 'plain' && K !== 'clean') continue;
      const p = parentOf(R, up), q = Qof(R, u);
      if (q.c === p.c) continue;
      const where = `(${s})[${n}] X=${X} u=${show(u.row)}`;
      const i = up.i, N = up.prov.src;
      // M(s) side
      if (N.k === 0) { bump(`FAIL PosChainImg ${K}: origin is a bottom node`, where); continue; }
      const uM = M[N.c][N.k - 1], pM = rawParent(M, uM), qM = Qof(M, uM);
      if (!qM || qM.c === pM.c) { bump(`FAIL PosChainImg ${K}: M(s) not in the cross case`, where); continue; }
      const cM = chainTo(M, qM, pM);
      if (!cM) { bump(`FAIL PosChainImg ${K}: no chain in M(s)`, where); continue; }
      const cMp = above(M, cM), y = cM.c;
      // R side
      const c = chainTo(R, q, p);
      if (!c) { bump(`FAIL PosChainImg ${K}: no chain in R`, where); continue; }
      const cp = above(R, c);
      const img = y <= cr ? (cp.c === cMp.c && cp.k === cMp.k)
        : (cp.c === y + w * i && cp.prov && lowK(cp) && same(cp.prov.src, cMp));
      const rowOK = cmp(cp.row, up.row) === 0;
      if (!img || !rowOK) { bump(`FAIL PosChainImg ${K}: img=${img} row=${rowOK}`, where); continue; }
      bump(`PosChainImg ${K} (${y <= cr ? 'col cM <= c_r' : 'col cM > c_r'}): ok`);
      if (y > cr) bump(`PosChainImg ${K}: kind of c+ ${kindOf(cp) === K ? 'same as' : 'differs from'} the kind of u+ (allowed)`, kindOf(cp) === K ? null : where);
      if (lex(R, up, cp)) bump(`PosLexAt ${K}: ok`); else bump(`FAIL PosLexAt ${K}`, where);
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
