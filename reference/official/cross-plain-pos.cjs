// Numerical test of the split of CrossLexFor IsPlain / IsClean in
// OmegaY/Official/Recon/CrossPlainBlock0.lean:
//   * block 0 (u in the column x0): proved there (crossLex_block0);
//   * CrossLexPos IsPlain / IsClean (u in a column X > x0): open.
//
// Usage: node cross-plain-pos.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                 [--random COUNT,MAXLEN,MAXVAL,SEED] [-v N] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs. For every node u of a new column X >= x0 with a
// node u+ above it whose origin is plain or clean (a copy of the lower part that is not a gap
// copy), p = the stored parent of u+, q = Q u. In the cross case column(q) != column(p) the test
// follows the stored parents from q to the node c whose stored parent is p and checks
// row(c+) = row(u+) and Lex(u+, c+) (as cross-lex.cjs). It also checks the facts used by the
// proof of block 0 (u in the column x0):
//   * the lower part of R[x0] has the rows and stored left ends of M[x0] below its top, and the
//     first node of the upper part of R[x0] has its stored left end left of the root column;
//   * M(s) is in the cross case too at the corresponding nodes (Q_M(s0) and the stored parent of
//     s+ in different columns), with the same q and p.
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

const same = (a, b) => a.c === b.c && a.k === b.k;
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
    const cr = r.root.c;
    // block 0: the lower part of R[x0] copies M[x0] below its top
    {
      const cX = R[x0], cM = M[x0], L = cM.length - 1;          // indices 0..L-1 below the top
      let ok = cX.length >= L;
      for (let k = 0; ok && k < L; k++) {
        const a = cX[k], b = cM[k];
        if (cmp(a.row, b.row) !== 0 || a.pc !== b.pc || a.pk !== b.pk) ok = false;
      }
      if (ok && cX.length > L && !(cX[L].pc < cr)) ok = false;
      bump(ok ? 'block 0: R[x0] lower part = M[x0] below the top' : 'FAIL block 0 cells', ok ? null : `(${s})[${n}]`);
    }
    for (let X = x0; X < R.length; X++) for (let k = 0; k + 1 < R[X].length; k++) {
      const u = R[X][k], up = R[X][k + 1];
      const K = kindOf(up);
      if (K !== 'plain' && K !== 'clean') continue;
      const p = parentOf(R, up), q = Qof(R, u);
      if (q.c === p.c) continue;
      const where = `(${s})[${n}] X=${X} u=${show(u.row)}`;
      const part = X === x0 ? 'block 0' : 'CrossLexPos';
      let c = q, ok = false;
      for (;;) {
        const b = rawParent(R, c);
        if (!b || b.c < p.c) break;
        if (same(b, p)) { ok = true; break; }
        c = b;
      }
      if (!ok) { bump(`FAIL chain ${part} ${K}`, where); continue; }
      const cp = above(R, c);
      const lexOK = cmp(cp.row, up.row) === 0 && lex(R, up, cp);
      bump(lexOK ? `${part} ${K}: ok` : `FAIL ${part} ${K}`, lexOK ? null : where);
      if (X === x0) {
        // the corresponding nodes of M(s): the same references
        const s0 = M[x0][k], sp = M[x0][k + 1];
        const pM = parentOf(M, sp), q0 = Qof(M, s0);
        const corr = sp && same(pM, p) && same(q0, q) && q0.c !== pM.c;
        bump(corr ? 'block 0: M(s) cross case with the same p, q' : 'FAIL block 0 correspondence', corr ? null : where);
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
