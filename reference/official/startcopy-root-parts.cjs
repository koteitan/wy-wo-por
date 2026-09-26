// Numerical test of the open statements that StartCopy and StartRoot are reduced to
// (OmegaY/Official/Classification/Proofs/ChainCorrStartCopy.lean, ChainCorrStartRoot.lean).
//
// Usage: node startcopy-root-parts.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                      [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs; every node of an output column X >= x0 records
// its origin (Trace.lean). Block i >= 1 copies the columns y of blockColumns(cr, x0, n, i) to
// X = y + w i. "Non-cut" means: not a clean copy with the cut flag b = 1 (cutOrigin = false).
// Rows of origins are compared as rows of M(s); emitted rows as output rows.
//
// StartCopy parts (ChainCorrStartCopy.lean):
//  CopyOrder   (A): for columns y, y' of block i and non-cut emits a of y, a' of y':
//                   row(src a) < row(src a') => row a < row a';  row(src a) = row(src a') => row a = row a'.
//  CopyEmitted (B): every node of an inner column y (cr < y < x0) is the origin of a non-cut emit of y.
//  CopyMono    (C1): in an inner column, the origin rows of the emits do not decrease.
//  CopyFirst   (C2): in an inner column, the first emit of every origin is non-cut.
//  CutTop         : for a non-cut node u of block i with leg l > cr, origin row sigma and
//                   pa = highest node of column l at or below sigma: if some cut emit of the copy of l
//                   has origin pa and row <= row(u), then pa has no raw parent (it is the top of l).
// StartRoot parts (ChainCorrStartRoot.lean):
//  BoundaryChain : for every node b of the boundary column B = cr + w i (i >= 1; the copy of x0 in
//                  block i - 1) with origin nu, every scale k and every node m* left of cr:
//                  the k-chain of nu in M reaches m* => the k-chain of b in the output reaches m*.
//  OriginReach   : for a non-cut node u of block i with leg cr, pa = highest node of cr at or below
//                  the origin row, pe = highest node of B at or below row(u), and every scale
//                  k >= jump(origin row, row pa) with an M step pa -> m'': the k-chain of the origin
//                  of pe in M reaches m''.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, degree, expandMountain} = O;

const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const same = (a, b) => a === b || (a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

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
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += 2;
    const where = x => `(${s})[${n}] ${x}`;
    for (let i = 1; i <= n; i++) {
      const ys = []; for (let y = cr + 1; y <= (i < n ? x0 : x0 - 1); y++) ys.push(y);
      // (A) CopyOrder
      const nc = [];
      for (const y of ys) for (const v of R[y + w * i]) if (!isCut(v)) nc.push({y, v});
      for (const a of nc) for (const b of nc) {
        const c1 = cmp(a.v.prov.src.row, b.v.prov.src.row), c2 = cmp(a.v.row, b.v.row);
        const ok = c1 > 0 || (c1 === 0 && c2 === 0) || (c1 < 0 && c2 < 0);
        bump(ok ? 'CopyOrder ok' : 'FAIL CopyOrder', ok ? null : where(`i=${i} y=${a.y} y'=${b.y} ${show(a.v.row)} ${show(b.v.row)}`));
      }
      for (const y of ys) {
        if (y >= x0) continue;
        const col = R[y + w * i];
        // (B) CopyEmitted
        for (const nd of M[y]) {
          const ok = col.some(v => same(v.prov.src, nd) && !isCut(v));
          bump(ok ? 'CopyEmitted ok' : 'FAIL CopyEmitted', ok ? null : where(`i=${i} y=${y} ${show(nd.row)}`));
        }
        // (C1) CopyMono, (C2) CopyFirst
        const firstSeen = new Set();
        col.forEach((v, k) => {
          if (k > 0) { const ok = cmp(col[k - 1].prov.src.row, v.prov.src.row) <= 0; bump(ok ? 'CopyMono ok' : 'FAIL CopyMono', ok ? null : where(`i=${i} y=${y} k=${k}`)); }
          const id = v.prov.src.k;
          if (!firstSeen.has(id)) { firstSeen.add(id); bump(isCut(v) ? 'FAIL CopyFirst' : 'CopyFirst ok', isCut(v) ? where(`i=${i} y=${y} ${show(v.row)}`) : null); }
        });
      }
    }
    // CutTop and OriginReach
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0 || isCut(v)) continue;
      const m = v.prov.src, la = leg(m);
      if (la < cr) continue;
      const pa = hAM(M, la, m.row);
      if (la > cr) {
        const L = R[la + w * i];
        const hit = L.some(q => isCut(q) && same(q.prov.src, pa) && cmp(q.row, v.row) <= 0);
        if (hit) { const ok = !rawParent(M, pa); bump(ok ? 'CutTop ok (used)' : 'FAIL CutTop', ok ? null : where(`X=${X} u=${show(v.row)}`)); }
        else bump('CutTop ok (vacuous)');
      } else {
        const pe = hAM(R, cr + w * i, v.row), mpp = rawParent(M, pa);
        if (!mpp) { bump('OriginReach ok (vacuous)'); continue; }
        const nu = pe.prov.src;
        for (let k = jump(m.row, pa.row); k <= D; k++) {
          if (jump(pa.row, mpp.row) > k) continue;
          const ok = reach(M, k, nu, mpp);
          bump(ok ? 'OriginReach ok' : 'FAIL OriginReach', ok ? null : where(`X=${X} u=${show(v.row)} k=${k}`));
        }
      }
    }
    // BoundaryChain
    for (let i = 1; i <= n; i++) for (const b of R[cr + w * i]) {
      const nu = b.prov.src;
      for (let k = 0; k <= D; k++) for (const mm of chain(M, k, nu)) if (mm.c < cr) {
        const ok = reach(R, k, b, mm);
        bump(ok ? 'BoundaryChain ok' : 'FAIL BoundaryChain', ok ? null : where(`i=${i} b=${show(b.row)} k=${k}`));
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
