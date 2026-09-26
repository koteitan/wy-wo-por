// Numerical test of the open statements that CutTop, BoundaryChain and OriginReach
// (ChainCorrStartCopy.lean, ChainCorrStartRoot.lean) are reduced to in
// OmegaY/Official/Classification/Proofs/StartRootParts*.lean.
//
// Usage: node start-root-parts.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                  [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs. Notation: x0 the last column, t its top, cr the
// root column, w = x0 - cr; block m copies x0 to the column x0 + w m (for m >= 1 this is the
// boundary column cr + w (m + 1) of block m + 1). "Cut" = a gap copy (clean copy with b = 1).
// An M step p -> p' at scale k: p' = rawParent(p), jump(row p, row p') <= k.
// CopyNode(m, v, p): v is a node of an inner column y + w m (cr < y < x0) of block m with origin p,
// not a cut copy unless p has no raw parent.
//
//  BoundaryStepLower : v a node of the copy of x0 in a block m >= 1 (m < n), lower part, not cut,
//                      origin nu, M step nu -> m' at scale k:
//                        m' < cr : the R k-chain of v reaches m';
//                        m' = cr : the R k-chain of v reaches m'' for every M step m' -> m'';
//                        m' > cr : the R k-chain of v reaches a CopyNode(m, ., m').
//  BoundaryCutChain  : v a cut node of the copy of x0 in a block m >= 1: every node left of cr on
//                      the M k-chain of its origin is on the R k-chain of v.
//  For a node u of block i >= 1, not cut, origin o = (x, sigma), leg l of o,
//  pa = highest node of l at or below sigma (in M):
//  GapTop            : l > cr, the copy of l in block i has a cut copy of pa, row pa < sigma
//                      => pa has no raw parent.
//  PaLookup          : l = cr, pe = highest node of cr + w i at or below row u (in R), the origin
//                      nu of pe is not upper => pa = highest node of cr at or below row nu.
//  OriginUpper (proved in Lean, checked here): l = cr and nu upper => nu = pa.
//  X0Reach (M only)  : nu a node of x0 below t, q = highest node of cr at or below row nu, M step
//                      q -> m'' at scale k => the M k-chain of nu reaches m''.
//  BoundaryChain1 (proved in Lean, checked here): BoundaryChain for i = 1.
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
  let first = true;
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += 2;
    const where = x => `(${s})[${n}] ${x}`;
    const isCopyNode = (m, v, p) => v.i === m && v.x !== x0 && v.c === p.c + w * m && same(v.prov.src, p) && (!isCut(v) || !rawParent(M, p));
    // X0Reach (M only, once per sequence)
    if (first) {
      first = false;
      for (const nu of M[x0]) {
        if (cmp(nu.row, t.row) >= 0) continue;
        const q = hAM(M, cr, nu.row), mpp = rawParent(M, q);
        if (!mpp) { bump('X0Reach vacuous'); continue; }
        for (let k = jump(q.row, mpp.row); k <= D; k++) {
          const ok = reach(M, k, nu, mpp);
          bump(ok ? 'X0Reach ok' : 'FAIL X0Reach', ok ? null : where(`nu=(${nu.c},${nu.k}) k=${k}`));
        }
      }
    }
    // the copies of x0
    for (let m = 0; m < n; m++) for (const v of R[x0 + w * m]) {
      const nu = v.prov.src;
      if (m === 0) {
        // BoundaryChain1
        for (let k = 0; k <= D; k++) for (const mm of chain(M, k, nu)) if (mm.c < cr) {
          const ok = reach(R, k, v, mm);
          bump(ok ? 'BoundaryChain1 ok' : 'FAIL BoundaryChain1', ok ? null : where(`b=${v.k} k=${k}`));
        }
        continue;
      }
      if (isCut(v)) {
        for (let k = 0; k <= D; k++) for (const mm of chain(M, k, nu)) if (mm.c < cr) {
          const ok = reach(R, k, v, mm);
          bump(ok ? 'BoundaryCutChain ok' : 'FAIL BoundaryCutChain', ok ? null : where(`m=${m} b=${v.k} k=${k}`));
        }
        continue;
      }
      if (v.prov.kind === 'upper') continue;
      const mp = rawParent(M, nu);
      if (!mp) { bump('BoundaryStepLower vacuous'); continue; }
      for (let k = jump(nu.row, mp.row); k <= D; k++) {
        const cR = chain(R, k, v);
        let ok;
        if (mp.c < cr) ok = cR.some(q => same(q, mp));
        else if (mp.c === cr) { const mpp = rawParent(M, mp); ok = !(mpp && jump(mp.row, mpp.row) <= k) || cR.some(q => same(q, mpp)); }
        else ok = cR.some(q => isCopyNode(m, q, mp));
        bump(ok ? 'BoundaryStepLower ok' : 'FAIL BoundaryStepLower', ok ? null : where(`m=${m} b=${v.k} k=${k}`));
      }
    }
    // GapTop, PaLookup, OriginUpper
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0 || isCut(v)) continue;
      const o = v.prov.src, la = leg(o);
      if (la < cr) continue;
      const pa = hAM(M, la, o.row);
      if (la > cr) {
        const gap = R[la + w * i].some(q => isCut(q) && same(q.prov.src, pa));
        if (!gap) { bump('GapTop vacuous (no gap copy of pa)'); continue; }
        if (cmp(pa.row, o.row) === 0) { bump('GapTop vacuous (row pa = sigma)'); continue; }
        const ok = !rawParent(M, pa);
        bump(ok ? 'GapTop ok' : 'FAIL GapTop', ok ? null : where(`X=${X} u=${v.k}`));
      } else {
        const pe = hAM(R, cr + w * i, v.row), nu = pe.prov.src;
        if (pe.prov.kind === 'upper') {
          const ok = same(nu, pa);
          bump(ok ? 'OriginUpper ok' : 'FAIL OriginUpper', ok ? null : where(`X=${X} u=${v.k}`));
        } else {
          const ok = same(hAM(M, cr, nu.row), pa);
          bump(ok ? 'PaLookup ok' : 'FAIL PaLookup', ok ? null : where(`X=${X} u=${v.k}`));
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
