// Numerical tests for the repair of StartCopy / CutTop / GapTop and for the MA-free route to
// PaLookup (OmegaY/Official/Classification/Proofs/StartRootFix*.lean).
//
// Usage: node start-root-fix.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// Notation as in start-root-parts.cjs. For a node u of block i >= 1 that is not a gap copy,
// o its origin (row sigma), l = leg(o), pa = highest node of l at or below sigma (in M),
// pe = highest node of phi(l) at or below row u (in R).
//
//  StartCopy       : l > cr => pe is a copy node of pa (not a gap copy unless pa has no raw parent).
//  StartCopyRel    : l > cr => pe is a copy or a gap copy of pa in block i (CutRel).
//  RootCmp         : for every real node c of cr, cmp(row u, row c) = cmp(sigma, row c)
//                    (u any non-gap node of block i >= 1, any column, upper part included).
//  X0First         : m >= 1, p a real node of x0 below t: the first emit of p in the copy of x0
//                    by block m exists, is not a gap copy, and has the row of p.
//  X0FirstRoot     : X0First restricted to p at the row of a real node of cr.
//  PaLookup        : as in start-root-parts.cjs.
//  StepInnerRel    : StepInner (chain-corr.cjs) for m' > cr, with the target a copy or a gap copy
//                    of m' in block i (CutRel) instead of a CopyNode.
//  InnerCutChain   : v a gap copy in an inner column of block i >= 1, origin m: every node left of
//                    cr on the M k-chain of m is on the R k-chain of v (every k).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, degree, expandMountain} = O;
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };

const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const same = (a, b) => a === b || (a.c === b.c && a.k === b.k);
const isCut = v => v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
const sgn = x => x < 0 ? -1 : x > 0 ? 1 : 0;

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
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error'); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    const where = x => `(${s})[${n}] ${x}`;
    const crRows = M[cr].filter(c => c.k >= 1).map(c => c.row);
    // X0First
    for (let m = 1; m < n; m++) {
      const col = R[x0 + w * m];
      for (const p of M[x0]) {
        if (p.k < 1 || cmp(p.row, t.row) >= 0) continue;
        const atRoot = crRows.some(r0 => cmp(r0, p.row) === 0);
        const f = col.find(v => v.prov.kind !== 'upper' && same(v.prov.src, p));
        const ok = !!f && !isCut(f) && cmp(f.row, p.row) === 0;
        bump(ok ? 'X0First ok' : 'FAIL X0First', ok ? null : where(`m=${m} p=(${p.c},${p.k})`));
        if (atRoot) bump(ok ? 'X0FirstRoot ok' : 'FAIL X0FirstRoot', ok ? null : where(`m=${m} p=(${p.c},${p.k})`));
      }
    }
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += 2;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0 || v.x === x0) continue;
      const m = v.prov.src;
      if (isCut(v)) for (let k = 0; k <= D; k++) for (const mm of chain(M, k, m)) if (mm.c < cr) {
        const ok = chain(R, k, v).some(r => same(r, mm));
        bump(ok ? 'InnerCutChain ok' : 'FAIL InnerCutChain', ok ? null : where(`X=${X} v=${v.k} k=${k}`));
      }
      if (isCut(v) && rawParent(M, m)) continue;
      const mp = rawParent(M, m);
      if (!mp || mp.c <= cr) continue;
      for (let k = jump(m.row, mp.row); k <= D; k++) {
        const cR = chain(R, k, v);
        const ok0 = cR.some(r => r.c === mp.c + w * i && r.i === i && same(r.prov.src, mp) && (!isCut(r) || !rawParent(M, mp)));
        const ok1 = cR.some(r => r.c === mp.c + w * i && r.i === i && same(r.prov.src, mp));
        bump(ok0 ? 'StepInner (m\' > cr) ok' : 'FAIL StepInner (m\' > cr)', ok0 ? null : where(`X=${X} v=${v.k} k=${k}`));
        bump(ok1 ? 'StepInnerRel ok' : 'FAIL StepInnerRel', ok1 ? null : where(`X=${X} v=${v.k} k=${k}`));
      }
    }
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0 || isCut(v)) continue;
      const o = v.prov.src;
      // RootCmp
      let okc = true;
      for (const r0 of crRows) if (sgn(cmp(v.row, r0)) !== sgn(cmp(o.row, r0))) okc = false;
      bump(okc ? 'RootCmp ok' : 'FAIL RootCmp', okc ? null : where(`X=${X} u=${v.k}`));
      const la = leg(o);
      if (la < cr) continue;
      const pa = hAM(M, la, o.row);
      if (la > cr) {
        const pe = hAM(R, la + w * i, v.row);
        const rel = pe && pe.i === i && pe.x === la && same(pe.prov.src, pa);
        const copy = rel && (!isCut(pe) || !rawParent(M, pa));
        bump(rel ? 'StartCopyRel ok' : 'FAIL StartCopyRel', rel ? null : where(`X=${X} u=${v.k}`));
        bump(copy ? 'StartCopy ok' : 'FAIL StartCopy', copy ? null : where(`X=${X} u=${v.k}`));
      } else {
        const pe = hAM(R, cr + w * i, v.row), nu = pe.prov.src;
        if (pe.prov.kind !== 'upper') {
          const ok = same(hAM(M, cr, nu.row), pa);
          bump(ok ? 'PaLookup ok' : 'FAIL PaLookup', ok ? null : where(`X=${X} u=${v.k}`));
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
