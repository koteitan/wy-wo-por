// Numerical test of the statements of StepInnerCleanRoot*.lean
// (namespace ChainCorr.Inner.CleanRoot).
//
// Usage: node step-inner-clean-root.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                       [--random COUNT,MAXLEN,MAXVAL,SEED] [--every K,J]
//                                       [--maxnodes N] [--timeout SEC] [SAMPLE.json ...]
// --every K,J keeps the inputs with index = J mod K (a subset of --legal); --maxnodes skips the
// expansions whose output has more than N nodes (counted as 'skipped big'); --timeout stops after
// SEC seconds (the counts are then partial; the last line says so).
//
// Derived from step-inner.cjs (same notation). For every clean copy (b = 0) v in block i >= 1 of
// a = (y, C), with l the leg column of a and b the node of the column l at the row C:
//  LookupInner      : l > cr => the raw parent of v in the output is a clean copy (b = 0) of b in
//                     block i (proved: lookupInner).
//  LookupRoot       : l = cr => for every k >= jump(b, pi(b)) the k-chain of the raw parent of v
//                     in the output reaches pi(b) (reduced to StartRoot / BoundaryChainAt).
//  CleanParentReach : a+ exists, m' = rawParent(a) and k >= jump(a, m'): m' is on the generation
//                     chain of a, or the chain ends at g = (cr, C), g -> g1 = pi(g) is a k-step and
//                     the k-chain of M from g1 reaches m' (proved: cleanParentReach). The count
//                     'via g (more steps)' is the case where the old CleanParent fails.
//  CleanParent (old): m' on the chain, or m' = pi(g) (false: StepInnerCleanRootFalse.lean).
// Also ChainFirst (the step a -> b exists with l >= cr), and NextCopyPlain, PlainOnce as in
// step-inner.cjs.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, degree, expandMountain} = O;

const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const same = (a, b) => a === b || (!!a && !!b && a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], every = null, maxNodes = Infinity, timeout = Infinity;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--every') every = args[++a].split(',').map(Number);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--timeout') timeout = Number(args[++a]);
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
let expansions = 0, idx = -1, timedOut = false;
const t0 = Date.now();
for (const s of inputs) {
  idx++;
  if (every && idx % every[0] !== every[1]) continue;
  if ((Date.now() - t0) / 1000 > timeout) { timedOut = true; break; }
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    { let z = 0; for (const c of r.R) z += c.length; if (z > maxNodes) { bump('skipped big'); continue; } }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += 2; // every scale >= the largest jump is tested
    const phi = (c, i) => c < cr ? c : c + w * i;
    const isCopy = (u, m, i) => !!u && !!m && u.i === i && u.x !== x0 && u.x > cr && u.c === m.c + w * i &&
      same(u.prov.src, m) && (!isCut(u) || !rawParent(M, m));
    const where = (X, v) => `(${s})[${n}] X=${X} v=${show(v.row)} ${v.prov.kind}${isCut(v) ? '*' : ''}(${v.prov.src.c},${show(v.prov.src.row)})`;
    const res = (name, ok, X, v) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : where(X, v));
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      for (const v of col) {
        const i = v.i;
        if (i === 0 || v.x === x0) continue;
        const m = v.prov.src, vp = col[v.k + 1], mp = M[m.c][m.k + 1];
        if (v.prov.kind === 'plain') {
          res('PlainOnce', col.filter(u => same(u.prov.src, m)).length === 1, X, v);
          if (mp) res('NextCopyPlain', isCopy(vp, mp, i), X, v);
        }
        if (!isCopy(v, m, i)) continue;
        if (v.prov.kind !== 'clean' || isCut(v)) continue;
        {
          const l = leg(m), b = M[l].find(q => cmp(q.row, m.row) === 0), v1 = rawParent(R, v);
          if (!b || l < cr) { res('ChainFirst', false, X, v); }
          else if (l > cr) {
            const ok = !!v1 && isCopy(v1, b, i) && v1.prov.kind === 'clean' && !isCut(v1) && v1.x > cr && v1.x < x0;
            res('LookupInner', ok, X, v);
          } else {
            let ok = !!v1; const bpp = rawParent(M, b);
            if (ok && bpp) for (let k = jump(b.row, bpp.row); k <= D; k++) if (!reach(R, k, v1, bpp)) ok = false;
            res('LookupRoot', ok, X, v);
          }
        }
        if (mp) {
          const m1 = M[mp.pc][mp.pk], G = [];
          for (let a = m; a.c > cr;) { const b = M[leg(a)].find(q => cmp(q.row, m.row) === 0); if (!b) break; G.push(b); a = b; }
          const onChain = G.some(g => same(g, m1)), last = G[G.length - 1];
          if (onChain) { bump('CleanParentReach on chain'); continue; }
          let ok = !!last && last.c === cr;
          const g1 = ok ? rawParent(M, last) : null;
          for (let k = jump(m.row, m1.row); ok && k <= D; k++) {
            // MStep M k last g1 and ScaleReach M k g1 m1
            ok = !!g1 && jump(last.row, g1.row) <= k && reach(M, k, g1, m1);
          }
          res(`CleanParentReach via g (${same(g1, m1) ? 'one step' : 'more steps'})`, ok, X, v);
          res(`CleanParent (old)`, !!last && last.c === cr && same(g1, m1), X, v);
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}${timedOut ? ' (TIMED OUT: partial)' : ''}, ${((Date.now() - t0) / 1000).toFixed(0)} s`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
