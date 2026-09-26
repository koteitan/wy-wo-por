// Numerical test of the open statements that StepInner is reduced to
// (OmegaY/Official/Classification/Proofs/ChainCorrStepInner.lean, namespace ChainCorr.Inner).
//
// Usage: node step-inner.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                            [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs; every node of an output column X >= x0 records
// its origin (Trace.lean), its source column x and its block i. Notation: cr the root column,
// w = x0 - cr, phi(c) = c (c < cr), c + w i (c >= cr); u+ is the node above u; the raw parent
// of u is the left end of u+; hAM(A, l, r) is the highest node of column l of A at or below row r;
// an M step p -> q at scale k is q = rawParent(p) with jump(row p, row q) <= k.
// A copy node (CopyNode) of m in block i >= 1 is a node of an inner column y + w i (cr < y < x0)
// whose origin is m and is not a gap copy (b = 1) unless m has no raw parent.
// A consecutive pair is (v, m) with v a copy node of m and v+ a copy node of m+.
// The statements (Lean names):
//  NextCopyPlain : v a copy of a plain origin m, m+ exists => v+ is a copy node of m+.
//  BumpCopyLower : consecutive pair, not both origins upper => jump(v, v+) <= jump(m, m+).
//  CleanNext     : v a clean copy (b = 0) of a => v+ is a gap copy (b = 1) of a.
//  LegLookup     : consecutive pair, pa = rawParent(m), pe = hAM(R, phi(col pa), row v):
//                  col pa < cr: pe = pa;  col pa > cr: pe is a copy node of pa;
//                  col pa = cr: every k >= jump(m, pa) and M step pa -> m'' at k:
//                  the k-chain of pe in the output reaches m''.
//  CleanLookup   : v a clean copy (b = 0) of a, l = leg column of a, b = the node of column l at
//                  row(a) (it exists, cr <= l), v1 = hAM(R, phi(l), row v): row v1 = row v;
//                  l > cr: v1 is a clean copy (b = 0) of b in block i;
//                  l = cr: every k and M step b -> m'' at k: the k-chain of v1 reaches m''.
//  CleanParent   : v a clean copy (b = 0) of a, a+ exists, m' = rawParent(a): m' is a node of the
//                  generation chain a -> b1 -> b2 -> ... -> (cr, row a) (next node: the node of the
//                  leg column at row(a), while the column is right of cr), or m' = rawParent of
//                  its last node (cr, row a).
// Also PlainOnce (not used by the Lean reduction): a plain origin is emitted once in its column.
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
        // consecutive pairs
        if (mp && isCopy(vp, mp, i)) {
          const bothUpper = v.prov.kind === 'upper' && vp.prov.kind === 'upper';
          if (!bothUpper) res('BumpCopyLower', jump(v.row, vp.row) <= jump(m.row, mp.row), X, v);
          const pa = M[mp.pc][mp.pk], pe = hAM(R, phi(pa.c, i), v.row);
          let ok;
          if (pa.c < cr) ok = same(pe, pa);
          else if (pa.c > cr) ok = isCopy(pe, pa, i);
          else {
            ok = !!pe;
            const mpp = rawParent(M, pa);
            if (ok && mpp) for (let k = Math.max(jump(m.row, pa.row), jump(pa.row, mpp.row)); k <= D; k++) if (!reach(R, k, pe, mpp)) ok = false;
          }
          res(`LegLookup (pa ${pa.c < cr ? '<' : pa.c === cr ? '=' : '>'} cr)`, ok, X, v);
        }
        if (v.prov.kind !== 'clean' || isCut(v)) continue;
        // clean copies of the root row
        res('CleanNext', !!vp && isCut(vp) && same(vp.prov.src, m), X, v);
        {
          const l = leg(m), b = M[l].find(q => cmp(q.row, m.row) === 0), v1 = hAM(R, phi(l, i), v.row);
          let ok = !!b && l >= cr && !!v1 && cmp(v1.row, v.row) === 0;
          if (ok && l > cr) ok = isCopy(v1, b, i) && v1.prov.kind === 'clean' && !isCut(v1);
          if (ok && l === cr) { const bpp = rawParent(M, b); if (bpp) for (let k = jump(b.row, bpp.row); k <= D; k++) if (!reach(R, k, v1, bpp)) ok = false; }
          res(`CleanLookup (l ${l === cr ? '=' : '>'} cr)`, ok, X, v);
        }
        if (mp) {
          const m1 = M[mp.pc][mp.pk], G = [];
          for (let a = m; a.c > cr;) { const b = M[leg(a)].find(q => cmp(q.row, m.row) === 0); if (!b) break; G.push(b); a = b; }
          const onChain = G.some(g => same(g, m1)), last = G[G.length - 1];
          const viaRoot = !onChain && !!last && last.c === cr && same(rawParent(M, last), m1);
          res(`CleanParent (${onChain ? 'on the chain' : 'via (cr, C)'})`, onChain || viaRoot, X, v);
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
