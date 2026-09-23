// Numerical test of the open statements that LegLookup is reduced to
// (OmegaY/Official/Classification/Proofs/StepInnerLookupLeg.lean, namespace ChainCorr.InnerLookup).
//
// Usage: node step-inner-lookup.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                   [--random COUNT,MAXLEN,MAXVAL,SEED] [--general] [SAMPLE.json ...]
//
// Notation as in step-inner.cjs: cr the root column, w = x0 - cr, phi(c) = c (c < cr),
// c + w i (c >= cr); a consecutive pair is (v, m) with v a copy node of m and v+ a copy node of m+
// (block i >= 1, inner column); pa = rawParent(m) = left(m+); pe = hAM(R, phi(col pa), row v).
// The statements (Lean names):
//  LegGapTop      : col pa > cr, a gap copy (b = 1) of pa in the column phi(col pa) at or below
//                   row v  =>  pa has no raw parent (pa is the top of its column).
//  LegOriginReach : col pa = cr, pa has a raw parent m'': for every k >= jump(m, pa), jump(pa, m''),
//                   the k-chain of M(s) from the origin of pe (a node of the boundary column
//                   cr + w i, emitted by block i - 1) reaches m''.
//  LegLeft        : col pa < cr  =>  pe = pa (proved in Lean from LegBelowTop; tested here).
// With --general, also the general form of LegGapTop that fails (GapAbove): for a gap copy g of
// p (inner column of block i) and a non-cut emit e of block i (inner column) whose origin q has
// row p <= row q < row p+ (p+ exists): row e < row g.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, degree, expandMountain} = O;

const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const same = (a, b) => a === b || (!!a && !!b && a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], general = false;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--general') general = true;
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
    const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);
    if (general) for (let i = 1; i <= n; i++) {
      const gaps = [], nonCut = [];
      for (let X = x0; X < R.length; X++) {
        const col = R[X];
        if (!col.length || col[0].i !== i || col[0].x === x0) continue;
        for (const u of col) (isCut(u) ? gaps : nonCut).push(u);
      }
      for (const g of gaps) {
        const p = g.prov.src, pp = M[p.c][p.k + 1];
        if (!pp) continue;
        const ok = nonCut.every(e => { const q = e.prov.src; return !(cmp(p.row, q.row) <= 0 && cmp(q.row, pp.row) < 0) || cmp(e.row, g.row) < 0; });
        res('GapAbove (general, expected to fail)', ok, `(${s})[${n}] g=(${g.c},${show(g.row)}) p=(${p.c},${show(p.row)})`);
      }
    }
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      for (const v of col) {
        const i = v.i;
        if (i === 0 || v.x === x0) continue;
        const m = v.prov.src, vp = col[v.k + 1], mp = M[m.c][m.k + 1];
        if (!isCopy(v, m, i) || !mp || !isCopy(vp, mp, i)) continue;
        const where = `(${s})[${n}] X=${X} v=${show(v.row)} ${v.prov.kind} m=(${m.c},${show(m.row)})`;
        const pa = M[mp.pc][mp.pk], pe = hAM(R, phi(pa.c, i), v.row);
        if (pa.c > cr) {
          const bad = !!rawParent(M, pa) && R[phi(pa.c, i)].some(q => isCut(q) && same(q.prov.src, pa) && cmp(q.row, v.row) <= 0);
          res('LegGapTop', !bad, where);
        } else if (pa.c === cr) {
          const mpp = rawParent(M, pa);
          if (!mpp) { bump('LegOriginReach (vacuous: pa has no raw parent)'); continue; }
          let ok = !!pe;
          if (ok) for (let k = Math.max(jump(m.row, pa.row), jump(pa.row, mpp.row)); k <= D; k++) if (!reach(M, k, pe.prov.src, mpp)) ok = false;
          res('LegOriginReach', ok, where);
        } else res('LegLeft (proved)', same(pe, pa), where);
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
