// Numerical test of the chain correspondence of
// OmegaY/Official/Classification/Proofs/ChainCorrRegions.lean.
//
// Usage: node chain-corr.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                            [--random COUNT,MAXLEN,MAXVAL,SEED] [--steps] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md); every node of
// an output column X = x + w i >= x0 records its origin (Trace.lean) and its block i.
// Notation: cr the root column, w = x0 - cr, phi(c) = c (c < cr), c + w i (c >= cr);
// an M step m -> m' at scale k is m' = rawParent(m) with jump(row m, row m') <= k (the step
// of scaleRoot); the R k-chain of v is the list of nodes scaleRoot visits from v.
// A copy node of m in block i is a node of an inner column y + w i (cr < y < x0) of block i
// whose origin is m, and whose origin is not a gap copy (b = 1) unless m has no raw parent.
// The statements (Lean names):
//  StepInner : v a copy node of m (non-gap), k any scale, m -> m' an M step at scale k:
//              m' < cr : the R k-chain of v reaches m';
//              m' = cr : it reaches a node v' of column cr + w i, and the R k-chain of v'
//                        reaches m'' whenever m' -> m'' is an M step at scale k;
//              m' > cr : it reaches a copy node of m' in block i.
//  StartLeg  : the leg of a lower-part origin (block i >= 1) is >= cr.
//  For a node u of block i >= 1 whose origin o is not a gap copy (upper part: leg >= cr),
//  la = leg(o), pa = highest node of column la at or below row(o) (in M),
//  pe = highest node of column phi(la) at or below row(u) (in the output):
//  StartJump : jump(row u, row pe) <= jump(row o, row pa);
//  StartCopy : la > cr => pe is a copy node of pa in block i;
//  StartRoot : la = cr => for every k >= jump(row o, row pa) and M step pa -> m'' at scale k,
//              the R k-chain of pe reaches m''.
// With --steps it also prints how many output steps match one step of M (the roadmap in
// ChainCorrRegions.lean: one step from a plain or upper node, several from a clean copy).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {mountain, cmp, jump, show, degree, expandMountain} = O;

const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const same = (a, b) => a === b || (a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => v.prov && v.prov.kind === 'clean' && v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], steps = false;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--steps') steps = true;
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
    const where = x => `(${s})[${n}] ${x}`;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0) continue;
      const m = v.prov.src;
      if (v.prov.kind !== 'upper') bump(leg(m) < cr ? 'FAIL StartLeg' : 'StartLeg ok', leg(m) < cr ? where(`X=${X}`) : null);
      // StepInner
      if (v.x !== x0 && !isCut(v)) {
        const mp = rawParent(M, m);
        if (mp) for (let k = jump(m.row, mp.row); k <= D; k++) {
          const cR = chain(R, k, v);
          let idx;
          if (mp.c < cr) idx = cR.findIndex(r => same(r, mp));
          else if (mp.c === cr) {
            idx = cR.findIndex(r => r.c === cr + w * i);
            const mpp = rawParent(M, mp);
            if (idx >= 0 && mpp && jump(mp.row, mpp.row) <= k && !reach(R, k, cR[idx], mpp)) idx = -1;
          } else idx = cR.findIndex(r => r.c === mp.c + w * i && r.i === i && same(r.prov.src, mp) && (!isCut(r) || !rawParent(M, mp)));
          const tag = `StepInner ${mp.c < cr ? '(m\' < cr)' : mp.c === cr ? '(m\' = cr)' : '(m\' > cr)'}`;
          bump(`${idx < 0 ? 'FAIL ' : ''}${tag}${idx < 0 ? '' : ' ok'}`, idx < 0 ? where(`X=${X} v=${show(v.row)} k=${k}`) : null);
          if (steps && idx >= 0) bump(`  steps from a ${v.prov.kind} node: ${idx}`);
        }
      }
      // the region nodes of RegionUpper, RegionPlain*, RegionClean*
      const la = leg(m);
      if (isCut(v) || la < cr) continue;
      const pe = hAM(R, la + w * i, v.row), pa = hAM(M, la, m.row), da = jump(m.row, pa.row);
      const okJ = jump(v.row, pe.row) <= da;
      bump(okJ ? 'StartJump ok' : 'FAIL StartJump', okJ ? null : where(`X=${X} u=${show(v.row)}`));
      if (la > cr) {
        const ok = pe.c === la + w * i && pe.i === i && same(pe.prov.src, pa) && (!isCut(pe) || !rawParent(M, pa));
        bump(ok ? 'StartCopy ok' : 'FAIL StartCopy', ok ? null : where(`X=${X} u=${show(v.row)}`));
      } else {
        const mpp = rawParent(M, pa);
        let ok = pe.c === cr + w * i;
        if (mpp) for (let k = Math.max(da, jump(pa.row, mpp.row)); k <= D; k++) if (!reach(R, k, pe, mpp)) ok = false;
        bump(ok ? 'StartRoot ok' : 'FAIL StartRoot', ok ? null : where(`X=${X} u=${show(v.row)}`));
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
