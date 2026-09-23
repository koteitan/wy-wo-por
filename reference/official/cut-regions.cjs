// Numerical test of the gap-copy statements of
// OmegaY/Official/Classification/Proofs/ChainCorrCut.lean (regions RegionCutBoundary and
// RegionCutInner: copies of the root row with b = 1).
//
// Usage: node cut-regions.cjs [--extraD K] [--legal MAXLEN,MAXVAL]
//                             [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md), n = 1, 2, 3.
// D = the largest degree of a row of M(s) and of the output (plus K with --extraD).
// Notation as in chain-corr.cjs: cr the root column, w = x0 - cr, B = cr + w i,
// phi(c) = c (c < cr), c + w i (c >= cr); root(A, k, u) the end of the scale-k chain of u.
// Wit(k, v, m): some k < k' <= D has root_R(k', v).c < phi(root_M(k', m).c).
// The statements (Lean names):
//  StepCut      : v a gap copy (b = 1) of m in an inner column of block i, k <= D, m -> m' an
//                 M step at scale k: Next (as StepInner, copies or gap copies) or Wit(k, v, m).
//  CutLeg       : the leg of the origin of a gap copy is >= cr.
//  For a gap copy u with origin o, la = leg(o), pa = highest node of column la at or below
//  row(o) (in M), pe = highest node of column phi(la) at or below row(u) (in the output):
//  CutJump      : jump(row u, row pe) <= jump(row o, row pa), or some k' >= both jumps
//                 (k' <= D) has root_R(k', pe).c < phi(root_M(k', pa).c);
//  CutStartCopy : la > cr => pe is the gap copy of pa in block i;
//  CutStartRoot : la = cr => pe is in column B and for d_a <= k <= D and an M step pa -> m''
//                 at scale k, the R k-chain of pe reaches m''.
// It also prints the kind of the first witness of the StepCut cases answered by Wit
// ("crossB": root_M >= cr and root_R < B at the witness scale).
'use strict';
// Tests the open statements of the cut regions (b = 1 gap copies).
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {mountain, cmp, jump, show, degree, expandMountain} = O;
const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const root = (A, k, u) => { const L = chain(A, k, u); return L[L.length - 1]; };
const same = (a, b) => a === b || (a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => !!(v.prov && v.prov.kind === 'clean' && v.prov.ib);
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
const args = process.argv.slice(2);
const inputs = [];
let extraD = 0;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--extraD') extraD = +args[++a];
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
  const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue; seen.add(key);
  for (const n of [1, 2, 3]) {
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error'); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += extraD;
    const where = x => `(${s})[${n}] ${x}`;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0) continue;
      const phi = c => c < cr ? c : c + w * i, B = cr + w * i;
      const cutNode = (vv, mm) => vv.c > B && vv.c < x0 + w * i && vv.i === i && isCut(vv) && same(vv.prov.src, mm);
      const copyNode = (vv, mm) => vv.c > B && vv.c < x0 + w * i && vv.i === i && vv.prov.kind !== 'upper' ? same(vv.prov.src, mm) && (!isCut(vv) || !rawParent(M, mm)) : (vv.c > B && vv.c < x0 + w * i && vv.i === i && same(vv.prov.src, mm));
      const rel = (vv, mm) => cutNode(vv, mm) || copyNode(vv, mm);
      const wit = (vv, mm, k) => { for (let kk = k + 1; kk <= D; kk++) if (root(R, kk, vv).c < phi(root(M, kk, mm).c)) return true; return false; };
      const next = (vv, k, mp) => {
        const cR = chain(R, k, vv);
        if (mp.c < cr) return cR.some(r => same(r, mp));
        if (mp.c === cr) {
          const mpp = rawParent(M, mp);
          return cR.some(r => r.c <= B && (!mpp || jump(mp.row, mpp.row) > k || reach(R, k, r, mpp)));
        }
        return cR.some(r => rel(r, mp));
      };
      // StepCut: from a cut node of an inner column
      if (isCut(v) && v.x !== x0) {
        const m = v.prov.src, mp = rawParent(M, m);
        if (mp) for (let k = jump(m.row, mp.row); k <= D; k++) {
          const ok = next(v, k, mp), w2 = ok || wit(v, m, k);
          if (!ok) {
            let kind = 'none';
            for (let kk = k + 1; kk <= D; kk++) { const rm = root(M, kk, m).c, rr = root(R, kk, v).c;
              if (rr < phi(rm)) { kind = (rm >= cr && rr < B ? 'crossB' : 'other') + (kk === k + 1 ? ' k+1' : ' higher') + (rm === cr ? ' rootM=cr' : rm > cr ? ' rootM>cr' : ' rootM<cr'); break; } }
            bump('StepCut wit kind: ' + kind + ` m'${mp.c < cr ? '<' : mp.c === cr ? '=' : '>'}cr`);
          }
          bump(`StepCut ${ok ? 'next' : w2 ? 'wit' : 'FAIL'}`, w2 ? null : where(`X=${X} v=${show(v.row)} k=${k}`));
        }
      }
      if (!isCut(v)) continue;
      const m = v.prov.src, la = leg(m);
      bump(la < cr ? 'FAIL CutLeg' : 'CutLeg ok', la < cr ? where(`X=${X}`) : null);
      if (la < cr) continue;
      const pe = hAM(R, phi(la), v.row), pa = hAM(M, la, m.row), da = jump(m.row, pa.row), de = jump(v.row, pe.row);
      if (da > D) { bump('allTop'); continue; }
      // CutJump
      let okJ = de <= da;
      if (!okJ) for (let kk = Math.max(de, da); kk <= D; kk++) if (root(R, kk, pe).c < phi(root(M, kk, pa).c)) okJ = true;
      bump(okJ ? 'CutJump ok' : 'FAIL CutJump', okJ ? null : where(`X=${X} u=${show(v.row)}`));
      if (de > da) { let cross = false; for (let kk = Math.max(de, da); kk <= D; kk++) if (root(M, kk, pa).c >= cr && root(R, kk, pe).c < B) cross = true; bump('CutJump de>da cross=' + cross); }
      if (la > cr) {
        const ok = cutNode(pe, pa);
        bump(ok ? 'CutStartCopy ok' : 'FAIL CutStartCopy', ok ? null : where(`X=${X} u=${show(v.row)} pe=(${pe.c},${show(pe.row)})`));
      } else {
        const mpp = rawParent(M, pa);
        let ok = pe.c === B;
        if (mpp) for (let k = Math.max(da, jump(pa.row, mpp.row)); k <= D; k++) if (!reach(R, k, pe, mpp)) ok = false;
        bump(ok ? 'CutStartRoot ok' : 'FAIL CutStartRoot', ok ? null : where(`X=${X} u=${show(v.row)}`));
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('     e.g.', m); }
