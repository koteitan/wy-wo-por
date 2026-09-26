// Numerical test of the open statements that the gap-copy statements StepCut, CutJump,
// CutStartCopy and CutStartRoot (ChainCorrCut.lean) are reduced to in
// OmegaY/Official/Classification/Proofs/CutParts*.lean (namespace ChainCorr.CutParts).
//
// Usage: node cut-parts.cjs [--extraD K] [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                           [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs; every node of an output column X >= x0 records
// its origin (Trace.lean), its source column x and its block i. Notation as in cut-regions.cjs:
// cr the root column, w = x0 - cr, B = cr + w i, phi(c) = c (c < cr), c + w i (c >= cr);
// u+ the node above u; rawParent(u) the left end of u+; hAM(A, l, r) the highest node of column l
// of A at or below row r; root(A, k, u) the end of the scale-k chain of u; an M step p -> q at
// scale k is q = rawParent(p) with jump(row p, row q) <= k.
// A gap copy is a node with origin {kind: 'clean', ib: true}; it is inner when x < x0.
// For a gap copy u of block i >= 1 with origin o, leg l of o (the column of the left end of o,
// x - 1 for a bottom node), pa = hAM(M, l, row o), pe = hAM(R, phi(l), row u):
//  CutPaRow      : row pa = row o.
//  CutGenReach   : (inner) if o -> m' is an M step at scale k <= D, the scale-k chain of pa in M
//                  reaches m'.
//  CutTopLookup  : (inner) if u+ is not a gap copy of o and m' = rawParent(o) exists:
//                  pe' = rawParent(u) exists, jump(row u, row pe') <= jump(row o, row m'), and
//                  m' < cr: pe' = m';  m' = cr: pe' is in column B and for every k <= D and M step
//                  m' -> m'' at scale k the output k-chain of pe' reaches m'';
//                  m' > cr: pe' is a copy node or a gap copy (inner, block i) of m'.
//  CutRunLow     : l > cr => the copy of column l in block i has a gap copy of pa at a row <= row u.
//  CutRunHigh    : l > cr => every non-gap emit of the copy of column l in block i whose origin row
//                  is > row pa has a row > row u.
//  CutOriginReach: l = cr => for d_a = jump(row o, row pa) <= k <= D and an M step pa -> m'' at
//                  scale k, the M k-chain of the origin of pe reaches m''.
//  CutJumpTop    : row pe < row u => CutJump (jump(row u, row pe) <= d_a, or some
//                  max(d_e, d_a) <= k' <= D has root_R(k', pe).c < phi(root_M(k', pa).c)).
//  CutTopNext    : (inner) at the top of a run (u+ not a gap copy of o), u+ is a non-cut copy of o+
//                  in the same column (derived in Lean from CopyOrder, CopyEmitted, CopyFirst).
//  CutBump       : (inner) at the top of a run, jump(row u, row u+) <= jump(row o, row o+).
//  CutLegLookup  : (inner) at the top of a run with m' = rawParent(o), pe2 = hAM(R, phi(m'), row u):
//                  m' < cr: pe2 = m';  m' = cr: for k >= jump(row o, row m') (k <= D) and an M step
//                  m' -> m'' at scale k, the output k-chain of pe2 reaches m'';
//                  m' > cr: pe2 is a gap copy (inner, block i) of m'.
// It also checks the fact proved in Lean that inside a run (u+ a gap copy of o) the raw parent of
// u is pe ("InRunParent").
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, eq, jump, show, degree, expandMountain} = O;

const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const root = (A, k, u) => { const L = chain(A, k, u); return L[L.length - 1]; };
const same = (a, b) => a === b || (!!a && !!b && a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => !!(v.prov && v.prov.kind === 'clean' && v.prov.ib);
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

const args = process.argv.slice(2);
const inputs = [];
let extraD = 0, copies = [1, 2, 3];
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--extraD') extraD = +args[++a];
  else if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
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
  for (const n of copies) {
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error'); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += extraD;
    const where = x => `(${s})[${n}] ${x}`;
    for (let X = x0; X < R.length; X++) for (const u of R[X]) {
      const i = u.i; if (i === 0 || !isCut(u)) continue;
      const phi = c => c < cr ? c : c + w * i, B = cr + w * i;
      const innerCol = vv => vv.c > B && vv.c < x0 + w * i && vv.i === i;
      const cutNode = (vv, mm) => innerCol(vv) && isCut(vv) && same(vv.prov.src, mm);
      const copyNode = (vv, mm) => innerCol(vv) && same(vv.prov.src, mm) && (!isCut(vv) || !rawParent(M, mm));
      const rel = (vv, mm) => cutNode(vv, mm) || copyNode(vv, mm);
      const o = u.prov.src, l = leg(o), inner = u.x !== x0;
      const tag = `X=${X} u=${show(u.row)}`;
      if (l < cr) { bump('FAIL CutLeg', where(tag)); continue; }
      const pa = hAM(M, l, o.row), pe = hAM(R, phi(l), u.row);
      // CutPaRow
      { const ok = eq(pa.row, o.row); bump(ok ? 'CutPaRow ok' : 'FAIL CutPaRow', ok ? null : where(tag)); }
      const mp = rawParent(M, o), up = R[X][u.k + 1];
      const inRun = !!up && isCut(up) && same(up.prov.src, o);
      if (inner && mp) {
        // CutGenReach
        for (let k = jump(o.row, mp.row); k <= D; k++) {
          const ok = reach(M, k, pa, mp);
          bump(ok ? 'CutGenReach ok' : 'FAIL CutGenReach', ok ? null : where(tag + ` k=${k}`));
        }
        if (inRun) {
          const ok2 = same(rawParent(R, u), pe);
          bump(ok2 ? 'InRunParent ok' : 'FAIL InRunParent', ok2 ? null : where(tag));
        } else {
          // CutTopLookup
          const pe1 = rawParent(R, u);
          let ok3 = !!pe1 && jump(u.row, pe1.row) <= jump(o.row, mp.row);
          if (ok3) {
            if (mp.c < cr) ok3 = same(pe1, mp);
            else if (mp.c === cr) {
              ok3 = pe1.c === B;
              const m2 = rawParent(M, mp);
              if (ok3 && m2) for (let k = jump(mp.row, m2.row); k <= D; k++) if (!reach(R, k, pe1, m2)) ok3 = false;
            } else ok3 = rel(pe1, mp);
          }
          bump(ok3 ? `CutTopLookup ok (m' ${mp.c < cr ? '<' : mp.c === cr ? '=' : '>'} cr)` : 'FAIL CutTopLookup', ok3 ? null : where(tag));
          // its parts: CutTopNext (derived in Lean from the block profile), CutBump, CutLegLookup
          const mu = M[o.c][o.k + 1];
          const nxt = !!up && !!mu && !isCut(up) && same(up.prov.src, mu) && up.i === i && up.x === u.x;
          bump(nxt ? 'CutTopNext ok' : 'FAIL CutTopNext', nxt ? null : where(tag));
          if (nxt) {
            const okB = jump(u.row, up.row) <= jump(o.row, mu.row);
            bump(okB ? 'CutBump ok' : 'FAIL CutBump', okB ? null : where(tag));
          }
          const pe2 = hAM(R, phi(mp.c), u.row);
          let ok4;
          if (mp.c < cr) ok4 = same(pe2, mp);
          else if (mp.c === cr) {
            ok4 = true;
            const m2 = rawParent(M, mp);
            if (m2) for (let k = Math.max(jump(o.row, mp.row), jump(mp.row, m2.row)); k <= D; k++) if (!reach(R, k, pe2, m2)) ok4 = false;
          } else ok4 = cutNode(pe2, mp);
          bump(ok4 ? `CutLegLookup ok (m' ${mp.c < cr ? '<' : mp.c === cr ? '=' : '>'} cr)` : 'FAIL CutLegLookup', ok4 ? null : where(tag));
        }
      }
      if (l > cr) {
        const L = R[phi(l)];
        const low = L.some(q => isCut(q) && same(q.prov.src, pa) && q.i === i && cmp(q.row, u.row) <= 0);
        bump(low ? 'CutRunLow ok' : 'FAIL CutRunLow', low ? null : where(tag));
        const high = L.every(q => isCut(q) || cmp(q.prov.src.row, pa.row) <= 0 || cmp(q.row, u.row) > 0);
        bump(high ? 'CutRunHigh ok' : 'FAIL CutRunHigh', high ? null : where(tag));
      } else {
        const nu = pe.prov.src, m2 = rawParent(M, pa), da = jump(o.row, pa.row);
        if (m2) for (let k = Math.max(da, jump(pa.row, m2.row)); k <= D; k++) {
          const ok = reach(M, k, nu, m2);
          bump(ok ? 'CutOriginReach ok' : 'FAIL CutOriginReach', ok ? null : where(tag + ` k=${k}`));
        }
      }
      // CutJumpTop
      if (cmp(pe.row, u.row) < 0) {
        const de = jump(u.row, pe.row), da = jump(o.row, pa.row);
        let ok = de <= da;
        for (let kk = Math.max(de, da); !ok && kk <= D; kk++) if (root(R, kk, pe).c < phi(root(M, kk, pa).c)) ok = true;
        bump(ok ? 'CutJumpTop ok (used)' : 'FAIL CutJumpTop', ok ? null : where(tag));
      } else bump('CutJumpTop ok (same row)');
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
