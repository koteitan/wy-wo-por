// Numerical test of the seam statements (OmegaY/Official/Classification/Proofs/Seam*.lean,
// namespace Recon.TopChain.Seam): the targets TopStepLoRoot, TopStartLoRoot, BoundaryChain and the
// open pieces they are reduced to.
//
// Usage: node seam-open.cjs [--copies 1,2,3] [--maxnodes N] [--legal MAXLEN,MAXVAL]
//          [--random COUNT,MAXLEN,MAXVAL,SEED] [--budget SECONDS] [SAMPLE.json ...]
//
// Notation (lower-chain.cjs): block i >= 1 of s[n], w = x0 - cr, B_i = cr + w i, tau = row of the
// top of x0. A node Q of a new column (X >= x0) has the origin o = the source of its emit.
//   ChainOK(Q)   : for every scale k and every node mu left of cr on the M k-chain of o,
//                  mu is on the R k-chain of Q (BoundaryChain is ChainOK on the columns B_i).
//   Step(Q)      : the one step behind ChainOK: if the M k-chain of o reaches a node left of cr,
//                  the first such node f is on the M k-chain of orig(Q1), Q1 = rawParent_R(Q),
//                  jump(Q, Q1) <= k (orig(Q1) = Q1 for an old column), split by the kind of Q:
//                  StepX0Top, StepCleanNT, StepCutNT (open) and the proved kinds.
//   CutParentNT  : u a gap copy of m (block i >= 1) that is not the top copy of m: the stored parent u1
//                  of u is in B_i and the leg of m is cr (with a node of cr at the row of m), or u1 is
//                  a gap copy, not the top copy, of the node b of the leg column of m at the row of m.
//   StepRootTop  : TopStepLoRoot, a+ >= tau: the node above A has the row of a+.
//   StartRootTop : TopStartLoRoot, pa+ >= tau: the node above pe has the row of pa+.
//   TopStepLoRoot, TopStartLoRoot: the full Stand (top-chain.cjs).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, degree, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], maxNodes = 800, budget = Infinity;
const rng = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--budget') budget = Number(args[++a]) * 1000;
  else if (args[a] === '--legal') {
    const [K, V] = args[++a].split(',').map(Number);
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  } else if (args[a] === '--random') {
    const [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
  } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
}

const same = (a, b) => !!a && !!b && a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const rawParent = (A, z) => { const v = above(A, z); return v && v.pc >= 0 ? A[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k || p.c >= u.c) return L; u = p; L.push(u); } };
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
const nm = z => z ? `(${z.c},${z.k}:${show(z.row)}${z.prov ? '|' + z.prov.kind[0] + (z.prov.ib ? '!' : '') : ''})` : 'null';

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);
const seen = new Set(); let expansions = 0; const t0 = Date.now();
const dump = head => { console.log(`${head}sequences ${seen.size}, expansions ${expansions}, ${(Date.now() - t0) / 1000}s`); for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('            e.g.', m); } };
process.on('SIGTERM', () => { dump('=== stopped by SIGTERM (partial): '); process.exit(0); });

for (const s of inputs) {
  if (Date.now() - t0 > budget) { bump('budget reached; inputs not taken'); break; }
  const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue; seen.add(key);
  for (const n of copies) {
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error', `(${s})[${n}]`); continue; }
    if (!r.root) continue;
    if (r.R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes)'); break; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, tt = M[x0][M[x0].length - 1], cr = tt.pc, w = x0 - cr, tau = tt.row;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row)); D += 2;
    const where = x => `(${s})[${n}] ${x}`;
    const phi = (c, i) => c < cr ? c : c + w * i;
    const topCopy = (i, z) => { const X = z.c + w * i; let T = null; if (R[X]) for (const v of R[X]) if (v.i === i && v.prov && same(v.prov.src, z)) T = v; return T; };
    const reachR = (k, v, t) => chain(R, k, v).some(q => same(q, t));
    const isTop = (i, Z, z) => { const T = topCopy(i, z); return !!T && same(T, Z) && (cmp(z.row, tau) < 0 || cmp(Z.row, z.row) === 0); };
    const stand = (i, A, a) => {
      if (!A || !a) return false;
      if (a.c < cr) return same(A, a);
      if (a.c === cr) {
        if (A.c !== cr + w * i) return false;
        const ap = above(M, a);
        if (ap && cmp(ap.row, tau) >= 0) { const Ap = above(R, A); if (!Ap || cmp(Ap.row, ap.row) !== 0) return false; }
        const b = rawParent(M, a);
        if (b && !reachR(jump(a.row, b.row), A, b)) return false;
        return true;
      }
      if (a.c >= x0) return false;
      return isTop(i, A, a);
    };
    // ChainOK and the step, for every node of a new column
    for (let X = x0; X < R.length; X++) for (let j = 0; j < R[X].length; j++) {
      const Q = R[X][j], o = Q.prov.src, i = Q.i;
      let T = null; for (const v of R[X]) if (v.prov && same(v.prov.src, o)) T = v;
      const top = same(T, Q);
      const low = cmp(Q.row, tau) < 0;
      let kind;
      if (i === 0) kind = 'StepBlock0 (proved)';
      else if (!low || Q.prov.kind === 'upper') kind = 'StepUpper (proved)';
      else if (top && Q.x !== x0) kind = 'StepTop (proved)';
      else if (top) kind = 'StepX0Top';
      else if (isCut(Q)) kind = 'StepCutNT';
      else kind = 'StepCleanNT';
      const bnd = Q.x === x0;
      if (kind === 'StepCutNT') {
        const l = leg(o), b = M[l] && M[l].find(q => cmp(q.row, o.row) === 0);
        const u1 = rawParent(R, Q);
        let ok;
        if (!u1) ok = false;
        else if (u1.c === cr + w * i) ok = l === cr && !!b;
        else { let T1 = null; for (const v of R[u1.c]) if (v.prov && same(v.prov.src, u1.prov.src)) T1 = v; ok = isCut(u1) && !!b && same(u1.prov.src, b) && !same(T1, u1); }
        res('CutParentNT', ok, where(`u=${nm(Q)} u1=${nm(u1)} m=${nm(o)}`));
      }
      for (let k = 0; k <= D; k++) {
        const Lm = chain(M, k, o).filter(q => q.c < cr), Lr = chain(R, k, Q);
        const okC = Lm.every(q => Lr.some(p => same(p, q)));
        res(`ChainOK${bnd ? ' [BoundaryChain: copy of x0]' : ''}`, okC, where(`Q=${nm(Q)} k=${k}`));
        if (!Lm.length) continue;
        const f = Lm[0], Q1 = rawParent(R, Q);
        let ok = !!Q1 && jump(Q.row, Q1.row) <= k && Q1.c < Q.c;
        if (ok) ok = chain(M, k, Q1.c < x0 ? Q1 : Q1.prov.src).some(q => same(q, f));
        res(`Step: ${kind}`, ok, where(`Q=${nm(Q)} o=${nm(o)} k=${k} f=${nm(f)} Q1=${nm(Q1)}`));
      }
    }
    // TopStepLoRoot and StepRootTop
    for (let i = 1; i <= n; i++) {
      const last = i < n ? x0 : x0 - 1;
      for (let y = cr + 1; y < x0 && y <= last; y++) for (const z of M[y]) {
        const Z = topCopy(i, z); if (!Z) continue;
        const a = rawParent(M, z); if (!a || a.c !== cr) continue;
        const zp = above(M, z); if (cmp(zp.row, tau) >= 0) continue;
        const A = rawParent(R, Z);
        const w2 = where(`i=${i} z=${nm(z)} Z=${nm(Z)} a=${nm(a)} A=${nm(A)}`);
        res('TopStepLoRoot (Stand and jump)', stand(i, A, a) && !!A && jump(Z.row, A.row) <= jump(z.row, a.row), w2);
        const ap = above(M, a);
        if (ap && cmp(ap.row, tau) >= 0) { const Ap = above(R, A); res('StepRootTop', !!Ap && cmp(Ap.row, ap.row) === 0, w2); }
        const nu = A.prov.src;
        res('StepRootLookup (proved)', A.prov.kind !== 'upper' && same(hAM(M, cr, nu.row), a), w2);
      }
    }
    // TopStartLoRoot and StartRootTop
    for (let X = x0; X < R.length; X++) for (const u of R[X]) {
      const i = u.i; if (i === 0 || !u.prov) continue;
      const o = u.prov.src; if (cmp(o.row, tau) >= 0) continue;
      let T = null; for (const v of R[X]) if (v.prov && same(v.prov.src, o)) T = v;
      if (!same(T, u)) continue;
      const la = leg(o); if (la !== cr) continue;
      const pe = hAM(R, phi(la, i), u.row), pa = hAM(M, la, o.row);
      const w3 = where(`X=${X} u=${nm(u)} o=${nm(o)} pa=${nm(pa)} pe=${nm(pe)}`);
      res('TopStartLoRoot (Stand)', stand(i, pe, pa), w3);
      const pap = above(M, pa);
      if (pap && cmp(pap.row, tau) >= 0) { const pep = above(R, pe); res('StartRootTop', !!pep && cmp(pep.row, pap.row) === 0, w3); }
      res('StartRootLookup (proved)', pe.prov.kind !== 'upper' && same(hAM(M, cr, pe.prov.src.row), pa), w3);
    }
  }
}
dump('=== final: ');
