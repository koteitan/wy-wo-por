// Numerical test of the chain statements with skips of
// OmegaY/Official/Classification/Proofs/ChainSkip.lean (namespace ChainCorr.Skip).
//
// Usage: node chain-skip.cjs [--copies 1,2,3] [--depth DMAX] [--extraD K] [--maxnodes N]
//                            [--legal MAXLEN,MAXVAL] [--random COUNT,MAXLEN,MAXVAL,SEED]
//                            [--progress N] [--budget SECONDS] [SAMPLE.json ...]
// --progress N prints the counts so far every N sequences; --budget stops taking new sequences
// after that time; SIGTERM prints the counts so far. The final block is marked "=== final".
//
// The expansion is the rule of omegay-trace.cjs. Notation as in chain-corr.cjs, cut-regions.cjs:
// cr the root column, w = x0 - cr, B = cr + w i, phi(c) = c (c < cr), c + w i (c >= cr).
// An M step m -> m' at scale k: m' = rawParent(m), jump(row m, row m') <= k.
// Copy(v, m): v is a node of an inner column y + w i (cr < y < x0) of block i with origin m, not a
// gap copy unless m has no raw parent. Cut(v, m): the same with a gap copy (b = 1) of m.
// CutRel = Copy or Cut.
// Next_Q(k, v, m'): m' < cr: the R k-chain of v reaches m'; m' = cr: it reaches a node q with
//   col q <= B whose R k-chain reaches m'' whenever m' -> m'' is an M step at k; m' > cr: it
//   reaches a node q with Q(q, m').
// SkipN_Q(0) = Q; SkipN_Q(d+1)(v, m) = SkipN_Q(d)(v, m) or (col v <= phi(col m) and for the M step
//   m -> m'' at k (if any) Next_{SkipN_Q(d)}(k, v, m'')). Sk_Q = SkipN_Q(DMAX) (default DMAX 4;
//   the depth actually used is reported).
// D (for the lexicographic statements) = the largest degree of a row of M(s) and the output
// (plus K with --extraD); the other statements are tested for every k up to that D + 2.
// Statements (Lean names, ChainCorr.Skip unless noted):
//  StepInnerSkip  : Copy(v, m), M step m -> m' at k: Next_{Sk_Copy}(k, v, m').
//  For a node u of block i >= 1 with origin o, la = leg(o), pa = hAM(M, la, row o),
//  pe = hAM(R, phi(la), row u), da = jump(row o, row pa), de = jump(row u, row pe):
//  (not a gap copy)
//  LeftStart      : la < cr, not (upper and la < cr): de <= da and for every k >= da the R k-chain
//                   of pe and the M k-chain of pa have a common node.
//  LeftRow        : la < cr, plain origin: row u = row o (also: the origin is plain).
//  StartJumpGe    : la >= cr: de <= da.
//  StartCopySkip  : la > cr: for every k >= da, Sk_Copy(k)(pe, pa).
//  StartRoot      : (ChainCorr) la = cr: for every k >= da and M step pa -> m'' at k, the R k-chain
//                   of pe reaches m''.
//  (gap copies)
//  StepCutSkip    : Cut(v, m), k <= D, M step m -> m' at k: Next_{Sk_CutRel}(k, v, m') or Wit(k, v, m)
//                   (some k < k' <= D has col root_R(k', v) < phi(col root_M(k', m))).
//  CutJumpD       : (label "CutJump") da <= D: de <= da, or some max(de, da) <= k' <= D has
//                   col root_R(k', pe) < phi(col root_M(k', pa)). The gap copies with da > D (an
//                   all-top origin key, proved by keyLe_allTop) are skipped, as in cut-regions.cjs.
//  CutStartCopySkip: la > cr: for da <= k <= D, Sk_CutRel(k)(pe, pa).
//  CutStartRoot   : (ChainCorr) la = cr: for da <= k <= D and M step pa -> m'' at k, the R k-chain of
//                   pe reaches m''.
//  CutLeg         : (ChainCorr, proved) la >= cr for a gap copy.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, degree, expandMountain} = O;
const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k) return L; u = p; L.push(u); } };
const root = (A, k, u) => { const L = chain(A, k, u); return L[L.length - 1]; };
const same = (a, b) => a === b || (!!a && !!b && a.c === b.c && a.k === b.k);
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], DMAX = 4, extraD = 0, maxNodes = Infinity, progress = 0;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--depth') DMAX = Number(args[++a]);
  else if (args[a] === '--extraD') extraD = Number(args[++a]);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--progress') progress = Number(args[++a]);
  else if (args[a] === '--budget') ++a;
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
const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);
const seen = new Set(); let expansions = 0; const t0 = Date.now();
const dump = head => { console.log(`${head}sequences ${seen.size}, expansions ${expansions}, ${(Date.now() - t0) / 1000}s`); for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); } };
process.on('SIGTERM', () => { dump('=== stopped by SIGTERM (partial): '); process.exit(0); });
let budget = Infinity; { const b = process.argv.indexOf('--budget'); if (b >= 0) budget = Number(process.argv[b + 1]) * 1000; }
for (const s of inputs) {
  if (Date.now() - t0 > budget) { bump('budget reached; inputs not taken', null); break; }
  const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue; seen.add(key);
  if (progress && seen.size % progress === 0) dump(`--- progress (last input ${key}): `);
  for (const n of copies) {
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error', `(${s})[${n}]`); continue; }
    if (r.R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes)'); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += extraD;
    const Dall = D + 2;
    const phi = (c, i) => c < cr ? c : c + w * i;
    const inner = (u, i) => !!u && u.i === i && u.x !== x0 && u.x > cr && u.x < x0;
    const isCopy = i => (u, m) => inner(u, i) && u.c === m.c + w * i && same(u.prov.src, m) && (!isCut(u) || !rawParent(M, m));
    const isCutN = i => (u, m) => inner(u, i) && u.c === m.c + w * i && isCut(u) && same(u.prov.src, m);
    const isRel = i => (u, m) => isCopy(i)(u, m) || isCutN(i)(u, m);
    // M step from m at scale k (or null)
    const mstep = (k, m) => { const p = rawParent(M, m); return p && jump(m.row, p.row) <= k && p.c < m.c ? p : null; };
    const next = (k, v, m2, i, Q) => {
      const cR = chain(R, k, v);
      if (m2.c < cr) return cR.some(q => same(q, m2));
      if (m2.c === cr) { const m3 = mstep(k, m2); return cR.some(q => q.c <= cr + w * i && (!m3 || reach(R, k, q, m3))); }
      return cR.some(q => Q(q, m2));
    };
    // SkipN_Q(d) with memo; returns the least d <= DMAX that works, or -1
    const skipDepth = (k, i, Q) => {
      const memo = new Map();
      const f = (d, v, m) => {
        const kk = `${d}|${v.c},${v.k}|${m.c},${m.k}`;
        if (memo.has(kk)) return memo.get(kk);
        let ok;
        if (d === 0) ok = Q(v, m);
        else {
          ok = f(d - 1, v, m);
          if (!ok && v.c <= phi(m.c, i)) { const m3 = mstep(k, m); ok = !m3 || next(k, v, m3, i, (q, m4) => f(d - 1, q, m4)); }
        }
        memo.set(kk, ok); return ok;
      };
      return (v, m) => { for (let d = 0; d <= DMAX; d++) if (f(d, v, m)) return d; return -1; };
    };
    const skCache = new Map();
    const Sk = (k, i, rel) => { const kk = `${k}|${i}|${rel}`; if (!skCache.has(kk)) skCache.set(kk, skipDepth(k, i, rel === 'copy' ? isCopy(i) : isRel(i))); return skCache.get(kk); };
    const wit = (k, v, m, i) => { for (let kk = k + 1; kk <= D; kk++) if (root(R, kk, v).c < phi(root(M, kk, m).c, i)) return true; return false; };
    let depthMax = 0;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      const i = v.i; if (i === 0) continue;
      const m = v.prov.src;
      const where = `(${s})[${n}] X=${X} v=(${v.c},${v.k}:${show(v.row)})`;
      // StepInnerSkip
      if (isCopy(i)(v, m)) {
        const mp = rawParent(M, m);
        if (mp) for (let k = jump(m.row, mp.row); k <= Dall; k++) {
          let used = -1;
          const ok = next(k, v, mp, i, (q, m2) => { const d = Sk(k, i, 'copy')(q, m2); if (d >= 0) used = Math.max(used, d); return d >= 0; });
          res(`StepInnerSkip (m' ${mp.c < cr ? '<' : mp.c === cr ? '=' : '>'} cr)`, ok, where + ` k=${k}`);
          if (ok && used > 0) bump(`  StepInnerSkip needed skip depth ${used}`);
          res('StepInnerSkipOne (depth <= 1)', ok && used <= 1, where + ` k=${k}`);
          if (!next(k, v, mp, i, isCopy(i))) bump('  StepInner (old, no skip) false here', where + ` k=${k}`);
        }
      }
      // StepCutSkip
      if (isCutN(i)(v, m)) {
        const mp = rawParent(M, m);
        if (mp) for (let k = jump(m.row, mp.row); k <= D; k++) {
          const okN = next(k, v, mp, i, (q, m2) => Sk(k, i, 'rel')(q, m2) >= 0);
          const ok = okN || wit(k, v, m, i);
          res('StepCutSkip', ok, where + ` k=${k}`);
          res('StepCut (old, no skip)', next(k, v, mp, i, isRel(i)) || wit(k, v, m, i), where + ` k=${k}`);
          if (ok) bump(`  StepCutSkip answered by ${okN ? 'Next' : 'Wit'}`);
        }
      }
      // the region nodes (index >= 1 in Lean = every JS node of a copied column)
      const la = leg(m), cut = isCut(v), up = v.prov.kind === 'upper';
      if (cut && la < cr) { res('CutLeg (proved)', false, where); continue; }
      if (!cut && up && la < cr) continue; // not a region node (proved upper case)
      const pe = hAM(R, phi(la, i), v.row), pa = hAM(M, la, m.row);
      if (!pe || !pa) { res('lookup exists', false, where); continue; }
      const da = jump(m.row, pa.row), de = jump(v.row, pe.row);
      if (!cut) {
        if (la < cr) {
          let ok = de <= da;
          for (let k = da; k <= Dall && ok; k++) { const cM = chain(M, k, pa); if (!chain(R, k, pe).some(q => cM.some(p => same(p, q)))) ok = false; }
          res('LeftStart', ok, where);
          res('LeftRow (plain, row u = row o)', v.prov.kind === 'plain' && cmp(v.row, m.row) === 0, where);
        } else {
          res('StartJumpGe', de <= da, where);
          if (la > cr) {
            let ok = true, used = 0;
            for (let k = da; k <= Dall; k++) { const d = Sk(k, i, 'copy')(pe, pa); if (d < 0) ok = false; else used = Math.max(used, d); }
            res('StartCopySkip', ok, where);
            if (ok) bump(`  StartCopySkip needed skip depth ${used}`);
            res('StartCopySkipOne (depth <= 1)', ok && used <= 1, where);
            if (!isCopy(i)(pe, pa)) bump('  StartCopy (old, no skip) false here', where);
          } else {
            let ok = true;
            for (let k = da; k <= Dall; k++) { const mpp = mstep(k, pa); if (mpp && !reach(R, k, pe, mpp)) ok = false; }
            res('StartRoot', ok, where);
          }
        }
      } else {
        if (da > D) { bump('  gap copy with an all-top origin key (no check)'); continue; }
        let okJ = de <= da;
        if (!okJ) for (let kk = Math.max(de, da); kk <= D; kk++) if (root(R, kk, pe).c < phi(root(M, kk, pa).c, i)) okJ = true;
        res('CutJump', okJ, where);
        if (la > cr) {
          let ok = true, used = 0;
          for (let k = da; k <= D; k++) { const d = Sk(k, i, 'rel')(pe, pa); if (d < 0) ok = false; else used = Math.max(used, d); }
          res('CutStartCopySkip', ok, where);
          res('CutStartCopy (old, CutNode pe pa)', isCutN(i)(pe, pa), where);
          if (ok) bump(`  CutStartCopySkip needed skip depth ${used}`);
        } else {
          let ok = true;
          for (let k = da; k <= D; k++) { const mpp = mstep(k, pa); if (mpp && !reach(R, k, pe, mpp)) ok = false; }
          res('CutStartRoot', ok, where);
        }
      }
    }
  }
}
dump('=== final: ');
