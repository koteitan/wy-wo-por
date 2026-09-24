// Numerical test of the corrected start `TopStart'` (OmegaY/Official/Classification/Proofs/
// TopStartFix*.lean, namespace ChainCorr.TopStartFix).
//
// Usage: node top-start-fix.cjs [--copies 1,2,3] [--maxnodes N] [--legal MAXLEN,MAXVAL]
//          [--random COUNT,MAXLEN,MAXVAL,SEED] [--filtered COUNT,MAXLEN,MAXVAL,SEED]
//          [--budget SECONDS] [SAMPLE.json ...]
// --filtered: random inputs as --random, kept only when M(s) has a node o in a column
//   (c_r, x0] with row o < tau, leg l > c_r, and a node of the column l at the row of o
//   (the mountain condition of the counterexamples of `TopStart`).
// --state FILE: resumable run; the counts and the next input are saved every 50 inputs, and a
//   saved list of excluded inputs (indices) is skipped (see top-start-fix-driver.cjs).
// --trace: print every input before it is expanded.
// --filter-up (before --filtered): also ask that o has a node above it and that the root column
//   has a node at the row of o (the non-vacuous cases of TopStartPaOUp).
//
// Notation as in lower-chain.cjs / top-chain.cjs: block i >= 1 of s[n], w = x0 - cr,
// phi(c) = c (c < cr), c + w i (c >= cr), tau the row of the top of x0. For the top copy u of its
// origin o in a column X of block i (X >= x0), l = leg(o), pa = hAM(M, l, row o),
// pe = hAM(R, phi(l), row u).
//   Stand(pe, pa)   : as in lower-chain.cjs (col pa > cr: pe is the top copy of pa).
//   StandW(pe, pa)  : the same, but col pa > cr: Rel(pe, pa), Rel = CopyNode or Top; and col pa = cr:
//                     only col pe = cr + w i and the chain clause (no clause for the node above).
//   TopStartW       : StandW(pe, pa) for every such u.                       (TopStart')
//   TopStartUp      : Stand(pe, pa) when o has a node o+ above it in M with row o+ < tau
//                     (HasAboveLow; TopStart'). The form with row o+ >= tau (what CopyQLower
//                     would use) is only reported: it is false, (1,21,5,20,30,23,20)[1].
//   TopStart        : Stand(pe, pa) for every u (reported: false).
//   piece ...       : the open pieces of TopStartFixParts.lean (TopStartLoRootW, StartRootTopUp,
//                     TopStartPaOUp, TopStartCutRight) and a check of the proved startPaORel.
//   (check) TopStep : Stand(A, a) for the stored parent A of the top copy Z of z and the stored
//                     parent a of z (as in lower-chain.cjs), split by the rows of z, z+ and col a.
//   StandCG (report): col pa > cr: pe is a non-gap copy of pa and every copy of pa above pe
//                     in its column is a gap copy.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let trace = false, stateFile = null;
let copies = [1, 2, 3], maxNodes = 800, budget = Infinity, progress = 0, maxM = Infinity, skip = 0, take = Infinity;
const rng = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const leg = u => u.k > 0 ? u.pc : u.c - 1;
let filteredStat = null;
const genSeen = new Set();
let filterUp = false;
const filt = s => {
  let M; try { M = O.mountain(s); } catch (e) { return false; }
  const x0 = s.length - 1, tc = M[x0][M[x0].length - 1];
  if (tc.pc < 0) return false;
  const cr = tc.pc, tau = tc.row;
  for (let c = cr + 1; c <= x0; c++) for (const o of M[c]) {
    if (cmp(o.row, tau) >= 0) continue;
    const l = leg(o); if (l <= cr) continue;
    if (filterUp && (!M[c][o.k + 1] || cmp(M[c][o.k + 1].row, tau) >= 0 || !M[cr].some(q => cmp(q.row, o.row) === 0))) continue;
    if (M[l].some(q => cmp(q.row, o.row) === 0)) return true;
  }
  return false;
};
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--budget') budget = Number(args[++a]) * 1000;
  else if (args[a] === '--progress') progress = Number(args[++a]);
  else if (args[a] === '--filter-up') filterUp = true;
  else if (args[a] === '--maxM') maxM = Number(args[++a]);
  else if (args[a] === '--skip') skip = Number(args[++a]);
  else if (args[a] === '--take') take = Number(args[++a]);
  else if (args[a] === '--trace') trace = true;
  else if (args[a] === '--state') stateFile = args[++a];
  else if (args[a] === '--legal') {
    const [K, V] = args[++a].split(',').map(Number);
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  } else if (args[a] === '--random' || args[a] === '--filtered') {
    const f = args[a] === '--filtered';
    const [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    let kept = 0;
    for (let t = 0; t < count; t++) {
      const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1];
      while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal));
      const k = s.join(',');
      if (genSeen.has(k)) continue;
      genSeen.add(k);
      if (!f || filt(s)) { inputs.push(s); kept++; }
    }
    if (f) filteredStat = `filtered: ${kept} distinct inputs kept of ${count} random draws`;
  } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
}
if (filteredStat) console.log(filteredStat);

const same = (a, b) => !!a && !!b && a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const rawParent = (A, z) => { const v = above(A, z); return v && v.pc >= 0 ? A[v.pc][v.pk] : null; };
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k || p.c >= u.c) return L; u = p; L.push(u); } };
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
const nm = z => z ? `(${z.c},${z.k}:${show(z.row)}${z.prov ? '|' + z.prov.kind[0] + (z.prov.ib ? '!' : '') : ''})` : 'null';

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);
const seen = new Set(); let expansions = 0; const t0 = Date.now();
const dump = head => { console.log(`${head}sequences ${seen.size}, expansions ${expansions}, ${(Date.now() - t0) / 1000}s`); for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('            e.g.', m); } };
process.on('SIGTERM', () => { dump('=== stopped by SIGTERM (partial): '); process.exit(0); });

let taken = 0, excluded = [];
if (stateFile && fs.existsSync(stateFile)) {
  const st = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
  skip = st.next; Object.assign(stat, st.stat); Object.assign(ex, st.ex); expansions = st.expansions;
  excluded = st.excluded || []; for (let q = 0; q < st.done; q++) seen.add(`#done${q}`);
}
const saveState = () => { if (stateFile) fs.writeFileSync(stateFile, JSON.stringify({next: skip + taken, done: seen.size, stat, ex, expansions, excluded})); };
for (const s of inputs.slice(skip, skip + take)) {
  if (stateFile && taken % 50 === 0) saveState();
  if (Date.now() - t0 > budget) { bump('budget reached; inputs not taken'); break; }
  taken++;
  const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  if (excluded.includes(skip + taken)) { bump('  excluded (an expansion stalled; see --state)', key); continue; }
  seen.add(key);
  if (progress && seen.size % progress === 0) dump(`--- progress (input #${skip + taken}, last ${key}): `);
  if (maxM < Infinity) { let z = 0; try { for (const col of O.mountain(s)) z += col.length; } catch (e) { z = Infinity; } if (z > maxM) { bump('skipped (M(s) larger than --maxM)'); continue; } }
  const tIn = Date.now();
  if (trace) console.log(`trace #${skip + taken}: ${key}`);
  for (const n of copies) {
    if (Date.now() - t0 > budget) break;
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error', `(${s})[${n}]`); continue; }
    if (!r.root) continue;
    if (r.R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes)'); break; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, tt = M[x0][M[x0].length - 1], cr = tt.pc, w = x0 - cr, tau = tt.row;
    const rho = M[tt.pc][tt.pk];
    const phi = (c, i) => c < cr ? c : c + w * i;
    const topCopy = (i, z) => { const X = z.c + w * i; let T = null; if (R[X]) for (const v of R[X]) if (v.i === i && v.prov && same(v.prov.src, z)) T = v; return T; };
    const reachR = (k, v, t) => chain(R, k, v).some(q => same(q, t));
    const isTop = (i, Z, z) => { const T = topCopy(i, z); return !!T && same(T, Z) && (cmp(z.row, tau) < 0 || cmp(Z.row, z.row) === 0); };
    const inner = (u, i) => !!u && u.i === i && u.x !== x0 && u.x > cr && u.x < x0;
    const isCopyN = (i, u, m) => inner(u, i) && u.c === m.c + w * i && !!u.prov && same(u.prov.src, m) && (!isCut(u) || !rawParent(M, m));
    const rel = (i, u, m) => isCopyN(i, u, m) || (m.c > cr && m.c < x0 && isTop(i, u, m));
    const standGen = (i, A, a, right, upClause = true) => {
      if (!A || !a) return false;
      if (a.c < cr) return same(A, a);
      if (a.c === cr) {
        if (A.c !== cr + w * i) return false;
        const ap = above(M, a);
        if (upClause && ap && cmp(ap.row, tau) >= 0) { const Ap = above(R, A); if (!Ap || cmp(Ap.row, ap.row) !== 0) return false; }
        const b = rawParent(M, a);
        if (b && !reachR(jump(a.row, b.row), A, b)) return false;
        return true;
      }
      if (a.c >= x0) return false;
      return right(i, A, a);
    };
    const stand = (i, A, a) => standGen(i, A, a, isTop);
    const standW = (i, A, a) => standGen(i, A, a, rel, false);
    const cgTop = (i, A, a) => {
      if (!inner(A, i) || A.c !== a.c + w * i || !A.prov || !same(A.prov.src, a) || isCut(A)) return false;
      for (const v of R[A.c]) if (v.k > A.k && v.prov && same(v.prov.src, a) && !isCut(v)) return false;
      return true;
    };
    // (check) TopStep: the stand-in of the stored parent of a top copy (lower-chain.cjs); the
    // clause of Stand on the node above is what CopyStepLower uses through cp_of_stand.
    for (let i = 1; i <= n; i++) {
      const last = i < n ? x0 : x0 - 1;
      for (let y = cr + 1; y < x0 && y <= last; y++) for (const z of M[y]) {
        const Z = topCopy(i, z); if (!Z) continue;
        const a = rawParent(M, z); if (!a) continue;
        const A = rawParent(R, Z), zp = above(M, z);
        const zk = cmp(z.row, tau) >= 0 ? 'z>=tau' : cmp(zp.row, tau) >= 0 ? 'z<tau<=z+' : 'z+<tau';
        const ak = a.c < cr ? 'a<cr' : a.c === cr ? 'a=cr' : 'a>cr';
        res(`  (check) TopStep Stand [${zk}, ${ak}]`, stand(i, A, a), `(${s})[${n}] i=${i} z=${nm(z)} Z=${nm(Z)} a=${nm(a)} A=${nm(A)}`);
      }
    }
    for (let X = x0; X < R.length; X++) for (const u of R[X]) {
      const i = u.i; if (!i || !u.prov) continue;
      const o = u.prov.src;
      let T = null; for (const v of R[X]) if (v.prov && same(v.prov.src, o)) T = v;
      if (!same(T, u)) continue;
      const la = leg(o); if (la < 0) continue;
      const pe = hAM(R, phi(la, i), u.row), pa = hAM(M, la, o.row);
      if (!pe || !pa) { bump('  a lookup is missing (premise false)'); continue; }
      const lcase = la < cr ? 'l<cr' : la === cr ? 'l=cr' : 'l>cr';
      const kind = u.prov.kind + (isCut(u) ? '!' : '');
      const hi = cmp(o.row, tau) >= 0 ? 'o>=tau' : 'o<tau';
      const op = above(M, o);
      const where = `(${s})[${n}] X=${X} u=${nm(u)} o=${nm(o)} pa=${nm(pa)} pe=${nm(pe)}`;
      const full = stand(i, pe, pa);
      res(`TopStartW [${hi}, ${lcase}, ${kind}]`, standW(i, pe, pa), where);
      const opLow = !!op && cmp(op.row, tau) < 0;
      if (opLow) res(`TopStartUp [${hi}, ${lcase}, ${kind}]`, full, where + ` o+=${nm(op)}`);
      else if (op) res(`  (report) TopStartUp with o+ >= tau (not asked) [${hi}, ${lcase}, ${kind}]`, full, where + ` o+=${nm(op)}`);
      res(`  (report) TopStart [${hi}, ${lcase}, ${kind}]`, full, where);
      // the pieces of TopStartFixParts.lean (row o < tau)
      if (hi === 'o<tau' && la === cr) {
        res('piece TopStartLoRootW', standW(i, pe, pa), where);
        if (opLow) {
          const pap = above(M, pa);
          let ok = true;
          if (pap && cmp(pap.row, tau) >= 0) { const pep = above(R, pe); ok = !!pep && cmp(pep.row, pap.row) === 0; }
          res(`piece StartRootTopUp [${pap && cmp(pap.row, tau) >= 0 ? 'pa+>=tau, non-vacuous' : 'vacuous'}]`, ok, where);
        }
        const pap = above(M, pa);
        if (pap && cmp(pap.row, tau) >= 0) { const pep = above(R, pe); res('  (report) StartRootTop (no HasAbove; false)', !!pep && cmp(pep.row, pap.row) === 0, where); }
      }
      if (hi === 'o<tau' && la > cr) {
        const paO = cmp(pa.row, o.row) === 0;
        if (!isCut(u) && paO) {
          res('  (proved) startPaORel: pe is a non-gap copy of pa', isCopyN(i, pe, pa), where);
          if (opLow) {
            const gap = R[pe.c].some(v => v.prov && same(v.prov.src, pa) && isCut(v));
            res(`piece TopStartPaOUp [${gap ? 'a gap copy of pa in phi(l), non-vacuous' : 'no gap copy of pa'}]`, isTop(i, pe, pa), where);
          }
        }
        if (isCut(u)) {
          res('piece TopStartCutRight [Rel]', rel(i, pe, pa), where);
          if (opLow) res('piece TopStartCutRight [HasAboveLow -> Top]', isTop(i, pe, pa), where);
          res('  (report) TopStartCutRight strong form: Top for every gap copy', isTop(i, pe, pa), where);
        }
      }
      if (!full) {
        const sr = cmp(pa.row, o.row) === 0 ? 'pa=o' : 'pa<o';
        const rr = cmp(o.row, rho.row) === 0 ? 'o=rho' : cmp(o.row, rho.row) < 0 ? 'o<rho' : 'o>rho';
        bump(`  (report) TopStart failure profile [${kind}, ${lcase}, ${sr}, ${rr}, o+ ${op ? 'exists' : 'none'}, ${X === x0 + w * i ? 'x0' : 'inner'}]`, where);
        if (la > cr) res('  (report) StandCG on the TopStart failures', cgTop(i, pe, pa), where);
      }
    }
  }
  if (Date.now() - tIn > 5000) bump('  slow input (> 5 s)', `${key}: ${Date.now() - tIn} ms`);
}
saveState();
dump(`=== final (inputs #${skip + 1}..#${skip + taken} of the list): `);
