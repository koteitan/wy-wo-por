// Numerical test of the open statements of package 3
// (OmegaY/Official/Classification/Proofs/Pkg3Jump.lean, Pkg3Run.lean), and of CutJump itself.
//
// Usage: node pkg3-rows.cjs [--copies 1,2,3] [--budget SEC] [--maxM N] [--legal MAXLEN,MAXVAL]
//                           [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs, n = 1, 2, 3 (an input is not expanded for a
// larger n once its output has more than 800 nodes or a column with more than 80 nodes;
// --maxM skips inputs whose M(s) has more than N nodes; --budget stops after SEC seconds).
// D = the largest degree of a row of M(s) and of the output.
// For a gap copy u (origin {kind: 'clean', ib: true}) of block i >= 1 with origin o = (x, C),
// leg l of o, pa = hAM(M, l, C), pe = hAM(R, phi(l), row u) (hAM: the highest node of index > 0
// at or below the row, as Lean's highestAtMost; inputs without pa or pe are vacuous):
//  CutJump       : row pe = row u, or some jump(row u, row pe) <= k' <= D has
//                  col root_R(k', pe) < phi(col root_M(k', pa)).
//  CutJumpRootRow: l = cr, row pe != row u => pe has a raw parent q, and if pa has a raw parent b,
//                  jump(row pe, row q) < jump(row pa, row b).
//  CutJumpRun    : l > cr, row pe != row u => the node above pe is a gap copy of pa.
//  CutRunTop     : l > cr => the column phi(l) has a gap copy of pa at a row >= row u.
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
// Lean highestAtMost: index > 0
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (q.k > 0 && cmp(q.row, row) <= 0) p = q; return p; };
function parseInputs(args) {
  const inputs = []; const opt = {extraD: 0, copies: [1, 2, 3], maxNodes: 800, maxCol: 80, budget: 1e9, maxM: 1e9};
  for (let a = 0; a < args.length; a++) {
    if (args[a] === '--extraD') opt.extraD = +args[++a];
    else if (args[a] === '--budget') opt.budget = +args[++a];
    else if (args[a] === '--maxM') opt.maxM = +args[++a];
    else if (args[a] === '--copies') opt.copies = args[++a].split(',').map(Number);
    else if (args[a] === '--legal') {
      const [K, V] = args[++a].split(',').map(Number);
      const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
      rec([1]);
    } else if (args[a] === '--legalN') { // exactly length K
      const [K, V] = args[++a].split(',').map(Number);
      const rec = s => { if (s.length === K) { inputs.push(s.slice()); return; } for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
      rec([1]);
    } else if (args[a] === '--random') {
      let [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
      const rnd = () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
      for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
    } else if (args[a] === '--sample') { // uniform sample of fraction p
      let [K, V, p, seed] = args[++a].split(',').map(Number);
      const rnd = () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
      const rec = s => { if (s.length === K) { if (rnd() < p) inputs.push(s.slice()); return; } for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
      rec([1]);
    } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
  }
  return {inputs, opt};
}
// iterate expansions; cb({s,n,M,R,x0,cr,w,D,t})
function forEach(inputs, opt, cb) {
  const seen = new Set(); let expansions = 0; const T0 = Date.now(); let skippedM = 0, stoppedAt = null;
  for (const s of inputs) {
    if ((Date.now() - T0) / 1000 > opt.budget) { stoppedAt = seen.size; break; }
    const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue; seen.add(key);
    if (opt.maxM < 1e9) { let Mm; try { Mm = O.mountain(s); } catch (e) { continue; } let c = 0; for (const col of Mm) c += col.length; if (c > opt.maxM) { skippedM++; continue; } }
    for (const n of opt.copies) {
      let r; try { r = expandMountain(s, n); } catch (e) { cb(null, 'expansion error'); break; }
      const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1];
      if (t.pc < 0) break;
      const cr = t.pc, w = x0 - cr;
      let D = 0, nodes = 0, maxc = 0; for (const A of [M, R]) for (const col of A) { maxc = Math.max(maxc, col.length); for (const nd of col) { D = Math.max(D, degree(nd.row)); } }
      for (const col of R) nodes += col.length;
      expansions++;
      cb({s, n, M, R, x0, cr, w, D: D + opt.extraD, t});
      if (nodes > opt.maxNodes || maxc > opt.maxCol) break;
    }
  }
  return {sequences: seen.size, expansions, skippedM, stoppedAt, inputs: inputs.length};
}
const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 4) ex[k].push(msg); };
const report = (info) => { console.log(`inputs ${info.inputs}, sequences ${info.sequences}, expansions ${info.expansions}, skippedM ${info.skippedM}, stoppedAt ${info.stoppedAt}`); for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); } };


const {inputs, opt} = parseInputs(process.argv.slice(2));
const t0 = Date.now();
const info = forEach(inputs, opt, (e, err) => {
  if (!e) { bump(err); return; }
  const {s, n, M, R, x0, cr, w, D} = e;
  const where = x => `(${s})[${n}] ${x}`;
  for (let X = x0; X < R.length; X++) { const col = R[X]; for (const u of col) {
    const i = u.i; if (i === 0 || !isCut(u)) continue;
    const phi = c => c < cr ? c : c + w * i;
    const o = u.prov.src, l = leg(o);
    const pa = hAM(M, l, o.row), pe = hAM(R, phi(l), u.row); if (!pa || !pe) { bump('vacuous (no pa/pe)'); continue; }
    const de = jump(u.row, pe.row);
    const tag = `X=${X} u=${show(u.row)}`;
    { let okJ = de === 0; for (let kk = de; !okJ && kk <= D; kk++) if (root(R, kk, pe).c < phi(root(M, kk, pa).c)) okJ = true; bump(okJ ? 'CutJump ok' : 'FAIL CutJump', okJ ? null : where(tag)); }
    if (l > cr) {
      const L = R[phi(l)];
      const okT = L.some(q => isCut(q) && same(q.prov.src, pa) && cmp(q.row, u.row) >= 0);
      bump(okT ? 'CutRunTop ok' : 'FAIL CutRunTop', okT ? null : where(tag));
    }
    if (de === 0) continue;
    if (l === cr) {
      const q = rawParent(R, pe), b = rawParent(M, pa);
      const ok = !!q && (!b || jump(pe.row, q.row) < jump(pa.row, b.row));
      bump(ok ? 'CutJumpRootRow ok' : 'FAIL CutJumpRootRow', ok ? null : where(tag));
    } else {
      const pup = R[pe.c][pe.k + 1];
      const ok = isCut(pe) && same(pe.prov.src, pa) && !!pup && isCut(pup) && same(pup.prov.src, pa);
      bump(ok ? 'CutJumpRun ok' : 'FAIL CutJumpRun', ok ? null : where(tag));
    }
  } }
});
report(info);
console.log('time', (Date.now() - t0) / 1000);
