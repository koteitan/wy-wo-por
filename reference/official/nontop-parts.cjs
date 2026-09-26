// Numerical tests of the parts of NonTopStep, StartRelNT, StartRootNT
// (OmegaY/Official/Classification/Proofs/LowerChain.lean; the proofs are in NonTop*.lean).
//
// Usage: node nontop-parts.cjs [--copies 1,2,3] [--maxnodes N] [--legal MAXLEN,MAXVAL]
//          [--legal-sample LEN,MAXVAL,COUNT,SEED] [--random COUNT,MAXLEN,MAXVAL,SEED]
//          [--budget SECONDS] [--progress N] [SAMPLE.json ...]
// --budget: no new input after SECONDS (checked between inputs only). Node cannot run the SIGTERM
// handler inside the synchronous loop, so `timeout` does not stop it: use --budget and --maxnodes,
// with `timeout -s KILL` as a backstop.
//
// Block i >= 1 of s[n], w = x0 - cr, phi_i(c) = c (c < cr), c + w i (c >= cr). JS rows are official
// rows, JS index k is the Lean index k + 1.
// A copy node u of block i (any column X = x + w i of the block, x in (cr, x0]) is a TOP copy if no
// node above u in its column has the same origin source.
// Statements (every node u of block i >= 1 whose origin is not a gap copy):
//   NTKind   : u not top  =>  u is a clean copy (b = 0) of o = (x, C), the next node u+ is a gap copy
//              (b = 1) of o, row u = C, row u+ = C + 1.
//   NTLeg    : u not top  =>  the leg l of o is >= cr, the leg column l has a node at the row C.
//   NTParent : u not top  =>  rawParent_R(u) = hAM(R, phi(l), C) is at the row C.
//   NTInner  : u not top, l > cr  =>  rawParent_R(u) is a clean copy (b = 0) of (l, C) in block i,
//              in the column phi_i(l) (so it is again a non-top node of block i, if l < x0).
//   NTBound  : u not top, l = cr  =>  the row-C chain of R from the node (cr + w i, C) (raw parents
//              at the same row) reaches the node (cr, C) of M.
//   RowBound (report only; false in general): for every root row C < tau and every block i >= 1 the
//              row-C chain of R from the node (cr + w i, C) reaches (cr, C).
//   For the copied root rows C (the top of cr in its level-2 region, that region below tau; the rows
//   of NonTopBound.CleanRowOK):
//   RootRowBound : the row-C chain of R from (cr + w i, C) reaches (cr, C);
//   RootRowClean : for i >= 2 the node (cr + w i, C) is the clean copy (b = 0) of (x0, C) in block
//                  i - 1, followed by a gap copy of (x0, C) one row up (NonTopBound.boundary_emit);
//   BoundRoot    : every step g -> m'' of M from g = (cr, C) (scales jump(g, m'') .. + 3) is reached by
//                  the chain of R from (cr + w i, C) (NonTopBound.boundRoot).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], maxNodes = Infinity, progress = 0, budget = Infinity;
const rng = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--progress') progress = Number(args[++a]);
  else if (args[a] === '--budget') budget = Number(args[++a]) * 1000;
  else if (args[a] === '--legal') {
    const [K, V] = args[++a].split(',').map(Number);
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  } else if (args[a] === '--legal-sample') {
    const [K, V, count, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const s = [1]; while (s.length < K) s.push(1 + Math.floor(rnd() * V)); inputs.push(s); }
  } else if (args[a] === '--random') {
    const [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
    const rnd = rng(seed);
    for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); inputs.push(s); }
  } else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) inputs.push(s);
}

const same = (a, b) => !!a && !!b && a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const rawParent = (A, z) => { const v = above(A, z); return v && v.pc >= 0 ? A[v.pc][v.pk] : null; };
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
const nm = z => z ? `(${z.c},${z.k}:${show(z.row)}${z.prov ? '|' + z.prov.kind[0] + (z.prov.ib ? '!' : '') : ''})` : 'null';
const succ = r => { const b = r.slice(); b[0] = (b[0] || 0) + 1; return b; };

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);
const seen = new Set(); let expansions = 0; const t0 = Date.now();
const dump = head => { console.log(`${head}sequences ${seen.size}, expansions ${expansions}, ${(Date.now() - t0) / 1000}s`); for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('            e.g.', m); } };
process.on('SIGTERM', () => { dump('=== stopped by SIGTERM (partial): '); process.exit(0); });

for (const s of inputs) {
  if (Date.now() - t0 > budget) { bump('budget reached; inputs not taken'); break; }
  const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue; seen.add(key);
  if (progress && seen.size % progress === 0) dump(`--- progress (last input ${key}): `);
  for (const n of copies) {
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error', `(${s})[${n}]`); continue; }
    if (!r.root) continue;
    if (r.R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes)'); break; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, tt = M[x0][M[x0].length - 1], cr = tt.pc, w = x0 - cr, tau = tt.row;
    const phi = (c, i) => c < cr ? c : c + w * i;
    // the row-C chain of R from q: raw parents at the same row
    const rowChain = q => { const L = [q]; for (;;) { if (q.c <= cr) return L; const p = rawParent(R, q); if (!p || cmp(p.row, q.row) !== 0 || p.c >= q.c) return L; q = p; L.push(q); } };
    // x ascends at the root-column row C: the node of x at the reference row reaches cr by in-row parents
    const ascAt = (x, C) => { const ref = (C[0] || 0) > 0 ? O.norm([C[0] - 1, ...C.slice(1)]) : C; let a = O.nodeAt(M, x, ref); while (a && a.c > cr) a = O.rowParent(M, a); return !!a && a.c === cr; };
    const reachesRootNode = q => { const L = rowChain(q); const e = L[L.length - 1]; return e.c === cr && cmp(e.row, q.row) === 0; };
    for (let i = 1; i <= n; i++) {
      const B = cr + w * i;
      for (const g of M[cr]) {
        if (cmp(g.row, tau) >= 0) continue;
        const q = R[B] ? R[B].find(v => cmp(v.row, g.row) === 0) : null;
        res('RowBound (all root rows, report)', !!q && reachesRootNode(q), `(${s})[${n}] i=${i} g=${nm(g)} q=${nm(q)}`);
        // RootRow: g is the top of the root column in its level-2 region (rows agreeing with g above omega^0)
        const lvl2 = v => v.row.length <= 1 ? g.row.length <= 1 : (cmp(v.row.slice(1), g.row.slice(1)) === 0 && v.row.length === g.row.length);
        const same2 = v => { const a = v.row.slice(1), b = g.row.slice(1); while (a.length && !a[a.length-1]) a.pop(); while (b.length && !b[b.length-1]) b.pop(); return cmp(a, b) === 0 && a.length === b.length; };
        let isTop2 = true; for (const v of M[cr]) if (same2(v) && cmp(v.row, g.row) > 0) isTop2 = false;
        if (!isTop2) continue;
        if (!ascAt(x0, g.row)) { bump('  RootRow where x0 does not ascend (skipped)'); continue; }
        const where = `(${s})[${n}] i=${i} g=${nm(g)} q=${nm(q)}`;
        // the level-2 region of g is below tau: tau - g >= omega, i.e. tau differs from g above omega^0
        const below2 = (() => { const a = g.row.slice(1), b = tau.slice(1); return cmp(a, b) < 0; })();
        if (!below2) { bump('  RootRow whose level-2 region meets tau (skipped)'); continue; }
        const isRoot = same(g, r.root);
        const m2 = rawParent(M, g);
        if (m2) { let ok = !!q; const kmin = jump(g.row, m2.row);
          if (ok) for (let kk = kmin; kk <= kmin + 3; kk++) { let u = q, hit = false; for (;;) { if (same(u, m2)) { hit = true; break; } const p = rawParent(R, u); if (!p || jump(u.row, p.row) > kk || p.c >= u.c) break; u = p; } if (!hit) { ok = false; break; } }
          res(`BoundRoot [${isRoot ? 'g=r' : 'g<r'}]`, ok, where + ` m''=${nm(m2)}`); }
        else bump(`  BoundRoot: g has no raw parent [${isRoot ? 'g=r' : 'g<r'}]`);
        res('RootRowBound', !!q && reachesRootNode(q), where);
        if (i >= 2 && q) {
          const qk = R[B].indexOf(q), up = R[B][qk + 1];
          res('RootRowClean', q.i === i - 1 && q.prov && q.prov.kind === 'clean' && !q.prov.ib && q.prov.src.c === x0 && cmp(q.prov.src.row, g.row) === 0 &&
            !!up && isCut(up) && same(up.prov.src, q.prov.src) && cmp(up.row, succ(q.row)) === 0, where + ` up=${nm(up)}`);
        }
      }
    }
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      for (let k = 0; k < col.length; k++) {
        const u = col[k], i = u.i; if (i === 0 || !u.prov || isCut(u)) continue;
        const o = u.prov.src;
        let top = true; for (let k2 = k + 1; k2 < col.length; k2++) if (col[k2].prov && same(col[k2].prov.src, o)) top = false;
        if (top) continue;
        const where = `(${s})[${n}] X=${X} i=${i} u=${nm(u)} o=${nm(o)}`;
        const up = col[k + 1];
        const kindOK = u.prov.kind === 'clean' && !u.prov.ib && !!up && isCut(up) && same(up.prov.src, o) &&
          cmp(u.row, o.row) === 0 && cmp(up.row, succ(u.row)) === 0;
        res(`NTKind [${X === x0 + w * i ? 'x0' : 'inner'}]`, kindOK, where + ` up=${nm(up)}`);
        if (!kindOK) continue;
        const l = leg(o), C = o.row;
        res('NTAscX0 (x and x0 ascend at C)', ascAt(o.c, C) && ascAt(x0, C), where);
        const pa = hAM(M, l, C);
        res('NTLeg', l >= cr && !!pa && cmp(pa.row, C) === 0, where + ` l=${l} pa=${nm(pa)}`);
        if (!(l >= cr)) continue;
        const pe = hAM(R, phi(l, i), C), rp = rawParent(R, u);
        res('NTParent', !!pe && same(pe, rp) && cmp(pe.row, C) === 0, where + ` pe=${nm(pe)} rp=${nm(rp)}`);
        if (!pe) continue;
        if (l > cr) {
          const ok = pe.i === i && pe.prov && pe.prov.kind === 'clean' && !pe.prov.ib && same(pe.prov.src, pa) && pe.c === phi(l, i);
          res('NTInner', ok, where + ` pe=${nm(pe)}`);
        } else res('NTBound', reachesRootNode(pe), where + ` pe=${nm(pe)}`);
      }
    }
  }
}
dump('=== final: ');
