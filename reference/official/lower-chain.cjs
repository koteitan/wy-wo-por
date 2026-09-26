// Numerical test of the shared "chain correspondence in the lower part of copied columns"
// (OmegaY/Official/Classification/Proofs/LowerChain*.lean, namespace ChainCorr.LowerChain).
//
// Usage: node lower-chain.cjs [--copies 1,2,3] [--maxnodes N] [--legal MAXLEN,MAXVAL]
//          [--legal-sample LEN,MAXVAL,COUNT,SEED] [--random COUNT,MAXLEN,MAXVAL,SEED]
//          [--budget SECONDS] [--expcap SECONDS] [--progress N] [SAMPLE.json ...]
// --budget: no new expansion after SECONDS; --expcap: skip the region part of an expansion whose
// step part took longer than SECONDS (reported). Node cannot stop inside a loop on SIGTERM.
//
// Block i >= 1 of s[n], w = x0 - cr, B = cr + w i, phi(c) = c (c < cr), c + w i (c >= cr).
// Top(i)(Z, z), for cr < col z < x0: Z is the highest node of the column phi(col z) whose origin
//   has the source z (the top copy), and row Z = row z when row z >= tau.
// Stand(i)(A, a):
//   col a <  cr : A = a;
//   col a =  cr : col A = B; if the node a+ above a has row >= tau, the node A+ above A has the
//                 row of a+; if a has a raw parent b, the R chain of A at the scale jump(a, b)
//                 reaches b;
//   col a >  cr : Top(i)(A, a).
// Statements:
//   TopStep   : Top(i)(Z, z), a = rawParent_M(z): A = rawParent_R(Z) exists, Stand(i)(A, a) and
//               jump(row Z, row A) <= jump(row z, row a).
//   TopExists : every node z of an inner column y of block i has a top copy in phi(y).
//   TopStart  : u = the top copy of its origin o in its column X of block i >= 1 (any kind),
//               la = leg(o), pa = hAM(M, la, row o), pe = hAM(R, phi(la), row u): Stand(i)(pe, pa).
//   CopyStepRel (NonTopStep, tested on every CopyNode pair, top or not): for a copy (v, z) that is
//               not a gap copy, a = rawParent_M(z), every k >= jump(z, a) up to D + 2:
//               Next_k(v, a) over Rel = CopyNode or Top.
//   StartRel  (StartRelNT, tested on every region node): origin not a gap copy, la > cr: Rel(pe, pa).
//   StartTop, CutStartTop: Top(i)(pe, pa) for every region node (only reported; false for clean
//               copies below a gap copy, which is why StartRel uses Rel).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], maxNodes = Infinity, progress = 0, budget = Infinity, expCap = Infinity;
const rng = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--progress') progress = Number(args[++a]);
  else if (args[a] === '--budget') budget = Number(args[++a]) * 1000;
  else if (args[a] === '--expcap') expCap = Number(args[++a]) * 1000;
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
const chain = (A, k, u) => { const L = [u]; for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k || p.c >= u.c) return L; u = p; L.push(u); } };
const reach = (A, k, v, t) => chain(A, k, v).some(r => same(r, t));
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
  if (progress && seen.size % progress === 0) dump(`--- progress (last input ${key}): `);
  const tIn = Date.now();
  for (const n of copies) {
    if (Date.now() - t0 > budget) break;
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error', `(${s})[${n}]`); continue; }
    if (!r.root) continue;
    if (r.R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes; larger n not expanded)'); break; }
    const tallGuard = r.R.some(col => col.length > 80);
    expansions++;
    const tExp = Date.now();
    const {M, R} = r, x0 = s.length - 1, tt = M[x0][M[x0].length - 1], cr = tt.pc, w = x0 - cr, tau = tt.row;
    const phi = (c, i) => c < cr ? c : c + w * i;
    const topMemo = new Map();
    const topCopy = (i, z) => {
      const key = `${i}|${z.c},${z.k}`;
      if (topMemo.has(key)) return topMemo.get(key);
      const X = z.c + w * i; let T = null;
      if (R[X]) for (const v of R[X]) if (v.i === i && v.prov && same(v.prov.src, z)) T = v;
      topMemo.set(key, T); return T;
    };
    const chainMemo = new Map();
    const chainR = (k, v) => { const key = `${k}|${v.c},${v.k}`; let L = chainMemo.get(key); if (!L) { L = chain(R, k, v); chainMemo.set(key, L); } return L; };
    const reachR = (k, v, t) => chainR(k, v).some(r => same(r, t));
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
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, O.degree(nd.row));
    const Dall = D + 2;
    const inner = (u, i) => !!u && u.i === i && u.x !== x0 && u.x > cr && u.x < x0;
    const isCopyN = (i, u, m) => inner(u, i) && u.c === m.c + w * i && same(u.prov.src, m) && (!isCut(u) || !rawParent(M, m));
    const rel = (i, u, m) => isCopyN(i, u, m) || (m.c > cr && m.c < x0 && isTop(i, u, m));
    const mstep = (k, m) => { const p = rawParent(M, m); return p && jump(m.row, p.row) <= k && p.c < m.c ? p : null; };
    const next = (k, v, m2, i) => {
      const cR = chainR(k, v);
      if (m2.c < cr) return cR.some(q => same(q, m2));
      if (m2.c === cr) { const m3 = mstep(k, m2); return cR.some(q => q.c <= cr + w * i && (!m3 || reachR(k, q, m3))); }
      return cR.some(q => rel(i, q, m2));
    };
    const standAny = (i, A, a) => {
      if (!A || !a) return false;
      if (a.c < cr) return same(A, a);
      if (a.c === cr) { if (A.c !== cr + w * i) return false; const b = rawParent(M, a); return !b || reachR(jump(a.row, b.row), A, b); }
      return A.c === a.c + w * i && A.i === i && !!A.prov && same(A.prov.src, a);
    };
    for (let i = 1; i <= n; i++) {
      const last = i < n ? x0 : x0 - 1;
      for (let y = cr + 1; y < x0 && y <= last; y++) {
        for (const z of M[y]) {
          const Z = topCopy(i, z);
          const where = `(${s})[${n}] i=${i} z=${nm(z)} Z=${nm(Z)}`;
          res('TopExists', !!Z, where);
          if (!Z) continue;
          const a = rawParent(M, z);
          if (!a) continue;
          const A = rawParent(R, Z);
          const zp = above(M, z);
          const kind = cmp(z.row, tau) >= 0 ? 'z>=tau' : cmp(zp.row, tau) >= 0 ? 'z<tau<=z+' : 'z+<tau';
          const acase = a.c < cr ? 'a<cr' : a.c === cr ? 'a=cr' : 'a>cr';
          const okS = stand(i, A, a), okJ = !!A && jump(Z.row, A.row) <= jump(z.row, a.row);
          res(`TopStep [${kind}, ${acase}]`, okS && okJ, where + ` a=${nm(a)} A=${nm(A)} S=${okS} J=${okJ}`);
          if (isCut(Z)) bump(`  top copy is a gap copy [${kind}, ${acase}]`);
        }
        // CopyStepRel: a CopyNode pair (v, z), every k >= jump(z, a): Next_k over Rel
        for (const v of R[y + w * i]) {
          if (v.i !== i || !v.prov) continue;
          const z = v.prov.src; if (z.c !== y || !isCopyN(i, v, z)) continue;
          const a = rawParent(M, z); if (!a) continue;
          const acase = a.c < cr ? 'a<cr' : a.c === cr ? 'a=cr' : 'a>cr';
          const kd = v.prov.kind + (isCut(v) ? '!' : '') + (same(topCopy(i, z), v) ? ',top' : ',nontop');
          const where = `(${s})[${n}] i=${i} z=${nm(z)} v=${nm(v)} a=${nm(a)}`;
          let ok = true, bad = -1;
          for (let k = jump(z.row, a.row); k <= Dall; k++) if (!next(k, v, a, i)) { ok = false; bad = k; break; }
          res(`CopyStepRel [${kd}, ${acase}]`, ok, where + ` k=${bad}`);
        }
      }
    }
    if (Date.now() - tExp > expCap) { bump('expansion cut by --expcap (region part not checked)', `(${s})[${n}]`); continue; }
    for (let X = x0; X < R.length; X++) for (const u of R[X]) {
      const i = u.i; if (i === 0) continue;
      const o = u.prov.src, la = leg(o);
      {
        // TopStart: u is the top copy of its origin o (o in (cr, x0])
        const Tu = (() => { const key = `col${X}|${o.c},${o.k}`; if (topMemo.has(key)) return topMemo.get(key); let T = null; for (const v of R[X]) if (v.prov && same(v.prov.src, o)) T = v; topMemo.set(key, T); return T; })();
        if (same(Tu, u) && la >= 0) {
          const pe0 = hAM(R, phi(la, i), u.row), pa0 = hAM(M, la, o.row);
          const lcase = la < cr ? 'l<cr' : la === cr ? 'l=cr' : 'l>cr';
          const w0 = `(${s})[${n}] X=${X} u=${nm(u)} o=${nm(o)} pa=${nm(pa0)} pe=${nm(pe0)}`;
          if (!pe0 || !pa0) bump('  TopStart: a lookup is missing (premise false)');
          else res(`TopStart [${u.prov.kind}${isCut(u) ? '!' : ''}, ${lcase}, ${X === x0 + w * i ? 'x0' : 'inner'}]`, stand(i, pe0, pa0), w0);
        } else if (!isCut(u) && la > cr) bump(`  non-top start of kind ${u.prov.kind}`);
      }
      if (la <= cr) continue;
      const pe = hAM(R, phi(la, i), u.row), pa = hAM(M, la, o.row);
      const where = `(${s})[${n}] X=${X} u=${nm(u)} o=${nm(o)} pa=${nm(pa)} pe=${nm(pe)}`;
      if (!pe || !pa) { res('lookup exists', false, where); continue; }
      if (!isCut(u)) res(`StartRel [${u.prov.kind}, ${X === x0 + w * i ? 'boundary' : 'inner'}]`, rel(i, pe, pa), where);
      if (!isCut(u)) res(`StartTop [${u.prov.kind}, ${X === x0 + w * i ? 'boundary' : 'inner'}]`, isTop(i, pe, pa), where);
      else res('CutStartTop (report)', isTop(i, pe, pa), where);
    }
    if (tallGuard) { bump('  larger n not expanded (a column of the output has more than 80 nodes)'); break; }
  }
  if (Date.now() - tIn > 5000) bump('  slow input (> 5 s)', `${key}: ${Date.now() - tIn} ms`);
}
dump('=== final: ');
