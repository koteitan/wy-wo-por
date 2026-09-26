// Numerical test of the open pieces of the top chain
// (OmegaY/Official/Classification/Proofs/TopChain*.lean, namespace Recon.TopChain).
//
// Usage: node top-chain.cjs [--copies 1,2,3] [--maxnodes N] [--legal MAXLEN,MAXVAL]
//          [--random COUNT,MAXLEN,MAXVAL,SEED] [--budget SECONDS] [SAMPLE.json ...]
//
// Notation as in lower-chain.cjs: block i >= 1 of s[n], w = x0 - cr, phi(c) = c (c < cr),
// c + w i (c >= cr), tau the row of the top of x0. For an inner column y of block i and a node z
// of y with a raw parent a (the stored parent of the node z+ above z), Z the top copy of z,
// A the raw parent of Z in R.
//   TopStepLoRoot : z+ < tau, col a = cr: Stand(A, a) and jump(Z, A) <= jump(z, a)
//                   (reported split by row a+ >= tau / < tau, a+ the node above a).
//   TopStepLoJump : z+ < tau, col a > cr: jump(Z, A) <= jump(z, a).
//   LowExpCopy    : (info) z+ < tau: lowExp(row V) <= lowExp(row z+) for the node V above Z.
//   RowLawV       : (info) z+ < tau: row V = bump(row Z, jump(Z, A)).
//   TopStart pieces: u the top copy of its origin o (row o < tau) in a column X of block i >= 1,
//                   l = leg(o), pa = hAM(M, l, row o), pe = hAM(R, phi(l), row u): Stand(pe, pa),
//                   split by l <, =, > cr, by the kind of u, and by row pa = row o.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, expandMountain} = O;

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
const lowExp = r => { for (let k = 0; k < r.length; k++) if (r[k]) return k; return -1; };
const bumpRow = (a, e) => { const b = []; for (let k = 0; k < Math.max(a.length, e + 1); k++) b.push(k < e ? 0 : (a[k] || 0)); b[e]++; return O.norm(b); };
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
    for (let i = 1; i <= n; i++) {
      const last = i < n ? x0 : x0 - 1;
      for (let y = cr + 1; y < x0 && y <= last; y++) {
        for (const z of M[y]) {
          const Z = topCopy(i, z); if (!Z) continue;
          const a = rawParent(M, z); if (!a) continue;
          const zp = above(M, z); if (cmp(zp.row, tau) >= 0) continue;
          const A = rawParent(R, Z), V = above(R, Z);
          const where = `(${s})[${n}] i=${i} z=${nm(z)} Z=${nm(Z)} a=${nm(a)} A=${nm(A)} V=${nm(V)}`;
          const okJ = !!A && jump(Z.row, A.row) <= jump(z.row, a.row);
          if (a.c === cr) {
            const ap = above(M, a);
            const sub = ap && cmp(ap.row, tau) >= 0 ? 'a+>=tau' : 'a+<tau';
            res(`TopStepLoRoot [${sub}] Stand`, stand(i, A, a), where);
            res(`TopStepLoRoot [${sub}] jump`, okJ, where);
          } else if (a.c > cr) res(`TopStepLoJump [${isCut(Z) ? 'Z cut' : 'Z noncut'}]`, okJ, where);
          if (V && A) {
            res('  (info) LowExpCopy lowExp(V) <= lowExp(z+)', lowExp(V.row) <= lowExp(zp.row), where);
            res('  (info) RowLawV row V = bump(row Z, jump(Z, A))', cmp(V.row, bumpRow(Z.row, jump(Z.row, A.row))) === 0, where);
          }
        }
      }
    }
    for (let X = x0; X < R.length; X++) for (const u of R[X]) {
      const i = u.i; if (i === 0 || !u.prov) continue;
      const o = u.prov.src; if (cmp(o.row, tau) >= 0) continue;
      let T = null; for (const v of R[X]) if (v.prov && same(v.prov.src, o)) T = v;
      if (!same(T, u)) continue;
      const la = leg(o); if (la < 0) continue;
      const pe = hAM(R, phi(la, i), u.row), pa = hAM(M, la, o.row);
      if (!pe || !pa) { bump('  TopStart: a lookup is missing'); continue; }
      const lcase = la < cr ? 'l<cr' : la === cr ? 'l=cr' : 'l>cr';
      const kind = u.prov.kind + (isCut(u) ? '!' : '');
      const sr = cmp(pa.row, o.row) === 0 ? 'pa=o' : 'pa<o';
      res(`TopStartLo [${lcase}, ${kind}, ${sr}]`, stand(i, pe, pa), `(${s})[${n}] X=${X} u=${nm(u)} o=${nm(o)} pa=${nm(pa)} pe=${nm(pe)}`);
    }
  }
}
dump('=== final: ');
