// Numerical test of LegPaLookup and of the two row facts it is reduced to
// (OmegaY/Official/Classification/Proofs/LegPartsPa.lean, namespace ChainCorr.LegPartsPa).
//
// Usage: node leg-palookup.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                              [--random COUNT,MAXLEN,MAXVAL,SEED] [--shard R/M] [--maxnodes N]
//                              [SAMPLE.json ...]
//
// Notation as in leg-parts.cjs: cr the root column, w = x0 - cr, tau the row of the top t of x0,
// B_m = x0 + w m the copy of x0 in block m (B_0 = x0), a consecutive pair (v, m) of block i >= 1
// (v a copy node of m, v+ a copy node of m+, inner column), pa = rawParent(m).
// Statements:
//  LegPaLookup  : col pa = cr, pa has a raw parent, pe = hAM(R, B_{i-1}, row v) is a lower copy of
//                 nu  =>  hAM(M, cr, row nu) = pa.
//  PaLookupRow  : the same for every non-gap node u of an inner column of block i >= 1 with
//                 origin o: pa = hAM(M, cr, row o), pe = hAM(R, B_{i-1}, row u) a lower copy of nu
//                 =>  hAM(M, cr, row nu) = pa   (covers LegPaLookup and SRParts.PaLookup).
//  RootSep      : (open ingredient) for every non-gap node u of an inner column of block i >= 1
//                 with origin o and every node c of cr:
//                 row c <= row o  =>  row c <= row u,   and   row o < row c  =>  row u < row c.
//  RootSepLeg   : RootSep only for the nodes v of consecutive pairs with pa in cr.
//  BFirst       : (open ingredient) for every block m < n and every node p of x0 below tau at the
//                 row of a node of cr, the first node of B_m with origin p exists and has the row
//                 of p (block 0 is proved: b0_profile).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, expandMountain} = O;
const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const same = (a, b) => a === b || (!!a && !!b && a.c === b.c && a.k === b.k);
const isCut = v => !!v.prov && v.prov.kind === 'clean' && !!v.prov.ib;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
let maxNodes = Infinity;
function inputs(args) {
  const out = []; let copies = [1, 2, 3]; const rest = [];
  for (let a = 0; a < args.length; a++) {
    if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
    else if (args[a] === '--legal') {
      const [K, V] = args[++a].split(',').map(Number);
      const rec = s => { if (s.length >= 2) out.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
      rec([1]);
    } else if (args[a] === '--random') {
      let [count, maxLen, maxVal, seed] = args[++a].split(',').map(Number);
      const rnd = () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
      for (let t = 0; t < count; t++) { const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1]; while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal)); out.push(s); }
    } else if (args[a] === '--shard') rest.push(args[++a]);
    else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
    else for (const s of JSON.parse(fs.readFileSync(args[a], 'utf8'))) out.push(s);
  }
  let res = out;
  if (rest.length) { const [r, m] = rest[0].split('/').map(Number); res = out.filter((_, i) => i % m === r); }
  return {seqs: res, copies};
}

const {seqs, copies} = inputs(process.argv.slice(2));
const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);
const seen = new Set(); let expansions = 0; const t0 = Date.now();
for (const s of seqs) {
  const key = s.join(','); if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue; seen.add(key);
  for (const n of copies) {
    let r; try { r = expandMountain(s, n); } catch (e) { bump('expansion error'); continue; }
    if (r.R.reduce((a, col) => a + col.length, 0) > maxNodes) { bump('skipped (output larger than --maxnodes)'); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr, tau = t.row;
    const B = m => x0 + w * m;
    // BFirst
    for (let mm = 0; mm < n; mm++) for (const p of M[x0]) {
      if (cmp(p.row, tau) >= 0 || !M[cr].some(c => cmp(c.row, p.row) === 0)) continue;
      const f = R[B(mm)].find(q => q.prov && same(q.prov.src, p));
      res(`BFirst (block ${mm === 0 ? '0, proved' : '>= 1'})`, !!f && cmp(f.row, p.row) === 0, `(${s})[${n}] m=${mm} p=(${p.c},${p.k}:${show(p.row)})`);
    }
    const isCopy = (u, m, i) => !!u && !!m && u.i === i && u.x !== x0 && u.x > cr && u.c === m.c + w * i && same(u.prov.src, m) && (!isCut(u) || !rawParent(M, m));
    for (let X = x0; X < R.length; X++) for (const u of R[X]) {
      const i = u.i; if (i === 0 || u.x === x0 || isCut(u)) continue;
      const o = u.prov.src, where = `(${s})[${n}] X=${X} u=(${u.c},${u.k}:${show(u.row)}) o=(${o.c},${o.k}:${show(o.row)})`;
      // RootSep
      let ok = true;
      for (const c of M[cr]) {
        if (cmp(c.row, o.row) <= 0 && cmp(c.row, u.row) > 0) ok = false;
        if (cmp(o.row, c.row) < 0 && cmp(u.row, c.row) >= 0) ok = false;
      }
      res('RootSep', ok, where);
      // PaLookupRow
      const pa = hAM(M, cr, o.row), pe = hAM(R, B(i - 1), u.row);
      if (pa && pe && pe.prov.kind !== 'upper') {
        const nu = pe.prov.src;
        res('PaLookupRow', same(hAM(M, cr, nu.row), pa) && nu.c === x0 && cmp(nu.row, tau) < 0, where + ` nu=(${nu.c},${nu.k})`);
      }
      // consecutive pairs with pa in cr
      const vp = R[X][u.k + 1], mp = M[o.c][o.k + 1];
      if (!isCopy(u, o, i) || !mp || !isCopy(vp, mp, i)) continue;
      const pa2 = M[mp.pc][mp.pk];
      if (pa2.c !== cr || !rawParent(M, pa2)) continue;
      res('RootSepLeg', ok, where);
      if (pe.prov.kind !== 'upper') {
        const nu = pe.prov.src;
        res('LegPaLookup', same(hAM(M, cr, nu.row), pa2) && nu.c === x0 && cmp(nu.row, tau) < 0, where + ` nu=(${nu.c},${nu.k})`);
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}, ${(Date.now() - t0) / 1000}s`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
