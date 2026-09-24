// Numerical test of the open statements that LowerParentBelowHolds is reduced to in
// OmegaY/Official/Recon/ParentBelowLowerFix*.lean, and of LowerParentBelowHolds itself.
//
// Usage: node parent-below-lower-fix.cjs [--copies 1,2,3] [--shard K/M] [--maxnodes N]
//                                        [--legal MAXLEN,MAXVAL]
//                                        [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// --maxnodes N: the expansion with n >= 2 copies is made only when, for every m < n, the output of
// the expansion with m copies has at most N·m nodes (the output grows very fast with n; for
// example (1,12,12,12,12,12)[2] does not finish in minutes). Skipped expansions are counted
// ('skipped (maxnodes)'); the expansions with n = 1 are never skipped by --maxnodes.
// --maxout N: the checks are skipped for an expansion whose output has more than N nodes
// (counted as 'skipped (maxout)'; for large random inputs, where a few outputs are very large).
//
// The rule is the one of omegay-trace.cjs (every emitted node records its origin), loaded as in
// parent-below-lower.cjs. For a block i >= 1 and a source column y in [cr, x0] (the copies of cr,
// and of x0 in the last block, are "hypothetical": the rule does not make them; they read the
// same boundary column cr + w i of the output), the lower copies of y are the emitted nodes below
// tau with their origins (nodes of y). Rows are compared as ordinals; origin rows are rows of M(s).
//
// For a node nd = (x, k) of M(s) (x > cr; JS index 0 is the bottom node) with leg column
// l = legOf(nd) >= cr:
//  LegCopyBelow : every lower copy z of the copy of l whose origin is below nd has a lower copy of
//                 the copy of x at the same row.
//  LegCopyOrder : for a lower copy e of nd made by the copy of x, every lower copy z of the copy
//                 of l with row z < row e has its origin below nd, or the copy of x has a lower
//                 copy at the row of z.
//  Boundary     : every row below tau of the output column cr + w i is the row of a lower copy of
//                 the copy of cr.
//  LegShadowOut : on the output: for a new column X = x + w i (i >= 1), a node nd of x with leg
//                 l >= cr, and a node z of the output column l + w i below tau: if z is below a
//                 lower copy of nd in X, or nd is at or above tau and x < x0, then X has a lower
//                 copy at the row of z.
//  LPB          : LowerParentBelowHolds on the output: for consecutive nodes u, u+ of a new column
//                 with row u < tau and row u+ != row u + 1, the stored parent of u+ is not above u.
'use strict';
const fs = require('fs');
const path = require('path');

const anchor = "  if (!col.length) throw new Error('empty column ' + X);";
let src = fs.readFileSync(path.join(__dirname, 'omegay-trace.cjs'), 'utf8');
if (!src.includes(anchor)) throw new Error('omegay-trace.cjs changed: cannot find the value step');
src = src.replace(anchor, '  if (copyColumn.rowsOnly) return col;\n' + anchor);
const mod = {exports: {}};
new Function('module', 'exports', 'require', src + '\nmodule.exports.copyColumn = copyColumn;')(mod, mod.exports, require);
const O = mod.exports;
const {cmp, eq, show, degree, addPow, expandMountain, copyColumn, norm} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], shK = 0, shM = 1, maxNodes = Infinity, maxOut = Infinity;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--shard') [shK, shM] = args[++a].split('/').map(Number);
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--maxout') maxOut = Number(args[++a]);
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
const bump = (k, ok, msg) => { const key = (ok ? '' : 'FAIL ') + k; stat[key] = (stat[key] || 0) + 1; if (!ok && msg && (ex[key] = ex[key] || []).length < 3) ex[key].push(msg()); };
const legOf = nd => nd.pc >= 0 ? nd.pc : nd.c - 1;
const slot = (Rg, j) => { const b = Rg.b.slice(); while (b.length <= Rg.d - 2) b.push(0); b[Rg.d - 2] = j; for (let k = 0; k < Rg.d - 2; k++) b[k] = 0; return {d: Rg.d - 1, b: norm(b)}; };
const seen = new Set();
let expansions = 0, idx = -1, done = 0;
for (const s of inputs) {
  idx++;
  if (idx % shM !== shK) continue;
  if (++done % 1000 === 0) process.stderr.write(`progress ${idx}/${inputs.length}\n`);
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  // sizes[n] = number of nodes of the output of the expansion with n copies (for --maxnodes)
  const sizes = {};
  const sizeOf = n => { if (!(n in sizes)) { try { sizes[n] = 0; for (const c of expandMountain(s, n).R) sizes[n] += c.length; } catch (e) { sizes[n] = Infinity; } } return sizes[n]; };
  for (const n of copies) {
    let r;
    copyColumn.rowsOnly = false;
    if (n >= 2 && maxNodes < Infinity) {
      let big = false;
      for (let m = 1; m < n && !big; m++) big = sizeOf(m) > maxNodes * m;
      if (big) { stat['skipped (maxnodes)'] = (stat['skipped (maxnodes)'] || 0) + 1; continue; }
    }
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', false, () => `(${s})[${n}]`); continue; }
    if (!r.root) continue;
    if (maxOut < Infinity) { let tot = 0; for (const c of r.R) tot += c.length; if (tot > maxOut) { stat['skipped (maxout)'] = (stat['skipped (maxout)'] || 0) + 1; continue; } }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, top = M[x0][M[x0].length - 1].row, cr = r.root.c, w = x0 - cr;
    let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
    const lower = [];
    for (let e = maxDeg + 3; e >= 2; e--) { const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))}; for (let j = 0; j < (top[e - 2] || 0); j++) lower.push(slot(hi, j)); }
    const where = m => `(${s})[${n}] ${m}`;
    for (let i = 1; i <= n; i++) {
      const EM = new Map();
      for (let y = cr; y <= x0; y++) {
        let c;
        try { copyColumn.rowsOnly = true; c = copyColumn(M, R, y, i, cr, w, x0, top, lower); } catch (e) { bump('copy', false, () => where(`i=${i} y=${y} ${e.message}`)); continue; }
        EM.set(y, c.filter(v => v.prov.kind !== 'upper').map(v => ({t: v.row, o: v.prov.src.row, src: v.prov.src, cut: v.prov.kind === 'clean' && !!v.prov.ib})));
      }
      for (let x = cr + 1; x <= x0; x++) {
        if (!EM.has(x)) continue;
        const Ex = EM.get(x);
        const rowsX = new Set(Ex.map(f => show(f.t)));
        for (const nd of M[x]) {
          const l = legOf(nd);
          if (l < cr || !EM.has(l)) continue;
          const El = EM.get(l);
          const w2 = m => () => where(`i=${i} x=${x} nd=${show(nd.row)} l=${l} ${m}`);
          for (const z of El) if (cmp(z.o, nd.row) < 0)
            bump('LegCopyBelow', rowsX.has(show(z.t)), w2(`z.o=${show(z.o)} z.t=${show(z.t)}${z.cut ? ' cut' : ''}`));
          // some lower copy e of nd with row z < row e  <=>  row z < the highest such row
          let m = null;
          for (const e of Ex) if (e.src === nd && (!m || cmp(e.t, m) > 0)) m = e.t;
          if (m) for (const z of El) if (cmp(z.t, m) < 0)
            bump('LegCopyOrder', cmp(z.o, nd.row) < 0 || rowsX.has(show(z.t)), w2(`e.t=${show(m)} z.o=${show(z.o)} z.t=${show(z.t)}`));
        }
      }
      if (EM.has(cr)) { const B = cr + w * i; if (B < R.length) { const tg = new Set(EM.get(cr).map(e => show(e.t))); for (const nd of R[B]) if (cmp(nd.row, top) < 0) bump('Boundary', tg.has(show(nd.row)), () => where(`i=${i} ${show(nd.row)}`)); } }
    }
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      for (let k = 0; k + 1 < col.length; k++) {
        const u = col[k], up = col[k + 1];
        if (cmp(u.row, top) >= 0 || eq(up.row, addPow(u.row, 0))) continue;
        const p = R[up.pc][up.pk];
        bump('LPB', cmp(p.row, u.row) <= 0, () => where(`X=${X} ${show(u.row)}`));
      }
      const x = col[0].x, i = col[0].i;
      if (i >= 1) {
        const lowX = col.filter(v => v.prov.kind !== 'upper');
        const rowsX = new Set(lowX.map(v => show(v.row)));
        for (const nd of M[x]) {
          const l = legOf(nd); if (l < cr) continue;
          const q = l + w * i; if (q >= R.length) continue;
          let m = null;
          for (const v of lowX) if (v.prov.src === nd && (!m || cmp(v.row, m) > 0)) m = v.row;
          const upperCase = cmp(nd.row, top) >= 0 && x !== x0;
          for (const z of R[q]) {
            if (cmp(z.row, top) >= 0) continue;
            if (!(upperCase || (m && cmp(z.row, m) < 0))) continue;
            bump('LegShadowOut', rowsX.has(show(z.row)), () => where(`X=${X} x=${x} i=${i} nd=${show(nd.row)} l=${l} z=${show(z.row)}`));
          }
        }
      }
    }
  }
}
console.log(`sequences: ${seen.size}, expansions: ${expansions}`);
for (const k of Object.keys(stat).sort()) console.log(`${k}: ${stat[k]}`);
for (const k of Object.keys(ex)) for (const m of ex[k]) console.log(`  ${k}: ${m}`);
