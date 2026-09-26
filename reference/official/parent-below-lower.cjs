// Numerical test of the open statements that LowerParentBelowHolds is reduced to
// (OmegaY/Official/Recon/ParentBelowLower*.lean), and of LowerParentBelowHolds itself.
//
// Usage: node parent-below-lower.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                    [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The rule is the one of omegay-trace.cjs (every emitted node records its origin). For a block
// i and a source column y in [cr, x0] (also y = cr and y = x0 in the last block, which the rule
// does not copy: a "hypothetical" copy, read with the same boundary column cr + w i of the
// output), the lower copies of y are the emitted nodes below tau with their origins. A copy is
// "cut" when it is a clean copy with the flag b = 1 (Lean: cutO). Origin rows are rows of M(s).
//
// Profile of a block i >= 1 (ParentBelowLowerProfile.lean):
//  NonCutOrder : non-cut copies a (of y), a' (of y'): row(o) < row(o') => row a < row a';
//                row(o) = row(o') => row a = row a'.
//  CutBetween  : cut a, non-cut a': row(o') <= row(o) => row a' < row a;  row(o) < row(o') => row a < row a'.
//  CutOrder    : cut a, cut a': row(o) < row(o') => row a < row a'.
//  CutLeg      : y > cr, (y, k) a node of M(s) (the bottom node included) with leg column l:
//                every cut copy a' of the copy of l with row(o') < row(y, k), or with
//                row(o') = row(y, k) when the copy of y makes a cut copy of (y, k), has a cut copy
//                of the copy of y at the same row.
//  Emitted     : y > cr: every node of y below tau is the origin of a non-cut copy of y.
//  Lift        : a non-cut copy is not below its origin.
//  Boundary    : every row below tau of the column cr + w i is the row of a copy of the copy of cr.
//  LegRight    : y > cr: every leg of a lower copy is >= cr (proved from LegBelowTop in Lean;
//                tested here for completeness).
// Block 0 (proved in Lean, tested here): Emitted, and every lower copy sits at its origin row.
// LPB: LowerParentBelowHolds on the output: for consecutive nodes u, u+ of a new column with
//      row u < tau and row u+ != row u + 1, the stored parent of u+ is not above u.
'use strict';
const fs = require('fs');
const path = require('path');

// omegay-trace.cjs does not export copyColumn; load the same source and export it too. The
// hypothetical copies are not columns of the output, so only their rows are read: the values
// (the last step of copyColumn) are skipped when copyColumn.rowsOnly is set.
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
let copies = [1, 2, 3];
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
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
const bump = (k, ok, msg) => { const key = (ok ? '' : 'FAIL ') + k; stat[key] = (stat[key] || 0) + 1; if (!ok && msg && (ex[key] = ex[key] || []).length < 3) ex[key].push(msg); };
const legOf = nd => nd.pc >= 0 ? nd.pc : nd.c - 1;
const slot = (Rg, j) => { const b = Rg.b.slice(); while (b.length <= Rg.d - 2) b.push(0); b[Rg.d - 2] = j; for (let k = 0; k < Rg.d - 2; k++) b[k] = 0; return {d: Rg.d - 1, b: norm(b)}; };
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    copyColumn.rowsOnly = false;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', false, `(${s})[${n}]`); continue; }
    if (!r.root) continue;
    expansions++;
    const {M, R} = r, x0 = s.length - 1, top = M[x0][M[x0].length - 1].row, cr = r.root.c, w = x0 - cr;
    let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
    const lower = [];
    for (let e = maxDeg + 3; e >= 2; e--) { const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))}; for (let j = 0; j < (top[e - 2] || 0); j++) lower.push(slot(hi, j)); }
    const where = m => `(${s})[${n}] ${m}`;
    for (let i = 0; i <= n; i++) {
      const EM = new Map();
      for (let y = cr; y <= x0; y++) {
        let c;
        try { copyColumn.rowsOnly = true; c = copyColumn(M, R, y, i, cr, w, x0, top, lower); } catch (e) { bump('copy', false, where(`i=${i} y=${y} ${e.message}`)); continue; }
        EM.set(y, c.filter(v => v.prov.kind !== 'upper').map(v => {
          const cut = v.prov.kind === 'clean' && !!v.prov.ib, o = v.prov.src;
          return {t: v.row, o: o.row, cut, src: o, leg: v.prov.kind === 'clean' ? legOf(o) : o.pc, y};
        }));
      }
      for (const y of EM.keys()) if (y > cr) for (const nd of M[y]) if (cmp(nd.row, top) < 0)
        bump(`Emitted i${i === 0 ? '=0' : '>=1'}`, EM.get(y).some(e => !e.cut && e.src === nd), where(`i=${i} y=${y} ${show(nd.row)}`));
      if (i === 0) { for (const [y, l] of EM) for (const e of l) bump('block 0 identity', !e.cut && eq(e.t, e.o), where(`y=${y} ${show(e.o)}`)); continue; }
      const all = []; for (const [, l] of EM) for (const e of l) all.push(e);
      for (const e of all) {
        if (!e.cut) bump('Lift', cmp(e.t, e.o) >= 0, where(`i=${i} y=${e.y} ${show(e.o)}`));
        if (e.y > cr && e.leg >= 0) bump('LegRight', e.leg >= cr, where(`i=${i} y=${e.y} ${show(e.o)}`));
      }
      for (const e of all) for (const f of all) {
        const co = cmp(e.o, f.o), ct = cmp(e.t, f.t);
        if (!e.cut && !f.cut) bump('NonCutOrder', !((co < 0 && ct >= 0) || (co === 0 && ct !== 0)), where(`i=${i} ${e.y} ${f.y}`));
        if (e.cut && !f.cut) bump('CutBetween', !((co >= 0 && ct <= 0) || (co < 0 && ct >= 0)), where(`i=${i} ${e.y} ${f.y}`));
        if (e.cut && f.cut) bump('CutOrder', !(co < 0 && ct >= 0), where(`i=${i} ${e.y} ${f.y}`));
      }
      for (const y of EM.keys()) if (y > cr) for (const nd of M[y]) {
        const l = legOf(nd); if (!EM.has(l)) continue;
        const yCut = EM.get(y).some(f => f.cut && f.src === nd);
        for (const e of EM.get(l)) if (e.cut && (cmp(e.o, nd.row) < 0 || (eq(e.o, nd.row) && yCut)))
          bump('CutLeg', EM.get(y).some(f => f.cut && eq(f.t, e.t)), where(`i=${i} y=${y} ${show(nd.row)} l=${l}`));
      }
      if (EM.has(cr)) { const B = cr + w * i; if (B < R.length) { const tg = new Set(EM.get(cr).map(e => show(e.t))); for (const nd of R[B]) if (cmp(nd.row, top) < 0) bump('Boundary', tg.has(show(nd.row)), where(`i=${i} ${show(nd.row)}`)); } }
    }
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      for (let k = 0; k + 1 < col.length; k++) {
        const u = col[k], up = col[k + 1];
        if (cmp(u.row, top) >= 0 || eq(up.row, addPow(u.row, 0))) continue;
        const p = R[up.pc][up.pk];
        bump('LPB', cmp(p.row, u.row) <= 0, where(`X=${X} ${show(u.row)}`));
      }
    }
  }
}
console.log(`expansions: ${expansions}`);
for (const k of Object.keys(stat).sort()) console.log(`${k}: ${stat[k]}`);
for (const k of Object.keys(ex)) for (const m of ex[k]) console.log(`  ${k}: ${m}`);
