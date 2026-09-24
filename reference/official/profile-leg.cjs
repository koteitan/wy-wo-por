// Numerical test of the leg forms of NonCutOrder and CutBetween (the profile of a block,
// OmegaY/Official/Recon/ParentBelowLowerProfile.lean). The unrestricted statements are false
// ((1,3,6,13,15,13)[1]); their only users (sameRow, legOrder in ParentBelowLowerCore.lean)
// compare the copy of a column x > cr with the copy of the leg column l of a node (x, k) of M(s).
//
// Usage: node profile-leg.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                             [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
// Environment: MAXNODES (skip outputs with more nodes; default no limit), SAMPLE=a/b (test only
// the inputs with index = a mod b).
//
// Setting (as parent-below-lower.cjs): block i >= 1, source columns y in [cr, x0] (including the
// hypothetical copies of cr, and of x0 in the last block, read with the boundary column
// cr + w i of the output). For a source column y the lower copies are the emitted nodes below
// tau with their origins; a copy is cut when it is a clean copy with b = 1.
//
// For y > cr, a node v = (y, k) of M(s) (every node, the bottom node included) with leg column
// l = column of the left end of v (y - 1 for the bottom node), l in [cr, x0]; E = the lower copies
// of y, F = the lower copies of l. "e below v" means: the origin of e is at or below v.
//  NCOLeg   non-cut e in E below v, non-cut f in F: sign(o(e) - o(f)) = sign(t(e) - t(f)).
//  CBLegE   cut e in E below v, non-cut f in F: o(f) <= o(e) -> t(f) < t(e); o(e) < o(f) -> t(e) < t(f).
//  CBLegF   non-cut e in E below v, cut f in F: o(e) <= o(f) -> t(e) < t(f); o(f) < o(e) -> t(f) < t(e).
//  NCOLegAll, CBLegEAll, CBLegFAll: the same without "e below v" (information).
//  NeedLegOrder: the conclusion of legOrder (e in E with origin v, f in F, t(f) < t(e)):
//               o(f) < o(v), or o(f) = o(v) and (f cut -> the copy of y makes a cut copy of v).
//  NeedSameRow: the conclusion of sameRow (f in F with o(f) < o(v), or o(f) = o(v) and
//               (f cut -> y makes a cut copy of v)): some e in E has t(e) = t(f).
// Reference: NonCutOrder, CutBetween over all pairs of the block (false).
'use strict';
const fs = require('fs');
const path = require('path');

// The same loading as parent-below-lower.cjs: omegay-trace.cjs with copyColumn exported, and
// the values step skipped for hypothetical copies.
const anchor = "  if (!col.length) throw new Error('empty column ' + X);";
let src = fs.readFileSync(path.join(__dirname, 'omegay-trace.cjs'), 'utf8');
if (!src.includes(anchor)) throw new Error('omegay-trace.cjs changed: cannot find the value step');
src = src.replace(anchor, '  if (copyColumn.rowsOnly) return col;\n' + anchor);
const mod = {exports: {}};
new Function('module', 'exports', 'require', src + '\nmodule.exports.copyColumn = copyColumn;')(mod, mod.exports, require);
const O = mod.exports;
const {cmp, eq, show, degree, expandMountain, copyColumn, norm} = O;

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
const MAXNODES = Number(process.env.MAXNODES || Infinity);
const [SA, SB] = (process.env.SAMPLE || '0/1').split('/').map(Number);

const stat = {}, ex = {};
const bump = (k, ok, msg) => { const key = (ok ? '' : 'FAIL ') + k; stat[key] = (stat[key] || 0) + 1; if (!ok && msg && (ex[key] = ex[key] || []).length < 3) ex[key].push(msg); };
const legOf = nd => nd.pc >= 0 ? nd.pc : nd.c - 1;
const slot = (Rg, j) => { const b = Rg.b.slice(); while (b.length <= Rg.d - 2) b.push(0); b[Rg.d - 2] = j; for (let k = 0; k < Rg.d - 2; k++) b[k] = 0; return {d: Rg.d - 1, b: norm(b)}; };
const sg = x => Math.sign(x);
const seen = new Set();
let expansions = 0, idx = -1;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  idx++;
  if (idx % SB !== SA) continue;
  for (const n of copies) {
    let r;
    copyColumn.rowsOnly = false;
    try { r = expandMountain(s, n); } catch (err) { continue; }
    if (!r.root) continue;
    { let nodes = 0; for (const c of r.R) nodes += c.length; if (nodes > MAXNODES) { bump('SKIP big (and larger n)', true); break; } }
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
        try { copyColumn.rowsOnly = true; c = copyColumn(M, R, y, i, cr, w, x0, top, lower); } catch (e) { bump('copy', false, where(`i=${i} y=${y} ${e.message}`)); continue; }
        EM.set(y, c.filter(v => v.prov.kind !== 'upper').map(v => ({t: v.row, o: v.prov.src.row, cut: v.prov.kind === 'clean' && !!v.prov.ib, src: v.prov.src, y})));
      }
      // reference: the unrestricted statements, by sorting (one count per neighbouring pair)
      const all = []; for (const [, l] of EM) for (const e of l) all.push(e);
      const nc = all.filter(e => !e.cut).sort((a, b) => cmp(a.o, b.o) || cmp(a.t, b.t));
      for (let t = 1; t < nc.length; t++) bump('ref NonCutOrder', sg(cmp(nc[t - 1].o, nc[t].o)) === sg(cmp(nc[t - 1].t, nc[t].t)), where(`i=${i}`));
      for (const e of all) if (e.cut) for (const f of all) if (!f.cut) {
        const co = cmp(e.o, f.o), ct = cmp(e.t, f.t);
        bump('ref CutBetween', !((co >= 0 && ct <= 0) || (co < 0 && ct >= 0)), where(`i=${i}`));
      }
      for (const y of EM.keys()) {
        if (y <= cr) continue;
        const E = EM.get(y);
        for (const v of M[y]) {
          const l = legOf(v);
          if (!EM.has(l)) continue;
          const F = EM.get(l);
          const tag = `i=${i} v=(${y},${show(v.row)}) l=${l}`;
          for (const e of E) {
            const below = cmp(e.o, v.row) <= 0;
            for (const f of F) {
              const co = cmp(e.o, f.o), ct = cmp(e.t, f.t);
              const msg = () => where(`${tag} e=${show(e.o)}${e.cut ? '*' : ''}->${show(e.t)} f=${show(f.o)}${f.cut ? '*' : ''}->${show(f.t)}`);
              if (!e.cut && !f.cut) {
                const ok = sg(co) === sg(ct);
                bump('NCOLegAll', ok, ok ? null : msg());
                if (below) bump('NCOLeg', ok, ok ? null : msg());
              } else if (e.cut && !f.cut) {
                const ok = co >= 0 ? ct > 0 : ct < 0;
                bump('CBLegEAll', ok, ok ? null : msg());
                if (below) bump('CBLegE', ok, ok ? null : msg());
              } else if (!e.cut && f.cut) {
                const ok = co <= 0 ? ct < 0 : ct > 0;
                bump('CBLegFAll', ok, ok ? null : msg());
                if (below) bump('CBLegF', ok, ok ? null : msg());
              }
            }
          }
          const yCut = E.some(e => e.cut && e.src === v);
          for (const e of E) if (e.src === v) for (const f of F) if (cmp(f.t, e.t) < 0) {
            const c = cmp(f.o, v.row);
            const ok = c < 0 || (c === 0 && (!f.cut || yCut));
            bump('NeedLegOrder', ok, ok ? null : where(`${tag} f=${show(f.o)}${f.cut ? '*' : ''}->${show(f.t)}`));
          }
          for (const f of F) {
            const c = cmp(f.o, v.row);
            if (!(c < 0 || (c === 0 && (!f.cut || yCut)))) continue;
            const ok = E.some(e => eq(e.t, f.t));
            bump('NeedSameRow', ok, ok ? null : where(`${tag} f=${show(f.o)}${f.cut ? '*' : ''}->${show(f.t)}`));
          }
        }
      }
    }
  }
}
console.log(`inputs ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(11), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
