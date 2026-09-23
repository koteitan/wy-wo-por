// Numerical tests of OmegaY/Official/Classification/Proofs/ChainCorrLegLeftItems.lean.
//
// Usage: node lift-leg-right.cjs [--items] [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// Default mode (about M(s) alone), statement LiftLegRight: t the top of the last column x0,
// cr the column of its left end, tau = row t. For a column cr < x <= x0, a node u of x below tau
// (not the bottom node, whose leg x - 1 >= cr is trivially right), and a region S of level
// d >= 2 containing row u and contained in a lower region (all rows < tau): let rho be the top
// of the root column in S, h the height (coefficient d - 2). If x ascends in S (the node of x at
// the reference row of rho reaches cr through in-row parents) and h(u) >= h(rho), the leg of u
// is >= cr. Also counted: the same without the ascension hypothesis (false).
//
// --items: the item invariant of the proof, on the item trees of the copies of block i >= 1
// (the rule of omegay-trace.cjs, patched at load time to report every item): a plain item that
// is not aligned (aligned: no cut bottom and source region = target region) has only nodes with
// leg >= cr in its source region.
//
// --budget SECONDS stops taking new sequences after that time; SIGTERM prints the summary so far.
'use strict';
const fs = require('fs');
const path = require('path');
const Module = require('module');
const O = require('./omegay-trace.cjs');
const {mountain, cmp, eq, norm, show, degree, topIn, nodeAt, rowParent} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], items = false, budget = Infinity;
const t0 = Date.now();
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--items') items = true;
  else if (args[a] === '--budget') budget = Number(args[++a]) * 1000;
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

const coef = (a, k) => a[k] || 0;
const inRegion = (row, R) => { for (let k = R.d - 1; k < Math.max(row.length, R.b.length); k++) if (coef(row, k) !== coef(R.b, k)) return false; return true; };
const height = (row, R) => coef(row, R.d - 2);
function slot(R, j) { const b = R.b.slice(); while (b.length <= R.d - 2) b.push(0); b[R.d - 2] = j; for (let k = 0; k < R.d - 2; k++) b[k] = 0; return {d: R.d - 1, b: norm(b)}; }
const leg = n => n.k > 0 ? n.pc : n.c - 1;
const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };

// the rule of omegay-trace.cjs with a hook on every item of a copy of block i >= 1
let hooked = null;
if (items) {
  const file = path.join(__dirname, 'omegay-trace.cjs');
  let src = fs.readFileSync(file, 'utf8');
  const patch = (a, b) => { if (!src.includes(a)) throw new Error('patch failed: ' + a.slice(0, 40)); src = src.replace(a, b); };
  patch(`  while (stack.length) {\n    const {S, T, C, o, ib} = stack.pop();`,
        `  while (stack.length) {\n    const item = stack.pop();\n    const {S, T, C, o, ib} = item;\n    if (i > 0) module.exports.hook(M, x, cr, item);`);
  src += '\nmodule.exports.hook = () => {};\n';
  const m = new Module(file, module);
  m.filename = file; m.paths = Module._nodeModulePaths(__dirname);
  m._compile(src, file);
  hooked = m.exports;
  let cur = '';
  hooked.hook = (M, x, cr, it) => {
    if (it.C) return;
    const aligned = !it.ib && it.S.d === it.T.d && eq(it.S.b, it.T.b);
    const bad = M[x].filter(n => n.k > 0 && inRegion(n.row, it.S) && leg(n) < cr);
    if (aligned) { bump(`  aligned plain item${bad.length ? ' (with legs left of cr)' : ''}`); return; }
    bump(bad.length ? 'FAIL ItemInv' : 'ItemInv ok', bad.length ? `${hooked.cur} x=${x} S=${show(it.S.b)}/${it.S.d} T=${show(it.T.b)} node ${show(bad[0].row)} leg ${leg(bad[0])} cr=${cr}` : null);
  };
}

const seen = new Set();
const summary = () => {
  console.log(`sequences ${seen.size}`);
  for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
};
// SIGTERM between two sequences prints the summary of the sequences done so far.
process.on('SIGTERM', () => { console.log(`stopped by SIGTERM after ${seen.size} sequences`); summary(); process.exit(0); });
(async () => {
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  if (Date.now() - t0 > budget) { console.log(`time budget reached after ${seen.size} sequences`); break; }
  seen.add(key);
  await new Promise(r => setImmediate(r));
  if (items) {
    for (const n of copies) { hooked.cur = `(${s})[${n}]`; try { hooked.expandMountain(s, n); } catch (e) { bump('expansion error'); } }
    continue;
  }
  let M; try { M = mountain(s); } catch (e) { continue; }
  const x0 = s.length - 1, tc = M[x0][M[x0].length - 1]; if (tc.pc < 0) continue;
  const cr = tc.pc, top = tc.row;
  let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
  const lower = [];
  for (let e = maxDeg + 3; e >= 2; e--) { const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))}; for (let j = 0; j < coef(top, e - 2); j++) lower.push(slot(hi, j)); }
  for (let x = cr + 1; x <= x0; x++) for (const n of M[x]) {
    if (n.k === 0 || cmp(n.row, top) >= 0) continue;
    const L = lower.find(Lr => inRegion(n.row, Lr));
    for (let d = 2; d <= L.d; d++) {
      const S = {d, b: norm(n.row.map((v, k) => k < d - 1 ? 0 : v))};
      const rho = topIn(M, cr, S); if (!rho) continue;
      const hRoot = height(rho.row, S);
      const ref = coef(rho.row, 0) > 0 ? norm([coef(rho.row, 0) - 1, ...rho.row.slice(1)]) : rho.row;
      let a = nodeAt(M, x, ref); while (a && a.c > cr) a = rowParent(M, a);
      const asc = !!a && a.c === cr;
      if (height(n.row, S) < hRoot) continue;
      const ok = leg(n) >= cr;
      const where = `(${s}) x=${x} node ${show(n.row)} d=${d} hRoot=${hRoot} leg=${leg(n)} cr=${cr}`;
      if (asc) bump(ok ? 'LiftLegRight ok' : 'FAIL LiftLegRight', ok ? null : where);
      bump(ok ? '  (without ascension) ok' : '  (without ascension) fails', ok ? null : where);
    }
  }
}
summary();
})();
