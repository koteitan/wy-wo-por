// Numerical test of the open statement ViaRoot
// (OmegaY/Official/Classification/Proofs/StepInnerCleanParent.lean, namespace ChainCorr.Inner.Clean).
//
// Usage: node step-inner-viaroot.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                    [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// For every clean copy (b = 0) v of a = (y, C) in a column of a block i >= 1 with cr < y < x0, with
// a+ present: follow the generation chain of a in the row C (next node: the node of the leg column
// at the row C) while the column is right of cr. When it reaches g = (cr, C):
//   ViaRoot: v(g) >= v(a)  =>  v(raw parent of g) < v(a).
// Also reported: whether the search from a passes g (the only case where ViaRoot is used).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, eq, show, expandMountain, nodeAt} = O;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
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
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      if (v.i === 0 || v.x === x0 || v.prov.kind !== 'clean' || v.prov.ib) continue;
      const a = v.prov.src, C = a.row;
      if (!M[a.c][a.k + 1]) { bump('no a+ (not needed)'); continue; }
      let cur = a, ok = true;
      while (cur.c > cr) { const b = nodeAt(M, leg(cur), C); if (!b) { ok = false; break; } cur = b; }
      if (!ok || cur.c !== cr) { bump('chain does not reach cr (not needed)'); continue; }
      const g = cur;
      const ap = M[a.c][a.k + 1], pa = M[ap.pc][ap.pk];
      if (g.value >= a.value) {
        const gp = M[g.c][g.k + 1], pg = gp && gp.pc >= 0 ? M[gp.pc][gp.pk] : null;
        const ok2 = !!pg && pg.value < a.value;
        bump(`ViaRoot ${ok2 ? 'ok' : 'FAIL'} (C0 ${C[0] ? '> 0' : '= 0'}; the search ${pa.c < cr ? 'passes g' : 'stops on the chain'})`,
          ok2 ? null : `(${s})[${n}] X=${X} a=(${a.c},${show(C)})`);
      } else bump('v(g) < v(a) (not needed)');
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
