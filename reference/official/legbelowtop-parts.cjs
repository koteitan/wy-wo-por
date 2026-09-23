// Counterexample search for LegBelowTop (OmegaY/Official/Classification/Proofs/
// ChainCorrStartLegJump.lean; disproved in LegBelowTopFalse.lean) and for general forms of it.
//
// Usage: node legbelowtop-parts.cjs [--legal MAXLEN,MAXVAL] [--random COUNT,MAXLEN,MAXVAL,SEED]
//                                   [--expand 1,2,3] [SAMPLE.json ...]
//
// Every statement is about one canonical mountain M (of each input s, and with --expand also
// of each expansion s[n]). Notation: an edge is a node a with an upper node a+ and its
// parent b = P(a) (the left end of a+); cap = row(a+). Rows are official rows (the bottom
// row is 0 here, 1 in Lean).
//  NC1      : every column c with col b < c <= col a has a node at row(b).
//  LowerIT  : every non-top node v of a column col b < c <= col a with row(v) < row(b) has
//             col P(v) >= col b.
//  NoCross  : every non-top node v with col P(v) < col b < col v <= col a has row(v+) >= cap.
//  LegBelowTop : the statement of ChainCorrStartLegJump.lean (the edge a = t-, b = root);
//             it is the special case of NoCross for that edge.
// All four hold for legal inputs of length <= 6 with entries <= 6 and length <= 5 with entries
// <= 8, and all four fail on larger entries: (1,2,4,8,10,8) breaks LegBelowTop, LowerIT and
// NoCross; (1,3,9,27,74,185)[1] breaks NC1.
'use strict';
const fs = require('fs');
const O = require('./omegay.cjs');
const {mountain, cmp, show, expand} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [];
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--expand') copies = args[++a].split(',').map(Number);
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
const P = (M, c, k) => { const up = M[c][k + 1]; return up ? {c: up.pc, k: up.pk} : null; };

function testMountain(M, name) {
  for (let ca = 0; ca < M.length; ca++) for (let ka = 0; ka + 1 < M[ca].length; ka++) {
    const b = P(M, ca, ka), hb = M[b.c][b.k].row, cap = M[ca][ka + 1].row;
    for (let c = b.c + 1; c <= ca; c++) {
      const has = M[c].some(n => cmp(n.row, hb) === 0);
      bump(has ? 'NC1 ok' : 'FAIL NC1', has ? null : `${name} a=(${ca},${ka}) c=${c}`);
      for (let k = 0; k + 1 < M[c].length; k++) {
        const p = P(M, c, k);
        if (cmp(M[c][k].row, hb) < 0) {
          const ok = p.c >= b.c;
          bump(ok ? 'LowerIT ok' : 'FAIL LowerIT', ok ? null : `${name} a=(${ca},${ka}) v=(${c},${k})`);
        }
        if (p.c < b.c) {
          const ok = cmp(M[c][k + 1].row, cap) >= 0;
          bump(ok ? 'NoCross ok' : 'FAIL NoCross', ok ? null : `${name} a=(${ca},${ka}) v=(${c},${k})`);
        }
      }
    }
  }
}

const seen = new Set();
let mountains = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key)) continue;
  seen.add(key);
  let M;
  try { M = mountain(s); } catch (e) { continue; }
  mountains++;
  testMountain(M, `(${s})`);
  // LegBelowTop on M(s)
  const x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc;
  if (s[x0] > 1 && cr >= 0) for (let x = cr + 1; x <= x0; x++) for (const nd of M[x]) if (cmp(nd.row, t.row) < 0) {
    const leg = nd.k > 0 ? nd.pc : nd.c - 1, ok = leg >= cr;
    bump(ok ? 'LegBelowTop ok' : 'FAIL LegBelowTop', ok ? null : `(${s}) x=${x} ${show(nd.row)}`);
  }
  for (const n of copies) {
    if (s[x0] === 1) continue;
    let out;
    try { out = expand(s, n); } catch (e) { bump('expansion error', `(${s})[${n}]`); continue; }
    const k2 = out.join(',');
    if (seen.has('x' + k2)) continue;
    seen.add('x' + k2);
    try { M = mountain(out); } catch (e) { continue; }
    mountains++;
    testMountain(M, `(${s})[${n}]`);
  }
}
console.log(`mountains ${mountains}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
