// Numerical test of the target statements of the reconstruction of the new columns
// (OmegaY/Official/Recon/): RowLawHolds, ChainHolds (Search.lean), BumpChainHolds, JumpLawHolds
// (RowLawColumn.lean), ParentBelowHolds, CrossChainHolds (ChainSplit.lean), SameColumnBelowHolds
// (ParentBelowSplit.lean), LowerParentBelowHolds, LowerSameColumnBelowHolds (ParentBelow.lean).
//
// Usage: node recon-targets.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                               [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs: R is the diagram built by the rule, with the
// stored parents it assigns (not the parents of the canonical mountain of the output). Rows are
// the rows of this repository (the bottom row is 0 here, 1 in Lean; the phantom of Lean is not
// stored here). For every node u of a column X >= x0 with a node u+ above it:
//   p  = the stored parent of u+ (Frame.rawParent u);
//   Q u = climb in the column of the stored parent of u (for a bottom node: from the phantom of
//         column X - 1) to the highest node with row <= row u (Frame.Q);
//   the chain of stored parents from a node c is c, rawParent c, rawParent (rawParent c), ...
//  RowLaw         : row u+ = row u + omega^jump(row u, row p)  (Row.B).
//  BumpChain      : row u+ = row u + omega^e for some e.
//  JumpLaw        : row u+ = row u + omega^e  =>  jump(row u, row p) = e.
//  ChainHolds     : the chain from Q u reaches p, through nodes of value >= v(u) before p.
//  ParentBelow    : row p <= row u.
//  SameColumnBelow: Q u in the column of p  =>  row p <= row u.
//  CrossChain     : Q u not in the column of p  =>  the chain from Q u reaches a node c with
//                   rawParent c = p and v(u) <= v(c).
//  LowerParentBelow / LowerSameColumnBelow: the same two, only when row u < tau (tau = the row of
//                   the top t of x0 in M(s)) and row u+ != row u + 1.
// Counterexamples are printed in input order (at most 3 per statement).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, addPow, expandMountain, mountain} = O;

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
  const M = mountain(s), x0 = s.length - 1, tau = M[x0][M[x0].length - 1].row;
  for (const n of copies) {
    let R;
    try { R = expandMountain(s, n).R; } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const rawParent = c => { const up = R[c.c][c.k + 1]; return up && up.pc >= 0 ? R[up.pc][up.pk] : null; };
    for (let X = x0; X < R.length; X++) {
      const col = R[X];
      for (let k = 0; k + 1 < col.length; k++) {
        const u = col[k], up = col[k + 1];
        const where = `(${s})[${n}] X=${X} u=${show(u.row)}`;
        const res = (name, ok) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : where);
        if (up.pc < 0) { res('stored parent exists', false); continue; }
        const p = R[up.pc][up.pk];
        res('RowLaw', cmp(up.row, addPow(u.row, jump(u.row, p.row))) === 0);
        let e = -1;
        for (let f = 0; f <= Math.max(u.row.length, up.row.length) + 1; f++) if (cmp(up.row, addPow(u.row, f)) === 0) { e = f; break; }
        res('BumpChain', e >= 0);
        if (e >= 0) res('JumpLaw', jump(u.row, p.row) === e);
        const below = cmp(p.row, u.row) <= 0;
        res('ParentBelow', below);
        // Q u
        let qc, qi;
        if (k === 0) { qc = X - 1; qi = -1; } else { qc = u.pc; qi = u.pk; }
        const cc = R[qc];
        while (qi + 1 < cc.length && cmp(cc[qi + 1].row, u.row) <= 0) qi++;
        const q = qi >= 0 ? cc[qi] : null;
        // ChainHolds
        {
          let c = q, ok = false;
          for (let fuel = 0; c && fuel < 100000; fuel++) {
            if (c === p) { ok = true; break; }
            if (c.value < u.value) break;
            c = rawParent(c);
          }
          res('ChainHolds', ok);
        }
        const lower = cmp(u.row, tau) < 0 && cmp(up.row, addPow(u.row, 0)) !== 0;
        if (q && q.c === p.c) {
          res('SameColumnBelow', below);
          if (lower) res('LowerSameColumnBelow', below);
        } else {
          let c = q, ok = false;
          for (let fuel = 0; c && fuel < 100000; fuel++) {
            const r = rawParent(c);
            if (r === p) { ok = u.value <= c.value; break; }
            c = r;
          }
          res('CrossChain', ok);
        }
        if (lower) res('LowerParentBelow', below);
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
