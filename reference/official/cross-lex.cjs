// Numerical test of CrossLexHolds (OmegaY/Official/Recon/CrossLex.lean) and of its split by
// the origin kind of the node above (CrossKinds.lean).
//
// Usage: node cross-lex.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                           [--random COUNT,MAXLEN,MAXVAL,SEED] [-v N] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md). For every node u
// of a new column X >= x0 with a node u+ above it, p = the stored parent of u+ (the left end
// of the edge u -> u+), and q = Q u (the highest node at or below row u in the column of the
// stored parent of u; for a bottom node, the bottom node of column X - 1). The cross case is
// column(q) != column(p). There the test follows the stored parents from q to the node c
// whose stored parent is p and checks
//   row(c+) = row(u+)  and  Lex(u+, c+),
// where Lex(z, w): z is a top, or the parent of z+ is left of the parent of w+, or the two
// parents are equal, row(z+) = row(w+) and Lex(z+, w+). It also checks the value inequality
// v(u) <= v(c) of CrossChainHolds, and that every cut node (a gap copy of the root row, b = 1)
// has below it a copy of the same root-row node (so that u+ is never cut in the cross case).
// Counts are split by the origin kind of u+ and of u (plain, clean, cut, upper).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, show, expandMountain} = O;

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], verbose = 0;
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '-v') verbose = +args[++a];
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

const same = (a, b) => a.c === b.c && a.k === b.k;
const above = (A, z) => A[z.c][z.k + 1] || null;
const parentOf = (A, v) => v.pc >= 0 ? A[v.pc][v.pk] : null; // stored left end of v
const rawParent = (A, z) => { const v = above(A, z); return v ? parentOf(A, v) : null; };
function Qof(A, u) {
  const lc = u.k === 0 ? u.c - 1 : u.pc, col = A[lc];
  let k = u.k === 0 ? -1 : u.pk;
  while (k + 1 < col.length && cmp(col[k + 1].row, u.row) <= 0) k++;
  return k < 0 ? null : col[k];
}
function lex(A, z, w) {
  for (;;) {
    const zu = above(A, z); if (!zu) return true;
    const wu = above(A, w); if (!wu) return false;
    const a = parentOf(A, zu), b = parentOf(A, wu);
    if (a.c < b.c) return true;
    if (!(same(a, b) && cmp(zu.row, wu.row) === 0)) return false;
    z = zu; w = wu;
  }
}
const kindOf = v => v.prov.kind === 'clean' ? (v.prov.ib ? 'cut' : 'clean') : v.prov.kind;

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < verbose) ex[k].push(msg); };
const seen = new Set();
let expansions = 0, nodes = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {R} = r, x0 = s.length - 1;
    for (let X = x0; X < R.length; X++) for (let k = 0; k + 1 < R[X].length; k++) {
      const u = R[X][k], up = R[X][k + 1];
      nodes++;
      const where = `(${s})[${n}] X=${X} u=${show(u.row)}`;
      if (kindOf(up) === 'cut') {
        const ok = u.prov.kind === 'clean' && same(u.prov.src, up.prov.src);
        bump(ok ? 'cut u+: u is a copy of the same root-row node' : 'FAIL cut u+: other u', ok ? null : where);
      }
      const p = parentOf(R, up), q = Qof(R, u);
      if (q.c === p.c) continue;
      let c = q, ok = false;
      for (;;) {
        const b = rawParent(R, c);
        if (!b || b.c < p.c) break;
        if (same(b, p)) { ok = true; break; }
        c = b;
      }
      const tag = `u+ ${kindOf(up)} (u ${kindOf(u)})`;
      if (!ok) { bump(`FAIL chain ${tag}`, where); continue; }
      const cp = above(R, c);
      const lexOK = cmp(cp.row, up.row) === 0 && lex(R, up, cp);
      bump(lexOK ? `CrossLex ok: ${tag}` : `FAIL CrossLex ${tag}`, lexOK ? null : where);
      if (c.value < u.value) bump('FAIL value v(u) <= v(c)', where);
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}, nodes with a node above ${nodes}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
