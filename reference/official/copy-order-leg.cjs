// Numerical test of CopyOrderLeg, the form of CopyOrder used by its callers
// (OmegaY/Official/Classification/Proofs/CopyShapeNoMA*.lean).
//
// Usage: as copy-noma.cjs.
//
//  COlegcol  for a non-cut emit e of a block column y with origin u, and the leg column
//            l = column of the left end of u (column y - 1 for a bottom node) when l is a block
//            column (cr < l): for every non-cut emit f of column l, the rows of e and f compare
//            like the rows of their origins (<, =, >).
//  COpairs   CopyOrder over all pairs of non-cut emits of the block (the statement of
//            ChainCorr.CopyOrder), for comparison; checked on neighbours after sorting by
//            (origin row, row), which is equivalent (one count per neighbouring pair).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, eq, show, mountain} = O;

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 4) ex[k].push(msg); };

// The canonical mountain of the output values (the rule of mountain() in omegay-trace.cjs,
// with BigInt values), compared column by column with the traced mountain R; a column that
// grows beyond the traced one is a mismatch (this keeps the check finite).
function canonMatches(values, R) {
  const M = [];
  for (let c = 0; c < values.length; c++) {
    const col = [{c, k: 0, row: [], value: BigInt(values[c]), pc: -1, pk: -1}];
    M.push(col);
    while (col[col.length - 1].value > 1n) {
      if (col.length >= R[c].length) return false;
      const u = col[col.length - 1];
      let cur = {c, k: u.k};
      const rowOf = p => p.k < 0 ? null : M[p.c][p.k].row;
      for (;;) {
        const ceiling = rowOf(cur);
        if (cur.k === 0) { if (cur.c === 0) return false; cur = {c: cur.c - 1, k: -1}; }
        else if (cur.k > 0) { const nd = M[cur.c][cur.k]; cur = {c: nd.pc, k: nd.pk}; }
        else return false;
        const cc = M[cur.c];
        while (cur.k + 1 < cc.length && ceiling !== null && cmp(cc[cur.k + 1].row, ceiling) <= 0) cur = {c: cur.c, k: cur.k + 1};
        if (cur.k >= 0 && M[cur.c][cur.k].value < u.value) break;
      }
      const p = M[cur.c][cur.k];
      col.push({c, k: col.length, row: O.addPow(u.row, O.jump(p.row, u.row)), value: u.value - p.value, pc: p.c, pk: p.k});
    }
    if (col.length !== R[c].length) return false;
    for (let k = 0; k < col.length; k++)
      if (!eq(col[k].row, R[c][k].row) || col[k].pc !== R[c][k].pc || col[k].pk !== R[c][k].pk) return false;
  }
  return true;
}

// Runs whose output has more than MAXNODES nodes are skipped, with the larger n of the input
// (environment variable MAXNODES, default: no limit).
const MAXNODES = Number(process.env.MAXNODES || Infinity);

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2];
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

const seen = new Set();
let runs = 0, legal = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  let M;
  try { M = mountain(s); } catch (e) { continue; }
  legal++;
  const x0 = s.length - 1, tc = M[x0][M[x0].length - 1];
  if (tc.pc < 0) continue;
  const cr = tc.pc, w = x0 - cr;
  for (const n of copies) {
    let r, out;
    try { r = O.expandMountain(s, n); out = r.R.map(c => c[0].value); } catch (e) { bump('expansion error'); continue; }
    { let nodes = 0; for (const c of r.R) nodes += c.length;
      if (nodes > MAXNODES) { bump('SKIP big (and larger n)'); break; } }
    if (!canonMatches(out, r.R)) { bump('SKIP reconstruction'); continue; }
    runs++;
    const R = r.R;
    M = r.M; // the origins are nodes of this copy of M(s)
    const where = t => `(${s})[${n}] ${t}`;
    for (let i = 1; i <= n; i++) {
      const ys = []; for (let y = cr + 1; y <= (i < n ? x0 : x0 - 1); y++) ys.push(y);
      const es = {}; for (const y of ys) es[y] = R[y + w * i];
      const nc = e => !(e.prov.kind === 'clean' && e.prov.ib);
      for (const y of ys) for (const e of es[y]) {
        if (!nc(e)) continue;
        const u = e.prov.src;
        const lc = u.pc >= 0 ? u.pc : u.c - 1;
        if (!ys.includes(lc)) continue;
        for (const f of es[lc]) {
          if (!nc(f)) continue;
          const c = cmp(u.row, f.prov.src.row), d = cmp(e.row, f.row);
          const ok = Math.sign(c) === Math.sign(d);
          bump(ok ? 'COlegcol ok' : 'FAIL COlegcol', ok ? null : where(`i=${i} u=(${y},${show(u.row)})->${show(e.row)} f=(${lc},${show(f.prov.src.row)})->${show(f.row)}`));
        }
      }
      // COpairs by sorting: origin row -> emit row must be a strictly increasing function
      const all = [];
      for (const y of ys) for (const e of es[y]) if (nc(e)) all.push({y, e});
      all.sort((a, b) => cmp(a.e.prov.src.row, b.e.prov.src.row) || cmp(a.e.row, b.e.row));
      for (let t = 1; t < all.length; t++) {
        const a = all[t - 1], b = all[t];
        const ok = Math.sign(cmp(a.e.prov.src.row, b.e.prov.src.row)) === Math.sign(cmp(a.e.row, b.e.row));
        bump(ok ? 'COpairs ok' : 'FAIL COpairs', ok ? null : where(`i=${i} (${a.y},${show(a.e.prov.src.row)})->${show(a.e.row)} (${b.y},${show(b.e.prov.src.row)})->${show(b.e.row)}`));
      }
    }
  }
}
console.log(`inputs ${seen.size}, legal ${legal}, runs ${runs}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
