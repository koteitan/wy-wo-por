// Numerical test of CopyEmitted, CopyFirst, CopyOrder and its variants on the traced run
// (OmegaY/Official/Classification/Proofs/CopyShapeNoMA*.lean).
//
// Usage: node copy-noma.cjs [--copies 1,2] [--legal MAXLEN,MAXVAL]
//                           [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The emits of the copy of column y in block i are the nodes of the output column y + w*i
// with their origins (omegay-trace.cjs). A non-cut emit is one whose origin is not
// {kind: 'clean', ib: true}. Only runs whose output mountain is the canonical mountain of the
// output values (the reconstruction of SpliceData) are counted.
//
//  CE   CopyEmitted: in an inner column (cr < y < x0), every node is the origin of a non-cut
//       emit.
//  CF   CopyFirst: in an inner column the first emit of every origin is non-cut.
//  COlt CopyOrder (strict part): non-cut emits of two block columns, origin rows r < r' =>
//       rows <. Counted once per pair of consecutive origin rows of the block (sorted), which
//       is equivalent to the check over all pairs.
//  COeq CopyOrder (equal part): origin rows r = r' => equal rows (once per origin row).
//  COsame, COsameEq  the same inside one column (y = y'): CopyOrderSame.
//  COleg   CopyOrder for a node u and its leg tip p_u (the highest node of the column of the
//          left end of u at or below row u), when that column is a block column.
//  COpar   CopyOrder for a node u and the left end (raw parent) of u, when its column is a
//          block column.
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
      // CE, CF
      for (const y of ys) {
        if (y === x0) continue;
        for (const nd of M[y]) {
          const ok = es[y].some(e => nc(e) && e.prov.src === nd);
          bump(ok ? 'CE ok' : 'FAIL CE', ok ? null : where(`i=${i} y=${y} node ${show(nd.row)}`));
        }
        const first = new Set();
        for (const e of es[y]) {
          if (first.has(e.prov.src)) continue;
          first.add(e.prov.src);
          bump(nc(e) ? 'CF ok' : 'FAIL CF', nc(e) ? null : where(`i=${i} y=${y} src ${show(e.prov.src.row)}`));
        }
      }
      // CopyOrder variants, by sorting (all pairs of non-cut emits of the block)
      const all = [];
      for (const y of ys) for (const e of es[y]) if (nc(e)) all.push({y, e});
      const orderCheck = (list, tagEq, tagLt) => {
        // origin row -> emit rows; equal origin rows need equal rows, and the emit rows of a
        // higher origin row must all be above those of a lower one
        list.sort((a, b) => cmp(a.e.prov.src.row, b.e.prov.src.row));
        const groups = [];
        for (const a of list) {
          const g = groups[groups.length - 1];
          if (g && eq(g.r, a.e.prov.src.row)) g.items.push(a); else groups.push({r: a.e.prov.src.row, items: [a]});
        }
        const msg = (a, b) => where(`i=${i} (${a.y},${show(a.e.prov.src.row)})->${show(a.e.row)} (${b.y},${show(b.e.prov.src.row)})->${show(b.e.row)}`);
        let prevMax = null;
        for (const g of groups) {
          let mn = g.items[0], mx = g.items[0];
          for (const a of g.items) { if (cmp(a.e.row, mn.e.row) < 0) mn = a; if (cmp(a.e.row, mx.e.row) > 0) mx = a; }
          if (tagEq) { const ok = eq(mn.e.row, mx.e.row); bump(ok ? tagEq + ' ok' : 'FAIL ' + tagEq, ok ? null : msg(mn, mx)); }
          if (prevMax) { const ok = cmp(prevMax.e.row, mn.e.row) < 0; bump(ok ? tagLt + ' ok' : 'FAIL ' + tagLt, ok ? null : msg(prevMax, mn)); }
          if (!prevMax || cmp(mx.e.row, prevMax.e.row) > 0) prevMax = mx;
        }
      };
      orderCheck(all.slice(), 'COeq', 'COlt');
      for (const y of ys) orderCheck(all.filter(a => a.y === y), 'COsameEq', 'COsame');
      // leg tips and raw parents
      for (const y of ys) for (const e of es[y]) {
        if (!nc(e)) continue;
        const u = e.prov.src;
        const lc = u.pc >= 0 ? u.pc : u.c - 1;
        if (!ys.includes(lc)) continue;
        let tip = null; for (const q of M[lc]) if (cmp(q.row, u.row) <= 0) tip = q;
        const pairs = [['COleg', tip]];
        if (u.pc >= 0) pairs.push(['COpar', M[u.pc][u.pk]]);
        for (const [tag, q] of pairs) {
          if (!q) continue;
          for (const f of es[lc]) {
            if (!nc(f) || f.prov.src !== q) continue;
            const c = cmp(q.row, u.row), d = cmp(f.row, e.row);
            const ok = c < 0 ? d < 0 : c === 0 ? d === 0 : d > 0;
            bump(ok ? tag + ' ok' : 'FAIL ' + tag, ok ? null : where(`i=${i} u=(${y},${show(u.row)})->${show(e.row)} q=(${lc},${show(q.row)})->${show(f.row)}`));
          }
        }
      }
    }
  }
}
console.log(`inputs ${seen.size}, legal ${legal}, runs ${runs}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
