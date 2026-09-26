// Numerical test of CutPredHolds (OmegaY/Official/Recon/CrossKinds.lean) and of the two
// facts it is reduced to in OmegaY/Official/Recon/CutPredItems.lean:
//
//   LiftPos:  for i != 0, a region S of level d >= 3 below the top row tau (first difference
//             from tau at an exponent >= d - 1), rho = top_S(cr): if column x has a node on the
//             row of rho and x ascends in S, then h(rho) < h(kappa), kappa = top_S(x0).
//             Tested on every such region (not only the reached ones).
//   CleanGap: for i != 0, a reached clean item (C != none, b = 0) of level d >= 2 whose region
//             has a node of column x and ascends: h(rho) <= hB + g (rho = top_S(cr),
//             hB = height of top_T(boundary) in the result, g = generations of (x, C)).
//
// CutPred: in the emits of every copied column, a cut emit (clean, b = 1) is immediately
// preceded by a clean emit of the same source node with the same left column.
//
// It also tests the three facts the Lean proof of CutPredHolds rests on
// (OmegaY/Official/Recon/CutPred{Floor,Lift,Gap,Boundary}.lean):
//   Floor:        for every edge q -> q+ of the last column x0 and every node w of the root
//                 column cr with row w <= row q, the stored parent p of q+ has row p >= row w;
//   SameRegion:   at every clean site the target region equals the source region;
//   BoundaryRows: every row < tau of cr is a row of the boundary column cr + w*i (1 <= i <= n).
//
// Usage: node cut-pred.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                          [--random COUNT,MAXLEN,MAXVAL,SEED] [-v N] [SAMPLE.json ...]
// The rule is the one of omegay.cjs (this repository), instrumented.
'use strict';
const fs = require('fs');
const O = require('./omegay.cjs');
const {cmp, eq, norm, degree, show, mountain, nodeAt, highestBelow, rowParent, topIn} = O;

const coef = (a, k) => a[k] || 0;
const inRegion = (row, R) => { for (let k = R.d - 1; k < Math.max(row.length, R.b.length); k++) if (coef(row, k) !== coef(R.b, k)) return false; return true; };
const height = (row, R) => coef(row, R.d - 2);
function slot(R, j) { const b = R.b.slice(); while (b.length <= R.d - 2) b.push(0); b[R.d - 2] = j; for (let k = 0; k < R.d - 2; k++) b[k] = 0; return {d: R.d - 1, b: norm(b)}; }

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

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < verbose) ex[k].push(msg); };

function ascends(M, x, cr, rho) {
  if (!rho) return false;
  const ref = coef(rho.row, 0) > 0 ? norm([coef(rho.row, 0) - 1, ...rho.row.slice(1)]) : rho.row;
  let a = nodeAt(M, x, ref);
  while (a && a.c > cr) a = rowParent(M, a);
  return !!a && a.c === cr;
}

// LiftPos on every lower region of level >= 3 that has a node of column cr.
function checkLiftPos(M, x, cr, x0, top, where) {
  const seenS = new Set();
  for (let d = 3; d <= degree(top) + 1; d++) for (const nd of M[cr]) {
    const b = norm(nd.row.map((v, k) => k < d - 1 ? 0 : v));
    // LowerRegion: first difference from tau (from the top) at k >= d - 1, with b_k < tau_k
    let below = false;
    for (let k = Math.max(b.length, top.length) - 1; k >= d - 1; k--) if (coef(b, k) !== coef(top, k)) { below = coef(b, k) < coef(top, k); break; }
    if (!below) continue;
    const key = d + ':' + b.join(','); if (seenS.has(key)) continue; seenS.add(key);
    const S = {d, b}, rho = topIn(M, cr, S);
    if (!rho || !nodeAt(M, x, rho.row) || !ascends(M, x, cr, rho)) continue;
    const kap = topIn(M, x0, S), hK = kap ? height(kap.row, S) : 0;
    const ok = height(rho.row, S) < hK;
    bump(ok ? `LiftPos ok (level ${d})` : `FAIL LiftPos (level ${d})`, ok ? null : `${where} S=${show(b)}@${d}`);
  }
}

function copyColumn(M, R, x, i, cr, w, x0, top, lower, where) {
  const X = x + w * i, made = [];
  const shift = p => p >= cr ? p + w * i : p;
  const emit = (row, p, prov) => {
    const q = p < 0 ? -1 : shift(p);
    const par = q < 0 ? null : highestBelow(R, q, row);
    made.push({row, par, prov, left: p});
  };
  const stack = lower.map(S => ({S, T: S, C: null, o: 0, ib: false})).reverse();
  while (stack.length) {
    const {S, T, C, o, ib} = stack.pop();
    const push = list => { for (let t = list.length - 1; t >= 0; t--) stack.push(list[t]); };
    if (S.d === 1) {
      const src = nodeAt(M, x, S.b);
      if (!src) continue;
      if (C) {
        const cs = nodeAt(M, x, C);
        if (!cs) throw new Error('clean copy source missing');
        emit(T.b, cs.pc >= 0 ? cs.pc : x - 1, {kind: 'clean', src: cs, ib});
      } else emit(T.b, src.pc, {kind: 'plain', src});
      continue;
    }
    const tau = topIn(M, x, S);
    if (!tau) continue;
    const kap = topIn(M, x0, S), rho = topIn(M, cr, S);
    const hCut = kap ? height(kap.row, S) : 0, hRoot = rho ? height(rho.row, S) : 0, hTop = height(tau.row, S);
    const asc = ascends(M, x, cr, rho);
    const list = [];
    if (!asc) {
      if (C || o || ib) throw new Error('clean copy of a non-ascending region');
      for (let j = 0; j <= hTop; j++) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
    } else if (!C) {
      const lift = (hCut - hRoot) * i, lim = S.d === 2 ? 1 : 0;
      if (!ib) {
        for (let j = 0; j <= hTop + lift; j++) {
          if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
          else if (j < hRoot + lift + lim) list.push({S: slot(S, hRoot), T: slot(T, j), C: rho.row, o: 0, ib: j > hRoot});
          else list.push({S: slot(S, j - lift), T: slot(T, j), C: null, o: 0, ib: i !== 0 && j === hRoot + lift});
        }
      } else {
        const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
        const tgt = i === 0 ? hTop : hB + hTop;
        for (let j = hRoot; j <= tgt; j++) {
          if (j < hB + hRoot + lim) list.push({S: slot(S, hRoot), T: slot(T, j - hRoot), C: rho.row, o: 0, ib: true});
          else list.push({S: slot(S, j - hB), T: slot(T, j - hRoot), C: null, o: 0, ib: j === hB + hRoot});
        }
      }
    } else {
      const cs = nodeAt(M, x, C);
      if (!cs) throw new Error('clean copy source missing');
      let gen = 0;
      if (cs.pc >= 0) { for (let a = cs; a.c > cr; gen++) { a = nodeAt(M, a.pc, C); if (!a) throw new Error('generation chain leaves the row'); } }
      else gen = x - cr;
      const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
      const tgt = i === 0 ? hTop : hB + gen - o;
      if (!ib && (!b || o)) throw new Error('clean copy without a boundary node');
      if (!ib && i !== 0) {
        let same = true;
        for (let k = S.d - 1; k < Math.max(S.b.length, T.b.length) + 1; k++) if (coef(S.b, k) !== coef(T.b, k)) same = false;
        bump(same ? 'SameRegion ok (clean sites)' : 'FAIL SameRegion', same ? null : `${where} S=${show(S.b)} T=${show(T.b)}`);
        const ok = hRoot <= hB + gen;
        bump(ok ? `CleanGap ok (level ${S.d})` : `FAIL CleanGap (level ${S.d})`, ok ? null : `${where} S=${show(S.b)}@${S.d} hRoot=${hRoot} hB=${hB} g=${gen}`);
        if (ok && hRoot === hB + gen) bump(`CleanGap tight (level ${S.d})`);
      }
      for (let j = 0; j <= tgt; j++) {
        const oo = Math.max(j - hB + o, 0);
        if (ib) list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: true});
        else if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
        else list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: j > hRoot});
      }
    }
    push(list);
  }
  const xa = x === x0 ? cr : x;
  for (const nd of M[xa]) if (cmp(nd.row, top) >= 0) emit(nd.row, nd.pc, {kind: 'upper', src: nd});
  // CutPred on the emits (left column = the stored leg column p before the shift)
  for (let k = 0; k < made.length; k++) {
    const e = made[k];
    if (e.prov.kind !== 'clean' || !e.prov.ib) continue;
    const p = made[k - 1];
    const ok = !!p && p.prov.kind === 'clean' && p.prov.src === e.prov.src && p.left === e.left;
    bump(ok ? 'CutPred ok (cut emits)' : 'FAIL CutPred', ok ? null : `${where} X=${X} k=${k}`);
  }
  for (let k = 1; k < made.length; k++) if (cmp(made[k - 1].row, made[k].row) >= 0) throw new Error('rows not increasing in column ' + X);
  const col = made.map((m, k) => ({c: X, k, row: m.row, value: null, pc: m.par ? m.par.c : -1, pk: m.par ? m.par.k : -1}));
  if (!col.length) throw new Error('empty column ' + X);
  col[col.length - 1].value = 1n;
  for (let k = col.length - 2; k >= 0; k--) {
    const up = col[k + 1];
    if (up.pc < 0) throw new Error('missing parent in column ' + X);
    col[k].value = up.value + R[up.pc][up.pk].value;
  }
  return col;
}

function run(seq, n) {
  const M = mountain(seq), x0 = seq.length - 1;
  const tc = M[x0][M[x0].length - 1];
  if (tc.pc < 0 || n === 0) return;
  const root = M[tc.pc][tc.pk], cr = root.c, w = x0 - cr, top = tc.row;
  let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
  const lower = [];
  for (let e = maxDeg + 3; e >= 2; e--) {
    const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))};
    for (let j = 0; j < coef(top, e - 2); j++) lower.push(slot(hi, j));
  }
  // Floor: parents of the last column
  for (let k = 0; k + 1 < M[x0].length; k++) {
    const q = M[x0][k], up = M[x0][k + 1], p = M[up.pc][up.pk];
    for (const w of M[cr]) if (cmp(w.row, q.row) <= 0) {
      const ok = cmp(w.row, p.row) <= 0;
      bump(ok ? 'Floor ok' : 'FAIL Floor', ok ? null : `(${seq}) q=${show(q.row)} w=${show(w.row)}`);
    }
  }
  const R = M.slice(0, x0);
  const ref = O.expand(seq, n);
  for (let i = 0; i <= n; i++) {
    const xs = [];
    if (i === 0) xs.push(x0); else for (let x = cr + 1; x <= (i < n ? x0 : x0 - 1); x++) xs.push(x);
    for (const x of xs) {
      const where = `(${seq})[${n}] i=${i} x=${x}`;
      if (i !== 0) checkLiftPos(M, x, cr, x0, top, where);
      R[x + w * i] = copyColumn(M, R, x, i, cr, w, x0, top, lower, where);
    }
  }
  for (let i = 1; i <= n; i++) for (const nd of M[cr]) if (cmp(nd.row, top) < 0) {
    const ok = R[cr + w * i].some(m => eq(m.row, nd.row));
    bump(ok ? 'BoundaryRows ok' : 'FAIL BoundaryRows', ok ? null : `(${seq})[${n}] i=${i} row=${show(nd.row)}`);
  }
  const mine = R.map(col => col[0].value);
  if (mine.length !== ref.length || mine.some((v, k) => v !== ref[k])) bump('FAIL harness differs from omegay.cjs', `(${seq})[${n}]`);
}

const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    try { run(s, n); expansions++; } catch (err) { bump('expansion error', `(${s})[${n}] ${err.message}`); }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
