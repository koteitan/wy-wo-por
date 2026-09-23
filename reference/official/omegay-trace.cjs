// Official omega-Y expansion with the origin of every emitted node.
//
// Generated from omegay.cjs of this repository (same rule, notes/03-official-rule.md);
// the only change is that every emitted node records its origin, as in
// OmegaY/Official/Classification/Trace.lean:
//   {kind: 'plain', src}      level-1 item without a copied root row (src = node (x, sigma))
//   {kind: 'clean', src, ib}  level-1 item copying the root row C (src = node (x, C); ib = cut flag)
//   {kind: 'upper', src}      upper part (src = node of column x' at the same row)
// Output nodes carry {prov, x, i}. Used by classification-witness.cjs.
// Official omega-Y expansion (clean-room implementation).
//
// Written from the specification in notes/03-official-rule.md of this repository.
// It was tested against the outputs of Naruyoko's program StudyAndExpandSequence
// (https://github.com/Naruyoko/StudyAndExpandSequence, the definition of omega-Y),
// but it is not derived from its code: that program has no license, and no part of
// it is reproduced here. The canonical mountain follows the rule stated in
// notes/00-survey.md section 1.3.
//
// Conventions: a row is an ordinal below omega^omega, stored as its Cantor
// coefficients in ascending exponent order ([] is 0, the bottom row). Columns are
// numbered from 0. A node is {c, k, row, value, pc, pk}: column c, index k in its
// column (0 is the bottom), value (BigInt), and parent (pc, pk) = the left end of the
// edge from the node below to this node (-1 for a bottom node).
'use strict';

// ---------- ordinals below omega^omega ----------
const coef = (a, k) => a[k] || 0;
function norm(a) { const b = a.slice(); while (b.length && !b[b.length - 1]) b.pop(); return b; }
function cmp(a, b) {
  for (let k = Math.max(a.length, b.length) - 1; k >= 0; k--) {
    const x = coef(a, k), y = coef(b, k);
    if (x !== y) return x < y ? -1 : 1;
  }
  return 0;
}
const eq = (a, b) => cmp(a, b) === 0;
// jump(a, b) = 0 if a = b, else 1 + the highest exponent where a and b differ.
function jump(a, b) {
  for (let k = Math.max(a.length, b.length) - 1; k >= 0; k--) if (coef(a, k) !== coef(b, k)) return k + 1;
  return 0;
}
// a + omega^e (ordinal sum): coefficients below e are dropped.
function addPow(a, e) {
  const b = [];
  for (let k = 0; k < Math.max(a.length, e + 1); k++) b.push(k < e ? 0 : coef(a, k));
  b[e]++;
  return norm(b);
}
const degree = a => norm(a).length - 1;
function show(a) {
  const sup = n => String(n).replace(/\d/g, d => '⁰¹²³⁴⁵⁶⁷⁸⁹'[+d]);
  const t = [];
  for (let k = a.length - 1; k >= 0; k--) {
    const c = coef(a, k); if (!c) continue;
    if (k === 0) t.push(String(c)); else t.push('ω' + (k > 1 ? sup(k) : '') + (c > 1 ? '·' + c : ''));
  }
  return t.join('+') || '0';
}

// ---------- canonical mountain ----------
// Parent search for the top node u of column c (value v > 1): a cursor starts at u.
// Repeat: remember the cursor's row as the ceiling; move the cursor to its left
// neighbour (the parent of a non-bottom node; the phantom below the bottom of the
// previous column for a bottom node); climb in that column while the next node up
// has row <= ceiling. Stop at the first real node with value < v.
function mountain(seq) {
  const M = [];
  for (let c = 0; c < seq.length; c++) {
    const v0 = BigInt(seq[c]);
    if (v0 < 1n) throw new Error('entries must be positive');
    const col = [{c, k: 0, row: [], value: v0, pc: -1, pk: -1}];
    M.push(col);
    while (col[col.length - 1].value > 1n) {
      const u = col[col.length - 1];
      let cur = {c, k: u.k}; // k = -1 is the phantom
      const rowOf = p => p.k < 0 ? null : M[p.c][p.k].row;
      for (;;) {
        const ceiling = rowOf(cur);
        if (cur.k === 0) { if (cur.c === 0) throw new Error('no parent'); cur = {c: cur.c - 1, k: -1}; }
        else if (cur.k > 0) { const n = M[cur.c][cur.k]; cur = {c: n.pc, k: n.pk}; }
        else throw new Error('no parent');
        const cc = M[cur.c];
        while (cur.k + 1 < cc.length && ceiling !== null && cmp(cc[cur.k + 1].row, ceiling) <= 0) cur = {c: cur.c, k: cur.k + 1};
        if (cur.k >= 0 && M[cur.c][cur.k].value < u.value) break;
      }
      const p = M[cur.c][cur.k];
      col.push({c, k: col.length, row: addPow(u.row, jump(p.row, u.row)), value: u.value - p.value, pc: p.c, pk: p.k});
    }
  }
  return M;
}

// ---------- queries ----------
const nodeAt = (M, c, row) => (M[c] || []).find(n => eq(n.row, row)) || null;
function highestBelow(M, c, row) {
  let best = null;
  for (const n of M[c] || []) if (cmp(n.row, row) < 0) best = n;
  return best;
}
// A region of level d >= 1 with base row b: all rows that agree with b in the
// coefficients of omega^k for k >= d-1. Level 1 is a single row. Slot j of a region
// of level d >= 2 is the region of level d-1 whose coefficient of omega^(d-2) is j.
const inRegion = (row, R) => { for (let k = R.d - 1; k < Math.max(row.length, R.b.length); k++) if (coef(row, k) !== coef(R.b, k)) return false; return true; };
const height = (row, R) => coef(row, R.d - 2);
function slot(R, j) { const b = R.b.slice(); while (b.length <= R.d - 2) b.push(0); b[R.d - 2] = j; for (let k = 0; k < R.d - 2; k++) b[k] = 0; return {d: R.d - 1, b: norm(b)}; }
function topIn(M, c, R) { let best = null; for (const n of M[c] || []) if (inRegion(n.row, R)) best = n; return best; }
// In-row parent of a node: the parent of the node just above it, when that parent
// lies in the same row (then the node above is at row + 1). Otherwise none.
function rowParent(M, n) {
  const up = M[n.c][n.k + 1];
  if (!up || up.pc < 0) return null;
  const p = M[up.pc][up.pk];
  return eq(p.row, n.row) ? p : null;
}

// ---------- official expansion ----------
// Branch counters (for test coverage only; see check.cjs --coverage).
const counters = {};
const tick = k => { counters[k] = (counters[k] || 0) + 1; };
function expandMountain(seq, n) {
  const M = mountain(seq), x0 = seq.length - 1;
  if (x0 < 0) return {M, R: [], root: null};
  const tc = M[x0][M[x0].length - 1];
  if (tc.pc < 0 || n === 0) return {M, R: M.slice(0, x0), root: tc.pc < 0 ? null : M[tc.pc][tc.pk]};
  const root = M[tc.pc][tc.pk], cr = root.c, w = x0 - cr, top = tc.row;
  let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
  // regions entirely below the top row of the last column, in ascending order
  const lower = [];
  for (let e = maxDeg + 3; e >= 2; e--) {
    const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))};
    for (let j = 0; j < coef(top, e - 2); j++) lower.push(slot(hi, j));
  }
  const R = M.slice(0, x0); // the result; earlier columns are shared read-only
  for (let i = 0; i <= n; i++) {
    const xs = [];
    if (i === 0) xs.push(x0); else for (let x = cr + 1; x <= (i < n ? x0 : x0 - 1); x++) xs.push(x);
    for (const x of xs) R[x + w * i] = copyColumn(M, R, x, i, cr, w, x0, top, lower);
  }
  return {M, R, root};
}

function copyColumn(M, R, x, i, cr, w, x0, top, lower) {
  const X = x + w * i, made = [];
  const shift = p => p >= cr ? p + w * i : p;
  const emit = (row, p, prov) => {
    const q = p < 0 ? -1 : shift(p);
    const par = q < 0 ? null : highestBelow(R, q, row);
    made.push({row, par, prov});
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
    let asc = false;
    if (rho) {
      const ref = coef(rho.row, 0) > 0 ? norm([coef(rho.row, 0) - 1, ...rho.row.slice(1)]) : rho.row;
      let a = nodeAt(M, x, ref);
      while (a && a.c > cr) a = rowParent(M, a);
      asc = !!a && a.c === cr;
    }
    const list = [];
    tick((asc ? (C ? 'clean' : ib ? 'lifted-ib' : 'lifted') : 'plain') + '@' + S.d);
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
      tick(cs.pc >= 0 ? 'generations-row' : 'generations-bottom');
      if (cs.pc >= 0) { for (let a = cs; a.c > cr; gen++) { a = nodeAt(M, a.pc, C); if (!a) throw new Error('generation chain leaves the row'); } }
      else gen = x - cr;
      const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
      const tgt = i === 0 ? hTop : hB + gen - o;
      if (!ib && (!b || o)) throw new Error('clean copy without a boundary node');
      for (let j = 0; j <= tgt; j++) {
        const oo = Math.max(j - hB + o, 0);
        if (ib) list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: true});
        else if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
        else list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: j > hRoot});
      }
    }
    push(list);
  }
  // rows at or above the top row of the last column: copied without lifting
  const xa = x === x0 ? cr : x;
  for (const nd of M[xa]) if (cmp(nd.row, top) >= 0) emit(nd.row, nd.pc, {kind: 'upper', src: nd});
  // assemble the column; values from the top: v(top) = 1, v(u) = v(u+) + v(parent(u+))
  for (let k = 1; k < made.length; k++) if (cmp(made[k - 1].row, made[k].row) >= 0) throw new Error('rows not increasing in column ' + X);
  const col = made.map((m, k) => ({c: X, k, row: m.row, value: null, pc: m.par ? m.par.c : -1, pk: m.par ? m.par.k : -1, prov: m.prov, x, i}));
  if (!col.length) throw new Error('empty column ' + X);
  col[col.length - 1].value = 1n;
  for (let k = col.length - 2; k >= 0; k--) {
    const up = col[k + 1];
    if (up.pc < 0) throw new Error('missing parent in column ' + X);
    col[k].value = up.value + R[up.pc][up.pk].value;
  }
  return col;
}

const expand = (seq, n) => expandMountain(seq, n).R.map(col => col[0].value);

module.exports = {counters, norm, cmp, eq, jump, addPow, degree, show, mountain, nodeAt, highestBelow, rowParent, topIn, expandMountain, expand};
