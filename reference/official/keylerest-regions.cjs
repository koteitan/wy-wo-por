// Numerical test of the region lemmas of KeyLeRest (OmegaY/Official/Classification/Proofs/).
//
// Usage: node keylerest-regions.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                   [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs (notes/03-official-rule.md) with one change:
// every item carries the list of cases (notes/03 §2.4) that produced it, so every emitted
// node of the lower part records the case of the item just above its level-1 item:
//   1     case 1 (the region does not ascend)       2low  case 2, slot below the root height
//   2gap  case 2, copy of the root row              2lift case 2, lifted slot
//   3gap  case 3, copy of the root row              3lift case 3, lifted slot
//   4low  case 4 (b = 0), slot below the root       4gap  case 4 (b = 0), copy of the root row
//   4cut  case 4 (b = 1)                            top   a first item of level 1
// For every node u of an output column X = x + w i >= x0 with origin o (Trace.lean), outside
// the proved upper case (upper part, leg left of cr), it checks KeyLeShift
// (Proofs/KeyShift.lean):  key(e) <= phi_i(key(a)),  e = leg atom of u in M(s[n]),
// a = leg atom of o.src in M(s), phi_i(c) = c (c < cr), c + w i (c >= cr).
// Per region it prints how often key(a) is all TOP ("top": proved, Proofs/KeyRegions.lean),
// key(e) = phi_i(key(a)) ("equal"), is entrywise below
// ("pointwise") or only lexicographically below ("lex"), how the jump d_e of the output leg
// compares with the jump d_a of the origin's leg, and whether the origin's leg is cr.
// Regions: block0 (i = 0; proved, Proofs/KeyBlockZero.lean), upper (i >= 1, leg >= cr), and
// for the lower part with i >= 1: boundary (x = x0) or inner (x < x0), origin kind, case.
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {mountain, nodeAt, highestBelow, rowParent, topIn, cmp, degree, norm, show, jump} = O;
const {legAtom, keyCmp, maxDeg, TOP} = require('./reserve.cjs');
const coef = (a, k) => a[k] || 0;
const height = (row, R) => coef(row, R.d - 2);
function slot(R, j) { const b = R.b.slice(); while (b.length <= R.d - 2) b.push(0); b[R.d - 2] = j; for (let k = 0; k < R.d - 2; k++) b[k] = 0; return {d: R.d - 1, b: norm(b)}; }

// ---------- the rule of omegay-trace.cjs, with the case path of every item ----------
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
  const stack = lower.map(S => ({S, T: S, C: null, o: 0, ib: false, path: []})).reverse();
  while (stack.length) {
    const {S, T, C, o, ib, path} = stack.pop();
    const push = list => { for (let t = list.length - 1; t >= 0; t--) stack.push(list[t]); };
    if (S.d === 1) {
      const src = nodeAt(M, x, S.b);
      if (!src) continue;
      if (C) {
        const cs = nodeAt(M, x, C);
        if (!cs) throw new Error('clean copy source missing');
        emit(T.b, cs.pc >= 0 ? cs.pc : x - 1, {kind: 'clean', src: cs, ib, path});
      } else emit(T.b, src.pc, {kind: 'plain', src, path});
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
    void ((asc ? (C ? 'clean' : ib ? 'lifted-ib' : 'lifted') : 'plain') + '@' + S.d);
    if (!asc) {
      if (C || o || ib) throw new Error('clean copy of a non-ascending region');
      for (let j = 0; j <= hTop; j++) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false, path: path.concat([{d: S.d, c: '1'}])});
    } else if (!C) {
      const lift = (hCut - hRoot) * i, lim = S.d === 2 ? 1 : 0;
      if (!ib) {
        for (let j = 0; j <= hTop + lift; j++) {
          if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false, path: path.concat([{d: S.d, c: '2low'}])});
          else if (j < hRoot + lift + lim) list.push({S: slot(S, hRoot), T: slot(T, j), C: rho.row, o: 0, ib: j > hRoot, path: path.concat([{d: S.d, c: '2gap'}])});
          else list.push({S: slot(S, j - lift), T: slot(T, j), C: null, o: 0, ib: i !== 0 && j === hRoot + lift, path: path.concat([{d: S.d, c: '2lift'}])});
        }
      } else {
        const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
        const tgt = i === 0 ? hTop : hB + hTop;
        for (let j = hRoot; j <= tgt; j++) {
          if (j < hB + hRoot + lim) list.push({S: slot(S, hRoot), T: slot(T, j - hRoot), C: rho.row, o: 0, ib: true, path: path.concat([{d: S.d, c: '3gap'}])});
          else list.push({S: slot(S, j - hB), T: slot(T, j - hRoot), C: null, o: 0, ib: j === hB + hRoot, path: path.concat([{d: S.d, c: '3lift'}])});
        }
      }
    } else {
      const cs = nodeAt(M, x, C);
      if (!cs) throw new Error('clean copy source missing');
      let gen = 0;
      void (cs.pc >= 0 ? 'generations-row' : 'generations-bottom');
      if (cs.pc >= 0) { for (let a = cs; a.c > cr; gen++) { a = nodeAt(M, a.pc, C); if (!a) throw new Error('generation chain leaves the row'); } }
      else gen = x - cr;
      const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
      const tgt = i === 0 ? hTop : hB + gen - o;
      if (!ib && (!b || o)) throw new Error('clean copy without a boundary node');
      for (let j = 0; j <= tgt; j++) {
        const oo = Math.max(j - hB + o, 0);
        if (ib) list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: true, path: path.concat([{d: S.d, c: '4cut'}])});
        else if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false, path: path.concat([{d: S.d, c: '4low'}])});
        else list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: j > hRoot, path: path.concat([{d: S.d, c: '4gap'}])});
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


// ---------- the test ----------
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
let expansions = 0, nodes = 0;
const hAM = (M, l, row) => { let p = null; for (const q of M[l]) if (cmp(q.row, row) <= 0) p = q; return p; };
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    const MO = mountain(R.map(c => c[0].value));
    const D = Math.max(maxDeg(M), maxDeg(MO));
    for (let X = x0; X < MO.length; X++) for (const u of MO[X]) {
      const ru = R[X][u.k];
      if (!ru || cmp(ru.row, u.row) !== 0 || ru.pc !== u.pc || ru.pk !== u.pk) { bump('FAIL reconstruction', `(${s})[${n}] X=${X}`); continue; }
      const o = ru.prov, i = ru.i, x = ru.x, src = o.src;
      const a = legAtom(M, src, D), e = legAtom(MO, u, D);
      if (o.kind === 'upper' && a.p < cr) continue; // proved: KeyUpper.keyOK_upper_low
      nodes++;
      const mk = a.K.map(v => v === TOP || v < cr ? v : v + w * i);
      const c = keyCmp(e.K, mk);
      const where = `(${s})[${n}] X=${X} i=${i} row=${show(u.row)} ${o.kind}(${src.c},${show(src.row)})`;
      let region;
      if (i === 0) region = 'block0';
      else if (o.kind === 'upper') region = 'upper';
      else {
        const last = o.path.length ? o.path[o.path.length - 1].c : 'top';
        const kind = o.kind === 'clean' ? (o.ib ? 'cleancut' : 'clean') : 'plain';
        region = `${x === x0 ? 'boundary' : 'inner'} ${kind} case ${last}`;
      }
      if (c > 0) bump(`FAIL ${region}`, where);
      const rel = a.K.every(v => v === TOP) ? 'top' : c === 0 ? 'equal' : e.K.every((v, j) => v <= mk[j]) ? 'pointwise' : 'lex';
      const pe = hAM(MO, e.p, u.row), pa = hAM(M, a.p, src.row);
      const de = jump(u.row, pe.row), da = jump(src.row, pa.row);
      bump(`${region.padEnd(30)} ${rel.padEnd(9)} d_e${de < da ? '<' : de === da ? '=' : '>'}d_a leg${a.p === cr ? '=cr' : '>cr'}`, rel === 'lex' || de > da ? where : null);
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}, nodes tested ${nodes}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
