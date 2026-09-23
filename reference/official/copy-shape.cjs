// Numerical test of the facts behind CopyOrder, CopyEmitted, CopyFirst
// (OmegaY/Official/Classification/Proofs/CopyShape*.lean).
//
// Usage: node copy-shape.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                            [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The rule is the one of omegay-trace.cjs (this repository), re-run here with a hook on every
// item of level d >= 2 processed in a block i >= 1.
//
//  MA  (run): a column x that does not ascend in a region S with a root top rho has no node
//             of S above row(rho).
//  MAall (M only): the same for every region (d, row of a node of x or cr), every x in (cr, x0].
//  MD  (run): i >= 1 and x ascends in S => h_kappa > h_rho.
//  MDall (M only): the same for every region as in MAall.
//  MDsource (M only, proved in CopyShapeMD.lean as md_source): h_kappa > h_rho in every such
//             region with a root top, whether x ascends or not (counted once per x).
//  MH  (run): case 4 with b = 0 and i >= 1 => o = 0, the boundary node q exists and
//             h_q + g >= h_rho.
//  Formula: every non-cut emit of block i >= 1 has row F(L, L, row(src)) (lower part) or
//           row(src) (upper part), with the maps F, G of CopyShape (below).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, eq, norm, show, mountain, nodeAt, highestBelow, rowParent, topIn} = O;

const coef = (a, k) => a[k] || 0;
const inRegion = (row, R) => { for (let k = R.d - 1; k < Math.max(row.length, R.b.length); k++) if (coef(row, k) !== coef(R.b, k)) return false; return true; };
const height = (row, R) => coef(row, R.d - 2);
function slot(R, j) { const b = R.b.slice(); while (b.length <= R.d - 2) b.push(0); b[R.d - 2] = j; for (let k = 0; k < R.d - 2; k++) b[k] = 0; return {d: R.d - 1, b: norm(b)}; }
const degree = a => norm(a).length - 1;

const stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };

function ascendsAt(M, cr, x, rho) {
  if (!rho) return false;
  const ref = coef(rho.row, 0) > 0 ? norm([coef(rho.row, 0) - 1, ...rho.row.slice(1)]) : rho.row;
  let a = nodeAt(M, x, ref);
  while (a && a.c > cr) a = rowParent(M, a);
  return !!a && a.c === cr;
}

// the rule, with hooks
function copyColumn(M, R, x, i, cr, w, x0, top, lower, where) {
  const made = [];
  const emit = (row, p, prov) => made.push({row, prov});
  const stack = lower.map(S => ({S, T: S, C: null, o: 0, ib: false})).reverse();
  while (stack.length) {
    const {S, T, C, o, ib} = stack.pop();
    const push = list => { for (let t = list.length - 1; t >= 0; t--) stack.push(list[t]); };
    if (S.d === 1) {
      const src = nodeAt(M, x, S.b);
      if (!src) continue;
      if (C) { const cs = nodeAt(M, x, C); emit(T.b, 0, {kind: 'clean', src: cs, ib}); }
      else emit(T.b, 0, {kind: 'plain', src});
      continue;
    }
    const tau = topIn(M, x, S);
    if (!tau) continue;
    const kap = topIn(M, x0, S), rho = topIn(M, cr, S);
    const hCut = kap ? height(kap.row, S) : 0, hRoot = rho ? height(rho.row, S) : 0, hTop = height(tau.row, S);
    const asc = ascendsAt(M, cr, x, rho);
    const list = [];
    if (i >= 1) {
      if (!asc && rho) {
        const ok = M[x].every(nd => !inRegion(nd.row, S) || cmp(nd.row, rho.row) <= 0);
        bump(ok ? 'MA ok' : 'FAIL MA', ok ? null : where(`x=${x} S=${S.d}:${show(S.b)} rho=${show(rho.row)}`));
      }
      if (asc) {
        const ok = hCut > hRoot;
        bump(ok ? 'MD ok' : 'FAIL MD', ok ? null : where(`x=${x} S=${S.d}:${show(S.b)} hK=${hCut} hR=${hRoot}`));
      }
    }
    if (!asc) {
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
      let gen = 0;
      if (cs.pc >= 0) { for (let a = cs; a.c > cr; gen++) a = nodeAt(M, a.pc, C); } else gen = x - cr;
      const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
      const tgt = i === 0 ? hTop : hB + gen - o;
      if (i >= 1 && !ib) {
        const ok = o === 0 && !!b && hB + gen >= hRoot;
        bump(ok ? 'MH ok' : 'FAIL MH', ok ? null : where(`x=${x} S=${S.d}:${show(S.b)} hB=${hB} g=${gen} hR=${hRoot} o=${o}`));
        bump(hB >= hRoot ? 'MH (hB >= hR alone)' : 'MH (needs g)');
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
  for (const nd of M[xa]) if (cmp(nd.row, top) >= 0) emit(nd.row, 0, {kind: 'upper', src: nd});
  return made;
}

// the maps of CopyShape
function makeMaps(M, R, cr, x0, i, w) {
  const B = cr + w * i;
  const F = (S, T, r) => {
    if (S.d === 1) return T.b;
    const s = height(r, S), rho = topIn(M, cr, S);
    if (!rho) return F(slot(S, s), slot(T, s), r);
    const hR = height(rho.row, S), kap = topIn(M, x0, S), hK = kap ? height(kap.row, S) : 0;
    const D = Math.max(Math.max(hK - hR, 0) * i, 1);
    if (s < hR) return F(slot(S, s), slot(T, s), r);
    if (s === hR && cmp(r, rho.row) <= 0) return F(slot(S, s), slot(T, s), r);
    if (s === hR) return G(slot(S, s), slot(T, hR + D), r);
    return F(slot(S, s), slot(T, s + D), r);
  };
  const G = (S, T, r) => {
    if (S.d === 1) return T.b;
    const s = height(r, S), rho = topIn(M, cr, S);
    if (!rho) return null;
    const hR = height(rho.row, S), b = topIn(R, B, T), hB = b ? height(b.row, T) : 0;
    if (s === hR) return G(slot(S, s), slot(T, hB), r);
    return F(slot(S, s), slot(T, s + hB - hR), r);
  };
  return {F, G};
}

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

const seen = new Set();
let expansions = 0;
for (const s of inputs) {
  const key = s.join(',');
  if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
  seen.add(key);
  let M0;
  try { M0 = mountain(s); } catch (e) { bump('mountain error'); continue; }
  const x0 = s.length - 1, tc = M0[x0][M0[x0].length - 1];
  if (tc.pc < 0) continue;
  const cr = tc.pc, w = x0 - cr, top = tc.row;
  // M-only forms of MA and MD
  {
    for (let x = cr + 1; x <= x0; x++) {
      const seenR = new Set();
      for (const src of [M0[x], M0[cr]]) for (const nd of src) for (let d = 2; d <= degree(nd.row) + 3; d++) {
        const S = {d, b: norm(nd.row.map((v, k) => k < d - 1 ? 0 : v))};
        const k = x + '|' + d + '|' + S.b.join(',');
        if (seenR.has(k)) continue; seenR.add(k);
        if (cmp(S.b, norm(top.map((v, k) => k < d - 1 ? 0 : v))) >= 0) continue; // S must lie below tau
        const rho = topIn(M0, cr, S);
        if (!rho) continue;
        const asc = ascendsAt(M0, cr, x, rho);
        { const kap0 = topIn(M0, x0, S), hK0 = kap0 ? height(kap0.row, S) : 0, ok0 = hK0 > height(rho.row, S);
          bump(ok0 ? 'MDsource ok' : 'FAIL MDsource', ok0 ? null : `(${s}) S=${d}:${show(S.b)}`); }
        if (!asc) {
          const ok = M0[x].every(v => !inRegion(v.row, S) || cmp(v.row, rho.row) <= 0);
          bump(ok ? 'MAall ok' : 'FAIL MAall', ok ? null : `(${s}) x=${x} S=${d}:${show(S.b)}`);
        } else {
          const kap = topIn(M0, x0, S), hK = kap ? height(kap.row, S) : 0;
          const ok = hK > height(rho.row, S);
          bump(ok ? 'MDall ok' : 'FAIL MDall', ok ? null : `(${s}) x=${x} S=${d}:${show(S.b)}`);
        }
      }
    }
  }
  for (const n of copies) {
    let r;
    try { r = O.expandMountain(s, n); } catch (err) { bump('expansion error'); continue; }
    expansions++;
    const {M} = r;
    let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
    const lower = [];
    for (let e = maxDeg + 3; e >= 2; e--) {
      const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))};
      for (let j = 0; j < coef(top, e - 2); j++) lower.push(slot(hi, j));
    }
    const R = r.R;
    for (let i = 1; i <= n; i++) {
      const {F} = makeMaps(M, R, cr, x0, i, w);
      for (let x = cr + 1; x <= (i < n ? x0 : x0 - 1); x++) {
        const where = t => `(${s})[${n}] i=${i} ${t}`;
        const made = copyColumn(M, R, x, i, cr, w, x0, top, lower, where);
        const col = R[x + w * i];
        const same = made.length === col.length && made.every((m, k) => eq(m.row, col[k].row));
        bump(same ? 'replay ok' : 'FAIL replay', same ? null : where(`x=${x}`));
        for (const m of made) {
          if (m.prov.kind === 'clean' && m.prov.ib) continue;
          const sr = m.prov.src.row;
          let want;
          if (m.prov.kind === 'upper') want = sr;
          else { const L = lower.find(L => inRegion(sr, L)); want = L ? F(L, L, sr) : null; }
          const ok = want && eq(want, m.row);
          bump(ok ? 'Formula ok' : 'FAIL Formula', ok ? null : where(`x=${x} src=${show(sr)} row=${show(m.row)} want=${want ? show(want) : '-'}`));
        }
      }
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(10), k); for (const m of ex[k] || []) console.log('             e.g.', m); }
