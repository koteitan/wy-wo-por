// Numerical tests for the proofs of CleanNext, CleanLookup, CleanParent
// (OmegaY/Official/Classification/Proofs/StepInnerClean*.lean, namespace ChainCorr.Inner.Clean).
//
// Usage: node step-inner-clean.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                  [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// The expansion is the rule of omegay-trace.cjs. For every column X = x + w i with i >= 1 and
// cr < x < x0 the items of the rule are replayed (the same traversal as copyColumn) and the
// level-2 items are inspected. The replay is checked against the traced column R[X].
//
// Statements (Lean names):
//  LiftTwo   : a reached level-2 item in case 2 (ascending, C = none, b = 0), i >= 1, whose
//              source column x has a node on the row of rho = top_S(cr): h_rho < h_kappa
//              (proved: liftTwo, and liftLast for every level).
//  GapTwo    : a reached level-2 item in case 4 (ascending, C given, b = 0), i >= 1, whose
//              source column x has a node on row C: h_rho < h_q + g - o.
//  ChainRoot : for a clean copy (b = 0) of a = (y, C): the generation chain of a in row C
//              reaches column cr exactly.
//  ViaRoot   : for a clean copy (b = 0) of a = (y, C), with a+ present, whose chain reaches
//              g = (cr, C): if v(g) >= v(a), then v(raw parent of g) < v(a).
//  CleanParent (on the chain / via g): the statement itself, for reference.
//  BoundaryRows: for 1 <= i <= n, every row < tau of the root column is a row of the output
//              column cr + w i (proved: boundaryRows).
//  LiftLast  : for a region S of level d >= 2 below tau with rho = top_S(cr): h(rho) < h(top_S(x0))
//              (proved: liftLast; tested for d = 2..8 and the regions around the root-column nodes).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, eq, norm, jump, show, expandMountain, nodeAt, topIn, rowParent} = O;
const coef = (a, k) => a[k] || 0;
const height = (row, R) => coef(row, R.d - 2);
function slot(R, j) { const b = R.b.slice(); while (b.length <= R.d - 2) b.push(0); b[R.d - 2] = j; for (let k = 0; k < R.d - 2; k++) b[k] = 0; return {d: R.d - 1, b: norm(b)}; }
const degree = a => norm(a).length - 1;
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
const res = (name, ok, msg) => bump(`${name} ${ok ? 'ok' : 'FAIL'}`, ok ? null : msg);

// Replay of the item traversal of copyColumn (omegay-trace.cjs), with a hook on level-2 items.
function replay(M, R, x, i, cr, w, x0, top, lower, hook) {
  const made = [];
  const stack = lower.map(S => ({S, T: S, C: null, o: 0, ib: false, path: []})).reverse();
  while (stack.length) {
    const it = stack.pop();
    const {S, T, C, o, ib} = it;
    if (S.d === 1) {
      const src = nodeAt(M, x, S.b);
      if (!src) continue;
      if (C) { const cs = nodeAt(M, x, C); made.push({row: T.b, kind: 'clean', src: cs, ib, item: it}); }
      else made.push({row: T.b, kind: 'plain', src, item: it});
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
    const info = {S, T, C, o, ib, asc, hCut, hRoot, hTop, rho, kap, tau, path: it.path};
    if (!asc) {
      for (let j = 0; j <= hTop; j++) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
      info.kase = 1;
    } else if (!C) {
      const lift = (hCut - hRoot) * i, lim = S.d === 2 ? 1 : 0;
      info.lift = lift;
      if (!ib) {
        info.kase = 2;
        for (let j = 0; j <= hTop + lift; j++) {
          if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
          else if (j < hRoot + lift + lim) list.push({S: slot(S, hRoot), T: slot(T, j), C: rho.row, o: 0, ib: j > hRoot});
          else list.push({S: slot(S, j - lift), T: slot(T, j), C: null, o: 0, ib: i !== 0 && j === hRoot + lift});
        }
      } else {
        info.kase = 3;
        const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
        const tgt = i === 0 ? hTop : hB + hTop;
        for (let j = hRoot; j <= tgt; j++) {
          if (j < hB + hRoot + lim) list.push({S: slot(S, hRoot), T: slot(T, j - hRoot), C: rho.row, o: 0, ib: true});
          else list.push({S: slot(S, j - hB), T: slot(T, j - hRoot), C: null, o: 0, ib: j === hB + hRoot});
        }
      }
    } else {
      info.kase = 4;
      const cs = nodeAt(M, x, C);
      let gen = 0;
      if (cs.pc >= 0) { for (let a = cs; a.c > cr; gen++) a = nodeAt(M, a.pc, C); } else gen = x - cr;
      const b = topIn(R, cr + w * i, T), hB = b ? height(b.row, T) : 0;
      const tgt = i === 0 ? hTop : hB + gen - o;
      Object.assign(info, {gen, hB, tgt, bnode: b});
      for (let j = 0; j <= tgt; j++) {
        const oo = Math.max(j - hB + o, 0);
        if (ib) list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: true});
        else if (j < hRoot) list.push({S: slot(S, j), T: slot(T, j), C: null, o: 0, ib: false});
        else list.push({S: slot(S, hRoot), T: slot(T, j), C, o: oo, ib: j > hRoot});
      }
    }
    list.forEach((c, j) => { c.path = it.path.concat([j]); });
    hook(info);
    for (let t = list.length - 1; t >= 0; t--) stack.push(list[t]);
  }
  return made;
}

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
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr, top = t.row;
    let maxDeg = 0; for (const col of M) for (const nd of col) maxDeg = Math.max(maxDeg, degree(nd.row));
    const lower = [];
    for (let e = maxDeg + 3; e >= 2; e--) {
      const hi = {d: e, b: norm(top.map((v, k) => k < e - 2 ? 0 : v))};
      for (let j = 0; j < coef(top, e - 2); j++) lower.push(slot(hi, j));
    }
    // LiftLast (M(s) only, once per sequence): regions of level d = 2..8 below tau around the
    // nodes u of the root column below tau, with top_S(cr) = u.
    if (n === copies[0]) for (const u of M[cr]) {
      if (cmp(u.row, top) >= 0) continue;
      for (let d = 2; d <= 8; d++) {
        const S = {d, b: norm(u.row.map((c, k) => k < d - 1 ? 0 : c))};
        let below = false;
        for (let k = Math.max(top.length, S.b.length) - 1; k >= d - 1; k--) if (coef(top, k) !== coef(S.b, k)) { below = coef(top, k) > coef(S.b, k); break; }
        if (!below || topIn(M, cr, S) !== u) continue;
        const kap = topIn(M, x0, S);
        res(`LiftLast (${u === M[t.pc][t.pk] ? 'rho = root' : 'rho below root'})`, !!kap && coef(u.row, d - 2) < coef(kap.row, d - 2), `(${s}) d=${d} rho=${show(u.row)}`);
      }
    }
    for (let i = 1; i <= n; i++) {
      const B = cr + w * i;
      for (const u of M[cr]) if (cmp(u.row, top) < 0) res('BoundaryRows', R[B].some(q => eq(q.row, u.row)), `(${s})[${n}] i=${i} row=${show(u.row)}`);
    }
    for (let X = x0; X < R.length; X++) {
      const col = R[X], x = col[0].x, i = col[0].i;
      if (i === 0 || x === x0) continue;
      const where = `(${s})[${n}] X=${X} x=${x} i=${i}`;
      const made = replay(M, R, x, i, cr, w, x0, top, lower, info => {
        if (info.S.d !== 2 || !info.asc) return;
        if (info.kase === 2) {
          const nd = info.rho && nodeAt(M, x, info.rho.row);
          if (nd) res('LiftTwo', info.hRoot < info.hCut, `${where} S=${show(info.S.b)} hRoot=${info.hRoot} hCut=${info.hCut}`);
          else bump('LiftTwo (no node on row rho, not needed)');
          bump(`LiftTwo-unconditional ${info.hRoot < info.hCut ? 'ok' : 'fails'}`);
        }
        if (info.kase === 4 && !info.ib) {
          const nd = nodeAt(M, x, info.C);
          if (nd) {
            res('GapTwo', info.hRoot < info.tgt, `${where} S=${show(info.S.b)} hRoot=${info.hRoot} hB=${info.hB} g=${info.gen} o=${info.o}`);
            res('GapTwo rho row = C', !!info.rho && eq(info.rho.row, info.C), where);
          } else bump('GapTwo (no node on row C, not needed)');
        }
      });
      // the replay emits the traced lower part
      const lowerR = col.filter(v => v.prov.kind !== 'upper');
      res('replay = traced lower part', made.length === lowerR.length && made.every((m, k) => eq(m.row, lowerR[k].row) && m.kind === lowerR[k].prov.kind && m.src === lowerR[k].prov.src), where);
      // clean copies (b = 0)
      made.forEach((m, k) => {
        if (m.kind !== 'clean' || m.ib) return;
        const a = m.src, C = a.row;
        // the chain in row C
        const G = []; let cur = a, ok = true;
        while (cur.c > cr) { const b = nodeAt(M, leg(cur), C); if (!b) { ok = false; break; } G.push(b); cur = b; }
        res('ChainRoot', ok && cur.c === cr, `${where} a=(${a.c},${show(C)})`);
        if (!ok || cur.c !== cr) return;
        const g = cur;
        const ap = M[a.c][a.k + 1];
        if (!ap) return;
        // ViaRoot (Lean form): v(g) >= v(a) -> v(raw parent of g) < v(a)
        if (g.value >= a.value) {
          const gp = M[g.c][g.k + 1];
          const pg = gp && gp.pc >= 0 ? M[gp.pc][gp.pk] : null;
          res('ViaRoot (v(g) >= v(a))', !!pg && pg.value < a.value, `${where} a=(${a.c},${show(C)})`);
        } else bump('ViaRoot (v(g) < v(a), not needed)');
        // the parent search from a
        const pa = M[ap.pc][ap.pk];
        const onChain = G.some(q => q === pa);
        if (onChain) { bump('CleanParent on the chain'); return; }
        const gp = M[g.c][g.k + 1];
        const pg = gp && gp.pc >= 0 ? M[gp.pc][gp.pk] : null;
        res('CleanParent via g', !!pg && pg === pa, `${where} a=(${a.c},${show(C)})`);
      });
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
