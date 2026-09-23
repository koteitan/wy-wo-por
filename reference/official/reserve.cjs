// Numerical test of the splice classification for candidate atom systems.
//
// Usage: node reserve.cjs [--weak PATH/engine.js] [--copies 1,2,3] [--cand NAME,...]
//                         [--real-control | --top-control] [--examples K] [--legal MAXLEN,MAXVAL]
//                         [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
// Environment: EXTRA_D=k adds k to the key dimension D (default: the largest degree of a
// row of M(s) and M(s[n])); FIX_D=d fixes D = d.
//
// See notes/04-official-design.md. An atom system E assigns to every mountain M a finite
// list of atoms (p, c, K): columns p < c and a key template K (a vector of columns or
// TOP over the scales D, ..., 0, compared lexicographically from scale D, TOP largest).
// E contains the real edges of M. For one expansion s[n] (root column cr, last column x0,
// width w) and each block step b = 0 .. n-1 (boundary B = x0 + b w), every atom
// e = (P, X, K) of E(s[n]) with B <= X < B + w must be classified:
//
//   reserve: P' = P (P < cr) or P' = cr + (P - B) (P >= B) is defined, and some atom
//            (P', cr + (X - B), K') of E(s) with child < x0 has K <= mu_{b+1}(K');
//   seam   : X = B, and some atom (l, x0, K') of E(s) with mu_b(l) = P has
//            K <= mu_b(K') and K < mu_b(Kc), where Kc is the largest key of an atom
//            (cr, x0, Kc) of E(s) (the control).
//
// mu_b is the column map c -> c (c < cr), c + b w (c >= cr). Also every atom of E(s[n])
// with child < x0 must be weaker than an atom of E(s) with the same endpoints (base).
// These are the hypotheses of Phyrion's iterated splice theorem
// (OmegaY/Splice/IteratedReservoirs.lean): graph G_b = the atoms of E(s[n]) below
// column x0 + b w, internal reserve F = the atoms of E(s) below x0, virtual reserve
// T = the atoms of E(s) into x0, control = an atom of T from the root column with the
// largest key, and seam demands N_b = the seam atoms themselves. A failure is reported
// as base, reserve, seam, or cross (the parent lies in an earlier block and the child
// is not the boundary, so no class can apply).
//
// --weak runs the same test on Phyrion's weak-magma expansion (engine.js of
// https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean, Apache-2.0), loaded
// from the given path.
'use strict';
const fs = require('fs');
const O = require('./omegay.cjs');

// ---------- mountain geometry ----------
const TOP = Infinity;
// raw parent of u: the left end of the edge from u to the node above it
function rawParent(M, u) { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; }
// root of u at scale s: follow raw parents along edges of degree <= s
function scaleRoot(M, s, u) {
  for (;;) { const p = rawParent(M, u); if (!p || O.jump(u.row, p.row) > s) return u; u = p; }
}
// key template of an edge from a node at row `row` whose parent is the node p:
// at scale s (from D down to 0), the column of the root of p at scale s if the degree
// jump(row, row p) is at most s, TOP otherwise (Phyrion's keyTemplate)
function keyAt(M, row, p, D) {
  const d = O.jump(row, p.row), K = [];
  for (let s = D; s >= 0; s--) K.push(d <= s ? scaleRoot(M, s, p).c : TOP);
  return K;
}
const keyOf = (M, u, D) => keyAt(M, u.row, rawParent(M, u), D);
function keyCmp(a, b) { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] < b[i] ? -1 : 1; return 0; }
function edges(M, D) {
  const E = [];
  for (const col of M) for (const u of col) { const p = rawParent(M, u); if (p) E.push({p: p.c, c: u.c, K: keyOf(M, u, D), u, par: p}); }
  return E;
}
function maxDeg(M) { let d = 0; for (const col of M) for (const n of col) d = Math.max(d, O.degree(n.row)); return d; }
// the left leg of u: the column of the parent of the edge into u; c - 1 at the bottom
const leg = u => u.k > 0 ? u.pc : u.c - 1;
// the leg atom of u: (leg u, column of u) with the key of a hypothetical edge from u
// whose parent is the highest node of the leg column at a row <= row u
function legAtom(M, u, D) {
  const l = leg(u); let p = null;
  for (const q of M[l]) if (O.cmp(q.row, u.row) <= 0) p = q;
  return {p: l, c: u.c, K: keyAt(M, u.row, p, D)};
}
const legAtoms = (M, D, keep) => {
  const A = [];
  for (const col of M) if (col[0].c > 0) for (const u of col) if (keep(u, col)) A.push(legAtom(M, u, D));
  return A;
};
const realAtoms = (M, D) => edges(M, D).map(({p, c, K}) => ({p, c, K}));

// ---------- atom systems ----------
const CANDS = {
  // Phyrion's representation: the real edges with their keys
  edges: realAtoms,
  // real edges and the leg atoms of the nodes other than the top of a column
  legNoTop: (M, D) => realAtoms(M, D).concat(legAtoms(M, D, (u, col) => u.k < col.length - 1)),
  // real edges and the leg atoms of the nodes other than the bottom of a column
  legNoBottom: (M, D) => realAtoms(M, D).concat(legAtoms(M, D, u => u.k > 0)),
  // the leg atoms of all nodes, without the real edges
  legOnly: (M, D) => legAtoms(M, D, () => true),
  // the design of notes/04: the real edges and the leg atoms of all nodes
  leg: (M, D) => realAtoms(M, D).concat(legAtoms(M, D, () => true)),
};

// ---------- the classification test ----------
let expandSeq = (s, n) => O.expand(s, n);
// control: 'max' (the largest key of an atom from cr into x0), 'real' (the real top edge),
// or 'top' (the leg atom of the top node t of x0; it goes from cr into x0)
function classify(E, s, n, control = 'max') {
  const M = O.mountain(s), x0 = s.length - 1, t = M[x0][M[x0].length - 1];
  const cr = t.pc, w = x0 - cr;
  const out = expandSeq(s, n), MO = O.mountain(out);
  const D = process.env.FIX_D !== undefined ? +process.env.FIX_D : Math.max(maxDeg(M), maxDeg(MO)) + (+process.env.EXTRA_D || 0);
  const Es = E(M, D), EO = E(MO, D);
  let Kc = null;
  if (control === 'real') Kc = keyOf(M, M[x0][M[x0].length - 2], D);
  else if (control === 'top') Kc = legAtom(M, t, D).K;
  else for (const a of Es) if (a.p === cr && a.c === x0 && (!Kc || keyCmp(a.K, Kc) > 0)) Kc = a.K;
  const F = Es.filter(a => a.c < x0), T = Es.filter(a => a.c === x0);
  const map = sh => K => K.map(v => v === TOP || v < cr ? v : v + sh);
  const bad = [];
  for (const e of EO) {
    if (e.c < x0) {
      if (!F.some(a => a.p === e.p && a.c === e.c && keyCmp(e.K, a.K) <= 0)) bad.push({kind: 'base', e});
      continue;
    }
    const b = Math.floor((e.c - x0) / w), B = x0 + b * w;
    if (b >= n) continue;
    const src = cr + (e.c - B);
    const Pp = e.p < cr ? e.p : e.p >= B ? cr + (e.p - B) : null;
    const mu = map((b + 1) * w), nu = map(b * w);
    if (Pp !== null && F.some(a => a.p === Pp && a.c === src && keyCmp(e.K, mu(a.K)) <= 0)) continue;
    if (e.c === B && Kc && keyCmp(e.K, nu(Kc)) < 0 &&
        T.some(a => (a.p < cr ? a.p : a.p + b * w) === e.p && keyCmp(e.K, nu(a.K)) <= 0)) continue;
    bad.push({kind: e.c === B ? 'seam' : Pp === null ? 'cross' : 'reserve', e, b});
  }
  return {bad, out, M, MO, cr, w, x0, D};
}

function main() {
  const args = process.argv.slice(2);
  const opt = {copies: [1, 2, 3], files: [], cands: null, examples: 3, control: 'max'};
  for (let a = 0; a < args.length; a++) {
    const k = args[a];
    if (k === '--weak') opt.weak = args[++a];
    else if (k === '--copies') opt.copies = args[++a].split(',').map(Number);
    else if (k === '--cand') opt.cands = args[++a].split(',');
    else if (k === '--examples') opt.examples = Number(args[++a]);
    else if (k === '--legal') opt.legal = args[++a].split(',').map(Number);
    else if (k === '--random') opt.random = args[++a].split(',').map(Number);
    else if (k === '--real-control') opt.control = 'real';
    else if (k === '--top-control') opt.control = 'top';
    else opt.files.push(k);
  }
  const candNames = opt.cands || Object.keys(CANDS);
  const inputs = [];
  for (const f of opt.files) for (const s of JSON.parse(fs.readFileSync(f, 'utf8'))) inputs.push(s);
  if (opt.legal) {
    const [K, V] = opt.legal;
    const rec = s => { if (s.length >= 2) inputs.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } };
    rec([1]);
  }
  if (opt.random) { // random legal sequences, as in check.cjs (mulberry32)
    let [count, maxLen, maxVal, seed] = opt.random;
    const rnd = () => {
      seed = (seed + 0x6D2B79F5) | 0; let t = seed;
      t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    for (let t = 0; t < count; t++) {
      const len = 2 + Math.floor(rnd() * (maxLen - 1)), s = [1];
      while (s.length < len) s.push(1 + Math.floor(rnd() * maxVal));
      inputs.push(s);
    }
  }
  if (opt.weak) { const Y = require(opt.weak); expandSeq = (s, n) => Y.expand(s.map(BigInt), n).result; }

  const seen = new Set();
  const stat = {}, ex = {};
  for (const name of candNames) { stat[name] = {expansions: 0, failed: 0, base: 0, seam: 0, reserve: 0, cross: 0}; ex[name] = []; }
  for (const s of inputs) {
    const key = s.join(',');
    if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
    seen.add(key);
    for (const n of opt.copies) for (const name of candNames) {
      const st = stat[name];
      const r = classify(CANDS[name], s, n, opt.control);
      st.expansions++;
      if (r.bad.length) {
        st.failed++;
        for (const k of new Set(r.bad.map(x => x.kind))) st[k]++;
        if (ex[name].length < opt.examples) {
          const f = r.bad[0];
          ex[name].push(`(${s})[${n}] = (${r.out}) cr=${r.cr} w=${r.w}: ${f.kind} atom ${f.e.p}->${f.e.c} key [${f.e.K.map(v => v === TOP ? 'T' : v)}] (${r.bad.length} bad atoms)`);
        }
      }
    }
  }
  console.log(`${opt.weak ? 'weak' : 'official'} expansions, ${seen.size} sequences, control ${opt.control}`);
  for (const name of candNames) {
    console.log(name.padEnd(12), JSON.stringify(stat[name]));
    for (const e of ex[name]) console.log('   e.g.', e);
  }
}
if (require.main === module) main();
module.exports = {classify, CANDS, rawParent, scaleRoot, keyAt, keyOf, keyCmp, edges, legAtom, maxDeg, TOP};
