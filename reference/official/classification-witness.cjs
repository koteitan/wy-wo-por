// Numerical test of the canonical witness of the splice classification.
//
// Usage: node classification-witness.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                                        [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
// Environment: EXTRA_D=k adds k to the key dimension D (default: the largest degree of a
// row of M(s) and M(s[n])).
//
// For every expansion s[n] (official rule, omegay-trace.cjs) and every node u of an output
// column X >= x0, let o be the origin of u and a = the leg atom of o.src in M(s), e = the
// leg atom of u in M(s[n]); b = floor((X - x0)/w), B = x0 + b w. The test checks the
// statement WitnessOK / KeyOK2 of OmegaY/Official/Classification/{Witness,KeyOrder}.lean:
//   seam    (X = B and o not upper): a.child = x0, mu_b(a.parent) = e.parent,
//           key(e) <= mu_b(key(a)), key(a) < Kc (Kc = key of the leg atom of the top of x0);
//   reserve (otherwise): a.child = cr + (X - B) < x0, a.parent = P' (as in reserveOK),
//           key(e) <= mu_{b+1}(key(a)).
// It also checks that the traced mountain equals the canonical mountain of the output, and
// prints how often key(e) equals / is pointwise below / is only lexicographically below
// the mapped key, per origin kind, block position and leg column (< cr or >= cr).
'use strict';
const fs = require('fs');
const P = require('./omegay-trace.cjs');
const O = require('./omegay.cjs');
const {legAtom, keyCmp, maxDeg, TOP} = require('./reserve.cjs');

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
  for (const n of copies) {
    let r;
    try { r = P.expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    const MO = O.mountain(R.map(c => c[0].value));
    const D = Math.max(maxDeg(M), maxDeg(MO)) + (+process.env.EXTRA_D || 0);
    const Kc = legAtom(M, t, D).K;
    const mapK = sh => K => K.map(v => v === TOP || v < cr ? v : v + sh);
    const mapC = sh => v => v < cr ? v : v + sh;
    for (let X = x0; X < MO.length; X++) for (const u of MO[X]) {
      const ru = R[X][u.k];
      if (!ru || O.cmp(ru.row, u.row) !== 0 || ru.pc !== u.pc || ru.pk !== u.pk) { bump('FAIL reconstruction', `(${s})[${n}] X=${X}`); continue; }
      const o = ru.prov, e = legAtom(MO, u, D), a = legAtom(M, o.src, D);
      const b = Math.floor((X - x0) / w), B = x0 + b * w;
      const seam = X === B && o.kind !== 'upper';
      const kind = o.kind === 'clean' && o.ib ? 'clean-cut' : o.kind;
      const where = `(${s})[${n}] X=${X} row=${O.show(u.row)} origin=${o.kind}(${o.src.c},${O.show(o.src.row)})`;
      let ok;
      if (seam) ok = a.c === x0 && mapC(b * w)(a.p) === e.p && keyCmp(e.K, mapK(b * w)(a.K)) <= 0 && keyCmp(a.K, Kc) < 0;
      else {
        const Pp = e.p < cr ? e.p : e.p >= B ? cr + (e.p - B) : null;
        ok = a.c === cr + X - B && a.c < x0 && Pp !== null && a.p === Pp && keyCmp(e.K, mapK((b + 1) * w)(a.K)) <= 0;
      }
      if (!ok) bump('FAIL witness', where);
      const mk = mapK(seam ? b * w : (b + 1) * w)(a.K);
      const rel = keyCmp(e.K, mk) === 0 ? 'equal' : e.K.every((v, j) => v <= mk[j]) ? 'pointwise' : 'lex only';
      bump(`${seam ? 'seam   ' : 'reserve'} ${kind.padEnd(9)} ${X === B ? 'X=B ' : 'X>B '} leg${a.p < cr ? '<' : '>='}cr  ${rel}`);
    }
  }
}
console.log(`sequences ${seen.size}, expansions ${expansions}`);
for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
