// Numerical tests for the case `leg < cr` that `StartLeg` (ChainCorrRegions.lean) wrongly
// excluded. Used by OmegaY/Official/Classification/Proofs/ChainCorrLegLeft*.lean and
// OmegaY/Official/Recon/JumpLawLowerLeft.lean.
//
// Usage: node startleg-left.cjs [--copies 1,2,3] [--legal MAXLEN,MAXVAL]
//                               [--random COUNT,MAXLEN,MAXVAL,SEED] [SAMPLE.json ...]
//
// For a node u of an output column X = x + w i (block i >= 1) whose origin o is not a gap
// copy and not an upper origin with leg < cr (the region nodes of keyLeRegion_of_chains):
// la = leg(o), pa = highest node of column la at or below row(o) in M, pe = highest node of
// column phi(la) at or below row(u) in R.
//  StartJumpGe  : la >= cr => jump(row u, row pe) <= jump(row o, row pa) (StartJump for legs >= cr).
//  LegRowMatchInner : la > cr and column la of M has a real node at row o => column la + w i of
//                 the output has a real node at row u.
//  LegLeftRow   : la < cr => row u = row o.
//  LegLeftPlain : la < cr => the origin is plain.
//  LegLeftSame  : la < cr => pe = pa (same column, same index).
//  LegLeftJump  : la < cr => jump(row u, row pe) <= jump(row o, row pa).
//  LegLeftRoot  : la < cr => col root_R(k, pe) <= col root_M(k, pa) for all k.
//  LowerPairsLeft : (Recon/JumpLawLowerLeft.lean) every node u = (X, k), k >= 1, of the lower
//                 part (origin not upper) whose output leg column is < cr: with lambda = row of the
//                 node below u, row u = bump(lambda, e), p = highest row of the leg column below
//                 row u: jump(lambda, p) = e.
//  (informational) whether the node below u has the row of the node below o: often not, so the
//                 jump law of the lower pairs does not follow from the rows of M(s) alone.
// Progress is printed to stderr every 1000 sequences; --budget SECONDS stops taking new sequences
// after that time (the summary covers the sequences processed). --status FILE writes the number of
// sequences taken and the current one to FILE; SIGTERM prints the summary so far (between sequences).
// --maxnodes N skips (and counts) the expansions whose output has more than N nodes.
// --timeout SEC checks each sequence in a worker thread and skips (and counts) a sequence whose check
// takes longer than SEC seconds (large entries can make a single expansion very large).
'use strict';
const fs = require('fs');
const O = require('./omegay-trace.cjs');
const {cmp, jump, show, degree, expandMountain} = O;
const {Worker, isMainThread, parentPort, workerData} = require('worker_threads');

const args = process.argv.slice(2);
const inputs = [];
let copies = [1, 2, 3], budget = Infinity, statusFile = null, maxNodes = Infinity, timeout = 0;
const t0 = Date.now();
for (let a = 0; a < args.length; a++) {
  if (args[a] === '--copies') copies = args[++a].split(',').map(Number);
  else if (args[a] === '--budget') budget = Number(args[++a]) * 1000;
  else if (args[a] === '--status') statusFile = args[++a];
  else if (args[a] === '--maxnodes') maxNodes = Number(args[++a]);
  else if (args[a] === '--timeout') timeout = Number(args[++a]) * 1000;
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
const rawParent = (M, u) => { const v = M[u.c][u.k + 1]; return v && v.pc >= 0 ? M[v.pc][v.pk] : null; };
const rootOf = (A, k, u) => { for (;;) { const p = rawParent(A, u); if (!p || jump(u.row, p.row) > k || p.c >= u.c) return u; u = p; } };
const isCut = v => v.prov && v.prov.kind === 'clean' && v.prov.ib;
const leg = u => u.k > 0 ? u.pc : u.c - 1;
const hAM = (A, l, row) => { let p = null; for (const q of A[l]) if (cmp(q.row, row) <= 0) p = q; return p; };

if (!isMainThread) ({copies, maxNodes} = workerData);
let stat = {}, ex = {};
const bump = (k, msg) => { stat[k] = (stat[k] || 0) + 1; if (msg && (ex[k] = ex[k] || []).length < 3) ex[k].push(msg); };
const test = (name, ok, msg) => bump(ok ? name + ' ok' : 'FAIL ' + name, ok ? null : msg);
const seen = new Set();
let expansions = 0;
const summary = () => {
  console.log(`sequences ${seen.size}, expansions ${expansions}`);
  for (const k of Object.keys(stat).sort()) { console.log(String(stat[k]).padStart(9), k); for (const m of ex[k] || []) console.log('            e.g.', m); }
};
// SIGTERM between two sequences prints the summary of the sequences done so far.
if (isMainThread) process.on('SIGTERM', () => { console.log(`stopped by SIGTERM after ${seen.size} sequences`); summary(); process.exit(0); });
const status = statusFile ? s => { try { fs.writeFileSync(statusFile, `${seen.size} ${s.join(',')}\n`); } catch (e) {} } : () => {};
function checkSeq(s) {
  for (const n of copies) {
    let r;
    try { r = expandMountain(s, n); } catch (err) { bump('expansion error', `(${s})[${n}]`); continue; }
    if (r.R.reduce((a, c) => a + c.length, 0) > maxNodes) { bump('  (skipped: output larger than --maxnodes)'); continue; }
    expansions++;
    const {M, R} = r, x0 = s.length - 1, t = M[x0][M[x0].length - 1], cr = t.pc, w = x0 - cr;
    let D = 0; for (const A of [M, R]) for (const col of A) for (const nd of col) D = Math.max(D, degree(nd.row));
    D += 2;
    for (let X = x0; X < R.length; X++) for (const v of R[X]) {
      if (v.i > 0 && v.k > 0 && v.prov.kind !== 'upper' && v.pc >= 0 && v.pc < cr) {
        const lam = R[X][v.k - 1].row;
        let e = -1; for (let f = 0; f <= D + 2; f++) if (O.eq(O.addPow(lam, f), v.row)) { e = f; break; }
        const p = O.highestBelow(R, v.pc, v.row);
        const ok = e >= 0 && p && jump(lam, p.row) === e;
        test('LowerPairsLeft', ok, `(${s})[${n}] X=${X} u=${show(v.row)} lambda=${show(lam)} e=${e} p=${p ? show(p.row) : '-'}`);
      }
      const i = v.i; if (i === 0 || isCut(v)) continue;
      const o = v.prov.src, la = leg(o);
      if (la >= cr) {
        // StartJumpGe (ChainCorrLegLeft.lean): StartJump for legs at or right of cr
        const pe = hAM(R, la + w * i, v.row), pa = hAM(M, la, o.row);
        test('StartJumpGe', jump(v.row, pe.row) <= jump(o.row, pa.row), `(${s})[${n}] X=${X} u=${show(v.row)} o=(${o.c},${o.k}) la=${la} cr=${cr}`);
        if (la > cr && M[la].some(q => q.k > 0 && cmp(q.row, o.row) === 0))
          test('LegRowMatchInner', R[la + w * i].some(q => q.k > 0 && cmp(q.row, v.row) === 0), `(${s})[${n}] X=${X} u=${show(v.row)} o=(${o.c},${o.k}) la=${la} cr=${cr}`);
        continue;
      }
      if (v.prov.kind === 'upper') continue;
      const where = `(${s})[${n}] X=${X} u=${show(v.row)} o=(${o.c},${o.k}) la=${la} cr=${cr}`;
      bump(`  kind ${v.prov.kind}`);
      test('LegLeftRow', cmp(v.row, o.row) === 0, where);
      test('LegLeftPlain', v.prov.kind === 'plain', where);
      const pe = hAM(R, la, v.row), pa = hAM(M, la, o.row);
      test('LegLeftSame', pe.c === pa.c && pe.k === pa.k, where);
      test('LegLeftJump', jump(v.row, pe.row) <= jump(o.row, pa.row), where);
      let okR = true;
      for (let k = 0; k <= D; k++) if (rootOf(R, k, pe).c > rootOf(M, k, pa).c) okR = false;
      test('LegLeftRoot', okR, where);
      if (v.k > 0 && o.k > 0) bump(cmp(R[X][v.k - 1].row, M[o.c][o.k - 1].row) === 0 ? '  (below: same row as below o)' : '  (below: row differs from below o)');
      test('  (column la has no node at row o)', !M[la].some(q => cmp(q.row, o.row) === 0), where);
    }
  }
}
// worker mode: check one sequence per message and return the counts
if (!isMainThread) {
  parentPort.on('message', seq => {
    stat = {}; ex = {}; expansions = 0;
    checkSeq(seq);
    parentPort.postMessage({stat, ex, expansions});
  });
} else {
  let worker = null;
  const merge = r => {
    expansions += r.expansions;
    for (const k of Object.keys(r.stat)) { stat[k] = (stat[k] || 0) + r.stat[k]; for (const m of r.ex[k] || []) if ((ex[k] = ex[k] || []).length < 3) ex[k].push(m); }
  };
  const runInWorker = seq => new Promise(resolve => {
    if (!worker) worker = new Worker(__filename, {workerData: {copies, maxNodes}});
    const w = worker;
    const timer = setTimeout(() => { w.removeAllListeners('message'); w.terminate(); worker = null; resolve(null); }, timeout);
    w.once('message', r => { clearTimeout(timer); w.removeAllListeners('error'); resolve(r); });
    w.once('error', e => { clearTimeout(timer); console.error('worker error', e); worker = null; resolve(null); });
    w.postMessage(seq);
  });
  (async () => {
    for (const s of inputs) {
      const key = s.join(',');
      if (seen.has(key) || s.length < 2 || s[s.length - 1] === 1) continue;
      if (Date.now() - t0 > budget) { console.log(`time budget reached after ${seen.size} sequences`); break; }
      seen.add(key);
      status(s);
      if (seen.size % 1000 === 0) process.stderr.write(`progress ${seen.size} sequences\n`);
      if (timeout > 0) {
        const r = await runInWorker(s);
        if (r) merge(r); else bump('  (skipped: sequence check longer than --timeout)', `(${s})`);
      } else {
        await new Promise(r => setImmediate(r));
        checkSeq(s);
      }
    }
    summary();
    if (worker) worker.terminate();
  })();
}
