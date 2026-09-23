// Large-value audit of the open statements (notes/05-large-value-audit.md).
//
// Runs the numerical harnesses of this directory on the input sets of the audit, in parallel
// child processes, and merges their counts into one table.
//
// Usage:
//   node large-value-audit.cjs gen   WORK                 generate the input sets and chunks
//   node large-value-audit.cjs run   WORK PAR [SETS] [HARNESSES] [TIMEOUT]
//                                                         run the harnesses on the chunks
//   node large-value-audit.cjs table WORK                 merge the outputs, print the table
//
// WORK is a scratch directory. With the environment variable LVA_SMALL set, `gen` makes small
// versions of A, C, D, E (for testing this script).
// SETS is a comma list of chunk prefixes (default: every chunk).
// HARNESSES is a comma list (default: all). A finished job is not run again.
//
// Input sets (every sequence starts with 1 and does not end with 1; n = 1, 2, 3):
//   A  all legal sequences of length <= 6 with entries <= 12
//   B  the 64 sequences of A that break LegBelowTop (samples/legbelowtop-bad64.json)
//   C  legal, length <= 7, entries <= 10: all of length <= 6, a seeded 1/8 of length 7
//   D  30000 seeded random legal sequences, length 2..8, entries <= 20
//   E  all legal sequences of length <= 5 with entries <= 20 and largest entry >= 13
//   F  all sequences of length 6 with entries <= 15 and largest entry >= 13, n = 1 only (run with
//      the harnesses chain-corr, copy-shape, startcopy-root-parts, step-inner-lookup in the audit)
//   K  counterexamples found by this audit and by the Lean refutations
//      (samples/known-counterexamples.json)
// Expansions whose output has more than 300 nodes ("big") are kept apart: for A, C, D, E a seeded
// sample of 200 of them with at most 1500 nodes forms the sets A+, C+, D+, E+ (chunks of 20). `run` processes the big
// chunks in a seeded random order, so a run stopped early still covers every set.
//
// Counts: a harness counts checks of its own kind (nodes, pairs of nodes, pairs of copies, ...),
// so the numbers of two harnesses are not comparable. A label that contains FAIL, ends in
// "fails" or "false" counts as a failure; informational labels are left out of the table.
'use strict';
const fs = require('fs'), path = require('path'), {spawn, spawnSync} = require('child_process');
const H = __dirname;
const O = require('./omegay-trace.cjs');

const mulberry = seed => () => { seed = (seed + 0x6D2B79F5) | 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const key = s => [s.length, Math.max(...s), ...s];
const cmpS = (a, b) => { const x = key(a), y = key(b); for (let i = 0; i < Math.max(x.length, y.length); i++) if (x[i] !== y[i]) return (x[i] ?? -1) - (y[i] ?? -1); return 0; };
const legal = (K, V, keep = () => true) => { const out = []; const rec = s => { if (s.length >= 2 && s[s.length - 1] !== 1 && keep(s)) out.push(s.slice()); if (s.length === K) return; for (let v = 1; v <= V; v++) { s.push(v); rec(s); s.pop(); } }; rec([1]); return out; };
const nodes = (s, n) => { let z = 0; for (const c of O.expandMountain(s, n).R) z += c.length; return z; };

function gen(W) {
  const sets = {};
  sets.A = legal(6, 12);
  sets.B = JSON.parse(fs.readFileSync(path.join(H, 'samples/legbelowtop-bad64.json'), 'utf8'));
  { const r = mulberry(7); sets.C = legal(7, 10).filter(s => s.length < 7 || r() < 1 / 8); }
  { const r = mulberry(20260923), seen = new Set(), L = []; while (L.length < 30000) { const len = 2 + Math.floor(r() * 7), s = [1]; while (s.length < len) s.push(1 + Math.floor(r() * 20)); if (s[s.length - 1] === 1 || seen.has(s.join())) continue; seen.add(s.join()); L.push(s); } sets.D = L; }
  sets.E = legal(5, 20, s => Math.max(...s) >= 13);
  sets.K = JSON.parse(fs.readFileSync(path.join(H, 'samples/known-counterexamples.json'), 'utf8'));
  const F = legal(6, 15, s => s.length === 6 && Math.max(...s) >= 13);
  if (process.env.LVA_SMALL) { // a small version of every set, for testing this script
    sets.A = legal(4, 12); sets.C = legal(4, 10); sets.D = sets.D.slice(0, 300); sets.E = legal(3, 20, s => Math.max(...s) >= 13);
  }
  const dir = path.join(W, 'chunks'); fs.mkdirSync(dir, {recursive: true});
  const put = (name, L) => fs.writeFileSync(path.join(dir, name + '.json'), JSON.stringify(L));
  if (process.env.LVA_SMALL) F.length = 300;
  F.sort((a, b) => Math.max(...a) - Math.max(...b) || cmpS(a, b));
  for (let j = 0; j * 3000 < F.length; j++) put(`F-n1.c${String(j).padStart(3, '0')}`, F.slice(j * 3000, (j + 1) * 3000));
  console.log('F', 1, 'small', F.length);
  for (const [tag, S] of Object.entries(sets)) {
    S.sort(cmpS);
    const prev = new Map(); // node count of s[n - 1]; once above 300 it is not computed again
    for (let n = 1; n <= 3; n++) {
      const small = [], big = [];
      for (const s of S) {
        let z = 301;
        if (tag === 'B' || tag === 'K') z = 0;
        else if (!(prev.get(s.join()) > 300)) { try { z = nodes(s, n); } catch (e) { z = 301; } }
        prev.set(s.join(), z);
        (z <= 300 ? small : big).push(s);
      }
      for (let j = 0; j * 3000 < small.length; j++) put(`${tag}-n${n}.c${String(j).padStart(3, '0')}`, small.slice(j * 3000, (j + 1) * 3000));
      if (big.length && tag !== 'B' && tag !== 'K') {
        // 200 big expansions with at most 1500 nodes, in a seeded random order; each size is
        // measured in a child process with a 5 s limit (some big expansions take hours)
        const r = mulberry(100 + n), idx = big.map((_, i) => i);
        for (let i = idx.length - 1; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [idx[i], idx[j]] = [idx[j], idx[i]]; }
        const P = [];
        for (const i of idx) {
          if (P.length >= 200) break;
          const p = spawnSync('node', ['-e', `const O=require(${JSON.stringify(path.join(H, 'omegay-trace.cjs'))});let z=0;for(const c of O.expandMountain([${big[i]}],${n}).R)z+=c.length;console.log(z)`], {timeout: 5000, encoding: 'utf8'});
          const z = +p.stdout;
          if (p.status === 0 && z > 0 && z <= 1500) P.push(big[i]);
        }
        P.sort((a, b) => a.length - b.length || Math.max(...a) - Math.max(...b));
        for (let j = 0; j * 20 < P.length; j++) put(`${tag}+-n${n}.c${String(j).padStart(3, '0')}`, P.slice(j * 20, (j + 1) * 20));
      }
      console.log(tag, n, 'small', small.length, 'big', big.length);
    }
  }
}

const ALL = ['chain-corr', 'check', 'classification-witness', 'copy-shape', 'cross-lex', 'cross-plain-pos', 'cross-upper',
  'cut-parts', 'cut-pred', 'cut-regions', 'jump-law-lower', 'jump-law-split', 'keylerest-regions', 'legbelowtop-parts',
  'legrowmatch-lower', 'parent-below-lower', 'recon-targets', 'reserve', 'start-root-parts', 'startcopy-root-parts',
  'startleg-jump', 'step-inner-clean', 'step-inner-lookup', 'step-inner-viaroot', 'step-inner',
  'cross-plain-pos-img', 'cross-upper-sim', 'leg-parts', 'lift-leg-right', 'lift-leg-right-items', 'lower-rows-parts', 'startleg-left'];
function argsOf(h, n, c) {
  if (h === 'reserve') return ['reserve.cjs', '--cand', 'leg', '--top-control', '--copies', n, c];
  if (h === 'legbelowtop-parts') return ['legbelowtop-parts.cjs', '--expand', n, c];
  if (h === 'cut-regions') return n === '3' ? ['cut-regions.cjs', c] : null; // it runs n = 1, 2, 3 itself
  if (h === 'lift-leg-right-items') return ['lift-leg-right.cjs', '--items', '--copies', n, c];
  return [h + '.cjs', '--copies', n, c];
}
function run(W, PAR, setsArg, hsArg, TO) {
  const dir = path.join(W, 'chunks'), OUT = path.join(W, 'out');
  const hs = hsArg && hsArg !== 'all' ? hsArg.split(',') : ALL;
  const pre = setsArg && setsArg !== 'all' ? setsArg.split(',') : null;
  const files = fs.readdirSync(dir).filter(f => !pre || pre.some(p => f.startsWith(p + '.c') || f.startsWith(p + '-n'))).sort();
  let jobs = [];
  for (const f of files) {
    const n = /-n(\d)\./.exec(f)[1], c = path.join(dir, f);
    for (const h of hs) { const a = argsOf(h, n, c); if (a) jobs.push({h, a, out: path.join(OUT, h, f.replace(/\.json$/, '.out'))}); }
  }
  jobs = jobs.filter(j => !fs.existsSync(j.out) && !fs.existsSync(j.out + '.err'));
  const r = mulberry(11), small = jobs.filter(j => !/\+-n/.test(j.out)), big = jobs.filter(j => /\+-n/.test(j.out));
  const byChunk = {}; for (const j of big) (byChunk[path.basename(j.out)] = byChunk[path.basename(j.out)] || []).push(j);
  const keys = Object.keys(byChunk); for (let a = keys.length - 1; a > 0; a--) { const b = Math.floor(r() * (a + 1)); [keys[a], keys[b]] = [keys[b], keys[a]]; }
  const todo = [...small, ...keys.flatMap(k => byChunk[k])];
  console.log('jobs', todo.length);
  let i = 0, running = 0, done = 0;
  const next = () => {
    while (running < PAR && i < todo.length) {
      const j = todo[i++]; running++;
      fs.mkdirSync(path.dirname(j.out), {recursive: true});
      const t0 = Date.now();
      const p = spawn('timeout', [String(TO), 'node', '--max-old-space-size=3072', ...j.a], {cwd: H});
      let buf = '';
      p.stdout.on('data', d => buf += d); p.stderr.on('data', d => buf += d);
      p.on('close', code => {
        const ok = code === 0 || (code === 1 && j.h === 'check');
        fs.writeFileSync(j.out + (ok ? '' : '.err'), buf + `\n#exit ${code} ${(Date.now() - t0) / 1000}s\n`);
        running--; done++;
        if (done % 100 === 0) console.log(new Date().toISOString(), done, '/', todo.length);
        if (i < todo.length) next(); else if (running === 0) console.log('all done');
      });
    }
  };
  next();
}

// ---------- merging ----------
const seqKey = m => { const g = /\(([\d,]+)\)(?:\[(\d+)\])?/.exec(m || ''); if (!g) return [1e9]; const s = g[1].split(',').map(Number); return [s.length, Math.max(...s), s.reduce((a, b) => a + b, 0), ...s, +(g[2] || 0)]; };
const lt = (a, b) => { for (let i = 0; i < Math.max(a.length, b.length); i++) { const x = a[i] ?? -1, y = b[i] ?? -1; if (x !== y) return x < y; } return false; };
const isFail = l => /\bFAIL\b/.test(l) || / fails$/.test(l) || / false$/.test(l) || /^expansion error/.test(l);
const norm = l => l.replace(/^FAIL /, '').replace(/ FAIL$/, '').replace(/ FAIL /, ' ').replace(/ (ok|fails|true|false)$/, '')
  .replace(/: ok$/, '').replace(/ ok:/, '').replace(/^ok /, '').replace(/ ok \(/, ' (').replace(/\s+/g, ' ').trim();
function merge(OUT) {
  const R = {}, errs = [];
  const add = (h, label, set, n, exList) => {
    const f = isFail(label), k = norm(label);
    const e = (((R[h] = R[h] || {})[k] = R[h][k] || {})[set] = R[h][k][set] || {ok: 0, fail: 0, ex: null});
    if (f) e.fail += n; else e.ok += n;
    for (const m of exList || []) if (!e.ex || lt(seqKey(m), seqKey(e.ex))) e.ex = m;
  };
  for (const h of fs.existsSync(OUT) ? fs.readdirSync(OUT) : []) for (const f of fs.readdirSync(path.join(OUT, h))) {
    const set = /^([A-Z]\+?)-n/.exec(f)[1], file = path.join(OUT, h, f);
    if (f.endsWith('.err')) { errs.push(`${h}/${f}`); continue; }
    const lines = fs.readFileSync(file, 'utf8').split('\n');
    let m, last = null, lastEx = [];
    const flush = () => { if (last) add(h, last.label, set, last.n, lastEx); last = null; lastEx = []; };
    for (const line of lines) {
      if (h === 'check') {
        if (line.startsWith('{"sequences"')) { const j = JSON.parse(line); add(h, 'BlockReconstruction', set, j.mountain); add(h, 'descent', set, j.lex); }
        else if ((m = /^\((.*)\)\[\d+\] (.*)$/.exec(line))) add(h, 'FAIL ' + (/canonical/.test(m[2]) ? 'BlockReconstruction' : /smaller/.test(m[2]) ? 'descent' : 'expansion error'), set, 1, [line]);
        continue;
      }
      if (h === 'reserve') {
        if ((m = /^leg\s+(\{.*\})$/.exec(line))) { const j = JSON.parse(m[1]); add(h, 'classification', set, j.expansions - j.failed); if (j.failed) add(h, 'FAIL classification', set, j.failed); }
        else if ((m = /^\s+e\.g\.\s+(.*)$/.exec(line))) add(h, 'FAIL classification', set, 0, [m[1]]);
        continue;
      }
      if (h === 'parent-below-lower') {
        if ((m = /^  (.+?): (\(.*)$/.exec(line))) add(h, m[1], set, 0, [m[2]]);
        else if ((m = /^([^:]+): (\d+)$/.exec(line)) && !line.startsWith('expansions')) add(h, m[1], set, +m[2]);
        continue;
      }
      if ((m = /^\s+e\.g\.\s+(.*)$/.exec(line))) { if (last) lastEx.push(m[1]); continue; }
      if ((m = /^\s*(\d+)\s+(\S.*)$/.exec(line))) { flush(); last = {label: m[2].trim(), n: +m[1]}; continue; }
      flush();
    }
    flush();
  }
  return {R, errs};
}

// [statement, status in Lean, harness, regex on the merged label]
const ROWS = [
  ['descent s[n] < s', 'check', /^descent$/], ['classification (classifiedB)', 'reserve', /^classification$/],
  ['BlockReconstruction', 'check', /^BlockReconstruction$/], ['WitnessHolds', 'classification-witness', /./],
  ['KeyLeRest', 'keylerest-regions', /./], ['RowLawHolds', 'recon-targets', /^RowLaw$/], ['JumpLawHolds', 'recon-targets', /^JumpLaw$/],
  ['ChainHolds', 'recon-targets', /^ChainHolds$/], ['ParentBelowHolds', 'recon-targets', /^ParentBelow$/],
  ['CrossChainHolds', 'recon-targets', /^CrossChain$/], ['LowerParentBelowHolds', 'recon-targets', /^LowerParentBelow$/],
  ['LowerPairsHolds', 'jump-law-split', /^lowerPairs$/], ['LowerRowsCopy', 'jump-law-lower', /^LowerRowsCopy/],
  ['LowerRowsBoundary', 'jump-law-lower', /^LowerRowsBoundary/], ['LowerLegGe', 'jump-law-lower', /^LowerLegGe/],
  ['NonCutOrder', 'parent-below-lower', /^NonCutOrder$/], ['CutBetween', 'parent-below-lower', /^CutBetween$/],
  ['CutOrder', 'parent-below-lower', /^CutOrder$/], ['CutLeg (Profile7)', 'parent-below-lower', /^CutLeg$/],
  ['Emitted (i >= 1)', 'parent-below-lower', /^Emitted i>=1$/], ['Lift', 'parent-below-lower', /^Lift$/],
  ['Boundary', 'parent-below-lower', /^Boundary$/], ['LegRight', 'parent-below-lower', /^LegRight$/],
  ['CrossLexHolds', 'cross-lex', /^(CrossLex|chain|value)/], ['CrossLexPos IsPlain', 'cross-plain-pos', /CrossLexPos plain/],
  ['CrossLexPos IsClean', 'cross-plain-pos', /CrossLexPos clean/], ['SeamLastPosHolds', 'cross-upper', /SeamLastPosHolds/],
  ['InnerHolds', 'cross-upper', /InnerHolds/], ['StepInner', 'chain-corr', /^StepInner/], ['StartLeg', 'chain-corr', /^StartLeg$/],
  ['StartJump', 'chain-corr', /^StartJump$/], ['StartCopy', 'chain-corr', /^StartCopy$/], ['StartRoot', 'chain-corr', /^StartRoot$/],
  ['MA', 'copy-shape', /^MA$/], ['MH', 'copy-shape', /^MH$/], ['CopyOrder', 'startcopy-root-parts', /^CopyOrder$/],
  ['CopyEmitted', 'startcopy-root-parts', /^CopyEmitted$/], ['CopyFirst', 'startcopy-root-parts', /^CopyFirst$/],
  ['CutTop', 'startcopy-root-parts', /^CutTop( \(used\))?$/], ['LegLookup', 'step-inner', /^LegLookup/],
  ['CleanNext', 'step-inner', /^CleanNext/], ['CleanLookup', 'step-inner', /^CleanLookup/], ['CleanParent', 'step-inner', /^CleanParent/],
  ['LegGapTop', 'step-inner-lookup', /^LegGapTop$/], ['LegOriginReach', 'step-inner-lookup', /^LegOriginReach$/],
  ['BoundaryStepLower', 'start-root-parts', /^BoundaryStepLower$/], ['BoundaryCutChain', 'start-root-parts', /^BoundaryCutChain$/],
  ['PaLookup', 'start-root-parts', /^PaLookup$/], ['X0Reach', 'start-root-parts', /^X0Reach$/], ['GapTop', 'start-root-parts', /^GapTop$/],
  ['CutRunLow', 'cut-parts', /^CutRunLow$/], ['CutRunHigh', 'cut-parts', /^CutRunHigh$/], ['CutOriginReach', 'cut-parts', /^CutOriginReach$/],
  ['CutJumpTop', 'cut-parts', /^CutJumpTop/], ['CutBump', 'cut-parts', /^CutBump$/], ['CutLegLookup', 'cut-parts', /^CutLegLookup/],
  ['LegBelowTop', 'startleg-jump', /^LegBelowTop$/],
];
function table(W) {
  const {R, errs} = merge(path.join(W, 'out'));
  const groups = {A: ['A', 'A+'], B: ['B'], C: ['C', 'C+'], D: ['D', 'D+'], E: ['E', 'E+'], F: ['F'], K: ['K']};
  console.log(`| statement | harness | ${Object.keys(groups).join(' | ')} | shortest counterexample |`);
  console.log(`|---|---|${Object.keys(groups).map(() => '---').join('|')}|---|`);
  for (const [name, h, re] of ROWS) {
    const Rh = R[h] || {}, keys = Object.keys(Rh).filter(k => re.test(k));
    let ex = null;
    const cells = Object.values(groups).map(sets => {
      let c = 0, f = 0;
      for (const k of keys) for (const s of sets) { const e = Rh[k][s]; if (!e) continue; c += e.ok + e.fail; f += e.fail; if (e.fail && e.ex && (!ex || lt(seqKey(e.ex), seqKey(ex)))) ex = e.ex; }
      return c ? `${c}${f ? ` / FAIL ${f}` : ''}` : '-';
    });
    console.log(`| ${name} | ${h} | ${cells.join(' | ')} | ${ex || ''} |`);
  }
  if (errs.length) console.log('\njobs that did not finish (timeout or error):', errs.length, errs.slice(0, 20).join(' '));
}

const [cmd, W, ...rest] = process.argv.slice(2);
if (cmd === 'gen') gen(W);
else if (cmd === 'run') run(W, +(rest[0] || 4), rest[1], rest[2], +(rest[3] || 3600));
else if (cmd === 'table') table(W);
else console.log('usage: node large-value-audit.cjs gen|run|table WORK ...');
