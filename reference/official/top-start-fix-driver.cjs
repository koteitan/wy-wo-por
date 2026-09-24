// Sequential driver for top-start-fix.cjs: runs ONE harness process at a time with --state and
// --trace, kills it when no new input has started for STALL seconds (an expansion of the JS
// reference that does not finish; node cannot be stopped by SIGTERM inside a loop), records that
// input as excluded in the state file, and resumes. Stops after DEADLINE seconds (the state file
// keeps the counts; a later call continues).
//
// Usage: node top-start-fix-driver.cjs STATE OUT STALL DEADLINE -- HARNESS-ARGS...
'use strict';
const fs = require('fs'), path = require('path'), {spawn} = require('child_process');
const [stateFile, outFile, stallS, deadlineS] = process.argv.slice(2, 6);
const hargs = process.argv.slice(process.argv.indexOf('--') + 1);
const t0 = Date.now(), stall = Number(stallS) * 1000, deadline = Number(deadlineS) * 1000;
const harness = path.join(__dirname, 'top-start-fix.cjs');

const runOnce = () => new Promise(resolve => {
  const out = fs.openSync(outFile, 'w');
  const child = spawn('node', ['--max-old-space-size=2048', harness, ...hargs, '--state', stateFile, '--trace'],
    {stdio: ['ignore', out, out]});
  let lastSize = -1, lastChange = Date.now(), why = null;
  const timer = setInterval(() => {
    const size = fs.statSync(outFile).size;
    if (size !== lastSize) { lastSize = size; lastChange = Date.now(); }
    if (Date.now() - lastChange > stall) { why = 'stall'; child.kill('SIGKILL'); }
    else if (Date.now() - t0 > deadline) { why = 'deadline'; child.kill('SIGKILL'); }
  }, 1000);
  child.on('exit', code => { clearInterval(timer); fs.closeSync(out); resolve({code, why}); });
});

(async () => {
  for (;;) {
    const {code, why} = await runOnce();
    if (!why) { console.log(`finished (exit ${code})`); break; }
    if (why === 'deadline') { console.log('deadline reached; state saved'); break; }
    // stalled: exclude the input that was being expanded
    const lines = fs.readFileSync(outFile, 'utf8').split('\n').filter(l => l.startsWith('trace #'));
    const k = Number(lines[lines.length - 1].match(/^trace #(\d+)/)[1]);
    const st = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
    st.excluded = [...(st.excluded || []), k];
    fs.writeFileSync(stateFile, JSON.stringify(st));
    console.log(`stalled at input #${k} (${lines[lines.length - 1]}); excluded, resuming`);
  }
})();
