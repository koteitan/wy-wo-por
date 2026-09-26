// Lists the inputs with the property Q of notes/03-official-rule.md section 5.
//
// Q(s): the finite band F of the root row lies strictly below the top row tau of the
// last column; with rho = the top of the root column in F, the lift h(kappa) - h(rho)
// in F is positive; and some column x strictly between the root column and the last
// column ascends in the reference row row(rho) - 1 (its in-row ancestors reach the root
// column) while its node at row(rho) (if any) does not reach the root column by
// in-row ancestors of row(rho).
//
// Usage: node ascension-gap.cjs SAMPLE.json ...
'use strict';
const fs = require('fs');
const O = require('./omegay.cjs');

function reaches(M, a, cr) { while (a && a.c > cr) a = O.rowParent(M, a); return !!a && a.c === cr; }

function Q(s) {
  const M = O.mountain(s), x0 = s.length - 1, t = M[x0][M[x0].length - 1];
  if (t.pc < 0) return false;
  const cr = t.pc, R = M[cr][t.pk].row;
  const inF = row => { for (let k = 1; k < Math.max(row.length, R.length); k++) if ((row[k] || 0) !== (R[k] || 0)) return false; return true; };
  if (inF(t.row)) return false;
  const topF = c => { let b = null; for (const n of M[c]) if (inF(n.row)) b = n; return b; };
  const kap = topF(x0), rho = topF(cr);
  if (!kap || !rho || (kap.row[0] || 0) <= (rho.row[0] || 0) || !(rho.row[0] > 0)) return false;
  const ref = O.norm([rho.row[0] - 1, ...rho.row.slice(1)]);
  for (let x = cr + 1; x < x0; x++) {
    if (!reaches(M, O.nodeAt(M, x, ref), cr)) continue;
    const b = O.nodeAt(M, x, rho.row);
    if (b && !reaches(M, b, cr)) return true;
  }
  return false;
}

const hits = [];
let total = 0;
for (const f of process.argv.slice(2)) for (const s of JSON.parse(fs.readFileSync(f, 'utf8'))) {
  if (s[s.length - 1] === 1) continue;
  total++;
  if (Q(s)) hits.push('(' + s.join(',') + ')');
}
console.log(JSON.stringify({sequences: total, Q: hits.length}));
for (const h of hits) console.log(h);
