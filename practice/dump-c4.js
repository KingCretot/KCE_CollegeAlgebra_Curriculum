/* Dumps generated Chapter 4 questions (with raw parameters) as JSON for verify-c4.py */
global.window = undefined;
const K = require('./core.js');
require('./gen-c4.js');
const RUNS = +(process.argv[2] || 250), out = [];
for (const id of Object.keys(K.lessons)) {
  if (/^R/.test(id)) continue;
  K.lessons[id].levels.forEach((gens, lv) => gens.forEach((g, gi) => {
    for (let r = 0; r < RUNS; r++) { K._gd = []; const q = g(); out.push({ id, lv: lv + 1, gi, q: q.q, ch: q.ch, a: q.a, why: q.why, graph: q.graph ? 1 : 0, p: q.p }); }
  }));
}
process.stdout.write(JSON.stringify(out));
