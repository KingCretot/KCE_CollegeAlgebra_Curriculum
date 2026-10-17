/* Structural test for College Algebra practice generators.
   Usage: node test-structure.js gen-c5.js [runs]  */
global.window = undefined;
const K = require('./core.js');
const file = process.argv[2], RUNS = +(process.argv[3] || 300);
require('./' + file);
let seed = 12345; K.setRng(() => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; });
let bad = 0; const pos = [0, 0, 0, 0];
const ids = Object.keys(K.lessons);
for (const id of ids) {
  const L = K.lessons[id];
  if (!L.title || !L.std || L.levels.length !== 3) { console.log('BAD LESSON DEF', id); bad++; }
  L.levels.forEach((gens, lv) => {
    if (gens.length < 2 && !/^R/.test(id) ) { console.log('FEWER THAN 2 GENERATORS', id, 'level', lv + 1); bad++; }
    gens.forEach((g, gi) => {
      for (let r = 0; r < RUNS; r++) {
        let q;
        try { K._gd = []; q = g(); } catch (e) { console.log('THROWS', id, lv + 1, gi, e.message); bad++; break; }
        const txt = [q.q, q.graph, q.why].concat(q.ch).join(' ');
        const keys = q.ch.map(K.strip);
        const errs = [];
        if (q.ch.length !== 4) errs.push('choices ' + q.ch.length);
        if (new Set(keys).size !== keys.length) errs.push('duplicate choices ' + keys.join(' | '));
        if (!(q.a >= 0 && q.a < q.ch.length)) errs.push('answer index');
        if (/NaN|undefined|Infinity|\[object|null/.test(txt)) errs.push('NaN/undefined in text');
        if (keys.some(k => k === '')) errs.push('empty choice');
        if (!q.why || K.strip(q.why).length < 10) errs.push('missing explanation');
        if (/-\d/.test(K.strip(q.q + ' ' + q.ch.join(' ')).replace(/\d-\d|[a-z]-[a-z]/gi, ''))) errs.push('hyphen minus: ' + K.strip(q.q).slice(0, 80));
        if (errs.length) { console.log('FAIL', id, 'L' + (lv + 1), 'gen' + gi, errs.join('; '), '::', K.strip(q.q).slice(0, 120)); bad++; break; }
        pos[q.a]++;
      }
    });
  });
}
console.log(file, 'lessons', ids.join(','), 'answer positions A-D', pos.join('/'), 'problems', bad);
process.exit(bad ? 1 : 0);
