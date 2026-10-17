/* Independent math check for gen-c2.js (Chapter 2 — Graphs & Functions).
   For every generator, runs many random cases, re-derives the answer from the problem data
   (parsing the displayed formulas wherever possible) and classifies EVERY choice as right or wrong.
   A case passes only when exactly one choice is mathematically correct and it is the marked one.
   Usage: node verify-c2.js [runs]   */
global.window = undefined;
const K = require('./core.js');
require('./gen-c2.js');
const RUNS = +(process.argv[2] || 250);
const EPS = 1e-7;
const near = (a, b) => Math.abs(a - b) < EPS * Math.max(1, Math.abs(a), Math.abs(b));

/* ---------- HTML → expression text ---------- */
function tree(h) {
  const root = { tag: 'root', cls: '', ch: [] }, st = [root];
  const re = /<(\/?)([a-zA-Z0-9]+)([^>]*)>|([^<]+)/g; let mt;
  while ((mt = re.exec(h))) {
    if (mt[4] !== undefined) { st[st.length - 1].ch.push({ text: mt[4] }); continue; }
    const tag = mt[2].toLowerCase();
    if (mt[1]) { for (let i = st.length - 1; i > 0; i--) if (st[i].tag === tag) { st.length = i; break; } continue; }
    const cm = /class="([^"]*)"/.exec(mt[3] || ''); const node = { tag, cls: cm ? cm[1] : '', ch: [] };
    st[st.length - 1].ch.push(node);
    if (!/^(br|img|input|hr)$/.test(tag) && !/\/\s*$/.test(mt[3] || '')) st.push(node);
  }
  return root;
}
const hasCls = (n, c) => n.cls && n.cls.split(/\s+/).includes(c);
function decode(t) { return t.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&').replace(/ /g, ' ').replace(/−/g, '-').replace(/·/g, '*').replace(/÷/g, '/'); }
function ser(n) {
  if (n.text !== undefined) return decode(n.text);
  if (n.tag === 'span' && hasCls(n, 'fr')) { const nu = n.ch.find(c => hasCls(c, 'nu')), de = n.ch.find(c => hasCls(c, 'de')); return '((' + ser(nu) + ')/(' + ser(de) + '))'; }
  if (n.tag === 'span' && hasCls(n, 'rad')) { const rc = n.ch.find(c => hasCls(c, 'rc')), cube = n.ch.some(c => c.tag === 'sup' && hasCls(c, 'ri')); return (cube ? 'cbrt(' : 'sqrt(') + ser(rc) + ')'; }
  if (n.tag === 'sup') return hasCls(n, 'ri') ? '' : '^(' + n.ch.map(ser).join('') + ')';
  if (n.tag === 'sub') return '';
  return n.ch.map(ser).join('');
}
const plain = h => ser(tree(h)).replace(/\s+/g, ' ').trim();
function findAll(n, pred, out) { out = out || []; if (n.ch) n.ch.forEach(c => { if (pred(c)) out.push(c); else findAll(c, pred, out); }); return out; }
const mths = h => findAll(tree(h), c => c.tag === 'span' && hasCls(c, 'mth'));

/* ---------- expression parser (implicit multiplication, |abs|, ⟦floor⟧, sqrt, cbrt, π, f(...) calls) ---------- */
function tokenize(s) {
  const t = []; let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9.]/.test(c)) { let j = i; while (j < s.length && /[0-9.]/.test(s[j])) j++; t.push({ k: 'num', v: parseFloat(s.slice(i, j)) }); i = j; continue; }
    if (s.startsWith('sqrt', i) || s.startsWith('cbrt', i)) { t.push({ k: 'fn', v: s.slice(i, i + 4) }); i += 4; continue; }
    if (c === 'π') { t.push({ k: 'num', v: Math.PI }); i++; continue; }
    if (/[a-zA-Z]/.test(c)) { t.push({ k: 'id', v: c }); i++; continue; }
    if ('+-*/^()|⟦⟧'.includes(c)) { t.push({ k: c }); i++; continue; }
    throw new Error('bad char "' + c + '" in ' + s);
  }
  return t;
}
function parseExpr(s, funcs) {
  funcs = funcs || [];
  const T = tokenize(s); let p = 0, absD = 0;
  const pk = () => T[p];
  const eat = k => { if (!T[p] || T[p].k !== k) throw new Error('expected ' + k + ' in ' + s); return T[p++]; };
  const startsP = tk => tk && (tk.k === 'num' || tk.k === 'id' || tk.k === 'fn' || tk.k === '(' || tk.k === '⟦' || (tk.k === '|' && absD === 0));
  function expr() { let a = term(); while (pk() && (pk().k === '+' || pk().k === '-')) { const op = T[p++].k, b = term(), A = a; a = op === '+' ? e => A(e) + b(e) : e => A(e) - b(e); } return a; }
  function term() {
    let a = unary();
    for (;;) {
      const tk = pk();
      if (tk && (tk.k === '*' || tk.k === '/')) { p++; const b = unary(), A = a; a = tk.k === '*' ? e => A(e) * b(e) : e => { const d = b(e); return Math.abs(d) < 1e-9 ? NaN : A(e) / d; }; }
      else if (startsP(tk)) { const b = power(), A = a; a = e => A(e) * b(e); }
      else break;
    }
    return a;
  }
  function unary() { if (pk() && pk().k === '-') { p++; const a = unary(); return e => -a(e); } if (pk() && pk().k === '+') { p++; return unary(); } return power(); }
  function power() { const b = primary(); if (pk() && pk().k === '^') { p++; const ex = unary(); return e => Math.pow(b(e), ex(e)); } return b; }
  function primary() {
    const tk = T[p++];
    if (!tk) throw new Error('unexpected end in ' + s);
    if (tk.k === 'num') return () => tk.v;
    if (tk.k === 'fn') { eat('('); const a = expr(); eat(')'); return tk.v === 'sqrt' ? e => { const v = a(e); return v < -1e-9 ? NaN : Math.sqrt(Math.max(0, v)); } : e => Math.cbrt(a(e)); }
    if (tk.k === 'id') {
      if (funcs.includes(tk.v) && pk() && pk().k === '(') { p++; const a = expr(); eat(')'); return e => e[tk.v](a(e)); }
      return e => { if (!(tk.v in e)) throw new Error('unbound ' + tk.v + ' in ' + s); return e[tk.v]; };
    }
    if (tk.k === '(') { const a = expr(); eat(')'); return a; }
    if (tk.k === '|') { absD++; const a = expr(); eat('|'); absD--; return e => Math.abs(a(e)); }
    if (tk.k === '⟦') { const a = expr(); eat('⟧'); return e => Math.floor(a(e) + 1e-9); }
    throw new Error('unexpected ' + tk.k + ' in ' + s);
  }
  const f = expr(); if (p !== T.length) throw new Error('trailing tokens in ' + s); return f;
}
const val = s => parseExpr(s)({});
function splitTop(s, sep) { const out = []; let d = 0, cur = ''; for (const c of s) { if ('([{'.includes(c)) d++; if (')]}'.includes(c)) d--; if (c === sep && d === 0) { out.push(cur); cur = ''; } else cur += c; } out.push(cur); return out.map(z => z.trim()); }
function point(s) { s = s.trim(); const m = /^\((.*)\)$/.exec(s); if (!m) throw new Error('not a point: ' + s); const pr = splitTop(m[1], ','); if (pr.length !== 2) throw new Error('not a point: ' + s); return pr.map(val); }
const ptEq = (a, b) => near(a[0], b[0]) && near(a[1], b[1]);
function intervalSet(s) { // returns membership predicate
  const parts = s.split('∪').map(z => z.trim()).map(z => {
    const lc = z[0] === '[', rc = z[z.length - 1] === ']', ends = splitTop(z.slice(1, -1), ',');
    const ev = t => t === '-∞' ? -Infinity : t === '∞' ? Infinity : val(t);
    return { a: ev(ends[0]), b: ev(ends[1]), lc, rc };
  });
  const f = x => parts.some(q => (x > q.a || (q.lc && near(x, q.a))) && (x < q.b || (q.rc && near(x, q.b))) && !(near(x, q.a) && !q.lc) && !(near(x, q.b) && !q.rc));
  f.ends = parts.reduce((acc, q) => acc.concat([q.a, q.b].filter(isFinite)), []);
  return f;
}
function setOf(s) { const m = /^\{(.*)\}$/.exec(s.trim()); return splitTop(m[1], ',').map(val).sort((a, b) => a - b); }
const setEq = (a, b) => a.length === b.length && a.every((v, i) => near(v, b[i]));
function testPts(extra) { const t = [-1000, 1000]; for (let i = -14; i <= 14; i += 0.5) t.push(i); for (let i = -36; i <= 36; i++) t.push(i / 3, i / 4); (extra || []).forEach(e => { if (isFinite(e)) [0, 1e-5, -1e-5, 0.3, -0.3].forEach(d => t.push(e + d)); }); return t; }
const fin = v => typeof v === 'number' && isFinite(v);
// equation "L = R" → F(x, y) = L − R
function eqF(s) { const sides = s.split('='); if (sides.length !== 2) throw new Error('not one equation: ' + s); const L = parseExpr(sides[0]), Rr = parseExpr(sides[1]); return (x, y) => L({ x, y }) - Rr({ x, y }); }
function propEq(F, G) { // F = λG for a nonzero constant λ
  let lam = null;
  for (let i = 0; i < 12; i++) { const x = Math.random() * 10 - 5, y = Math.random() * 10 - 5, g = G(x, y), f = F(x, y); if (Math.abs(g) < 1e-6) continue; const l = f / g; if (lam === null) lam = l; else if (!near(l, lam)) return false; }
  return lam !== null && Math.abs(lam) > 1e-9;
}
function lineInfo(F) { const c = F(0, 0), A = F(1, 0) - c, B = F(0, 1) - c; return { A, B, C: -c, slope: Math.abs(B) < 1e-12 ? Infinity : -A / B, through: (x, y) => Math.abs(F(x, y)) < 1e-7 }; }
// functions defined in the question: "f(x) = ..." (also g, H, C, V, A, r)
function qFuncs(h) {
  const fs = {};
  mths(h).forEach(n => {
    if (hasCls(n, 'pw')) { fs.pw = pwParse(n); return; }
    const s = ser(n).trim(), m = /^([fgHC])\(x\) = (.*)$/.exec(s);
    if (m && !fs[m[1]]) { const ex = parseExpr(m[2]); fs[m[1]] = x => ex({ x }); }
  });
  return fs;
}
function pwParse(n) {
  const pe = findAll(n, c => hasCls(c, 'pe')).map(ser), pc = findAll(n, c => hasCls(c, 'pc')).map(ser);
  const pieces = pe.map((e, i) => {
    const ex = parseExpr(e), cs = pc[i].replace(/^if\s*/, '');
    const parts = cs.split(/(≤|≥|<|>)/).map(z => z.trim());
    const ces = []; for (let j = 0; j < parts.length; j += 2) ces.push(parts[j] === 'x' ? null : parseExpr(parts[j]));
    const ops = []; for (let j = 1; j < parts.length; j += 2) ops.push(parts[j]);
    const cond = x => ops.every((op, j) => { const a = ces[j] ? ces[j]({}) : x, b = ces[j + 1] ? ces[j + 1]({}) : x; return op === '<' ? a < b - 1e-12 : op === '>' ? a > b + 1e-12 : op === '≤' ? a <= b + 1e-12 : a >= b - 1e-12; });
    return { f: x => ex({ x }), cond };
  });
  const F = x => { const hits = pieces.filter(q => q.cond(x)); if (hits.length !== 1) return hits.length ? 'MULTI' : NaN; return hits[0].f(x); };
  F.pieces = pieces; return F;
}
function sameFn(f, g, xs) { return xs.every(x => { const a = f(x), b = g(x); if (!fin(a) && !fin(b)) return true; return fin(a) && fin(b) && near(a, b); }); }
const RX = () => [-3.7, -2.2, -1.1, -0.4, 0.6, 1.3, 2.9, 4.4, 5.6];
function numChoice(s) { const m = /^(?:About |After )?\$?(-?[0-9.,]+)/.exec(s.replace(/,/g, '')); if (!m) throw new Error('no number in ' + s); return parseFloat(m[1]); }

/* ---------- per-kind judges: return array of booleans (choice is mathematically correct) ---------- */
const PARF = { 'x': x => x, 'x^(2)': x => x * x, 'x^(3)': x => x * x * x, 'sqrt(x)': x => x < 0 ? NaN : Math.sqrt(x), 'cbrt(x)': Math.cbrt, '|x|': Math.abs };
const parentFn = key => ({ id: x => x, sq: x => x * x, cu: x => x * x * x, sr: x => x < 0 ? NaN : Math.sqrt(x), cr: Math.cbrt, ab: Math.abs })[key];
let ALLENDS = [];
function domainMatches(f, I) { return testPts(I.ends.concat(ALLENDS)).every(x => fin(f(x)) === I(x)); }
function rangeOf(f, lo, hi) { // numeric range on [lo, hi] sampled densely incl. huge values
  const xs = []; for (let i = 0; i <= 4000; i++) xs.push(lo + (hi - lo) * i / 4000); [1e3, 1e4, 1e5, 1e6, 1e9, 1e12].forEach(v => { xs.push(v, -v); }); for (let i = Math.ceil(lo); i <= hi; i += 0.5) xs.push(i);
  let mn = Infinity, mx = -Infinity; xs.forEach(x => { const v = f(x); if (fin(v)) { mn = Math.min(mn, v); mx = Math.max(mx, v); } });
  return { mn: mn < -200 ? -Infinity : mn, mx: mx > 200 ? Infinity : mx };
}
function rangeMatches(f, I, lo, hi) { const r = rangeOf(f, lo, hi); return testPts(I.ends.concat([r.mn, r.mx])).every(y => (y >= r.mn - 1e-9 && y <= r.mx + 1e-9) === I(y)); }
function DRparse(s) { const m = /^Domain (.*); range (.*)$/.exec(s); return [intervalSet(m[1]), intervalSet(m[2])]; }
function circCR(s) { const m = /^Center (\(.*\)), radius (.*)$/.exec(s); return { c: point(m[1]), r: val(m[2]) }; }
function genCoef(G) { const c = G(0, 0), A = (G(1, 0) + G(-1, 0) - 2 * c) / 2, D = (G(1, 0) - G(-1, 0)) / 2, E = (G(0, 1) - G(0, -1)) / 2; return { h: -D / (2 * A), k: -E / (2 * A), r2: (D * D + E * E) / (4 * A * A) - c / A }; }
function firstEq(h) { const m = mths(h).map(ser).find(s => /=/.test(s) && /y/.test(s)); return eqF(m); }
function rhsFn(s, funcs, v) { const i = s.indexOf('='); const ex = parseExpr(s.slice(i + 1), funcs); return ex; }

const J = {
  pt: (q, p, C) => C.map(s => ptEq(point(s), [p.x, p.y])),
  quad: (q, p, C) => { const qd = p.x > 0 && p.y > 0 ? 'I' : p.x < 0 && p.y > 0 ? 'II' : p.x < 0 && p.y < 0 ? 'III' : 'IV'; return C.map(s => s === 'Quadrant ' + qd); },
  dist: (q, p, C) => { const d = Math.hypot(p.x2 - p.x1, p.y2 - p.y1); return C.map(s => near(val(s), d) && simplestRad(s)); },
  mid: (q, p, C) => C.map(s => ptEq(point(s), [(p.x1 + p.x2) / 2, (p.y1 + p.y2) / 2])),
  endpt: (q, p, C) => C.map(s => { const b = point(s); return ptEq([(p.x1 + b[0]) / 2, (p.y1 + b[1]) / 2], [p.mx, p.my]); }),
  icpt: (q, p, C) => { const F = firstEqAny(q.q); return C.map(s => { const m = /^x-intercept (\(.*\)); y-intercept (\(.*\))$/.exec(s); const a = point(m[1]), b = point(m[2]); return a[1] === 0 && b[0] === 0 && Math.abs(F(a[0], 0)) < 1e-9 && Math.abs(F(0, b[1])) < 1e-9; }); },
  onGraph: (q, p, C) => { const F = firstEqAny(q.q); return C.map(s => { const a = point(s); return Math.abs(F(a[0], a[1])) < 1e-9; }); },
  rtri: (q, p, C) => {
    const V = {}; let mt; const re = /([ABC])\((-?\d+), (-?\d+)\)/g, t = plain(q.q); while ((mt = re.exec(t))) V[mt[1]] = [+mt[2], +mt[3]];
    const rightAt = Object.keys(V).filter(L => { const o = Object.keys(V).filter(z => z !== L), u = [V[o[0]][0] - V[L][0], V[o[0]][1] - V[L][1]], w = [V[o[1]][0] - V[L][0], V[o[1]][1] - V[L][1]]; return u[0] * w[0] + u[1] * w[1] === 0; });
    return C.map(s => /^Not/.test(s) ? rightAt.length === 0 : rightAt.length === 1 && s === 'A right triangle with the right angle at ' + rightAt[0]);
  },
  findy: (q, p, C) => { const r = p.d * p.d - (p.x2 - p.x1) * (p.x2 - p.x1), sol = r < 0 ? [] : r === 0 ? [p.y1] : [p.y1 - Math.sqrt(r), p.y1 + Math.sqrt(r)]; return C.map(s => { const vals = (s.match(/y = (-?[0-9.]+)/g) || []).map(z => +z.slice(4)).sort((a, b) => a - b); return setEq(vals, sol); }); },
  meet: (q, p, C) => C.map(s => { const m = /^Meet at (\(.*\)); each drives (.*) miles$/.exec(s); return ptEq(point(m[1]), [(p.x1 + p.x2) / 2, (p.y1 + p.y2) / 2]) && near(val(m[2]), Math.hypot(p.x2 - p.x1, p.y2 - p.y1) / 2); }),
  circEq: (q, p, C) => { const G = (x, y) => (x - p.h) ** 2 + (y - p.k) ** 2 - p.r2; return C.map(s => propEq(eqF(s), G)); },
  cr: (q, p, C) => { const G = genCoef(firstEq(q.q)); return C.map(s => { const z = circCR(s); return ptEq(z.c, [G.h, G.k]) && near(z.r * z.r, G.r2) && z.r > 0 && simplestRad(s.split('radius ')[1]); }); },
  crGen: (q, p, C) => J.cr(q, p, C),
  circPt: (q, p, C) => { const r2 = (p.px - p.h) ** 2 + (p.py - p.k) ** 2, G = (x, y) => (x - p.h) ** 2 + (y - p.k) ** 2 - r2; return C.map(s => propEq(eqF(s), G)); },
  circDiam: (q, p, C) => { const h = (p.x1 + p.x2) / 2, k = (p.y1 + p.y2) / 2, r2 = ((p.x2 - p.x1) ** 2 + (p.y2 - p.y1) ** 2) / 4, G = (x, y) => (x - h) ** 2 + (y - k) ** 2 - r2; return C.map(s => propEq(eqF(s), G)); },
  circType: (q, p, C) => {
    const G = genCoef(firstEq(q.q));
    return C.map(s => {
      let m;
      if ((m = /^A circle with center (\(.*\)) and radius (.*)$/.exec(s))) return G.r2 > 1e-9 && ptEq(point(m[1]), [G.h, G.k]) && near(val(m[2]) ** 2, G.r2);
      if ((m = /^The single point (\(.*\))$/.exec(s))) return Math.abs(G.r2) < 1e-9 && ptEq(point(m[1]), [G.h, G.k]);
      if (/^No graph/.test(s)) return G.r2 < -1e-9;
      throw new Error('circType choice ' + s);
    });
  },
  tower: (q, p, C) => { const d = Math.hypot(p.a - p.h, p.b - p.k); return C.map(s => { const m = /^About ([0-9.]+) mi; (inside|outside)/.exec(s); return m[1] === (Math.round(d * 10) / 10).toFixed(1) && (m[2] === 'inside') === (d <= p.R); }); },
  tangent: (q, p, C) => { // radius = shortest distance from the center to the axis (sampled)
    let best = Infinity; for (let t = -50; t <= 50; t += 0.01) best = Math.min(best, p.ax === 'x' ? Math.hypot(p.h - t, p.k) : Math.hypot(p.h, p.k - t));
    const r2 = Math.round(best * 100) ** 2 / 10000, G = (x, y) => (x - p.h) ** 2 + (y - p.k) ** 2 - r2; return C.map(s => propEq(eqF(s), G));
  },
  isFn: (q, p, C) => C.map(s => { const m = /^\{(.*)\}$/.exec(s); const prs = splitTop(m[1], ',').map(point); const isF = prs.every(a => prs.every(b => a[0] !== b[0] || a[1] === b[1])); return p.askNot ? !isF : isF; }),
  fval: (q, p, C) => { const F = qFuncs(q.q); const fn = F.f || F.pw; const v = fn(p.x); return C.map(s => near(val(s), v)); },
  drSet: (q, p, C) => { const m = /\{(\(.*\))\}/.exec(plain(q.q)); const prs = splitTop(m[1], ',').map(point); const S = [...new Set(prs.map(z => z[p.askD ? 0 : 1]))].sort((a, b) => a - b); return C.map(s => setEq(setOf(s), S)); },
  vlt: (q, p, C) => { const isF = ['par', 'abs', 'cub'].includes(p.t); return C.map(s => s === (isF ? 'Yes, because no vertical line crosses the graph more than once' : 'No, because some vertical line crosses the graph more than once')); },
  readF: (q, p, C) => { const v = p.lin ? p.mm * p.c + p.b : p.s * (p.c - p.h) ** 2 + p.kk; return C.map(s => /^-?[0-9.]+$/.test(s) && near(val(s), v)); },
  drGraph: (q, p, C) => {
    let D, Rg;
    if (p.t === 'par') { D = () => true; Rg = y => p.s > 0 ? y >= p.k - 1e-12 : y <= p.k + 1e-12; }
    if (p.t === 'sqrt') { D = x => x >= p.h - 1e-12; Rg = y => p.s > 0 ? y >= p.k - 1e-12 : y <= p.k + 1e-12; }
    if (p.t === 'seg') {
      const inc = (x, a, b, ca, cb) => (x > a + 1e-12 || (ca && near(x, a))) && (x < b - 1e-12 || (cb && near(x, b)));
      D = x => inc(x, p.x1, p.x2, p.c1, p.c2);
      Rg = y => p.y1 < p.y2 ? inc(y, p.y1, p.y2, p.c1, p.c2) : inc(y, p.y2, p.y1, p.c2, p.c1);
    }
    return C.map(s => { const [d, r] = DRparse(s); return testPts(d.ends.concat(r.ends, [p.x1, p.x2, p.y1, p.y2, p.h, p.k])).every(x => d(x) === D(x) && r(x) === Rg(x)); });
  },
  domF: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => domainMatches(f, intervalSet(s))); },
  fneg: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => { const g = parseExpr(s); return sameFn(x => g({ x }), x => f(-x), RX()); }); },
  rewrite: (q, p, C) => C.map(s => { const pr = splitTop(s, ';'), m1 = /^f\(x\) = (.*)$/.exec(pr[0]), m2 = /^f\((-?\d+)\) = (.*)$/.exec(pr[1]); const g = parseExpr(m1[1]); return sameFn(x => g({ x }), x => (p.c - p.a * x) / p.b, RX()) && +m2[1] === p.x && near(val(m2[2]), (p.c - p.a * p.x) / p.b); }),
  incdec: (q, p, C) => {
    const beh = i => p.ys[i + 1] > p.ys[i] ? 'i' : p.ys[i + 1] < p.ys[i] ? 'd' : 'c';
    const truth = x => { for (let i = 0; i < 4; i++) if (x > p.xs[i] + 1e-9 && x < p.xs[i + 1] - 1e-9) return beh(i) === p.ask; return false; };
    return C.map(s => { const I = intervalSet(s); return testPts(p.xs.concat(I.ends)).every(x => I(x) === truth(x)); });
  },
  taxi: (q, p, C) => C.map(s => { const pr = splitTop(s, ';'), m1 = /^C\(x\) = (.*)$/.exec(pr[0]), m2 = /^C\((\d+)\) = \$([0-9.,]+)$/.exec(pr[1]); const g = parseExpr(m1[1]); return sameFn(x => g({ x }), x => p.r * x + p.b, RX()) && +m2[1] === p.x && near(parseFloat(m2[2].replace(/,/g, '')), p.r * p.x + p.b); }),
  findk: (q, p, C) => C.map(s => { const k = val(s); return near(p.t * p.t + k * p.t + p.c, p.v); }),
  slope2: (q, p, C) => C.map(s => /^[-0-9()/ ]+$/.test(s) && near(val(s), (p.y2 - p.y1) / (p.x2 - p.x1))),
  hv: (q, p, C) => C.map(s => p.vert ? s === 'Undefined' : (s !== 'Undefined' && val(s) === 0)),
  xint: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => { const a = point(s); return a[1] === 0 && Math.abs(f(a[0])) < 1e-9; }); },
  lineSlope: (q, p, C) => C.map(s => near(val(s), p.m[0] / p.m[1])),
  stdSlope: (q, p, C) => { const L = lineInfo(firstEqAny(q.q)); return C.map(s => near(val(s), L.slope)); },
  roc: (q, p, C) => C.map(s => near(numChoice(s.replace(/ residents.*/, '')), (p.p2 - p.p1) / (p.t2 - p.t1))),
  lineFromGraph: (q, p, C) => C.map(s => { const g = rhsFn(s); return sameFn(x => g({ x }), x => p.m[0] / p.m[1] * x + p.b, RX()); }),
  icptF: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => { const m = /^x-intercept (\(.*\)); y-intercept (\(.*\))$/.exec(s); const a = point(m[1]), b = point(m[2]); return a[1] === 0 && b[0] === 0 && Math.abs(f(a[0])) < 1e-9 && near(f(0), b[1]); }); },
  plan: (q, p, C) => { const r = (p.c2 - p.c1) / (p.g2 - p.g1), fee = p.c1 - r * p.g1; return C.map(s => { const m = /^\$([0-9.]+) per GB; fixed fee \$([0-9.]+)$/.exec(s); return near(+m[1], r) && near(+m[2], fee); }); },
  findkSlope: (q, p, C) => C.map(s => { const k = val(s); return near((p.y2 - p.y1) / (p.x2 - k), p.m[0] / p.m[1]); }),
  table: (q, p, C) => C.map(s => { const g = rhsFn(s); return p.xs.every((x, i) => near(g({ x }), p.ys[i])); }),
  deprec: (q, p, C) => C.map(s => near(numChoice(s), (p.V - p.X) / p.d)),
  lineThru: (q, p, C) => C.map(s => { const L = lineInfo(eqF(s)); return p.pts.every(z => L.through(z[0], z[1])) && (!p.m || near(L.slope, p.m[0] / p.m[1])) && (p.pts.length > 1 || p.m); }),
  ppSlope: (q, p, C) => { const m0 = p.m[0] / p.m[1]; return C.map(s => p.perp ? near(val(s) * m0, -1) : near(val(s), m0)); },
  hvLine: (q, p, C) => C.map(s => { const L = lineInfo(eqF(s)); return L.through(p.a, p.b) && (p.vert ? Math.abs(L.B) < 1e-12 : Math.abs(L.A) < 1e-12); }),
  parPerp: (q, p, C) => { const m0 = -p.A / p.B; return C.map(s => { const L = lineInfo(eqF(s)); return L.through(p.px, p.py) && (p.perp ? near(L.slope * m0, -1) : near(L.slope, m0)); }); },
  stdForm: (q, p, C) => { const G = (x, y) => y - (p.p / p.q) * x - p.r; return C.map(s => { const F = eqF(s), L = lineInfo(F); return propEq(F, G) && L.A > 0 && [L.A, L.B, L.C].every(z => Math.abs(z - Math.round(z)) < 1e-9); }); },
  model: (q, p, C) => { const r = (p.v2 - p.v1) / (p.t2 - p.t1); return C.map(s => near(numChoice(s), p.v1 + r * (p.t3 - p.t1))); },
  kLines: (q, p, C) => { const m2 = p.b / p.d; return C.map(s => { const m1 = -val(s) / p.a; return p.perp ? near(m1 * m2, -1) : near(m1, m2); }); },
  perpBis: (q, p, C) => C.map(s => { const g = rhsFn(s); return [-3, 0, 2.5, 7].every(x => { const y = g({ x }); return near(Math.hypot(x - p.x1, y - p.y1), Math.hypot(x - p.x2, y - p.y2)); }); }),
  parDR: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => { const I = intervalSet(s); return p.askD ? domainMatches(f, I) : rangeMatches(f, I, -60, 60); }); },
  pwEval: (q, p, C) => { const f = qFuncs(q.q).pw; return C.map(s => near(val(s), f(p.x))); },
  gint: (q, p, C) => C.map(s => near(val(s), Math.floor(p.v + 1e-12))),
  parId: (q, p, C) => { const t = parentFn(p.key); return C.map(s => { const g = rhsFn(s); return sameFn(x => g({ x }), t, RX()); }); },
  pwGraphRead: (q, p, C) => { const T = x => x < p.c ? p.yL + p.m1 * (x - p.c) : x > p.c ? p.yR + p.m2 * (x - p.c) : (p.closedL ? p.yL : p.yR); return C.map(s => s !== 'Undefined' && near(val(s), T(p.x))); },
  pwDots: (q, p, C) => {
    const f = qFuncs(q.q).pw, pcs = f.pieces, c = p.c, dots = pcs.map(pc => ({ y: pc.f(c), closed: pc.cond(c) }));
    return C.map(s => { const m = /^(Closed|Open) dot at (\(.*\)); (closed|open) dot at (\(.*\))$/.exec(s); const d1 = { pt: point(m[2]), closed: m[1] === 'Closed' }, d2 = { pt: point(m[4]), closed: m[3] === 'closed' }; return [d1, d2].every(d => { const tr = dots.find(z => near(z.y, d.pt[1])); return d.pt[0] === c && tr && tr.closed === d.closed; }); });
  },
  pwSum: (q, p, C) => { const f = qFuncs(q.q).pw; return C.map(s => near(val(s), f(p.u) + f(p.w))); },
  parking: (q, p, C) => { const hrs = Math.ceil(p.h + p.mn / 60), cost = p.p + p.q * (hrs - 1); return C.map(s => near(numChoice(s), cost)); },
  pwFromGraph: (q, p, C) => { const T = x => x < p.c ? p.m1 * x + p.b1 : x > p.c ? p.m2 * x + p.b2 : (p.closedL ? p.m1 * x + p.b1 : p.m2 * x + p.b2); return C.map((s, ci) => { const f = pwParse(mths(q.ch[ci])[0]); return [-5, -2.5, p.c - 1, p.c - 0.01, p.c, p.c + 0.01, p.c + 1, 3.5, 6].every(x => near(f(x), T(x))); }); },
  contK: (q, p, C) => C.map(s => { const k = val(s); return near(p.c * p.c + k, p.a * p.c + p.b); }),
  shiftDesc: (q, p, C) => { const g = rhsFn(mths(q.q).map(ser)[0]), par = parentFn(p.key); return C.map(s => { const m = /^Shift (right|left) (\d+) and (up|down) (\d+)$/.exec(s), dx = (m[1] === 'right' ? 1 : -1) * m[2], dy = (m[3] === 'up' ? 1 : -1) * m[4]; return sameFn(x => g({ x }), x => par(x - dx) + dy, RX().concat([7.3, 9.1, 11.5])); }); },
  vertex: (q, p, C) => {
    const g = rhsFn(mths(q.q).map(ser)[0]), xs = []; for (let x = -20; x <= 20; x++) xs.push(x);
    const ys = xs.map(x => g({ x })), up = ys[0] > ys[20], i = ys.indexOf(up ? Math.min(...ys) : Math.max(...ys));
    return C.map(s => ptEq(point(s), [xs[i], ys[i]]));
  },
  evenOdd: (q, p, C) => { const f = qFuncs(q.q).f, X = [0.5, 1.3, 2, 2.7, 3.1, 4.6]; const ev = X.every(x => near(f(-x), f(x))), od = X.every(x => near(f(-x), -f(x))); const lab = ev && od ? 'Both even and odd' : ev ? 'Even' : od ? 'Odd' : 'Neither'; return C.map(s => s === lab); },
  tfGraph: (q, p, C) => { const par = parentFn(p.key), T = x => p.a * par(x - p.h) + p.kk; return C.map(s => { const g = rhsFn(s); return sameFn(x => g({ x }), T, RX().concat([6.2, 7.7, -6.6])); }); },
  domRange: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => { const [d, r] = DRparse(s); return domainMatches(f, d) && rangeMatches(f, r, -60, 60); }); },
  tfDesc: (q, p, C) => { const par = parentFn(p.key), T = x => p.s * par(x - p.h) + p.kk; return C.map(s => { const g = rhsFn(s); return sameFn(x => g({ x }), T, RX().concat([6.2, 7.7, -6.6])); }); },
  ptImage: (q, p, C) => {
    const src = mths(q.q).map(ser).filter(s => /^y = /.test(s))[1], tests = [1.7, -2.3].map(r => (x => p.b + r * (x - p.a)));
    const gs = tests.map(F => { const ex = parseExpr(src.slice(4), ['f']); return x => ex({ x, f: F }); });
    return C.map(s => { const a = point(s); return gs.every(g => near(g(a[0]), a[1])); });
  },
  absZeros: (q, p, C) => {
    const ex = rhsFn(mths(q.q).map(ser).find(s => /^y = /.test(s))), g = x => ex({ x });
    const Z = []; for (let x = -40; x <= 40; x += 0.5) if (Math.abs(g(x)) < 1e-9) Z.push(x);
    return C.map(s => /^There are no/.test(s) ? Z.length === 0 : setEq((s.match(/x = (-?[0-9.]+)/g) || []).map(z => +z.slice(4)).sort((a, b) => a - b), Z));
  },
  gFromF: (q, p, C) => {
    const poly = (xs, ys) => x => { if (x < xs[0] - 1e-9 || x > xs[3] + 1e-9) return NaN; for (let i = 0; i < 3; i++) if (x <= xs[i + 1] + 1e-9) return ys[i] + (ys[i + 1] - ys[i]) * (x - xs[i]) / (xs[i + 1] - xs[i]); return NaN; };
    const F = poly(p.xs, p.ys), G = poly(p.gx, p.gy), xs = []; for (let x = -9; x <= 9; x += 0.25) xs.push(x);
    return C.map(s => { const ex = rhsFn(s, ['f']); return sameFn(x => ex({ x, f: F }), G, xs); });
  },
  stretchA: (q, p, C) => C.map(s => { const g = rhsFn(s); return p.pts.every(z => near(g({ x: z[0] }), z[1])); }),
  opVal: (q, p, C) => { const F = qFuncs(q.q), a = F.f(p.x), b = F.g(p.x), v = { '+': a + b, '−': a - b, '·': a * b, '/': a / b }[p.op]; return C.map(s => near(val(s), v)); },
  compVal: (q, p, C) => { const F = qFuncs(q.q); return C.map(s => near(val(s), F.f(F.g(p.x)))); },
  domQ: (q, p, C) => { const F = qFuncs(q.q), h = x => { const d = F.g(x); return Math.abs(d) < 1e-9 ? NaN : F.f(x) / d; }; return C.map(s => domainMatches(h, intervalSet(s))); },
  compF: (q, p, C) => { const F = qFuncs(q.q), T = p.fog ? x => F.f(F.g(x)) : x => F.g(F.f(x)); return C.map(s => { const g = parseExpr(s); return sameFn(x => g({ x }), T, RX()); }); },
  diffQ: (q, p, C) => { const f = qFuncs(q.q).f; return C.map(s => { const g = parseExpr(s); return [[1.3, 0.7], [-2.1, 1.9], [0.4, -1.2], [3.3, 2.2]].every(([x, h]) => near(g({ x, h }), (f(x + h) - f(x)) / h)); }); },
  diffFG: (q, p, C) => { const F = qFuncs(q.q); return C.map(s => { const g = parseExpr(s); return sameFn(x => g({ x }), x => F.f(x) - F.g(x), RX()); }); },
  tableComp: (q, p, C) => { const f = x => p.fv[p.S.indexOf(x)], g = x => p.gv[p.S.indexOf(x)]; return C.map(s => near(val(s), f(g(p.a)))); },
  domComp: (q, p, C) => { const F = qFuncs(q.q), h = x => { const u = F.g(x); return fin(u) ? F.f(u) : NaN; }; return C.map(s => domainMatches(h, intervalSet(s))); },
  decomp: (q, p, C) => { const Hs = mths(q.q).map(ser).find(s => /^H\(x\) = /.test(s)), H = parseExpr(Hs.slice(7)); return C.map(s => { const pr = splitTop(s, ','), f = parseExpr(pr[0].replace(/^f\(x\) = /, '')), g = parseExpr(pr[1].replace(/^g\(x\) = /, '')); return RX().every(x => { const hv = H({ x }), cv = f({ x: g({ x }) }); return (!fin(hv) && !fin(cv)) || near(hv, cv); }) && RX().some(x => fin(H({ x }))); }); },
  coupon: (q, p, C) => { const c = x => x - p.D, pp = x => x * (100 - p.pc) / 100, v = p.first ? pp(c(p.Xp)) : c(pp(p.Xp)); return C.map(s => near(numChoice(s), v)); },
  ripple: (q, p, C) => C.map(s => { const g = parseExpr(s.split('=')[1]); return [0.5, 1.7, 3].every(t => near(g({ t }), Math.PI * (p.c * t) ** 2)); })
};
function firstEqAny(h) { const s = mths(h).map(ser).find(z => /=/.test(z) && /[xy]/.test(z)); if (/^y = /.test(s)) { const ex = parseExpr(s.slice(4)); return (x, y) => y - ex({ x }); } return eqF(s); }
function simplestRad(s) { const re = /sqrt\((\d+)\)/g; let m; while ((m = re.exec(s))) { const N = +m[1]; for (let f = 2; f * f <= N; f++) if (N % (f * f) === 0) return false; if (N < 2) return false; } return true; }

/* ---------- run ---------- */
let fails = 0, cases = 0, whyHyphen = 0; const counts = [];
for (const id of Object.keys(K.lessons)) {
  if (/^R/.test(id)) continue;
  K.lessons[id].levels.forEach((gens, lv) => gens.forEach((g, gi) => {
    let ok = 0, kind = '?';
    for (let r = 0; r < RUNS; r++) {
      K._gd = []; const q = g(); kind = q.p && q.p.kind;
      if (!q.p || !J[q.p.kind]) { console.log('NO JUDGE', id, lv + 1, gi, kind); fails++; break; }
      let res;
      ALLENDS = []; q.ch.map(plain).forEach(s => { try { if (/[\[(].*,.*[\])]/.test(s) && !/[a-z]/i.test(s.replace(/sqrt/g, ''))) ALLENDS = ALLENDS.concat(intervalSet(s.replace(/^.*?(?=[\[(])/, '')).ends); } catch (e) { } });
      try { res = J[q.p.kind](q, q.p, q.ch.map(plain)); }
      catch (e) { console.log('JUDGE ERROR', id, 'L' + (lv + 1), 'g' + gi, kind, e.message, '::', K.strip(q.q).slice(0, 140), '|', q.ch.map(plain).join(' || ')); fails++; break; }
      cases++;
      const nRight = res.filter(Boolean).length;
      if (nRight !== 1 || !res[q.a]) { console.log('FAIL', id, 'L' + (lv + 1), 'g' + gi, kind, 'correct flags', res.join(','), 'marked', q.a, '::', K.strip(q.q).slice(0, 160), '|', q.ch.map(plain).join(' || ')); fails++; if (fails > 40) process.exit(1); continue; }
      if (/[^a-z]-\d/i.test(' ' + K.strip(q.why).replace(/\d-\d/g, ''))) whyHyphen++;
      ok++;
    }
    counts.push(id + ' L' + (lv + 1) + ' g' + gi + ' [' + kind + '] ' + ok + '/' + RUNS);
  }));
}
console.log(counts.join('\n'));
console.log('generators checked:', counts.length, '| cases:', cases, '| hyphen-minus in explanations:', whyHyphen, '| FAILURES:', fails);
process.exit(fails ? 1 : 0);
