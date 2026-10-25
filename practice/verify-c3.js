/* Independent math check for gen-c3.js (Chapter 3).
   Every choice is parsed back from its displayed text and judged by an independent computation
   (expression parsing + numeric evaluation, long division, brute-force search, root finding).
   A question passes only if exactly one choice is judged correct and it is the marked one.
   Usage: node verify-c3.js [runs per generator] */
global.window = undefined;
const K = require('./core.js');
require('./gen-c3.js');
const RUNS = +(process.argv[2] || 250);

/* ---------- expression parser over a ring (numbers or polynomials) ---------- */
function tokenize(s) {
  s = s.replace(/−/g, '-').replace(/·/g, '*').replace(/÷/g, '/').replace(/(\d),(\d{3})/g, '$1$2').replace(/\s+/g, '');
  const t = []; let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\d/.test(c) || (c === '.' && /\d/.test(s[i + 1]))) { let j = i; while (j < s.length && /[\d.]/.test(s[j])) j++; t.push({ k: 'n', v: parseFloat(s.slice(i, j)) }); i = j; continue; }
    if (/[a-zA-Z]/.test(c)) { t.push({ k: 'v', v: c }); i++; continue; }
    if ('+-*/^()√'.includes(c)) { t.push({ k: c }); i++; continue; }
    throw new Error('bad char ' + c + ' in ' + s);
  }
  return t;
}
function parse(str, ring) {
  const t = tokenize(str); let p = 0;
  const peek = () => t[p], eat = (k) => { if (!t[p] || t[p].k !== k) throw new Error('expected ' + k + ' in ' + str); p++; };
  const startsAtom = (x) => x && (x.k === 'n' || x.k === 'v' || x.k === '(' || x.k === '√');
  function expr() {
    let v;
    if (peek() && (peek().k === '+' || peek().k === '-')) { const s = peek().k; p++; v = term(); if (s === '-') v = ring.neg(v); } else v = term();
    while (peek() && (peek().k === '+' || peek().k === '-')) { const s = peek().k; p++; const w = term(); v = s === '+' ? ring.add(v, w) : ring.sub(v, w); }
    return v;
  }
  function term() {
    let v = unary();
    for (;;) {
      const x = peek();
      if (x && x.k === '*') { p++; v = ring.mul(v, unary()); } else if (x && x.k === '/') { p++; v = ring.div(v, unary()); } else if (startsAtom(x)) v = ring.mul(v, power()); else break;
    }
    return v;
  }
  function unary() { if (peek() && peek().k === '-') { p++; return ring.neg(unary()); } return power(); }
  function power() {
    const b = atom();
    if (peek() && peek().k === '^') { p++; let neg = false; if (peek().k === '-') { neg = true; p++; } let e; if (peek().k === '(') { p++; e = parse_num_expr(); eat(')'); } else { e = peek().v; p++; } return ring.pow(b, neg ? -e : e); }
    return b;
  }
  function parse_num_expr() { const x = peek(); p++; return x.v; }
  function atom() {
    const x = peek(); if (!x) throw new Error('unexpected end in ' + str);
    if (x.k === 'n') { p++; return ring.num(x.v); }
    if (x.k === 'v') { p++; return ring.v(x.v); }
    if (x.k === '(') { p++; const v = expr(); eat(')'); return v; }
    if (x.k === '√') { p++; return ring.sqrt(atom()); }
    throw new Error('unexpected ' + x.k + ' in ' + str);
  }
  const v = expr(); if (p !== t.length) throw new Error('trailing tokens in ' + str); return v;
}
const NUM = (vars) => ({ num: (v) => v, v: (n) => { if (!(n in vars)) throw new Error('unknown var ' + n); return vars[n]; }, add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b, div: (a, b) => a / b, pow: (a, b) => Math.pow(a, b), neg: (a) => -a, sqrt: Math.sqrt });
const trim = (a) => { a = a.slice(); while (a.length > 1 && Math.abs(a[a.length - 1]) < 1e-12) a.pop(); return a; };
const POLY = {
  num: (v) => [v], v: (n) => { if (n !== 'x') throw new Error('poly var ' + n); return [0, 1]; },
  add: (a, b) => trim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => (a[i] || 0) + (b[i] || 0))),
  sub: (a, b) => trim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => (a[i] || 0) - (b[i] || 0))),
  mul: (a, b) => { const r = new Array(a.length + b.length - 1).fill(0); a.forEach((x, i) => b.forEach((y, j) => { r[i + j] += x * y; })); return trim(r); },
  div: (a, b) => { if (b.length !== 1) throw new Error('poly div'); return a.map((x) => x / b[0]); },
  pow: (a, e) => { let r = [1]; for (let i = 0; i < e; i++) r = POLY.mul(r, a); return r; },
  neg: (a) => a.map((x) => -x), sqrt: (a) => [Math.sqrt(a[0])]
};
// exponents are converted before K.plain so they survive inside stacked fractions (K.plain strips tags there)
const plain = (h) => K.plain(String(h).replace(/<sup>(.*?)<\/sup>/g, "^$1"));
const rhs = (s) => { const i = s.lastIndexOf('='); return (i >= 0 ? s.slice(i + 1) : s).trim(); };
const ev = (s, x, extra) => parse(s, NUM(Object.assign({ x: x }, extra || {})));
const poly = (s) => parse(s, POLY); // ascending coefficients
const pval = (c, x) => c.reduceRight((s, t) => s * x + t, 0);
const deg = (c) => trim(c).length - 1;
const close = (a, b, tol) => Math.abs(a - b) <= (tol || 1e-7) * (1 + Math.abs(b));
function nums(s) {
  s = s.replace(/−\$/g, '−').replace(/\$/g, '');
  const re = /−?\d{1,3}(?:,\d{3})+(?:\.\d+)?|−?\d+(?:\.\d+)?(?:\/\d+)?/g; const out = []; let mm;
  while ((mm = re.exec(s))) { const t = mm[0].replace(/,/g, '').replace('−', '-'); if (t.includes('/')) { const [a, b] = t.split('/'); out.push(+a / +b); } else out.push(+t); }
  return out;
}
function intervals(s) {
  return s.split('∪').map((part) => {
    part = part.trim(); const lc = part[0] === '[', rc = part[part.length - 1] === ']';
    const [a, b] = part.slice(1, -1).split(',').map((x) => x.trim());
    const val = (x) => x === '∞' ? Infinity : x === '−∞' ? -Infinity : ev(x, 0);
    return { lo: val(a), hi: val(b), lc: lc, rc: rc };
  });
}
const inU = (U, x) => U.some((I) => (x > I.lo || (I.lc && x === I.lo)) && (x < I.hi || (I.rc && x === I.hi)));
function splitFrac(s) { // top-level "A/B" of a plain rational expression
  let d = 0; for (let i = 0; i < s.length; i++) { if (s[i] === '(') d++; else if (s[i] === ')') d--; else if (s[i] === '/' && d === 0) return [s.slice(0, i), s.slice(i + 1)]; }
  throw new Error('no fraction in ' + s);
}
function ratRoots(c) { const out = []; for (let q = 1; q <= 6; q++) for (let pp = -60; pp <= 60; pp++) { const x = pp / q; if (Math.abs(pval(c, x)) < 1e-9 && !out.some((y) => Math.abs(y - x) < 1e-9)) out.push(x); } return out; }
// complex
const C = (re, im) => ({ re, im: im || 0 });
const cmul = (a, b) => C(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re), cadd = (a, b) => C(a.re + b.re, a.im + b.im);
const cpval = (c, z) => c.reduceRight((s, t) => cadd(cmul(s, z), C(t)), C(0));
const cabs = (z) => Math.hypot(z.re, z.im);
function listItems(s) { return s.replace(/,? and /g, ', ').split(',').map((x) => x.trim()).filter(Boolean); }
function cvals(item) { // values denoted by one list item
  item = item.replace(/\s+/g, '');
  const body = (b) => { // ± body
    if (b.startsWith('i√')) return C(0, Math.sqrt(+b.slice(2)));
    if (b.startsWith('√')) return C(Math.sqrt(+b.slice(1)), 0);
    if (b.endsWith('i')) return C(0, b === 'i' ? 1 : +b.slice(0, -1));
    return C(+b, 0);
  };
  if (item.includes('±')) { const [a, b] = item.split('±'); const base = a ? +a.replace('−', '-') : 0, bb = body(b); return [C(base + bb.re, bb.im), C(base - bb.re, -bb.im)]; }
  if (item.includes('i')) {
    const t = item.replace(/−/g, '-'); let mm = t.match(/^(-?\d+)([+-])(\d*)i$/);
    if (mm) return [C(+mm[1], (mm[2] === '-' ? -1 : 1) * (mm[3] ? +mm[3] : 1))];
    mm = t.match(/^(-?)(\d*)i$/); if (mm) return [C(0, (mm[1] ? -1 : 1) * (mm[2] ? +mm[2] : 1))];
    throw new Error('complex ' + item);
  }
  return [C(ev(item, 0), 0)];
}
function signChanges(c) { const s = c.filter((v) => Math.abs(v) > 1e-12); let k = 0; for (let i = 1; i < s.length; i++) if ((s[i] > 0) !== (s[i - 1] > 0)) k++; return k; }
const BEHS = { 'Rises on both ends': [1, 1], 'Falls on both ends': [-1, -1], 'Falls to the left, rises to the right': [-1, 1], 'Rises to the left, falls to the right': [1, -1] };
const behOf = (c) => { const d = deg(c), a = Math.sign(c[d]); return [d % 2 ? -a : a, a]; };
function parseSentence(s) { // "w varies directly as the square of x and inversely as y" -> {dep, sig:{x:2,y:-1}}
  const mm = s.match(/(\w) varies (.*)$/); const dep = mm[1], rest = mm[2], sig = {};
  const re = /(directly|inversely|jointly) as (.*?)(?= and (?:directly|inversely) as |$)/g; let c;
  while ((c = re.exec(rest))) c[2].split(' and ').forEach((part) => { const e = /square of/.test(part) ? 2 : /cube of/.test(part) ? 3 : 1, v = part.trim().slice(-1); sig[v] = c[1] === 'inversely' ? -e : e; });
  return { dep: dep, sig: sig };
}

/* ---------- judges: return a function(choiceText) -> true if that choice is correct ---------- */
const J = {
  vertex(q) { const c = poly(plain(q.p.f)), xv = -c[1] / (2 * c[2]), yv = pval(c, xv); return (s) => { const v = nums(s); return v.length === 2 && close(v[0], xv) && close(v[1], yv); }; },
  range(q) { let mn = Infinity, mx = -Infinity; for (let x = -30; x <= 30; x += 0.0005) { const y = q.p.fn(x); mn = Math.min(mn, y); mx = Math.max(mx, y); } const up = q.p.fn(1000) > 0; return (s) => { const U = intervals(s); if (U.length !== 1) return false; const I = U[0]; return up ? close(I.lo, mn, 1e-5) && I.lc && I.hi === Infinity : close(I.hi, mx, 1e-5) && I.rc && I.lo === -Infinity; }; },
  rangeP(q) { const c = poly(plain(q.p.f)); return J.range({ p: { fn: (x) => pval(c, x) } }); },
  openExt(q) { const c = poly(plain(q.p.f)), up = c[2] > 0, ext = c[0] - c[1] * c[1] / (4 * c[2]); return (s) => (/Opens up/.test(s) === up) && (/minimum/.test(s) === up) && close(nums(s)[0], ext); },
  eqexpr(q) { const f = rhs(plain(q.p.f)); return (s) => [-2.3, -0.7, 0.9, 1.6, 3.1].every((x) => close(ev(rhs(s), x), ev(f, x))); },
  graph(q) {
    const und = q.p.undef || [], pts = []; for (let x = -6.5; x <= 6.5; x += 0.37) if (und.every((u) => Math.abs(x - u) > 0.05)) pts.push(x);
    return (s) => { const e = rhs(s); if (!pts.every((x) => close(ev(e, x), q.p.fn(x), 1e-6))) return false; for (let x = -6; x <= 6; x++) { const a = ev(e, x), defined = isFinite(a); if (defined !== (und.indexOf(x) < 0)) return false; } return true; };
  },
  proj(q) { const f = plain(q.p.f); let best = -Infinity, bt = 0; for (let t = 0; t <= 20; t += 0.0005) { const h = ev(f, 0, { t: t }); if (h > best) { best = h; bt = t; } } return (s) => { const v = nums(s); return close(v[0], bt, 1e-3) && close(v[1], best, 1e-6); }; },
  fence(q) { const P = q.p.P; let best = 0; for (let x = 0; x <= P / 2; x += 0.005) best = Math.max(best, q.p.river ? x * (P - 2 * x) : x * (P / 2 - x)); if (!new RegExp('\\b' + P + ' feet').test(plain(q.q))) throw new Error('fence perimeter missing'); return (s) => close(nums(s)[0], best, 1e-6); },
  profit(q) { const f = plain(q.p.f); let best = -Infinity, bx = 0; for (let x = 0; x <= 3000; x++) { const v = ev(f, x); if (v > best) { best = v; bx = x; } } return (s) => { const v = nums(s); return v[0] === bx && close(v[1], best); }; },
  findA(q) { const p = q.p, t = plain(q.q); if (!t.includes('(' + K.plain(K.R(p.x1).html()) + ', ' + K.plain(K.R(p.y1).html()) + ')')) throw new Error('point missing'); return (s) => { const a = nums(s)[0]; return close(a * (p.x1 - p.h) ** 2 + p.k, p.y1) && close(a * 0 + p.k, p.k); }; },
  qint(q) { // quadratic formula on the parsed coefficients; y-intercept is f(0)
    const c = poly(rhs(plain(q.p.f))); if (deg(c) !== 2) throw new Error('not quadratic'); if (!plain(q.q).includes(plain(q.p.f))) throw new Error('f missing');
    const D = c[1] * c[1] - 4 * c[2] * c[0], r = [(-c[1] - Math.sqrt(D)) / (2 * c[2]), (-c[1] + Math.sqrt(D)) / (2 * c[2])].sort((a, b) => a - b);
    return (s) => { if (!/^x-intercepts .*; y-intercept /.test(s)) return false; const v = nums(s); if (v.length !== 6 || v[1] !== 0 || v[3] !== 0 || v[4] !== 0) return false; const g = [v[0], v[2]].sort((a, b) => a - b); return close(g[0], r[0]) && close(g[1], r[1]) && close(v[5], c[0]); };
  },
  mult(q) { // expand the factored form, find integer zeros by search, count multiplicity by repeated division
    const c = poly(rhs(plain(q.p.f))); if (!plain(q.q).includes(plain(q.p.f))) throw new Error('f missing');
    const mult = (cc, z) => { let k = 0, cur = cc.slice(); for (;;) { if (cur.length < 2 || Math.abs(pval(cur, z)) > 1e-6) return k; const d = cur.slice().reverse(), qq = [d[0]]; for (let i = 1; i < d.length - 1; i++) qq.push(d[i] + qq[i - 1] * z); cur = qq.reverse(); k++; } };
    const want = {}; for (let z = -20; z <= 20; z++) { const m0 = mult(c, z); if (m0) want[z] = m0; }
    if (Object.values(want).reduce((a, b) => a + b, 0) !== deg(c)) throw new Error('zeros do not account for degree');
    return (s) => { const got = {}; const re = /(−?\d+) \(multiplicity (\d+)\)/g; let mm, cnt = 0; while ((mm = re.exec(s))) { got[+mm[1].replace('−', '-')] = +mm[2]; cnt++; } return cnt === Object.keys(want).length && Object.keys(want).every((z) => got[z] === want[z]); };
  },
  rem(q) { const f = rhs(plain(q.p.f)); if (!plain(q.q).includes(plain(K.minusH('<i>x</i>', q.p.k)))) throw new Error('divisor missing'); const r = ev(f, q.p.k); return (s) => close(nums(s)[0], r); },
  fk(q) { const f = rhs(plain(q.p.f)); if (!plain(q.q).includes('f(' + K.n(q.p.k) + ')')) throw new Error('f(k) missing'); const r = ev(f, q.p.k); return (s) => close(nums(s)[0], r); },
  qr(q) { // long division by (x - k) with subtraction, from the highest power down
    const c = poly(rhs(plain(q.p.f))).slice().reverse(), k = q.p.k, quo = []; let cur = c.slice();
    for (let i = 0; i < c.length - 1; i++) { const t = cur[i]; quo.push(t); cur[i] -= t; cur[i + 1] -= t * -k; }
    const r = cur[cur.length - 1], qa = quo.slice().reverse();
    return (s) => { const mm = s.match(/^Quotient (.+); remainder (.+)$/); if (!mm) return false; const qq = poly(mm[1]); return qq.length === qa.length && qq.every((v, i) => close(v, qa[i])) && close(ev(mm[2], 0), r); };
  },
  setup(q) { const c = poly(rhs(plain(q.p.f))).slice().reverse(); return (s) => { const mm = s.match(/^(\S+) in the box; coefficients (.+)$/); if (!mm) return false; const cs = mm[2].split(',').map((x) => ev(x, 0)); return ev(mm[1], 0) === q.p.k && cs.length === c.length && cs.every((v, i) => v === c[i]); }; },
  divexpr(q) { const f = rhs(plain(q.p.f)); return (s) => [-2.3, -0.7, 0.9, 1.6, 3.1, 4.4].every((x) => close(ev(s, x), ev(f, x) / (x - q.p.k))); },
  zeroOf(q) { const c = poly(rhs(plain(q.p.f))); return (s) => Math.abs(pval(c, nums(s)[0])) < 1e-9; },
  findB(q) { const p = q.p; if (!plain(q.q).includes('remainder is ' + K.n(p.r))) throw new Error('r missing'); return (s) => { const b = nums(s)[0]; return close(p.k ** 3 + b * p.k ** 2 + p.c1 * p.k + p.c0, p.r); }; },
  divAlg(q) { const qq = plain(q.p.q); if (!plain(q.q).includes(qq)) throw new Error('q missing'); return (s) => [-2.3, -0.7, 0.9, 1.6, 3.1].every((x) => close(ev(rhs(s), x), (x - q.p.k) * ev(qq, x) + q.p.r)); },
  notCand(q) { const c = poly(rhs(plain(q.p.f))), L = Math.abs(c[c.length - 1]), c0 = Math.abs(c[0]); return (s) => { const t = s.replace('−', '-'); let a, b; if (t.includes('/')) { [a, b] = t.split('/').map(Number); } else { a = +t; b = 1; } const g = (x, y) => y ? g(y, x % y) : x, gg = g(Math.abs(a), b); a = Math.abs(a) / gg; b = b / gg; const inList = c0 % a === 0 && L % b === 0; return !inList; }; },
  factorOf(q) { const c = poly(rhs(plain(q.p.f))); return (s) => { const l = poly(s); return l.length === 2 && Math.abs(pval(c, -l[0] / l[1])) < 1e-9; }; },
  desc(q) { const c = poly(rhs(plain(q.p.f))), cn = c.map((v, i) => i % 2 ? -v : v), v = signChanges(q.p.pos ? c : cn), want = []; for (let t = v; t >= 0; t -= 2) want.push(t); return (s) => { const got = nums(s); return got.length === want.length && got.every((x, i) => x === want[i]); }; },
  zeros(q) { const c = poly(rhs(plain(q.p.f))), d = deg(c); return (s) => { let vals = []; listItems(s).forEach((it) => { vals = vals.concat(cvals(it)); }); const distinct = vals.filter((z, i) => vals.findIndex((w) => cabs(C(w.re - z.re, w.im - z.im)) < 1e-9) === i); return distinct.length === d && distinct.every((z) => cabs(cpval(c, z)) < 1e-6); }; },
  fromZeros(q) { const p = q.p; return (s) => { const c = poly(rhs(s)); return deg(c) === 3 && p.zs.every((z) => Math.abs(pval(c, z)) < 1e-9) && close(pval(c, p.x0), p.v); }; },
  cubicConj(q) { const p = q.p; return (s) => { const c = poly(rhs(s)); return deg(c) === 3 && Math.abs(pval(c, p.r)) < 1e-9 && cabs(cpval(c, C(p.p, p.q))) < 1e-9 && close(pval(c, p.x0), p.v); }; },
  combo(q) { const c = poly(rhs(plain(q.p.f))), d = deg(c), v = signChanges(c), w = signChanges(c.map((x, i) => i % 2 ? -x : x)); return (s) => { const [a, b, cc] = nums(s); return a + b + cc === d && a <= v && (v - a) % 2 === 0 && b <= w && (w - b) % 2 === 0 && cc % 2 === 0; }; },
  endb(q) { const c = poly(rhs(plain(q.p.f))), f = rhs(plain(q.p.f)), L = Math.sign(ev(f, -1e4)), Rr = Math.sign(ev(f, 1e4)), b = behOf(c); if (b[0] !== L || b[1] !== Rr) throw new Error('end behavior mismatch'); return (s) => { const t = BEHS[s]; return t && t[0] === L && t[1] === Rr; }; },
  touch(q) { const f = rhs(plain(q.p.f)); return (s) => { const z = nums(s)[0]; if (Math.abs(ev(f, z)) > 1e-9) return false; return Math.sign(ev(f, z - 1e-3)) === Math.sign(ev(f, z + 1e-3)); }; },
  turn(q) { const c = poly(rhs(plain(q.p.f))); return (s) => nums(s)[0] === deg(c) - 1; },
  degEnd(q) { const c = poly(rhs(plain(q.p.f))), b = behOf(c); return (s) => { const mm = s.match(/^Degree (\d+); (.+)$/); if (!mm) return false; const key = Object.keys(BEHS).find((k) => k.toLowerCase() === mm[2]); return +mm[1] === deg(c) && key && BEHS[key][0] === b[0] && BEHS[key][1] === b[1]; }; },
  describe(q) { // read the conditions from the question text; check each choice's zeros, multiplicities (by repeated division) and end behavior
    const t = plain(q.q), bm = Object.keys(BEHS).find((k) => t.toLowerCase().includes(k.toLowerCase())); if (!bm) throw new Error('no end behavior in ' + t);
    const grab = (re) => { const mm = t.match(re); return mm ? listItems(mm[1]).map((x) => ev(x, 0)) : []; };
    const want = {}; grab(/crosses the x-axis at (.*?)(?:, crosses and|, and touches|,? touches)/).forEach((z) => { want[z] = 1; }); grab(/flattens out at (.*?)(?:,|$)/).forEach((z) => { want[z] = 3; }); grab(/touches it at (.*?) \(/).forEach((z) => { want[z] = 2; });
    const total = Object.values(want).reduce((a, b) => a + b, 0); if (Object.keys(want).length !== 3) throw new Error('describe parse ' + JSON.stringify(want));
    const mult = (c, z) => { let k = 0, cur = c.slice(); for (;;) { if (Math.abs(pval(cur, z)) > 1e-9 || cur.length < 2) return k; const d = cur.slice().reverse(), qq = [d[0]]; for (let i = 1; i < d.length - 1; i++) qq.push(d[i] + qq[i - 1] * z); cur = qq.reverse(); k++; } };
    return (s) => { const c = poly(rhs(s)); if (deg(c) !== total) return false; const b = behOf(c); if (b[0] !== BEHS[bm][0] || b[1] !== BEHS[bm][1]) return false; return Object.keys(want).every((z) => mult(c, +z) === want[z]); };
  },
  ivt(q) { const f = rhs(plain(q.p.f)); return (s) => { const [a, b] = nums(s); let ch = 0; for (let i = 0; i < 4000; i++) { const x1 = a + (b - a) * i / 4000, x2 = a + (b - a) * (i + 1) / 4000; if (ev(f, x1) * ev(f, x2) <= 0) ch++; } if (ch && ev(f, a) * ev(f, b) >= 0) throw new Error('interval with zero but no sign change'); return ev(f, a) * ev(f, b) < 0; }; },
  ineq(q) { const f = rhs(plain(q.p.f)); for (let x = -7.3; x < 7; x += 0.41) if (!close(ev(f, x), q.p.fn(x))) throw new Error('ineq fn mismatch'); if (!plain(q.q).includes(q.p.gt ? '> 0' : '< 0')) throw new Error('sign missing');
    return (s) => { const U = intervals(s); for (let k = -800; k <= 800; k++) { const x = k / 100, v = ev(f, x), want = q.p.gt ? v > 0 : v < 0; if (inU(U, x) !== want) return false; } return true; }; },
  box(q) { const p = q.p, hi = Math.min(p.L, p.W) / 2, V = p.d * (p.L - 2 * p.d) * (p.W - 2 * p.d); return (s) => { const mm = s.match(/^Domain (.+); (.+) cubic inches$/); if (!mm) return false; const U = intervals(mm[1]); return U.length === 1 && U[0].lo === 0 && !U[0].lc && U[0].hi === hi && !U[0].rc && close(nums(mm[2])[0], V); }; },
  va(q) { const [a, b] = splitFrac(rhs(plain(q.p.f))), nc = poly(a), dc = poly(b), vas = ratRoots(dc).filter((x) => Math.abs(pval(nc, x)) > 1e-9).sort((x, y) => x - y); if (vas.length !== deg(dc)) throw new Error('va count'); return (s) => { if (/y =/.test(s)) return false; const v = nums(s).sort((x, y) => x - y); return v.length === vas.length && v.every((x, i) => close(x, vas[i])); }; },
  ha(q) { const f = rhs(plain(q.p.f)), L = ev(f, 1e7), L2 = ev(f, -1e7), none = Math.abs(L) > 1e3; if (!none && !close(L, L2, 1e-4)) throw new Error('ha sides'); return (s) => none ? s === 'No horizontal asymptote' : (/^y =/.test(s) && Math.abs(ev(rhs(s), 0) - L) < 1e-4); },
  asym(q) { const f = rhs(plain(q.p.f)), L = ev(f, 1e8); let va = null; for (let x = -10; x <= 10; x++) if (!isFinite(ev(f, x)) || Math.abs(ev(f, x + 1e-9)) > 1e6) va = x; return (s) => { const mm = s.match(/^x = (.+) and y = (.+)$/); return !!mm && ev(mm[1], 0) === va && Math.abs(ev(mm[2], 0) - L) < 1e-6; }; },
  hole(q) {
    const [a, b] = splitFrac(rhs(plain(q.p.f))), nc = poly(a), dc = poly(b), dr = ratRoots(dc), holes = dr.filter((x) => Math.abs(pval(nc, x)) < 1e-9), vas = dr.filter((x) => Math.abs(pval(nc, x)) > 1e-9);
    const f = (x) => pval(nc, x) / pval(dc, x);
    if (holes.length !== 1 || vas.length !== 1) throw new Error('hole setup');
    const hx = holes[0], hy = (f(hx + 1e-6) + f(hx - 1e-6)) / 2;
    return (s) => { const mm = s.match(/^Hole at (.+); vertical asymptote x = (.+)$/); if (!mm) return false; const pt = nums(mm[1]); return close(pt[0], hx) && close(pt[1], hy, 1e-5) && close(ev(mm[2], 0), vas[0]); };
  },
  oblique(q) { const f = rhs(plain(q.p.f)); return (s) => { const e = rhs(s); return [1e7, -1e7].every((x) => Math.abs(ev(f, x) - ev(e, x)) < 1e-3); }; },
  intercepts(q) { const f = rhs(plain(q.p.f)); return (s) => { const v = nums(s); return v.length === 4 && v[1] === 0 && v[2] === 0 && Math.abs(ev(f, v[0])) < 1e-9 && close(ev(f, 0), v[3]); }; },
  avgcost(q) { const p = q.p, A = (x) => (p.c * x + p.F) / x, lim = A(1e12); return (s) => { const v = nums(s); return close(v[0], A(p.N)) && close(v[1], lim, 1e-6); }; },
  solveCost(q) { const p = q.p; let lo = 1, hi = 1e7; const g = (x) => (p.c * x + p.F) / x - p.T; for (let i = 0; i < 200; i++) { const mid = (lo + hi) / 2; if (g(lo) * g(mid) <= 0) hi = mid; else lo = mid; } return (s) => Math.abs(nums(s)[0] - lo) < 1e-4; },
  vary(q) {
    const p = q.p, t = plain(q.q); let y = p.y1; p.e.forEach((e) => { y *= Math.pow(e[2] / e[1], e[0]); });
    p.e.forEach((e) => { if (Math.abs(e[0]) === 2 && !/square/.test(t)) throw new Error('square missing'); if (e[0] < 0 && !/inversely/.test(t)) throw new Error('inversely missing'); });
    if (p.e.some((e) => e[0] > 0) && !/directly|jointly/.test(t)) throw new Error('directly missing');
    const want = p.round !== undefined ? K.round(y, p.round) : y;
    return (s) => close(nums(s)[0], want, 1e-9);
  },
  translate(q) {
    const t = plain(q.q), sen = t.match(/“(.*)”/)[1], ps = parseSentence(sen); if (ps.dep !== q.p.dep) throw new Error('dep');
    const vars = { k: 1.3, x: 1.7, y: 2.9, z: 0.6 };
    return (s) => { const mm = s.match(/^(\w) = (.+)$/); if (!mm || mm[1] !== ps.dep) return false; const pts = [vars, { k: 1.3, x: 3.1, y: 0.7, z: 2.2 }]; return pts.every((vv) => { let want = vv.k; Object.keys(ps.sig).forEach((v) => { want *= Math.pow(vv[v], ps.sig[v]); }); return close(parse(mm[2], NUM(vv)), want); }); };
  },
  scale(q) {
    const t = plain(q.q), ps = parseSentence(t.match(/(\w varies .*?)\. If/)[1]), mult = { doubled: 2, tripled: 3, quadrupled: 4 };
    const mx = mult[t.match(/x is (\w+)/)[1]], my = mult[t.match(/y is (\w+)/)[1]];
    const z = (x, y) => Math.pow(x, ps.sig.x) * Math.pow(y, ps.sig.y), fct = z(1.7 * mx, 2.3 * my) / z(1.7, 2.3);
    return (s) => close(nums(s)[0], fct);
  }
};

/* ---------- run ---------- */
let total = 0, fails = 0, perGen = [];
for (const id of Object.keys(K.lessons)) {
  if (/^R/.test(id)) continue;
  K.lessons[id].levels.forEach((gens, lv) => gens.forEach((g, gi) => {
    let ok = 0, type = '';
    for (let r = 0; r < RUNS; r++) {
      K._gd = []; const q = g(); total++;
      type = q.p && q.p.t;
      try {
        if (!q.p || !J[q.p.t]) throw new Error('no judge for ' + (q.p && q.p.t));
        const judge = J[q.p.t](q), verdicts = q.ch.map((c) => { try { return !!judge(plain(c)); } catch (e) { throw new Error('choice parse: ' + plain(c) + ' :: ' + e.message); } });
        const nRight = verdicts.filter(Boolean).length;
        if (nRight !== 1 || !verdicts[q.a]) throw new Error('verdicts ' + verdicts.join(',') + ' marked ' + q.a);
        ok++;
      } catch (e) {
        fails++; if (fails <= 25) console.log('FAIL', id, 'L' + (lv + 1), 'gen' + gi, e.message, '\n   Q:', plain(q.q).slice(0, 200), '\n   choices:', q.ch.map(plain).join(' | '), '\n   marked:', plain(q.ans));
      }
    }
    perGen.push(id + ' L' + (lv + 1) + ' g' + gi + ' [' + type + '] ' + ok + '/' + RUNS);
  }));
}
console.log(perGen.join('\n'));
console.log('generators', perGen.length, 'questions checked', total, 'failures', fails);
process.exit(fails ? 1 : 0);
