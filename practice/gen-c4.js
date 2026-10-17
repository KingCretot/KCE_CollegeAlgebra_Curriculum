/* Chapter 4 — Inverse, Exponential & Logarithmic Functions */
(function (K) {
  var ri = K.ri, rnz = K.rnz, pick = K.pick, n = K.n, P = K.poly, Q = K.Q, mc = K.mc, M = K.MINUS, m = K.m, fr = K.frx, R = K.R, C = K.COL;
  var xi = '<i>x</i>', yi = '<i>y</i>', zi = '<i>z</i>', INF = '∞', NINF = M + '∞';
  var FI = '<i>f</i><sup>' + M + '1</sup>';
  var H3O = '[H<sub>3</sub>O<sup>+</sup>]', I0 = '<i>I</i><sub>0</sub>';

  /* ---------- helpers ---------- */
  function QP(o, p) { var q = Q(o); q.p = p; return q; }
  function fx(s) { return '<i>f</i>(<i>x</i>) = ' + s; }
  function xeq(v) { return m('<i>x</i> = ' + v); }
  function xap(v) { return m('<i>x</i> ≈ ' + v); }
  // fixed decimals with Unicode minus
  function dec(v, d) { var s = K.round(v, d).toFixed(d); if (/^-0(\.0*)?$/.test(s)) s = s.slice(1); return s.replace(/^-/, M); }
  function comma(s) { var p = s.split('.'); p[0] = p[0].replace(/\B(?=(\d{3})+(?!\d))/g, ','); return p.join('.'); }
  function decc(v, d) { return comma(dec(v, d)); }
  function money(v) { return '$' + decc(v, 2); }
  function moneyW(v) { return Math.abs(v - Math.round(v)) < 1e-9 ? '$' + comma(String(Math.round(v))) : money(v); }
  // true when v is not within a hair of a rounding tie at d decimals
  function safe(v, d) { var s = Math.abs(v) * Math.pow(10, d); return Math.abs(s - Math.floor(s) - 0.5) > 1e-6; }
  function ln(v) { return Math.log(v); }
  function lg10(v) { return Math.log(v) / Math.LN10; }
  function d4(v) { return dec(v, 4); }
  // numeric choices: numerically equal wrong values are dropped before formatting
  function mcN(c, ws, fmt, ext) {
    var list = [];
    ws.forEach(function (w) { if (typeof w === 'number' && isFinite(w) && Math.abs(w - c) > 1e-9) list.push(fmt(w)); });
    return mc(fmt(c), list, ext || function (i) { var f = 1 + rnz(-4, 4) * (0.07 + 0.02 * (i % 10)); return fmt(c * f + (c === 0 ? rnz(-3, 3) : 0)); });
  }
  // rational choices; wrap(html) builds the choice text
  function mcR(c, ws, wrap, ext) {
    c = R(c); wrap = wrap || function (h) { return h; };
    var list = [];
    ws.forEach(function (w) { if (w === null || w === undefined) return; w = R(w); if (!w.eq(c)) list.push(wrap(w.html())); });
    return mc(wrap(c.html()), list, ext || function (i) { return wrap(c.add(rnz(-3, 3) * (1 + Math.floor(i / 10))).html()); });
  }
  function rpow(r, e) { r = R(r); var out = R(1); for (var i = 0; i < Math.abs(e); i++) out = out.mul(r); return e < 0 ? R(1).div(out) : out; }
  function pw(b, e) { return b + '<sup>' + e + '</sup>'; }
  function ex(e) { return 'e<sup>' + e + '</sup>'; }
  function lg(b, a, par) { var L = b === 10 ? 'log' : b === 'e' ? 'ln' : 'log<sub>' + b + '</sub>'; return L + (par ? '(' + a + ')' : ' ' + a); }
  function bh(r) { r = R(r); if (r.d === 1) return n(r.n); if (r.n === 1 && r.d === 2) return '(½)'; if (r.n === 1 && r.d === 3) return '(⅓)'; if (r.n === 1 && r.d === 4) return '(¼)'; return '(' + r.n + '/' + r.d + ')'; }
  function rs(r) { r = R(r); return r.d === 1 ? n(r.n) : (r.n < 0 ? M : '') + Math.abs(r.n) + '/' + r.d; } // inline rational (for exponents)
  function sub(v) { return v < 0 ? '(' + n(v) + ')' : n(v); }
  function iv(lo, hi, lc, rc) { return m((lc || '(') + lo + ', ' + hi + (rc || ')')); }
  function ivUnion(a, b, closed) { return m('(' + NINF + ', ' + a + (closed ? ']' : ')') + ' ∪ ' + (closed ? '[' : '(') + b + ', ' + INF + ')'); }
  function setStr(arr) { arr = arr.slice().sort(function (p, q) { return p - q; }); return xeq(n(arr[0])) + ' or ' + xeq(n(arr[1])); }
  function coefTerm(c, first, body) { c = R(c); var neg = c.n < 0, a = c.abs(); var co = (a.n === 1 && a.d === 1) ? '' : a.html() + ' '; return (first ? (neg ? M : '') : (neg ? ' ' + M + ' ' : ' + ')) + co + body; }
  function logCombo(b, cs, vars) { var out = '', first = true; cs.forEach(function (c, i) { c = R(c); if (c.n === 0) return; out += coefTerm(c, first, lg(b, vars[i])); first = false; }); return out; }
  function eqTriple(a, b) { return a.every(function (v, i) { return R(v).eq(R(b[i])); }); }
  function sci(v) {
    var e = Math.floor(lg10(v)), mt = v / Math.pow(10, e);
    if (mt >= 9.95) { mt /= 10; e += 1; }
    return dec(mt, 1) + ' × 10' + K.sup(n(e));
  }
  function sciSafe(v) { var e = Math.floor(lg10(v)), mt = v / Math.pow(10, e); return safe(mt, 1) && mt < 9.95; }
  function expF(a, b, h, k, neg) { return (neg ? M : '') + (a === 1 ? '' : n(a) + ' · ') + pw(bh(b), K.minusH(xi, h)) + K.plusK(k); }
  function graphGrid(o) { o.lab = o.lab || 2; return K.plane(o); }

  /* ---------- 4.1 Inverse Functions ---------- */
  var c41 = [
    [
      function () {   // one-to-one choice
        var c = rnz(-6, 6), h = rnz(-4, 4), k = rnz(-5, 5), s = pick([2, 3, -2, -3, 4]);
        var goods = [
          [m(fx(K.xp(3) + K.plusK(c))), 'Cubing always increases, so ' + m(K.xp(3) + K.plusK(c)) + ' rises everywhere and every horizontal line hits it once.', 'cube'],
          [m(fx(P([[s, xi], [c, '']]))), 'A line with nonzero slope ' + n(s) + ' always ' + (s > 0 ? 'rises' : 'falls') + ', so every horizontal line hits it once.', 'line'],
          [m(fx(K.sqrt(K.minusH(xi, h)))), 'A square root always increases on its domain, so no output repeats.', 'sqrt'],
          [m(fx(pw('2', xi) + K.plusK(c))), 'An exponential with base 2 always increases, so no output repeats.', 'exp']
        ];
        var bads = [
          [m(fx(K.xp(2) + K.plusK(c))), m('<i>f</i>(' + M + '1) = <i>f</i>(1) = ' + n(1 + c))],
          [m(fx('|' + K.minusH(xi, h) + '|')), m('<i>f</i>(' + n(h - 1) + ') = <i>f</i>(' + n(h + 1) + ') = 1')],
          [m(fx(K.xp(4) + K.plusK(c))), m('<i>f</i>(' + M + '1) = <i>f</i>(1) = ' + n(1 + c))],
          [m(fx('(' + K.minusH(xi, h) + ')' + K.sup(2) + K.plusK(k))), m('<i>f</i>(' + n(h - 1) + ') = <i>f</i>(' + n(h + 1) + ') = ' + n(1 + k))]
        ];
        var g = pick(goods), bs = K.sample(bads, 3);
        return QP({ q: 'Which function is one-to-one?', mc: mc(g[0], bs.map(function (b) { return b[0]; })), why: [g[1], 'Each other choice repeats an output, so some horizontal line hits it twice: ' + bs.map(function (b) { return b[1]; }).join('; ') + '.', 'Only a one-to-one function has an inverse function.'] }, { t: 'oto' });
      },
      function () {   // inverse from a table
        var xs = [-2, -1, 0, 1, 2, 3], ys, j, y, wr;
        do {
          ys = K.sample([-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8], 6);
          j = ri(0, 5); y = ys[j];
          wr = xs.indexOf(y) >= 0 ? ys[xs.indexOf(y)] : null;
        } while (y === xs[j] || wr === null || wr === xs[j]);
        var a = xs[j];
        return QP({ q: 'The table lists the one-to-one function ' + m('<i>f</i>') + '. What is ' + m(FI + '(' + n(y) + ')') + '?', graph: K.xyTable(xs, ys, xi, m('<i>f</i>(<i>x</i>)')),
          mc: mcR(a, [wr, -a, y !== 0 ? R(1, y) : null], null),
          why: [m(FI + '(' + n(y) + ')') + ' asks: which input gives the output ' + n(y) + '?', 'Find ' + n(y) + ' in the ' + m('<i>f</i>(<i>x</i>)') + ' row: ' + m('<i>f</i>(' + n(a) + ') = ' + n(y)) + '.', 'So ' + m(FI + '(' + n(y) + ') = ' + n(a)) + '. (Looking up ' + n(y) + ' in the ' + xi + ' row gives ' + m('<i>f</i>(' + n(y) + ') = ' + n(wr)) + ', a different question.)'] },
          { t: 'tbl', xs: xs, ys: ys, y: y });
      },
      function () {   // inverse of a linear function
        var a = ri(2, 6), b = rnz(-9, 9), pre = FI + '(<i>x</i>) = ';
        var right = m(pre + fr(K.minusH(xi, b), n(a)));
        var w = K.shuffle([m(pre + fr(xi, n(a)) + K.plusK(-b)), m(pre + fr(K.minusH(xi, -b), n(a))), m(pre + P([[a, xi], [-b, '']])), m(pre + fr('1', P([[a, xi], [b, '']])))]);
        return QP({ q: 'Find the inverse of ' + m(fx(P([[a, xi], [b, '']]))) + '.', mc: mc(right, w),
          why: ['Write ' + m('<i>y</i> = ' + P([[a, xi], [b, '']])) + ' and swap ' + xi + ' and ' + yi + ': ' + m('<i>x</i> = ' + P([[a, yi], [b, '']])) + '.', 'Solve for ' + yi + ': ' + m(K.minusH(xi, b) + ' = ' + n(a) + '<i>y</i>') + ', so ' + m('<i>y</i> = ' + fr(K.minusH(xi, b), n(a))) + '.', 'The inverse undoes the steps in reverse order: ' + (b > 0 ? 'subtract ' + n(b) : 'add ' + n(-b)) + ' first, then divide by ' + a + '. Check: ' + m(n(a) + ' · ' + fr(K.minusH(xi, b), n(a)) + K.plusK(b) + ' = <i>x</i>') + '.'] },
          { t: 'linv', a: a, b: b });
      },
      function () {   // read f^-1 from a graph
        var type = K.coin() ? 'line' : 'sqrt', f, pts = [], from, s = 0, b = 0, a = 0, c = 0;
        if (type === 'line') {
          s = pick([-3, -2, -1, 2, 3]); b = ri(-3, 3);
          f = function (x) { return s * x + b; };
          for (var x = -4; x <= 4; x++) { if (Math.abs(f(x)) <= 7) pts.push([x, f(x)]); }
        } else {
          a = ri(1, 6); c = ri(-4, 3); from = -a;
          f = function (x) { return Math.sqrt(x + a) + c; };
          for (var t = 0; t <= 3; t++) pts.push([-a + t * t, c + t]);
        }
        var cand = pts.filter(function (p) { return p[0] !== p[1]; });
        var tp = pick(cand), x1 = tp[0], y1 = tp[1];
        var others = K.sample(pts.filter(function (p) { return p !== tp; }), 2), shown = [tp].concat(others);
        var wr = [-x1, y1];
        if (type === 'line' || y1 + a >= 0) { var fy = f(y1); if (Math.abs(fy - Math.round(fy)) < 1e-9 && Math.abs(fy) <= 30) wr.splice(0, 0, Math.round(fy)); }
        others.forEach(function (p) { wr.push(p[0]); });
        var g = graphGrid({ x: [-8, 8], y: [-8, 8], fns: [{ f: f, from: from }], lines: [{ m: 1, b: 0, dash: true, color: C.gray }], pts: shown.map(function (p) { return { x: p[0], y: p[1] }; }) });
        return QP({ q: 'The graph of the one-to-one function ' + m('<i>f</i>') + ' is shown (the dashed gray line is ' + m('<i>y</i> = <i>x</i>') + '). Use the graph to find ' + m(FI + '(' + n(y1) + ')') + '.', graph: g,
          mc: mcN(x1, wr, n, function (i) { return n(x1 + rnz(-3, 3) * (1 + Math.floor(i / 10))); }),
          why: [m(FI + '(' + n(y1) + ')') + ' is the input of ' + m('<i>f</i>') + ' whose output is ' + n(y1) + '.', 'On the graph, the point ' + K.pt(x1, y1) + ' is on ' + m('<i>f</i>') + ': when ' + m('<i>y</i> = ' + n(y1)) + ', ' + m('<i>x</i> = ' + n(x1)) + '.', 'So ' + m(FI + '(' + n(y1) + ') = ' + n(x1)) + '. Reflected over ' + m('<i>y</i> = <i>x</i>') + ', the point ' + K.pt(y1, x1) + ' is on ' + m(FI) + '.'] },
          { t: 'gread', type: type, s: s, b: b, a: a, c: c, y: y1, shown: shown });
      }
    ],
    [
      function () {   // verify by composition
        var a = ri(2, 5), b = rnz(-8, 8), c = K.coin() ? -b : -b + rnz(-4, 4), s = c + b;
        function ch(sh) { return m('<i>f</i>(<i>g</i>(<i>x</i>)) = ' + P([[1, xi], [sh, '']])) + (sh === 0 ? ', so ' + m('<i>f</i>') + ' and ' + m('<i>g</i>') + ' are inverses' : ', so ' + m('<i>f</i>') + ' and ' + m('<i>g</i>') + ' are not inverses'); }
        var ws = [], cand = s === 0 ? [-2 * b, c, b] : [0, c - b, -s, c];
        cand.forEach(function (v) { if (v !== s) ws.push(ch(v)); });
        var steps = ['Substitute ' + m('<i>g</i>(<i>x</i>)') + ' into ' + m('<i>f</i>') + ': ' + m('<i>f</i>(<i>g</i>(<i>x</i>)) = ' + n(a) + ' · ' + fr(K.minusH(xi, -c), n(a)) + K.plusK(b)) + '.', 'The ' + a + 's cancel: ' + m(P([[1, xi], [c, ''], [b, '']]) + ' = ' + P([[1, xi], [s, '']])) + '.'];
        if (s === 0) steps.push('Also ' + m('<i>g</i>(<i>f</i>(<i>x</i>)) = ' + fr('(' + P([[a, xi], [b, '']]) + ')' + K.plusK(c), n(a)) + ' = <i>x</i>') + '. Both compositions give ' + xi + ', so ' + m('<i>g</i> = ' + FI) + '.');
        else steps.push('Since ' + m('<i>f</i>(<i>g</i>(<i>x</i>)) ≠ <i>x</i>') + ', they are not inverses. (The inverse is ' + m(FI + '(<i>x</i>) = ' + fr(K.minusH(xi, b), n(a))) + '.)');
        return QP({ q: 'Let ' + m(fx(P([[a, xi], [b, '']]))) + ' and ' + m('<i>g</i>(<i>x</i>) = ' + fr(K.minusH(xi, -c), n(a))) + '. Find ' + m('<i>f</i>(<i>g</i>(<i>x</i>))') + ' and decide whether ' + m('<i>f</i>') + ' and ' + m('<i>g</i>') + ' are inverses.', mc: mc(ch(s), ws, function (i) { return ch(s + rnz(-5, 5) * (1 + Math.floor(i / 10))); }), why: steps },
          { t: 'comp', a: a, b: b, c: c });
      },
      function () {   // inverse of (ax + b)/(x − c)
        var a, b, c;
        do { a = rnz(-4, 4); b = rnz(-6, 6); c = rnz(-5, 5); } while (c === a || -a * c - b === 0);
        var pre = FI + '(<i>x</i>) = ';
        var right = m(pre + fr(P([[c, xi], [b, '']]), K.minusH(xi, a)));
        var w = K.shuffle([m(pre + fr(K.minusH(xi, c), P([[a, xi], [b, '']]))), m(pre + fr(P([[c, xi], [-b, '']]), K.minusH(xi, a))), m(pre + fr(P([[c, xi], [b, '']]), K.minusH(xi, -a))), m(pre + fr(P([[a, xi], [b, '']]), K.minusH(xi, c)))]);
        return QP({ q: 'Find the inverse of the one-to-one function ' + m(fx(fr(P([[a, xi], [b, '']]), K.minusH(xi, c)))) + '.', mc: mc(right, w),
          why: ['Swap ' + xi + ' and ' + yi + ': ' + m('<i>x</i> = ' + fr(P([[a, yi], [b, '']]), K.minusH(yi, c))) + '.', 'Clear the fraction: ' + m(P([[1, '<i>xy</i>'], [-c, xi]]) + ' = ' + P([[a, yi], [b, '']])) + '. Collect the ' + yi + '-terms: ' + m(P([[1, '<i>xy</i>'], [-a, yi]]) + ' = ' + P([[c, xi], [b, '']])) + '.', 'Factor: ' + m('<i>y</i>(' + K.minusH(xi, a) + ') = ' + P([[c, xi], [b, '']])) + ', so ' + m(FI + '(<i>x</i>) = ' + fr(P([[c, xi], [b, '']]), K.minusH(xi, a))) + ', ' + m('<i>x</i> ≠ ' + n(a)) + '.'] },
          { t: 'ratinv', a: a, b: b, c: c });
      },
      function () {   // restricted quadratic
        var h, k;
        do { h = rnz(-5, 5); k = rnz(-6, 6); } while (h === k);
        var pre = FI + '(<i>x</i>) = ';
        function opt(sg, inside, plus, dom) { return m(pre + (sg < 0 ? M : '') + K.sqrt(K.minusH(xi, inside)) + K.plusK(plus)) + ', ' + m('<i>x</i> ≥ ' + n(dom)); }
        var right = opt(1, k, h, k);
        var w = K.shuffle([opt(-1, k, h, k), opt(1, -k, h, -k), opt(1, h, k, h), opt(1, k, -h, k)]);
        return QP({ q: 'Find the inverse of ' + m(fx('(' + K.minusH(xi, h) + ')' + K.sup(2) + K.plusK(k))) + ', ' + m('<i>x</i> ≥ ' + n(h)) + ', including its domain.', mc: mc(right, w),
          why: ['Swap ' + xi + ' and ' + yi + ': ' + m('<i>x</i> = (' + K.minusH(yi, h) + ')' + K.sup(2) + K.plusK(k)) + ', so ' + m(K.minusH(xi, k) + ' = (' + K.minusH(yi, h) + ')' + K.sup(2)) + '.', 'Take the square root. The original domain ' + m('<i>x</i> ≥ ' + n(h)) + ' becomes ' + m('<i>y</i> ≥ ' + n(h)) + ', so ' + m(K.minusH(yi, h)) + ' is not negative: use the positive root, ' + m(K.sqrt(K.minusH(xi, k)) + ' = ' + K.minusH(yi, h)) + '.', m(pre + K.sqrt(K.minusH(xi, k)) + K.plusK(h)) + ' with domain ' + m('<i>x</i> ≥ ' + n(k)) + ', which is the range of ' + m('<i>f</i>') + '.'] },
          { t: 'sqinv', h: h, k: k });
      }
    ],
    [
      function () {   // domain and range of f^-1 from a graph
        var h, k;
        do { h = ri(-4, 3); k = ri(-4, 4); } while (h === k);
        var x0 = Math.min(-2, h - 2), y0 = Math.min(-2, k - 2), L = Math.max(h + 10 - x0, k + 5 - y0, 12);
        var f = function (x) { return Math.sqrt(x - h) + k; };
        var g = graphGrid({ x: [x0, x0 + L], y: [y0, y0 + L], fns: [{ f: f, from: h }], lines: [{ m: 1, b: 0, dash: true, color: C.gray }], pts: [{ x: h, y: k }, { x: h + 4, y: k + 2 }] });
        function ch(d, r, op) { return 'Domain ' + m((op ? '(' : '[') + n(d) + ', ' + INF + ')') + '; range ' + m((op ? '(' : '[') + n(r) + ', ' + INF + ')'); }
        return QP({ q: 'The graph of ' + m(fx(K.sqrt(K.minusH(xi, h)) + K.plusK(k))) + ' is shown, with the line ' + m('<i>y</i> = <i>x</i>') + ' dashed. What are the domain and range of ' + m(FI) + '?', graph: g,
          mc: mc(ch(k, h), [ch(h, k), ch(k, h, true), 'Domain ' + m('(' + NINF + ', ' + INF + ')') + '; range ' + m('[' + n(h) + ', ' + INF + ')')]),
          why: ['The graph of ' + m('<i>f</i>') + ' starts at ' + K.pt(h, k) + ' and rises to the right: domain ' + m('[' + n(h) + ', ' + INF + ')') + ', range ' + m('[' + n(k) + ', ' + INF + ')') + '.', 'An inverse swaps inputs and outputs, so the domain and range trade places.', m(FI) + ' has domain ' + m('[' + n(k) + ', ' + INF + ')') + ' and range ' + m('[' + n(h) + ', ' + INF + ')') + '. Its graph starts at ' + K.pt(k, h) + ', the reflection of ' + K.pt(h, k) + ' over ' + m('<i>y</i> = <i>x</i>') + '.'] },
          { t: 'drinv', h: h, k: k, pts: [[h, k], [h + 4, k + 2]] });
      },
      function () {   // taxi fare inverse
        var r = pick([2, 2.5, 4, 1.25]), b = ri(2, 6), mi = ri(4, 20), F = r * mi + b;
        var CI = '<i>C</i><sup>' + M + '1</sup>';
        function rideCh(v) { return m(CI + '(' + n(F) + ') = ' + n(v)) + ': a fare of ' + money(F) + ' pays for a ride of ' + n(v) + ' miles'; }
        var w = [m(CI + '(' + n(F) + ') = ' + n(r * F + b)) + ': a ride of ' + n(F) + ' miles costs ' + money(r * F + b), rideCh((F + b) / r)];
        if (F / r - b > 0) w.push(rideCh(F / r - b));
        return QP({ q: 'A taxi charges a ' + money(b) + ' pickup fee plus ' + money(r) + ' per mile, so ' + m('<i>C</i>(<i>m</i>) = ' + n(r) + '<i>m</i> + ' + n(b)) + ' is the fare in dollars for an ' + m('<i>m</i>') + '-mile ride. Find ' + m(CI + '(' + n(F) + ')') + ' and interpret it.', mc: mc(rideCh(mi), w, function (i) { return rideCh(mi + rnz(-4, 4) * (1 + Math.floor(i / 10))); }),
          why: ['Solve ' + m('<i>F</i> = ' + n(r) + '<i>m</i> + ' + n(b)) + ' for ' + m('<i>m</i>') + ': ' + m(CI + '(<i>F</i>) = ' + fr('<i>F</i> ' + M + ' ' + n(b), n(r))) + '.', m(CI + '(' + n(F) + ') = ' + fr(n(F) + ' ' + M + ' ' + n(b), n(r)) + ' = ' + n(mi)) + '.', 'The inverse takes a fare and returns the miles: a ' + money(F) + ' fare pays for a ' + n(mi) + '-mile ride. (Check: ' + m(n(r) + '(' + n(mi) + ') + ' + n(b) + ' = ' + n(F)) + '.)'] },
          { t: 'taxi', r: r, b: b, F: F });
      },
      function () {   // domain of f^-1 for a rational function = range of f
        var a, b, d, e;
        do { d = pick([1, 1, 2, 3]); a = rnz(-6, 6); b = rnz(-6, 6); e = rnz(-6, 6); } while (R(a, d).eq(R(-e, d)) || R(a, d).eq(R(e, d)) || a * e - b * d === 0);
        var den = P([[d, xi], [e, '']]), num = P([[a, xi], [b, '']]);
        var A = R(a, d);
        function ex1(v) { v = R(v); return ivUnion(v.html(), v.html()); }
        var ws = [R(-e, d), R(e, d), R(-a, d)].filter(function (v) { return !v.eq(A); }).map(ex1);
        ws.push('All real numbers');
        return QP({ q: 'For the one-to-one function ' + m(fx(fr(num, den))) + ', what is the domain of ' + m(FI) + '?', mc: mc(ex1(A), ws),
          why: ['The domain of ' + m(FI) + ' is the range of ' + m('<i>f</i>') + '. Find ' + m(FI) + ': swap to get ' + m('<i>x</i> = ' + fr(P([[a, yi], [b, '']]), P([[d, yi], [e, '']]))) + '.', 'Then ' + m(P([[d, '<i>xy</i>'], [e, xi]]) + ' = ' + P([[a, yi], [b, '']])) + ', so ' + m('<i>y</i>(' + P([[d, xi], [-a, '']]) + ') = ' + P([[-e, xi], [b, '']])) + ' and ' + m(FI + '(<i>x</i>) = ' + fr(P([[-e, xi], [b, '']]), P([[d, xi], [-a, '']]))) + '.', m(FI) + ' is not defined only at ' + m('<i>x</i> = ' + A.html()) + ', so its domain is ' + ex1(A) + '. (' + m('<i>x</i> = ' + R(-e, d).html()) + ' is excluded from the domain of ' + m('<i>f</i>') + ', not of ' + m(FI) + '.)'] },
          { t: 'ratdom', a: a, b: b, d: d, e: e });
      }
    ]
  ];
  K.lesson('4.1', { title: 'Inverse Functions', std: 'Lial 12e · Section 4.1', levels: c41 });

  /* ---------- 4.2 Exponential Functions ---------- */
  function mbGen(recip) {   // matching bases: (b^p)^(Ax+B) = (b^q)^(Cx+D)
    var b, ex, p, q, A, B, Cc, D, sp, xv, tries = 0;
    do {
      b = pick([2, 2, 3, 5]); ex = { 2: [1, 2, 3, 4, 5], 3: [1, 2, 3, 4], 5: [1, 2, 3] }[b];
      p = pick(ex); q = pick(ex); A = ri(1, 3); Cc = ri(1, 3); B = rnz(-4, 4); D = rnz(-5, 5);
      sp = recip ? -p : p;
      xv = (sp * A - q * Cc) !== 0 ? R(q * D - sp * B, sp * A - q * Cc) : null;
      tries++;
    } while (!xv || (!recip && (p === q || xv.d !== 1)) || (recip && xv.d > 6) || Math.abs(xv.val()) > 12 || (recip && p === 1 && q === 1));
    var lb = recip ? '(' + K.f(1, Math.pow(b, p)) + ')' : n(Math.pow(b, p)), rb = n(Math.pow(b, q));
    var lexp = P([[A, '<i>x</i>'], [B, '']]), rexp = P([[Cc, '<i>x</i>'], [D, '']]);
    var ws = [];
    if (A !== Cc) ws.push(R(D - B, A - Cc));
    if (sp * A - q * Cc !== 0) ws.push(R(D - B, sp * A - q * Cc));
    ws.push(xv.neg());
    if (recip && p * A - q * Cc !== 0) ws.push(R(q * D - p * B, p * A - q * Cc));
    return QP({ q: 'Solve: ' + m(pw(lb, lexp) + ' = ' + pw(rb, rexp)) + (recip ? '. Give an exact answer.' : ''), mc: mcR(xv, ws, function (h) { return xeq(h); }),
      why: ['Write both sides with base ' + b + ': ' + m(lb + ' = ' + pw(b, n(sp))) + ' and ' + m(rb + ' = ' + pw(b, n(q))) + '.', 'Multiply the exponents (distribute to every term): ' + m(pw(b, P([[sp * A, xi], [sp * B, '']])) + ' = ' + pw(b, P([[q * Cc, xi], [q * D, '']]))) + '.', 'Same base, so the exponents are equal: ' + m(P([[sp * A, xi], [sp * B, '']]) + ' = ' + P([[q * Cc, xi], [q * D, '']])) + ', which gives ' + xeq(xv.html()) + '.'] },
      { t: 'mbase', b: b, sp: sp, q: q, A: A, B: B, C: Cc, D: D });
  }
  var c42 = [
    [
      function () {   // evaluate b^x exactly
        var q = pick([1, 1, 2, 3]), r, p, inv = false;
        if (q === 1) { r = pick([2, 3, 4, 5, 10]); p = pick([-3, -2, -1, 2, 3]); if (r === 10 && p === 3) p = 2; inv = K.coin() && r < 10 && Math.pow(r, 3) <= 125; }
        else if (q === 2) { r = pick([2, 3, 4, 5]); p = pick([-3, -1, 1, 3]); }
        else { r = pick([2, 3]); p = pick([-2, -1, 1, 2]); }
        var B = inv ? R(1, Math.pow(r, q)) : R(Math.pow(r, q)), x0 = R(p, q), br = inv ? R(1, r) : R(r), val = rpow(br, p);
        var ws = [val.neg(), R(B.n * p, B.d * q), R(1).div(val)];
        var steps = [m('<i>f</i>(' + x0.html() + ') = ' + pw(bh(B), rs(x0))) + '.'];
        if (q > 1) steps.push('The denominator ' + q + ' means a ' + (q === 2 ? 'square' : 'cube') + ' root: the ' + (q === 2 ? 'square' : 'cube') + ' root of ' + B.html() + ' is ' + br.html() + '.');
        steps.push('Raise to the power ' + n(p) + ': ' + m('(' + br.html() + ')' + K.sup(n(p)) + ' = ' + val.html()) + '.');
        if (p < 0) steps.push('A negative exponent gives a reciprocal, never a negative number.');
        return QP({ q: 'For ' + m(fx(pw(bh(B), xi))) + ', find ' + m('<i>f</i>(' + x0.html() + ')') + '. Give an exact answer.', mc: mcR(val, ws), why: steps }, { t: 'evalexp', B: [B.n, B.d], x: [p, q] });
      },
      function () {   // asymptote and range from the equation
        var a = pick([1, 1, 2, 3]), b = pick([R(2), R(3), R(4), R(5), R(1, 2), R(1, 3)]), h = ri(-3, 3), k = rnz(-6, 6);
        function ch(av, up) { return 'Asymptote ' + m('<i>y</i> = ' + n(av)) + '; range ' + m(up ? '(' + n(av) + ', ' + INF + ')' : '(' + NINF + ', ' + n(av) + ')'); }
        var ws = [ch(0, true), ch(-k, true), ch(k, false)]; if (h !== 0 && h !== k && h !== -k) ws.push(ch(h, true));
        return QP({ q: 'What are the horizontal asymptote and the range of ' + m(fx(expF(a, b, h, k))) + '?', mc: mc(ch(k, true), ws),
          why: ['The parent ' + m(pw(bh(b), xi)) + ' has asymptote ' + m('<i>y</i> = 0') + ' and range ' + m('(0, ' + INF + ')') + '.', (function () { var ps = []; if (a !== 1) ps.push('multiplying by ' + a); if (h !== 0) ps.push('shifting ' + (h > 0 ? 'right ' + h : 'left ' + (-h))); var t0 = ps.join(' and '); return ps.length ? t0.charAt(0).toUpperCase() + t0.slice(1) + ' do' + (ps.length === 1 ? 'es' : '') + ' not move the asymptote. ' : ''; })() + (k > 0 ? 'Adding ' + k : 'Subtracting ' + (-k)) + ' moves it to ' + m('<i>y</i> = ' + n(k)) + '.', 'The graph stays above its asymptote, so the range is ' + m('(' + n(k) + ', ' + INF + ')') + '.'] },
          { t: 'asym', a: a, b: [b.n, b.d], h: h, k: k, neg: false });
      },
      function () {   // simple matching bases
        var b = pick([2, 3, 5]), mx = { 2: 6, 3: 4, 5: 3 }[b], nn = ri(2, mx), c = rnz(-4, 4), neg = K.coin(), t = neg ? -nn : nn, V = Math.pow(b, nn);
        var a = t - c;
        return QP({ q: 'Solve: ' + m(pw(b, K.minusH(xi, -c)) + ' = ' + (neg ? K.f(1, V) : n(V))), mc: mcR(a, [t, t + c, neg ? nn - c : V - c], function (h) { return xeq(h); }),
          why: ['Write the right side as a power of ' + b + ': ' + m((neg ? K.f(1, V) : n(V)) + ' = ' + pw(b, n(t))) + '.', 'Same base, so the exponents are equal: ' + m(K.minusH(xi, -c) + ' = ' + n(t)) + '.', xeq(n(t) + K.plusK(-c) + ' = ' + n(a)) + '.'] },
          { t: 'mb1', b: b, c: c, tv: t });
      }
    ],
    [
      function () { return mbGen(false); },
      function () {   // identify the exponential graph
        var b = pick([R(2), R(3), R(1, 2)]), h = rnz(-3, 3), k = rnz(-4, 3), bv = b.val();
        var y0 = Math.min(-2, k - 2), y1 = Math.max(2, k + 7);
        var p2 = bv > 1 ? [h + 1, k + bv] : [h - 1, k + 2];
        var g = graphGrid({ x: [-7, 7], y: [y0, y1], lab: 2, fns: [{ f: function (x) { return Math.pow(bv, x - h) + k; } }], lines: [{ m: 0, b: k, dash: true, color: C.red }], pts: [{ x: h, y: k + 1 }, { x: p2[0], y: p2[1] }] });
        function ch(hh, kk) { return m('<i>y</i> = ' + pw(bh(b), K.minusH(xi, hh)) + K.plusK(kk)); }
        var ws = [ch(-h, k), ch(h, -k)]; if (h !== k) ws.push(ch(k, h)); ws.push(ch(-h, -k));
        return QP({ q: 'Which equation matches the graph? The dashed line is the horizontal asymptote, and two points on the curve are marked.', graph: g, mc: mc(ch(h, k), ws),
          why: ['The asymptote is ' + m('<i>y</i> = ' + n(k)) + ', so the graph was shifted ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + ': the equation ends in ' + m(K.plusK(k)) + '.', 'The parent ' + m(pw(bh(b), xi)) + ' passes through ' + K.pt(0, 1) + '; here that point is at ' + K.pt(h, k + 1) + ', a shift ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + ', so the exponent is ' + m(K.minusH(xi, h)) + '.', 'Check the other marked point: ' + m(pw(bh(b), '(' + n(p2[0]) + ' ' + M + ' ' + sub(h) + ')') + K.plusK(k) + ' = ' + n(p2[1])) + ' ✔'] },
          { t: 'expgraph', b: [b.n, b.d], h: h, k: k, pts: [[h, k + 1], p2], asy: k });
      },
      function () {   // compound interest
        var names = { 1: 'annually', 2: 'semiannually', 4: 'quarterly', 12: 'monthly', 365: 'daily' };
        var Pp, r, nn, t, A;
        do { Pp = 500 * ri(2, 20); r = pick([2, 2.5, 3, 3.5, 4, 4.5, 5, 6]); nn = pick([1, 2, 4, 12, 365]); t = ri(2, 12); A = Pp * Math.pow(1 + r / 100 / nn, nn * t); } while (!safe(A, 2));
        var rd = r / 100;
        var ws = [Pp * Math.pow(1 + rd, nn * t), Pp * Math.pow(1 + rd / nn, t), Pp * (1 + rd * t), Pp * Math.exp(rd * t)];
        return QP({ q: moneyW(Pp) + ' is invested at ' + n(r) + '% interest compounded ' + names[nn] + ' for ' + t + ' years. Find the balance to the nearest cent.', mc: mcN(A, ws, money),
          why: ['Use ' + m('<i>A</i> = <i>P</i>(1 + ' + fr('<i>r</i>', '<i>n</i>') + ')' + K.sup('<i>nt</i>')) + ' with ' + m('<i>P</i> = ' + n(Pp) + ', <i>r</i> = ' + n(rd) + ', <i>n</i> = ' + nn + ', <i>t</i> = ' + t) + '.', m('<i>A</i> = ' + n(Pp) + '(1 + ' + (nn === 1 ? n(rd) : fr(n(rd), nn)) + ')' + K.sup(nn * t)) + (nn > 1 ? '. Divide the rate by ' + m('<i>n</i>') + ' and multiply the time by ' + m('<i>n</i>') + '.' : '.'), m('<i>A</i> ≈ ' + money(A)) + '.'] },
          { t: 'compound', P: Pp, r: rd, n: nn, yrs: t });
      }
    ],
    [
      function () {   // continuous compounding, balance or interest
        var Pp, r, t, A, want = K.coin() ? 'bal' : 'int', v;
        do { Pp = 500 * ri(2, 30); r = pick([2, 2.5, 3, 3.5, 4, 4.5, 5, 5.5, 6, 7]); t = ri(3, 20); A = Pp * Math.exp(r / 100 * t); v = want === 'bal' ? A : A - Pp; } while (!safe(v, 2) || !safe(A, 2));
        var rd = r / 100, sh = want === 'bal' ? 0 : Pp;
        var ws = [Pp * Math.pow(1 + rd, t) - sh, Pp * (1 + rd * t) - sh, Pp * Math.pow(1 + rd / 12, 12 * t) - sh];
        if (want === 'int') ws.unshift(A);
        var steps = ['Continuous compounding: ' + m('<i>A</i> = <i>Pe</i>' + K.sup('<i>rt</i>')) + ' with ' + m('<i>P</i> = ' + n(Pp) + ', <i>r</i> = ' + n(rd) + ', <i>t</i> = ' + t) + '.', m('<i>A</i> = ' + n(Pp) + ex(n(rd) + ' · ' + t)) + ' ' + m('= ' + n(Pp) + ex(n(K.round(rd * t, 6)))) + ' ' + m('≈ ' + money(A)) + '.'];
        if (want === 'int') steps.push('Interest earned = balance − principal: ' + m(money(A) + ' ' + M + ' ' + money(Pp)) + ' ' + m('= ' + money(A - Pp)) + '.');
        return QP({ q: moneyW(Pp) + ' is deposited in an account paying ' + n(r) + '% interest compounded continuously. ' + (want === 'bal' ? 'What is the balance after ' + t + ' years, to the nearest cent?' : 'How much interest is earned in ' + t + ' years, to the nearest cent?'), mc: mcN(v, ws, money), why: steps },
          { t: 'cont', P: Pp, r: rd, yrs: t, want: want });
      },
      function () { return mbGen(true); },
      function () {   // reflected exponential: range and y-intercept
        var a = pick([1, 2, 3]), b = pick([2, 3]), h = ri(-2, 2), k = rnz(-5, 6);
        var pwr = h <= 0 ? R(Math.pow(b, -h)) : R(1, Math.pow(b, h));
        var f0 = pwr.mul(-a).add(k);
        function ch(rk, down, y) { return 'Range ' + m(down ? '(' + NINF + ', ' + n(rk) + ')' : '(' + n(rk) + ', ' + INF + ')') + '; ' + m('<i>y</i>') + '-intercept ' + K.pt(0, y); }
        var cands = [[k, false, f0], [k, true, pwr.mul(a).add(k)], [-k, true, f0]];
        if (h !== 0) cands.push([k, true, R(1).div(pwr).mul(-a).add(k)]);
        cands.push([k, true, pwr.mul(-a).add(-k)]);
        var ws = cands.filter(function (c) { return !(c[0] === k && c[1] === true && R(c[2]).eq(f0)); }).map(function (c) { return ch(c[0], c[1], c[2]); });
        return QP({ q: 'For ' + m(fx(expF(a, R(b), h, k, true))) + ', what are the range and the ' + m('<i>y</i>') + '-intercept?', mc: mc(ch(k, true, f0), ws),
          why: ['The asymptote is ' + m('<i>y</i> = ' + n(k)) + '. The negative sign in front reflects the graph so it lies below the asymptote: range ' + m('(' + NINF + ', ' + n(k) + ')') + '.', m('<i>f</i>(0) = ' + M + (a === 1 ? '' : n(a) + ' · ') + pw(b, n(-h)) + K.plusK(k) + ' = ' + M + (a === 1 ? '' : n(a) + ' · ') + pwr.html() + K.plusK(k) + ' = ' + f0.html()) + '.', 'Range ' + m('(' + NINF + ', ' + n(k) + ')') + '; ' + m('<i>y</i>') + '-intercept ' + K.pt(0, f0) + '.'] },
          { t: 'reflexp', a: a, b: b, h: h, k: k });
      },
      function () {   // exponential function through two points
        var x1 = pick([0, 1]), a = pick([2, 3, 4, 5]), Cc = ri(1, 6), y1, y2;
        do { a = pick([2, 3, 4, 5]); Cc = ri(1, 6); y1 = Cc * Math.pow(a, x1); y2 = Cc * Math.pow(a, x1 + 2); } while (y2 > 1000);
        function fe(cc, aa) { return m(fx((cc === 1 ? '' : n(cc) + ' · ') + pw(n(aa), xi))); }
        var cands = [[Cc, a * a], [y1, a], [a, Cc], [Cc * a, a], [Cc, a + 1]];
        var ws = cands.filter(function (c) { return !(c[0] === Cc && c[1] === a) && c[1] !== 1; }).map(function (c) { return fe(c[0], c[1]); });
        return QP({ q: 'An exponential function ' + m(fx('<i>C</i> · ' + pw('<i>a</i>', xi))) + ' (with ' + m('<i>a</i> &gt; 0') + ') passes through ' + K.pt(x1, y1) + ' and ' + K.pt(x1 + 2, y2) + '. Find ' + m('<i>f</i>(<i>x</i>)') + '.', mc: mc(fe(Cc, a), ws),
          why: ['Divide the outputs: ' + m(fr('<i>f</i>(' + (x1 + 2) + ')', '<i>f</i>(' + x1 + ')') + ' = ' + fr('<i>C</i> · ' + pw('<i>a</i>', x1 + 2), '<i>C</i> · ' + pw('<i>a</i>', x1 === 0 ? '0' : '1')) + ' = ' + pw('<i>a</i>', 2)) + ', so ' + m(pw('<i>a</i>', 2) + ' = ' + fr(n(y2), n(y1)) + ' = ' + a * a) + '.', 'Since ' + m('<i>a</i> &gt; 0') + ', ' + m('<i>a</i> = ' + a) + '. Then ' + m('<i>C</i> = ' + fr(n(y1), pw(a, x1)) + ' = ' + Cc) + '.', fe(Cc, a) + '. Check: ' + m('<i>f</i>(' + (x1 + 2) + ') = ' + (Cc === 1 ? '' : n(Cc) + ' · ') + pw(a, x1 + 2) + ' = ' + n(y2)) + ' ✔'] },
          { t: 'twopt', x1: x1, y1: y1, y2: y2 });
      }
    ]
  ];
  K.lesson('4.2', { title: 'Exponential Functions', std: 'Lial 12e · Section 4.2', levels: c42 });

  /* ---------- 4.3 Logarithmic Functions ---------- */
  var c43 = [
    [
      function () {   // exponential form -> log form
        var b = pick([2, 3, 4, 5, 10]), e;
        do { e = pick([2, 3, 4, -1, -2, -3]); } while (Math.pow(b, Math.abs(e)) > 1000);
        var v = rpow(b, e), vh = v.html(), vin = v.d === 1 ? n(v.n) : '1/' + v.d, par = v.d !== 1;
        function lgs(base, arg, val, p2) { return m(lg(base, arg, p2) + ' = ' + val); }
        var ws = K.shuffle([lgs(b, vh, n(-e), par), lgs(b, n(e), vh, e < 0)].concat(e >= 2 && Math.pow(e, b) !== v.val() ? [lgs(e, vh, n(b), par)] : []).concat(e * e !== 1 ? [lgs(vin, n(b), n(e))] : []));  // log_v b = e would be TRUE when e = ±1
        return QP({ q: 'Write ' + m(pw(b, n(e)) + ' = ' + vh) + ' in logarithmic form.', mc: mc(lgs(b, vh, n(e), par), ws, function (i) { return lgs(b, vh, n(e + (i % 2 ? -1 : 1) * (1 + Math.floor(i / 2))), par); }),
          why: [m(pw(b, n(e)) + ' = ' + vh) + ' says the exponent ' + n(e) + ' on base ' + b + ' gives ' + vh + '.', 'In log form, the base stays the base and the exponent becomes the value of the log: ' + m(lg(b, vh, par) + ' = ' + n(e)) + '.', 'A logarithm is an exponent: ' + m(lg(b, vh, par)) + ' is the power on ' + b + ' that gives ' + vh + '.'] },
          { t: 'tolog', b: b, e: e });
      },
      function () {   // evaluate log_b v
        var r, s, t, b, v;
        do { r = pick([2, 3, 5]); s = pick([1, 1, 2, 3]); t = rnz(-5, 6); b = Math.pow(r, s); } while (b > 125 || Math.pow(r, Math.abs(t)) > 729 || t === s);
        v = rpow(r, t);
        var ans = R(t, s), ws = [ans.neg(), R(s, t), rpow(r, t - s)];
        return QP({ q: 'Evaluate ' + m(lg(b, v.html(), v.d !== 1)) + '. Give an exact answer.', mc: mcR(ans, ws),
          why: [m(lg(b, v.html(), v.d !== 1)) + ' asks: ' + b + ' to what power gives ' + v.html() + '?', s === 1 ? m(v.html() + ' = ' + pw(b, n(t))) + (t < 0 ? ' (a reciprocal means a negative exponent).' : '.') : 'Write both as powers of ' + r + ': ' + m(b + ' = ' + pw(r, s)) + ' and ' + m(v.html() + ' = ' + pw(r, n(t))) + '. Then ' + m('(' + pw(r, s) + ')' + K.sup('<i>y</i>') + ' = ' + pw(r, n(t))) + ' gives ' + m(s + '<i>y</i> = ' + n(t)) + '.', 'So ' + m(lg(b, v.html(), v.d !== 1) + ' = ' + ans.html()) + '.'] },
          { t: 'evallog', b: b, v: [v.n, v.d] });
      },
      function () {   // log_b(x + c) = e
        var b = pick([2, 3, 4, 5]), e, c = rnz(-9, 9);
        do { e = ri(1, 3); } while (Math.pow(b, e) > 125);
        var V = Math.pow(b, e), a = V - c;
        return QP({ q: 'Solve: ' + m(lg(b, K.minusH(xi, -c), true) + ' = ' + e), mc: mcR(a, [V, V + c, b * e - c], function (h) { return xeq(h); }),
          why: ['Exponential form: ' + m(pw(b, e) + ' = ' + K.minusH(xi, -c)) + '.', m(pw(b, e) + ' = ' + V) + ', so ' + m(K.minusH(xi, -c) + ' = ' + V) + ' and ' + xeq(n(a)) + '.', 'Check: ' + m(lg(b, n(a) + K.plusK(c), true) + ' = ' + lg(b, V) + ' = ' + e) + ' ✔ (the argument is positive).'] },
          { t: 'logeq1', b: b, c: c, e: e });
      },
      function () {   // domain of log
        var b = pick([2, 3, 5, 10, 'e']), h = rnz(-7, 7), k;
        do { k = rnz(-6, 6); } while (k === h || k === -h);
        return QP({ q: 'What is the domain of ' + m(fx(lg(b, K.minusH(xi, h), true) + K.plusK(k))) + '?', mc: mc(iv(n(h), INF), [iv(n(h), INF, '['), iv(n(-h), INF), iv(n(k), INF), iv(NINF, n(h))]),
          why: ['You can only take the log of a positive number, so the argument must be positive: ' + m(K.minusH(xi, h) + ' &gt; 0') + '.', 'So ' + m('<i>x</i> &gt; ' + n(h)) + '. The ' + m(K.plusK(k)) + ' shifts the graph vertically and does not change the domain.', 'Domain: ' + iv(n(h), INF) + ', with a parenthesis because ' + m('<i>x</i> = ' + n(h)) + ' would make the argument 0.'] },
          { t: 'logdom', b: b, h: h, k: k });
      }
    ],
    [
      function () {   // identify the log graph
        var b = pick([2, 3]), h = rnz(-4, 2), k = rnz(-3, 3);
        var x0 = Math.min(-2, h - 2), x1 = Math.max(4, h + 10), y0 = Math.min(-2, k - 4), y1 = Math.max(2, k + 4);
        var g = graphGrid({ x: [x0, x1], y: [y0, y1], lab: 2, fns: [{ f: function (x) { return Math.log(x - h) / Math.log(b) + k; }, from: h + 0.0005 }], lines: [{ vx: h, dash: true, color: C.red }], pts: [{ x: h + 1, y: k }, { x: h + b, y: k + 1 }] });
        function ch(hh, kk) { return m('<i>y</i> = ' + lg(b, K.minusH(xi, hh), true) + K.plusK(kk)); }
        var ws = [ch(-h, k), ch(h, -k)]; if (h !== k) ws.push(ch(k, h)); ws.push(ch(-h, -k));
        return QP({ q: 'Which equation matches the graph? The dashed line is the vertical asymptote, and two points on the curve are marked.', graph: g, mc: mc(ch(h, k), ws),
          why: ['The vertical asymptote is ' + m('<i>x</i> = ' + n(h)) + ', so the argument is ' + m(K.minusH(xi, h)) + ' (it is 0 at the asymptote).', 'The parent ' + m(lg(b, xi)) + ' passes through ' + K.pt(1, 0) + '; here that point is ' + K.pt(h + 1, k) + ', so the graph was shifted ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + ': the equation ends in ' + m(K.plusK(k)) + '.', 'Check the other point: ' + m(lg(b, '(' + n(h + b) + ' ' + M + ' ' + sub(h) + ')') + K.plusK(k) + ' = ' + lg(b, b) + K.plusK(k) + ' = ' + n(k + 1)) + ' ✔'] },
          { t: 'loggraph', b: b, h: h, k: k, pts: [[h + 1, k], [h + b, k + 1]], asy: h });
      },
      function () {   // expand
        var b = pick([2, 3, 5, 7]), p = ri(2, 5), q = pick([R(1, 2), R(1), R(2), R(3), R(4)]), r = ri(1, 4);
        var yh = q.eq(R(1, 2)) ? K.sqrt(yi) : K.xp(q.n, 'y');
        var arg = fr(K.xp(p) + yh, K.xp(r, 'z'));
        var co = [R(p), q, R(-r)];
        var cands = [[p, q, r], [1, q, -r], q.eq(R(1, 2)) ? [p, 2, -r] : [p, q, -1], [-p, q.neg(), r], [q, p, -r], [p, q, R(-1, r)]];
        var ws = cands.filter(function (c) { return !eqTriple(c, co); }).map(function (c) { return m(logCombo(b, c, [xi, yi, zi])); });
        return QP({ q: 'Expand ' + m(lg(b, arg, true)) + ' using the properties of logarithms. Assume all variables are positive.', mc: mc(m(logCombo(b, co, [xi, yi, zi])), ws),
          why: ['Quotient property: ' + m(lg(b, K.xp(p) + yh, true) + ' ' + M + ' ' + lg(b, K.xp(r, 'z'))) + '.', 'Product property: ' + m(lg(b, K.xp(p)) + ' + ' + lg(b, yh) + ' ' + M + ' ' + lg(b, K.xp(r, 'z'))) + (q.eq(R(1, 2)) ? ', with ' + m(K.sqrt(yi) + ' = ' + pw(yi, '1/2')) + '.' : '.'), 'Power property: ' + m(logCombo(b, co, [xi, yi, zi])) + '.'] },
          { t: 'expand', b: b, co: co.map(function (c) { return [c.n, c.d]; }) });
      },
      function () {   // condense
        var b = pick([2, 3, 4, 5, 10]), a = ri(2, 4), c = ri(1, 4), d = ri(1, 4);
        var qs = logCombo(b, [a, -c, d], [xi, yi, zi]);
        function L(h) { return m(lg(b, h, true)); }
        var right = L(fr(K.xp(a) + K.xp(d, 'z'), K.xp(c, 'y')));
        var ws = [L(K.xp(a) + K.xp(c, 'y') + K.xp(d, 'z')), L(fr(K.xp(a), K.xp(c, 'y') + K.xp(d, 'z'))), L(fr(n(a) + xi + ' · ' + (d === 1 ? '' : n(d)) + zi, (c === 1 ? '' : n(c)) + yi))];
        if (a !== c) ws.push(L(fr(K.xp(c) + K.xp(d, 'z'), K.xp(a, 'y'))));
        return QP({ q: 'Write as a single logarithm: ' + m(qs) + '. Assume all variables are positive.', mc: mc(right, ws),
          why: ['Power property first: move each coefficient up as an exponent: ' + m(lg(b, K.xp(a)) + ' ' + M + ' ' + lg(b, K.xp(c, 'y')) + ' + ' + lg(b, K.xp(d, 'z'))) + '.', 'Adding logs multiplies: ' + m(lg(b, K.xp(a)) + ' + ' + lg(b, K.xp(d, 'z')) + ' = ' + lg(b, K.xp(a) + K.xp(d, 'z'), true)) + '.', 'Subtracting a log divides: ' + right + '.'] },
          { t: 'condense', b: b, co: [a, -c, d] });
      },
      function () {   // numeric properties
        var sum = K.coin(), b, k, Mv, N;
        if (!sum) {
          do { b = pick([2, 3, 5]); k = ri(1, 3); N = ri(2, 7); Mv = N * Math.pow(b, k); } while (Math.abs(Math.log(N) / Math.log(b) - Math.round(Math.log(N) / Math.log(b))) < 1e-9 || Mv > 500);
        } else {
          var tot, ds;
          do { b = pick([6, 10, 12, 15]); k = b === 10 ? pick([2, 3]) : 2; tot = Math.pow(b, k); ds = []; for (var i = 2; i < tot; i++) if (tot % i === 0 && Math.abs(Math.log(i) / Math.log(b) - Math.round(Math.log(i) / Math.log(b))) > 1e-9) ds.push(i); } while (!ds.length);
          N = pick(ds); Mv = tot / N;
        }
        var expr = sum ? lg(b, n(Mv)) + ' + ' + lg(b, n(N)) : lg(b, n(Mv)) + ' ' + M + ' ' + lg(b, n(N));
        return QP({ q: 'Evaluate without a calculator: ' + m(expr), mc: mcN(k, [Math.pow(b, k), -k, k + 1, 2 * k], n),
          why: [sum ? 'Product property: ' + m(expr) + ' ' + m('= ' + lg(b, n(Mv) + ' · ' + n(N), true)) + ' ' + m('= ' + lg(b, n(Mv * N))) + '.' : 'Quotient property: ' + m(expr) + ' ' + m('= ' + lg(b, fr(n(Mv), n(N)), true)) + ' ' + m('= ' + lg(b, n(Mv / N))) + '.', m(n(sum ? Mv * N : Mv / N) + ' = ' + pw(b, k)) + ', so the value is ' + k + '.', 'Neither log is a whole number by itself; the properties make the problem easy.'] },
          { t: 'lognum', b: b, M: Mv, N: N, sum: sum });
      }
    ],
    [
      function () {   // unknown base
        var frac = K.coin(), a, nn, V, ans, ws, why, rhs;
        if (!frac) {
          do { a = ri(2, 9); nn = pick([2, 3, 4]); V = Math.pow(a, nn); } while (V > 1000);
          ans = a; rhs = n(nn);
          ws = [m('<i>x</i> = ±' + a), xeq(n(-a)), xeq(R(V, nn).html()), xeq(n(V))];
          why = ['Exponential form: ' + m(pw(xi, nn) + ' = ' + n(V)) + '.', 'The real ' + (nn % 2 ? '' : 'positive ') + 'number whose ' + (nn === 2 ? 'square' : nn === 3 ? 'cube' : 'fourth power') + ' is ' + n(V) + ' is ' + a + (nn % 2 ? '.' : '. (' + M + a + ' also works in the equation, but a log base must be positive.)'), 'A base must be positive and not 1, so ' + xeq(n(a)) + '.'];
        } else {
          var c, p, q;
          do { c = pick([2, 3, 4, 5]); p = pick([1, 2, 3, 5]); q = pick([2, 3]); V = Math.pow(c, p); ans = Math.pow(c, q); } while (K.gcd(p, q) !== 1 || V > 250 || ans > 125);
          rhs = R(p, q).html();
          ws = [m('<i>x</i> = ±' + ans), xeq(n(V)), xeq(R(V * q, p).html()), xeq(R(V * p, q).html())];
          why = ['Exponential form: ' + m(pw(xi, p + '/' + q) + ' = ' + n(V)) + '.', (p === 1 ? 'Raise both sides to the power ' + q + ': ' + m('<i>x</i> = ' + pw(n(V), q) + ' = ' + ans) + '.' : 'Raise both sides to the power ' + q + '/' + p + ': ' + m('<i>x</i> = ' + pw(n(V), q + '/' + p)) + '. Since ' + m(n(V) + ' = ' + pw(c, p)) + ', this is ' + m(pw('(' + pw(c, p) + ')', q + '/' + p) + ' = ' + pw(c, q) + ' = ' + ans) + '.'), 'The base ' + ans + ' is positive and not 1, so ' + xeq(n(ans)) + '.'];
        }
        return QP({ q: 'Solve: ' + m(lg(xi, n(V)) + ' = ' + rhs), mc: mc(xeq(n(ans)), ws), why: why }, { t: 'logbase', V: V, rhs: frac ? [p, q] : [nn, 1] });
      },
      function () {   // log_b 2 = A, log_b 3 = B
        var i = ri(1, 4), j = ri(1, 3), mode = pick(['prod', 'prod', 'q23', 'q32']), ci, cj, Nh, N;
        if (mode === 'prod') { ci = i; cj = j; N = Math.pow(2, i) * Math.pow(3, j); Nh = n(N); if (N > 500) { i = 2; ci = 2; N = 4 * Math.pow(3, j); Nh = n(N); } }
        else if (mode === 'q23') { ci = i; cj = -j; Nh = K.f(Math.pow(2, i), Math.pow(3, j)); }
        else { ci = -i; cj = j; Nh = K.f(Math.pow(3, j), Math.pow(2, i)); }
        function lin(a, b2) { return m(P([[a, '<i>A</i>'], [b2, '<i>B</i>']])); }
        var cands = [[cj, ci], [ci, -cj], [-ci, cj], [Math.abs(ci), Math.abs(cj)], [ci + cj, 0]];
        var ws = cands.filter(function (c) { return !(c[0] === ci && c[1] === cj); }).map(function (c) { return lin(c[0], c[1]); });
        ws.splice(1, 0, m(n(Math.abs(ci * cj)) + '<i>AB</i>'));
        var bi = '<i>b</i>';
        return QP({ q: 'Given ' + m(lg(bi, '2') + ' = <i>A</i>') + ' and ' + m(lg(bi, '3') + ' = <i>B</i>') + ', write ' + m(lg(bi, Nh, mode !== 'prod')) + ' in terms of ' + m('<i>A</i>') + ' and ' + m('<i>B</i>') + '.', mc: mc(lin(ci, cj), ws),
          why: ['Factor into 2s and 3s: ' + m(Nh + ' = ' + (mode === 'prod' ? pw(2, i) + ' · ' + pw(3, j) : mode === 'q23' ? fr(pw(2, i), pw(3, j)) : fr(pw(3, j), pw(2, i)))) + '.', (mode === 'prod' ? 'Product property: ' + m(lg(bi, pw(2, i)) + ' + ' + lg(bi, pw(3, j))) : 'Quotient property: ' + m(mode === 'q23' ? lg(bi, pw(2, i)) + ' ' + M + ' ' + lg(bi, pw(3, j)) : lg(bi, pw(3, j)) + ' ' + M + ' ' + lg(bi, pw(2, i)))) + '.', 'Power property: ' + lin(ci, cj) + '.'] },
          { t: 'logAB', ci: ci, cj: cj, N: mode === 'prod' ? [N, 1] : mode === 'q23' ? [Math.pow(2, i), Math.pow(3, j)] : [Math.pow(3, j), Math.pow(2, i)] });
      },
      function () {   // expand a radical quotient
        var b = pick([2, 3, 5, 10]), s = pick([2, 3]), a = ri(1, 5), dd = ri(1, 3), r = ri(1, 4);
        if (a % s === 0 && dd % s === 0) dd = dd === 1 ? 2 : dd - 1;
        var inner = K.xp(a) + K.xp(dd, 'y'), rad = s === 2 ? K.sqrt(inner) : K.cbrt(inner);
        var co = [R(a, s), R(dd, s), R(-r)];
        var cands = [[R(a, s), R(dd), R(-r)], [R(a * s), R(dd * s), R(-r)], [R(a, s), R(dd, s), R(r)], [R(a), R(dd), R(-r, s)]];
        var ws = cands.filter(function (c) { return !eqTriple(c, co); }).map(function (c) { return m(logCombo(b, c, [xi, yi, zi])); });
        return QP({ q: 'Expand ' + m(lg(b, fr(rad, K.xp(r, 'z')), true)) + ' completely. Assume all variables are positive.', mc: mc(m(logCombo(b, co, [xi, yi, zi])), ws),
          why: ['Quotient property: ' + m(lg(b, rad) + ' ' + M + ' ' + lg(b, K.xp(r, 'z'))) + '.', 'A ' + (s === 2 ? 'square' : 'cube') + ' root is the power 1/' + s + ' on everything inside: ' + m(fr('1', s) + ' ' + lg(b, inner, true) + ' = ' + fr('1', s) + '(' + logCombo(b, [a, dd], [xi, yi]) + ')') + '.', 'Distribute and use the power property on ' + m(K.xp(r, 'z')) + ': ' + m(logCombo(b, co, [xi, yi, zi])) + '.'] },
          { t: 'expand', b: b, co: co.map(function (c) { return [c.n, c.d]; }) });
      }
    ]
  ];
  K.lesson('4.3', { title: 'Logarithmic Functions', std: 'Lial 12e · Section 4.3', levels: c43 });

  /* ---------- 4.4 Evaluating Logarithms and the Change-of-Base Theorem ---------- */
  var c44 = [
    [
      function () {   // exact common and natural logs
        var base = K.coin() ? 10 : 'e', kind = pick(['int', 'int', 'half', 'third']), ans, arg, why;
        if (base === 10) {
          if (kind === 'int') { var k = pick([-4, -3, -2, -1, 2, 3, 4, 5]); ans = R(k); arg = k > 0 ? comma(String(Math.pow(10, k))) : '0.' + '0'.repeat(-k - 1) + '1'; why = m(arg + ' = ' + pw(10, n(k))) + '.'; }
          else { var neg = K.coin(); ans = R(neg ? -1 : 1, kind === 'half' ? 2 : 3); var rt = kind === 'half' ? K.sqrt('10') : K.cbrt('10'); arg = neg ? fr('1', rt) : rt; why = m(arg + ' = ' + pw(10, rs(ans))) + ': a root is a fractional exponent' + (neg ? ', and a reciprocal is a negative exponent.' : '.'); }
        } else {
          if (kind === 'int') { var k2 = pick([2, 3, 4, 5, 6, 7]), neg2 = K.coin(); ans = R(neg2 ? -k2 : k2); arg = neg2 ? fr('1', ex(k2)) : ex(k2); why = neg2 ? m(fr('1', ex(k2)) + ' = ' + ex(n(-k2))) + '.' : m('ln ' + ex(k2) + ' = ' + k2) + ' because ln and ' + m(ex(xi)) + ' undo each other.'; }
          else { var neg3 = K.coin(); ans = R(neg3 ? -1 : 1, kind === 'half' ? 2 : 3); var rt2 = kind === 'half' ? K.sqrt('e') : K.cbrt('e'); arg = neg3 ? fr('1', rt2) : rt2; why = m(arg + ' = ' + ex(rs(ans))) + ': a root is a fractional exponent' + (neg3 ? ', and a reciprocal is a negative exponent.' : '.'); }
        }
        var par = /class="fr"/.test(arg);
        var ws = [ans.neg(), ans.add(1), ans.n !== 0 && Math.abs(ans.n) * ans.d !== 1 ? R(ans.d, ans.n) : null, ans.add(-1)];
        return QP({ q: 'Evaluate exactly: ' + m(lg(base, arg, par)), mc: mcR(ans, ws),
          why: [(base === 10 ? m('log') + ' with no base written means base 10: ask 10 to what power gives ' + arg + '.' : m('ln') + ' means base ' + m('e') + ': ask ' + m('e') + ' to what power gives ' + arg + '.'), why, m(lg(base, arg, par) + ' = ' + ans.html()) + '.'] },
          { t: 'exactlog', base: base, ans: [ans.n, ans.d] });
      },
      function () {   // change of base to the nearest hundredth
        var a, x, v;
        do { a = pick([2, 3, 4, 5, 6, 7, 8, 9, 12, 15]); x = ri(2, 500); v = ln(x) / ln(a); } while (Math.abs(v - Math.round(v)) < 0.011 || !safe(v, 2) || x === a);
        return QP({ q: 'Use the change-of-base theorem to evaluate ' + m(lg(a, n(x))) + ' to the nearest hundredth.', mc: mcN(v, [ln(a) / ln(x), x / a, lg10(x / a), ln(x)], function (w) { return dec(w, 2); }),
          why: ['Change of base: ' + m(lg(a, n(x)) + ' = ' + fr('ln ' + n(x), 'ln ' + n(a))) + '. The number goes on top; the base goes in the denominator.', m('ln ' + n(x) + ' ≈ ' + d4(ln(x))) + ' and ' + m('ln ' + n(a) + ' ≈ ' + d4(ln(a))) + '.', 'Divide, then round: ' + m(fr(d4(ln(x)), d4(ln(a))) + ' ≈ ' + dec(v, 2)) + '. Check: ' + m(pw(a, dec(v, 2)) + ' ≈ ' + n(x)) + '.'] },
          { t: 'cob', a: a, x: x });
      },
      function () {   // domain of a log with a linear argument
        var s = pick([1, 2, 3, -1, -2, -3]), c = rnz(-9, 9), base = pick([10, 'e', 2, 5]);
        var r0 = R(-c, s), argH = P([[s, xi], [c, '']]);
        var right = s > 0 ? iv(r0.html(), INF) : iv(NINF, r0.html());
        var ws = [s > 0 ? iv(NINF, r0.html()) : iv(r0.html(), INF), s > 0 ? iv(r0.html(), INF, '[') : iv(NINF, r0.html(), '(', ']'), s > 0 ? iv(r0.neg().html(), INF) : iv(NINF, r0.neg().html())];
        return QP({ q: 'What is the domain of ' + m(fx(lg(base, argH, true))) + '? Write it in interval notation.', mc: mc(right, ws),
          why: ['The argument of a log must be positive: ' + m(argH + ' &gt; 0') + '.', s > 0 ? (s === 1 ? 'So ' + m('<i>x</i> &gt; ' + r0.html()) + '.' : m(P([[s, xi]]) + ' &gt; ' + n(-c)) + ', so ' + m('<i>x</i> &gt; ' + r0.html()) + '.') : m(P([[s, xi]]) + ' &gt; ' + n(-c)) + '. Dividing by ' + n(s) + ' flips the inequality: ' + m('<i>x</i> &lt; ' + r0.html()) + '.', 'Domain: ' + right + '. The endpoint is left out because the log of 0 is not defined.'] },
          { t: 'lindom', s: s, c: c });
      },
      function () {   // which expression equals log_a x
        var a = pick([3, 5, 6, 7]), x = pick([10, 12, 20, 25, 30, 40, 45, 50, 60, 80, 90]);
        var useLn = K.coin();
        var right = m(useLn ? fr('ln ' + x, 'ln ' + a) : fr('log ' + x, 'log ' + a));
        var ws = K.shuffle([m(useLn ? fr('ln ' + a, 'ln ' + x) : fr('log ' + a, 'log ' + x)), m('ln ' + x + ' ' + M + ' ln ' + a), m(fr('log ' + x, 'ln ' + a)), m('ln(' + x + ' ' + M + ' ' + a + ')')]);
        return QP({ q: 'Which expression is equal to ' + m(lg(a, n(x))) + '?', mc: mc(right, ws),
          why: ['The change-of-base theorem: ' + m(lg('<i>a</i>', '<i>x</i>') + ' = ' + fr('ln <i>x</i>', 'ln <i>a</i>') + ' = ' + fr('log <i>x</i>', 'log <i>a</i>')) + '.', 'Both logs must use the same base, and the base (here ' + a + ') goes in the denominator.', 'So ' + m(lg(a, n(x)) + ' = ' + (useLn ? fr('ln ' + x, 'ln ' + a) : fr('log ' + x, 'log ' + a)) + ' ≈ ' + dec(ln(x) / ln(a), 4)) + '. A difference such as ' + m('ln ' + x + ' ' + M + ' ln ' + a) + ' equals ' + m('ln ' + fr(x, a)) + ', which is not the same thing.'] },
          { t: 'cobform', a: a, x: x });
      }
    ],
    [
      function () {   // pH
        var c, k, ph;
        do { c = ri(10, 99) / 10; k = ri(2, 12); ph = k - lg10(c); } while (!safe(ph, 1) || Math.abs(ph - 7) < 0.1 || !safe(-Math.log(c * Math.pow(10, -k)), 1));
        var conc = c * Math.pow(10, -k);
        function ch(v, cls) { return m('pH ≈ ' + dec(v, 1)) + ', ' + (cls || (K.round(v, 1) < 7 ? 'acidic' : 'basic')); }
        var ws = [ch(-ph), ch(ph, ph < 7 ? 'basic' : 'acidic')].concat([-Math.log(conc), k + lg10(c)].filter(function (v) { return dec(v, 1) !== '7.0'; }).map(function (v) { return ch(v); }));
        return QP({ q: 'A solution has ' + m(H3O + ' = ' + c.toFixed(1) + ' × 10' + K.sup(M + k)) + '. Find its pH to the nearest tenth, and decide whether it is acidic or basic.', mc: mc(ch(ph), ws.filter(function (w) { return K.strip(w) !== K.strip(ch(ph)); })),
          why: ['pH ' + m('= ' + M + 'log' + H3O + ' = ' + M + 'log(' + c.toFixed(1) + ' × 10' + K.sup(M + k) + ')') + '.', m('log(' + c.toFixed(1) + ' × 10' + K.sup(M + k) + ') ≈ ' + d4(-ph)) + ', so pH ' + m('≈ ' + d4(ph) + ' ≈ ' + dec(ph, 1)) + '.', 'The pH is ' + (ph < 7 ? 'below' : 'above') + ' 7, so the solution is ' + (ph < 7 ? 'acidic' : 'basic') + '.'] },
          { t: 'ph', c: c, k: k });
      },
      function () {   // decibels
        var c, k, D;
        do { c = ri(3, 19) / 2; k = ri(3, 12); D = 10 * (k + lg10(c)); } while (!safe(D, 0) || c === 1 || !safe(D / 10, 0) || !safe(10 * Math.log(c * Math.pow(10, k)), 0));
        var cs = n(c);
        return QP({ q: 'The decibel rating of a sound with intensity ' + m('<i>I</i>') + ' is ' + m('<i>D</i> = 10 log' + fr('<i>I</i>', I0)) + '. A sound has intensity ' + m('<i>I</i> = ' + cs + ' × 10' + K.sup(k) + ' ' + I0) + '. Find its decibel rating to the nearest whole decibel.', mc: mcN(D, [D / 10, 10 * Math.log(c * Math.pow(10, k)), 10 * k], function (w) { return dec(w, 0) + ' decibels'; }),
          why: [m(fr('<i>I</i>', I0) + ' = ' + cs + ' × 10' + K.sup(k)) + ', so ' + m('<i>D</i> = 10 log(' + cs + ' × 10' + K.sup(k) + ')') + '.', m('log(' + cs + ' × 10' + K.sup(k) + ') ≈ ' + d4(D / 10)) + '. Use log (base 10), not ln.', m('<i>D</i> ≈ 10(' + d4(D / 10) + ') ≈ ' + dec(D, 0)) + ' decibels.'] },
          { t: 'db', c: c, k: k });
      },
      function () {   // domain with a quadratic argument
        var p, q, lead = pick([1, -1]), base = pick([10, 'e', 2, 3]);
        if (K.coin()) { var aa = ri(1, 7); p = -aa; q = aa; } else { do { p = ri(-7, 5); q = ri(-5, 8); } while (q <= p); }
        var argH = P([[lead, K.xp(2)], [-lead * (p + q), xi], [lead * p * q, '']]);
        var uni = ivUnion(n(p), n(q)), mid = iv(n(p), n(q)), uniC = ivUnion(n(p), n(q), true), midC = iv(n(p), n(q), '[', ']');
        var right = lead > 0 ? uni : mid;
        var ws = lead > 0 ? [mid, uniC, iv(n(q), INF)] : [uni, midC, iv(n(p), INF)];
        return QP({ q: 'What is the domain of ' + m(fx(lg(base, argH, true))) + '?', mc: mc(right, ws),
          why: ['The argument must be positive: ' + m(argH + ' &gt; 0') + '.', 'Factor: ' + m((lead < 0 ? M : '') + '(' + K.minusH(xi, p) + ')(' + K.minusH(xi, q) + ') &gt; 0') + '. The zeros are ' + n(p) + ' and ' + n(q) + '.', (lead > 0 ? 'The parabola opens up, so it is positive outside the zeros: ' : 'The parabola opens down, so it is positive between the zeros: ') + right + '. The zeros themselves are excluded.'] },
          { t: 'quaddom', p: p, q: q, lead: lead });
      }
    ],
    [
      function () {   // [H3O+] from pH
        var ph, conc;
        do { ph = ri(10, 139) / 10; conc = Math.pow(10, -ph); } while (Math.round(ph * 10) % 10 === 0 || !sciSafe(conc));
        var ws = [Math.exp(-ph), Math.pow(10, ph), conc * 10];
        var cs = sci(conc);
        var list = ws.map(function (w) { return m(sci(w)); }).filter(function (w) { return K.strip(w) !== K.strip(m(cs)); });
        return QP({ q: 'A solution has pH ' + m(ph.toFixed(1)) + '. Find ' + m(H3O) + ' in moles per liter, in scientific notation with the coefficient rounded to the nearest tenth.', mc: mc(m(cs), list, function (i) { return m(sci(conc * (1 + 0.3 * rnz(1, 5)) * (i % 2 ? 1 : 10))); }),
          why: ['pH ' + m('= ' + M + 'log' + H3O) + ', so ' + m('log' + H3O + ' = ' + M + ph.toFixed(1)) + '.', 'Rewrite in exponential form (base 10): ' + m(H3O + ' = 10' + K.sup(M + ph.toFixed(1))) + '.', m('10' + K.sup(M + ph.toFixed(1)) + ' ≈ ' + cs) + ' moles per liter.'] },
          { t: 'phinv', ph: ph });
      },
      function () {   // intensity ratio from decibels
        var d = pick([20, 30, 40, 50]), D2 = 5 * ri(6, 14), D1 = D2 + d;
        var pair = pick([['A rock concert', 'city traffic'], ['A jet engine nearby', 'a vacuum cleaner'], ['A leaf blower', 'a normal conversation'], ['A chainsaw', 'a quiet office']]);
        var ratio = Math.pow(10, d / 10);
        function tm(h) { return h + ' times'; }
        return QP({ q: pair[0] + ' measures ' + D1 + ' decibels and ' + pair[1] + ' measures ' + D2 + ' decibels. Using ' + m('<i>D</i> = 10 log' + fr('<i>I</i>', I0)) + ', how many times more intense is the louder sound?', mc: mc(tm(comma(String(ratio))), [tm(String(d)), tm(String(d / 10)), tm(m(pw(10, d)))]),
          why: ['Solve ' + m('<i>D</i> = 10 log' + fr('<i>I</i>', I0)) + ' for ' + m('<i>I</i>') + ': ' + m('<i>I</i> = ' + I0 + ' · 10' + K.sup('<i>D</i>/10')) + '.', 'Ratio: ' + m(fr(I0 + ' · 10' + K.sup(D1 + '/10'), I0 + ' · 10' + K.sup(D2 + '/10')) + ' = 10' + K.sup('(' + D1 + ' ' + M + ' ' + D2 + ')/10') + ' = ' + pw(10, d / 10)) + '.', m(pw(10, d / 10) + ' = ' + comma(String(ratio))) + ': every 10 decibels multiplies the intensity by 10.'] },
          { t: 'dbratio', D1: D1, D2: D2 });
      },
      function () {   // domain of a sum of logs
        var lo, hi;
        do { lo = ri(-8, 4); hi = lo + ri(2, 10); } while (lo === 0 || hi === 0 || -lo === hi);
        var a = -lo, b = hi;
        var arg1 = K.minusH(xi, lo), arg2 = P([[b, ''], [-1, xi]]);
        var right = iv(n(lo), n(hi));
        var e1 = Math.min(a, -b), e2 = Math.max(a, -b);
        var ws = [iv(n(lo), n(hi), '[', ']'), ivUnion(n(lo), n(hi)), iv(n(lo), INF)];
        if (e1 !== e2) ws.splice(2, 0, iv(n(e1), n(e2)));
        return QP({ q: 'What is the domain of ' + m(fx(lg(10, arg1, true) + ' + ' + lg('e', arg2, true))) + '?', mc: mc(right, ws),
          why: ['Each log needs a positive argument: ' + m(arg1 + ' &gt; 0') + ' and ' + m(arg2 + ' &gt; 0') + '.', 'So ' + m('<i>x</i> &gt; ' + n(lo)) + ' and ' + m('<i>x</i> &lt; ' + n(hi)) + '.', 'Both must hold at once (the intersection): ' + right + '.'] },
          { t: 'sumdom', lo: lo, hi: hi });
      }
    ]
  ];
  K.lesson('4.4', { title: 'Evaluating Logarithms and the Change-of-Base Theorem', std: 'Lial 12e · Section 4.4', levels: c44 });

  /* ---------- 4.5 Exponential and Logarithmic Equations ---------- */
  function h2(v) { return xap(dec(v, 2)); }
  var c45 = [
    [
      function () {   // a^x = c
        var a, c, v;
        do { a = pick([2, 3, 4, 5, 6, 7]); c = ri(2, 200); v = ln(c) / ln(a); } while (Math.abs(v - Math.round(v)) < 0.011 || !safe(v, 2));
        return QP({ q: 'Solve ' + m(pw(a, xi) + ' = ' + c) + '. Round to the nearest hundredth.', mc: mcN(v, [ln(a) / ln(c), c / a, ln(c), lg10(c / a)], h2),
          why: ['Take ln of both sides: ' + m('ln ' + pw(a, xi) + ' = ln ' + c) + ', so ' + m('<i>x</i> ln ' + a + ' = ln ' + c) + ' (power property).', 'Divide: ' + m('<i>x</i> = ' + fr('ln ' + c, 'ln ' + a) + ' ≈ ' + fr(d4(ln(c)), d4(ln(a))) + ' ≈ ' + d4(v)) + '.', 'To the nearest hundredth, ' + h2(v) + '.'] },
          { t: 'axc', a: a, c: c });
      },
      function () {   // e^(kx) = c
        var k, c, v;
        do { k = pick([0.02, 0.05, 0.08, 0.2, 0.3, 0.4, 0.5, 1.5, 2, 3]); c = ri(2, 50); v = ln(c) / k; } while (!safe(v, 2));
        return QP({ q: 'Solve ' + m(ex(n(k) + xi) + ' = ' + c) + '. Round to the nearest hundredth.', mc: mcN(v, [lg10(c) / k, k * ln(c), c / k], h2),
          why: ['The base is ' + m('e') + ', so take ln of both sides: ' + m(n(k) + '<i>x</i> = ln ' + c) + '.', m('ln ' + c + ' ≈ ' + d4(ln(c))) + ', so ' + m('<i>x</i> = ' + fr('ln ' + c, n(k)) + ' ≈ ' + d4(v)) + '.', 'To the nearest hundredth, ' + h2(v) + '. (Using log instead of ln does not undo base ' + m('e') + '.)'] },
          { t: 'ekx', k: k, c: c });
      },
      function () {   // ln x = d or log x = d
        var useLn = K.coin(), d, v;
        do { d = ri(5, 45) / 10; v = useLn ? Math.exp(d) : Math.pow(10, d); } while (!safe(v, 2) || Math.round(d * 10) % 10 === 0);
        var base = useLn ? Math.E : 10, other = useLn ? Math.pow(10, d) : Math.exp(d);
        var fmt = function (w) { return xap(decc(w, 2)); };
        return QP({ q: 'Solve ' + m((useLn ? 'ln ' : 'log ') + xi + ' = ' + n(d)) + '. Round to the nearest hundredth.', mc: mcN(v, [other, d * base, Math.pow(base, 1 / d)], fmt),
          why: [(useLn ? m('ln <i>x</i>') + ' means base ' + m('e') : m('log <i>x</i>') + ' means base 10') + ', so write the equation in exponential form.', m('<i>x</i> = ' + (useLn ? ex(n(d)) : pw('10', n(d))) + ' ≈ ' + decc(v, 4)) + '.', 'To the nearest hundredth, ' + fmt(v) + '.'] },
          { t: 'lnx', useLn: useLn, d: d });
      },
      function () {   // exact solution form
        var a, c;
        do { a = pick([2, 3, 5, 6, 7]); c = ri(5, 60); } while (Math.abs(ln(c) / ln(a) - Math.round(ln(c) / ln(a))) < 1e-6 || c % a === 0);
        var useLn = K.coin(), L = useLn ? 'ln ' : 'log ';
        var ws = [xeq(fr(L + a, L + c)), xeq(R(c, a).html()), xeq('ln ' + c + ' ' + M + ' ln ' + a)];
        return QP({ q: 'Which is the exact solution of ' + m(pw(a, xi) + ' = ' + c) + '?', mc: mc(xeq(fr(L + c, L + a)), ws),
          why: ['Take ' + L.trim() + ' of both sides: ' + m('<i>x</i> ' + L + a + ' = ' + L + c) + '.', 'Divide by ' + m(L + a) + ': ' + xeq(fr(L + c, L + a)) + '. That is the exact solution (it equals ' + m(lg(a, n(c))) + ').', 'It is about ' + dec(ln(c) / ln(a), 4) + '. Note ' + m('ln ' + c + ' ' + M + ' ln ' + a + ' = ln ' + R(c, a).html()) + ', a different number.'] },
          { t: 'exact', a: a, c: c });
      }
    ],
    [
      function () {   // a^(px+q) = c
        var a, p, q, c, L, v;
        do { a = pick([2, 3, 5, 7]); p = pick([1, 2, 3]); q = rnz(-4, 4); c = ri(5, 200); L = ln(c) / ln(a); v = (L - q) / p; } while (Math.abs(L - Math.round(L)) < 1e-6 || !safe(v, 2));
        var ws = [L / p, (L + q) / p, (ln(c) - q) / (p * ln(a))];
        return QP({ q: 'Solve ' + m(pw(a, P([[p, xi], [q, '']])) + ' = ' + c) + '. Round to the nearest hundredth.', mc: mcN(v, ws, h2),
          why: ['Take ln of both sides; the whole exponent multiplies ln ' + a + ': ' + m('(' + P([[p, xi], [q, '']]) + ') ln ' + a + ' = ln ' + c) + '.', 'Divide: ' + m(P([[p, xi], [q, '']]) + ' = ' + fr('ln ' + c, 'ln ' + a) + ' ≈ ' + d4(L)) + '.', (q > 0 ? 'Subtract ' + q : 'Add ' + (-q)) + (p > 1 ? ', then divide by ' + p : '') + ': ' + m('<i>x</i> ≈ ' + (p > 1 ? fr(d4(L) + K.plusK(-q), p) : d4(L) + K.plusK(-q)) + ' ≈ ' + dec(v, 2)) + '.'] },
          { t: 'axpq', a: a, p: p, q: q, c: c });
      },
      function () {   // log equation with an extraneous root
        var b, nn, N, divs, p;
        do { b = pick([2, 3, 10]); nn = b === 2 ? ri(2, 6) : b === 3 ? ri(2, 4) : ri(1, 2); N = Math.pow(b, nn); divs = []; for (var i = 1; i <= N; i++) if (N % i === 0 && i * i !== N) divs.push(i); } while (!divs.length);
        p = pick(divs);
        var d = N / p - p, q = -N / p;
        var lhs = lg(b, xi) + ' + ' + lg(b, K.minusH(xi, -d), true);
        return QP({ q: 'Solve: ' + m(lhs + ' = ' + nn), mc: mc(xeq(n(p)), [setStr([p, q]), xeq(n(q)), 'No solution']),
          why: ['Product property: ' + m(lg(b, xi + '(' + K.minusH(xi, -d) + ')', true) + ' = ' + nn) + ', so ' + m(P([[1, K.xp(2)], [d, xi]]) + ' = ' + pw(b, nn) + ' = ' + N) + '.', 'Then ' + m(P([[1, K.xp(2)], [d, xi], [-N, '']]) + ' = 0') + ', so ' + m('(' + K.minusH(xi, p) + ')(' + K.minusH(xi, q) + ') = 0') + ': candidates ' + n(p) + ' and ' + n(q) + '.', 'Check: ' + xeq(n(q)) + ' gives ' + m(lg(b, n(q), true)) + ', which is not defined, so it is extraneous. The solution is ' + xeq(n(p)) + '.'] },
          { t: 'logext', b: b, d: d, nn: nn });
      },
      function () {   // quadratic in form with e^x
        var p, q;
        do { p = ri(2, 9); q = ri(2, 9); } while (p === q || !safe(ln(p), 2) || !safe(ln(q), 2));
        var mid = q - p;
        var lhs = ex('2<i>x</i>') + (mid === 0 ? '' : (mid > 0 ? ' + ' : ' ' + M + ' ') + (Math.abs(mid) === 1 ? '' : Math.abs(mid)) + ex(xi)) + ' ' + M + ' ' + p * q;
        return QP({ q: 'Solve ' + m(lhs + ' = 0') + '. Round to the nearest hundredth.', mc: mc(h2(ln(p)), [xeq(n(p)), h2(ln(p)) + ' or ' + h2(ln(q)), 'No real solution']),
          why: ['Let ' + m('<i>u</i> = ' + ex(xi)) + ', so ' + m(ex('2<i>x</i>') + ' = <i>u</i>' + K.sup(2)) + ': ' + m('<i>u</i>' + K.sup(2) + (mid === 0 ? '' : (mid > 0 ? ' + ' : ' ' + M + ' ') + (Math.abs(mid) === 1 ? '' : Math.abs(mid)) + '<i>u</i>') + ' ' + M + ' ' + p * q + ' = 0') + '.', 'Factor: ' + m('(<i>u</i> ' + M + ' ' + p + ')(<i>u</i> + ' + q + ') = 0') + ', so ' + m(ex(xi) + ' = ' + p) + ' or ' + m(ex(xi) + ' = ' + M + q) + '. Since ' + m(ex(xi) + ' &gt; 0') + ' always, reject ' + M + q + '.', m('<i>x</i> = ln ' + p + ' ≈ ' + dec(ln(p), 2)) + '.'] },
          { t: 'qform', p: p, q: q });
      }
    ],
    [
      function () {   // time to reach a target
        var Pp, mult, r, A, cont = K.coin(), nn = pick([4, 12]), t;
        do { Pp = 1000 * ri(1, 20); mult = pick([1.25, 1.5, 1.6, 1.75, 2, 2.5, 3]); r = pick([2.5, 3, 3.5, 4, 4.5, 5, 5.5, 6]) / 100; A = Pp * mult; t = cont ? ln(A / Pp) / r : ln(A / Pp) / (nn * ln(1 + r / nn)); } while (!safe(t, 2));
        var ws = cont ? [lg10(A / Pp) / r, (A / Pp - 1) / r, ln(A - Pp) / r] : [ln(A / Pp) / r, (A / Pp - 1) / r, lg10(A / Pp) / (nn * ln(1 + r / nn)), ln(A / Pp) / ln(1 + r / nn)];
        var nm = nn === 4 ? 'quarterly' : 'monthly';
        var fmt = function (w) { return m(dec(w, 2)) + ' years'; };
        var steps = cont ? ['Use ' + m('<i>A</i> = <i>Pe</i>' + K.sup('<i>rt</i>')) + ': ' + m(n(A) + ' = ' + n(Pp) + ex(n(r) + '<i>t</i>')) + ', so ' + m(ex(n(r) + '<i>t</i>') + ' = ' + n(mult)) + '.', 'Take ln: ' + m(n(r) + '<i>t</i> = ln ' + n(mult)) + ', so ' + m('<i>t</i> = ' + fr('ln ' + n(mult), n(r)) + ' ≈ ' + d4(t)) + '.', 'It takes about ' + fmt(t) + '.'] :
          ['Use ' + m('<i>A</i> = <i>P</i>(1 + ' + fr('<i>r</i>', '<i>n</i>') + ')' + K.sup('<i>nt</i>')) + ': ' + m(n(A) + ' = ' + n(Pp) + '(1 + ' + fr(n(r), nn) + ')' + K.sup(nn + '<i>t</i>')) + ', so ' + m('(1 + ' + fr(n(r), nn) + ')' + K.sup(nn + '<i>t</i>') + ' = ' + n(mult)) + '.', 'Take ln: ' + m(nn + '<i>t</i> · ln(1 + ' + fr(n(r), nn) + ') = ln ' + n(mult)) + '.', m('<i>t</i> = ' + fr('ln ' + n(mult), nn + ' ln(1 + ' + fr(n(r), nn) + ')') + ' ≈ ' + d4(t)) + ', about ' + fmt(t) + '.'];
        return QP({ q: 'How long will it take ' + moneyW(Pp) + ' invested at ' + n(r * 100) + '% interest compounded ' + (cont ? 'continuously' : nm) + ' to grow to ' + moneyW(A) + '? Round to the nearest hundredth of a year.', mc: mcN(t, ws, fmt), why: steps },
          { t: 'ttime', P: Pp, A: A, r: r, n: cont ? 0 : nn });
      },
      function () {   // a^x = b^(x + c)
        var a, b, c, v;
        do { a = pick([2, 3, 4, 5, 6, 7]); b = pick([2, 3, 4, 5, 6, 7]); c = rnz(-3, 3); v = c * ln(b) / (ln(a) - ln(b)); } while (a === b || (a === 2 && b === 4) || (a === 4 && b === 2) || !safe(v, 2));
        var ws = [-v, c / (ln(a) - ln(b)), c * ln(a) / (ln(a) - ln(b))];
        return QP({ q: 'Solve ' + m(pw(a, xi) + ' = ' + pw(b, K.minusH(xi, -c))) + '. Round to the nearest hundredth.', mc: mcN(v, ws, h2),
          why: ['Take ln of both sides: ' + m('<i>x</i> ln ' + a + ' = (' + K.minusH(xi, -c) + ') ln ' + b) + '.', 'Distribute and collect the ' + xi + '-terms: ' + m('<i>x</i> ln ' + a + ' ' + M + ' <i>x</i> ln ' + b + ' = ' + (c === 1 ? '' : c === -1 ? M : n(c)) + 'ln ' + b) + ', so ' + m('<i>x</i> = ' + fr((c === 1 ? '' : c === -1 ? M : n(c)) + 'ln ' + b, 'ln ' + a + ' ' + M + ' ln ' + b)) + '.', m('<i>x</i> ≈ ' + fr(d4(c * ln(b)), d4(ln(a) - ln(b))) + ' ≈ ' + dec(v, 2)) + '.'] },
          { t: 'axbx', a: a, b: b, c: c });
      },
      function () {   // log(x + a) + log(x − c) = log K with an extraneous root
        var a = ri(1, 6), c = ri(1, 6), r = c + ri(1, 6), s = c - a - r, Kv = (r + a) * (r - c), base = pick([10, 'e', 2]);
        var lhs = lg(base, K.minusH(xi, -a), true) + ' + ' + lg(base, K.minusH(xi, c), true);
        return QP({ q: 'Solve: ' + m(lhs + ' = ' + lg(base, n(Kv))), mc: mc(xeq(n(r)), [setStr([r, s]), xeq(n(s)), 'No solution']),
          why: ['Product property: ' + m(lg(base, '(' + K.minusH(xi, -a) + ')(' + K.minusH(xi, c) + ')', true) + ' = ' + lg(base, n(Kv))) + ', so ' + m('(' + K.minusH(xi, -a) + ')(' + K.minusH(xi, c) + ') = ' + Kv) + '.', 'Expand: ' + m(P([[1, K.xp(2)], [a - c, xi], [-a * c - Kv, '']]) + ' = 0') + ', so ' + m('(' + K.minusH(xi, r) + ')(' + K.minusH(xi, s) + ') = 0') + ': candidates ' + n(r) + ' and ' + n(s) + '.', 'Check: ' + xeq(n(s)) + ' makes ' + m(K.minusH(xi, -a) + ' = ' + n(s + a)) + ', and the log of a negative number is not defined, so it is extraneous. The solution is ' + xeq(n(r)) + '.'] },
          { t: 'logext2', a: a, c: c, K: Kv, base: base });
      },
      function () {   // 4^x − S·2^x + P = 0 (exact)
        var B = pick([2, 3]), i, j;
        do { i = ri(0, B === 2 ? 4 : 2); j = ri(0, B === 2 ? 4 : 2); } while (i >= j);
        var S = Math.pow(B, i) + Math.pow(B, j), Pr = Math.pow(B, i + j);
        var ws = [setStr([Math.pow(B, i), Math.pow(B, j)]), setStr([-i, -j].map(function (v) { return v === 0 ? 0 : v; })), xeq(n(j)) + ' only', 'No real solution'];
        return QP({ q: 'Solve: ' + m(pw(B * B, xi) + ' ' + M + ' ' + S + ' · ' + pw(B, xi) + ' + ' + Pr + ' = 0') + '. Give exact answers.', mc: mc(setStr([i, j]), ws),
          why: ['Since ' + m(pw(B * B, xi) + ' = (' + pw(B, xi) + ')' + K.sup(2)) + ', let ' + m('<i>u</i> = ' + pw(B, xi)) + ': ' + m('<i>u</i>' + K.sup(2) + ' ' + M + ' ' + S + '<i>u</i> + ' + Pr + ' = 0') + '.', 'Factor: ' + m('(<i>u</i> ' + M + ' ' + Math.pow(B, i) + ')(<i>u</i> ' + M + ' ' + Math.pow(B, j) + ') = 0') + ', so ' + m(pw(B, xi) + ' = ' + Math.pow(B, i)) + ' or ' + m(pw(B, xi) + ' = ' + Math.pow(B, j)) + '.', 'Write each as a power of ' + B + ': ' + m(Math.pow(B, i) + ' = ' + pw(B, i)) + ' and ' + m(Math.pow(B, j) + ' = ' + pw(B, j)) + ', so ' + setStr([i, j]) + '.'] },
          { t: 'qform2', B: B, S: S, Pr: Pr });
      }
    ]
  ];
  K.lesson('4.5', { title: 'Exponential and Logarithmic Equations', std: 'Lial 12e · Section 4.5', levels: c45 });

  /* ---------- 4.6 Applications and Models of Exponential Growth and Decay ---------- */
  var c46 = [
    [
      function () {   // evaluate a model
        var A0, k, t, v;
        do { A0 = pick([50, 80, 100, 120, 200, 250, 500, 1000]); k = rnz(-12, 12) / 100; t = ri(2, 20); v = A0 * Math.exp(k * t); } while (Math.abs(k) < 0.02 || !safe(v, 1));
        var unit = pick([['grams', 'years'], ['milligrams', 'hours'], ['thousand bacteria', 'hours']]);
        var fmt = function (w) { return m(decc(w, 1)) + ' ' + unit[0]; };
        return QP({ q: 'A quantity is modeled by ' + m('<i>A</i>(<i>t</i>) = ' + A0 + ex(n(k) + '<i>t</i>')) + ' ' + unit[0] + ', with ' + m('<i>t</i>') + ' in ' + unit[1] + '. Find ' + m('<i>A</i>(' + t + ')') + ' to the nearest tenth.', mc: mcN(v, [A0 * Math.exp(-k * t), A0 * Math.exp(k), A0 * Math.pow(1 + k, t)], fmt),
          why: ['Substitute ' + m('<i>t</i> = ' + t) + ': ' + m('<i>A</i>(' + t + ') = ' + A0 + ex('(' + n(k) + ')(' + t + ')') + ' = ' + A0 + ex(n(K.round(k * t, 6)))) + '.', m(ex(n(K.round(k * t, 6))) + ' ≈ ' + dec(Math.exp(k * t), 6)) + ', so ' + m('<i>A</i>(' + t + ') ≈ ' + decc(v, 1)) + '.', (k < 0 ? 'Since ' + m('<i>k</i> &lt; 0') + ', the quantity decays.' : 'Since ' + m('<i>k</i> &gt; 0') + ', the quantity grows.')] },
          { t: 'model', A0: A0, k: k, tt: t });
      },
      function () {   // k from half-life
        var h = pick([3, 5, 6, 8, 10, 12, 15, 20, 25, 28, 30, 45, 50, 64, 75]), k = -ln(2) / h;
        while (!safe(k, 4)) h = pick([5, 8, 12, 20, 30]), k = -ln(2) / h;
        var fmt = function (w) { return m('<i>k</i> ≈ ' + dec(w, 4)); };
        return QP({ q: 'A radioactive substance has a half-life of ' + h + ' years. In the model ' + m('<i>A</i>(<i>t</i>) = <i>A</i><sub>0</sub>' + ex('<i>kt</i>')) + ', find ' + m('<i>k</i>') + ' to the nearest ten-thousandth.', mc: mcN(k, [-k, -lg10(2) / h, -1 / h], fmt),
          why: ['After one half-life, half remains: ' + m(fr('1', '2') + '<i>A</i><sub>0</sub> = <i>A</i><sub>0</sub>' + ex(h + '<i>k</i>')) + ', so ' + m(ex(h + '<i>k</i>') + ' = 0.5') + '.', 'Take ln: ' + m(h + '<i>k</i> = ln 0.5 = ' + M + 'ln 2') + ', so ' + m('<i>k</i> = ' + M + fr('ln 2', h) + ' ≈ ' + dec(k, 6)) + '.', 'Rounded: ' + fmt(k) + '. It is negative because the substance decays.'] },
          { t: 'halfk', h: h });
      },
      function () {   // doubling time
        var k, v, unit = pick(['hours', 'years']);
        do { k = pick([0.02, 0.025, 0.03, 0.035, 0.04, 0.045, 0.05, 0.06, 0.08, 0.12, 0.15, 0.2, 0.25, 0.35]); v = ln(2) / k; } while (!safe(v, 2));
        var fmt = function (w) { return m(dec(w, 2)) + ' ' + unit; };
        return QP({ q: 'A ' + (unit === 'hours' ? 'bacteria culture' : 'population') + ' grows according to ' + m('<i>P</i>(<i>t</i>) = <i>P</i><sub>0</sub>' + ex(n(k) + '<i>t</i>')) + ', with ' + m('<i>t</i>') + ' in ' + unit + '. Find the doubling time to the nearest hundredth.', mc: mcN(v, [2 / k, lg10(2) / k, 1 / k], fmt),
          why: ['Doubling means ' + m('<i>P</i> = 2<i>P</i><sub>0</sub>') + ': ' + m('2<i>P</i><sub>0</sub> = <i>P</i><sub>0</sub>' + ex(n(k) + '<i>t</i>')) + ', so ' + m(ex(n(k) + '<i>t</i>') + ' = 2') + '.', 'Take ln: ' + m(n(k) + '<i>t</i> = ln 2') + ', so ' + m('<i>t</i> = ' + fr('ln 2', n(k)) + ' ≈ ' + d4(v)) + '.', 'Doubling time ≈ ' + fmt(v) + '. The starting amount cancels.'] },
          { t: 'dbl', k: k });
      }
    ],
    [
      function () {   // find k from data, predict
        var P0, g, P1, t1, t2, Y0, k, v;
        do { P0 = 1000 * ri(10, 60); g = ri(3, 25) / 100; P1 = Math.round(P0 * (1 + g) / 100) * 100; t1 = ri(3, 8); t2 = t1 + ri(3, 10); k = ln(P1 / P0) / t1; v = P0 * Math.exp(k * t2); } while (P1 === P0 || !safe(v / 100, 0));
        Y0 = ri(2010, 2018);
        var k10 = lg10(P1 / P0) / t1;
        var fmt = function (w) { return comma(dec(Math.round(w / 100) * 100, 0)) + ' people'; };
        return QP({ q: 'A town had ' + comma(String(P0)) + ' people in ' + Y0 + ' and ' + comma(String(P1)) + ' in ' + (Y0 + t1) + '. Assuming the model ' + m('<i>P</i>(<i>t</i>) = <i>P</i><sub>0</sub>' + ex('<i>kt</i>')) + ', predict the population in ' + (Y0 + t2) + ' to the nearest hundred.', mc: mcN(v, [P0 + (P1 - P0) / t1 * t2, P1 * Math.exp(k * t2), P0 * Math.exp(k10 * t2)], fmt, function (i) { return fmt(v + 100 * rnz(2, 9) * (1 + i)); }),
          why: ['Let ' + m('<i>t</i> = 0') + ' be ' + Y0 + ': ' + m('<i>P</i>(<i>t</i>) = ' + comma(String(P0)) + ex('<i>kt</i>')) + '. In ' + (Y0 + t1) + ', ' + m('<i>t</i> = ' + t1) + ': ' + m(comma(String(P1)) + ' = ' + comma(String(P0)) + ex(t1 + '<i>k</i>')) + '.', m('<i>k</i> = ' + fr('ln(' + comma(String(P1)) + '/' + comma(String(P0)) + ')', t1) + ' ≈ ' + dec(k, 6)) + '. Keep it unrounded.', (Y0 + t2) + ' is ' + m('<i>t</i> = ' + t2) + ': ' + m('<i>P</i>(' + t2 + ') = ' + comma(String(P0)) + ex(t2 + '<i>k</i>') + ' ≈ ' + decc(v, 0)) + ', about ' + fmt(v) + '.'] },
          { t: 'predict', P0: P0, P1: P1, t1: t1, t2: t2 });
      },
      function () {   // carbon dating
        var f, t;
        do { f = pick([5, 10, 15, 20, 25, 30, 35, 40, 45, 55, 60, 65, 70, 75, 80, 85, 90]) / 100; t = -5730 * ln(f) / ln(2); } while (!safe(t / 100, 0));
        var fmt = function (w) { return comma(dec(Math.round(w / 100) * 100, 0)) + ' years'; };
        return QP({ q: 'A bone has ' + Math.round(f * 100) + '% of its original carbon‑14. Carbon‑14 has a half-life of 5730 years. How old is the bone, to the nearest hundred years?', mc: mcN(t, [-5730 * ln(1 - f) / ln(2), 2 * (1 - f) * 5730, -5730 * ln(f)], fmt, function (i) { return fmt(t + 100 * rnz(3, 12) * (1 + i)); }),
          why: ['Half-life 5730: ' + m('<i>k</i> = ' + M + fr('ln 2', '5730') + ' ≈ ' + dec(-ln(2) / 5730, 7)) + '.', n(Math.round(f * 100)) + '% remains: ' + m(n(f) + '<i>A</i><sub>0</sub> = <i>A</i><sub>0</sub>' + ex('<i>kt</i>')) + ', so ' + m('ln ' + n(f) + ' = <i>kt</i>') + '. The starting amount cancels.', m('<i>t</i> = ' + fr('ln ' + n(f), '<i>k</i>') + ' ≈ ' + decc(t, 0)) + ', about ' + fmt(t) + '.'] },
          { t: 'carbon', f: f });
      },
      function () {   // amount left after t, from half-life
        var A0, h, t, v;
        do { A0 = pick([40, 60, 80, 100, 120, 150, 200, 250, 300, 400]); h = ri(3, 30); t = ri(2, 60); v = A0 * Math.pow(0.5, t / h); } while (t % h === 0 || !safe(v, 1) || v < 0.5);
        var lin = A0 * (1 - t / (2 * h));
        var fmt = function (w) { return m(dec(w, 1)) + ' mg'; };
        var ws = [A0 * Math.pow(0.5, h / t), A0 * Math.exp(-t / h)]; if (lin > 0) ws.unshift(lin);
        return QP({ q: 'A hospital isotope has a half-life of ' + h + ' days. A patient receives a ' + A0 + ' mg dose. How much remains after ' + t + ' days, to the nearest tenth of a milligram?', mc: mcN(v, ws, fmt),
          why: ['Half-life ' + h + ': ' + m('<i>k</i> = ' + M + fr('ln 2', h)) + ', so ' + m('<i>A</i>(<i>t</i>) = ' + A0 + ex('(' + M + 'ln 2/' + h + ')<i>t</i>')) + ', which is the same as ' + m(A0 + '(' + fr('1', '2') + ')' + K.sup('<i>t</i>/' + h)) + '.', m('<i>A</i>(' + t + ') = ' + A0 + '(0.5)' + K.sup(t + '/' + h) + ' ≈ ' + A0 + '(' + dec(Math.pow(0.5, t / h), 6) + ')') + '.', m('<i>A</i>(' + t + ') ≈ ' + dec(v, 1)) + ' mg.'] },
          { t: 'halfleft', A0: A0, h: h, tt: t });
      }
    ],
    [
      function () {   // time to reach a target from two data points
        var P0, P1, t1, T, t;
        do { P0 = 100 * ri(2, 20); P1 = Math.round(P0 * (1 + ri(30, 200) / 100) / 10) * 10; t1 = ri(2, 6); T = Math.round(P1 * ri(3, 12) / 100) * 100; t = t1 * ln(T / P0) / ln(P1 / P0); } while (T <= P1 || !safe(t, 1) || !safe(t - t1, 1));
        var fmt = function (w) { return m(dec(w, 1)) + ' hours'; };
        var ws = [t1 * (T - P0) / (P1 - P0), t - t1, t1 * ln(T / P0) / lg10(P1 / P0)];
        var k = ln(P1 / P0) / t1;
        return QP({ q: 'A bacteria culture starts with ' + comma(String(P0)) + ' bacteria and has ' + comma(String(P1)) + ' after ' + t1 + ' hours. Assuming exponential growth ' + m('<i>P</i>(<i>t</i>) = <i>P</i><sub>0</sub>' + ex('<i>kt</i>')) + ', how many hours after the start will it reach ' + comma(String(T)) + ' bacteria? Round to the nearest tenth.', mc: mcN(t, ws, fmt),
          why: ['Find ' + m('<i>k</i>') + ': ' + m(comma(String(P1)) + ' = ' + comma(String(P0)) + ex(t1 + '<i>k</i>')) + ', so ' + m('<i>k</i> = ' + fr('ln(' + comma(String(P1)) + '/' + comma(String(P0)) + ')', t1) + ' ≈ ' + dec(k, 6)) + '.', 'Set ' + m(comma(String(T)) + ' = ' + comma(String(P0)) + ex('<i>kt</i>')) + ': ' + m('<i>t</i> = ' + fr('ln(' + comma(String(T)) + '/' + comma(String(P0)) + ')', '<i>k</i>') + ' ≈ ' + d4(t)) + '.', 'Measured from the start, about ' + fmt(t) + '.'] },
          { t: 'reach', P0: P0, P1: P1, t1: t1, T: T });
      },
      function () {   // Newton's law of cooling
        var Ts, T0, T1, t1, t2, k, v, Dd;
        do { Ts = ri(65, 75); T0 = ri(160, 200); T1 = T0 - ri(15, 40); t1 = ri(4, 10); t2 = t1 + ri(5, 25); Dd = T0 - Ts; k = ln((T1 - Ts) / Dd) / t1; v = Ts + Dd * Math.exp(k * t2); } while (!safe(v, 0));
        var kb = ln(T1 / T0) / t1, lin = T0 - (T0 - T1) / t1 * t2;
        var fmt = function (w) { return dec(w, 0) + '°F'; };
        var ws = [T0 * Math.exp(kb * t2), Dd * Math.exp(k * t2)]; if (lin > 0) ws.push(lin);
        return QP({ q: 'A cup of coffee at ' + T0 + '°F is placed in a ' + Ts + '°F room. After ' + t1 + ' minutes it is ' + T1 + '°F. Using Newton’s law of cooling, ' + m('<i>T</i>(<i>t</i>) = <i>T</i><sub>s</sub> + (<i>T</i><sub>0</sub> ' + M + ' <i>T</i><sub>s</sub>)' + ex('<i>kt</i>')) + ', find its temperature after ' + t2 + ' minutes, to the nearest degree.', mc: mcN(v, ws, fmt, function (i) { return fmt(v + rnz(-9, 9) * (1 + Math.floor(i / 10))); }),
          why: [m('<i>T</i>(<i>t</i>) = ' + Ts + ' + ' + Dd + ex('<i>kt</i>')) + '. At ' + m('<i>t</i> = ' + t1) + ': ' + m(T1 + ' = ' + Ts + ' + ' + Dd + ex(t1 + '<i>k</i>')) + ', so ' + m(ex(t1 + '<i>k</i>') + ' = ' + fr(T1 - Ts, Dd)) + '.', m('<i>k</i> = ' + fr('ln(' + (T1 - Ts) + '/' + Dd + ')', t1) + ' ≈ ' + dec(k, 6)) + '.', m('<i>T</i>(' + t2 + ') = ' + Ts + ' + ' + Dd + ex(t2 + '<i>k</i>') + ' ≈ ' + dec(v, 2)) + ', about ' + fmt(v) + '. Do not forget to add the room temperature back.'] },
          { t: 'cool', Ts: Ts, T0: T0, T1: T1, t1: t1, t2: t2 });
      },
      function () {   // half-life from data
        var A0, A1, t1, h;
        do { A0 = 50 * ri(2, 16); A1 = Math.round(A0 * ri(30, 90) / 100); t1 = ri(2, 20); h = t1 * ln(2) / ln(A0 / A1); } while (A1 * 2 === A0 || !safe(h, 1));
        var fmt = function (w) { return m(dec(w, 1)) + ' days'; };
        var ws = [t1 * ln(A0 / A1) / ln(2), t1 * (A0 / 2) / (A0 - A1), t1 * lg10(2) / ln(A0 / A1)];
        return QP({ q: 'A sample of a radioactive substance decays from ' + A0 + ' grams to ' + A1 + ' grams in ' + t1 + ' days. Assuming ' + m('<i>A</i>(<i>t</i>) = <i>A</i><sub>0</sub>' + ex('<i>kt</i>')) + ', find the half-life to the nearest tenth of a day.', mc: mcN(h, ws, fmt),
          why: [m(A1 + ' = ' + A0 + ex(t1 + '<i>k</i>')) + ', so ' + m('<i>k</i> = ' + fr('ln(' + A1 + '/' + A0 + ')', t1) + ' ≈ ' + dec(ln(A1 / A0) / t1, 6)) + '.', 'Half-life: set ' + m(ex('<i>kt</i>') + ' = 0.5') + ': ' + m('<i>t</i> = ' + fr(M + 'ln 2', '<i>k</i>')) + '.', m('<i>t</i> ≈ ' + fr(M + d4(ln(2)), dec(ln(A1 / A0) / t1, 6)) + ' ≈ ' + d4(h)) + ', about ' + fmt(h) + '.'] },
          { t: 'halfdata', A0: A0, A1: A1, t1: t1 });
      }
    ]
  ];
  K.lesson('4.6', { title: 'Applications and Models of Exponential Growth and Decay', std: 'Lial 12e · Section 4.6', levels: c46 });

  K.review('4', 'Chapter 4 Review: Inverse, Exponential & Logarithmic Functions');
})(typeof window !== 'undefined' ? window.KCEP : globalThis.KCEP);
