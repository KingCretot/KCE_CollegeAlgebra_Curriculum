/* Chapter R — Review of Basic Concepts (Lial, Essentials of College Algebra 12e)
   R.1 Sets · R.2 Real Numbers · R.3 Polynomials · R.4 Factoring · R.5 Rational Expressions · R.6 Rational Exponents · R.7 Radicals */
(function (K) {
  var ri = K.ri, rnz = K.rnz, pick = K.pick, n = K.n, P = K.poly, X = K.x, Y = K.y, Q = K.Q, mc = K.mc, M = K.MINUS, m = K.m, fr = K.frx, R = K.R, xp = K.xp;
  var NE = '≠', EMPTY = '∅', CUP = '∪', CAP = '∩', IN = '∈', NIN = '∉', SUB = '⊆', PR = '′';

  /* ---------- general helpers ---------- */
  function pn(v) { return v < 0 ? '(' + n(v) + ')' : n(v); }                       // parenthesize negatives
  function sg(v) { return v < 0 ? ' ' + M + ' ' + n(-v) : ' + ' + n(v); }           // " + 3" / " − 3"
  function gcd(a, b) { return K.gcd(a, b); }
  function isSq(v) { var s = Math.round(Math.sqrt(v)); return s * s === v; }
  function ipow(b, e) { var r = 1; for (var i = 0; i < e; i++) r *= b; return r; }
  function rat(a, b) { return R(a, b).html(); }
  function money(v) { return K.money(v); }

  /* polynomial arrays c[p] = coefficient of x^p */
  function ph(c, v) { var t = []; for (var p = c.length - 1; p >= 0; p--) t.push([c[p] || 0, xp(p, v)]); return P(t); }
  function trim(r) { while (r.length > 1 && !r[r.length - 1]) r.pop(); return r; }
  function padd(a, b, s) { s = s === undefined ? 1 : s; var r = []; for (var i = 0; i < Math.max(a.length, b.length); i++) r[i] = (a[i] || 0) + s * (b[i] || 0); return trim(r); }
  function pmul(a, b) { var r = []; for (var i = 0; i < a.length; i++) for (var j = 0; j < b.length; j++) r[i + j] = (r[i + j] || 0) + a[i] * (b[j] || 0); for (var k = 0; k < r.length; k++) r[k] = r[k] || 0; return trim(r); }
  function pev(c, x) { var s = 0; for (var i = c.length - 1; i >= 0; i--) s = s * x + (c[i] || 0); return s; }
  function pf(c) { return function (x) { return pev(c, x); }; }
  function lin(a, b, v) { return P([[a, xp(1, v)], [b, '']]); }                     // ax + b
  function bin(a, b, v) { return '(' + lin(a, b, v) + ')'; }

  /* numeric-equality guard: wrong answers that equal the correct expression are dropped */
  var TPOS = [1.37, 2.71, 0.61, 3.19, 1.93], TALL = [1.37, 2.71, -0.83, 3.19, -1.61, 0.61];
  function same(f, g, pts) {
    pts = pts || TALL; var cnt = 0;
    for (var i = 0; i < pts.length; i++) {
      var a = f(pts[i]), b = g(pts[i]);
      if (!isFinite(a) || !isFinite(b)) continue;
      cnt++;
      if (Math.abs(a - b) > 1e-7 * (1 + Math.abs(a))) return false;
    }
    return cnt > 0;
  }
  // c = [html, fn]; wr = array of [html, fn] (fn null → non-expression text, never equal)
  function mcF(c, wr, extra, pts) {
    var kept = [c];
    var dup = function (w) { return kept.some(function (k) { return w[1] && k[1] && same(k[1], w[1], pts); }); };
    var ok = [];
    wr.forEach(function (w) { if (w && !dup(w) && ok.indexOf(w[0]) < 0) { kept.push(w); ok.push(w[0]); } });
    return mc(c[0], ok, extra ? function (i) { var w = extra(i); if (dup(w)) return c[0]; kept.push(w); return w[0]; } : undefined);
  }
  function attach(o, p) { o.p = p; return o; }

  /* monomial with rational coefficient and rational exponents.
     vars = [[name, exp], ...]; posOnly → negative exponents written in the denominator */
  function expS(e) { e = R(e); return e.d === 1 ? n(e.n) : (e.n < 0 ? M : '') + Math.abs(e.n) + '/' + e.d; }
  function vpow(v, e) { e = R(e); if (e.n === 0) return ''; if (e.n === 1 && e.d === 1) return '<i>' + v + '</i>'; return '<i>' + v + '</i><sup>' + expS(e) + '</sup>'; }
  function mono(c, vars, posOnly) {
    c = R(c);
    if (!posOnly) {
      var body = vars.map(function (t) { return vpow(t[0], t[1]); }).join('');
      if (body === '') return c.html();
      return K.coef(c, true) + body;
    }
    var top = '', bot = '';
    vars.forEach(function (t) { var e = R(t[1]); if (e.n > 0) top += vpow(t[0], e); else if (e.n < 0) bot += vpow(t[0], e.neg()); });
    var sgn = c.n < 0 ? M : '', cn = Math.abs(c.n), cd = c.d;
    var T = (cn === 1 && top !== '') ? top : cn + top;
    var B = (cd === 1 && bot !== '') ? bot : (cd === 1 ? '' : cd + bot);
    return B === '' ? sgn + T : sgn + fr(T, B);
  }
  function monoF(c, vars) { c = R(c).val(); return function (x) { var y = 0.53 * x + 1.9, s = c; vars.forEach(function (t) { var e = R(t[1]).val(), b = (t[0] === 'x' || t[0] === 'a') ? x : y; s *= Math.pow(b, e); }); return s; }; }
  var T2 = [1.37, 2.71, 0.61, 3.19, 1.93];

  /* radicals */
  // gap = true: an indexed radical follows a coefficient or variable, so add a small space (keeps 2x ∛5 from reading as 2x³√5)
  function rootH(r, idx, gap) { if (idx === 2) return K.sqrt(r); return '<span class="rad"' + (gap ? ' style="margin-left:.3em"' : '') + '><sup class="ri">' + idx + '</sup>√<span class="rc">' + r + '</span></span>'; }
  function radH(c, r, idx) { idx = idx || 2; if (r === 1) return n(c); var pre = c === 1 ? '' : c === -1 ? M : n(c); return pre + rootH(r, idx, pre !== '' && pre !== M); }
  function sqf(N, idx) { idx = idx || 2; var s = 1, f = N; for (var k = 2; ipow(k, idx) <= f; k++) { var kp = ipow(k, idx); while (f % kp === 0) { f /= kp; s *= k; } } return [s, f]; }
  function cbrtR(v) { return v < 0 ? -Math.pow(-v, 1 / 3) : Math.pow(v, 1 / 3); }
  var SQF = [2, 3, 5, 6, 7, 10, 11, 13, 14, 15];

  /* ================= R.1 SETS ================= */
  function cmp(a, b) { return (typeof a === 'number') ? a - b : (a < b ? -1 : a > b ? 1 : 0); }
  function uniq(a) { var o = []; a.forEach(function (v) { if (o.indexOf(v) < 0) o.push(v); }); return o.sort(cmp); }
  function has(a, v) { return a.indexOf(v) >= 0; }
  function uni(a, b) { return uniq(a.concat(b)); }
  function inter(a, b) { return uniq(a.filter(function (v) { return has(b, v); })); }
  function minus(a, b) { return uniq(a.filter(function (v) { return !has(b, v); })); }
  function range(a, b) { var r = []; for (var i = a; i <= b; i++) r.push(i); return r; }
  function el(v) { return typeof v === 'number' ? n(v) : v; }
  function setH(a) { a = uniq(a); return a.length ? '{' + a.map(el).join(', ') + '}' : EMPTY; }
  function dropOne(a) { var b = a.slice(); b.splice(ri(0, b.length - 1), 1); return b; }
  function setExtra(ans, U) { return function () { if (ans.length > 1 && K.coin()) return setH(dropOne(ans)); var out = minus(U, ans); return out.length ? setH(ans.concat([pick(out)])) : setH(dropOne(ans)); }; }
  var SA = '<i>A</i>', SB = '<i>B</i>', SC = '<i>C</i>', SU = '<i>U</i>', SS = '<i>S</i>', xv = '<i>x</i>';
  function uH(N) { return '{1, 2, 3, …, ' + N + '}'; }
  function sb(body) { return '{' + xv + ' | ' + body + '}'; }

  // set operations shown with A, B (and C); f returns the resulting set
  var OPS2 = [
    { h: SA + PR + ' ' + CAP + ' ' + SB, f: function (S) { return inter(minus(S.U, S.A), S.B); }, w: function (S) { return [SA + PR + ' is everything in ' + SU + ' that is not in ' + SA + ': ' + setH(minus(S.U, S.A)) + '.', 'Now keep only the elements of ' + SA + PR + ' that are also in ' + SB + '.']; } },
    { h: SA + ' ' + CAP + ' ' + SB + PR, f: function (S) { return inter(S.A, minus(S.U, S.B)); }, w: function (S) { return [SB + PR + ' is everything in ' + SU + ' that is not in ' + SB + ': ' + setH(minus(S.U, S.B)) + '.', 'Now keep only the elements of ' + SA + ' that are also in ' + SB + PR + '.']; } },
    { h: SA + PR + ' ' + CUP + ' ' + SB, f: function (S) { return uni(minus(S.U, S.A), S.B); }, w: function (S) { return [SA + PR + ' is everything in ' + SU + ' that is not in ' + SA + ': ' + setH(minus(S.U, S.A)) + '.', 'The union puts together every element of ' + SA + PR + ' and of ' + SB + ', each listed once.']; } },
    { h: SA + ' ' + CUP + ' ' + SB + PR, f: function (S) { return uni(S.A, minus(S.U, S.B)); }, w: function (S) { return [SB + PR + ' is everything in ' + SU + ' that is not in ' + SB + ': ' + setH(minus(S.U, S.B)) + '.', 'The union puts together every element of ' + SA + ' and of ' + SB + PR + ', each listed once.']; } },
    { h: '(' + SA + ' ' + CAP + ' ' + SB + ')' + PR, f: function (S) { return minus(S.U, inter(S.A, S.B)); }, w: function (S) { return ['Work inside the parentheses first: ' + SA + ' ' + CAP + ' ' + SB + ' = ' + setH(inter(S.A, S.B)) + '.', 'The complement is everything in ' + SU + ' that is not in ' + setH(inter(S.A, S.B)) + '.']; } },
    { h: '(' + SA + ' ' + CUP + ' ' + SB + ')' + PR, f: function (S) { return minus(S.U, uni(S.A, S.B)); }, w: function (S) { return ['Work inside the parentheses first: ' + SA + ' ' + CUP + ' ' + SB + ' = ' + setH(uni(S.A, S.B)) + '.', 'The complement is everything in ' + SU + ' that is not in ' + setH(uni(S.A, S.B)) + '.']; } },
    { h: SA + ' ' + CAP + ' ' + SB, f: function (S) { return inter(S.A, S.B); } },
    { h: SA + ' ' + CUP + ' ' + SB, f: function (S) { return uni(S.A, S.B); } },
    { h: SA + PR + ' ' + CAP + ' ' + SB + PR, f: function (S) { return inter(minus(S.U, S.A), minus(S.U, S.B)); } }
  ];
  var OPS3 = [
    { h: '(' + SA + ' ' + CUP + ' ' + SB + ')' + PR + ' ' + CAP + ' ' + SC, f: function (S) { return inter(minus(S.U, uni(S.A, S.B)), S.C); },
      w: function (S) { var u = uni(S.A, S.B), c = minus(S.U, u); return [SA + ' ' + CUP + ' ' + SB + ' = ' + setH(u) + '.', '(' + SA + ' ' + CUP + ' ' + SB + ')' + PR + ' = ' + setH(c) + ', everything in ' + SU + ' not in that union.', 'Intersect with ' + SC + ': keep what is also in ' + setH(S.C) + '.']; } },
    { h: SA + PR + ' ' + CAP + ' (' + SB + ' ' + CUP + ' ' + SC + ')', f: function (S) { return inter(minus(S.U, S.A), uni(S.B, S.C)); },
      w: function (S) { var c = minus(S.U, S.A), u = uni(S.B, S.C); return [SA + PR + ' = ' + setH(c) + '.', SB + ' ' + CUP + ' ' + SC + ' = ' + setH(u) + '.', 'Keep only what is in both of those sets.']; } },
    { h: SA + ' ' + CAP + ' (' + SB + ' ' + CUP + ' ' + SC + ')' + PR, f: function (S) { return inter(S.A, minus(S.U, uni(S.B, S.C))); },
      w: function (S) { var u = uni(S.B, S.C), c = minus(S.U, u); return [SB + ' ' + CUP + ' ' + SC + ' = ' + setH(u) + '.', '(' + SB + ' ' + CUP + ' ' + SC + ')' + PR + ' = ' + setH(c) + '.', 'Intersect with ' + SA + ' = ' + setH(S.A) + '.']; } },
    { h: '(' + SA + ' ' + CUP + ' ' + SC + ') ' + CAP + ' ' + SB + PR, f: function (S) { return inter(uni(S.A, S.C), minus(S.U, S.B)); },
      w: function (S) { var u = uni(S.A, S.C), c = minus(S.U, S.B); return [SA + ' ' + CUP + ' ' + SC + ' = ' + setH(u) + '.', SB + PR + ' = ' + setH(c) + '.', 'Keep only what is in both of those sets.']; } },
    { h: '(' + SA + ' ' + CAP + ' ' + SB + ')' + PR + ' ' + CAP + ' ' + SC, f: function (S) { return inter(minus(S.U, inter(S.A, S.B)), S.C); },
      w: function (S) { var i = inter(S.A, S.B), c = minus(S.U, i); return [SA + ' ' + CAP + ' ' + SB + ' = ' + setH(i) + '.', '(' + SA + ' ' + CAP + ' ' + SB + ')' + PR + ' = ' + setH(c) + '.', 'Intersect with ' + SC + ' = ' + setH(S.C) + '.']; } },
    // distractor-only operations (common slips)
    { h: '', f: function (S) { return inter(uni(S.A, S.B), S.C); } },
    { h: '', f: function (S) { return minus(S.U, inter(uni(S.A, S.B), S.C)); } },
    { h: '', f: function (S) { return inter(S.A, uni(S.B, S.C)); } },
    { h: '', f: function (S) { return uni(minus(S.U, S.A), inter(S.B, S.C)); } },
    { h: '', f: function (S) { return inter(minus(S.U, S.A), inter(S.B, S.C)); } },
    { h: '', f: function (S) { return inter(S.A, uni(minus(S.U, S.B), S.C)); } },
    { h: '', f: function (S) { return inter(S.C, minus(S.U, S.A)); } },
    { h: '', f: function (S) { return inter(S.C, minus(S.U, S.B)); } }
  ];

  var r1 = [
    [ // Level 1
      function () { // set-builder → roster
        var v = ri(0, 2), ans, w, q, why, lo, hi;
        if (v === 0) {
          lo = ri(1, 5); hi = lo + ri(4, 7);
          ans = range(lo + 1, hi - 1); w = [range(lo, hi), range(lo, hi - 1), range(lo + 1, hi)];
          q = 'Write ' + sb(xv + ' is a natural number between ' + lo + ' and ' + hi) + ' in roster form.';
          why = ['Read the bar as “such that.” Natural numbers are 1, 2, 3, …', '“Between ' + lo + ' and ' + hi + '” leaves out both ' + lo + ' and ' + hi + ' themselves.', 'Roster form: ' + setH(ans) + ', a finite set with ' + ans.length + ' elements.'];
        } else if (v === 1) {
          lo = -ri(1, 5); hi = ri(1, 4);
          ans = range(lo, hi - 1); w = [range(lo + 1, hi - 1), range(lo, hi), range(lo + 1, hi)];
          q = 'Write ' + sb(xv + ' is an integer and ' + m(n(lo) + ' ≤ ' + xv + ' &lt; ' + hi)) + ' in roster form.';
          why = ['The symbol ≤ includes ' + n(lo) + ', and the symbol &lt; leaves out ' + hi + '.', 'List every integer from ' + n(lo) + ' up to ' + (hi - 1) + '.', 'Roster form: ' + setH(ans) + '.'];
        } else {
          var N = ri(9, 16), ev = K.coin(), par = ev ? 0 : 1;
          var f = function (a, b) { return range(a, b).filter(function (z) { return z % 2 === par; }); };
          ans = f(1, N - 1); w = [f(1, N), range(1, N - 1).filter(function (z) { return z % 2 !== par; }), ev ? f(0, N - 1) : f(3, N - 1)];
          q = 'Write ' + sb(xv + ' is ' + (ev ? 'an even' : 'an odd') + ' natural number less than ' + N) + ' in roster form.';
          why = ['Natural numbers start at 1 (0 is not a natural number).', '“Less than ' + N + '” leaves out ' + N + ' itself. List the ' + (ev ? 'even' : 'odd') + ' ones: ' + ans.map(n).join(', ') + '.', 'Roster form: ' + setH(ans) + '.'];
        }
        return attach(Q({ q: q, mc: mc(setH(ans), w.map(setH), setExtra(ans, range(-6, 20))), why: why }), { t: 'roster' });
      },
      function () { // union or intersection
        var letters = K.coin(), pool = letters ? 'abcdefgh'.split('') : range(1, 12), A, B, I;
        do { A = uniq(K.sample(pool, ri(3, 5))); B = uniq(K.sample(pool, ri(3, 5))); I = inter(A, B); } while (I.length < 1 || I.length === A.length || I.length === B.length);
        var cap = K.coin(), U = uni(A, B), ans = cap ? I : U;
        var w = [cap ? U : I, minus(A, B), minus(B, A), uni(minus(A, B), minus(B, A))];
        var op = SA + ' ' + (cap ? CAP : CUP) + ' ' + SB;
        var why = cap ? ['The intersection ' + SA + ' ' + CAP + ' ' + SB + ' keeps only the elements that are in <b>both</b> sets.', 'Check each element of ' + SA + ' against ' + SB + ': ' + I.map(el).join(', ') + (I.length > 1 ? ' are' : ' is') + ' in both.', SA + ' ' + CAP + ' ' + SB + ' = ' + setH(I) + '.']
          : ['The union ' + SA + ' ' + CUP + ' ' + SB + ' holds every element that is in <b>either</b> set.', 'Elements in both sets (' + I.map(el).join(', ') + ') are listed only once.', SA + ' ' + CUP + ' ' + SB + ' = ' + setH(U) + '.'];
        return attach(Q({ q: 'Let ' + SA + ' = ' + setH(A) + ' and ' + SB + ' = ' + setH(B) + '. Find ' + op + '.', mc: mc(setH(ans), w.map(setH), setExtra(ans, pool)), why: why }), { t: 'set', sets: { A: A, B: B, U: pool }, op: op });
      },
      function () { // number of subsets
        var nEl = ri(3, 6), letters = K.coin(), S = letters ? 'abcdefghjk'.split('').slice(0, 10) : range(1, 15);
        S = uniq(K.sample(S, nEl));
        var ans = ipow(2, nEl);
        return attach(Q({ q: 'How many subsets does ' + setH(S) + ' have?', mc: K.mcNum(ans, [2 * nEl, ans - 1, nEl * nEl, ipow(2, nEl - 1)]), why: ['Count the elements: the set has ' + nEl + ' elements.', 'A set with ' + m('<i>n</i>') + ' elements has ' + m('2<sup><i>n</i></sup>') + ' subsets, counting ' + EMPTY + ' and the set itself.', m('2<sup>' + nEl + '</sup> = ' + ans) + ' subsets.'] }), { t: 'count', mode: 'all' });
      }
    ],
    [ // Level 2
      function () { // complement combined with ∩ / ∪
        var N = pick([10, 12]), U = range(1, N), S, op, ans;
        do {
          S = { U: U, A: uniq(K.sample(U, ri(4, 6))), B: uniq(K.sample(U, ri(4, 6))) };
          op = pick(OPS2.slice(0, 6)); ans = op.f(S);
        } while (ans.length < 1 || ans.length > 8 || inter(S.A, S.B).length === 0);
        var w = K.shuffle(OPS2.filter(function (o) { return o !== op; })).map(function (o) { return setH(o.f(S)); });
        var why = op.w(S).concat([op.h + ' = ' + setH(ans) + '.']);
        return attach(Q({ q: 'Let ' + SU + ' = ' + uH(N) + ', ' + SA + ' = ' + setH(S.A) + ', and ' + SB + ' = ' + setH(S.B) + '. Find ' + op.h + '.', mc: mc(setH(ans), w, setExtra(ans, U)), why: why }), { t: 'set', sets: S, op: op.h });
      },
      function () { // which statement is true (∈, ∉, ⊆)
        var S = uniq(K.sample(range(1, 9), 4)), out = minus(range(1, 9), S);
        var e = pick(S), e2 = pick(S.filter(function (z) { return z !== e; })), f = pick(out), pair = uniq([e, e2]);
        var sS = SS;
        var T = [
          [m(n(e) + ' ' + IN + ' ' + sS), n(e) + ' is listed in ' + sS + ', so ' + n(e) + ' is an element of ' + sS + '.'],
          [m(n(f) + ' ' + NIN + ' ' + sS), n(f) + ' is not listed in ' + sS + ', so ' + n(f) + ' is not an element of ' + sS + '.'],
          [m(EMPTY + ' ' + SUB + ' ' + sS), 'The empty set is a subset of every set.'],
          [m(setH(pair) + ' ' + SUB + ' ' + sS), 'Both ' + n(pair[0]) + ' and ' + n(pair[1]) + ' are in ' + sS + ', so ' + setH(pair) + ' is a subset of ' + sS + '.']
        ];
        var F = [m('{' + n(e) + '} ' + IN + ' ' + sS), m(n(e) + ' ' + SUB + ' ' + sS), m(n(f) + ' ' + IN + ' ' + sS), m(setH([e, f]) + ' ' + SUB + ' ' + sS), m(sS + ' ' + SUB + ' ' + setH(pair)), m(n(e) + ' ' + NIN + ' ' + sS)];
        var t = pick(T), wr = K.sample(F, 3);
        return attach(Q({ q: 'Let ' + SS + ' = ' + setH(S) + '. Which statement is true?', mc: mc(t[0], wr), why: [IN + ' connects an <b>element</b> to a set; ' + SUB + ' connects a <b>set</b> to a set.', t[1], 'Each other statement either uses the wrong symbol (a set written with ' + IN + ', or a number written with ' + SUB + ') or claims something about an element that is not true.'] }), { t: 'truth', S: S });
      },
      function () { // count subsets of a set given in set-builder form
        var v = K.coin(), lo, hi, S, q1;
        if (v) { lo = -ri(1, 4); hi = lo + ri(2, 5); S = range(lo, hi); q1 = sb(xv + ' is an integer and ' + m(n(lo) + ' ≤ ' + xv + ' ≤ ' + n(hi))); }
        else { lo = ri(1, 6); hi = lo + ri(4, 7); S = range(lo + 1, hi - 1); q1 = sb(xv + ' is a natural number between ' + lo + ' and ' + hi); }
        var k = S.length, proper = K.coin(), ans = ipow(2, k) - (proper ? 1 : 0);
        return attach(Q({ q: 'How many ' + (proper ? '<b>proper</b> subsets' : 'subsets') + ' does ' + q1 + ' have?' + (proper ? ' (A proper subset is any subset except the set itself.)' : ''), mc: K.mcNum(ans, [proper ? ipow(2, k) : ipow(2, k) - 1, ipow(2, k + 1), ipow(2, k - 1), 2 * k]), why: ['Write the set in roster form first: ' + setH(S) + ', which has ' + k + ' elements.', 'It has ' + m('2<sup>' + k + '</sup> = ' + ipow(2, k)) + ' subsets' + (proper ? '.' : ', counting ' + EMPTY + ' and the set itself.'), proper ? 'A proper subset is any subset except the set itself, so there are ' + m(ipow(2, k) + ' ' + M + ' 1 = ' + ans) + '.' : 'Answer: ' + ans + ' subsets.'] }), { t: 'count', mode: proper ? 'proper' : 'all' });
      }
    ],
    [ // Level 3
      function () { // three-set expressions
        var U = range(1, 12), S, op, ans;
        do {
          S = { U: U, A: uniq(K.sample(U, ri(4, 6))), B: uniq(K.sample(U, ri(4, 6))), C: uniq(K.sample(U, ri(4, 6))) };
          op = pick(OPS3.slice(0, 5)); ans = op.f(S);
        } while (ans.length < 1 || ans.length > 7);
        var w = K.shuffle(OPS3.filter(function (o) { return o !== op; })).map(function (o) { return setH(o.f(S)); });
        return attach(Q({ q: 'Let ' + SU + ' = ' + uH(12) + ', ' + SA + ' = ' + setH(S.A) + ', ' + SB + ' = ' + setH(S.B) + ', and ' + SC + ' = ' + setH(S.C) + '. Find ' + op.h + '.', mc: mc(setH(ans), w, setExtra(ans, U)), why: op.w(S).concat([op.h + ' = ' + setH(ans) + '.']) }), { t: 'set', sets: S, op: op.h });
      },
      function () { // multiples inside a universal set
        var N, p, q, A, B, U, op, ans, opi;
        do {
          N = ri(20, 30); var pq = K.sample([2, 3, 4, 5, 6, 7], 2); p = pq[0]; q = pq[1]; U = range(1, N);
          A = U.filter(function (z) { return z % p === 0; }); B = U.filter(function (z) { return z % q === 0; });
          opi = ri(0, 2);
          ans = opi === 0 ? inter(A, B) : opi === 1 ? minus(A, B) : minus(B, A);
        } while (ans.length < 1 || ans.length > 9 || inter(A, B).length < 1);
        op = [SA + ' ' + CAP + ' ' + SB, SA + ' ' + CAP + ' ' + SB + PR, SA + PR + ' ' + CAP + ' ' + SB][opi];
        var all = [inter(A, B), minus(A, B), minus(B, A), uni(A, B), minus(U, uni(A, B))];
        var w = all.filter(function (s, i) { return i !== opi; }).map(setH);
        var why = [SA + ' = ' + setH(A) + ' and ' + SB + ' = ' + setH(B) + '.',
          opi === 0 ? 'The intersection keeps the numbers that are multiples of both ' + p + ' and ' + q + '.' : opi === 1 ? SA + ' ' + CAP + ' ' + SB + PR + ' keeps the multiples of ' + p + ' that are <b>not</b> multiples of ' + q + '.' : SA + PR + ' ' + CAP + ' ' + SB + ' keeps the multiples of ' + q + ' that are <b>not</b> multiples of ' + p + '.',
          op + ' = ' + setH(ans) + '.'];
        return attach(Q({ q: 'Let ' + SU + ' = ' + uH(N) + ', ' + SA + ' = ' + sb(xv + ' ' + IN + ' ' + SU + ' and ' + xv + ' is a multiple of ' + p) + ', and ' + SB + ' = ' + sb(xv + ' ' + IN + ' ' + SU + ' and ' + xv + ' is a multiple of ' + q) + '. Find ' + op + '.', mc: mc(setH(ans), w, setExtra(ans, U)), why: why }), { t: 'mult', N: N, p: p, q: q, op: op });
      },
      function () { // counting subsets: of a union, or containing a given element
        if (K.coin()) {
          var pool = 'abcdefgh'.split(''), A, B, Un;
          do { A = uniq(K.sample(pool, ri(2, 4))); B = uniq(K.sample(pool, ri(2, 4))); Un = uni(A, B); } while (inter(A, B).length < 1 || Un.length < 3 || Un.length > 6);
          var k = Un.length, ans = ipow(2, k);
          return attach(Q({ q: 'Let ' + SA + ' = ' + setH(A) + ' and ' + SB + ' = ' + setH(B) + '. How many subsets does ' + SA + ' ' + CUP + ' ' + SB + ' have?', mc: K.mcNum(ans, [ipow(2, A.length) + ipow(2, B.length), ipow(2, A.length + B.length), ipow(2, inter(A, B).length), ans - 1]), why: [SA + ' ' + CUP + ' ' + SB + ' = ' + setH(Un) + '. Shared elements are listed once, so it has ' + k + ' elements.', 'A set with ' + k + ' elements has ' + m('2<sup>' + k + '</sup>') + ' subsets.', m('2<sup>' + k + '</sup> = ' + ans) + '.'] }), { t: 'count', mode: 'union' });
        }
        var nEl = ri(3, 6), S = uniq(K.sample(range(1, 12), nEl)), e = pick(S), ans2 = ipow(2, nEl - 1);
        return attach(Q({ q: 'How many subsets of ' + setH(S) + ' contain the element ' + n(e) + '?', mc: K.mcNum(ans2, [ipow(2, nEl), ipow(2, nEl) - 1, nEl, ans2 - 1]), why: ['Every subset that contains ' + n(e) + ' is ' + n(e) + ' together with a subset of the other ' + (nEl - 1) + ' elements.', 'The other ' + (nEl - 1) + ' elements have ' + m('2<sup>' + (nEl - 1) + '</sup> = ' + ans2) + ' subsets.', 'So ' + ans2 + ' subsets contain ' + n(e) + ' (exactly half of all ' + ipow(2, nEl) + ').'] }), { t: 'count', mode: 'contain', e: e });
      }
    ]
  ];
  K.lesson('R.1', { title: 'Sets', std: 'Lial 12e · Section R.1', levels: r1 });

  /* ================= R.2 REAL NUMBERS ================= */
  function ovl(d) { return '<span style="text-decoration:overline">' + d + '</span>'; }
  // number items: [html, class]  classes: nat, zero, neg, ratn (rational, not an integer), irr
  function itemOf(cls, disguise) {
    var k, s;
    switch (cls) {
      case 'nat': s = ri(2, 9); return disguise ? pick([K.sqrt(s * s), fr(s * (k = ri(2, 4)), k)]) : n(ri(1, 12));
      case 'zero': return disguise ? fr('0', ri(2, 9)) : '0';
      case 'neg': s = ri(2, 9); return disguise ? pick([M + K.sqrt(s * s), M + fr(s * (k = ri(2, 4)), k)]) : n(-ri(1, 12));
      case 'ratn': {
        var t = ri(0, 3);
        if (t === 0) { var q = ri(2, 9), p; do { p = ri(1, 11); } while (gcd(p, q) !== 1 || p % q === 0); return (K.coin() ? M : '') + fr(p, q); }
        if (t === 1) return pick(['0.75', '1.25', '0.7', '3.4', M + '2.5', M + '0.6']);
        if (t === 2) return '0.' + ovl(pick([1, 2, 3, 4, 5, 6, 7, 8]));
        return M + '0.' + ovl(pick([3, 6]));
      }
      case 'irr': { var r; do { r = ri(2, 40); } while (isSq(r)); var u = ri(0, 4); return u === 0 ? 'π' : u === 1 ? fr(K.sqrt(r), ri(2, 5)) : K.sqrt(r); }
    }
  }
  var CLASSQ = {
    nat: ['a natural number', 'Natural numbers are 1, 2, 3, …'],
    zero: ['a whole number but not a natural number', 'Whole numbers are 0, 1, 2, …; the only whole number that is not natural is 0.'],
    neg: ['an integer but not a whole number', 'Integers that are not whole numbers are the negative integers: −1, −2, −3, …'],
    ratn: ['a rational number but not an integer', 'A rational number is a quotient of integers; its decimal ends or repeats. It must not simplify to an integer.'],
    irr: ['a real number but not a rational number', 'Irrational numbers have decimals that never end and never repeat, such as π or the square root of a number that is not a perfect square.']
  };
  function classNote(cls) { return { nat: 'a natural number', zero: 'zero (whole, not natural)', neg: 'a negative integer', ratn: 'a rational number that is not an integer', irr: 'irrational' }[cls]; }

  // property statements
  function propStmt() {
    var a = ri(2, 9), b = ri(2, 9), V = '<i>' + pick(['x', 'y', 'z']) + '</i>', t = ri(0, 8), s, name;
    while (b === a) b = ri(2, 9);
    switch (t) {
      case 0: s = n(a) + ' + ' + n(b) + V + ' = ' + n(b) + V + ' + ' + n(a); name = 'Commutative property of addition'; break;
      case 1: s = K.coin() ? n(a) + ' · ' + V + ' = ' + V + ' · ' + n(a) : '(' + V + ' + ' + n(b) + ') · ' + n(a) + ' = ' + n(a) + '(' + V + ' + ' + n(b) + ')'; name = 'Commutative property of multiplication'; break;
      case 2: s = '(' + n(a) + ' + ' + V + ') + ' + n(b) + ' = ' + n(a) + ' + (' + V + ' + ' + n(b) + ')'; name = 'Associative property of addition'; break;
      case 3: s = '(' + n(a) + ' · ' + n(b) + ')' + V + ' = ' + n(a) + '(' + n(b) + V + ')'; name = 'Associative property of multiplication'; break;
      case 4: s = K.coin() ? n(a) + '(' + V + ' + ' + n(b) + ') = ' + n(a) + V + ' + ' + n(a * b) : n(a) + V + ' + ' + n(b) + V + ' = (' + n(a) + ' + ' + n(b) + ')' + V; name = 'Distributive property'; break;
      case 5: s = K.coin() ? V + ' + 0 = ' + V : '0 + ' + n(b) + V + ' = ' + n(b) + V; name = 'Identity property of addition'; break;
      case 6: s = K.coin() ? '1 · ' + V + ' = ' + V : n(b) + V + ' · 1 = ' + n(b) + V; name = 'Identity property of multiplication'; break;
      case 7: s = n(b) + V + ' + (' + M + n(b) + V + ') = 0'; name = 'Inverse property of addition'; break;
      default: { var p = ri(2, 9), q; do { q = ri(2, 9); } while (q === p); s = fr(p, q) + ' · ' + fr(q, p) + ' = 1'; name = 'Inverse property of multiplication'; }
    }
    return [s, name];
  }
  var PROPS = ['Commutative property of addition', 'Commutative property of multiplication', 'Associative property of addition', 'Associative property of multiplication', 'Distributive property', 'Identity property of addition', 'Identity property of multiplication', 'Inverse property of addition', 'Inverse property of multiplication'];
  var PROPWHY = {
    'Commutative property of addition': 'Only the <b>order</b> of the two terms being added changed: ' + m('<i>a</i> + <i>b</i> = <i>b</i> + <i>a</i>') + '.',
    'Commutative property of multiplication': 'Only the <b>order</b> of the two factors changed: ' + m('<i>ab</i> = <i>ba</i>') + '.',
    'Associative property of addition': 'The order stayed the same; only the <b>grouping</b> of the sum changed: ' + m('(<i>a</i> + <i>b</i>) + <i>c</i> = <i>a</i> + (<i>b</i> + <i>c</i>)') + '.',
    'Associative property of multiplication': 'The order stayed the same; only the <b>grouping</b> of the product changed: ' + m('(<i>ab</i>)<i>c</i> = <i>a</i>(<i>bc</i>)') + '.',
    'Distributive property': 'Multiplication is spread over a sum (or a common factor is pulled out of one): ' + m('<i>a</i>(<i>b</i> + <i>c</i>) = <i>ab</i> + <i>ac</i>') + '.',
    'Identity property of addition': 'Adding 0 leaves a number unchanged: ' + m('<i>a</i> + 0 = <i>a</i>') + '.',
    'Identity property of multiplication': 'Multiplying by 1 leaves a number unchanged: ' + m('<i>a</i> · 1 = <i>a</i>') + '.',
    'Inverse property of addition': 'A number plus its opposite is 0: ' + m('<i>a</i> + (' + M + '<i>a</i>) = 0') + '.',
    'Inverse property of multiplication': 'A nonzero number times its reciprocal is 1: ' + m('<i>a</i> · ' + fr('1', '<i>a</i>') + ' = 1') + '.'
  };

  var r2 = [
    [ // Level 1
      function () { // which is irrational / rational
        var askIrr = K.coin(), c, w;
        if (askIrr) { c = itemOf('irr'); w = [itemOf('nat', true), itemOf('ratn'), itemOf(pick(['ratn', 'neg']), K.coin())]; }
        else {
          c = itemOf(pick(['nat', 'neg', 'ratn', 'ratn']), true);
          var rs = K.sample([2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 15, 17, 19, 20], 2);
          w = [K.sqrt(rs[0]), 'π', fr(K.sqrt(rs[1]), ri(2, 5))];
        }
        var why = askIrr ? ['An irrational number’s decimal never ends and never repeats. A square root is irrational only when the number under it is not a perfect square.', m(c) + ' is irrational.', 'The others are rational: square roots of perfect squares are integers, fractions of integers are rational, and decimals that end or repeat are rational.']
          : ['A rational number can be written as a quotient of integers; its decimal ends or repeats.', m(c) + ' is rational (simplify it first if it is a square root or a fraction).', 'The others are irrational: π and square roots of numbers that are not perfect squares never end or repeat.'];
        return attach(Q({ q: 'Which number is ' + (askIrr ? '<b>irrational</b>' : '<b>rational</b>') + '?', mc: mc(m(c), w.map(m), function () { return m(askIrr ? itemOf(pick(['nat', 'neg', 'ratn', 'zero']), K.coin()) : (function () { var r; do { r = ri(2, 60); } while (isSq(r)); return K.sqrt(r); })()); }), why: why }), { t: 'classify', cls: askIrr ? 'irr' : 'rat' });
      },
      function () { // order of operations, simple
        var eh, val, wr, why;
        if (K.coin()) {
          var a = ri(1, 9), b = ri(2, 5), c = ri(2, 4), e = ri(2, 5), d = e * ri(1, 6);
          eh = n(a) + ' + ' + n(b) + ' · ' + n(c) + '<sup>2</sup> ' + M + ' ' + n(d) + ' ÷ ' + n(e);
          val = a + b * c * c - d / e;
          wr = [(a + b) * c * c - d / e, a + (b * c) * (b * c) - d / e, b * c * c - d / e, a + b * c * c - d];
          why = ['Exponents first: ' + m(n(c) + '<sup>2</sup> = ' + c * c) + '.', 'Multiply and divide: ' + m(n(b) + ' · ' + c * c + ' = ' + b * c * c) + ' and ' + m(n(d) + ' ÷ ' + n(e) + ' = ' + d / e) + '.', 'Add and subtract left to right: ' + m(n(a) + ' + ' + b * c * c + ' ' + M + ' ' + d / e + ' = ' + n(val)) + '.'];
        } else {
          var a2 = ri(2, 7), b2; do { b2 = ri(2, 7); } while (b2 === a2);
          eh = M + n(a2) + '<sup>2</sup> + (' + M + n(b2) + ')<sup>2</sup>';
          val = -a2 * a2 + b2 * b2;
          wr = [a2 * a2 + b2 * b2, -a2 * a2 - b2 * b2, a2 * a2 - b2 * b2];
          why = ['In ' + m(M + n(a2) + '<sup>2</sup>') + ' the exponent applies only to ' + a2 + ': ' + m(M + n(a2) + '<sup>2</sup> = ' + M + a2 * a2) + '.', 'In ' + m('(' + M + n(b2) + ')<sup>2</sup>') + ' the parentheses square the negative: ' + m('(' + M + n(b2) + ')<sup>2</sup> = ' + b2 * b2) + '.', m(M + a2 * a2 + ' + ' + b2 * b2 + ' = ' + n(val)) + '.'];
        }
        return attach(Q({ q: 'Evaluate ' + m(eh) + '.', mc: K.mcNum(val, wr), why: why }), { t: 'num', eh: eh });
      },
      function () { // distance on the number line
        var a, b; do { a = ri(-9, 9); b = ri(-9, 9); } while (a === b || (a >= 0 && b >= 0) || Math.abs(a - b) < 3);
        var lo = Math.min(a, b), hi = Math.max(a, b), d = hi - lo, wr = [Math.abs(a + b), -d, d + 1, d - 1];
        var why = ['Distance between two numbers is the absolute value of their difference: ' + m('|<i>b</i> ' + M + ' <i>a</i>|') + '.', m('|' + n(hi) + ' ' + M + ' ' + pn(lo) + '| = |' + n(d) + '| = ' + d) + '.', 'Distance is never negative, and the order of subtraction does not matter.'];
        if (K.coin()) {
          var L = Math.min(lo - 1, hi - 10), H = Math.max(hi + 1, lo + 10);
          if (H - L > 20) { L = lo - 1; H = hi + 1; }
          var g = K.numberLine({ min: L, max: H, step: 1, pts: [{ x: a }, { x: b }] });
          return attach(Q({ q: 'The two dots on the number line mark two real numbers. What is the distance between them?', graph: g, mc: K.mcNum(d, wr), why: ['The dots are at ' + n(lo) + ' and ' + n(hi) + '.'].concat(why.slice(0, 2)) }), { t: 'dist', a: a, b: b, nl: true });
        }
        return attach(Q({ q: 'Find the distance between ' + m(n(a)) + ' and ' + m(n(b)) + ' on the number line.', mc: K.mcNum(d, wr), why: why }), { t: 'dist', a: a, b: b });
      }
    ],
    [ // Level 2
      function () { // order of operations: −a² + b(c − d)³ ÷ e
        var a = ri(2, 5), c, d, t, e = ri(2, 4), b = e * ri(1, 3);
        do { c = ri(1, 9); d = ri(1, 9); t = c - d; } while (t === 0 || Math.abs(t) > 3);
        var eh = M + n(a) + '<sup>2</sup> + ' + n(b) + '(' + n(c) + ' ' + M + ' ' + n(d) + ')<sup>3</sup> ÷ ' + n(e);
        var val = -a * a + b * t * t * t / e;
        var wr = [a * a + b * t * t * t / e, t < 0 ? -a * a - b * t * t * t / e : -a * a - b * t * t * t / e - 2, -a * a + ipow(b * t, 3) / e, -a * a + b * t * t * t];
        return attach(Q({ q: 'Evaluate ' + m(eh) + '.', mc: K.mcNum(val, wr), why: ['Parentheses: ' + m(n(c) + ' ' + M + ' ' + n(d) + ' = ' + n(t)) + '.', 'Exponents: ' + m(M + n(a) + '<sup>2</sup> = ' + M + a * a) + ' (only the ' + a + ' is squared) and ' + m(pn(t) + '<sup>3</sup> = ' + n(t * t * t)) + '.', 'Multiply and divide left to right: ' + m(n(b) + '(' + n(t * t * t) + ') = ' + n(b * t * t * t)) + ', then ' + m(n(b * t * t * t) + ' ÷ ' + n(e) + ' = ' + n(b * t * t * t / e)) + '.', 'Add: ' + m(M + a * a + ' + ' + pn(b * t * t * t / e) + ' = ' + n(val)) + '.'] }), { t: 'num', eh: eh });
      },
      function () { // name the property
        var st = propStmt(), name = st[1];
        var op = /addition/.test(name) ? 'addition' : /multiplication/.test(name) ? 'multiplication' : '';
        var near = PROPS.filter(function (p) { return p !== name && (op === '' ? /Commutative|Associative/.test(p) : (p.indexOf(op) >= 0 || p.split(' ')[0] === name.split(' ')[0] || p === 'Distributive property')); });
        var w = K.sample(near, 3);
        return attach(Q({ q: 'Which property is shown by ' + m(st[0]) + '?', mc: mc(name, w, function () { return pick(PROPS); }), why: [PROPWHY[name], 'So the statement shows the ' + name.charAt(0).toLowerCase() + name.slice(1) + '.'] }), { t: 'prop', s: st[0] });
      },
      function () { // absolute value expressions
        var eh, val, wr, why;
        if (K.coin()) {
          var a = rnz(-9, 9), b = ri(-6, 6), c = ri(-6, 6);
          while (b === c) c = ri(-6, 6);
          eh = M + '|' + n(a) + '| + |' + n(b) + ' ' + M + ' ' + pn(c) + '|';
          val = -Math.abs(a) + Math.abs(b - c);
          wr = [Math.abs(a) + Math.abs(b - c), -val, -Math.abs(a) - Math.abs(b - c), -a + (b - c)];
          why = [m(M + '|' + n(a) + '| = ' + M + Math.abs(a)) + ': take the absolute value first, then apply the negative sign in front.', m('|' + n(b) + ' ' + M + ' ' + pn(c) + '| = |' + n(b - c) + '| = ' + Math.abs(b - c)) + '.', m(M + Math.abs(a) + ' + ' + Math.abs(b - c) + ' = ' + n(val)) + '.'];
        } else {
          var p = ri(-8, 8), q = ri(-8, 8), r = ri(-8, 8), s = ri(-8, 8);
          while (p === q) q = ri(-8, 8); while (r === s) s = ri(-8, 8);
          eh = '|' + n(p) + ' ' + M + ' ' + pn(q) + '| ' + M + ' |' + n(r) + ' ' + M + ' ' + pn(s) + '|';
          val = Math.abs(p - q) - Math.abs(r - s);
          wr = [(p - q) - (r - s), Math.abs(p - q) + Math.abs(r - s), -val, Math.abs(p - q - r + s)];
          why = ['Simplify inside each absolute value first: ' + m(n(p) + ' ' + M + ' ' + pn(q) + ' = ' + n(p - q)) + ' and ' + m(n(r) + ' ' + M + ' ' + pn(s) + ' = ' + n(r - s)) + '.', m('|' + n(p - q) + '| = ' + Math.abs(p - q)) + ' and ' + m('|' + n(r - s) + '| = ' + Math.abs(r - s)) + '.', m(Math.abs(p - q) + ' ' + M + ' ' + Math.abs(r - s) + ' = ' + n(val)) + '.'];
        }
        return attach(Q({ q: 'Evaluate ' + m(eh) + '.', mc: K.mcNum(val, wr), why: why }), { t: 'num', eh: eh });
      },
      function () { // which elements of S belong to a number set
        var dN = K.coin(), dG = K.coin();
        var items = [[itemOf('neg', dG), 'neg', dG], ['0', 'zero', false], [itemOf('nat', dN), 'nat', dN], [itemOf('ratn'), 'ratn', false], [itemOf('ratn'), 'ratn', false], [itemOf('irr'), 'irr', false]];
        while (items[3][0] === items[4][0]) items[4][0] = itemOf('ratn');
        items[5][0] = (function () { var r; do { r = ri(2, 30); } while (isSq(r)); return K.sqrt(r); })();
        items = K.shuffle(items);
        var cats = {
          natural: function (c) { return c === 'nat'; }, whole: function (c) { return c === 'nat' || c === 'zero'; },
          integers: function (c) { return c === 'nat' || c === 'zero' || c === 'neg'; }, rational: function (c) { return c !== 'irr'; }, irrational: function (c) { return c === 'irr'; }
        };
        var ask = pick(['natural', 'whole', 'integers', 'rational', 'irrational']);
        var sel = function (f) { var l = items.filter(function (it) { return f(it[1], it); }).map(function (it) { return it[0]; }); return l.length ? '{' + l.join(', ') + '}' : EMPTY; };
        var ans = sel(cats[ask]);
        var w = Object.keys(cats).filter(function (k) { return k !== ask; }).map(function (k) { return sel(cats[k]); });
        w.push(sel(function (c, it) { return cats[ask](c) && !it[2]; }));                  // missed a disguised member
        w.push(sel(function (c, it) { return cats[ask](c) || it[2]; }));
        w.push(sel(function (c) { return c === 'irr' || c === 'ratn'; }));
        var nameQ = { natural: 'natural numbers', whole: 'whole numbers', integers: 'integers', rational: 'rational numbers', irrational: 'irrational numbers' }[ask];
        var why = ['Simplify any disguised numbers first: ' + items.filter(function (it) { return it[2]; }).map(function (it) { return m(it[0]) + ' is ' + classNote(it[1]); }).concat(items.filter(function (it) { return !it[2] && it[1] === 'irr'; }).map(function (it) { return m(it[0]) + ' is irrational'; })).join('; ') + '.',
          { natural: 'Natural numbers: 1, 2, 3, …', whole: 'Whole numbers: 0, 1, 2, …', integers: 'Integers: …, −2, −1, 0, 1, 2, …', rational: 'Rational numbers: quotients of integers (decimals that end or repeat).', irrational: 'Irrational numbers: decimals that never end and never repeat.' }[ask],
          'The ' + nameQ + ' in ' + SS + ': ' + m(ans) + '.'];
        return attach(Q({ q: 'Let ' + SS + ' = ' + m('{' + items.map(function (it) { return it[0]; }).join(', ') + '}') + '. Which elements of ' + SS + ' are <b>' + nameQ + '</b>?', mc: mc(m(ans), w.map(m)), why: why }), { t: 'classset', ask: ask, items: items.map(function (it) { return it[0]; }) });
      }
    ],
    [ // Level 3
      function () { // evaluate with variables, fraction bar and absolute value
        var a, b, k = ri(2, 5), den, t = K.coin();
        do { a = rnz(-5, 5); b = rnz(-5, 5); den = t ? Math.abs(a) - b : a - Math.abs(b); } while (den === 0 || (t ? a - b : a - b) === 0);
        var numer = t ? -a * a + k * b : a * a - k * Math.abs(a * b);
        var top = t ? M + xv + '<sup>2</sup> + ' + k + '<i>y</i>' : xv + '<sup>2</sup> ' + M + ' ' + k + '|' + xv + '<i>y</i>|';
        var bot = t ? '|' + xv + '| ' + M + ' <i>y</i>' : xv + ' ' + M + ' |<i>y</i>|';
        var eh = fr(top, bot), val = R(numer, den);
        var w1 = t ? R(a * a + k * b, den) : R(a * a - k * a * b, den);
        var d2 = t ? a - b : a - b;
        var w2 = R(numer, d2), w3 = val.neg();
        var subT = t ? M + pn(a) + '<sup>2</sup> + ' + k + '(' + n(b) + ')' : pn(a) + '<sup>2</sup> ' + M + ' ' + k + '|(' + n(a) + ')(' + n(b) + ')|';
        var subB = t ? '|' + n(a) + '| ' + M + ' ' + pn(b) : n(a) + ' ' + M + ' |' + n(b) + '|';
        return attach(Q({ q: 'Evaluate ' + m(eh) + ' for ' + m(xv + ' = ' + n(a)) + ' and ' + m('<i>y</i> = ' + n(b)) + '.', mc: mcF([val.html(), function () { return val.val(); }], [[w1.html(), function () { return w1.val(); }], [w2.html(), function () { return w2.val(); }], [w3.html(), function () { return w3.val(); }]], function () { var z = val.add(rnz(-3, 3)); return [z.html(), function () { return z.val(); }]; }), why: ['Numerator: ' + m(subT + ' = ' + n(numer)) + (t ? ' (the square applies before the negative sign: ' + m(M + pn(a) + '<sup>2</sup> = ' + n(-a * a)) + ').' : '.'), 'Denominator: ' + m(subB + ' = ' + n(den)) + '.', (den > 1 && gcd(numer, den) === 1 ? 'Divide: the value is ' + m(val.html()) + ', which is already in lowest terms.' : 'Divide: ' + m(fr(n(numer), n(den)) + ' = ' + val.html()) + '.')] }), { t: 'num', eh: eh, vars: { x: a, y: b } });
      },
      function () { // temperature readings, distance between extremes
        var t1 = -ri(2, 15), r = ri(8, 25), f = ri(5, 30), t2 = t1 + r, t3 = t2 - f;
        var hi = Math.max(t1, t2, t3), lo = Math.min(t1, t2, t3), d = hi - lo;
        var city = pick(['Fargo', 'Duluth', 'Bismarck', 'Minneapolis', 'Fairbanks']);
        return attach(Q({ q: 'At 6 AM the temperature in ' + city + ' was ' + m(n(t1) + '°F') + '. By 2 PM it had risen ' + r + ' degrees, and by 10 PM it had fallen ' + f + ' degrees from the 2 PM reading. How many degrees apart are the highest and lowest of the three readings?', mc: K.mcNum(d, [Math.abs(t3 - t1), r + f, Math.abs(r - f), Math.abs(hi + lo)]), why: ['The three readings: 6 AM ' + m(n(t1) + '°') + ', 2 PM ' + m(n(t1) + ' + ' + r + ' = ' + n(t2) + '°') + ', 10 PM ' + m(n(t2) + ' ' + M + ' ' + f + ' = ' + n(t3) + '°') + '.', 'Highest: ' + m(n(hi) + '°') + '. Lowest: ' + m(n(lo) + '°') + '.', 'Distance: ' + m('|' + n(hi) + ' ' + M + ' ' + pn(lo) + '| = ' + d) + ' degrees.'] }), { t: 'temp', t1: t1, r: r, f: f });
      },
      function () { // classify a disguised number
        var cls = pick(['nat', 'zero', 'neg', 'ratn', 'irr']);
        var others = K.sample(['nat', 'zero', 'neg', 'ratn', 'irr'].filter(function (c) { return c !== cls; }), 3);
        var c = itemOf(cls, true), w = others.map(function (o) { return itemOf(o, true); });
        var why = [CLASSQ[cls][1], m(c) + ' is ' + classNote(cls) + ', so it fits.', 'The others: ' + others.map(function (o, i) { return m(w[i]) + ' is ' + classNote(o); }).join('; ') + '.'];
        return attach(Q({ q: 'Which number is <b>' + CLASSQ[cls][0] + '</b>?', mc: mc(m(c), w.map(m)), why: why }), { t: 'classify', cls: cls });
      }
    ]
  ];
  K.lesson('R.2', { title: 'Real Numbers and Their Properties', std: 'Lial 12e · Section R.2', levels: r2 });

  /* ================= R.3 POLYNOMIALS ================= */
  function m2(c, a, b) { return P([[c, xp(a, 'x') + xp(b, 'y')]]); }
  function m2f(c, a, b) { return function (x) { var y = 0.53 * x + 1.9; return c * Math.pow(x, a) * Math.pow(y, b); }; }
  function rpoly(deg, lo, hi, lead) { var c = []; for (var i = 0; i <= deg; i++) c[i] = ri(lo, hi); c[deg] = lead || rnz(lo, hi); return c; }

  var r3 = [
    [ // Level 1
      function () { // exponent rules on monomials
        var v = ri(0, 2), eh, c, w, why, a, b;
        if (v === 0) {
          var c1 = rnz(-6, 6), c2 = rnz(-6, 6); a = ri(2, 6); b = ri(2, 6);
          while (Math.abs(c1) === 1) c1 = rnz(-6, 6);
          eh = '(' + m2(c1, a, 0) + ')(' + m2(c2, b, 0) + ')';
          c = [m(m2(c1 * c2, a + b, 0)), m2f(c1 * c2, a + b, 0)];
          w = [[m(m2(c1 * c2, a * b, 0)), m2f(c1 * c2, a * b, 0)], [m(m2(c1 + c2, a + b, 0)), m2f(c1 + c2, a + b, 0)], [m(m2(-c1 * c2, a + b, 0)), m2f(-c1 * c2, a + b, 0)]];
          why = ['Multiply the coefficients: ' + m(pn(c1) + ' · ' + pn(c2) + ' = ' + n(c1 * c2)) + '.', 'Product rule: same base, add the exponents: ' + m(xp(a) + ' · ' + xp(b) + ' = ' + xp(a + b)) + '.', 'Answer: ' + c[0] + '.'];
        } else if (v === 1) {
          do { a = ri(2, 6); b = ri(2, 5); } while (a * b === a + b);
          eh = '(' + xp(a) + ')<sup>' + b + '</sup>';
          c = [m(xp(a * b)), m2f(1, a * b, 0)];
          w = [[m(xp(a + b)), m2f(1, a + b, 0)], [m(m2(b, a, 0)), m2f(b, a, 0)], [m(xp(a * b + 1)), m2f(1, a * b + 1, 0)]];
          why = ['A power of a power multiplies the exponents: ' + m('(<i>a</i><sup><i>m</i></sup>)<sup><i>n</i></sup> = <i>a</i><sup><i>mn</i></sup>') + '.', m(a + ' · ' + b + ' = ' + a * b) + ', so the answer is ' + c[0] + '. (Adding the exponents is the rule for a product, not a power.)'];
        } else {
          var cc = pick([-3, -2, 2, 3, 4]); a = ri(2, 5); b = ri(2, 3);
          eh = '(' + m2(cc, a, 0) + ')<sup>' + b + '</sup>';
          c = [m(m2(ipow(cc, b), a * b, 0)), m2f(ipow(cc, b), a * b, 0)];
          w = [[m(m2(cc, a * b, 0)), m2f(cc, a * b, 0)], [m(m2(cc * b, a * b, 0)), m2f(cc * b, a * b, 0)], [m(m2(ipow(cc, b), a + b, 0)), m2f(ipow(cc, b), a + b, 0)]];
          why = ['The power applies to the coefficient too: ' + m(pn(cc) + '<sup>' + b + '</sup> = ' + n(ipow(cc, b))) + '.', 'Multiply the exponents on ' + X + ': ' + m('(' + xp(a) + ')<sup>' + b + '</sup> = ' + xp(a * b)) + '.', 'Answer: ' + c[0] + '.'];
        }
        return attach(Q({ q: 'Simplify ' + m(eh) + '.', mc: mcF(c, w, function () { var k = rnz(-3, 3); return [m(m2(1, a * b + k + 7, 0)), m2f(1, a * b + k + 7, 0)]; }, TPOS), why: why }), { t: 'expr', eh: eh });
      },
      function () { // add or subtract polynomials
        var a = [rnz(-9, 9), rnz(-9, 9), rnz(-9, 9)], b = [rnz(-9, 9), rnz(-9, 9), rnz(-9, 9)], sub = K.coin(), r = padd(a, b, sub ? -1 : 1);
        if (r.length < 2) b[1] = (b[1] || 0) + 1, r = padd(a, b, sub ? -1 : 1);
        var eh = '(' + ph(a) + ') ' + (sub ? M : '+') + ' (' + ph(b) + ')';
        var c = [m(ph(r)), pf(r)];
        var w = sub ? [[m(ph(padd(a, b))), pf(padd(a, b))], [m(ph(trim([a[0] + b[0], a[1] - b[1], a[2] - b[2]]))), pf(trim([a[0] + b[0], a[1] - b[1], a[2] - b[2]]))], [m(ph(trim([a[0] + b[0], a[1] + b[1], a[2] - b[2]]))), pf(trim([a[0] + b[0], a[1] + b[1], a[2] - b[2]]))]]
          : [[m(ph(padd(a, b, -1))), pf(padd(a, b, -1))], [m(ph(trim([r[0], r[1] || 0, a[2] * b[2]]))), pf(trim([r[0], r[1] || 0, a[2] * b[2]]))], [m(ph(trim([r[0], -(r[1] || 0), r[2] || 0]))), pf(trim([r[0], -(r[1] || 0), r[2] || 0]))]];
        var nb = b.map(function (z) { return -z; });
        return attach(Q({ q: (sub ? 'Subtract: ' : 'Add: ') + m(eh), mc: mcF(c, w, function () { var z = r.slice(); z[0] += rnz(-3, 3); return [m(ph(z)), pf(z)]; }), why: [sub ? 'Subtracting means changing the sign of <b>every</b> term in the second polynomial: ' + m(ph(a) + ' + (' + ph(nb) + ')') + '.' : 'Remove the parentheses and group like terms (same variable, same exponent).', 'Combine like terms: ' + m(xp(2)) + '-terms ' + m(n(a[2]) + (sub ? sg(-b[2]) : sg(b[2])) + ' = ' + n(r[2] || 0)) + '; ' + X + '-terms ' + m(n(a[1]) + (sub ? sg(-b[1]) : sg(b[1])) + ' = ' + n(r[1] || 0)) + '; constants ' + m(n(a[0]) + (sub ? sg(-b[0]) : sg(b[0])) + ' = ' + n(r[0])) + '.', 'Answer: ' + c[0] + '.'] }), { t: 'expr', eh: eh });
      },
      function () { // degree of a polynomial in two variables
        var terms = [], degs = [], tries = 0;
        while (terms.length < 3 && tries++ < 100) {
          var i = ri(0, 5), j = ri(0, 4); if (i + j === 0 && terms.length < 2) continue;
          if (degs.indexOf(i + j) >= 0) continue;
          degs.push(i + j); terms.push([rnz(-9, 9), i, j]);
        }
        var top = Math.max.apply(null, degs), maxSingle = Math.max.apply(null, terms.map(function (t) { return Math.max(t[1], t[2]); }));
        var eh = P(terms.map(function (t) { return [t[0], xp(t[1], 'x') + xp(t[2], 'y')]; }));
        var tt = terms.filter(function (t) { return t[1] + t[2] === top; })[0];
        return attach(Q({ q: 'What is the degree of the polynomial ' + m(eh) + '?', mc: K.mcNum(top, [maxSingle, terms.length, top + 1, top - 1]), why: ['The degree of a term is the <b>sum</b> of the exponents on its variables.', 'Term degrees: ' + terms.map(function (t) { return m(m2(t[0], t[1], t[2])) + ' → ' + (t[1] + t[2]); }).join(', ') + '.', 'The polynomial’s degree is the highest term degree: ' + top + ' (from ' + m(m2(tt[0], tt[1], tt[2])) + ').'] }), { t: 'deg', eh: eh });
      }
    ],
    [ // Level 2
      function () { // (c x^a y^b)^k (d x^e y^f)
        var c = pick([-3, -2, 2, 3]), k = ri(2, 3), a = ri(1, 3), b = ri(1, 3), d = rnz(-5, 5), e = ri(1, 4), f = ri(1, 4);
        var coef = ipow(c, k) * d, X1 = a * k + e, Y1 = b * k + f;
        var eh = '(' + m2(c, a, b) + ')<sup>' + k + '</sup>(' + m2(d, e, f) + ')';
        var cc = [m(m2(coef, X1, Y1)), m2f(coef, X1, Y1)];
        var w = [[m(m2(c * k * d, X1, Y1)), m2f(c * k * d, X1, Y1)], [m(m2(coef, a * k * e, b * k * f)), m2f(coef, a * k * e, b * k * f)], [m(m2(c * d, X1, Y1)), m2f(c * d, X1, Y1)], [m(m2(-coef, X1, Y1)), m2f(-coef, X1, Y1)], [m(m2(coef, a + k + e, b + k + f)), m2f(coef, a + k + e, b + k + f)]];
        return attach(Q({ q: 'Simplify ' + m(eh) + '.', mc: mcF(cc, K.shuffle(w).slice(0, 4), function () { var z = rnz(-2, 2); return [m(m2(coef, X1 + z, Y1)), m2f(coef, X1 + z, Y1)]; }, TPOS), why: ['Power rule first: ' + m('(' + m2(c, a, b) + ')<sup>' + k + '</sup> = ' + pn(c) + '<sup>' + k + '</sup>' + xp(a * k) + xp(b * k, 'y') + ' = ' + m2(ipow(c, k), a * k, b * k)) + '.', 'Multiply the coefficients: ' + m(pn(ipow(c, k)) + ' · ' + pn(d) + ' = ' + n(coef)) + '.', 'Product rule on each variable: ' + m(xp(a * k) + ' · ' + xp(e) + ' = ' + xp(X1)) + ' and ' + m(xp(b * k, 'y') + ' · ' + xp(f, 'y') + ' = ' + xp(Y1, 'y')) + ', so the answer is ' + cc[0] + '.'] }), { t: 'expr', eh: eh });
      },
      function () { // binomial × trinomial
        var a = rnz(-3, 3), b = rnz(-7, 7), t = rpoly(2, -6, 6, 1); t[0] = rnz(-7, 7); t[1] = rnz(-6, 6);
        var r = pmul([b, a], t);
        var eh = bin(a, b) + '(' + ph(t) + ')';
        var w1 = trim([b * t[0], b * t[1], a * t[1] + b, a]);               // multiplied only matching positions
        var w2 = pmul([-b, a], t);                                              // sign error on the constant
        var w3 = trim([b * t[0], a * t[0] + b * t[1], a * t[1], a]);        // missed b·x² term
        return attach(Q({ q: 'Multiply: ' + m(eh), mc: mcF([m(ph(r)), pf(r)], [[m(ph(w1)), pf(w1)], [m(ph(w2)), pf(w2)], [m(ph(w3)), pf(w3)]], function () { var z = r.slice(); z[1] += rnz(-3, 3); return [m(ph(z)), pf(z)]; }), why: ['Multiply ' + m(lin(a, 0)) + ' by every term: ' + m(ph(pmul([0, a], t))) + '.', 'Multiply ' + m(n(b)) + ' by every term: ' + m(ph(pmul([b], t))) + '.', 'Combine like terms: ' + m(ph(r)) + '. (There are 2 × 3 = 6 products before combining.)'] }), { t: 'expr', eh: eh });
      },
      function () { // special products
        var a = ri(1, 5), b = ri(1, 9), sq = K.coin(), sB = K.coin() ? 1 : -1, eh, c, w, why;
        if (sq) {
          var r = [b * b, 2 * a * b * sB, a * a];
          eh = bin(a, sB * b) + '<sup>2</sup>';
          c = [m(ph(r)), pf(r)];
          w = [[m(ph([b * b, 0, a * a])), pf([b * b, 0, a * a])], [m(ph([b * b, a * b * sB, a * a])), pf([b * b, a * b * sB, a * a])], [m(ph([sB * b * b, 2 * a * b * sB, a * a])), pf([sB * b * b, 2 * a * b * sB, a * a])], [m(ph([b * b, 2 * b * sB, 2 * a])), pf([b * b, 2 * b * sB, 2 * a])]];
          why = ['Square of a binomial: ' + m('(<i>p</i> ' + (sB > 0 ? '+' : M) + ' <i>q</i>)<sup>2</sup> = <i>p</i><sup>2</sup> ' + (sB > 0 ? '+' : M) + ' 2<i>pq</i> + <i>q</i><sup>2</sup>') + '.', 'Here ' + m('<i>p</i> = ' + lin(a, 0)) + ' and ' + m('<i>q</i> = ' + b) + ': ' + m('<i>p</i><sup>2</sup> = ' + ph([0, 0, a * a])) + ', ' + m('2<i>pq</i> = ' + ph([0, 2 * a * b])) + ', ' + m('<i>q</i><sup>2</sup> = ' + b * b) + '.', 'Answer: ' + c[0] + '. Do not forget the middle term.'];
        } else {
          var r2 = [-b * b, 0, a * a];
          eh = bin(a, b) + bin(a, -b);
          c = [m(ph(r2)), pf(r2)];
          w = [[m(ph([b * b, 0, a * a])), pf([b * b, 0, a * a])], [m(ph([-b * b, -2 * a * b, a * a])), pf([-b * b, -2 * a * b, a * a])], [m(ph([-b * b, 0, 2 * a])), pf([-b * b, 0, 2 * a])], [m(ph([-b * b, 2 * a * b, a * a])), pf([-b * b, 2 * a * b, a * a])]];
          why = ['A sum times a difference: ' + m('(<i>p</i> + <i>q</i>)(<i>p</i> ' + M + ' <i>q</i>) = <i>p</i><sup>2</sup> ' + M + ' <i>q</i><sup>2</sup>') + '.', 'The middle terms ' + m(ph([0, a * b])) + ' and ' + m(ph([0, -a * b])) + ' cancel.', m('(' + lin(a, 0) + ')<sup>2</sup> ' + M + ' ' + b + '<sup>2</sup> = ' + ph(r2)) + '.'];
        }
        return attach(Q({ q: 'Multiply: ' + m(eh), mc: mcF(c, K.shuffle(w).slice(0, 4), function () { var z = [b * b + rnz(1, 4), sq ? 2 * a * b * sB : 0, a * a]; return [m(ph(z)), pf(z)]; }), why: why }), { t: 'expr', eh: eh });
      },
      function () { // divide a polynomial by a monomial
        var k = ri(2, 5), s = K.coin() ? 1 : -1, q = [rnz(-6, 6), rnz(-6, 6), ri(1, 5)], e = ri(1, 2);
        var mon = []; for (var i = 0; i < e; i++) mon.push(0); mon.push(s * k);
        var top = pmul(q, mon);
        var eh = fr(ph(top), ph(mon));
        var c = [m(ph(q)), pf(q)];
        var w = [[m(ph(trim([0].concat(q)))), pf(trim([0].concat(q)))], [m(ph(q.map(function (z, i) { return i === 0 ? z * k : z; }))), pf(q.map(function (z, i) { return i === 0 ? z * k : z; }))], [m(ph(q.map(function (z) { return -z; }))), pf(q.map(function (z) { return -z; }))]];
        return attach(Q({ q: 'Divide: ' + m(eh), mc: mcF(c, w, function () { var z = q.slice(); z[0] += rnz(-3, 3); return [m(ph(z)), pf(z)]; }, TPOS), why: ['Divide <b>each</b> term of the numerator by ' + m(ph(mon)) + '.', 'Divide the coefficients and subtract the exponents: ' + top.map(function (z, i) { return z ? m(fr(P([[z, xp(i)]]), ph(mon)) + ' = ' + P([[z / (s * k), xp(i - e)]])) : ''; }).filter(Boolean).reverse().join(', ') + '.', 'Answer: ' + c[0] + '.'] }), { t: 'expr', eh: eh });
      }
    ],
    [ // Level 3
      function () { // long division by x − k with remainder
        var k = rnz(-5, 5), q = [rnz(-6, 6), rnz(-6, 6), ri(1, 3)], r = K.coin() ? rnz(-9, 9) : rnz(-9, 9);
        var dvd = padd(pmul([-k, 1], q), [r]);
        var rem = function (rr, kk) { return rr === 0 ? '' : (rr < 0 ? ' ' + M + ' ' : ' + ') + fr(n(Math.abs(rr)), lin(1, -kk)); };
        var ansH = ph(q) + rem(r, k);
        var ansF = function (x) { return pev(q, x) + r / (x - k); };
        // dividing by x + k instead (sign slip)
        var q2 = [], c3 = dvd[3], c2 = dvd[2], c1 = dvd[1], c0 = dvd[0];
        var b2 = c3, b1 = c2 - k * b2, b0 = c1 - k * b1, r2 = c0 - k * b0; q2 = [b0, b1, b2];
        var w = [[m(ph(q)), pf(q)], [m(ph(q2) + rem(r2, -k)), function (x) { return pev(q2, x) + r2 / (x + k); }], [m(ph(q) + rem(-r, k)), function (x) { return pev(q, x) - r / (x - k); }], [m(ph(q) + rem(r, -k)), function (x) { return pev(q, x) + r / (x + k); }]];
        var parts = [ph(dvd), lin(1, -k)];
        return attach(Q({ q: 'Use long division to divide ' + m('(' + parts[0] + ')') + ' by ' + m('(' + parts[1] + ')') + '.', mc: mcF([m(ansH), ansF], w, function () { var z = q.slice(); z[0] += rnz(-3, 3); return [m(ph(z) + rem(r, k)), function (x) { return pev(z, x) + r / (x - k); }]; }), why: ['Divide the leading terms: ' + m(P([[q[2], xp(3)]]) + ' ÷ ' + X + ' = ' + P([[q[2], xp(2)]])) + '. Multiply ' + m(P([[q[2], xp(2)]]) + '(' + parts[1] + ')') + ', subtract, and bring down the next term.', 'Repeat with each new leading term to get the quotient ' + m(ph(q)) + '.', 'The last subtraction leaves the remainder ' + n(r) + ', which is written over the divisor: ' + m(ansH) + '.', 'Check: ' + m('(' + parts[1] + ')(' + ph(q) + ')' + sg(r)) + ' = ' + m(parts[0]) + ' ✔'] }), { t: 'expr2', parts: parts, tpl: '({0})/({1})' });
      },
      function () { // garden with a path around it
        var w = ri(2, 5), d = K.coin() ? 0 : ri(2, 6);
        var path = [4 * w * w + 2 * w * d, 4 * w];  // (x+2w)(x+d+2w) − x(x+d)
        var total = pmul([2 * w, 1], [d + 2 * w, 1]);
        var w1 = [w * w + w * d, 2 * w];                // used w instead of 2w
        var w2 = [2 * w * d, 4 * w];                    // forgot the corners
        var shape = d === 0 ? 'A square garden is ' + m(X) + ' feet on each side.' : 'A rectangular garden is ' + m(X) + ' feet wide and ' + m('(' + lin(1, d) + ')') + ' feet long.';
        var outer = d === 0 ? '(' + lin(1, 2 * w) + ')<sup>2</sup>' : '(' + lin(1, 2 * w) + ')(' + lin(1, d + 2 * w) + ')';
        var inner = d === 0 ? xp(2) : X + '(' + lin(1, d) + ')';
        return attach(Q({ q: shape + ' A path ' + w + ' feet wide runs all the way around it. Which expression gives the area of the <b>path alone</b>, in square feet?', mc: mcF([m(ph(path)), pf(path)], [[m(ph(total)), pf(total)], [m(ph(w1)), pf(w1)], [m(ph(w2)), pf(w2)]], function () { var z = path.slice(); z[0] += rnz(1, 6) * w; return [m(ph(z)), pf(z)]; }, TPOS), why: ['The path adds ' + w + ' feet on <b>each</b> side, so the outer rectangle is ' + m(2 * w) + ' feet longer in each direction: area ' + m(outer + ' = ' + ph(total)) + '.', 'The garden alone has area ' + m(d === 0 ? xp(2) : inner + ' = ' + ph([0, d, 1])) + '.', 'Path = outer ' + M + ' garden = ' + m(ph(path)) + ' square feet.'] }), { t: 'path', w: w, d: d });
      },
      function () { // (x + a)² − (x + b)(x + c)
        var a, b, c, r;
        do { a = rnz(-6, 6); b = rnz(-6, 6); c = rnz(-6, 6); r = [a * a - b * c, 2 * a - b - c]; } while (r[1] === 0 || r[0] === 0 || b === c);
        var eh = bin(1, a) + '<sup>2</sup> ' + M + ' ' + bin(1, b) + bin(1, c);
        var sq = [a * a, 2 * a, 1], pr = [b * c, b + c, 1];
        var w1 = trim([a * a + b * c, 2 * a + b + c]);                 // minus reached only x²
        var w2 = trim([a * a - b * c, -(b + c)]);                       // (x + a)² taken as x² + a²
        var w3 = trim([a * a - b * c, 2 * a - b - c, 2]);               // added the x² terms
        return attach(Q({ q: 'Simplify ' + m(eh) + '.', mc: mcF([m(ph(r)), pf(r)], [[m(ph(w1)), pf(w1)], [m(ph(w2)), pf(w2)], [m(ph(w3)), pf(w3)]], function () { var z = r.slice(); z[0] += rnz(-4, 4); return [m(ph(z)), pf(z)]; }), why: ['Square the binomial: ' + m(bin(1, a) + '<sup>2</sup> = ' + ph(sq)) + '.', 'FOIL the product: ' + m(bin(1, b) + bin(1, c) + ' = ' + ph(pr)) + '.', 'Subtract <b>every</b> term of the product: ' + m(ph(sq) + ' ' + M + ' ' + P([[1, xp(2)], [-(b + c), X], [-b * c, '']]).replace(/^/, '') + ' = ' + ph(r)) + '. (The minus sign changes every sign in the product.)'] }), { t: 'expr', eh: eh });
      }
    ]
  ];
  K.lesson('R.3', { title: 'Polynomials', std: 'Lial 12e · Section R.3', levels: r3 });

  /* ================= R.4 FACTORING ================= */
  // factored form: k (integer), mon (html of a monomial factor), facs = array of coefficient arrays (repeats → exponent)
  // factor order: higher degree first, then larger leading coefficient, then smaller |constant|, then − before + (keeps (x − 4)(x + 4) together)
  function fkey(c) { return [99 - (c.length - 1), 99 - c[c.length - 1], Math.abs(c[0]), c[0] < 0 ? 0 : 1].map(function (z) { return ('000' + (z + 500)).slice(-4); }).join('|'); }
  function fmtF(k, mon, facs, v) {
    var groups = {}, order = [];
    facs.forEach(function (c) { var key = fkey(c) + ph(c, v); if (!groups[key]) { groups[key] = { c: c, e: 0 }; order.push(key); } groups[key].e++; });
    order.sort();
    var h = (k === 1 ? '' : k === -1 ? M : n(k)) + (mon || '');
    order.forEach(function (key) { var g = groups[key]; h += '(' + ph(g.c, v) + ')' + (g.e > 1 ? '<sup>' + g.e + '</sup>' : ''); });
    return h;
  }
  function fF(k, monF, facs) { return function (x) { var s = k * (monF ? monF(x) : 1); facs.forEach(function (c) { s *= pev(c, x); }); return s; }; }
  function fact(k, facs, v, monH, monF) { return [m(fmtF(k, monH, facs, v)), fF(k, monF, facs)]; }
  function prodAll(facs) { var r = [1]; facs.forEach(function (c) { r = pmul(r, c); }); return r; }

  var r4 = [
    [ // Level 1
      function () { // GCF in two variables
        var k = ri(2, 9), a = ri(1, 3), b = ri(1, 3), p, q, s = K.coin() ? 1 : -1;
        do { p = ri(1, 6); q = ri(1, 6); } while (gcd(p, q) !== 1 || p === q);
        var eh = P([[k * p, xp(a + 1) + xp(b, 'y')], [s * k * q, xp(a) + xp(b + 1, 'y')]]);
        var g = m2(k, a, b), gf = m2f(k, a, b);
        var mk = function (pre, prf, inner, innF) { return [m(pre + '(' + inner + ')'), function (x) { return prf(x) * innF(x, 0.53 * x + 1.9); }]; };
        var c = mk(g, gf, P([[p, X], [s * q, Y]]), function (x, y) { return p * x + s * q * y; });
        var w = [mk(g, gf, P([[p, X], [-s * q, Y]]), function (x, y) { return p * x - s * q * y; }),
          mk(g, gf, P([[p, X], [s * q, '']]), function (x) { return p * x + s * q; }),
          mk(g, gf, P([[p, X + Y], [s * q, Y]]), function (x, y) { return p * x * y + s * q * y; }),
          mk(m2(k, a + 1, b), m2f(k, a + 1, b), P([[p, ''], [s * q, Y]]), function (x, y) { return p + s * q * y; })];
        return attach(Q({ q: 'Factor out the greatest common factor: ' + m(eh), mc: mcF(c, w, null, TPOS), why: ['GCF of the coefficients ' + k * p + ' and ' + k * q + ' is ' + k + '. The lowest powers are ' + m(xp(a)) + ' and ' + m(xp(b, 'y')) + ', so the GCF is ' + m(g) + '.', 'Divide each term by ' + m(g) + ': ' + m(fr(P([[k * p, xp(a + 1) + xp(b, 'y')]]), g) + ' = ' + P([[p, X]])) + ' and ' + m(fr(P([[s * k * q, xp(a) + xp(b + 1, 'y')]]), g) + ' = ' + P([[s * q, Y]])) + '.', 'Answer: ' + c[0] + '. Check by distributing.'] }), { t: 'expr', eh: eh, chk: 'factor' });
      },
      function () { // x² + bx + c
        var p, q; do { p = rnz(-9, 9); q = rnz(-9, 9); } while (p === q || p === -q);
        var poly = pmul([p, 1], [q, 1]);
        var c = fact(1, [[p, 1], [q, 1]]);
        var w = [fact(1, [[-p, 1], [-q, 1]]), fact(1, [[p, 1], [-q, 1]]), fact(1, [[-p, 1], [q, 1]])];
        return attach(Q({ q: 'Factor ' + m(ph(poly)) + '.', mc: mcF(c, w), why: ['Find two numbers whose product is ' + n(p * q) + ' and whose sum is ' + n(p + q) + '.', m(pn(p) + ' · ' + pn(q) + ' = ' + n(p * q)) + ' and ' + m(n(p) + sg(q) + ' = ' + n(p + q)) + '.', 'So ' + m(ph(poly) + ' = ' + fmtF(1, '', [[p, 1], [q, 1]])) + '. Check with FOIL.'] }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      },
      function () { // difference of squares
        var a, b, v = pick(['x', 'y']); do { a = ri(1, 5); b = ri(1, 9); } while (gcd(a, b) !== 1 || (a === 1 && b === 1));
        var poly = [-b * b, 0, a * a];
        var c = fact(1, [[b, a], [-b, a]], v);
        var w = [fact(1, [[-b, a], [-b, a]], v), fact(1, [[b, a], [b, a]], v), fact(1, [[a, b], [-a, b]], v), [m(ph([b * b, 0, a * a], v)), function (x) { return a * a * x * x + b * b; }]];
        return attach(Q({ q: 'Factor ' + m(ph(poly, v)) + ' completely.', mc: mcF(c, K.shuffle(w).slice(0, 3)), why: ['This is a difference of squares: ' + m(ph([0, 0, a * a], v) + ' = (' + lin(a, 0, v) + ')<sup>2</sup>') + ' and ' + m(b * b + ' = ' + b + '<sup>2</sup>') + '.', 'Use ' + m('<i>p</i><sup>2</sup> ' + M + ' <i>q</i><sup>2</sup> = (<i>p</i> + <i>q</i>)(<i>p</i> ' + M + ' <i>q</i>)') + '.', 'Answer: ' + c[0] + '. (A perfect square like ' + m('(' + lin(a, -b, v) + ')<sup>2</sup>') + ' would have a middle term.)'] }), { t: 'expr', eh: ph(poly, v), chk: 'factor' });
      }
    ],
    [ // Level 2
      function () { // ax² + bx + c, a > 1
        var p, q, r, s, poly;
        do { p = ri(1, 4); r = ri(1, 4); q = rnz(-9, 9); s = rnz(-9, 9); poly = pmul([q, p], [s, r]); }
        while ((p === 1 && r === 1) || gcd(p, Math.abs(q)) !== 1 || gcd(r, Math.abs(s)) !== 1 || poly[1] === 0 || (p === r && q === s) || Math.abs(poly[0]) > 60);
        var c = fact(1, [[q, p], [s, r]]);
        var w = [fact(1, [[-q, p], [-s, r]]), fact(1, [[s, p], [q, r]]), fact(1, [[-q, p], [s, r]]), fact(1, [[q, p], [-s, r]]), fact(1, [[-s, p], [-q, r]])];
        var ac = poly[2] * poly[0];
        return attach(Q({ q: 'Factor ' + m(ph(poly)) + ' completely.', mc: mcF(c, K.shuffle(w), function () { var z = [rnz(-9, 9), p], y = [rnz(-9, 9), r]; return fact(1, [z, y]); }), why: ['Key product: ' + m('<i>ac</i> = ' + pn(poly[2]) + '(' + n(poly[0]) + ') = ' + n(ac)) + '. Find two numbers with product ' + n(ac) + ' and sum ' + n(poly[1]) + ': ' + n(p * s) + ' and ' + n(q * r) + '.', 'Split the middle term and group: ' + m(P([[poly[2], xp(2)], [p * s, X], [q * r, X], [poly[0], '']])) + '.', 'Factor out the common binomial: ' + c[0] + '. Check: FOIL gives back ' + m(ph(poly)) + '.'] }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      },
      function () { // sum or difference of cubes
        var a, b; do { a = ri(1, 3); b = ri(1, 5); } while (gcd(a, b) !== 1 || (a === 1 && b === 1));
        var sgn = K.coin() ? 1 : -1, poly = [sgn * b * b * b, 0, 0, a * a * a];
        var lin1 = [sgn * b, a], tri = [b * b, -sgn * a * b, a * a];
        var c = [m('(' + ph(lin1) + ')(' + ph(tri) + ')'), function (x) { return pev(lin1, x) * pev(tri, x); }];
        var mk = function (L, T) { return [m('(' + ph(L) + ')(' + ph(T) + ')'), function (x) { return pev(L, x) * pev(T, x); }]; };
        var w = [mk(lin1, [b * b, sgn * a * b, a * a]), mk([-sgn * b, a], tri), mk(lin1, [b * b, -2 * sgn * a * b, a * a]), mk([-sgn * b, a], [b * b, sgn * a * b, a * a]), [m('(' + ph(lin1) + ')<sup>3</sup>'), function (x) { return Math.pow(pev(lin1, x), 3); }]];
        var cubeA = a === 1 ? X : '(' + lin(a, 0) + ')', cubeB = n(b);
        return attach(Q({ q: 'Factor ' + m(ph(poly)) + '.', mc: mcF(c, K.shuffle(w)), why: ['Write each term as a cube: ' + (a === 1 ? m(xp(3)) + ' is already a cube' : m(ph([0, 0, 0, a * a * a]) + ' = ' + cubeA + '<sup>3</sup>')) + ' and ' + m(b * b * b + ' = ' + cubeB + '<sup>3</sup>') + '. This is a ' + (sgn > 0 ? 'sum' : 'difference') + ' of cubes.', 'Use ' + (sgn > 0 ? m('<i>p</i><sup>3</sup> + <i>q</i><sup>3</sup> = (<i>p</i> + <i>q</i>)(<i>p</i><sup>2</sup> ' + M + ' <i>pq</i> + <i>q</i><sup>2</sup>)') : m('<i>p</i><sup>3</sup> ' + M + ' <i>q</i><sup>3</sup> = (<i>p</i> ' + M + ' <i>q</i>)(<i>p</i><sup>2</sup> + <i>pq</i> + <i>q</i><sup>2</sup>)')) + ' (SOAP: same, opposite, always positive).', 'With ' + m('<i>p</i> = ' + lin(a, 0)) + ' and ' + m('<i>q</i> = ' + b) + ': ' + c[0] + '. The trinomial does not factor further.'] }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      },
      function () { // grouping, four terms
        var a, b, d = pick([1, 1, 2, 3]); do { a = rnz(-7, 7); b = ri(1, 9); } while (a === b || a === -b || gcd(b, d) !== 1);
        var poly = pmul([a, 1], [b, 0, d]);
        var c = fact(1, [[a, 1], [b, 0, d]]);
        var w = [fact(1, [[-a, 1], [b, 0, d]]), fact(1, [[a, 1], [-b, 0, d]]), fact(1, [[b, 1], [a, 0, d]]), fact(1, [[a, d], [b, 0, 1]])];
        var p1 = P([[d, xp(3)], [a * d, xp(2)]]), p2 = P([[b, X], [a * b, '']]);
        return attach(Q({ q: 'Factor by grouping: ' + m(ph(poly)), mc: mcF(c, w), why: ['Group in pairs: ' + m('(' + p1 + ') + (' + p2 + ')') + '.', 'Factor each pair: ' + m(P([[d, xp(2)]]) + bin(1, a) + ' + ' + (b === 1 ? '' : n(b)) + bin(1, a)) + '.', 'Factor out the common binomial ' + m(bin(1, a)) + ': ' + c[0] + '.'] }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      },
      function () { // perfect square trinomial
        var a, b, sgn = K.coin() ? 1 : -1; do { a = ri(1, 5); b = ri(1, 9); } while (gcd(a, b) !== 1 || (a === 1 && b === 1));
        var L = [sgn * b, a], poly = pmul(L, L);
        var c = fact(1, [L, L]);
        var w = [fact(1, [[-sgn * b, a], [-sgn * b, a]]), fact(1, [[b, a], [-b, a]]), fact(1, [[sgn * b * b, a], [sgn, a]]), fact(1, [[sgn * b, a * a], [sgn * b, 1]])];
        return attach(Q({ q: 'Factor ' + m(ph(poly)) + '.', mc: mcF(c, w), why: ['The first and last terms are perfect squares: ' + m(ph([0, 0, a * a]) + ' = ' + (a === 1 ? X : '(' + lin(a, 0) + ')') + '<sup>2</sup>') + ' and ' + m(b * b + ' = ' + b + '<sup>2</sup>') + '.', 'Check the middle term: ' + m('2(' + lin(a, 0) + ')(' + b + ') = ' + ph([0, 2 * a * b])) + '. The trinomial’s middle term is ' + m(ph([0, poly[1]])) + ', so the binomial is ' + m('(' + lin(a, sgn * b) + ')') + '.', 'Perfect square trinomial: ' + c[0] + '.'] }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      }
    ],
    [ // Level 3
      function () { // grouping, then a difference of squares
        var a, b; do { a = rnz(-6, 6); b = ri(1, 6); } while (a === b || a === -b);
        var facs = [[a, 1], [-b, 1], [b, 1]], poly = prodAll(facs);
        var c = fact(1, facs);
        var w = [fact(1, [[-a, 1], [-b, 1], [b, 1]]), fact(1, [[a, 1], [b * b, 0, 1]]), fact(1, [[a, 1], [-b, 1], [-b, 1]]), fact(1, [[b, 1], [-a, 1], [a, 1]])];
        return attach(Q({ q: 'Factor completely: ' + m(ph(poly)), mc: mcF(c, w), why: ['Group in pairs: ' + m('(' + P([[1, xp(3)], [a, xp(2)]]) + ') + (' + P([[-b * b, X], [-a * b * b, '']]) + ')') + ' = ' + m(xp(2) + bin(1, a) + ' ' + M + ' ' + (b === 1 ? '' : b * b) + bin(1, a)) + '.', 'Factor out the binomial: ' + m(bin(1, a) + '(' + ph([-b * b, 0, 1]) + ')') + '.', 'Keep going: ' + m(ph([-b * b, 0, 1])) + ' is a difference of squares, so the answer is ' + c[0] + '.'] }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      },
      function () { // GCF first, then factor further
        var v = ri(0, 2), c, w, poly, why;
        if (v === 0) {
          var k = ri(2, 6), p = ri(1, 7), monF = function (x) { return x; };
          poly = [0, -k * p * p, 0, k];
          c = fact(k, [[p, 1], [-p, 1]], 'x', X, monF);
          w = [fact(k, [[-p, 1], [-p, 1]], 'x', X, monF), fact(k, [[p, 1], [-p, 1]], 'x', '', null), fact(k, [[p, 1], [p, 1]], 'x', X, monF), fact(k, [[p * p, 0, 1]], 'x', X, monF)];
          why = ['Take out the GCF first: ' + m(ph(poly) + ' = ' + n(k) + X + '(' + ph([-p * p, 0, 1]) + ')') + '.', m(ph([-p * p, 0, 1])) + ' is a difference of squares: ' + m('(' + lin(1, -p) + ')(' + lin(1, p) + ')') + '.', 'Factored completely: ' + c[0] + '.'];
        } else if (v === 1) {
          var k2 = ri(2, 5), p2, q2; do { p2 = rnz(-7, 7); q2 = rnz(-7, 7); } while (p2 === q2 || p2 === -q2);
          poly = pmul([k2], pmul([p2, 1], [q2, 1]));
          c = fact(k2, [[p2, 1], [q2, 1]]);
          w = [fact(k2, [[-p2, 1], [-q2, 1]]), fact(1, [[k2 * p2, k2], [q2 * k2, 1]]), fact(k2, [[p2, 1], [-q2, 1]]), fact(1, [[p2, 1], [q2, 1]])];
          why = ['Take out the GCF ' + k2 + ' first: ' + m(ph(poly) + ' = ' + k2 + '(' + ph(pmul([p2, 1], [q2, 1])) + ')') + '.', 'Factor the trinomial: two numbers with product ' + n(p2 * q2) + ' and sum ' + n(p2 + q2) + ' are ' + n(p2) + ' and ' + n(q2) + '.', 'Factored completely: ' + c[0] + '.'];
        } else {
          var p3 = ri(1, 3), sq = p3 * p3;
          poly = [-sq * sq, 0, 0, 0, 1];
          c = fact(1, [[sq, 0, 1], [p3, 1], [-p3, 1]]);
          w = [fact(1, [[p3, 1], [p3, 1], [-p3, 1], [-p3, 1]]), fact(1, [[sq, 0, 1], [-p3, 1], [-p3, 1]]), fact(1, [[sq, 0, 1], [p3, 1], [p3, 1]]), fact(1, [[-sq, 0, 1], [p3, 1], [-p3, 1]])];
          why = ['Difference of squares: ' + m(ph(poly) + ' = (' + ph([sq, 0, 1]) + ')(' + ph([-sq, 0, 1]) + ')') + '.', 'Keep going: ' + m(ph([-sq, 0, 1]) + ' = (' + lin(1, -p3) + ')(' + lin(1, p3) + ')') + '. The sum ' + m(ph([sq, 0, 1])) + ' does not factor over the real numbers.', 'Factored completely: ' + c[0] + '.'];
        }
        return attach(Q({ q: 'Factor completely: ' + m(ph(poly)), mc: mcF(c, w), why: why }), { t: 'expr', eh: ph(poly), chk: 'factor' });
      },
      function () { // substitution
        var h, p, q; do { h = rnz(-5, 5); p = rnz(-6, 6); q = rnz(-6, 6); } while (p === q || h + p === 0 || h + q === 0 || h === p || h === q || p + q === 0);
        var B = p + q, C = p * q, u = '(' + lin(1, h) + ')';
        var eh = u + '<sup>2</sup>' + K.coef(B, false) + u + sg(C);
        var c = fact(1, [[h + p, 1], [h + q, 1]]);
        var w = [fact(1, [[p, 1], [q, 1]]), fact(1, [[h - p, 1], [h - q, 1]]), fact(1, [[-p, 1], [-q, 1]]), fact(1, [[h + p, 1], [h - q, 1]])];
        return attach(Q({ q: 'Factor ' + m(eh) + '.', mc: mcF(c, w), why: ['Let ' + m('<i>u</i> = ' + lin(1, h)) + '. The expression becomes ' + m('<i>u</i><sup>2</sup>' + K.coef(B, false) + '<i>u</i>' + sg(C)) + '.', 'Factor: ' + m(fmtF(1, '', [[p, 1], [q, 1]], 'u')) + '.', 'Replace ' + m('<i>u</i>') + ' with ' + m(lin(1, h)) + ' and simplify: ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'factor' });
      }
    ]
  ];
  K.lesson('R.4', { title: 'Factoring Polynomials', std: 'Lial 12e · Section R.4', levels: r4 });

  /* ================= R.5 RATIONAL EXPRESSIONS ================= */
  function xne(vals) { vals = vals.slice().sort(function (a, b) { return a - b; }); return vals.map(function (v) { return m(X + ' ' + NE + ' ' + n(v)); }).join(' and '); }
  function fx(f) { return f; }
  var r5 = [
    [ // Level 1
      function () { // domain
        var v = ri(0, 2), num, den, zeros, wr, a, b, why0;
        if (v === 0) {
          b = ri(1, 9); do { a = rnz(-9, 9); } while (a === b || a === -b);
          num = lin(1, a); den = ph([-b * b, 0, 1]); zeros = [-b, b];
          wr = [[-a], [b], [-b * b, b * b]];
          why0 = m(den + ' = (' + lin(1, -b) + ')(' + lin(1, b) + ')') + ' is 0 when ' + m(X + ' = ' + b) + ' or ' + m(X + ' = ' + n(-b)) + '.';
        } else if (v === 1) {
          b = rnz(-9, 9); do { a = rnz(-9, 9); } while (a === -b || a === 0);
          num = lin(1, a); den = ph([0, -b, 1]); zeros = [0, b];
          wr = [[b], [0, -b], [-a]];
          why0 = m(den + ' = ' + X + bin(1, -b)) + ' is 0 when ' + m(X + ' = 0') + ' or ' + m(X + ' = ' + n(b)) + '.';
        } else {
          var r1, r2; do { r1 = rnz(-7, 7); r2 = rnz(-7, 7); a = rnz(-9, 9); } while (r1 === r2 || r1 === -r2 || -a === r1 || -a === r2);
          num = lin(1, a); den = ph(pmul([-r1, 1], [-r2, 1])); zeros = [r1, r2];
          wr = [[-r1, -r2], [-a], [r1, -r2]];
          why0 = 'Factor: ' + m(den + ' = ' + fmtF(1, '', [[-r1, 1], [-r2, 1]])) + ', which is 0 when ' + m(X + ' = ' + n(r1)) + ' or ' + m(X + ' = ' + n(r2)) + '.';
        }
        var eh = fr(num, den);
        return attach(Q({ q: 'What is the domain of ' + m(eh) + '? (All real numbers except…)', mc: mc(xne(zeros), wr.map(xne), function () { return xne([zeros[0] + rnz(1, 3)]); }), why: ['The domain leaves out every value that makes the <b>denominator</b> 0. The numerator does not matter.', why0, 'Domain: all real numbers with ' + xne(zeros) + '.'] }), { t: 'domain', eh: eh });
      },
      function () { // monomial quotient in lowest terms
        var A, B, mE, kE, g; do { g = ri(2, 6); A = g * ri(1, 6); B = g * ri(1, 6); mE = ri(1, 7); kE = ri(1, 7); } while (A === B || mE === kE || gcd(A, B) === 1);
        var co = R(A, B), e = mE - kE;
        var eh = fr(P([[A, xp(mE)]]), P([[B, xp(kE)]]));
        var mkk = function (cc, ee) { return [m(mono(cc, [['x', ee]], true)), monoF(cc, [['x', ee]])]; };
        var c = mkk(co, e);
        var w = [mkk(co, -e), mkk(R(B, A), e), mkk(R(B, A), -e), mkk(co, mE + kE)];
        return attach(Q({ q: 'Write ' + m(eh) + ' in lowest terms. Assume ' + m(X + ' ' + NE + ' 0') + '.', mc: mcF(c, K.shuffle(w).slice(0, 3), null, TPOS), why: ['Divide the coefficients by their GCF, ' + gcd(A, B) + ': ' + m(fr(A, B) + ' = ' + co.html()) + '.', 'Quotient rule on ' + X + ': ' + m(fr(xp(mE), xp(kE))) + (e > 0 ? ' leaves ' + m(xp(e)) + ' in the numerator.' : ' leaves ' + m(xp(-e)) + ' in the denominator.'), 'Answer: ' + c[0] + '.'] }), { t: 'expr', eh: eh, pos: 1 });
      },
      function () { // factor and divide out a common factor
        var k = ri(2, 9), p = rnz(-8, 8), v = K.coin(), num, c, w;
        var den = ph([-p * p, 0, 1]);
        if (v) {
          num = ph([k * p, k]);
          c = [m(fr(n(k), lin(1, -p))), function (x) { return k / (x - p); }];
          w = [[m(fr(n(k), lin(1, p))), function (x) { return k / (x + p); }], [m(fr('1', lin(1, -p))), function (x) { return 1 / (x - p); }], [m(fr(n(k), ph([-p, 0, 1]))), function (x) { return k / (x * x - p); }], [m(fr(n(k * p), lin(1, -p))), function (x) { return k * p / (x - p); }]];
        } else {
          num = ph([0, p, 1]);
          c = [m(fr(X, lin(1, -p))), function (x) { return x / (x - p); }];
          w = [[m(fr(X, lin(1, p))), function (x) { return x / (x + p); }], [m(fr('1', lin(1, -p))), function (x) { return 1 / (x - p); }], [m(fr(X, ph([-p, 0, 1]))), function (x) { return x / (x * x - p); }], [m(fr(lin(1, p), lin(1, -p))), function (x) { return (x + p) / (x - p); }]];
        }
        var eh = fr(num, den);
        return attach(Q({ q: 'Write ' + m(eh) + ' in lowest terms.', mc: mcF(c, K.shuffle(w)), why: ['Factor the numerator: ' + m(num + ' = ' + (v ? n(k) + bin(1, p) : X + bin(1, p))) + '.', 'Factor the denominator: ' + m(den + ' = ' + bin(1, -p) + bin(1, p)) + '.', 'Divide out the common factor ' + m(bin(1, p)) + ': ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'lowest' });
      }
    ],
    [ // Level 2
      function () { // lowest terms, two trinomials
        var r, s, t; do { r = rnz(-7, 7); s = rnz(-7, 7); t = rnz(-7, 7); } while (r === s || s === t || r === t);
        var nu = pmul([-r, 1], [-s, 1]), de = pmul([-s, 1], [-t, 1]);
        var eh = fr(ph(nu), ph(de));
        var c = [m(fr(lin(1, -r), lin(1, -t))), function (x) { return (x - r) / (x - t); }];
        var w = [[m(fr(lin(1, -t), lin(1, -r))), function (x) { return (x - t) / (x - r); }], [m(fr(lin(1, r), lin(1, t))), function (x) { return (x + r) / (x + t); }], [m(R(nu[0], de[0]).html()), function () { return nu[0] / de[0]; }], [m(fr(lin(1, -r), lin(1, -s))), function (x) { return (x - r) / (x - s); }], [m(fr(ph([nu[0], nu[1]]), ph([de[0], de[1]]))), function (x) { return (nu[1] * x + nu[0]) / (de[1] * x + de[0]); }]];
        return attach(Q({ q: 'Write ' + m(eh) + ' in lowest terms.', mc: mcF(c, K.shuffle(w).slice(0, 4)), why: ['Factor the top and bottom: ' + m(fr(fmtF(1, '', [[-r, 1], [-s, 1]]), fmtF(1, '', [[-s, 1], [-t, 1]])))
          + '.', 'Only whole factors divide out (never the ' + m(xp(2)) + ' terms). The common factor is ' + m(bin(1, -s)) + '.', 'Lowest terms: ' + c[0] + ', with ' + xne([s, t]) + '.'] }), { t: 'expr', eh: eh, chk: 'lowest' });
      },
      function () { // add / subtract with unlike denominators
        var a, b, p, q, sub, A, B, ok;
        do {
          a = ri(1, 7); b = ri(1, 7); p = rnz(-6, 6); q = rnz(-6, 6); sub = K.coin();
          var sB = sub ? -1 : 1; A = a + sB * b; B = -a * q - sB * b * p;   // numerator Ax + B
          ok = p !== q && !(A === 0 && B === 0) && (A === 0 || (A * p + B !== 0 && A * q + B !== 0));
        } while (!ok);
        var sB2 = sub ? -1 : 1;
        var dH = bin(1, -p) + bin(1, -q);
        var eh = fr(n(a), lin(1, -p)) + (sub ? ' ' + M + ' ' : ' + ') + fr(n(b), lin(1, -q));
        var c = [m(fr(lin(A, B), dH)), function (x) { return (A * x + B) / ((x - p) * (x - q)); }];
        var w = [[m(fr(n(a + sB2 * b), lin(2, -p - q))), function (x) { return (a + sB2 * b) / (2 * x - p - q); }],
          [m(fr(n(a + sB2 * b), dH)), function (x) { return (a + sB2 * b) / ((x - p) * (x - q)); }],
          [m(fr(lin(a + sB2 * b, -a * p - sB2 * b * q), dH)), function (x) { return ((a + sB2 * b) * x - a * p - sB2 * b * q) / ((x - p) * (x - q)); }]];
        if (sub) w.push([m(fr(lin(a - b, -a * q - b * p), dH)), function (x) { return ((a - b) * x - a * q - b * p) / ((x - p) * (x - q)); }]);
        if (a + sB2 * b === 0) w.splice(0, 2);
        return attach(Q({ q: (sub ? 'Subtract' : 'Add') + ' and simplify: ' + m(eh), mc: mcF(c, K.shuffle(w).slice(0, 3), function () { var z = B + rnz(-4, 4); return [m(fr(lin(A, z), dH)), function (x) { return (A * x + z) / ((x - p) * (x - q)); }]; }), why: ['The denominators share no factor, so the LCD is ' + m(dH) + '.', 'Rewrite the numerators over the LCD: ' + m((a === 1 ? '' : n(a)) + bin(1, -q) + (sub ? ' ' + M + ' ' : ' + ') + (b === 1 ? '' : n(b)) + bin(1, -p)) + (sub ? ' (the minus sign reaches both terms of the second numerator)' : '') + '.', 'Simplify: ' + m(P([[a, X], [-a * q, '']]) + (sub ? ' ' + M + ' (' + P([[b, X], [-b * p, '']]) + ')' : ' + ' + P([[b, X], [-b * p, '']])) + ' = ' + lin(A, B)) + '.', 'Result: ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'lowest' });
      },
      function () { // multiply or divide
        var p, q; do { p = rnz(-6, 6); q = rnz(-6, 6); } while (p === q || p === -q);
        var eh, c, w, why;
        if (K.coin()) {
          eh = '[' + fr(ph([-p * p, 0, 1]), lin(1, q)) + '] ÷ [' + fr(lin(1, -p), ph([-q * q, 0, 1])) + ']';
          c = fact(1, [[p, 1], [-q, 1]]);
          w = [fact(1, [[p, 1], [q, 1]]), [m(fr(lin(1, p), lin(1, -q))), function (x) { return (x + p) / (x - q); }], [m(fr(fmtF(1, '', [[-p, 1], [-p, 1], [p, 1]]), fmtF(1, '', [[q, 1], [q, 1], [-q, 1]]))), function (x) { return (x - p) * (x - p) * (x + p) / ((x + q) * (x + q) * (x - q)); }], fact(1, [[-p, 1], [q, 1]])];
          why = ['To divide, multiply by the reciprocal of the second fraction: ' + m(fr(ph([-p * p, 0, 1]), lin(1, q)) + ' · ' + fr(ph([-q * q, 0, 1]), lin(1, -p))) + '.', 'Factor: ' + m(fr(bin(1, -p) + bin(1, p), lin(1, q)) + ' · ' + fr(bin(1, -q) + bin(1, q), lin(1, -p))) + '.', 'Divide out ' + m(bin(1, -p)) + ' and ' + m(bin(1, q)) + ': ' + c[0] + '.'];
        } else {
          eh = fr(lin(1, p), lin(1, -q)) + ' · ' + fr(ph([-q * q, 0, 1]), ph([-p * p, 0, 1]));
          c = [m(fr(lin(1, q), lin(1, -p))), function (x) { return (x + q) / (x - p); }];
          w = [[m(fr(lin(1, -q), lin(1, p))), function (x) { return (x - q) / (x + p); }], [m(fr(lin(1, q), lin(1, p))), function (x) { return (x + q) / (x + p); }], [m(fr(lin(1, -p), lin(1, q))), function (x) { return (x - p) / (x + q); }], [m(fr(lin(1, -q), lin(1, -p))), function (x) { return (x - q) / (x - p); }]];
          why = ['Factor the second fraction: ' + m(fr(bin(1, -q) + bin(1, q), bin(1, -p) + bin(1, p))) + '.', 'Divide out ' + m(bin(1, p)) + ' (top left, bottom right) and ' + m(bin(1, -q)) + ' (bottom left, top right).', 'What is left: ' + c[0] + '.'];
        }
        return attach(Q({ q: (/÷/.test(eh) ? 'Divide' : 'Multiply') + ' and simplify: ' + m(eh), mc: mcF(c, K.shuffle(w).slice(0, 3)), why: why }), { t: 'expr', eh: eh, chk: 'lowest' });
      }
    ],
    [ // Level 3
      function () { // complex fraction
        var a, b, c, d; do { a = ri(1, 9); b = rnz(-6, 6); c = ri(1, 9); d = rnz(-6, 6); } while (a * d === -b * c || a * d === b * c);
        var top = fr(n(a), X) + sg(-b), bot = fr(n(c), X) + sg(d);
        var eh = fr(top, bot);
        var numH = P([[a, ''], [-b, X]]), denH = P([[c, ''], [d, X]]);
        var C = [m(fr(numH, denH)), function (x) { return (a - b * x) / (c + d * x); }];
        var w = [[m(R(a - b, c + d === 0 ? 1 : c + d).html()), function () { return (a - b) / (c + d === 0 ? 1 : c + d); }],
          [m(fr(P([[a, X], [-b, '']]), P([[c, X], [d, '']]))), function (x) { return (a * x - b) / (c * x + d); }],
          [m(fr(numH, P([[c, X], [d, '']]))), function (x) { return (a - b * x) / (c * x + d); }],
          [m(fr(P([[a, ''], [b, X]]), P([[c, ''], [-d, X]]))), function (x) { return (a + b * x) / (c - d * x); }]];
        if (c + d === 0) w.shift();
        return attach(Q({ q: 'Simplify the complex fraction ' + m(eh) + '.', mc: mcF(C, w, function () { var z = rnz(1, 4); return [m(fr(P([[a + z, ''], [-b, X]]), denH)), function (x) { return (a + z - b * x) / (c + d * x); }]; }), why: ['The only small denominator is ' + X + ', so multiply the top and bottom of the big fraction by ' + X + '.', 'Top: ' + m(X + '(' + top + ') = ' + numH) + '. Bottom: ' + m(X + '(' + bot + ') = ' + denH) + '. Every term gets multiplied, including the constants.', 'Result: ' + C[0] + '.'] }), { t: 'expr', eh: eh, chk: 'lowest' });
      },
      function () { // add / subtract when one denominator factors
        var a, b, p, sub, A, B; do { a = rnz(-9, 9); b = ri(1, 6); p = ri(1, 7); sub = K.coin(); A = sub ? -b : b; B = sub ? a + b * p : a - b * p; } while (a === 0 || (!sub && a === 2 * b * p) || (sub && a === -2 * b * p) || B === 0);
        // a/(x² − p²) ± b/(x + p) = (A x + B)/((x − p)(x + p))
        var eh = fr(n(a), ph([-p * p, 0, 1])) + (sub ? ' ' + M + ' ' : ' + ') + fr(n(b), lin(1, p));
        var dH = bin(1, -p) + bin(1, p);
        var c = [m(fr(lin(A, B), dH)), function (x) { return (A * x + B) / ((x - p) * (x + p)); }];
        var sB = sub ? -1 : 1;
        var w = [[m(fr(n(a + sB * b), dH)), function (x) { return (a + sB * b) / ((x - p) * (x + p)); }],
          [m(fr(lin(sB * b, a + sB * b * p), dH)), function (x) { return (sB * b * x + a + sB * b * p) / ((x - p) * (x + p)); }],
          [m(fr(n(a + sB * b), ph([-p * p + p, 1, 1]))), function (x) { return (a + sB * b) / (x * x + x - p * p + p); }],
          [m(fr(lin(A, B), '(' + lin(1, p) + ')(' + ph([-p * p, 0, 1]) + ')')), function (x) { return (A * x + B) / ((x + p) * (x * x - p * p)); }]];
        return attach(Q({ q: (sub ? 'Subtract' : 'Add') + ' and simplify: ' + m(eh), mc: mcF(c, K.shuffle(w).slice(0, 3), function () { var z = B + rnz(-4, 4); return [m(fr(lin(A, z), dH)), function (x) { return (A * x + z) / ((x - p) * (x + p)); }]; }), why: ['Factor: ' + m(ph([-p * p, 0, 1]) + ' = ' + dH) + ', so the LCD is ' + m(dH) + '.', 'Multiply the second fraction by ' + m(fr(lin(1, -p), lin(1, -p))) + ': its numerator becomes ' + m((b === 1 ? '' : n(b) + bin(1, -p) + ' = ') + lin(b, -b * p)) + '.', 'Combine: ' + m(n(a) + (sub ? ' ' + M + ' (' + lin(b, -b * p) + ')' : ' + ' + lin(b, -b * p)) + ' = ' + lin(A, B)) + ', so the result is ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'lowest' });
      },
      function () { // average cost word problem
        var F, c, n1, n2, tries = 0;
        do { F = pick([480, 600, 720, 840, 900, 960, 1080, 1200]); c = pick([8, 10, 12, 15, 18, 20, 25]); var ds = range(15, 80).filter(function (z) { return F % z === 0; }); n1 = pick(ds); n2 = pick(ds); } while (n2 <= n1 || F / n1 - F / n2 < 2);
        var a1 = F / n1 + c, a2 = F / n2 + c, diff = a1 - a2;
        return attach(Q({ q: 'A school charters a bus for ' + money(F) + ' and pays ' + money(c) + ' per student for museum tickets. With ' + m(X) + ' students, the average cost per student is ' + m(fr(F + ' + ' + c + X, X)) + ' dollars. How much less is the average cost per student with ' + n2 + ' students than with ' + n1 + ' students?', mc: K.mc(money(diff), [money(a2), money(a1), money(F / (n2 - n1)), money(diff + c)], function () { var z = diff + rnz(-4, 4); return money(z > 0 ? z : diff + rnz(5, 8)); }), why: ['With ' + n1 + ' students: ' + m(fr(F + ' + ' + c + '(' + n1 + ')', n1) + ' = ' + fr(F + c * n1, n1) + ' = ' + a1) + ' dollars.', 'With ' + n2 + ' students: ' + m(fr(F + ' + ' + c + '(' + n2 + ')', n2) + ' = ' + fr(F + c * n2, n2) + ' = ' + a2) + ' dollars.', 'Difference: ' + m(money(a1) + ' ' + M + ' ' + money(a2) + ' = ' + money(diff)) + '. Only the bus share changes; the ' + money(c) + ' ticket cost is the same for everyone.'] }), { t: 'cost', F: F, c: c, n1: n1, n2: n2 });
      }
    ]
  ];
  K.lesson('R.5', { title: 'Rational Expressions', std: 'Lial 12e · Section R.5', levels: r5 });

  /* ================= R.6 RATIONAL EXPONENTS ================= */
  function powH(base, e) { return (base < 0 ? '(' + n(base) + ')' : n(base)) + '<sup>' + expS(e) + '</sup>'; }
  function rv(r) { return [R(r).html(), function () { return R(r).val(); }]; }
  function rvm(r) { return [m(R(r).html()), function () { return R(r).val(); }]; }
  var r6 = [
    [ // Level 1
      function () { // a^(m/n)
        var nn, rr, mm; do { nn = ri(2, 5); rr = ri(2, 5); mm = ri(1, 4); } while (ipow(rr, nn) > 625 || gcd(mm, nn) !== 1 || mm === nn || ipow(rr, mm) > 300);
        var b = ipow(rr, nn), val = ipow(rr, mm), eh = powH(b, R(mm, nn));
        var w = [R(b * mm, nn), R(rr), R(1, val), R(rr * mm)];
        return attach(Q({ q: 'Evaluate ' + m(eh) + '.', mc: mcF(rvm(val), w.map(rvm), function () { return rvm(val + rnz(1, 5)); }), why: ['Read ' + m('<i>a</i><sup><i>m</i>/<i>n</i></sup>') + ' as a root, then a power: the denominator is the root, the numerator is the power.', m(b + '<sup>1/' + nn + '</sup> = ' + rr) + ' because ' + m(rr + '<sup>' + nn + '</sup> = ' + b) + '.', (mm > 1 ? 'Then the power: ' + m(rr + '<sup>' + mm + '</sup> = ' + val) + '.' : 'The power is 1, so the value is ' + val + '.') + ' (A rational exponent is not multiplication: ' + m(b + ' · ' + fr(mm, nn)) + ' is wrong.)'] }), { t: 'num', eh: eh });
      },
      function () { // negative integer exponent
        var b, k; do { b = ri(2, 6); k = ri(1, 4); } while (ipow(b, k) > 300 || (k === 1 && b < 3));
        var fracBase = K.coin() && k <= 3, eh, val, w, why;
        if (fracBase) {
          var top; do { top = ri(1, 5); } while (gcd(top, b) !== 1 || top === b || ipow(top, k) > 300);
          eh = '(' + fr(top, b) + ')<sup>' + M + k + '</sup>';
          val = R(ipow(b, k), ipow(top, k));
          w = [R(ipow(top, k), ipow(b, k)), R(-ipow(b, k), ipow(top, k)), R(-top * k, b)];
          why = ['A negative exponent means reciprocal: ' + m('(' + fr('<i>a</i>', '<i>b</i>') + ')<sup>' + M + '<i>n</i></sup> = (' + fr('<i>b</i>', '<i>a</i>') + ')<sup><i>n</i></sup>') + '.', m('(' + fr(b, top) + ')<sup>' + k + '</sup> = ' + val.html()) + '.', 'The negative exponent does not make the answer negative.'];
        } else {
          eh = n(b) + '<sup>' + M + k + '</sup>';
          val = R(1, ipow(b, k));
          w = [R(-ipow(b, k)), R(-1, ipow(b, k)), R(-b * k)];
          why = ['A negative exponent means reciprocal: ' + m('<i>a</i><sup>' + M + '<i>n</i></sup> = ' + fr('1', '<i>a</i><sup><i>n</i></sup>')) + '.', (k === 1 ? 'So ' : m(b + '<sup>' + k + '</sup> = ' + ipow(b, k)) + ', so ') + m(eh + ' = ' + val.html()) + '.', 'It is not ' + m(n(-ipow(b, k))) + ': the negative sign moves the power to the denominator.'];
        }
        return attach(Q({ q: 'Evaluate ' + m(eh) + '.', mc: mcF(rvm(val), w.map(rvm), function () { return rvm(val.add(rnz(1, 3))); }), why: why }), { t: 'num', eh: eh });
      },
      function () { // product or quotient rule with fractional exponents
        var e1, e2, res, prod = K.coin(), eh, tries = 0;
        do {
          e1 = R(ri(1, 5), pick([2, 3, 4, 5, 6])); e2 = R(ri(1, 5), pick([2, 3, 4, 5, 6]));
          res = prod ? e1.add(e2) : e1.sub(e2);
        } while ((e1.d === 1 || e2.d === 1 || e1.d === e2.d || res.n <= 0 || res.eq(1) || e1.eq(e2)) && tries++ < 200);
        if (res.n <= 0) { e1 = R(1, 2); e2 = R(1, 3); res = prod ? e1.add(e2) : e1.sub(e2); }
        eh = prod ? vpow('x', e1) + ' · ' + vpow('x', e2) : fr(vpow('x', e1), vpow('x', e2));
        var LD = K.lcm(e1.d, e2.d);
        var mk = function (e) { return [m(mono(1, [['x', e]], true)), monoF(1, [['x', e]])]; };
        var w = [mk(prod ? e1.mul(e2) : e1.div(e2)), mk(R(e1.n + (prod ? e2.n : -e2.n), e1.d + e2.d)), mk(R(res.d, res.n)), mk(prod ? e1.sub(e2).abs() : e1.add(e2))];
        return attach(Q({ q: 'Simplify ' + m(eh) + '. Write the answer with a positive exponent; assume ' + m(X + ' &gt; 0') + '.', mc: mcF(mk(res), w, function () { return mk(res.add(R(rnz(1, 3), res.d))); }, TPOS), why: [prod ? 'Product rule: same base, <b>add</b> the exponents.' : 'Quotient rule: same base, <b>subtract</b> the exponents.', 'Use a common denominator: ' + m(expS(e1) + (prod ? ' + ' : ' ' + M + ' ') + expS(e2) + ' = ' + (e1.n * LD / e1.d) + '/' + LD + (prod ? ' + ' : ' ' + M + ' ') + (e2.n * LD / e2.d) + '/' + LD + ' = ' + expS(res)) + '.', 'Answer: ' + mk(res)[0] + '.'] }), { t: 'expr', eh: eh, pos: 1 });
      }
    ],
    [ // Level 2
      function () { // a^(−m/n), negative bases, real or not
        var v = ri(0, 3), eh, c, w, why, rr, nn, mm, b;
        if (v === 0) {
          do { nn = ri(2, 5); rr = ri(2, 5); mm = ri(1, 3); } while (ipow(rr, nn) > 625 || gcd(mm, nn) !== 1 || ipow(rr, mm) > 200);
          b = ipow(rr, nn); eh = powH(b, R(-mm, nn));
          var val = R(1, ipow(rr, mm));
          c = rvm(val); w = [rvm(ipow(rr, mm)), rvm(-ipow(rr, mm)), rvm(R(-b * mm, nn)), rvm(R(-1, ipow(rr, mm)))];
          why = ['Negative exponent → reciprocal: ' + m(eh + ' = ' + fr('1', powH(b, R(mm, nn)))) + '.', 'Root first: ' + m(b + '<sup>1/' + nn + '</sup> = ' + rr) + (mm > 1 ? ', then the power: ' + m(rr + '<sup>' + mm + '</sup> = ' + ipow(rr, mm)) : '') + '.', 'Answer: ' + m(val.html()) + '.'];
        } else if (v === 1) {
          do { nn = pick([3, 5]); rr = ri(2, 4); mm = ri(1, 4); } while (ipow(rr, nn) > 1024 || gcd(mm, nn) !== 1 || ipow(rr, mm) > 100);
          b = -ipow(rr, nn); eh = powH(b, R(mm, nn));
          var v1 = ipow(-rr, mm);
          c = rvm(v1); w = [rvm(-v1), ['Not a real number', null], rvm(R(1, v1))];
          why = ['An <b>odd</b> root of a negative number is real: ' + m('(' + n(b) + ')<sup>1/' + nn + '</sup> = ' + n(-rr)) + ' because ' + m('(' + n(-rr) + ')<sup>' + nn + '</sup> = ' + n(b)) + '.', mm > 1 ? 'Then the power: ' + m('(' + n(-rr) + ')<sup>' + mm + '</sup> = ' + n(v1)) + '.' : 'The power is 1, so nothing more to do.', 'Answer: ' + m(n(v1)) + '.'];
        } else if (v === 2) {
          rr = ri(2, 9); mm = pick([1, 3]); if (ipow(rr, mm) > 300) mm = 1;
          b = rr * rr; eh = M + powH(b, R(mm, 2));
          var v2 = -ipow(rr, mm);
          c = rvm(v2); w = [['Not a real number', null], rvm(-v2), rvm(R(-1, ipow(rr, mm)))];
          why = ['Without parentheses, the exponent applies only to ' + b + '; the negative sign is applied afterward.', m(b + '<sup>' + expS(R(mm, 2)) + '</sup> = ' + (mm > 1 ? rr + '<sup>' + mm + '</sup> = ' : '') + ipow(rr, mm)) + '.', 'So the value is ' + m(n(v2)) + ', a real number.'];
        } else {
          rr = ri(2, 9); mm = pick([1, 3]); if (ipow(rr, mm) > 300) mm = 1;
          b = -rr * rr; eh = powH(b, R(mm, 2));
          c = ['Not a real number', null]; w = [rvm(-ipow(rr, mm)), rvm(ipow(rr, mm)), rvm(R(1, ipow(rr, mm)))];
          why = ['The denominator 2 of the exponent means a square root.', 'No real number squared gives ' + m(n(b)) + ', so ' + m('(' + n(b) + ')<sup>1/2</sup>') + ' is not real.', (mm > 1 ? 'So ' + m(eh + ' = ((' + n(b) + ')<sup>1/2</sup>)<sup>' + mm + '</sup>') + ' is not a real number either. ' : '') + 'Compare ' + m(M + rr * rr + '<sup>1/2</sup> = ' + n(-rr)) + ', where the negative sign is outside the power.'];
        }
        var o = Q({ q: 'Evaluate ' + m(eh) + '.', mc: mcF(c, w, function () { return rvm(R(rnz(-30, 30), pick([1, 1, 2, 3, 4]))); }), why: why });
        return attach(o, { t: 'num', eh: eh });
      },
      function () { // (x^a y^b)^k with fractional exponents
        var k = pick([2, 3, 4, 6]), e1, e2, d1, d2;
        var dv = [1, 2, 3, 4, 6].filter(function (z) { return k % z === 0 && z > 1; });
        d1 = pick(dv); d2 = pick(dv);
        do { e1 = R(ri(1, 5), d1); } while (e1.d !== d1);
        do { e2 = R(-ri(1, 5), d2); } while (e2.d !== d2);
        var X1 = e1.mul(k), Y1 = e2.mul(k);
        var eh = '(' + vpow('x', e1) + vpow('y', e2) + ')<sup>' + k + '</sup>';
        var mk = function (a, b) { return [m(mono(1, [['x', a], ['y', b]], true)), monoF(1, [['x', a], ['y', b]])]; };
        var c = mk(X1, Y1);
        var w = [mk(e1.add(k), e2.add(k)), mk(X1, Y1.neg()), mk(X1.neg(), Y1), mk(e1.add(k), Y1)];
        return attach(Q({ q: 'Simplify ' + m(eh) + '. Write the answer with only positive exponents; assume all variables are positive.', mc: mcF(c, w, function () { return mk(X1.add(rnz(1, 3)), Y1); }, TPOS), why: ['Raise each factor to the power ' + k + ' by <b>multiplying</b> exponents: ' + m('(' + vpow('x', e1) + ')<sup>' + k + '</sup> = ' + vpow('x', X1)) + ' and ' + m('(' + vpow('y', e2) + ')<sup>' + k + '</sup> = ' + vpow('y', Y1)) + '.', 'A negative exponent moves its factor to the denominator: ' + m(vpow('y', Y1) + ' = ' + fr('1', vpow('y', Y1.neg()))) + '.', 'Answer: ' + c[0] + '.'] }), { t: 'expr', eh: eh, pos: 1 });
      },
      function () { // (c a^p b^q)^r
        var r = pick([R(1, 2), R(-1, 2), R(1, 3), R(-1, 3), R(3, 2), R(-3, 2), R(2, 3), R(-2, 3)]);
        var t = r.d === 2 ? ri(2, 5) : ri(2, 3), cc = ipow(t, r.d);
        var p = r.d * ri(1, 2) * (K.coin() ? 1 : -1), q; do { q = rnz(-5, 5); } while (q % r.d === 0 && K.coin());
        var co = r.n > 0 ? R(ipow(t, r.n)) : R(1, ipow(t, -r.n));
        var A1 = R(p).mul(r), B1 = R(q).mul(r);
        var eh = '(' + n(cc) + vpow('a', p) + vpow('b', q) + ')<sup>' + expS(r) + '</sup>';
        var mk = function (c0, a, b) { return [m(mono(c0, [['a', a], ['b', b]], true)), monoF(c0, [['a', a], ['b', b]])]; };
        var c = mk(co, A1, B1);
        var w = [mk(R(1, 1).div(co), A1, B1), mk(co, A1.neg(), B1.neg()), mk(co, A1, R(q).add(r)), mk(R(cc).mul(r), A1, B1)];
        return attach(Q({ q: 'Simplify ' + m(eh) + '. Write the answer with only positive exponents; assume all variables are positive.', mc: mcF(c, w, function () { return mk(co, A1.add(1), B1); }, TPOS), why: ['Raise every factor to the ' + m(expS(r)) + ' power: ' + m(cc + '<sup>' + expS(r) + '</sup>') + ', ' + m('(' + vpow('a', p) + ')<sup>' + expS(r) + '</sup>') + ', ' + m('(' + vpow('b', q) + ')<sup>' + expS(r) + '</sup>') + '.', m(cc + '<sup>' + expS(r) + '</sup> = ' + co.html()) + ' (root ' + r.d + ' of ' + cc + ' is ' + t + (r.n < 0 ? '; the negative exponent gives a reciprocal' : '') + '). Multiply the exponents: ' + m(vpow('a', A1)) + ' and ' + m(vpow('b', B1)) + '.', 'With positive exponents only: ' + c[0] + '.'] }), { t: 'expr', eh: eh, pos: 1 });
      }
    ],
    [ // Level 3
      function () { // factor out the least power
        var e = pick([R(-1, 2), R(1, 2), R(-1, 3), R(1, 3), R(-3, 2), R(3, 2), R(2, 3), R(-2, 3), R(1, 4), R(-1, 4)]);
        var d = pick([1, 2]), g = ri(1, 5), u, v; do { u = rnz(-6, 6); v = rnz(-6, 6); } while (gcd(u, v) !== 1 || (u < 0 && v < 0));
        var e2 = e.add(d);
        var t1 = [g * u, e], t2 = [g * v, e2];
        var terms = K.coin() ? [t1, t2] : [t2, t1];
        var eh = mono(terms[0][0], [['x', terms[0][1]]]) + (terms[1][0] < 0 ? ' ' + M + ' ' : ' + ') + mono(Math.abs(terms[1][0]), [['x', terms[1][1]]]);
        var gH = mono(g, [['x', e]]), gFn = monoF(g, [['x', e]]);
        var inner = function (vv, dd, uu) { return '(' + (vv < 0 && uu > 0 ? P([[uu, ''], [vv, xp(dd)]]) : P([[vv, xp(dd)], [uu, '']])) + ')'; };   // positive term first
        var mk = function (pre, preF, vv, dd, uu) { return [m(pre + inner(vv, dd, uu)), function (x) { return preF(x) * (vv * Math.pow(x, dd) + uu); }]; };
        var c = mk(gH, gFn, v, d, u);
        var w = [mk(gH, gFn, v, d + 1, u), mk(gH, gFn, v, d, -u), mk(mono(g, [['x', e2]]), monoF(g, [['x', e2]]), u, d, v), mk(mono(1, [['x', e]]), monoF(1, [['x', e]]), v, d, u)];
        return attach(Q({ q: 'Factor out the least power of ' + X + ': ' + m(eh) + '. Assume ' + m(X + ' &gt; 0') + '.', mc: mcF(c, w, function () { return mk(gH, gFn, v + rnz(1, 2), d, u); }, TPOS), why: ['The exponents are ' + m(expS(e)) + ' and ' + m(expS(e2)) + '. The smaller one is ' + m(expS(e)) + (g > 1 ? ', and the GCF of the coefficients is ' + g : '') + ', so factor out ' + m(gH) + '.', 'Divide each term by ' + m(gH) + ' (subtract exponents): ' + m(mono(g * u, [['x', e]]) + ' → ' + n(u)) + ' and ' + m(mono(g * v, [['x', e2]]) + ' → ' + P([[v, xp(d)]])) + ', because ' + m(expS(e2) + ' ' + M + ' ' + (e.n < 0 ? '(' + expS(e) + ')' : expS(e)) + ' = ' + d) + '.', 'Answer: ' + c[0] + '. Check: distributing gives back the original.'] }), { t: 'expr', eh: eh });
      },
      function () { // metabolic rate / scaling word problem
        var v = K.coin(), t, k, ans, e, why, w;
        if (v) { t = ri(2, 4); k = ipow(t, 4); e = R(3, 4); ans = ipow(t, 3); }
        else { t = ri(2, 5); k = ipow(t, 3); e = R(2, 3); ans = t * t; }
        var q = v ? 'Biologists model an animal’s metabolic rate as proportional to ' + m('<i>M</i><sup>3/4</sup>') + ', where ' + m('<i>M</i>') + ' is body mass. One animal is ' + k + ' times as heavy as another. How many times as large is its metabolic rate?'
          : 'The surface area of similar-shaped animals is proportional to ' + m('<i>M</i><sup>2/3</sup>') + ', where ' + m('<i>M</i>') + ' is body mass. One animal is ' + k + ' times as heavy as another. How many times as large is its surface area?';
        w = [R(k * e.n, e.d), R(k), R(t), R(1, ans)];
        return attach(Q({ q: q, mc: mcF(rvm(ans), w.map(rvm), function () { return rvm(ans + rnz(1, 5)); }), why: ['If the mass is multiplied by ' + k + ', the quantity is multiplied by ' + m(k + '<sup>' + expS(e) + '</sup>') + '.', 'Root first: ' + m(k + '<sup>1/' + e.d + '</sup> = ' + t) + ' because ' + m(t + '<sup>' + e.d + '</sup> = ' + k) + '.', 'Then the power: ' + m(t + '<sup>' + e.n + '</sup> = ' + ans) + '. So it is ' + ans + ' times as large, not ' + k + ' times.'] }), { t: 'scale', k: k, e: e.toString() });
      },
      function () { // combine product and quotient rules with coefficients
        var e1, e2, e3, res, c1, c2, c3, tries = 0;
        do {
          e1 = R(ri(1, 5), pick([2, 3, 4])); e2 = R(ri(1, 5), pick([2, 3, 4, 6])); e3 = R(rnz(-5, 5), pick([2, 3, 6]));
          res = e1.add(e2).sub(e3);
          c3 = ri(2, 6); c1 = ri(2, 9); c2 = ri(2, 9);
        } while ((res.n === 0 || (c1 * c2) % c3 !== 0 || e1.d === 1 || e2.d === 1 || e3.d === 1 || e1.d === e2.d || res.eq(1)) && tries++ < 500);
        if (res.n === 0 || res.eq(1)) { e1 = R(1, 2); e2 = R(2, 3); e3 = R(-1, 6); res = R(4, 3); c1 = 4; c2 = 3; c3 = 6; }
        var co = R(c1 * c2, c3);
        var eh = fr('(' + mono(c1, [['x', e1]]) + ')(' + mono(c2, [['x', e2]]) + ')', mono(c3, [['x', e3]]));
        var mk = function (cc, ee) { return [m(mono(cc, [['x', ee]], true)), monoF(cc, [['x', ee]])]; };
        var c = mk(co, res);
        var w = [mk(co, e1.add(e2).add(e3)), mk(R(c1 + c2, c3), res), mk(co, e1.mul(e2).sub(e3)), mk(co, res.neg())];
        return attach(Q({ q: 'Simplify ' + m(eh) + '. Write the answer with only positive exponents; assume ' + m(X + ' &gt; 0') + '.', mc: mcF(c, w, function () { return mk(co.add(rnz(1, 3)), res); }, TPOS), why: ['Coefficients: ' + m(fr(c1 + ' · ' + c2, c3) + ' = ' + co.html()) + '.', 'Exponents of ' + X + ': add for the product, subtract for the quotient: ' + m(expS(e1) + ' + ' + expS(e2) + ' ' + M + ' ' + (e3.n < 0 ? '(' + expS(e3) + ')' : expS(e3)) + ' = ' + expS(res)) + ' (use a common denominator).', 'Answer with a positive exponent: ' + c[0] + '.'] }), { t: 'expr', eh: eh, pos: 1 });
      }
    ]
  ];
  K.lesson('R.6', { title: 'Rational Exponents', std: 'Lial 12e · Section R.6', levels: r6 });

  /* ================= R.7 RADICALS ================= */
  function radSum(cst, co, f) { return (co < 0 && cst > 0) ? P([[cst, ''], [co, rootH(f, 2)]]) : P([[co, rootH(f, 2)], [cst, '']]); }      // co√f + cst (constant first when only the radical is negative)
  function radSumC(cst, co, f) { return P([[cst, ''], [co, rootH(f, 2)]]); }     // cst + co√f
  function rsF(cst, co, f) { return function () { return cst + co * Math.sqrt(f); }; }
  var r7 = [
    [ // Level 1
      function () { // simplify √N or ∛N
        var cube = K.coin(), idx = cube ? 3 : 2, s, f, N;
        do { s = cube ? ri(2, 5) : ri(2, 10); f = cube ? pick([2, 3, 4, 5, 6, 7, 9, 10]) : pick(SQF); N = ipow(s, idx) * f; } while (N > (cube ? 1000 : 600));
        var rt = function (v) { return cube ? cbrtR(v) : Math.sqrt(v); };
        var mk = function (c, r) { return [m(radH(c, r, idx)), function () { return c * rt(r); }]; };
        var c = mk(s, f);
        var w = [mk(ipow(s, idx), f), sqf(s, idx)[0] === 1 ? mk(f, s) : null, mk(s + 1, f), mk(s, f * s)];
        return attach(Q({ q: 'Simplify ' + m(rootH(N, idx)) + '.', mc: mcF(c, w, function () { return mk(s + ri(2, 4), f); }), why: ['Find the largest perfect ' + (cube ? 'cube' : 'square') + ' factor of ' + N + ': ' + m(N + ' = ' + ipow(s, idx) + ' · ' + f) + '.', m(rootH(N, idx) + ' = ' + rootH(ipow(s, idx), idx) + ' · ' + rootH(f, idx) + ' = ' + radH(s, f, idx)) + '.', 'The ' + (cube ? 'cube' : 'square') + ' root of ' + ipow(s, idx) + ' is ' + s + ', not ' + ipow(s, idx) + '.'] }), { t: 'expr', eh: rootH(N, idx), chk: 'rad' });
      },
      function () { // radical ↔ rational exponent
        var nn = pick([3, 4, 5]), mm; do { mm = ri(1, nn - 1); } while (gcd(mm, nn) !== 1);
        var toExp = K.coin(), rad = rootH(mm === 1 ? X : xp(mm), nn), ex = vpow('x', R(mm, nn));
        var f = function (e) { return function (x) { return Math.pow(x, e); }; };
        var c, w, q, why;
        if (toExp) {
          q = 'Write ' + m(rad) + ' using a rational exponent. Assume ' + m(X + ' &gt; 0') + '.';
          c = [m(ex), f(mm / nn)];
          w = [[m(vpow('x', R(nn, mm))), f(nn / mm)], [m(xp(mm * nn)), f(mm * nn)], [m(vpow('x', R(-mm, nn))), f(-mm / nn)]];
          why = ['The index becomes the denominator and the power becomes the numerator: ' + m('<span class="rad"><sup class="ri"><i>n</i></sup>√<span class="rc"><i>a</i><sup><i>m</i></sup></span></span> = <i>a</i><sup><i>m</i>/<i>n</i></sup>') + '.', 'Here the index is ' + nn + ' and the power is ' + mm + ', so ' + m(rad + ' = ' + ex) + '.'];
        } else {
          q = 'Write ' + m(ex) + ' in radical form. Assume ' + m(X + ' &gt; 0') + '.';
          c = [m(rad), f(mm / nn)];
          w = [[m(mm === 1 ? xp(nn) : rootH(xp(nn), mm)), f(nn / mm)], [m(fr('1', rad)), f(-mm / nn)], [m(rootH(xp(mm + 1), nn)), f((mm + 1) / nn)], [m(n(mm) + rootH(X, nn, true)), function (x) { return mm * Math.pow(x, 1 / nn); }]];
          why = ['The denominator of the exponent is the index of the root; the numerator is the power: ' + m('<i>a</i><sup><i>m</i>/<i>n</i></sup> = ' + '<span class="rad"><sup class="ri"><i>n</i></sup>√<span class="rc"><i>a</i><sup><i>m</i></sup></span></span>') + '.', 'Index ' + nn + ', power ' + mm + ': ' + m(ex + ' = ' + rad) + '.'];
        }
        return attach(Q({ q: q, mc: mcF(c, w, function () { var e = R(ri(1, 9), ri(2, 7)); return toExp ? [m(vpow('x', e)), f(e.val())] : [m(rootH(e.n === 1 ? X : xp(e.n), e.d)), f(e.val())]; }, TPOS), why: why }), { t: 'expr', eh: toExp ? rad : ex, pos: 1 });
      },
      function () { // product rule √a · √b
        var a, b, pr, sf; do { a = ri(2, 20); b = ri(2, 20); pr = a * b; sf = sqf(pr); } while (a === b || isSq(a) || isSq(b) || sf[0] === 1 || pr > 400);
        var c = [m(radH(sf[0], sf[1])), function () { return Math.sqrt(pr); }];
        var mk = function (cc, r) { return [m(radH(cc, r)), function () { return cc * Math.sqrt(r); }]; };
        var sa = sqf(a + b);
        var w = [mk(sa[0], sa[1]), [m(n(pr)), function () { return pr; }], mk(sf[0] * sf[0], sf[1]), sqf(sf[0])[0] === 1 && sf[1] > 1 ? mk(sf[1], sf[0]) : null];
        return attach(Q({ q: 'Multiply and simplify: ' + m(K.sqrt(a) + ' · ' + K.sqrt(b)), mc: mcF(c, w, function () { return mk(sf[0] + rnz(1, 3), sf[1]); }), why: ['Product rule: ' + m(K.sqrt(a) + ' · ' + K.sqrt(b) + ' = ' + K.sqrt(a + ' · ' + b) + ' = ' + K.sqrt(pr)) + '.', sf[1] === 1 ? m(pr + ' = ' + sf[0] + '<sup>2</sup>') + ', a perfect square.' : 'Largest perfect-square factor: ' + m(pr + ' = ' + sf[0] * sf[0] + ' · ' + sf[1]) + '.', 'Answer: ' + c[0] + '. (The product rule multiplies radicands; it never adds them.)'] }), { t: 'expr', eh: K.sqrt(a) + ' · ' + K.sqrt(b), chk: 'rad' });
      }
    ],
    [ // Level 2
      function () { // combine like radicals
        var f = pick([2, 3, 5, 6, 7]), a, b, p, q, sub = K.coin(), tot;
        do { a = ri(2, 5); b = ri(2, 5); p = ri(1, 6); q = ri(1, 6); tot = p * a + (sub ? -1 : 1) * q * b; } while (a === b || tot === 0 || a * a * f > 200 || b * b * f > 200);
        var N1 = a * a * f, N2 = b * b * f;
        var eh = radH(p, N1) + (sub ? ' ' + M + ' ' : ' + ') + radH(q, N2);
        var mk = function (cc, r) { return [m(radH(cc, r)), function () { return cc * Math.sqrt(r); }]; };
        var c = mk(tot, f);
        var w = [p + (sub ? -1 : 1) * q !== 0 ? mk(p + (sub ? -1 : 1) * q, sub ? Math.abs(N1 - N2) : N1 + N2) : null, ['They cannot be combined.', null], mk(p * a - (sub ? -1 : 1) * q * b, f), mk(a + (sub ? -1 : 1) * b, f)];
        return attach(Q({ q: 'Simplify ' + m(eh) + '.', mc: mcF(c, w, function () { return mk(tot + rnz(1, 3), f); }), why: ['Simplify each radical first: ' + m(K.sqrt(N1) + ' = ' + radH(a, f)) + ' and ' + m(K.sqrt(N2) + ' = ' + radH(b, f)) + '.', 'Multiply by the coefficients: ' + m(radH(p * a, f)) + ' and ' + m(radH(q * b, f)) + '. Now they are like radicals.', 'Combine: ' + m(n(p * a) + (sub ? ' ' + M + ' ' : ' + ') + n(q * b) + ' = ' + n(tot)) + ', so the answer is ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'rad' });
      },
      function () { // radicals with variables
        var cube = K.coin(), idx = cube ? 3 : 2, s, f, a, r, N;
        do { s = ri(2, cube ? 3 : 6); f = cube ? pick([2, 3, 4, 5]) : pick([2, 3, 5, 6, 7]); N = ipow(s, idx) * f; } while (N > 200);
        a = ri(1, 3); r = cube ? ri(1, 2) : 1;
        var E = idx * a + r;
        var inH = function (cc, rr) { return n(cc) + xp(rr); };
        var eh = rootH(n(N) + xp(E), idx);
        var rt = function (v) { return cube ? cbrtR(v) : Math.sqrt(v); };
        var mk = function (cc, ea, rc, er) { var pre = (cc === 1 ? '' : n(cc)) + xp(ea); return [m(pre + rootH(inH(rc, er), idx, pre !== '')), function (x) { return cc * Math.pow(x, ea) * rt(rc * Math.pow(x, er)); }]; };
        var c = mk(s, a, f, r);
        var w = [mk(ipow(s, idx), a, f, r), mk(s, idx * a, f, r), mk(s, a, f, 0), mk(s, a + 1, f, r)];
        w[2] = [m(n(s) + xp(a) + rootH(n(f), idx, true)), function (x) { return s * Math.pow(x, a) * rt(f); }];
        return attach(Q({ q: 'Simplify ' + m(eh) + '. Assume ' + m(X + ' ≥ 0') + '.', mc: mcF(c, w, null, TPOS), why: ['Split into perfect ' + (cube ? 'cubes' : 'squares') + ' and what is left: ' + m(N + ' = ' + ipow(s, idx) + ' · ' + f) + ' and ' + m(xp(E) + ' = ' + xp(idx * a) + (r ? ' · ' + xp(r) : '')) + '.', 'The ' + (cube ? 'cube' : 'square') + ' root of the perfect part comes out: ' + m(rootH(ipow(s, idx) + xp(idx * a), idx) + ' = ' + n(s) + xp(a)) + '.', 'Answer: ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'rad', pos: 1 });
      },
      function () { // rationalize a single square root
        var b = pick([2, 3, 5, 6, 7, 10, 11, 14, 15]), a; do { a = ri(1, 12); } while (gcd(a, b) === 1 && K.coin());
        var g = gcd(a, b), top = a / g, bot = b / g;
        var ansH = bot === 1 ? radH(top, b) : fr(radH(top, b), bot);
        var val = a / Math.sqrt(b);
        var w = [[m(radH(a, b)), function () { return a * Math.sqrt(b); }], [m(R(a, b).html()), function () { return a / b; }], [m(fr(radH(a, b), b * b)), function () { return a * Math.sqrt(b) / (b * b); }], [m(fr(K.sqrt(b), a === 1 ? b + 1 : a)), function () { return Math.sqrt(b) / (a === 1 ? b + 1 : a); }]];
        var eh = fr(n(a), K.sqrt(b));
        return attach(Q({ q: 'Rationalize the denominator: ' + m(eh), mc: mcF([m(ansH), function () { return val; }], w), why: ['Multiply the top and bottom by ' + m(K.sqrt(b)) + ': ' + m(fr((a === 1 ? '' : n(a)) + K.sqrt(b), K.sqrt(b) + ' · ' + K.sqrt(b)) + ' = ' + fr(radH(a, b), b)) + '.', g > 1 ? 'Reduce: ' + m(a + ' and ' + b) + ' share the factor ' + g + ', giving ' + m(ansH) + '.' : 'The fraction ' + m(fr(a, b)) + ' does not reduce, so the answer is ' + m(ansH) + '.', 'No radical is left in the denominator.'] }), { t: 'expr', eh: eh, chk: 'rad' });
      },
      function () { // conjugate product
        var a, b; do { a = pick(SQF); b = ri(1, 5); } while (a === b * b);
        var sA = K.coin() ? 1 : -1, val = a - b * b;
        var eh = '(' + radSum(sA * b, 1, a) + ')(' + radSum(-sA * b, 1, a) + ')';
        var w = [[m(n(a + b * b)), function () { return a + b * b; }], [m(n(a - b)), function () { return a - b; }], [m(radSumC(val, -2 * b, a)), rsF(val, -2 * b, a)], [m(n(a * a - b * b)), function () { return a * a - b * b; }]];
        return attach(Q({ q: 'Multiply: ' + m(eh), mc: mcF([m(n(val)), function () { return val; }], w, function () { var z = val + rnz(-5, 5); return [m(n(z)), function () { return z; }]; }), why: ['These are conjugates: ' + m('(<i>p</i> + <i>q</i>)(<i>p</i> ' + M + ' <i>q</i>) = <i>p</i><sup>2</sup> ' + M + ' <i>q</i><sup>2</sup>') + '.', m('(' + K.sqrt(a) + ')<sup>2</sup> ' + M + ' ' + b + '<sup>2</sup> = ' + a + ' ' + M + ' ' + b * b + ' = ' + n(val)) + '.', 'The middle terms ' + m(radH(b, a)) + ' and ' + m(radH(-b, a)) + ' cancel, so no radical is left.'] }), { t: 'expr', eh: eh });
      }
    ],
    [ // Level 3
      function () { // rationalize with a conjugate
        var a, b, c, sg2 = K.coin() ? -1 : 1, D;
        do { a = pick([2, 3, 5, 6, 7, 10, 11, 13]); b = ri(1, 4); c = ri(1, 12); D = a - b * b; } while (D === 0 || Math.abs(D) > 12);
        // c/(√a + sg2·b) = c(√a − sg2·b)/D
        var g = gcd(c, Math.abs(D)), k = c / g, den = D / g; if (den < 0) { k = -k; den = -den; }
        var numH = radSum(-sg2 * k * b, k, a);
        var ansH = den === 1 ? numH : fr(numH, den);
        var val = c / (Math.sqrt(a) + sg2 * b);
        var mkF = function (cst, co, de) { var h = radSum(cst, co, a); return [m(de === 1 ? h : fr(h, de)), function () { return (cst + co * Math.sqrt(a)) / de; }]; };
        var Dp = a + b * b, g2 = gcd(c, Dp);
        var w = [mkF(sg2 * k * b, k, den), mkF(-sg2 * (c / g2) * b, c / g2, Dp / g2), mkF(0, c, a), mkF(-sg2 * b, 1, den === 1 ? 2 : den)];
        var eh = fr(n(c), radSum(sg2 * b, 1, a));
        var numC = c === 1 ? radSum(-sg2 * b, 1, a) : n(c) + '(' + radSum(-sg2 * b, 1, a) + ')';
        return attach(Q({ q: 'Rationalize the denominator and simplify: ' + m(eh), mc: mcF([m(ansH), function () { return val; }], w, function () { return mkF(-sg2 * k * b + rnz(1, 3), k, den); }), why: ['Multiply the top and bottom by the conjugate ' + m(radSum(-sg2 * b, 1, a)) + '.', 'Denominator: ' + m('(' + K.sqrt(a) + ')<sup>2</sup> ' + M + ' ' + b + '<sup>2</sup> = ' + a + ' ' + M + ' ' + b * b + ' = ' + n(D)) + '. Numerator: ' + m(numC) + '.', (K.strip(fr(numC, n(D))) === K.strip(ansH) ? 'Result: ' + m(ansH) + '. It does not simplify further.' : 'Simplify: ' + m(fr(numC, n(D)) + ' = ' + ansH) + '.')] }), { t: 'expr', eh: eh, chk: 'rad' });
      },
      function () { // diagonal of a rectangle
        var a, b, S, sf, tries = 0;
        do { a = ri(3, 20); b = ri(3, 20); S = a * a + b * b; sf = sqf(S); } while ((a >= b || sf[0] === 1 || sf[1] === 1) && tries++ < 500);
        var thing = pick(b <= 12 ? ['room', 'deck', 'patio', 'rug', 'garden bed'] : ['room', 'deck', 'patio', 'garden bed']);
        var mk = function (cc, r) { return [m(radH(cc, r) + ' ft'), function () { return cc * Math.sqrt(r); }]; };
        var c = mk(sf[0], sf[1]);
        var sab = sqf(a + b);
        var w = [[m(n(a + b) + ' ft'), function () { return a + b; }], [m(n(S) + ' ft'), function () { return S; }], mk(sab[0], sab[1]), mk(sf[0] * sf[0], sf[1])];
        return attach(Q({ q: 'A rectangular ' + thing + ' measures ' + a + ' feet by ' + b + ' feet. What is the exact length of its diagonal, in simplest radical form?', mc: mcF(c, w), why: ['By the Pythagorean theorem, the diagonal is ' + m(K.sqrt(a + '<sup>2</sup> + ' + b + '<sup>2</sup>') + ' = ' + K.sqrt(a * a + ' + ' + b * b) + ' = ' + K.sqrt(S)) + '.', 'Largest perfect-square factor: ' + m(S + ' = ' + sf[0] * sf[0] + ' · ' + sf[1]) + '.', m(K.sqrt(S) + ' = ' + radH(sf[0], sf[1])) + ' ≈ ' + n(Math.sqrt(S), 1) + ' feet.'] }), { t: 'diag', a: a, b: b });
      },
      function () { // (p√a + q)(r√a + s)
        var a = pick([2, 3, 5, 6, 7]), p, q, r, s, C, D;
        do { p = rnz(-3, 3); q = rnz(-6, 6); r = rnz(-3, 3); s = rnz(-6, 6); C = p * r * a + q * s; D = p * s + q * r; } while (D === 0 || C === 0 || p < 0);
        var rf = function (co, cst) { return P([[co, rootH(a, 2)], [cst, '']]); };   // radical term first in both factors, so the FOIL labels match the display
        var eh = '(' + rf(p, q) + ')(' + rf(r, s) + ')';
        var mk = function (cst, co) { return [m(radSumC(cst, co, a)), rsF(cst, co, a)]; };
        var c = mk(C, D);
        var w = [mk(p * r + q * s, D), [m(n(C)), function () { return C; }], mk(C, p * s - q * r), mk(-p * r * a + q * s, D)];
        return attach(Q({ q: 'Multiply and simplify: ' + m(eh), mc: mcF(c, w, function () { return mk(C + rnz(1, 4), D); }), why: ['Use FOIL. First: ' + m(radH(p, a) + ' · ' + (r < 0 ? '(' + radH(r, a) + ')' : radH(r, a)) + ' = ' + pn(p * r) + ' · ' + a + ' = ' + n(p * r * a)) + ' (because ' + m(K.sqrt(a) + ' · ' + K.sqrt(a) + ' = ' + a) + ').', 'Outer + Inner: ' + m(radH(p * s, a)) + ' and ' + m(radH(q * r, a)) + ' combine to ' + m(radH(D, a)) + '. Last: ' + m(pn(q) + ' · ' + pn(s) + ' = ' + n(q * s)) + '.', 'Combine the whole numbers: ' + m(n(p * r * a) + sg(q * s) + ' = ' + n(C)) + '. Answer: ' + c[0] + '.'] }), { t: 'expr', eh: eh, chk: 'rad' });
      }
    ]
  ];
  K.lesson('R.7', { title: 'Radical Expressions', std: 'Lial 12e · Section R.7', levels: r7 });

  K.review('R', 'Chapter R Review: Review of Basic Concepts');
})(typeof window !== 'undefined' ? window.KCEP : globalThis.KCEP);
