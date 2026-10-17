/* KCE College Algebra — Chapter 5: Systems & Matrices
   Practice generators for Lial, Essentials of College Algebra 12e, Sections 5.1–5.8, plus the chapter review.
   Every question also carries o.p (problem data) and o.raw (the raw value behind each choice) for verify-c5.py. */
(function (K) {
  var ri = K.ri, rnz = K.rnz, pick = K.pick, n = K.n, P = K.poly, X = K.x, Y = K.y, Z = '<i>z</i>', Q = K.Q, M = K.MINUS, m = K.m, R = K.R, C = K.COL, SYM = K.ineqSym;
  var SL = [R(1), R(2), R(3), R(-1), R(-2), R(-3), R(1, 2), R(-1, 2), R(1, 3), R(-1, 3), R(2, 3), R(-2, 3), R(3, 2), R(-3, 2)];

  /* ================= shared helpers ================= */
  function iv(s) { return '<i>' + s + '</i>'; }
  function rh(v) { return R(v).html(); }
  function sub(v) { v = R(v); return v.n < 0 ? '(' + v.html() + ')' : v.html(); }
  function ctr(h) { return '<div class="center">' + h + '</div>'; }
  function sys(arr) { return '<div class="center"><div class="callout" style="display:inline-block;text-align:left;margin:6px 0 0">' + arr.join('<br>') + '</div></div>'; }
  function e2(a, b, c) { return m(P([[a, X], [b, Y]]) + ' = ' + rh(c)); }
  function e3(a, b, c, d) { return m(P([[a, X], [b, Y], [c, Z]]) + ' = ' + rh(d)); }
  function eqR(r) { return r.length === 3 ? e2(r[0], r[1], r[2]) : e3(r[0], r[1], r[2], r[3]); }
  function yEq(mm, b) { return m(K.lineEq(mm, b)); }
  function lab(name, h) { return '<span style="display:inline-block;margin:4px 10px;white-space:nowrap">' + m(name + ' = ') + h + '</span>'; }
  function Rs(i) { return 'R<sub>' + i + '</sub>'; }
  function rowOp(t, k, s) { k = R(k); var a = k.abs(); return m(Rs(t) + (k.n < 0 ? ' ' + M + ' ' : ' + ') + (a.n === 1 && a.d === 1 ? '' : a.html()) + Rs(s)); }
  function cp(c) { return c === 1 ? ' + ' : c === -1 ? ' ' + M + ' ' : (c < 0 ? ' ' + M + ' ' + (-c) : ' + ' + c); }
  function lead(c) { return c === 1 ? '' : c === -1 ? M : n(c); }
  function dsum(r, c) { var s = R(0); r.forEach(function (v, i) { s = s.add(R(v).mul(c[i])); }); return s; }
  function dot(r, c) { return m(r.map(function (v, i) { return sub(v) + '(' + rh(c[i]) + ')'; }).join(' + ') + ' = ' + rh(dsum(r, c))); }
  function d2txt(A) { return m(sub(A[0][0]) + '(' + rh(A[1][1]) + ') ' + M + ' ' + sub(A[0][1]) + '(' + rh(A[1][0]) + ')'); }
  function sy(v) { v = R(v); return '(' + v.n + (v.d !== 1 ? '/' + v.d : '') + ')'; }
  function pl(k, one, many) { return k + ' ' + (k === 1 ? one : many); }
  // unreduced quotient num/den with the sign in front, never in the denominator (−18/6, not 18/−6)
  function sfr(nu, de) { nu = R(nu); de = R(de); if (de.n < 0) { nu = nu.neg(); de = de.neg(); } return (nu.n < 0 ? M : '') + K.frx(nu.abs().html(), de.html()); }
  // "v = num/den = value", skipping the middle step when it would repeat the value
  function qeq(lhs, nu, de) { var v = R(nu).div(de), f = sfr(nu, de); return m(lhs + ' = ' + (K.strip(f) === K.strip(v.html()) ? '' : f + ' = ') + v.html()); }

  // multiple choice with raw values recorded for the verifier
  function mcR(c, w, fmt, extra) {
    var map = {};
    function add(r) { var h = fmt(r), k = K.strip(h); if (!(k in map)) map[k] = r; return h; }
    var res = K.mc(add(c), w.filter(function (v) { return v !== null && v !== undefined; }).map(add), extra ? function (i) { return add(extra(i)); } : null);
    res.raw = res.ch.map(function (h) { return map[K.strip(h)]; });
    return res;
  }
  function QQ(o, p) { var q = Q(o); q.p = p; q.raw = o.mc.raw; return q; }

  // formatters
  function fPt(r) { return K.pt(r[0], r[1]); }
  function fTri(r) { return '(' + rh(r[0]) + ', ' + rh(r[1]) + ', ' + rh(r[2]) + ')'; }
  function fNum(r) { return rh(r); }
  function fMat(A) { return K.mat(A); }
  function fDet(A) { return K.mat(A, null, true); }
  function pEx(x, y) { return function () { return [R(x).add(rnz(-3, 3)), R(y).add(rnz(-3, 3))]; }; }
  function tEx(t) { return function () { var u = t.slice(), i = ri(0, 2); u[i] = R(u[i]).add(rnz(-3, 3)); return u; }; }
  function nEx(v, s) { s = s || 4; return function () { return R(v).add(rnz(-s, s)); }; }
  function pairW(x, y) { return [[y, x], [R(x).neg(), y], [x, R(y).neg()], [R(y).neg(), R(x).neg()]]; }
  function triW(t) { return [[t[1], t[0], t[2]], [t[0], t[2], t[1]], [t[2], t[1], t[0]], [R(t[0]).neg(), t[1], t[2]]]; }

  // exact matrix helpers (entries numbers or R)
  function minor(A, i, j) { return A.filter(function (_, a) { return a !== i; }).map(function (r) { return r.filter(function (_, b) { return b !== j; }); }); }
  function det(A) { if (A.length === 1) return R(A[0][0]); var s = R(0); for (var j = 0; j < A.length; j++) { var t = R(A[0][j]).mul(det(minor(A, 0, j))); s = j % 2 ? s.sub(t) : s.add(t); } return s; }
  function dv(A) { return det(A).val(); }
  function num(v) { v = R(v); return v.d === 1 ? v.n : v; }
  function mmap(A, f) { return A.map(function (r, i) { return r.map(function (v, j) { return f(v, i, j); }); }); }
  function tr(A) { return A[0].map(function (_, j) { return A.map(function (r) { return r[j]; }); }); }
  function mmul(A, B) { return A.map(function (r) { return B[0].map(function (_, j) { var s = R(0); r.forEach(function (v, k) { s = s.add(R(v).mul(B[k][j])); }); return num(s); }); }); }
  function inv(A) {
    var d = det(A);
    var Cf = mmap(A, function (_, i, j) { var mi = A.length === 2 ? R(A[1 - i][1 - j]) : det(minor(A, i, j)); return (i + j) % 2 ? mi.neg() : mi; });
    return tr(Cf).map(function (r) { return r.map(function (v) { return num(v.div(d)); }); });
  }
  function rSys2(x, y, lo, hi, cond) { var a1, b1, a2, b2; do { a1 = rnz(lo, hi); b1 = rnz(lo, hi); a2 = rnz(lo, hi); b2 = rnz(lo, hi); } while (a1 * b2 - a2 * b1 === 0 || (cond && !cond(a1, b1, a2, b2))); return [[a1, b1, a1 * x + b1 * y], [a2, b2, a2 * x + b2 * y]]; }
  function rSys3(s, one) {
    var A;
    do { A = [[one ? 1 : rnz(-3, 3), ri(-3, 3), ri(-3, 3)], [rnz(-3, 3), ri(-3, 3), ri(-3, 3)], [ri(-3, 3), ri(-3, 3), ri(-3, 3)]]; }
    while (dv(A) === 0 || A.some(function (r) { return r.filter(function (v) { return v !== 0; }).length < 2; }));
    return A.map(function (r) { return [r[0], r[1], r[2], r[0] * s[0] + r[1] * s[1] + r[2] * s[2]]; });
  }
  function coefM(S) { return S.map(function (r) { return r.slice(0, r.length - 1); }); }
  function constC(S) { return S.map(function (r) { return r[r.length - 1]; }); }
  // eliminate x from equations 2 and 3 using equation 1 (whose x-coefficient is 1)
  function elimX(S) {
    var out = [], rows = [];
    [1, 2].forEach(function (i) {
      var k = S[i][0], r = [S[i][1] - k * S[0][1], S[i][2] - k * S[0][2], S[i][3] - k * S[0][3]]; rows.push(r);
      var how = k === 0 ? 'equation ' + (i + 1) + ' already has no ' + X + '-term: ' : (k > 0 ? 'equation ' + (i + 1) + ' minus ' + (k === 1 ? '' : n(k) + ' times ') : 'equation ' + (i + 1) + ' plus ' + (k === -1 ? '' : n(-k) + ' times ')) + 'equation 1 gives ';
      out.push(how + m(P([[r[0], Y], [r[1], Z]]) + ' = ' + n(r[2])));
    });
    return { txt: out.join('; '), rows: rows };
  }

  /* ================= 5.1 Systems of Linear Equations ================= */
  var CAT = { one: 'Exactly one solution', none: 'No solution', inf: 'Infinitely many solutions', two: 'Exactly two solutions' };
  function lineThrough(x, y) {
    for (var t = 0; t < 80; t++) { var mm = pick(SL), b = mm.mul(-x).add(y); if (b.isInt() && Math.abs(b.val()) <= 6) return [mm, b]; }
    return [R(1), R(y - x)];
  }
  function fSetLin(r) {
    if (r[0] === 'none') return '∅ (no solution)';
    if (r[0] === 'pt') return '{' + K.pt(r[1], r[2]) + '}';
    if (r[0] === 'infx') return '{(' + X + ', ' + P([[r[1], X], [r[2], '']]) + ')}';
    return '{(' + P([[r[1], Y], [r[2], '']]) + ', ' + Y + ')}';
  }

  // L1: substitution
  function g511a() {
    var x, y, mm, b, a, c;
    do { x = ri(-5, 5); mm = rnz(-4, 4); b = ri(-6, 6); y = mm * x + b; a = rnz(-5, 5); c = rnz(-4, 4); } while (Math.abs(y) > 12 || a + c * mm === 0);
    var d = a * x + c * y, k = a + c * mm;
    var S = [[-mm, 1, b], [a, c, d]];
    return QQ({ q: 'Solve the system by substitution. Write the solution as an ordered pair.' + sys([yEq(mm, b), e2(a, c, d)]),
      mc: mcR([x, y], pairW(x, y), fPt, pEx(x, y)),
      why: ['The first equation gives ' + Y + '. Substitute it into the second: ' + m(P([[a, X]]) + cp(c) + (b === 0 && mm > 0 && Math.abs(c) === 1 ? P([[mm, X]]) : '(' + P([[mm, X], [b, '']]) + ')') + ' = ' + n(d)) + '.',
        'Simplify: ' + m(P([[k, X], [c * b, '']]) + ' = ' + n(d)) + (c * b === 0 ? '' : ', so ' + m(P([[k, X]]) + ' = ' + n(d - c * b))) + (k === 1 ? '.' : ' and ' + m('<i>x</i> = ' + n(x)) + '.'),
        'Then ' + m('<i>y</i> = ' + (mm === 1 && b === 0 ? '' : (mm === 1 ? n(x) : K.lin([[mm, n(x)]])) + K.plusK(b) + ' = ') + n(y)) + '. The solution is ' + K.pt(x, y) + '.'] }, { t: 'sol', eqs: S });
  }
  // L1: elimination with opposite coefficients
  function g511b() {
    var x = ri(-6, 6), y = ri(-6, 6), onY = K.coin(), a1, b1, a2, b2;
    if (onY) { b1 = ri(1, 5); b2 = -b1; do { a1 = rnz(-5, 5); a2 = rnz(-5, 5); } while (a1 + a2 === 0); }
    else { a1 = ri(1, 5); a2 = -a1; do { b1 = rnz(-5, 5); b2 = rnz(-5, 5); } while (b1 + b2 === 0); }
    var c1 = a1 * x + b1 * y, c2 = a2 * x + b2 * y;
    var why = onY ?
      ['The ' + Y + '-terms ' + m(P([[b1, Y]])) + ' and ' + m(P([[b2, Y]])) + ' are opposites, so add the equations: ' + m(P([[a1 + a2, X]]) + ' = ' + n(c1 + c2)) + '.',
        'Divide: ' + m('<i>x</i> = ' + n(x)) + '.',
        'Substitute into the first equation: ' + m(K.lin([[a1, n(x)]]) + K.coef(b1, false) + '<i>y</i> = ' + n(c1)) + ', so ' + m('<i>y</i> = ' + n(y)) + '. The solution is ' + K.pt(x, y) + '.'] :
      ['The ' + X + '-terms ' + m(P([[a1, X]])) + ' and ' + m(P([[a2, X]])) + ' are opposites, so add the equations: ' + m(P([[b1 + b2, Y]]) + ' = ' + n(c1 + c2)) + '.',
        'Divide: ' + m('<i>y</i> = ' + n(y)) + '.',
        'Substitute into the first equation: ' + m(P([[a1, X]]) + K.lin([[b1, n(y)]], true) + ' = ' + n(c1)) + ', so ' + m('<i>x</i> = ' + n(x)) + '. The solution is ' + K.pt(x, y) + '.'];
    return QQ({ q: 'Solve the system by elimination. Write the solution as an ordered pair.' + sys([e2(a1, b1, c1), e2(a2, b2, c2)]), mc: mcR([x, y], pairW(x, y), fPt, pEx(x, y)), why: why }, { t: 'sol', eqs: [[a1, b1, c1], [a2, b2, c2]] });
  }
  // L1: classify (one / none / infinitely many)
  function g511c() {
    var a, b; do { a = rnz(-5, 5); b = rnz(-5, 5); } while (K.gcd(a, b) !== 1);
    var c = rnz(-9, 9), kind = pick(['one', 'none', 'inf']), k = pick([2, 3, -2, -3, 4, -1]), r2, why;
    if (kind === 'inf') {
      r2 = [k * a, k * b, k * c];
      why = ['Multiply the first equation by ' + n(k) + ': ' + e2(k * a, k * b, k * c) + '.', 'That is exactly the second equation, so both equations describe the same line.', 'Every point on that line is a solution: infinitely many solutions (a dependent system).'];
    } else if (kind === 'none') {
      var dd = rnz(-6, 6); r2 = [k * a, k * b, k * c + dd];
      why = ['Multiply the first equation by ' + n(k) + ': ' + e2(k * a, k * b, k * c) + '.', 'The second equation has the same left side but equals ' + n(r2[2]) + '. Subtracting gives ' + m('0 = ' + n(dd)) + ', which is false.', 'The lines are parallel, so there is no solution (an inconsistent system).'];
    } else {
      var a2, b2; do { a2 = rnz(-6, 6); b2 = rnz(-6, 6); } while (a * b2 - a2 * b === 0); r2 = [a2, b2, ri(-12, 12)];
      why = ['Solve each equation for ' + Y + ' to compare slopes: the slopes are ' + m(rh(R(-a, b))) + ' and ' + m(rh(R(-a2, b2))) + '.', 'Different slopes mean the lines cross at exactly one point.', 'So the system has exactly one solution (consistent and independent).'];
    }
    return QQ({ q: 'How many solutions does the system have?' + sys([e2(a, b, c), e2(r2[0], r2[1], r2[2])]), mc: mcR(kind, ['one', 'none', 'inf', 'two'].filter(function (s) { return s !== kind; }), function (s) { return CAT[s]; }), why: why }, { t: 'count', eqs: [[a, b, c], r2] });
  }
  // L1: read the solution from a graph
  function g511d() {
    var x = ri(-4, 4), y = ri(-4, 4), L1 = lineThrough(x, y), L2, g = 0;
    do { L2 = lineThrough(x, y); } while (L2[0].eq(L1[0]) && g++ < 60);
    if (L2[0].eq(L1[0])) return g511d();
    var gr = K.plane({ x: [-7, 7], y: [-7, 7], lines: [{ m: L1[0], b: L1[1], color: C.blue }, { m: L2[0], b: L2[1], color: C.red }] });
    return QQ({ q: 'The graph shows the two lines of a linear system. What is the solution of the system? Write it as an ordered pair.', graph: gr,
      mc: mcR([x, y], pairW(x, y), fPt, pEx(x, y)),
      why: ['The solution of a system is the point on both lines: where the lines intersect.', 'The lines cross at ' + K.pt(x, y) + '.',
        'Check: the blue line is ' + yEq(L1[0], L1[1]) + ' and the red line is ' + yEq(L2[0], L2[1]) + '. At ' + m('<i>x</i> = ' + n(x)) + ', both give ' + m('<i>y</i> = ' + n(y)) + '.'] },
      { t: 'sol', eqs: [[L1[0].neg(), 1, L1[1]], [L2[0].neg(), 1, L2[1]]] });
  }
  // L2: elimination, multiplying both equations
  function g512a() {
    var x = ri(-5, 5), y = ri(-5, 5);
    var s = rSys2(x, y, -6, 6, function (a1, b1, a2, b2) { return Math.abs(a1) !== Math.abs(a2) && Math.abs(b1) !== Math.abs(b2) && Math.abs(a1) > 1 && Math.abs(a2) > 1 && K.gcd(a1, a2) < Math.min(Math.abs(a1), Math.abs(a2)); });
    var a1 = s[0][0], a2 = s[1][0], L = K.lcm(Math.abs(a1), Math.abs(a2)), k1 = L / a1, k2 = -L / a2;
    var yc = s[0][1] * k1 + s[1][1] * k2, cc = s[0][2] * k1 + s[1][2] * k2;
    return QQ({ q: 'Solve the system. Write the solution as an ordered pair.' + sys([eqR(s[0]), eqR(s[1])]), mc: mcR([x, y], pairW(x, y), fPt, pEx(x, y)),
      why: ['To eliminate ' + X + ', multiply the first equation by ' + n(k1) + ' and the second by ' + n(k2) + ': ' + e2(a1 * k1, s[0][1] * k1, s[0][2] * k1) + ' and ' + e2(a2 * k2, s[1][1] * k2, s[1][2] * k2) + '.',
        'Add the new equations: ' + m(P([[yc, Y]]) + ' = ' + n(cc)) + ', so ' + m('<i>y</i> = ' + n(y)) + '.',
        'Substitute into the first equation: ' + m(P([[a1, X]]) + K.lin([[s[0][1], n(y)]], true) + ' = ' + n(s[0][2])) + ', so ' + m('<i>x</i> = ' + n(x)) + '. The solution is ' + K.pt(x, y) + '.'] }, { t: 'sol', eqs: s });
  }
  // L2: dependent or inconsistent system, solution set
  function g512b() {
    var mm = rnz(-4, 4), b = rnz(-6, 6), s = pick([1, -1, 2, -2, 3]), k = pick([2, 3, -2, -3, -1]);
    var r1 = [-mm * s, s, b * s], dep = ri(1, 10) <= 7, del = dep ? 0 : rnz(-5, 5), r2 = [r1[0] * k, r1[1] * k, r1[2] * k + del];
    var cor = dep ? ['infx', mm, b] : ['none'];
    var wr = [dep ? ['none'] : ['infx', mm, b], ['infx', -mm, b], ['infx', mm, -b], ['pt', 0, b]];
    var why = dep ?
      ['Multiply the first equation by ' + n(k) + ': ' + e2(r1[0] * k, r1[1] * k, r1[2] * k) + ', which is the second equation.', 'Both equations describe the same line, so every point on it is a solution.', 'Solve the first equation for ' + Y + ': ' + yEq(mm, b) + '. The solution set is ' + fSetLin(cor) + '.'] :
      ['Multiply the first equation by ' + n(k) + ': ' + e2(r1[0] * k, r1[1] * k, r1[2] * k) + '.', 'The second equation has the same left side but equals ' + n(r2[2]) + ', so subtracting gives ' + m('0 = ' + n(del)) + ', which is false.', 'The system is inconsistent, so its solution set is ∅.'];
    return QQ({ q: 'Solve the system. Which describes its solution set? (If there are infinitely many solutions, they are written in terms of ' + X + '.)' + sys([eqR(r1), eqR(r2)]),
      mc: mcR(cor, wr, fSetLin, function () { return ['infx', mm + rnz(-2, 2), b + rnz(-2, 2)]; }), why: why }, { t: 'linset', eqs: [r1, r2] });
  }
  // L2: three equations in three variables
  function g512c() {
    var t = [ri(-4, 4), ri(-4, 4), ri(-4, 4)], S = rSys3(t, true), E = elimX(S);
    return QQ({ q: 'Solve the system. Write the solution as an ordered triple.' + sys(S.map(eqR)), mc: mcR(t, triW(t), fTri, tEx(t)),
      why: ['Eliminate ' + X + ' using equation 1: ' + E.txt + '.',
        'Solve that two-variable system: ' + m('<i>y</i> = ' + n(t[1])) + ' and ' + m('<i>z</i> = ' + n(t[2])) + '.',
        'Back-substitute into equation 1: ' + m('<i>x</i>' + K.lin([[S[0][1], n(t[1])], [S[0][2], n(t[2])]], true) + ' = ' + n(S[0][3])) + ', so ' + m('<i>x</i> = ' + n(t[0])) + '.',
        'The solution is ' + fTri(t) + '.'] }, { t: 'sol', eqs: S });
  }
  // L3: ticket word problem
  var TIX = [['A school play', 'adult', 'student', 'tickets', 'ticket'], ['A museum', 'adult', 'child', 'passes', 'pass'], ['A concert', 'floor', 'balcony', 'tickets', 'ticket'], ['A bakery', 'large', 'small', 'cakes', 'cake']];
  function g513a() {
    var c = pick(TIX), p1 = ri(8, 20), p2 = ri(3, p1 - 2), a = ri(8, 40), s = ri(8, 40), tot = a + s, money = p1 * a + p2 * s;
    var fmt = function (r) { return rh(r[0]) + ' ' + c[1] + ' and ' + rh(r[1]) + ' ' + c[2] + ' ' + c[3]; };
    var A = iv('a'), B = iv('b');
    return QQ({ q: c[0] + ' sold ' + tot + ' ' + c[3] + ' for a total of $' + money + '. ' + c[1].charAt(0).toUpperCase() + c[1].slice(1) + ' ' + c[3] + ' cost $' + p1 + ' each and ' + c[2] + ' ' + c[3] + ' cost $' + p2 + ' each. How many of each type were sold?',
      mc: mcR([a, s], [[s, a], [a + 1, s - 1], [a - 1, s + 1]], fmt, function () { var d = rnz(-5, 5); return [a + d, s - d]; }),
      why: ['Let ' + A + ' = number of ' + c[1] + ' ' + c[3] + ' and ' + B + ' = number of ' + c[2] + ' ' + c[3] + ': ' + m(A + ' + ' + B + ' = ' + tot) + ' and ' + m(p1 + A + ' + ' + p2 + B + ' = ' + money) + '.',
        'Substitute ' + m(B + ' = ' + tot + ' ' + M + ' ' + A) + ': ' + m(p1 + A + ' + ' + p2 + '(' + tot + ' ' + M + ' ' + A + ') = ' + money) + ', so ' + m((p1 - p2) + A + ' = ' + (money - p2 * tot)) + ' and ' + m(A + ' = ' + a) + '.',
        'Then ' + m(B + ' = ' + tot + ' ' + M + ' ' + a + ' = ' + s) + '. Check: ' + m(p1 + '(' + a + ') + ' + p2 + '(' + s + ') = ' + money) + '.'] }, { t: 'sol', eqs: [[1, 1, tot], [p1, p2, money]] });
  }
  // L3: three-type ticket problem
  var TIX3 = [['A theater', 'orchestra', 'mezzanine', 'balcony', 'tickets'], ['A zoo', 'family', 'adult', 'child', 'passes'], ['A coffee shop', 'large', 'medium', 'small', 'drinks']];
  function g513b() {
    var c = pick(TIX3), p1, p2, p3, k, a, b, cc, T, Mo, A3;
    do { p3 = ri(3, 8); p2 = p3 + ri(2, 5); p1 = p2 + ri(2, 6); k = pick([2, 3]); cc = ri(5, 20); a = k * cc; b = ri(10, 40); T = a + b + cc; Mo = p1 * a + p2 * b + p3 * cc; A3 = [[1, 1, 1], [p1, p2, p3], [1, 0, -k]]; } while (dv(A3) === 0);
    var fmt = function (r) { return rh(r[0]) + ' ' + c[1] + ', ' + rh(r[1]) + ' ' + c[2] + ', ' + rh(r[2]) + ' ' + c[3]; };
    var a_ = iv('a'), b_ = iv('b'), c_ = iv('c'), co = k * p1 + p3 - p2 * (k + 1);
    return QQ({ q: c[0] + ' sold ' + T + ' ' + c[4] + ' for $' + Mo + '. ' + c[1].charAt(0).toUpperCase() + c[1].slice(1) + ' ' + c[4] + ' cost $' + p1 + ', ' + c[2] + ' ' + c[4] + ' cost $' + p2 + ', and ' + c[3] + ' ' + c[4] + ' cost $' + p3 + '. It sold ' + (k === 2 ? 'twice' : 'three times') + ' as many ' + c[1] + ' ' + c[4] + ' as ' + c[3] + ' ' + c[4] + '. How many of each type did it sell?',
      mc: mcR([a, b, cc], [[cc, b, a], [b, a, cc], [a, cc, b]], fmt, function () { var c2 = cc + rnz(-3, 3), a2 = k * c2; return [a2, T - a2 - c2, c2]; }),
      why: ['Let ' + a_ + ', ' + b_ + ', and ' + c_ + ' be the numbers of ' + c[1] + ', ' + c[2] + ', and ' + c[3] + ' ' + c[4] + ': ' + m(a_ + ' + ' + b_ + ' + ' + c_ + ' = ' + T) + ', ' + m(p1 + a_ + ' + ' + p2 + b_ + ' + ' + p3 + c_ + ' = ' + Mo) + ', and ' + m(a_ + ' = ' + k + c_) + '.',
        'Substitute ' + m(a_ + ' = ' + k + c_) + ': ' + m(b_ + ' + ' + (k + 1) + c_ + ' = ' + T) + ' and ' + m(p2 + b_ + ' + ' + (k * p1 + p3) + c_ + ' = ' + Mo) + '.',
        'Substitute ' + m(b_ + ' = ' + T + ' ' + M + ' ' + (k + 1) + c_) + ': ' + m(P([[co, c_]]) + ' = ' + n(Mo - p2 * T)) + ', so ' + m(c_ + ' = ' + cc) + '.',
        'Then ' + m(a_ + ' = ' + k + '(' + cc + ') = ' + a) + ' and ' + m(b_ + ' = ' + T + ' ' + M + ' ' + (k + 1) * cc + ' = ' + b) + '.'] },
      { t: 'sol', eqs: [[1, 1, 1, T], [p1, p2, p3, Mo], [1, 0, -k, 0]] });
  }
  // L3: parabola through three points
  function g513c() {
    var a, b, c, xs, f;
    do { a = rnz(-3, 3); b = ri(-5, 5); c = ri(-6, 6); xs = K.sample([-3, -2, -1, 0, 1, 2, 3], 3).sort(function (u, v) { return u - v; }); f = function (t) { return a * t * t + b * t + c; }; } while (xs.some(function (t) { return Math.abs(f(t)) > 30; }));
    var ys = xs.map(f), A = iv('a'), B = iv('b'), Cc = iv('c');
    var fq = function (r) { return m('<i>y</i> = ' + P([[r[0], K.xp(2)], [r[1], X], [r[2], '']])); };
    var eq = function (t, v) { return m(P([[t * t, A], [t, B], [1, Cc]]) + ' = ' + n(v)); };
    var df = function (i, j) { return m(P([[xs[j] * xs[j] - xs[i] * xs[i], A], [xs[j] - xs[i], B]]) + ' = ' + n(ys[j] - ys[i])); };
    return QQ({ q: 'A parabola ' + m('<i>y</i> = <i>ax</i><sup>2</sup> + <i>bx</i> + <i>c</i>') + ' passes through ' + K.pt(xs[0], ys[0]) + ', ' + K.pt(xs[1], ys[1]) + ', and ' + K.pt(xs[2], ys[2]) + '. Substitute each point into ' + m('<i>y</i> = <i>ax</i><sup>2</sup> + <i>bx</i> + <i>c</i>') + ' to get a system of three equations in ' + A + ', ' + B + ', and ' + Cc + ', then solve the system. What is the equation of the parabola?',
      mc: mcR([a, b, c], [[a, -b, c], [-a, b, c], [a, b, -c], [b, a, c]].filter(function (r) { return r[0] !== 0; }), fq, function () { return [a, b + rnz(-2, 2), c + rnz(-2, 2)]; }),
      why: ['Substitute each point into ' + m('<i>y</i> = <i>ax</i><sup>2</sup> + <i>bx</i> + <i>c</i>') + ': ' + eq(xs[0], ys[0]) + ', ' + eq(xs[1], ys[1]) + ', and ' + eq(xs[2], ys[2]) + '.',
        'Subtract to eliminate ' + Cc + ': ' + df(0, 1) + ' and ' + df(1, 2) + '.',
        'Solve these two equations: ' + m(A + ' = ' + n(a)) + ' and ' + m(B + ' = ' + n(b)) + '. Then the first equation gives ' + m(Cc + ' = ' + n(c)) + '.',
        'The parabola is ' + fq([a, b, c]) + '.'] }, { t: 'parab', pts: xs.map(function (t, i) { return [t, ys[i]]; }) });
  }
  K.lesson('5.1', { title: 'Systems of Linear Equations', std: 'Lial 12e · Section 5.1', levels: [[g511a, g511b, g511c, g511d], [g512a, g512b, g512c], [g513a, g513b, g513c]] });

  /* ================= 5.2 Matrix Solution of Linear Systems ================= */
  var CAT3 = { one: 'Exactly one solution', none: 'No solution', inf: 'Infinitely many solutions', zero: 'Only the solution (0, 0, 0)' };
  // L1: write the augmented matrix
  function g521a() {
    var nv = K.coin() ? 3 : 2, rows = [], i, j;
    for (i = 0; i < nv; i++) { var r; do { r = []; for (j = 0; j < nv; j++) r.push(ri(-6, 6)); } while (r.filter(function (v) { return v !== 0; }).length < 2); r.push(rnz(-12, 12)); rows.push(r); }
    var zr = -1;
    if (nv === 3) { zr = ri(0, 2); var zc = ri(1, 2); rows[zr][zc] = 0; if (rows[zr].slice(0, 3).filter(function (v) { return v !== 0; }).length < 2) rows[zr][3 - zc] = rnz(-6, 6); if (rows[zr][0] === 0) rows[zr][0] = rnz(-6, 6); }
    var fmt = function (A) { return K.mat(A, nv); };
    var w1 = rows.map(function (r) { return r.map(function (v, j) { return j === nv ? -v : v; }); });
    var w2 = nv === 3 ? rows.map(function (r) { var cf = r.slice(0, 3).filter(function (v) { return v !== 0; }); while (cf.length < 3) cf.push(0); return cf.concat([r[3]]); }) : rows.map(function (r) { return [r[1], r[0], r[2]]; });
    var w3 = rows.map(function (r) { return r.map(function (v, j) { return j < nv ? Math.abs(v) : v; }); });
    var why2;
    if (zr >= 0) { var miss = rows[zr][1] === 0 ? Y : Z; why2 = 'Equation ' + (zr + 1) + ' has no ' + miss + '-term, so row ' + (zr + 1) + ' has a 0 in the ' + miss + '-column.'; }
    else why2 = 'Keep each sign: a subtracted term gives a negative entry.';
    return QQ({ q: 'Which matrix is the augmented matrix of the system?' + sys(rows.map(eqR)),
      mc: mcR(rows, [w1, w2, w3], fmt, function () { var A = rows.map(function (r) { return r.slice(); }), a = ri(0, nv - 1), b = ri(0, nv); A[a][b] += rnz(-2, 2); return A; }),
      why: ['Each equation becomes one row: the coefficients of ' + (nv === 3 ? X + ', ' + Y + ', and ' + Z : X + ' and ' + Y) + ' in order, then a bar, then the constant.', why2, 'The augmented matrix is ' + K.mat(rows, nv) + '.'] }, { t: 'aug', eqs: rows });
  }
  // L1: read the solution from a reduced matrix
  function g521b() {
    var nv = K.coin() ? 2 : 3, sol = [], i;
    do { sol = []; for (i = 0; i < nv; i++) sol.push(ri(-9, 9)); } while (sol[0] === sol[nv - 1] || sol.every(function (v) { return v === 1; }));
    var Mx = sol.map(function (v, i) { var r = []; for (var j = 0; j < nv; j++) r.push(i === j ? 1 : 0); r.push(v); return r; });
    var fmt = nv === 2 ? fPt : fTri, rev = sol.slice().reverse(), fl = sol.slice(); fl[0] = -fl[0];
    var ones = sol.map(function () { return 1; });
    var names = nv === 2 ? [X, Y] : [X, Y, Z];
    return QQ({ q: 'The augmented matrix of a system in ' + (nv === 2 ? X + ' and ' + Y : X + ', ' + Y + ', and ' + Z) + ' has been reduced by the Gauss-Jordan method. What is the solution of the system?' + ctr(K.mat(Mx, nv)),
      mc: mcR(sol, [rev, fl, ones], fmt, nv === 2 ? pEx(sol[0], sol[1]) : tEx(sol)),
      why: ['Each row is an equation: ' + sol.map(function (v, i) { return 'row ' + (i + 1) + ' says ' + m(names[i] + ' = ' + n(v)); }).join(', ') + '.', 'Write the values in order: ' + fmt(sol) + '.'] }, { t: 'msol', mat: Mx });
  }
  // L1: perform a row operation
  function g521c() {
    var nr = pick([2, 3]), nc = nr + 1, Mx = [], i, j;
    for (i = 0; i < nr; i++) { var r; do { r = []; for (j = 0; j < nc; j++) r.push(ri(-6, 6)); } while (r.filter(function (v) { return v !== 0; }).length < 2); Mx.push(r); }
    var t = ri(1, nr), s; do { s = ri(1, nr); } while (s === t); var k = rnz(-3, 3);
    var T = Mx[t - 1], S = Mx[s - 1], sc = S.map(function (v) { return k * v; });
    var row = T.map(function (v, j) { return v + k * S[j]; });
    var fmt = function (r) { return K.mat([r], nc - 1); };
    var w = [T.map(function (v, j) { return v - k * S[j]; }), T.map(function (v, j) { return k * v + S[j]; }), T.map(function (v) { return v + k; }), S.map(function (v, j) { return v + k * T[j]; })];
    return QQ({ q: 'Replace row ' + t + ' of the matrix with ' + rowOp(t, k, s) + '. What is the new row ' + t + '?' + ctr(K.mat(Mx, nc - 1)),
      mc: mcR(row, w, fmt, function () { var r = row.slice(); r[ri(0, nc - 1)] += rnz(-2, 2); return r; }),
      why: [k === 1 ? 'Row ' + s + ' is ' + K.mat([sc], nc - 1) + '; it is used as is.' : 'Multiply each entry of row ' + s + ' by ' + n(k) + ': ' + K.mat([sc], nc - 1) + '.', (k === 1 ? 'Add row ' + s : 'Add that') + ' to row ' + t + ' entry by entry: ' + K.mat([T], nc - 1) + ' + ' + K.mat([sc], nc - 1) + ' = ' + K.mat([row], nc - 1) + '.', 'Only row ' + t + ' changes; row ' + s + ' stays the same.'] },
      { t: 'rowop', mat: Mx, op: [t, k, s] });
  }
  // L1: read the number of solutions from a row-echelon matrix
  function g521d() {
    var kind = pick(['one', 'none', 'inf']), a = ri(-4, 4), b = ri(-4, 4), d = ri(-4, 4), f = 0, g = 0, c, e, why, x, y, z;
    if (kind === 'one') {
      f = pick([1, 2, -1, 3]);
      do { x = ri(-5, 5); y = ri(-5, 5); z = ri(-5, 5); } while (x === 0 && y === 0 && z === 0);
      g = f * z; e = y + d * z; c = x + a * y + b * z;
      why = ['The last row says ' + m(P([[f, Z]]) + ' = ' + n(g)) + ', so ' + m('<i>z</i> = ' + n(z)) + '.', 'Back-substitution then gives exactly one value for ' + Y + ' and for ' + X + ': the solution is ' + fTri([x, y, z]) + '.', 'So the system has exactly one solution.'];
    } else {
      c = ri(-9, 9); e = ri(-9, 9); g = kind === 'none' ? rnz(-9, 9) : 0;
      why = kind === 'none' ? ['The last row says ' + m('0<i>x</i> + 0<i>y</i> + 0<i>z</i> = ' + n(g)) + ', that is, ' + m('0 = ' + n(g)) + '.', 'That statement is false, so the system is inconsistent: no solution.'] :
        ['The last row says ' + m('0 = 0') + ', which is always true and gives no information.', 'That leaves two equations for three variables with no contradiction, so ' + Z + ' can be any number: infinitely many solutions.'];
    }
    var Mx = [[1, a, b, c], [0, 1, d, e], [0, 0, f, g]];
    return QQ({ q: 'The augmented matrix of a system in ' + X + ', ' + Y + ', and ' + Z + ' has been reduced to the form below. How many solutions does the system have?' + ctr(K.mat(Mx, 3)),
      mc: mcR(kind, ['one', 'none', 'inf', 'zero'].filter(function (s) { return s !== kind; }), function (s) { return CAT3[s]; }), why: why }, { t: 'mcount', mat: Mx });
  }
  // L2: Gauss-Jordan, two variables
  function g522a() {
    var x = ri(-6, 6), y = ri(-6, 6), b1 = rnz(-4, 4), a2 = rnz(-5, 5), b2;
    do { b2 = rnz(-5, 5); } while (b2 - a2 * b1 === 0);
    var r1 = [1, b1, x + b1 * y], r2 = [a2, b2, a2 * x + b2 * y], swap = K.coin(), shown = swap ? [r2, r1] : [r1, r2];
    var p2 = b2 - a2 * b1, c2 = r2[2] - a2 * r1[2];
    return QQ({ q: 'Use the Gauss-Jordan method to solve the system. Write the solution as an ordered pair.' + sys(shown.map(eqR)), mc: mcR([x, y], pairW(x, y), fPt, pEx(x, y)),
      why: ['Write the augmented matrix' + (swap ? ', swapping the rows so the first entry is 1' : '') + ': ' + K.mat([r1, r2], 2) + '.',
        rowOp(2, -a2, 1) + ' gives ' + K.mat([r1, [0, p2, c2]], 2) + '.' + (p2 === 1 ? '' : ' Divide row 2 by ' + n(p2) + '.') + ' Row 2 now says ' + m('<i>y</i> = ' + n(y)) + '.',
        rowOp(1, -b1, 2) + ' gives ' + K.mat([[1, 0, x], [0, 1, y]], 2) + ', so the solution is ' + K.pt(x, y) + '.'] }, { t: 'sol', eqs: shown });
  }
  // L2: Gauss-Jordan, three variables
  function g522b() {
    var t = [ri(-4, 4), ri(-4, 4), ri(-4, 4)], S = rSys3(t, true), E = elimX(S);
    var after = [S[0], [0].concat(E.rows[0]), [0].concat(E.rows[1])];
    var ops = [1, 2].filter(function (i) { return S[i][0] !== 0; }).map(function (i) { return rowOp(i + 1, -S[i][0], 1); });
    return QQ({ q: 'Use a matrix method to solve the system. Write the solution as an ordered triple.' + sys(S.map(eqR)), mc: mcR(t, triW(t), fTri, tEx(t)),
      why: ['Write the augmented matrix ' + K.mat(S, 3) + '.',
        (ops.length ? 'Clear column 1 with ' + ops.join(' and ') : 'Column 1 is already clear below the 1') + ': ' + K.mat(after, 3) + '.',
        'Finish reducing rows 2 and 3 (or back-substitute): ' + m('<i>z</i> = ' + n(t[2])) + ' and ' + m('<i>y</i> = ' + n(t[1])) + '; then row 1 gives ' + m('<i>x</i> = ' + n(t[0])) + '.',
        'The solution is ' + fTri(t) + '.'] }, { t: 'sol', eqs: S });
  }
  // L2: back-substitution from row-echelon form
  function g522c() {
    var x = ri(-5, 5), y = ri(-5, 5), z = ri(-5, 5), a = rnz(-3, 3), b = ri(-3, 3), d = rnz(-3, 3);
    var c = x + a * y + b * z, e = y + d * z, Mx = [[1, a, b, c], [0, 1, d, e], [0, 0, 1, z]], t = [x, y, z];
    return QQ({ q: 'The augmented matrix of a system in ' + X + ', ' + Y + ', and ' + Z + ' has been reduced to the form below. Use back-substitution to find the solution.' + ctr(K.mat(Mx, 3)),
      mc: mcR(t, [[c, e, z], [z, y, x], [x, y, -z], [y, x, z]], fTri, tEx(t)),
      why: ['Row 3 says ' + m('<i>z</i> = ' + n(z)) + '.',
        'Row 2 says ' + m(P([[1, Y], [d, Z]]) + ' = ' + n(e)) + ', so ' + m('<i>y</i> = ' + n(e) + K.lin([[-d, n(z)]], true) + ' = ' + n(y)) + '.',
        'Row 1 says ' + m(P([[1, X], [a, Y], [b, Z]]) + ' = ' + n(c)) + ', so ' + m('<i>x</i> = ' + n(c) + K.lin([[-a, n(y)], [-b, n(z)]], true) + ' = ' + n(x)) + '. The solution is ' + fTri(t) + '.'] }, { t: 'msol', mat: Mx });
  }
  // L2: which row operation creates a 0
  function g522d() {
    var nr = pick([2, 3]), nc = nr + 1, r = ri(2, nr), a11 = pick([1, 1, -1, 2, 3]), c = rnz(-4, 4), Mx = [], i, j;
    for (i = 0; i < nr; i++) { var row = []; for (j = 0; j < nc; j++) row.push(ri(-6, 6)); Mx.push(row); }
    Mx[0][0] = a11; Mx[r - 1][0] = -c * a11;
    for (i = 0; i < nr; i++) if (i !== r - 1 && i !== 0 && Mx[i][0] === 0) Mx[i][0] = rnz(-5, 5);
    var ar1 = Mx[r - 1][0], fmt = function (o) { return rowOp(o[0], o[1], o[2]); };
    var w = [[r, -c, 1], [1, c, r], [r, R(1).div(c), 1]];
    if (nr === 3) w.push([r === 2 ? 3 : 2, c, 1]);
    return QQ({ q: 'Which row operation changes the entry in row ' + r + ', column 1 to 0?' + ctr(K.mat(Mx, nc - 1)),
      mc: mcR([r, c, 1], w, fmt, function () { var k; do { k = c + rnz(-2, 2); } while (k === 0 || k === c); return [r, k, 1]; }),
      why: ['The entry in row ' + r + ', column 1 is ' + n(ar1) + ', and the entry in row 1, column 1 is ' + n(a11) + '.',
        (c === 1 ? 'Adding row 1 to row ' + r : c === -1 ? 'Subtracting row 1 from row ' + r : 'Adding ' + n(c) + ' times row 1 to row ' + r) + ' gives ' + m(n(ar1) + (Math.abs(c) === 1 ? (c > 0 ? ' + ' : ' ' + M + ' ') + sub(a11) : K.lin([[c, n(a11)]], true)) + ' = 0') + ' in that position.',
        'So use ' + rowOp(r, c, 1) + '. It changes only row ' + r + '.'] }, { t: 'rowzero', mat: Mx, pos: [r, 1] });
  }
  // L3: classify a 3 × 3 system (and solve it if possible)
  function g523a() {
    var t = [ri(-4, 4), ri(-4, 4), ri(-4, 4)], kind = pick(['one', 'none', 'inf']), S, why;
    var lc = function (v) { return v === 1 ? '' : v === -1 ? M : n(v); };
    if (kind === 'one') {
      S = rSys3(t, true); var E = elimX(S);
      why = ['Eliminate ' + X + ' using equation 1: ' + E.txt + '.', 'Solve that pair: ' + m('<i>y</i> = ' + n(t[1])) + ', ' + m('<i>z</i> = ' + n(t[2])) + '; then equation 1 gives ' + m('<i>x</i> = ' + n(t[0])) + '.', 'The system has exactly one solution, ' + fTri(t) + '.'];
    } else {
      var r1, r2, r3, al, be;
      do {
        r1 = [1, rnz(-3, 3), rnz(-3, 3)]; r2 = [rnz(-3, 3), ri(-3, 3), ri(-3, 3)];
        al = pick([1, -1, 2]); be = pick([1, -1, 2, -2]);
        r3 = [0, 1, 2].map(function (j) { return al * r1[j] + be * r2[j]; });
      } while ((r1[1] * r2[2] - r1[2] * r2[1] === 0 && r1[0] * r2[2] - r1[2] * r2[0] === 0 && r1[0] * r2[1] - r1[1] * r2[0] === 0) || r3.filter(function (v) { return v !== 0; }).length < 2 || r2.filter(function (v) { return v !== 0; }).length < 2);
      var c1 = r1[0] * t[0] + r1[1] * t[1] + r1[2] * t[2], c2 = r2[0] * t[0] + r2[1] * t[1] + r2[2] * t[2], del = kind === 'none' ? rnz(-4, 4) : 0, c3 = al * c1 + be * c2 + del;
      S = [r1.concat([c1]), r2.concat([c2]), r3.concat([c3])];
      var comb = lc(al) + '(equation 1) ' + (be < 0 ? M : '+') + ' ' + lc(Math.abs(be)) + '(equation 2)';
      why = kind === 'none' ?
        ['Compare equation 3 with ' + comb + ', which is ' + e3(r3[0], r3[1], r3[2], al * c1 + be * c2) + '.', 'Equation 3 has the same left side but equals ' + n(c3) + ', so subtracting gives ' + m('0 = ' + n(del)) + ', which is false.', 'Row reduction produces the row ' + K.mat([[0, 0, 0, del]], 3) + ', so the system has no solution.'] :
        ['Equation 3 is exactly ' + comb + ': ' + e3(r3[0], r3[1], r3[2], c3) + '.', 'It adds no new information; row reduction produces a row of zeros, ' + K.mat([[0, 0, 0, 0]], 3) + '.', 'Two independent equations in three variables with no contradiction give infinitely many solutions.'];
    }
    var fmt = function (r) { return r[0] === 'one' ? 'Exactly one solution: ' + fTri(r.slice(1)) : CAT[r[0]]; };
    var bad = function () { var u = t.slice(), i = ri(0, 2); u[i] += rnz(-3, 3); return ['one'].concat(u); };
    var cor = kind === 'one' ? ['one'].concat(t) : [kind];
    var w = ['none', 'inf'].filter(function (s) { return s !== kind; }).map(function (s) { return [s]; }).concat([bad(), bad()]);
    return QQ({ q: 'Solve the system, or decide that it has no solution or infinitely many solutions.' + sys(S.map(eqR)), mc: mcR(cor, w, fmt, bad), why: why }, { t: 'cat3', eqs: S });
  }
  // L3: three-ingredient mixture
  var MIX = [['A shop mixes', 'peanuts', 'cashews', 'raisins', 'trail mix', 'p', 'c', 'r'], ['A coffee roaster blends', 'Colombian', 'Kenyan', 'Sumatran', 'coffee', 'c', 'k', 's'], ['A candy store mixes', 'gummies', 'chocolates', 'mints', 'candy', 'g', 'c', 'm']];
  function g523b() {
    var c = pick(MIX), pp, pc, pr, k, r, a, b, T, V, A3;
    do { pp = ri(2, 6); pc = ri(7, 12); pr = ri(1, 5); k = pick([2, 3]); r = ri(1, 5); a = k * r; b = ri(1, 6); T = a + b + r; V = pp * a + pc * b + pr * r; A3 = [[1, 1, 1], [pp, pc, pr], [1, 0, -k]]; } while (pr === pp || dv(A3) === 0);
    var u = iv(c[5]), v = iv(c[6]), w_ = iv(c[7]);
    var fmt = function (s) { return rh(s[0]) + ' lb ' + c[1] + ', ' + rh(s[1]) + ' lb ' + c[2] + ', ' + rh(s[2]) + ' lb ' + c[3]; };
    var S = [[1, 1, 1, T], [pp, pc, pr, V], [1, 0, -k, 0]];
    return QQ({ q: c[0] + ' ' + c[1] + ' ($' + pp + ' per pound), ' + c[2] + ' ($' + pc + ' per pound), and ' + c[3] + ' ($' + pr + ' per pound) to make ' + T + ' pounds of ' + c[4] + ' worth $' + V + ' in all. The mix uses ' + (k === 2 ? 'twice' : 'three times') + ' as many pounds of ' + c[1] + ' as ' + c[3] + '. How many pounds of each go into the mix?',
      mc: mcR([a, b, r], [[r, b, a], [b, a, r], [a, r, b]], fmt, function () { var r2 = r + rnz(-2, 2); if (r2 < 1) r2 = r + 1; return [k * r2, T - k * r2 - r2, r2]; }),
      why: ['Let ' + u + ', ' + v + ', and ' + w_ + ' be the pounds of ' + c[1] + ', ' + c[2] + ', and ' + c[3] + ': ' + m(u + ' + ' + v + ' + ' + w_ + ' = ' + T) + ', ' + m(P([[pp, u], [pc, v], [pr, w_]]) + ' = ' + V) + ', and ' + m(u + ' ' + M + ' ' + k + w_ + ' = 0') + '.',
        'The augmented matrix is ' + K.mat(S, 3) + '. Row-reduce it, or substitute ' + m(u + ' = ' + k + w_) + ' to get ' + m(v + ' + ' + (k + 1) + w_ + ' = ' + T) + ' and ' + m(P([[pc, v], [k * pp + pr, w_]]) + ' = ' + V) + '.',
        'Solving gives ' + m(w_ + ' = ' + r) + ' and ' + m(v + ' = ' + b) + ', so ' + m(u + ' = ' + k + '(' + r + ') = ' + a) + '.',
        'Check: ' + m(pp + '(' + a + ') + ' + pc + '(' + b + ') + ' + pr + '(' + r + ') = ' + V) + '.'] }, { t: 'sol', eqs: S });
  }
  // L3: dependent or inconsistent system from the matrix, in terms of y
  function g523c() {
    var k = rnz(-4, 4), c = rnz(-8, 8), a = pick([2, 3, -2, -1, -3]), dep = ri(1, 10) <= 7, del = dep ? 0 : rnz(-5, 5);
    var r1 = [1, k, c], r2 = [a, a * k, a * c + del];
    var cor = dep ? ['infy', -k, c] : ['none'];
    var w = dep ? [['infy', k, c], ['infy', -k, -c], ['none'], ['pt', c, 0]] : [['infy', -k, c], ['infy', k, c], ['pt', c, 0]];
    return QQ({ q: 'Use the Gauss-Jordan method to solve the system. Which describes the solution set? (If there are infinitely many solutions, they are written in terms of ' + Y + '.)' + sys([eqR(r1), eqR(r2)]),
      mc: mcR(cor, w, fSetLin, function () { return ['infy', -k + rnz(-2, 2), c + rnz(-2, 2)]; }),
      why: ['The augmented matrix is ' + K.mat([r1, r2], 2) + '.',
        rowOp(2, -a, 1) + ' gives ' + K.mat([r1, [0, 0, del]], 2) + (dep ? '. The zero row says ' + m('0 = 0') + ', so it gives no information.' : '. Row 2 says ' + m('0 = ' + n(del)) + ', which is false.'),
        dep ? 'Row 1 says ' + e2(1, k, c) + ', so ' + m('<i>x</i> = ' + P([[-k, Y], [c, '']])) + ' for any ' + Y + '. The solution set is ' + fSetLin(cor) + '.' : 'The system is inconsistent, so the solution set is ∅.'] }, { t: 'linset', eqs: [r1, r2] });
  }
  K.lesson('5.2', { title: 'Matrix Solution of Linear Systems', std: 'Lial 12e · Section 5.2', levels: [[g521a, g521b, g521c, g521d], [g522a, g522b, g522c, g522d], [g523a, g523b, g523c]] });

  /* ================= 5.3 Determinant Solution of Linear Systems ================= */
  function rand3(lo, hi) { var A = [], i, j; for (i = 0; i < 3; i++) { A.push([]); for (j = 0; j < 3; j++) A[i].push(ri(lo, hi)); } return A; }
  // L1: 2 × 2 determinant
  function g531a() {
    var A; do { A = [[rnz(-9, 9), rnz(-9, 9)], [rnz(-9, 9), rnz(-9, 9)]]; } while (false);
    var a = A[0][0], b = A[0][1], c = A[1][0], d = A[1][1], D = a * d - b * c;
    return QQ({ q: 'Evaluate the determinant.' + ctr(K.mat(A, null, true)),
      mc: mcR(D, [a * d + b * c, b * c - a * d, a * c - b * d], fNum, nEx(D, 5)),
      why: ['For ' + K.mat([[iv('a'), iv('b')], [iv('c'), iv('d')]], null, true) + ', the determinant is ' + m('<i>ad</i> ' + M + ' <i>bc</i>') + '.',
        d2txt(A) + ' = ' + m(n(a * d) + ' ' + M + ' ' + sub(b * c) + ' = ' + n(D)) + '.'] }, { t: 'det', mat: A });
  }
  // L1: minor or cofactor
  function g531b() {
    var A, i, j, Mn, sm;
    do { A = rand3(-5, 5); i = ri(0, 2); j = ri(0, 2); sm = minor(A, i, j); Mn = dv(sm); } while (Mn === 0 || A[i][j] === 0);
    var sign = (i + j) % 2 ? -1 : 1, kind = K.coin() ? 'minor' : 'cofactor', ans = kind === 'minor' ? Mn : sign * Mn;
    var wt = dv(minor(A, j, i)), w = [-ans, wt, kind === 'minor' ? sign * Mn : Mn, A[i][j] * ans];
    return QQ({ q: 'Find the ' + kind + ' of the entry ' + n(A[i][j]) + ' in row ' + (i + 1) + ', column ' + (j + 1) + ' of the matrix.' + ctr(K.mat(A)),
      mc: mcR(ans, w, fNum, nEx(ans, 5)),
      why: ['Delete row ' + (i + 1) + ' and column ' + (j + 1) + '. The minor is ' + K.mat(sm, null, true) + ' = ' + d2txt(sm) + ' = ' + n(Mn) + '.',
        kind === 'cofactor' ? 'The cofactor attaches the sign ' + m('(' + M + '1)<sup>' + (i + 1) + ' + ' + (j + 1) + '</sup>') + ', which is ' + (sign > 0 ? '+' : M) + ' here: the cofactor is ' + n(ans) + '.' :
          'A minor has no sign attached, so the answer is ' + n(ans) + ' (the cofactor would be ' + n(sign * Mn) + ').'] }, { t: 'cof', mat: A, i: i, j: j, kind: kind });
  }
  // L1: which determinant is Dx / Dy
  function g531c() {
    var s, v = K.coin() ? 'x' : 'y';
    do { s = rSys2(ri(-5, 5), ri(-5, 5), -6, 6); } while (s[0][2] === 0 || s[1][2] === 0 || (s[0][2] === s[0][0] && s[1][2] === s[1][0]) || (s[0][2] === s[0][1] && s[1][2] === s[1][1]) || (s[0][0] === s[0][1] && s[1][0] === s[1][1]));
    var a1 = s[0][0], b1 = s[0][1], c1 = s[0][2], a2 = s[1][0], b2 = s[1][1], c2 = s[1][2];
    var D = [[a1, b1], [a2, b2]], Dx = [[c1, b1], [c2, b2]], Dy = [[a1, c1], [a2, c2]];
    var cor = v === 'x' ? Dx : Dy, w = [D, v === 'x' ? Dy : Dx, v === 'x' ? [[b1, c1], [b2, c2]] : [[c1, a1], [c2, a2]]];
    var Dv = m('<i>D</i><sub><i>' + v + '</i></sub>');
    return QQ({ q: 'For the system below, which determinant is ' + Dv + ' in Cramer’s rule?' + sys(s.map(eqR)),
      mc: mcR(cor, w, fDet, function () { var A = cor.map(function (r) { return r.slice(); }); A[ri(0, 1)][ri(0, 1)] += rnz(-2, 2); return A; }),
      why: [m('<i>D</i>') + ' uses the coefficients of ' + X + ' and ' + Y + ': ' + K.mat(D, null, true) + '.',
        Dv + ' replaces the ' + iv(v) + '-column (column ' + (v === 'x' ? 1 : 2) + ') with the constants ' + n(c1) + ' and ' + n(c2) + '.',
        'So ' + Dv + ' = ' + K.mat(cor, null, true) + '.'] }, { t: 'dmat', eqs: s, v: v });
  }
  // L2: 3 × 3 determinant
  function g532a() {
    var A, t;
    do { A = rand3(-4, 5); t = [0, 1, 2].map(function (j) { return A[0][j] * dv(minor(A, 0, j)); }); } while (t[1] === 0 || t[2] === 0);
    var D = t[0] - t[1] + t[2];
    var mt = function (j) { var sm = minor(A, 0, j); return sub(A[0][j]) + K.mat(sm, null, true) + ' = ' + m(sub(A[0][j]) + '(' + n(dv(sm)) + ') = ' + n(t[j])); };
    return QQ({ q: 'Evaluate the determinant.' + ctr(K.mat(A, null, true)),
      mc: mcR(D, [t[0] + t[1] + t[2], -D, t[0] - t[1] - t[2]], fNum, nEx(D, 6)),
      why: ['Expand along row 1 with the signs +, ' + M + ', +.',
        'The three products: ' + mt(0) + '; ' + mt(1) + '; ' + mt(2) + '.',
        'Combine with the signs: ' + m(n(t[0]) + ' ' + M + ' ' + sub(t[1]) + ' + ' + sub(t[2]) + ' = ' + n(D)) + '.'] }, { t: 'det', mat: A });
  }
  // L2: Cramer's rule, two variables
  function g532b() {
    var a1, b1, a2, b2, c1, c2, D, Dx, Dy, ok = false;
    while (!ok) {
      a1 = rnz(-6, 6); b1 = rnz(-6, 6); a2 = rnz(-6, 6); b2 = rnz(-6, 6); D = a1 * b2 - a2 * b1;
      if (D === 0) continue;
      if (K.coin()) { var x0 = ri(-5, 5), y0 = ri(-5, 5); c1 = a1 * x0 + b1 * y0; c2 = a2 * x0 + b2 * y0; } else { c1 = ri(-12, 12); c2 = ri(-12, 12); }
      Dx = c1 * b2 - c2 * b1; Dy = a1 * c2 - a2 * c1;
      ok = R(Dx, D).d <= 6 && R(Dy, D).d <= 6 && Dx !== 0 && Dy !== 0;
    }
    var x = R(Dx, D), y = R(Dy, D);
    return QQ({ q: 'Use Cramer’s rule to solve the system. Write the solution as an ordered pair.' + sys([e2(a1, b1, c1), e2(a2, b2, c2)]),
      mc: mcR([x, y], [[y, x], [R(D, Dx), R(D, Dy)], [Dx, Dy], [x.neg(), y.neg()]], fPt, pEx(x, y)),
      why: [m('<i>D</i>') + ' = ' + K.mat([[a1, b1], [a2, b2]], null, true) + ' = ' + d2txt([[a1, b1], [a2, b2]]) + ' = ' + n(D) + '.',
        m('<i>D</i><sub><i>x</i></sub>') + ' = ' + K.mat([[c1, b1], [c2, b2]], null, true) + ' = ' + n(Dx) + ' and ' + m('<i>D</i><sub><i>y</i></sub>') + ' = ' + K.mat([[a1, c1], [a2, c2]], null, true) + ' = ' + n(Dy) + '.',
        qeq('<i>x</i>', Dx, D) + ' and ' + qeq('<i>y</i>', Dy, D) + '. The solution is ' + K.pt(x, y) + '.'] }, { t: 'sol', eqs: [[a1, b1, c1], [a2, b2, c2]] });
  }
  // L2: Cramer's rule, one variable of a 3 × 3 system
  function g532c() {
    var t, S, A, D;
    do { t = [ri(-4, 4), ri(-4, 4), ri(-4, 4)]; S = rSys3(t, false); A = coefM(S); D = dv(A); } while (Math.abs(D) > 40);
    var vi = ri(0, 2), vn = ['x', 'y', 'z'][vi], Av = A.map(function (r, i) { var u = r.slice(); u[vi] = S[i][3]; return u; }), Dv = dv(Av), ans = t[vi];
    var others = t.filter(function (_, i) { return i !== vi; });
    return QQ({ q: 'Use Cramer’s rule to find the value of ' + iv(vn) + ' in the solution of the system.' + sys(S.map(eqR)),
      mc: mcR(ans, [Dv, others[0], others[1], -ans, R(D).div(Dv === 0 ? 1 : Dv)], fNum, nEx(ans, 4)),
      why: ['The coefficient determinant is ' + m('<i>D</i>') + ' = ' + K.mat(A, null, true) + ' = ' + n(D) + '.',
        m('<i>D</i><sub><i>' + vn + '</i></sub>') + ' replaces the ' + iv(vn) + '-column with the constants: ' + K.mat(Av, null, true) + ' = ' + n(Dv) + '.',
        qeq(iv(vn), Dv, D) + '.'] }, { t: 'solvar', eqs: S, v: vi });
  }
  // L3: the value of k that makes D = 0, and what the system does for that k
  var SOLN = { one: 'exactly one solution', none: 'no solution', inf: 'infinitely many solutions' };
  function g533a() {
    var a, t, k0, c1, c2, d, dep = K.coin(), Kk = iv('k');
    do { a = rnz(-5, 5); t = pick([2, 3, -2, -3]); k0 = rnz(-5, 5); c1 = rnz(-9, 9); } while (Math.abs(t * a) > 12);
    d = t * k0; c2 = dep ? t * c1 : t * c1 + rnz(-6, 6);
    var kind = dep ? 'inf' : 'none', other = dep ? 'none' : 'inf';
    var fmt = function (r) { return m(Kk + ' = ' + rh(r[0])) + '; ' + SOLN[r[1]]; };
    return QQ({ q: 'For which value of ' + Kk + ' is the determinant ' + m('<i>D</i>') + ' of this system equal to 0 (so Cramer’s rule cannot be used), and how many solutions does the system have for that value of ' + Kk + '?' + sys([m(P([[a, X]]) + ' + ' + Kk + Y + ' = ' + n(c1)), e2(t * a, d, c2)]),
      mc: mcR([k0, kind], [[k0, other], [k0, 'one'], [-k0, kind], [d, kind]], fmt, function () { return [k0 + rnz(-3, 3), kind]; }),
      why: [m('<i>D</i> = ') + K.mat([[a, Kk], [t * a, d]], null, true) + ' = ' + m(sub(a) + '(' + n(d) + ') ' + M + ' ' + Kk + '(' + n(t * a) + ') = ' + P([[a * d, ''], [-t * a, Kk]])) + '.',
        'Set ' + m('<i>D</i> = 0') + ': ' + m(P([[t * a, Kk]]) + ' = ' + n(a * d)) + ', so ' + m(Kk + ' = ' + n(k0)) + '. For every other value of ' + Kk + ', ' + m('<i>D</i> ≠ 0') + ' and the system has exactly one solution.',
        'With ' + m(Kk + ' = ' + n(k0)) + ', multiply the first equation by ' + n(t) + ': ' + e2(t * a, d, t * c1) + '. ' + (dep ? 'That is exactly the second equation, so both equations describe the same line: infinitely many solutions.' : 'The second equation has the same left side but equals ' + n(c2) + ', so the lines are parallel: no solution.')] },
      { t: 'kD0f', a: a, ta: t * a, d: d, c1: c1, c2: c2 });
  }
  // L3: area of a triangle with one corner at the origin: ½|ad − bc|
  var LAND = [['A surveyor maps a triangular plot of land from GPS points', 'meters'], ['A farmer marks off a triangular pasture with a GPS unit', 'meters'], ['A park planner lays out a triangular flower bed on a site plan', 'feet']];
  function g533b() {
    var mpt = function (x, y) { return m(K.pt(x, y)); };
    var shift = ri(1, 3) === 1, a, b, c, d, D, p0 = 0, q0 = 0, ctx = pick(LAND), unit, q;
    if (shift) {
      do { a = ri(-6, 6); b = ri(-6, 6); c = ri(-6, 6); d = ri(-6, 6); D = a * d - b * c; } while (Math.abs(D) < 4 || (a === 0 && b === 0) || (c === 0 && d === 0));
      do { p0 = ri(-5, 5); q0 = ri(-5, 5); } while (p0 === 0 && q0 === 0);
      unit = 'square units';
    } else {
      do { a = ri(10, 60); b = ri(-20, 40); c = ri(-20, 40); d = ri(10, 60); D = a * d - b * c; } while (Math.abs(D) < 20 || b === 0 || c === 0);
      unit = 'square ' + ctx[1];
    }
    var pts = [[p0, q0], [p0 + a, q0 + b], [p0 + c, q0 + d]], area = R(Math.abs(D), 2);
    var unit1 = unit.replace('units', 'unit').replace('meters', 'meter').replace('feet', 'foot');
    var fmt = function (v) { return K.comma(R(v).val()) + ' ' + (R(v).eq(1) ? unit1 : unit); };
    if (shift) q = 'A triangle has vertices ' + mpt(pts[0][0], pts[0][1]) + ', ' + mpt(pts[1][0], pts[1][1]) + ', and ' + mpt(pts[2][0], pts[2][1]) + '. Translate it so that ' + mpt(pts[0][0], pts[0][1]) + ' moves to the origin (' + [[p0, X], [q0, Y]].filter(function (u) { return u[0] !== 0; }).map(function (u) { return (u[0] > 0 ? 'subtract ' + u[0] + ' from' : 'add ' + (-u[0]) + ' to') + ' every ' + u[1] + '-coordinate'; }).join(' and ') + '), then use a determinant to find the area of the triangle.';
    else q = ctx[0] + '. With one corner at the origin ' + mpt(0, 0) + ', the other two corners are at ' + mpt(a, b) + ' and ' + mpt(c, d) + ', in ' + ctx[1] + '. Use a determinant to find the area.';
    var why = [];
    if (shift) why.push('Translating a triangle does not change its area. Subtracting ' + mpt(p0, q0) + ' from each vertex gives ' + mpt(0, 0) + ', ' + mpt(a, b) + ', and ' + mpt(c, d) + '.');
    why.push('A triangle with corners ' + mpt(0, 0) + ', ' + m('(<i>a</i>, <i>b</i>)') + ', and ' + m('(<i>c</i>, <i>d</i>)') + ' has area ' + m(K.f(1, 2) + '|<i>ad</i> ' + M + ' <i>bc</i>|') + ', half the absolute value of the determinant ' + K.mat([[iv('a'), iv('b')], [iv('c'), iv('d')]], null, true) + '.');
    why.push('Here ' + K.mat([[a, b], [c, d]], null, true) + ' = ' + d2txt([[a, b], [c, d]]) + ' = ' + m(n(a * d) + ' ' + M + ' ' + sub(b * c) + ' = ' + n(D)) + '.');
    why.push('Area = ' + m(K.f(1, 2) + '|' + n(D) + '| = ' + K.comma(area.val())) + ' ' + unit + '.' + (D < 0 ? ' The absolute value matters: an area is never negative.' : ''));
    return QQ({ q: q, mc: mcR(area, [Math.abs(D), R(Math.abs(a * d + b * c), 2), R(Math.abs(a * c - b * d), 2), R(Math.abs(D), 4)].filter(function (v) { return R(v).n !== 0; }), fmt, function () { var v; do { v = area.add(rnz(-5, 5)); } while (v.val() <= 0); return v; }), why: why },
      { t: 'area', pts: pts });
  }
  // L3: value of k that blocks Cramer's rule
  function g533c() {
    var a, b, d, k;
    do { a = rnz(-6, 6); b = rnz(-6, 6); d = rnz(-6, 6); } while ((a * d) % b !== 0 || Math.abs(a * d / b) > 12);
    k = a * d / b; var c1 = rnz(-9, 9), c2 = rnz(-9, 9), Kk = iv('k');
    return QQ({ q: 'For which value of ' + Kk + ' can Cramer’s rule <b>not</b> be used to solve this system?' + sys([m(P([[a, X]]) + ' + ' + Kk + Y + ' = ' + n(c1)), e2(b, d, c2)]),
      mc: mcR(k, [-k, a * d, R(b * d, a), R(a * b, d)], fNum, nEx(k, 4)),
      why: ['Cramer’s rule divides by ' + m('<i>D</i>') + ', so it fails when ' + m('<i>D</i> = 0') + '. Here ' + m('<i>D</i> = ') + K.mat([[a, Kk], [b, d]], null, true) + ' = ' + m(sub(a) + '(' + n(d) + ') ' + M + ' ' + Kk + '(' + n(b) + ') = ' + P([[a * d, ''], [-b, Kk]])) + '.',
        'Set ' + m('<i>D</i> = 0') + ': ' + m(P([[b, Kk]]) + ' = ' + n(a * d)) + ', so ' + m(Kk + ' = ' + n(k)) + '.',
        'For that value the system has no solution or infinitely many, so another method is needed.'] }, { t: 'kD0', a: a, b: b, d: d });
  }
  // L3: Cramer's rule, full 3 × 3 solution
  function g533d() {
    var t, S, A, D;
    do { t = [ri(-4, 4), ri(-4, 4), ri(-4, 4)]; S = rSys3(t, false); A = coefM(S); D = dv(A); } while (Math.abs(D) > 40);
    var Dk = [0, 1, 2].map(function (vi) { return dv(A.map(function (r, i) { var u = r.slice(); u[vi] = S[i][3]; return u; })); });
    return QQ({ q: 'Use Cramer’s rule to solve the system. Write the solution as an ordered triple.' + sys(S.map(eqR)),
      mc: mcR(t, triW(t).concat([Dk]), fTri, tEx(t)),
      why: ['The coefficient determinant is ' + m('<i>D</i>') + ' = ' + K.mat(A, null, true) + ' = ' + n(D) + ', which is not 0.',
        'Replacing each column in turn with the constants gives ' + m('<i>D</i><sub><i>x</i></sub> = ' + n(Dk[0])) + ', ' + m('<i>D</i><sub><i>y</i></sub> = ' + n(Dk[1])) + ', and ' + m('<i>D</i><sub><i>z</i></sub> = ' + n(Dk[2])) + '.',
        qeq('<i>x</i>', Dk[0], D) + ', ' + qeq('<i>y</i>', Dk[1], D) + ', and ' + qeq('<i>z</i>', Dk[2], D) + '. The solution is ' + fTri(t) + '.'] }, { t: 'sol', eqs: S });
  }
  K.lesson('5.3', { title: 'Determinant Solution of Linear Systems', std: 'Lial 12e · Section 5.3', levels: [[g531a, g531b, g531c], [g532a, g532b, g532c], [g533a, g533b, g533c, g533d]] });

  /* ================= 5.4 Partial Fractions ================= */
  function pmul(p, q) { var r = [], i, j; for (i = 0; i < p.length + q.length - 1; i++) r.push(0); for (i = 0; i < p.length; i++) for (j = 0; j < q.length; j++) r[i + j] += p[i] * q[j]; return r; }
  function padd(p, q) { var L = Math.max(p.length, q.length), r = []; for (var i = 0; i < L; i++) { var a = p[p.length - L + i] || 0, b = q[q.length - L + i] || 0; r.push(a + b); } return r; }
  function psc(p, k) { return p.map(function (v) { return v * k; }); }
  function pev(c, x) { return c.reduce(function (s, v) { return s * x + v; }, 0); }
  function pFmt(c) { var L = c.length; return P(c.map(function (v, i) { return [v, K.xp(L - 1 - i)]; })); }
  function lf(r) { return [1, -r]; }                      // x − r
  function qf(k) { return [1, 0, k]; }                    // x² + k
  function facH(f) { return f.length === 2 ? K.minusH(X, -f[1]) : P([[1, K.xp(2)], [f[2], '']]); }
  function isX(f) { return f.length === 2 && f[1] === 0; }
  function powH(f, pw) { var h = facH(f); return pw === 1 ? h : (isX(f) ? h : '(' + h + ')') + '<sup>' + pw + '</sup>'; }
  function facProd(list) { return list.slice().sort(function (u, v) { return (isX(v[0]) ? 1 : 0) - (isX(u[0]) ? 1 : 0); }).map(function (t) { var f = t[0], pw = t[1]; if (isX(f)) return pw === 1 ? X : X + '<sup>' + pw + '</sup>'; return '(' + facH(f) + ')' + (pw > 1 ? '<sup>' + pw + '</sup>' : ''); }).join(''); }
  function fpar(r) { return r === 0 ? X : '(' + K.minusH(X, r) + ')'; }
  function tkey(t) { var f = t[1]; return [f.length, f.length === 2 ? -f[1] : f[2], t[2]]; }
  // decomposition {q: quotient coeffs or null, t: [[numerator coeffs, factor coeffs, power], ...]} → canonical html
  function decH(dc, ord) {
    ord = ord || [];
    var key = function (t) { var i = ord.indexOf(JSON.stringify(t[1])), k = tkey(t); return [i < 0 ? 1000 : i].concat(k); };
    var ts = dc.t.slice().sort(function (u, v) { var a = key(u), b = key(v); for (var i = 0; i < 4; i++) if (a[i] !== b[i]) return a[i] - b[i]; return 0; });
    var parts = [], first = true;
    if (dc.q) { parts.push(m(pFmt(dc.q))); first = false; }
    ts.forEach(function (t) {
      var nm = t[0].slice(); while (nm.length > 1 && nm[0] === 0) nm.shift();
      var den = powH(t[1], t[2]);
      if (nm.length === 1) { var v = R(nm[0]); parts.push(m((first ? (v.n < 0 ? M : '') : (v.n < 0 ? M + ' ' : '+ ')) + K.frx(v.abs().html(), den))); }
      else if (nm[0] < 0) parts.push(m((first ? M : M + ' ') + K.frx(pFmt(psc(nm, -1)), den)));   // − (4x + 1)/(x² + 9), never + −4x…
      else parts.push(m((first ? '' : '+ ') + K.frx(pFmt(nm), den)));
      first = false;
    });
    return parts.join(' ');
  }
  function dec(q, terms) { return { q: q, t: terms }; }
  // formatter that lists factors in the order of the correct decomposition (same order for every choice)
  function decF(cor) { var ord = []; cor.t.forEach(function (t) { var k = JSON.stringify(t[1]); if (ord.indexOf(k) < 0) ord.push(k); }); return function (dc) { return decH(dc, ord); }; }
  function eqSplit(lhs, terms) { return m(lhs + ' =') + ' ' + terms.map(function (t, i) { return m((i ? '+ ' : '') + t); }).join(' '); }
  function bigFrac(num, denH) { return ctr(m(K.frx(pFmt(num), denH))); }
  var LET = ['A', 'B', 'C', 'D'];
  // L1: choose the form
  function g541a() {
    var type = ri(1, 3), facs, cor, w, why, num, r, s, k;
    k = pick([1, 2, 3, 4, 5, 9]);
    if (type === 1) { do { r = rnz(-5, 5); s = ri(-5, 5); } while (r === s); facs = [[lf(r), 2], [lf(s), 1]]; cor = [[0, 1, 0], [0, 2, 0], [1, 1, 0]]; w = [[[0, 2, 0], [1, 1, 0]], [[0, 1, 0], [0, 1, 0], [1, 1, 0]], [[0, 1, 0], [1, 1, 0]]]; }
    else if (type === 2) { r = ri(-5, 5); facs = [[lf(r), 1], [qf(k), 1]]; cor = [[0, 1, 0], [1, 1, 1]]; w = [[[0, 1, 0], [1, 1, 0]], [[0, 1, 1], [1, 1, 0]], [[1, 1, 1]]]; }
    else { facs = [[lf(0), 2], [qf(k), 1]]; cor = [[0, 1, 0], [0, 2, 0], [1, 1, 1]]; w = [[[0, 2, 0], [1, 1, 1]], [[0, 1, 0], [0, 2, 0], [1, 1, 0]], [[0, 1, 0], [1, 1, 1]]]; }
    var den = facs.reduce(function (a, f) { var p = [1]; for (var i = 0; i < f[1]; i++) p = pmul(p, f[0]); return pmul(a, p); }, [1]);
    do { num = [rnz(-4, 4), ri(-6, 6), rnz(-9, 9)]; } while (facs.some(function (f) { return f[0].length === 2 && pev(num, -f[0][1]) === 0; }) || (num[1] === 0 && num[2] === num[0] * k));
    var fmt = function (form) {
      var li = 0;
      return m(form.map(function (t) { var top = t[2] === 0 ? iv(LET[li++]) : iv(LET[li++] + 'x') + ' + ' + iv(LET[li++]); return K.frx(top, powH(facs[t[0]][0], t[1])); }).join(' + '));
    };
    if (type === 1) why = ['The repeated factor ' + m(powH(lf(r), 2)) + ' needs one term for each power: ' + m(K.frx(iv('A'), facH(lf(r)))) + ' and ' + m(K.frx(iv('B'), powH(lf(r), 2))) + '.', 'The distinct linear factor ' + m(facH(lf(s))) + ' gets one term with a constant numerator.', 'So the form is ' + fmt(cor) + '.'];
    else if (type === 2) why = [m(facH(lf(r))) + ' is linear, so it gets a constant numerator.', m(facH(qf(k))) + ' is an irreducible quadratic (it has no real zeros), so it gets a linear numerator.', 'So the form is ' + fmt(cor) + '.'];
    else why = [m(X + '<sup>2</sup>') + ' is the repeated linear factor ' + m(X + ' · ' + X) + ', so it needs terms over ' + X + ' and over ' + m(X + '<sup>2</sup>') + '.', m(facH(qf(k))) + ' is irreducible, so it gets a linear numerator.', 'So the form is ' + fmt(cor) + '.'];
    return QQ({ q: 'Which is the correct form of the partial fraction decomposition?' + bigFrac(num, facProd(facs)), mc: mcR(cor, w, fmt), why: why },
      { t: 'pform', num: num, den: den, facs: facs.map(function (f) { return [f[0], f[1]]; }) });
  }
  // L1: find one constant
  function g541b() {
    var r, s, A, B; do { r = ri(-5, 5); s = ri(-5, 5); } while (r === s);
    A = rnz(-6, 6); B = rnz(-6, 6);
    var num = padd(psc(lf(s), A), psc(lf(r), B)), which = K.coin() ? 'A' : 'B', ans = which === 'A' ? A : B, root = which === 'A' ? r : s, other = which === 'A' ? s : r;
    var nv = pev(num, root);
    return QQ({ q: 'In the decomposition below, find ' + iv(which) + '.' + ctr(m(K.frx(pFmt(num), fpar(r) + fpar(s)) + ' = ' + K.frx(iv('A'), facH(lf(r))) + ' + ' + K.frx(iv('B'), facH(lf(s))))),
      mc: mcR(ans, [which === 'A' ? B : A, nv, -ans, R(root - other, nv === 0 ? 1 : nv)], fNum, nEx(ans, 4)),
      why: ['Multiply both sides by ' + m(fpar(r) + fpar(s)) + ': ' + m(pFmt(num) + ' = <i>A</i>' + fpar(s) + ' + <i>B</i>' + fpar(r)) + '.',
        'Let ' + m('<i>x</i> = ' + n(root)) + ', which makes the ' + iv(which === 'A' ? 'B' : 'A') + '-term 0: ' + m(n(nv) + ' = ' + iv(which) + '(' + n(root - other) + ')') + '.',
        'So ' + qeq(iv(which), nv, root - other) + '.'] },
      { t: 'pconst', num: num, den: pmul(lf(r), lf(s)), root: root });
  }
  // L1: proper or improper
  function g541c() {
    function quad() { var r = ri(-5, 5), s = ri(-5, 5); return pmul(lf(r), lf(s)); }
    function rp(d) { var p = [rnz(-5, 5)]; for (var i = 0; i < d; i++) p.push(ri(-7, 7)); return p; }
    var imp = K.coin() ? [rp(2), quad()] : [rp(3), quad()];
    var props = [[rp(1), quad()], [rp(2), pmul(quad(), lf(ri(-4, 4)))], [[rnz(-9, 9)], quad()], [rp(1), pmul(lf(ri(-4, 4)), qf(pick([1, 4, 9])))]];
    var fmt = function (f) { return m(K.frx(pFmt(f[0]), pFmt(f[1]))); };
    return QQ({ q: 'Which rational expression is improper, so that you must use long division before finding its partial fraction decomposition?',
      mc: mcR(imp, K.shuffle(props), fmt),
      why: ['An expression is proper when the degree of the numerator is less than the degree of the denominator.', 'In ' + fmt(imp) + ', the numerator has degree ' + (imp[0].length - 1) + ' and the denominator has degree 2, so it is improper: divide first.', 'In each of the other choices the numerator has a lower degree than the denominator.'] }, { t: 'improper' });
  }
  function decEx(c, k) { return function () { var d = JSON.parse(JSON.stringify(c)); var t = d.t[ri(0, d.t.length - 1)]; var j = ri(0, t[0].length - 1); t[0][j] += rnz(-2, 2); if (t[0].every(function (v) { return v === 0; })) t[0][t[0].length - 1] = 1; return d; }; }
  // L2: distinct linear factors, denominator not factored
  function g542a() {
    var r, s, A, B; do { r = ri(-6, 6); s = ri(-6, 6); A = rnz(-6, 6); B = rnz(-6, 6); } while (r >= s || A === B);
    var num = padd(psc(lf(s), A), psc(lf(r), B)), den = pmul(lf(r), lf(s));
    var mk = function (a, b) { return dec(null, [[[a], lf(r), 1], [[b], lf(s), 1]]); }, cor = mk(A, B);
    return QQ({ q: 'Find the partial fraction decomposition.' + bigFrac(num, pFmt(den)),
      mc: mcR(cor, [mk(B, A), mk(A * (r - s), B * (s - r)), mk(A, -B), dec(null, [[[A], lf(-r), 1], [[B], lf(-s), 1]])], decF(cor), decEx(cor)),
      why: ['Factor the denominator: ' + m(pFmt(den) + ' = ' + fpar(r) + fpar(s)) + '. Write ' + m(K.frx(iv('A'), facH(lf(r))) + ' + ' + K.frx(iv('B'), facH(lf(s)))) + '.',
        'Multiply by the denominator: ' + eqSplit(pFmt(num), ['<i>A</i>' + fpar(s), '<i>B</i>' + fpar(r)]) + '.',
        m('<i>x</i> = ' + n(r)) + ': ' + m(n(pev(num, r)) + ' = ' + P([[r - s, '<i>A</i>']])) + ', so ' + m('<i>A</i> = ' + n(A)) + '. ' + m('<i>x</i> = ' + n(s)) + ': ' + m(n(pev(num, s)) + ' = ' + P([[s - r, '<i>B</i>']])) + ', so ' + m('<i>B</i> = ' + n(B)) + '.',
        'The decomposition is ' + decF(cor)(cor) + '.'] }, { t: 'pfd', num: num, den: den });
  }
  // L2: repeated linear factor
  function g542b() {
    var r = rnz(-5, 5), A = rnz(-6, 6), B; do { B = rnz(-9, 9); } while (B === A);
    var num = [A, B - A * r], den = pmul(lf(r), lf(r)), fact = K.coin();
    var mk = function (a, b) { return dec(null, [[[a], lf(r), 1], [[b], lf(r), 2]]); }, cor = mk(A, B);
    return QQ({ q: 'Find the partial fraction decomposition.' + bigFrac(num, fact ? powH(lf(r), 2) : pFmt(den)),
      mc: mcR(cor, [mk(B, A), mk(A, B - A * r), mk(A, -B), mk(-A, B)], decF(cor), decEx(cor)),
      why: [(fact ? '' : 'The denominator is ' + m(powH(lf(r), 2)) + '. ') + 'A repeated factor needs a term for each power: ' + m(K.frx(iv('A'), facH(lf(r))) + ' + ' + K.frx(iv('B'), powH(lf(r), 2))) + '. Multiply by ' + m(powH(lf(r), 2)) + ': ' + m(pFmt(num) + ' = <i>A</i>' + fpar(r) + ' + <i>B</i>') + '.',
        'Match the ' + X + '-coefficients: ' + m('<i>A</i> = ' + n(A)) + '. Let ' + m('<i>x</i> = ' + n(r)) + ': ' + m('<i>B</i> = ' + n(B)) + '.',
        'The decomposition is ' + decF(cor)(cor) + '.'] }, { t: 'pfd', num: num, den: den });
  }
  // L2: irreducible quadratic factor
  function g542c() {
    var r = ri(-4, 4), k = pick([1, 2, 3, 4, 9]), A = rnz(-5, 5), B = rnz(-4, 4), Cc = ri(-6, 6);
    var num = padd(psc(qf(k), A), pmul([B, Cc], lf(r))), den = pmul(lf(r), qf(k)), n0 = pev(num, r);
    var mk = function (a, b, c) { return dec(null, [[[a], lf(r), 1], [[b, c], qf(k), 1]]); }, cor = mk(A, B, Cc);
    return QQ({ q: 'Find the partial fraction decomposition.' + bigFrac(num, facProd([[lf(r), 1], [qf(k), 1]])),
      mc: mcR(cor, [mk(A, Cc, B), mk(A, -B, Cc), mk(n0, B, Cc), mk(A, B, -Cc), mk(-A, B, Cc)], decF(cor), decEx(cor)),
      why: ['Write ' + m(K.frx(iv('A'), facH(lf(r))) + ' + ' + K.frx('<i>Bx</i> + <i>C</i>', facH(qf(k)))) + ' and multiply: ' + eqSplit(pFmt(num), ['<i>A</i>(' + facH(qf(k)) + ')', '(<i>Bx</i> + <i>C</i>)' + fpar(r)]) + '.',
        'Let ' + m('<i>x</i> = ' + n(r)) + ': ' + m(n(n0) + ' = ' + P([[r * r + k, '<i>A</i>']])) + ', so ' + m('<i>A</i> = ' + n(A)) + '.',
        'Match coefficients. ' + m(X + '<sup>2</sup>') + ': ' + m('<i>A</i> + <i>B</i> = ' + n(num[0])) + ', so ' + m('<i>B</i> = ' + n(B)) + '. ' + X + ': ' + m('<i>C</i> ' + M + ' (' + n(r) + ')(' + n(B) + ') = ' + n(num[1])) + ', so ' + m('<i>C</i> = ' + n(Cc)) + '.',
        'The decomposition is ' + decF(cor)(cor) + '.'] }, { t: 'pfd', num: num, den: den });
  }
  // L3: three distinct linear factors (factor the cubic first)
  function g543a() {
    var r, s, A, B, Cc; do { r = rnz(-5, 5); s = rnz(-5, 5); A = rnz(-5, 5); B = rnz(-5, 5); Cc = rnz(-5, 5); } while (r >= s || A === B || B === Cc || A === Cc);
    var den = pmul([1, 0], pmul(lf(r), lf(s)));
    var num = padd(padd(psc(pmul(lf(r), lf(s)), A), psc(pmul([1, 0], lf(s)), B)), psc(pmul([1, 0], lf(r)), Cc));
    var mk = function (a, b, c) { return dec(null, [[[a], lf(0), 1], [[b], lf(r), 1], [[c], lf(s), 1]]); }, cor = mk(A, B, Cc);
    return QQ({ q: 'Find the partial fraction decomposition.' + bigFrac(num, pFmt(den)),
      mc: mcR(cor, [mk(B, A, Cc), mk(A, Cc, B), mk(A, B, -Cc), mk(-A, B, Cc)], decF(cor), decEx(cor)),
      why: ['Factor out ' + X + ', then factor the quadratic: ' + m(pFmt(den) + ' = <i>x</i>' + fpar(r) + fpar(s)) + '. Write ' + m(K.frx(iv('A'), X)) + ' ' + m('+ ' + K.frx(iv('B'), facH(lf(r)))) + ' ' + m('+ ' + K.frx(iv('C'), facH(lf(s)))) + '.',
        'Multiply by the denominator: ' + eqSplit(pFmt(num), ['<i>A</i>' + fpar(r) + fpar(s), '<i>Bx</i>' + fpar(s), '<i>Cx</i>' + fpar(r)]) + '.',
        m('<i>x</i> = 0') + ': ' + m(n(pev(num, 0)) + ' = ' + P([[r * s, '<i>A</i>']])) + ', so ' + m('<i>A</i> = ' + n(A)) + '. ' + m('<i>x</i> = ' + n(r)) + ': ' + m(n(pev(num, r)) + ' = ' + P([[r * (r - s), '<i>B</i>']])) + ', so ' + m('<i>B</i> = ' + n(B)) + '. ' + m('<i>x</i> = ' + n(s)) + ': ' + m(n(pev(num, s)) + ' = ' + P([[s * (s - r), '<i>C</i>']])) + ', so ' + m('<i>C</i> = ' + n(Cc)) + '.',
        'The decomposition is ' + decF(cor)(cor) + '.'] }, { t: 'pfd', num: num, den: den });
  }
  // L3: improper fraction: divide first
  function g543b() {
    var r, s, A, B, t; do { r = ri(-5, 5); s = ri(-5, 5); A = rnz(-5, 5); B = rnz(-5, 5); t = rnz(-4, 4); } while (r >= s || A === B);
    var den = pmul(lf(r), lf(s)), rem = padd(psc(lf(s), A), psc(lf(r), B)), num = padd(pmul([1, t], den), rem);
    var mk = function (q, a, b) { return dec(q, [[[a], lf(r), 1], [[b], lf(s), 1]]); }, cor = mk([1, t], A, B);
    return QQ({ q: 'Find the partial fraction decomposition.' + bigFrac(num, pFmt(den)),
      mc: mcR(cor, [mk(null, A, B), mk([1, -t], A, B), mk([1, t], B, A), mk([1, t], -A, -B)], decF(cor), decEx(cor)),
      why: ['The numerator has the higher degree, so divide first: ' + m('(' + pFmt(num) + ') ÷ (' + pFmt(den) + ')') + ' gives the quotient ' + m(pFmt([1, t])) + ' and the remainder ' + m(pFmt(rem)) + '.',
        'Decompose the remainder: ' + eqSplit(K.frx(pFmt(rem), fpar(r) + fpar(s)), [K.frx(iv('A'), facH(lf(r))), K.frx(iv('B'), facH(lf(s)))]) + ', so ' + eqSplit(pFmt(rem), ['<i>A</i>' + fpar(s), '<i>B</i>' + fpar(r)]) + '.',
        m('<i>x</i> = ' + n(r)) + ' gives ' + m('<i>A</i> = ' + n(A)) + ', and ' + m('<i>x</i> = ' + n(s)) + ' gives ' + m('<i>B</i> = ' + n(B)) + '.',
        'The decomposition is ' + decF(cor)(cor) + '.'] }, { t: 'pfd', num: num, den: den });
  }
  // L3: repeated and distinct linear factors
  function g543c() {
    var r, s, A, B, Cc; do { r = ri(-4, 4); s = ri(-4, 4); A = rnz(-5, 5); B = rnz(-5, 5); Cc = rnz(-5, 5); } while (r === s || A === B || A === Cc);
    var den = pmul(pmul(lf(r), lf(r)), lf(s));
    var num = padd(padd(psc(pmul(lf(r), lf(s)), A), psc(lf(s), B)), psc(pmul(lf(r), lf(r)), Cc));
    var mk = function (a, b, c) { return dec(null, [[[a], lf(r), 1], [[b], lf(r), 2], [[c], lf(s), 1]]); }, cor = mk(A, B, Cc);
    return QQ({ q: 'Find the partial fraction decomposition.' + bigFrac(num, facProd([[lf(r), 2], [lf(s), 1]])),
      mc: mcR(cor, [mk(B, A, Cc), mk(A, B, -Cc), mk(Cc, B, A), mk(A, -B, Cc)], decF(cor), decEx(cor)),
      why: ['Write ' + m(K.frx(iv('A'), facH(lf(r)))) + ' ' + m('+ ' + K.frx(iv('B'), powH(lf(r), 2))) + ' ' + m('+ ' + K.frx(iv('C'), facH(lf(s)))) + ' and multiply: ' + eqSplit(pFmt(num), ['<i>A</i>' + fpar(r) + fpar(s), '<i>B</i>' + fpar(s), '<i>C</i>' + powH(lf(r), 2)]) + '.',
        m('<i>x</i> = ' + n(r)) + ': ' + m(n(pev(num, r)) + ' = ' + P([[r - s, '<i>B</i>']])) + ', so ' + m('<i>B</i> = ' + n(B)) + '. ' + m('<i>x</i> = ' + n(s)) + ': ' + m(n(pev(num, s)) + ' = ' + P([[(s - r) * (s - r), '<i>C</i>']])) + ', so ' + m('<i>C</i> = ' + n(Cc)) + '.',
        'Match the ' + m(X + '<sup>2</sup>') + '-coefficients: ' + m('<i>A</i> + <i>C</i> = ' + n(num[0])) + ', so ' + m('<i>A</i> = ' + n(A)) + '.',
        'The decomposition is ' + decF(cor)(cor) + '.'] }, { t: 'pfd', num: num, den: den });
  }
  K.lesson('5.4', { title: 'Partial Fractions', std: 'Lial 12e · Section 5.4', levels: [[g541a, g541b, g541c], [g542a, g542b, g542c], [g543a, g543b, g543c]] });

  /* ================= 5.5 Nonlinear Systems of Equations ================= */
  function sortPts(pts) { return pts.slice().sort(function (u, v) { var a = R(u[0]).sub(v[0]).val(); if (a !== 0) return a; return R(u[1]).sub(v[1]).val(); }); }   // increasing x, then y
  function fSet(pts) { if (!pts.length) return 'No real solutions'; var s = sortPts(pts).map(fPt); return s.length === 1 ? s[0] : s.length === 2 ? s[0] + ' and ' + s[1] : s.slice(0, -1).join(', ') + ', and ' + s[s.length - 1]; }
  function setEx(pts) { return function () { var u = pts.map(function (p) { return p.slice(); }), i = ri(0, u.length - 1); u[i] = [R(u[i][0]).add(rnz(-2, 2)), R(u[i][1]).add(rnz(-2, 2))]; return u; }; }
  var CPAIRS = (function () {
    var out = [];
    [5, 10, 13, 17, 20, 25].forEach(function (r2) {
      var L = [], x, y; for (x = -5; x <= 5; x++) for (y = -5; y <= 5; y++) if (x * x + y * y === r2) L.push([x, y]);
      L.forEach(function (p1) { L.forEach(function (p2) { if (p1[0] < p2[0]) { var mm = R(p2[1] - p1[1], p2[0] - p1[0]), b = R(p1[1]).sub(mm.mul(p1[0])); out.push({ r2: r2, p: [p1, p2], m: mm, b: b }); } }); });
    });
    return out;
  })();
  function circFns(r2) { var r = Math.sqrt(r2); return [{ f: function (x) { return Math.sqrt(Math.max(0, r2 - x * x)); }, from: -r, to: r, color: C.blue }, { f: function (x) { return -Math.sqrt(Math.max(0, r2 - x * x)); }, from: -r, to: r, color: C.blue }]; }
  function circEq(r2) { return m('<i>x</i><sup>2</sup> + <i>y</i><sup>2</sup> = ' + r2); }
  function swapPts(pts) { return pts.map(function (p) { return [p[1], p[0]]; }); }
  // parabola y = a(x − x1)(x − x2) + (mx + d) meeting the line y = mx + d at x1 and x2
  function parabLine() {
    var x1, x2, a, mm, d, B, Cq, hx, ky;
    do { x1 = ri(-4, 3); x2 = ri(x1 + 1, 4); a = pick([1, -1]); mm = ri(-2, 2); d = ri(-3, 3); B = -a * (x1 + x2) + mm; Cq = a * x1 * x2 + d; hx = -B / (2 * a); ky = a * hx * hx + B * hx + Cq; }
    while (Math.abs(mm * x1 + d) > 8 || Math.abs(mm * x2 + d) > 8 || Math.abs(ky) > 9 || Math.abs(hx) > 5);
    return { x1: x1, x2: x2, a: a, m: mm, d: d, B: B, C: Cq, pts: [[x1, mm * x1 + d], [x2, mm * x2 + d]] };
  }
  function parEq(o) { return m('<i>y</i> = ' + P([[o.a, K.xp(2)], [o.B, X], [o.C, '']])); }
  function parSy(o) { return ['y - (' + sy(o.a) + '*x**2 + ' + sy(o.B) + '*x + ' + sy(o.C) + ')', 'y - (' + sy(o.m) + '*x + ' + sy(o.d) + ')']; }
  // L1: read the solutions from a graph
  function g551a() {
    var pts, eqs, gr, chk, sy2;
    if (K.coin()) {
      var c = pick(CPAIRS.filter(function (o) { return o.m.d <= 2 && o.b.d === 1 && Math.abs(o.m.val()) <= 3; }));
      var W = Math.ceil(Math.sqrt(c.r2)) + 2; pts = c.p;
      eqs = [circEq(c.r2), yEq(c.m, c.b)];
      gr = K.plane({ x: [-W, W], y: [-W, W], fns: circFns(c.r2), lines: [{ m: c.m, b: c.b, color: C.red }], pts: pts.map(function (p) { return { x: p[0], y: p[1] }; }) });
      chk = m(sub(pts[0][0]) + '<sup>2</sup> + ' + sub(pts[0][1]) + '<sup>2</sup> = ' + c.r2);
      sy2 = ['x**2 + y**2 - ' + sy(c.r2), 'y - (' + sy(c.m) + '*x + ' + sy(c.b) + ')'];
    } else {
      var o = parabLine(); pts = o.pts; eqs = [parEq(o), yEq(o.m, o.d)];
      gr = K.plane({ x: [-6, 6], y: [-10, 10], fns: [{ f: function (x) { return o.a * x * x + o.B * x + o.C; }, color: C.blue }], lines: [{ m: o.m, b: o.d, color: C.red }], pts: pts.map(function (p) { return { x: p[0], y: p[1] }; }) });
      chk = m(n(pts[0][1]) + ' = ' + K.subst([[o.a, 2], [o.B, 1], [o.C, 0]], n(pts[0][0])));
      sy2 = parSy(o);
    }
    return QQ({ q: 'The graph shows the system below. What is the solution set of the system?' + sys(eqs), graph: gr,
      mc: mcR(pts, [swapPts(pts), [pts[0]], [pts[1]], pts.map(function (p) { return [-p[0], p[1]]; })], fSet, setEx(pts)),
      why: ['Each solution is a point where the two graphs intersect.', 'The graphs cross at ' + fSet(pts) + '.', 'Check ' + fPt(pts[0]) + ' in the first equation: ' + chk + ' ✓. It is on the line too.'] }, { t: 'nl', eqs: sy2 });
  }
  // L1: parabola and horizontal line
  function g551b() {
    var a = pick([1, -1, 2, -2]), s = ri(1, 4), c = ri(-8, 8), d = c + a * s * s;
    var pts = [[s, d], [-s, d]];
    return QQ({ q: 'Solve the system.' + sys([m('<i>y</i> = ' + P([[a, K.xp(2)], [c, '']])), m('<i>y</i> = ' + n(d))]),
      mc: mcR(pts, [[[s, d]], swapPts(pts), [[s * s, d], [-s * s, d]], [[s, -d], [-s, -d]]], fSet, function () { var t = s + rnz(-2, 2); if (t <= 0) t = s + 1; return [[t, d], [-t, d]]; }),
      why: ['Substitute ' + m('<i>y</i> = ' + n(d)) + ' into the first equation: ' + m(n(d) + ' = ' + P([[a, K.xp(2)], [c, '']])) + '.',
        'Then ' + m(P([[a, K.xp(2)]]) + ' = ' + n(d - c)) + ', so ' + m('<i>x</i><sup>2</sup> = ' + (s * s)) + ' and ' + m('<i>x</i> = ±' + s) + '. Do not forget the negative root.',
        'Both ' + X + '-values pair with ' + m('<i>y</i> = ' + n(d)) + ': ' + fSet(pts) + '.'] }, { t: 'nl', eqs: ['y - (' + sy(a) + '*x**2 + ' + sy(c) + ')', 'y - ' + sy(d)] });
  }
  // L1: number of real solutions
  function g551c() {
    var type = ri(1, 3), cnt, eqs, sy2, why;
    if (type <= 2) {
      var r = ri(2, 6), k = pick([ri(-r + 1, r - 1), r, -r, r + ri(1, 3), -r - ri(1, 3)]), vert = type === 2, v = vert ? X : Y;
      cnt = Math.abs(k) < r ? 2 : Math.abs(k) === r ? 1 : 0;
      eqs = [circEq(r * r), m(v + ' = ' + n(k))]; sy2 = ['x**2 + y**2 - ' + sy(r * r), (vert ? 'x' : 'y') + ' - ' + sy(k)];
      var o = vert ? Y : X;
      why = ['The circle has center (0, 0) and radius ' + r + ', so it reaches from ' + m(v + ' = ' + M + r) + ' to ' + m(v + ' = ' + r) + '.',
        'Substitute: ' + m(o + '<sup>2</sup> = ' + (r * r) + ' ' + M + ' ' + sub(k) + '<sup>2</sup> = ' + n(r * r - k * k)) + (cnt === 2 ? ', which has two real solutions.' : cnt === 1 ? ', so ' + m(o + ' = 0') + ' only: the line is tangent to the circle.' : ', which has no real solution: the line misses the circle.'),
        'So the system has ' + cnt + ' real solution' + (cnt === 1 ? '' : 's') + '.'];
    } else {
      var c = ri(-5, 5), kk = c + pick([ri(1, 6), 0, -ri(1, 6), ri(1, 6)]);
      cnt = kk > c ? 2 : kk === c ? 1 : 0;
      eqs = [m('<i>y</i> = ' + P([[1, K.xp(2)], [c, '']])), m('<i>y</i> = ' + n(kk))]; sy2 = ['y - (x**2 + ' + sy(c) + ')', 'y - ' + sy(kk)];
      why = ['The parabola opens up with vertex ' + K.pt(0, c) + ', so its lowest y-value is ' + n(c) + '.',
        'Substitute: ' + m('<i>x</i><sup>2</sup> = ' + n(kk) + ' ' + M + ' ' + sub(c) + ' = ' + n(kk - c)) + (cnt === 2 ? ', which has two real solutions.' : cnt === 1 ? ', so ' + m('<i>x</i> = 0') + ' only.' : ', which has no real solution.'),
        'So the system has ' + cnt + ' real solution' + (cnt === 1 ? '' : 's') + '.'];
    }
    return QQ({ q: 'How many real solutions does the system have?' + sys(eqs), mc: mcR(cnt, [0, 1, 2, 4].filter(function (v) { return v !== cnt; }), fNum), why: why }, { t: 'nlcount', eqs: sy2 });
  }
  // L2: line and circle by substitution
  function g552a() {
    var c = pick(CPAIRS.filter(function (o) { return o.m.d === 1 && o.b.d === 1 && o.m.n !== 0 && Math.abs(o.m.val()) <= 3 && Math.abs(o.b.val()) <= 7; }));
    var mm = c.m.val(), b = c.b.val(), pts = c.p, x1 = pts[0][0], x2 = pts[1][0];
    var A2 = 1 + mm * mm, B2 = 2 * mm * b, C2 = b * b - c.r2, g = K.gcd(K.gcd(A2, B2), C2), L = A2 / g;
    return QQ({ q: 'Solve the system.' + sys([circEq(c.r2), yEq(mm, b)]),
      mc: mcR(pts, [swapPts(pts), pts.map(function (p) { return [p[0], -p[1]]; }), [pts[0]], pts.map(function (p) { return [-p[0], -p[1]]; })], fSet, setEx(pts)),
      why: ['Substitute ' + m('<i>y</i> = ' + P([[mm, X], [b, '']])) + ' into the circle: ' + m('<i>x</i><sup>2</sup> + (' + P([[mm, X], [b, '']]) + ')<sup>2</sup> = ' + c.r2) + '.',
        'Expand and simplify: ' + m(P([[A2 / g, K.xp(2)], [B2 / g, X], [C2 / g, '']]) + ' = 0') + '.',
        'Factor: ' + m((L === 1 ? '' : n(L)) + fpar(x1) + fpar(x2) + ' = 0') + ', so ' + m('<i>x</i> = ' + n(x1)) + ' or ' + m('<i>x</i> = ' + n(x2)) + '.',
        'The line gives ' + m('<i>y</i> = ' + n(pts[0][1])) + ' and ' + m('<i>y</i> = ' + n(pts[1][1])) + '. The solutions are ' + fSet(pts) + '.'] },
      { t: 'nl', eqs: ['x**2 + y**2 - ' + sy(c.r2), 'y - (' + sy(mm) + '*x + ' + sy(b) + ')'] });
  }
  // L2: eliminate the squared terms
  function g552b() {
    var x0 = ri(1, 4), y0, a1, b1, a2, b2;
    do { y0 = ri(1, 4); a1 = ri(1, 3); b1 = ri(1, 3); a2 = ri(1, 2); b2 = pick([-1, -2, -3, 1, 2]); } while (a1 * b2 - a2 * b1 === 0 || x0 === y0);
    var X0 = x0 * x0, Y0 = y0 * y0, c1 = a1 * X0 + b1 * Y0, c2 = a2 * X0 + b2 * Y0;
    var pts = [[x0, y0], [x0, -y0], [-x0, y0], [-x0, -y0]];
    var Lc = K.lcm(Math.abs(b1), Math.abs(b2)), k1 = Lc / b1, k2 = -Lc / b2, cx = a1 * k1 + a2 * k2, cc = c1 * k1 + c2 * k2;
    var sq = function (c, v) { return [c, '<i>' + v + '</i><sup>2</sup>']; };
    return QQ({ q: 'Solve the system.' + sys([m(P([sq(a1, 'x'), sq(b1, 'y')]) + ' = ' + c1), m(P([sq(a2, 'x'), sq(b2, 'y')]) + ' = ' + n(c2))]),
      mc: mcR(pts, [[[x0, y0]], swapPts(pts), [[x0, y0], [-x0, -y0]], [[X0, Y0], [X0, -Y0], [-X0, Y0], [-X0, -Y0]]], fSet, function () { var t = y0 + ri(1, 2); return [[x0, t], [x0, -t], [-x0, t], [-x0, -t]]; }),
      why: [(k1 === 1 && k2 === 1 ? 'Add the equations' : k1 === 1 && k2 === -1 ? 'Subtract the second equation from the first' : k1 === -1 && k2 === 1 ? 'Subtract the first equation from the second' : k2 === 1 ? 'Multiply the first equation by ' + n(k1) + ', then add the second equation' : k1 === 1 ? 'Multiply the second equation by ' + n(k2) + ', then add the first equation' : 'Multiply the first equation by ' + n(k1) + ' and the second by ' + n(k2) + ', then add') + ' to eliminate ' + m('<i>y</i><sup>2</sup>') + ': ' + m(P([sq(cx, 'x')]) + ' = ' + n(cc)) + '.',
        'So ' + m('<i>x</i><sup>2</sup> = ' + X0) + ' and ' + m('<i>x</i> = ±' + x0) + '. Substitute into the first equation: ' + m(n(a1 * X0) + ' + ' + P([sq(b1, 'y')]) + ' = ' + c1) + ', so ' + m('<i>y</i><sup>2</sup> = ' + Y0) + ' and ' + m('<i>y</i> = ±' + y0) + '.',
        'Only squares appear, so every combination of signs works: ' + fSet(pts) + '.'] },
      { t: 'nl', eqs: [sy(a1) + '*x**2 + ' + sy(b1) + '*y**2 - ' + sy(c1), sy(a2) + '*x**2 + ' + sy(b2) + '*y**2 - ' + sy(c2)] });
  }
  // L2: parabola and line by substitution
  function g552c() {
    var o = parabLine(), pts = o.pts;
    return QQ({ q: 'Solve the system.' + sys([parEq(o), yEq(o.m, o.d)]),
      mc: mcR(pts, [swapPts(pts), pts.map(function (p) { return [-p[0], p[1]]; }), [pts[1]], pts.map(function (p) { return [-p[0], -p[1]]; })], fSet, setEx(pts)),
      why: ['Set the expressions for ' + Y + ' equal: ' + m(P([[o.a, K.xp(2)], [o.B, X], [o.C, '']]) + ' = ' + P([[o.m, X], [o.d, '']])) + '.',
        'Collect terms: ' + m(P([[o.a, K.xp(2)], [o.B - o.m, X], [o.C - o.d, '']]) + ' = 0') + ', which factors as ' + m((o.a === -1 ? M : '') + fpar(o.x1) + fpar(o.x2) + ' = 0') + '. So ' + m('<i>x</i> = ' + n(o.x1)) + ' or ' + m('<i>x</i> = ' + n(o.x2)) + '.',
        'Use the line to find ' + Y + ': ' + m('<i>y</i> = ' + n(pts[0][1])) + ' and ' + m('<i>y</i> = ' + n(pts[1][1])) + '. The solutions are ' + fSet(pts) + '.'] }, { t: 'nl', eqs: parSy(o) });
  }
  // L3: xy = k with a line
  function g553a() {
    var x1, y1, sum = K.coin(), k, pts, eq2, sy2, why;
    do { x1 = rnz(-6, 6); y1 = rnz(-6, 6); } while (Math.abs(x1) === Math.abs(y1));
    k = x1 * y1;
    if (sum) {
      var s = x1 + y1; pts = [[x1, y1], [y1, x1]]; eq2 = m(P([[1, X], [1, Y]]) + ' = ' + n(s)); sy2 = 'x + y - ' + sy(s);
      why = ['Solve the line for ' + Y + ': ' + m('<i>y</i> = ' + P([[-1, X], [s, '']])) + '.', 'Substitute: ' + m('<i>x</i>(' + P([[-1, X], [s, '']]) + ') = ' + n(k)) + ', so ' + m(P([[1, K.xp(2)], [-s, X], [k, '']]) + ' = 0') + ' and ' + m(fpar(x1) + fpar(y1) + ' = 0') + '.', 'So ' + m('<i>x</i> = ' + n(x1)) + ' or ' + m('<i>x</i> = ' + n(y1)) + ', giving ' + fSet(pts) + '.'];
    } else {
      var d = x1 - y1; pts = [[x1, y1], [-y1, -x1]]; eq2 = m(P([[1, X], [-1, Y]]) + ' = ' + n(d)); sy2 = 'x - y - ' + sy(d);
      why = ['Solve the line for ' + Y + ': ' + m('<i>y</i> = ' + P([[1, X], [-d, '']])) + '.', 'Substitute: ' + m('<i>x</i>(' + P([[1, X], [-d, '']]) + ') = ' + n(k)) + ', so ' + m(P([[1, K.xp(2)], [-d, X], [-k, '']]) + ' = 0') + ' and ' + m(fpar(x1) + fpar(-y1) + ' = 0') + '.', 'So ' + m('<i>x</i> = ' + n(x1)) + ' or ' + m('<i>x</i> = ' + n(-y1)) + '; then ' + m('<i>y</i> = <i>x</i> ' + M + ' ' + sub(d)) + ' gives ' + fSet(pts) + '.'];
    }
    return QQ({ q: 'Solve the system.' + sys([m('<i>xy</i> = ' + n(k)), eq2]),
      mc: mcR(pts, [pts.map(function (p) { return [-p[0], -p[1]]; }), [pts[0]], sum ? [[x1, y1], [-y1, -x1]] : [[x1, y1], [y1, x1]], swapPts(pts).map(function (p) { return [p[0], -p[1]]; })], fSet, setEx(pts)), why: why },
      { t: 'nl', eqs: ['x*y - ' + sy(k), sy2] });
  }
  // L3: rectangle word problem
  var TRIPLES = [[3, 4, 5], [6, 8, 10], [5, 12, 13], [8, 15, 17], [9, 12, 15], [7, 24, 25], [12, 16, 20], [20, 21, 29]];
  function g553b() {
    var kind = K.coin() ? 'area' : 'diag', L, W, P2, Ar, D, ctx, u, why, q;
    var Lv = iv('L'), Wv = iv('W');
    if (kind === 'area') {
      do { W = ri(2, 12); L = ri(W + 1, 20); } while (L * W > 200);
      Ar = L * W; P2 = 2 * (L + W); ctx = pick([['garden', 'ft'], ['patio', 'ft'], ['rug', 'ft']]); u = ctx[1];
      q = 'A rectangular ' + ctx[0] + ' has an area of ' + Ar + ' square ' + (u === 'ft' ? 'feet' : 'meters') + ' and a perimeter of ' + P2 + ' ' + (u === 'ft' ? 'feet' : 'meters') + '. What are its dimensions?';
      why = ['Let ' + Lv + ' and ' + Wv + ' be the length and width: ' + m(Lv + Wv + ' = ' + Ar) + ' and ' + m('2' + Lv + ' + 2' + Wv + ' = ' + P2) + ', so ' + m(Lv + ' + ' + Wv + ' = ' + (L + W)) + '.',
        'Substitute ' + m(Wv + ' = ' + (L + W) + ' ' + M + ' ' + Lv) + ': ' + m(Lv + '(' + (L + W) + ' ' + M + ' ' + Lv + ') = ' + Ar) + ', so ' + m(Lv + '<sup>2</sup> ' + M + ' ' + (L + W) + Lv + ' + ' + Ar + ' = 0') + '.',
        'Factor: ' + m('(' + Lv + ' ' + M + ' ' + L + ')(' + Lv + ' ' + M + ' ' + W + ') = 0') + '. The ' + ctx[0] + ' is ' + L + ' ' + u + ' by ' + W + ' ' + u + '.'];
    } else {
      var t = pick(TRIPLES); L = t[1]; W = t[0]; D = t[2]; P2 = 2 * (L + W); ctx = pick([['TV screen', 'in.'], ['window', 'in.'], ['garden', 'ft']]); u = ctx[1];
      var unit = u === 'ft' ? 'feet' : 'inches', S = L + W;
      q = 'A rectangular ' + ctx[0] + ' has a diagonal of ' + D + ' ' + unit + ' and a perimeter of ' + P2 + ' ' + unit + '. What are its dimensions?';
      why = ['Let ' + Lv + ' and ' + Wv + ' be the length and width: ' + m(Lv + '<sup>2</sup> + ' + Wv + '<sup>2</sup> = ' + D + '<sup>2</sup>') + ' (Pythagorean theorem) and ' + m(Lv + ' + ' + Wv + ' = ' + S) + '.',
        'Substitute ' + m(Wv + ' = ' + S + ' ' + M + ' ' + Lv) + ': ' + m(Lv + '<sup>2</sup> + (' + S + ' ' + M + ' ' + Lv + ')<sup>2</sup> = ' + (D * D)) + ', which simplifies to ' + m(Lv + '<sup>2</sup> ' + M + ' ' + S + Lv + ' + ' + (L * W) + ' = 0') + '.',
        'Factor: ' + m('(' + Lv + ' ' + M + ' ' + L + ')(' + Lv + ' ' + M + ' ' + W + ') = 0') + '. The ' + ctx[0] + ' is ' + L + ' ' + u + ' by ' + W + ' ' + u + '.'];
    }
    var fmt = function (r) { return rh(r[0]) + ' ' + u + ' by ' + rh(r[1]) + ' ' + u; };
    var w = kind === 'area' ? [[L + 1, W - 1], [L - 1, W + 1], [L + 2, W - 2], [L + 3, W - 3]] : [[L + 1, W - 1], [L - 1, W + 1], [D, P2 / 2 - D], [L + 2, W - 2]];
    w = w.filter(function (r) { return r[0] > 0 && r[1] > 0 && R(r[0]).val() >= R(r[1]).val(); });
    return QQ({ q: q, mc: mcR([L, W], w, fmt, function (i) { var dd, ee; do { dd = rnz(-3, 3); ee = i > 6 ? ri(-2, 2) : -dd; } while (W + ee <= 0 || L + dd < W + ee); return [L + dd, W + ee]; }), why: why }, { t: 'rect', kind: kind, A: Ar, P: P2, D: D });
  }
  // L3: circle and parabola
  function g553c() {
    var x0, y0, B, A, s, y1, rt;
    do { x0 = ri(1, 4); y0 = ri(-3, 4); B = x0 * x0 - y0; A = x0 * x0 + y0 * y0; s = x0 * x0 - 2 * y0 - 1; y1 = -1 - y0; rt = Math.round(Math.sqrt(Math.max(s, 0))); } while (B === 0 || A > 40 || (s > 0 && rt * rt !== s) || (s > 0 && rt === x0 && y1 === y0));
    var pts = [[x0, y0], [-x0, y0]];
    if (s > 0) pts = pts.concat([[rt, y1], [-rt, y1]]); else if (s === 0) pts.push([0, y1]);
    var w = s >= 0 ? [[[x0, y0], [-x0, y0]], pts.map(function (p) { return [p[0], -p[1]]; }), swapPts(pts)] : [[[x0, y0], [-x0, y0], [0, y1]], [[x0, y0]], swapPts(pts), [[x0, -y0], [-x0, -y0]]];
    var Yv = '<i>y</i>';
    return QQ({ q: 'Solve the system.' + sys([circEq(A), m('<i>y</i> = ' + P([[1, K.xp(2)], [-B, '']]))]),
      mc: mcR(pts, w, fSet, setEx(pts)),
      why: ['The second equation gives ' + m('<i>x</i><sup>2</sup> = ' + P([[1, Yv], [B, '']])) + '. Substitute into the first: ' + m(P([[1, Yv], [B, '']]) + ' + <i>y</i><sup>2</sup> = ' + A) + ', so ' + m(P([[1, '<i>y</i><sup>2</sup>'], [1, Yv], [B - A, '']]) + ' = 0') + '.',
        'Factor: ' + m('(' + K.minusH(Yv, y0) + ')(' + K.minusH(Yv, y1) + ') = 0') + ', so ' + m('<i>y</i> = ' + n(y0)) + ' or ' + m('<i>y</i> = ' + n(y1)) + '.',
        m('<i>y</i> = ' + n(y0)) + ': ' + m('<i>x</i><sup>2</sup> = ' + (x0 * x0)) + ', so ' + m('<i>x</i> = ±' + x0) + '. ' + m('<i>y</i> = ' + n(y1)) + ': ' + m('<i>x</i><sup>2</sup> = ' + n(s)) + (s > 0 ? ', so ' + m('<i>x</i> = ±' + rt) + '.' : s === 0 ? ', so ' + m('<i>x</i> = 0') + '.' : ', which has no real solution.'),
        'The solution set is ' + fSet(pts) + '.'] }, { t: 'nl', eqs: ['x**2 + y**2 - ' + sy(A), 'y - (x**2 - ' + sy(B) + ')'] });
  }
  K.lesson('5.5', { title: 'Nonlinear Systems of Equations', std: 'Lial 12e · Section 5.5', levels: [[g551a, g551b, g551c], [g552a, g552b, g552c], [g553a, g553b, g553c]] });

  /* ================= 5.6 Systems of Inequalities and Linear Programming ================= */
  function holds(lhs, op, rhs) { var s = R(lhs).sub(rhs).n; return op === '<' ? s < 0 : op === '<=' ? s <= 0 : op === '>' ? s > 0 : s >= 0; }
  function sat(I, x, y) { return holds(R(I[0]).mul(x).add(R(I[1]).mul(y)), I[2], I[3]); }
  function iy(mm, b, op) { return m(Y + ' ' + SYM[op] + ' ' + P([[mm, X], [b, '']])); }
  function istd(I) { return m(P([[I[0], X], [I[1], Y]]) + ' ' + SYM[I[2]] + ' ' + rh(I[3])); }
  function shadeOf(I) { var a = R(I[0]).val(), b = R(I[1]).val(), c = R(I[3]).val(); return (I[2] === '<' || I[2] === '<=') ? { a: a, b: b, c: c } : { a: -a, b: -b, c: -c }; }
  function lineOf(I) { var a = R(I[0]), b = R(I[1]), c = R(I[3]); return b.n === 0 ? { vx: c.div(a).val() } : { m: a.neg().div(b), b: c.div(b) }; }
  function red3(a, b, c) { var g = K.gcd(K.gcd(a, b), c); return [a / g, b / g, c / g]; }
  // feasible region with corners (0,0), (X2,0), (px,py), (0,Y1)
  function region4() {
    var px, py, Y1, X2;
    do { px = ri(1, 6); py = ri(1, 6); Y1 = ri(py + 1, 10); X2 = ri(px + 1, 10); } while (!((py - Y1) * (X2 - px) > -py * px));
    var l1 = red3(Y1 - py, px, px * Y1), l2 = red3(py, X2 - px, py * X2);
    var cons = [[l1[0], l1[1], '<=', l1[2]], [l2[0], l2[1], '<=', l2[2]], [1, 0, '>=', 0], [0, 1, '>=', 0]];
    return { c: [[0, 0], [X2, 0], [px, py], [0, Y1]], cons: cons, X2: X2, Y1: Y1, px: px, py: py };
  }
  function lpGraph(rg, labels) {
    return K.plane({ x: [-1, rg.X2 + 1], y: [-1, rg.Y1 + 1], lines: [Object.assign(lineOf(rg.cons[0]), { color: C.blue }), Object.assign(lineOf(rg.cons[1]), { color: C.red })],
      shade: [{ parts: rg.cons.map(shadeOf) }], pts: rg.c.map(function (p) { return labels ? { x: p[0], y: p[1], label: '(' + p[0] + ', ' + p[1] + ')' } : { x: p[0], y: p[1] }; }) });
  }
  function objVals(cs, o) { return cs.map(function (p) { return o[0] * p[0] + o[1] * p[1]; }); }
  function uniqObj(cs, lo, hi, mixed) {
    var o, v;
    do { o = mixed ? [rnz(lo, hi), rnz(lo, hi)] : [ri(1, hi), ri(1, hi)]; v = objVals(cs, o); } while (new Set(v).size !== v.length);
    return o;
  }
  function fOpt(r) { return rh(r[0]) + ' at ' + K.pt(r[1], r[2]); }
  function lpChoices(cs, o, goal) {
    var v = objVals(cs, o), bi = 0; v.forEach(function (x, i) { if (goal === 'max' ? x > v[bi] : x < v[bi]) bi = i; });
    var cor = [v[bi], cs[bi][0], cs[bi][1]], w = cs.map(function (p, i) { return [v[i], p[0], p[1]]; }).filter(function (_, i) { return i !== bi; });
    return { cor: cor, w: w, v: v, bi: bi };
  }
  function objH(name, o) { return m(iv(name) + ' = ' + P([[o[0], X], [o[1], Y]])); }
  function valList(name, cs, v) { return cs.map(function (p, i) { return m(iv(name) + K.pt(p[0], p[1]) + ' = ' + n(v[i])); }).join(', '); }
  // L1: which point satisfies a system of inequalities
  function g561a() {
    var I1, I2, good, bad1, bad2, edge, x, y;
    do {
      var mm = pick([1, 2, -1, -2, R(1, 2), R(-1, 2)]), b = ri(-3, 3), op1 = pick(['<', '<=', '>', '>=']);
      I1 = [R(mm).neg(), 1, op1, b];
      var a2 = rnz(-3, 3), b2 = rnz(-3, 3); I2 = [a2, b2, pick(['<', '<=', '>', '>=']), ri(-6, 6)];
      good = []; bad1 = []; bad2 = []; edge = [];
      for (x = -5; x <= 5; x++) for (y = -5; y <= 5; y++) {
        var s1 = sat(I1, x, y), s2 = sat(I2, x, y);
        if (s1 && s2) good.push([x, y]); else if (s1) bad2.push([x, y]); else if (s2) bad1.push([x, y]);
        if (!s1 && (I1[2] === '<' || I1[2] === '>') && R(I1[0]).mul(x).add(y).eq(I1[3]) && s2) edge.push([x, y]);
      }
    } while (good.length < 3 || bad1.length < 2 || bad2.length < 2);
    var cor = pick(good), w = [edge.length ? pick(edge) : pick(bad1), pick(bad2), pick(bad1)];
    var tst = function (I, p) { var lhs = R(I[0]).mul(p[0]).add(R(I[1]).mul(p[1])); return m(K.lin([[I[0], n(p[0])], [I[1], n(p[1])]]) + ' = ' + rh(lhs)) + ', and ' + m(rh(lhs) + ' ' + SYM[I[2]] + ' ' + rh(I[3])) + ' is ' + (sat(I, p[0], p[1]) ? 'true' : 'false'); };
    var mm1 = R(I1[0]).neg();
    var e1 = iy(mm1, I1[3], I1[2]);
    var b0 = w[0], f1 = !sat(I1, b0[0], b0[1]);
    return QQ({ q: 'Which point is a solution of the system?' + sys([e1, istd(I2)]), mc: mcR(cor, w, fPt, function () { return pick(bad1.concat(bad2)); }),
      why: ['A solution must make both inequalities true.',
        'For ' + fPt(cor) + ': in the first, the right side is ' + m(K.lin([[mm1, n(cor[0])]]) + K.plusK(I1[3]) + ' = ' + rh(mm1.mul(cor[0]).add(I1[3]))) + ', and ' + m(n(cor[1]) + ' ' + SYM[I1[2]] + ' ' + rh(mm1.mul(cor[0]).add(I1[3]))) + ' is true; in the second, ' + tst(I2, cor) + '.',
        'Each other point fails at least one inequality. For example, ' + fPt(b0) + (f1 ? ' gives ' + m(n(b0[1]) + ' ' + SYM[I1[2]] + ' ' + rh(mm1.mul(b0[0]).add(I1[3]))) + ' in the first inequality, which is false.' : ' fails the second: ' + tst(I2, b0) + '.')] },
      { t: 'ineqpt', ineqs: [I1, I2] });
  }
  // L1: which inequality is graphed
  function g561b() {
    var mm = pick([R(1), R(2), R(-1), R(-2), R(1, 2), R(-1, 2), R(3), R(-3), R(2, 3), R(-2, 3)]), b = ri(-3, 3), op = pick(['<', '<=', '>', '>=']);
    var I = [mm.neg(), 1, op, b], dash = op === '<' || op === '>', above = op === '>' || op === '>=';
    var gr = K.plane({ x: [-6, 6], y: [-6, 6], lines: [{ m: mm, b: b, dash: dash }], shade: [shadeOf(I)] });
    var sh = shadeOf(I);
    return QQ({ q: 'Which inequality does the graph show?', graph: gr,
      mc: mcR([mm, b, op], ['<', '<=', '>', '>='].filter(function (o) { return o !== op; }).map(function (o) { return [mm, b, o]; }), function (r) { return iy(r[0], r[1], r[2]); }),
      why: ['The boundary line has y-intercept ' + n(b) + ' and slope ' + rh(mm) + ': ' + yEq(mm, b) + '.',
        dash ? 'The line is dashed, so points on it are not included: use &lt; or &gt;.' : 'The line is solid, so points on it are included: use ≤ or ≥.',
        'The shading is ' + (above ? 'above' : 'below') + ' the line, where ' + Y + ' is ' + (above ? 'greater' : 'less') + ': ' + iy(mm, b, op) + '.'] },
      { t: 'ineqg', shade: [sh.a, sh.b, sh.c], dash: dash });
  }
  // L1: evaluate the objective at listed corners
  function g561c() {
    var rg = region4(), goal = K.coin() ? 'max' : 'min', o = uniqObj(rg.c, -4, 9, goal === 'min'), nm = goal === 'max' ? 'P' : 'C';
    var L = lpChoices(rg.c, o, goal), cs = K.shuffle(rg.c);
    return QQ({ q: 'A feasible region has corner points ' + cs.map(function (p) { return K.pt(p[0], p[1]); }).join(', ') + '. Find the ' + (goal === 'max' ? 'maximum' : 'minimum') + ' value of ' + objH(nm, o) + ' and where it occurs.',
      mc: mcR(L.cor, L.w, fOpt), why: ['Evaluate ' + iv(nm) + ' at every corner: ' + valList(nm, rg.c, L.v) + '.', 'The ' + (goal === 'max' ? 'largest' : 'smallest') + ' value is ' + n(L.cor[0]) + ', at ' + K.pt(L.cor[1], L.cor[2]) + '.'] },
      { t: 'lpc', corners: rg.c, obj: o, goal: goal });
  }
  // L2: graph with labeled corners, optimize
  function g562a() {
    var rg = region4(), o = uniqObj(rg.c, 1, 8, false), L = lpChoices(rg.c, o, 'max');
    return QQ({ q: 'The shaded region is the feasible region for the constraints below. Find the maximum value of ' + objH('P', o) + '.' + sys(rg.cons.map(istd)), graph: lpGraph(rg, true),
      mc: mcR(L.cor, L.w, fOpt),
      why: ['The maximum of a linear objective occurs at a corner of the feasible region. The corners are ' + rg.c.map(function (p) { return K.pt(p[0], p[1]); }).join(', ') + '.', 'Evaluate: ' + valList('P', rg.c, L.v) + '.', 'The maximum is ' + n(L.cor[0]) + ', at ' + K.pt(L.cor[1], L.cor[2]) + '.'] },
      { t: 'lp', cons: rg.cons, obj: o, goal: 'max' });
  }
  // L2: which point is a corner point
  function g562b() {
    var rg = region4(), l1 = rg.cons[0], l2 = rg.cons[1];
    var cor = pick(rg.c.slice(1));
    var xi1 = R(l1[3], l1[0]), yi2 = R(l2[3], l2[1]);
    var w = [[xi1, 0], [0, yi2]];
    if (rg.X2 >= 2) w.push([Math.floor(rg.X2 / 2), 0]); else w.push([0, Math.floor(rg.Y1 / 2)]);
    var inner = null, x, y; for (x = 1; x <= 3 && !inner; x++) for (y = 1; y <= 3 && !inner; y++) if (rg.cons.every(function (I) { return sat(I, x, y) && !R(I[0]).mul(x).add(R(I[1]).mul(y)).eq(I[3]); })) inner = [x, y];
    if (inner) w.push(inner);
    var why2 = cor[0] === rg.px && cor[1] === rg.py ? 'Solve the boundary equations ' + m(P([[l1[0], X], [l1[1], Y]]) + ' = ' + l1[3]) + ' and ' + m(P([[l2[0], X], [l2[1], Y]]) + ' = ' + l2[3]) + ' together: ' + K.pt(cor[0], cor[1]) + '. It satisfies ' + m('<i>x</i> ≥ 0') + ' and ' + m('<i>y</i> ≥ 0') + ', so it is a corner.' :
      K.pt(cor[0], cor[1]) + ' lies on the boundary ' + (cor[1] === 0 ? m('<i>y</i> = 0') : m('<i>x</i> = 0')) + ' and on the boundary line ' + (cor[1] === 0 ? m(P([[l2[0], X], [l2[1], Y]]) + ' = ' + l2[3]) : m(P([[l1[0], X], [l1[1], Y]]) + ' = ' + l1[3])) + ', and it satisfies every constraint, so it is a corner.';
    return QQ({ q: 'The constraints of a linear programming problem are listed below. Which point is a corner point of the feasible region?' + sys(rg.cons.map(istd)),
      mc: mcR(cor, w, fPt), why: ['A corner point is a point where two boundary lines meet and every constraint is still satisfied.', why2,
        'Each other choice either breaks a constraint (for example, ' + fPt([xi1, 0]) + ' gives ' + m(P([[l2[0], X], [l2[1], Y]])) + ' = ' + rh(xi1.mul(l2[0])) + ', more than ' + l2[3] + ') or lies along an edge or inside the region rather than at a corner.'] },
      { t: 'corner', cons: rg.cons });
  }
  // L2: which system describes the shaded region
  function g562c() {
    var x0 = ri(-2, 2), y0 = ri(-2, 2), L1, L2, g = 0;
    var lt = function () { for (var t = 0; t < 80; t++) { var mm = pick([R(1), R(2), R(-1), R(-2), R(1, 2), R(-1, 2), R(3), R(-3)]), b = mm.mul(-x0).add(y0); if (b.isInt() && Math.abs(b.val()) <= 5) return [mm, b]; } return [R(1), R(y0 - x0)]; };
    L1 = lt(); do { L2 = lt(); } while (L2[0].eq(L1[0]) && g++ < 50);
    if (L2[0].eq(L1[0])) return g562c();
    var o1 = pick(['<=', '>=']), o2 = pick(['<=', '>=']);
    var I1 = [L1[0].neg(), 1, o1, L1[1]], I2 = [L2[0].neg(), 1, o2, L2[1]];
    var tp = null, x, y; for (x = -5; x <= 5 && !tp; x++) for (y = -5; y <= 5 && !tp; y++) if (sat([I1[0], 1, o1 === '<=' ? '<' : '>', I1[3]], x, y) && sat([I2[0], 1, o2 === '<=' ? '<' : '>', I2[3]], x, y)) tp = [x, y];
    if (!tp) return g562c();
    var gr = K.plane({ x: [-6, 6], y: [-6, 6], lines: [{ m: L1[0], b: L1[1], color: C.blue }, { m: L2[0], b: L2[1], color: C.red }], shade: [{ parts: [shadeOf(I1), shadeOf(I2)] }] });
    var fl = function (o) { return o === '<=' ? '>=' : '<='; };
    var fmt = function (r) { return iy(r[0][0], r[0][1], r[0][2]) + '<br>' + iy(r[1][0], r[1][1], r[1][2]); };
    var mk = function (a, b) { return [[L1[0], L1[1], a], [L2[0], L2[1], b]]; };
    var ab = function (o) { return o === '>=' ? 'above' : 'below'; };
    return QQ({ q: 'Which system of inequalities has the shaded region as its solution? (Blue and red are the two boundary lines.)', graph: gr,
      mc: mcR(mk(o1, o2), [mk(fl(o1), o2), mk(o1, fl(o2)), mk(fl(o1), fl(o2))], fmt),
      why: ['The boundary lines are ' + yEq(L1[0], L1[1]) + ' (blue) and ' + yEq(L2[0], L2[1]) + ' (red). Both are solid, so use ≤ or ≥.',
        'The region is ' + ab(o1) + ' the blue line and ' + ab(o2) + ' the red line.',
        'Check the point ' + fPt(tp) + ' from the region: it makes ' + iy(L1[0], L1[1], o1) + ' and ' + iy(L2[0], L2[1], o2) + ' both true.'] },
      { t: 'ineqsys', shade: [shadeOf(I1), shadeOf(I2)].map(function (s) { return [s.a, s.b, s.c]; }) });
  }
  // L3: maximize profit (word problem)
  var LPC = [{ who: 'A furniture shop', v: 'make', vs: 'makes', x: ['table', 'tables'], y: ['chair', 'chairs'], res: 'labor', u: 'pieces', per: 'week', pro: 'it' },
    { who: 'A bakery', v: 'bake', vs: 'bakes', x: ['cake', 'cakes'], y: ['pie', 'pies'], res: 'oven', u: 'items', per: 'day', pro: 'it' },
    { who: 'A tutor', v: 'teach', vs: 'teaches', x: ['group lesson', 'group lessons'], y: ['private lesson', 'private lessons'], res: 'teaching', u: 'lessons', per: 'week', pro: 'she' }];
  function g563a() {
    var c = pick(LPC), px, py, T, a, b, H, cs, o, v;
    do { px = ri(1, 8); py = ri(1, 8); T = px + py; a = ri(2, 4); b = ri(1, a - 1); H = a * px + b * py; } while (H % a !== 0 || H / a >= T || H / b <= T);
    cs = [[0, 0], [H / a, 0], [px, py], [0, T]];
    do { o = [5 * ri(4, 18), 5 * ri(3, 14)]; v = objVals(cs, o); } while (new Set(v).size !== 4);
    var L = lpChoices(cs, o, 'max');
    var fmt = function (r) { return pl(R(r[1]).val(), c.x[0], c.x[1]) + ' and ' + pl(R(r[2]).val(), c.y[0], c.y[1]) + ' ($' + R(r[0]).val() + ')'; };
    var w = L.w.slice(); var ex = [px - 1, py + 1]; if (ex[0] >= 0 && ex[0] + ex[1] <= T && a * ex[0] + b * ex[1] <= H) w.push([o[0] * ex[0] + o[1] * ex[1], ex[0], ex[1]]);
    var Pro = c.pro.charAt(0).toUpperCase() + c.pro.slice(1);
    return QQ({ q: c.who + ' ' + c.vs + ' ' + c.x[1] + ' and ' + c.y[1] + '. ' + Pro + ' can ' + c.v + ' at most ' + T + ' ' + c.u + ' a ' + c.per + ' in all. Each ' + c.x[0] + ' takes ' + a + ' hours of ' + c.res + ' time and each ' + c.y[0] + ' takes ' + pl(b, 'hour', 'hours') + ', and ' + H + ' hours of ' + c.res + ' time are available each ' + c.per + '. Each ' + c.x[0] + ' earns $' + o[0] + ' and each ' + c.y[0] + ' earns $' + o[1] + '. How many of each should ' + c.pro + ' ' + c.v + ' each ' + c.per + ' to earn the most?',
      mc: mcR(L.cor, w, fmt),
      why: ['Let ' + X + ' = number of ' + c.x[1] + ' and ' + Y + ' = number of ' + c.y[1] + '. Maximize ' + objH('P', o) + ' subject to ' + m('<i>x</i> + <i>y</i> ≤ ' + T) + ', ' + m(P([[a, X], [b, Y]]) + ' ≤ ' + H) + ', ' + m('<i>x</i> ≥ 0') + ', ' + m('<i>y</i> ≥ 0') + '.',
        'The corners are ' + cs.map(function (p) { return K.pt(p[0], p[1]); }).join(', ') + '; the corner ' + K.pt(px, py) + ' solves ' + m('<i>x</i> + <i>y</i> = ' + T) + ' and ' + m(P([[a, X], [b, Y]]) + ' = ' + H) + ' together.',
        'Earnings at each corner: ' + valList('P', cs, L.v) + '.',
        'The maximum is $' + L.cor[0] + ', with ' + pl(L.cor[1], c.x[0], c.x[1]) + ' and ' + pl(L.cor[2], c.y[0], c.y[1]) + '.'] },
      { t: 'lp', cons: [[1, 1, '<=', T], [a, b, '<=', H], [1, 0, '>=', 0], [0, 1, '>=', 0]], obj: o, goal: 'max' });
  }
  // L3: minimize cost (unbounded region)
  var LPM = [['A farmer mixes two feeds', 'Feed X', 'Feed Y', 'bags', 'bag', 'protein', 'fiber'], ['A nutritionist combines two supplements', 'Brand X', 'Brand Y', 'tablets', 'tablet', 'vitamin A', 'vitamin C']];
  function g563b() {
    var c = pick(LPM), a1, b1, a2, b2, px, py, c1, c2, cs, o, v;
    do { a1 = ri(2, 5); b1 = ri(1, 2); a2 = ri(1, 2); b2 = ri(2, 5); px = ri(1, 6); py = ri(1, 6); c1 = a1 * px + b1 * py; c2 = a2 * px + b2 * py; }
    while (a1 * b2 <= a2 * b1 || c1 % b1 !== 0 || c2 % a2 !== 0);
    cs = [[0, c1 / b1], [px, py], [c2 / a2, 0]];
    do { o = [ri(2, 12), ri(2, 12)]; v = objVals(cs, o); } while (new Set(v).size !== 3);
    var L = lpChoices(cs, o, 'min');
    var fmt = function (r) { return pl(R(r[1]).val(), c[4], c[3]) + ' of ' + c[1] + ' and ' + pl(R(r[2]).val(), c[4], c[3]) + ' of ' + c[2] + ' ($' + R(r[0]).val() + ')'; };
    var w = L.w.slice(); w.push([o[0] * (px + 1) + o[1] * (py + 1), px + 1, py + 1]); w.push([0, 0, 0]);
    var un = function (k) { return pl(k, 'unit', 'units'); };
    return QQ({ q: c[0] + '. Each ' + c[4] + ' of ' + c[1] + ' provides ' + un(a1) + ' of ' + c[5] + ' and ' + un(a2) + ' of ' + c[6] + '. Each ' + c[4] + ' of ' + c[2] + ' provides ' + un(b1) + ' of ' + c[5] + ' and ' + un(b2) + ' of ' + c[6] + '. The mix must contain at least ' + c1 + ' units of ' + c[5] + ' and at least ' + c2 + ' units of ' + c[6] + '. ' + c[1] + ' costs $' + o[0] + ' per ' + c[4] + ' and ' + c[2] + ' costs $' + o[1] + ' per ' + c[4] + '. How many of each minimize the cost?',
      mc: mcR(L.cor, w, fmt),
      why: ['Let ' + X + ' and ' + Y + ' be the numbers of ' + c[3] + ' of ' + c[1] + ' and ' + c[2] + '. Minimize ' + objH('C', o) + ' subject to ' + m(P([[a1, X], [b1, Y]]) + ' ≥ ' + c1) + ', ' + m(P([[a2, X], [b2, Y]]) + ' ≥ ' + c2) + ', ' + m('<i>x</i> ≥ 0') + ', ' + m('<i>y</i> ≥ 0') + '.',
        'The feasible region is unbounded, with corners ' + cs.map(function (p) { return K.pt(p[0], p[1]); }).join(', ') + '. The middle corner solves the two boundary equations together.',
        'Cost at each corner: ' + valList('C', cs, L.v) + '.',
        'The minimum cost is $' + L.cor[0] + ' at ' + K.pt(L.cor[1], L.cor[2]) + '.'] },
      { t: 'lp', cons: [[a1, b1, '>=', c1], [a2, b2, '>=', c2], [1, 0, '>=', 0], [0, 1, '>=', 0]], obj: o, goal: 'min' });
  }
  // L3: read the corners from the graph, objective with mixed signs
  function g563c() {
    var rg = region4(), goal = K.coin() ? 'max' : 'min', o = uniqObj(rg.c, -5, 6, true), nm = goal === 'max' ? 'P' : 'C';
    var L = lpChoices(rg.c, o, goal);
    return QQ({ q: 'The shaded region is a feasible region; its corners lie on grid points. Find the ' + (goal === 'max' ? 'maximum' : 'minimum') + ' value of ' + objH(nm, o) + ' on the region and where it occurs.', graph: lpGraph(rg, false),
      mc: mcR(L.cor, L.w, fOpt),
      why: ['Read the corners from the graph: ' + rg.c.map(function (p) { return K.pt(p[0], p[1]); }).join(', ') + '.', 'Evaluate ' + iv(nm) + ' at each: ' + valList(nm, rg.c, L.v) + '.', 'The ' + (goal === 'max' ? 'maximum' : 'minimum') + ' is ' + n(L.cor[0]) + ', at ' + K.pt(L.cor[1], L.cor[2]) + '. (With a negative coefficient, the best corner is not always the one farthest from the origin.)'] },
      { t: 'lp', cons: rg.cons, obj: o, goal: goal });
  }
  K.lesson('5.6', { title: 'Systems of Inequalities and Linear Programming', std: 'Lial 12e · Section 5.6', levels: [[g561a, g561b, g561c], [g562a, g562b, g562c], [g563a, g563b, g563c]] });

  /* ================= 5.7 Properties of Matrices ================= */
  function rmat(r, c, lo, hi) { var A = [], i, j; for (i = 0; i < r; i++) { A.push([]); for (j = 0; j < c; j++) A[i].push(ri(lo, hi)); } return A; }
  function madd(A, B, k, h) { return mmap(A, function (v, i, j) { return k * v + h * B[i][j]; }); }
  function mlab(name, A) { return lab(iv(name), K.mat(A)); }
  function dimS(r) { return r === 'undef' ? m('<i>AB</i>') + ' is not defined' : m(r[0] + ' × ' + r[1]); }
  function mEx(A) { return function () { var B = A.map(function (r) { return r.slice(); }); var i = ri(0, B.length - 1), j = ri(0, B[0].length - 1); B[i][j] = R(B[i][j]).add(rnz(-3, 3)); return mmap(B, num); }; }
  // L1: dimensions of a product
  function g571a() {
    var mm = ri(1, 5), nn = ri(2, 5), rr = K.coin() || K.coin() ? nn : ri(1, 5), pp = ri(1, 5);
    var def = rr === nn, cor = def ? [mm, pp] : 'undef';
    var w = def ? [[pp, mm], [nn, nn], 'undef', [mm, nn]] : [[mm, pp], [nn, rr], [rr, nn], [pp, mm]];
    return QQ({ q: 'Matrix ' + iv('A') + ' is ' + m(mm + ' × ' + nn) + ' and matrix ' + iv('B') + ' is ' + m(rr + ' × ' + pp) + '. What are the dimensions of the product ' + m('<i>AB</i>') + '?',
      mc: mcR(cor, w, dimS, function () { return [ri(1, 6), ri(1, 6)]; }),
      why: def ? ['Write the dimensions side by side: ' + m('(' + mm + ' × ' + nn + ')(' + rr + ' × ' + pp + ')') + '.', 'The inside numbers match (' + nn + ' and ' + rr + '), so ' + m('<i>AB</i>') + ' is defined.', 'The outside numbers give its size: ' + m(mm + ' × ' + pp) + '.'] :
        ['Write the dimensions side by side: ' + m('(' + mm + ' × ' + nn + ')(' + rr + ' × ' + pp + ')') + '.', 'The inside numbers ' + nn + ' and ' + rr + ' do not match: each row of ' + iv('A') + ' has ' + nn + ' entries but each column of ' + iv('B') + ' has ' + rr + '.', 'So ' + m('<i>AB</i>') + ' is not defined.'] },
      { t: 'dims', A: [mm, nn], B: [rr, pp] });
  }
  // L1: sum or difference
  function g571b() {
    var d = pick([[2, 2], [2, 3], [3, 2]]), A = rmat(d[0], d[1], -9, 9), B = rmat(d[0], d[1], -9, 9), plus = K.coin();
    if (!B.some(function (r) { return r.some(function (v) { return v < 0; }); })) B[0][0] = -ri(1, 9);
    var cor = madd(A, B, 1, plus ? 1 : -1), w = [madd(A, B, 1, plus ? -1 : 1), plus ? madd(A, B, -1, 1) : madd(A, B, -1, 1), mmap(A, function (v, i, j) { return plus ? v + Math.abs(B[i][j]) : v - Math.abs(B[i][j]); })];
    var op = plus ? '+' : M;
    return QQ({ q: 'Find ' + m('<i>A</i> ' + op + ' <i>B</i>') + '.' + ctr(mlab('A', A) + mlab('B', B)),
      mc: mcR(cor, w, fMat, mEx(cor)),
      why: ['Both matrices are ' + m(d[0] + ' × ' + d[1]) + ', so they can be ' + (plus ? 'added' : 'subtracted') + ' entry by entry.',
        'Row 1: ' + A[0].map(function (v, j) { return m(n(v) + ' ' + op + ' ' + sub(B[0][j]) + ' = ' + n(cor[0][j])); }).join(', ') + '; the other rows work the same way.',
        m('<i>A</i> ' + op + ' <i>B</i> = ') + K.mat(cor) + '.'] }, { t: 'matexpr', mats: { A: A, B: B }, expr: plus ? 'A+B' : 'A-B' });
  }
  // L1: equal matrices
  function g571c() {
    var a = rnz(-6, 6), k = pick([2, 3, 4, -2, -3]), x = ri(-8, 8), y = ri(-6, 6), b = ri(-9, 9), c = ri(-9, 9), d = x + a, e = k * y;
    var L = [[m(P([[1, X], [a, '']])), b], [c, m(P([[k, Y]]))]], Rm = [[d, b], [c, e]];
    var fmt = function (r) { return m('<i>x</i> = ' + rh(r[0]) + ', <i>y</i> = ' + rh(r[1])); };
    return QQ({ q: 'Find ' + X + ' and ' + Y + ' so that the matrices are equal.' + ctr(K.mat(L) + ' ' + m('=') + ' ' + K.mat(Rm)),
      mc: mcR([x, y], [[d + a, y], [x, e * k], [x, e - k], [y, x]], fmt, function () { return [x + rnz(-3, 3), y + rnz(-2, 2)]; }),
      why: ['Equal matrices have the same dimensions and equal corresponding entries.', 'Row 1, column 1: ' + m(P([[1, X], [a, '']]) + ' = ' + n(d)) + ', so ' + m('<i>x</i> = ' + n(x)) + '.', 'Row 2, column 2: ' + m(P([[k, Y]]) + ' = ' + n(e)) + ', so ' + m('<i>y</i> = ' + n(y)) + '.'] },
      { t: 'eqmat', L: [['x + ' + sy(a), b], [c, sy(k) + '*y']], Rm: Rm });
  }
  // L2: linear combination kA − hB
  function g572a() {
    var d = pick([[2, 2], [2, 3]]), A = rmat(d[0], d[1], -6, 6), B = rmat(d[0], d[1], -6, 6), k = pick([2, 3, -2, -1]), h = pick([2, 3, -2]);
    var cor = madd(A, B, k, -h), kA = madd(A, B, k, 0), hB = madd(A, B, 0, h);
    var name = m((k === -1 ? M : n(k)) + '<i>A</i> ' + (h < 0 ? '+ ' + (-h) : M + ' ' + h) + '<i>B</i>');
    return QQ({ q: 'Find ' + name + '.' + ctr(mlab('A', A) + mlab('B', B)),
      mc: mcR(cor, [madd(A, B, k, h), madd(A, B, k, -k), madd(A, B, k, h < 0 ? 1 : -1)], fMat, mEx(cor)),
      why: ['Multiply every entry of ' + iv('A') + ' by ' + n(k) + ': ' + K.mat(kA) + '.', 'Multiply every entry of ' + iv('B') + ' by ' + n(h) + ': ' + K.mat(hB) + '.', 'Subtract entry by entry: ' + name + ' = ' + K.mat(cor) + '.'] },
      { t: 'matexpr', mats: { A: A, B: B }, expr: '(' + k + ')*A - (' + h + ')*B' });
  }
  // L2: 2 × 2 product
  function g572b() {
    var A, B, AB, BA;
    do { A = rmat(2, 2, -5, 6); B = rmat(2, 2, -5, 6); AB = mmul(A, B); BA = mmul(B, A); } while (JSON.stringify(AB) === JSON.stringify(BA));
    var ew = mmap(A, function (v, i, j) { return v * B[i][j]; }), rr = mmul(A, tr(B));
    var col = function (j) { return [B[0][j], B[1][j]]; };
    return QQ({ q: 'Find the product ' + m('<i>AB</i>') + '.' + ctr(mlab('A', A) + mlab('B', B)),
      mc: mcR(AB, [ew, BA, rr], fMat, mEx(AB)),
      why: ['Each entry is a row of ' + iv('A') + ' times a column of ' + iv('B') + '. Row 1: ' + dot(A[0], col(0)) + ' and ' + dot(A[0], col(1)) + '.', 'Row 2: ' + dot(A[1], col(0)) + ' and ' + dot(A[1], col(1)) + '.', m('<i>AB</i> = ') + K.mat(AB) + '. (Multiplying matching entries is not matrix multiplication.)'] },
      { t: 'matexpr', mats: { A: A, B: B }, expr: 'A@B' });
  }
  // L2: one entry of a product
  function g572c() {
    var tall = K.coin(), A = tall ? rmat(3, 2, -5, 6) : rmat(2, 3, -5, 6), B = tall ? rmat(2, 3, -5, 6) : rmat(3, 2, -5, 6), AB = mmul(A, B);
    var i = ri(0, AB.length - 1), j = ri(0, AB[0].length - 1), col = B.map(function (r) { return r[j]; }), ans = AB[i][j];
    var w = [AB[j] && AB[j][i] !== undefined ? AB[j][i] : null, A[i][0] * col[0], ans - A[i][0] * col[0] + A[i][0] + col[0], A[i].reduce(function (s, v) { return s + v; }, 0) * col.reduce(function (s, v) { return s + v; }, 0)];
    return QQ({ q: 'Find the entry in row ' + (i + 1) + ', column ' + (j + 1) + ' of ' + m('<i>AB</i>') + '.' + ctr(mlab('A', A) + mlab('B', B)),
      mc: mcR(ans, w, fNum, nEx(ans, 5)),
      why: ['Use row ' + (i + 1) + ' of ' + iv('A') + ', ' + K.mat([A[i]]) + ', and column ' + (j + 1) + ' of ' + iv('B') + ', ' + K.mat(col.map(function (v) { return [v]; })) + '.', 'Multiply matching entries and add: ' + dot(A[i], col) + '.', 'The entry is ' + n(ans) + '.'] },
      { t: 'entry', mats: { A: A, B: B }, expr: 'A@B', i: i, j: j });
  }
  // L3: application: quantities times prices
  var SALES = [['Two stores', 'Store 1', 'Store 2', ['notebooks', 'pens', 'folders'], 'store'], ['Two food trucks', 'Truck 1', 'Truck 2', ['tacos', 'burritos', 'drinks'], 'truck'], ['Two school clubs', 'Club 1', 'Club 2', ['T-shirts', 'mugs', 'caps'], 'club']];
  function g573a() {
    var c = pick(SALES), Qm = rmat(2, 3, 2, 15), Pc = [[ri(2, 12)], [ri(2, 12)], [ri(2, 12)]];
    while (Pc[0][0] === Pc[2][0]) Pc[2][0] = ri(2, 12);
    var cor = mmul(Qm, Pc), rev = mmul(Qm, [Pc[2], Pc[1], Pc[0]]), two = mmul(Qm.map(function (r) { return [r[0], r[1]]; }), [Pc[0], Pc[1]]);
    var odd = [[cor[0][0]], [cor[1][0] - Qm[1][0] * Pc[0][0]]];
    var pv = function (r) { return r.map(function (v) { return v[0]; }); };
    return QQ({ q: c[0] + ' sell ' + c[3].join(', ').replace(/, ([^,]*)$/, ', and $1') + '. Matrix ' + iv('Q') + ' gives the number of each item sold (row 1: ' + c[1] + ', row 2: ' + c[2] + '; columns in the order ' + c[3].join(', ') + '). Column matrix ' + iv('P') + ' gives each item’s price in dollars. Find ' + m('<i>QP</i>') + ', the total sales for each ' + c[4] + '.' + ctr(mlab('Q', Qm) + mlab('P', Pc)),
      mc: mcR(cor, [rev, two, odd], fMat, mEx(cor)),
      why: [m('<i>QP</i>') + ' is ' + m('(2 × 3)(3 × 1) = 2 × 1') + ': one total for each row of ' + iv('Q') + '.', c[1] + ': ' + dot(Qm[0], pv(Pc)) + '.', c[2] + ': ' + dot(Qm[1], pv(Pc)) + '.', 'So ' + m('<i>QP</i> = ') + K.mat(cor) + ': $' + cor[0][0] + ' and $' + cor[1][0] + '.'] },
      { t: 'matexpr', mats: { A: Qm, B: Pc }, expr: 'A@B' });
  }
  // L3: AB − BA
  function g573b() {
    var A, B, AB, BA;
    do { A = rmat(2, 2, -4, 5); B = rmat(2, 2, -4, 5); AB = mmul(A, B); BA = mmul(B, A); } while (JSON.stringify(AB) === JSON.stringify(BA));
    var cor = madd(AB, BA, 1, -1);
    return QQ({ q: 'Find ' + m('<i>AB</i> ' + M + ' <i>BA</i>') + '.' + ctr(mlab('A', A) + mlab('B', B)),
      mc: mcR(cor, [[[0, 0], [0, 0]], madd(AB, BA, -1, 1), madd(AB, BA, 1, 1)], fMat, mEx(cor)),
      why: [m('<i>AB</i> = ') + K.mat(AB) + ' (row of ' + iv('A') + ' times column of ' + iv('B') + ').', m('<i>BA</i> = ') + K.mat(BA) + ' (row of ' + iv('B') + ' times column of ' + iv('A') + ').',
        m('<i>AB</i> ' + M + ' <i>BA</i> = ') + K.mat(cor) + '. It is not the zero matrix, because matrix multiplication is not commutative.'] },
      { t: 'matexpr', mats: { A: A, B: B }, expr: 'A@B - B@A' });
  }
  // L3: which product is (not) defined
  function g573c() {
    var d = K.sample([2, 3, 4, 5], 4), sh = { A: [d[0], d[1]], B: [d[1], d[2]], C: [d[2], d[3]] };
    var defd = ['AB', 'BC', 'ABC'], und = ['BA', 'CB', 'AC', 'CA'], askNot = K.coin();
    var cor = askNot ? pick(und) : pick(defd), w = askNot ? defd.slice() : K.sample(und, 3);
    var dimOf = function (e) { return '(' + e.split('').map(function (ch) { return sh[ch][0] + ' × ' + sh[ch][1]; }).join(')(') + ')'; };
    var fmt = function (e) { return m('<i>' + e + '</i>'); };
    return QQ({ q: iv('A') + ' is ' + m(d[0] + ' × ' + d[1]) + ', ' + iv('B') + ' is ' + m(d[1] + ' × ' + d[2]) + ', and ' + iv('C') + ' is ' + m(d[2] + ' × ' + d[3]) + '. Which product is ' + (askNot ? '<b>not</b> defined' : 'defined') + '?',
      mc: mcR(cor, w, fmt),
      why: ['A product ' + m('<i>XY</i>') + ' is defined only when ' + iv('X') + ' has as many columns as ' + iv('Y') + ' has rows.',
        fmt(cor) + ': ' + m(dimOf(cor)) + (askNot ? '. The inside numbers do not match, so it is not defined.' : '. The inside numbers match' + (cor === 'ABC' ? ' at each step, giving a ' + m(d[0] + ' × ' + d[3]) + ' matrix.' : ', so it is defined.')),
        askNot ? 'The others are defined: ' + m('<i>AB</i>') + ' is ' + m(d[0] + ' × ' + d[2]) + ', ' + m('<i>BC</i>') + ' is ' + m(d[1] + ' × ' + d[3]) + ', and ' + m('<i>ABC</i>') + ' is ' + m(d[0] + ' × ' + d[3]) + '.' : 'Each of the other products has inside numbers that do not match.'] },
      { t: 'undef', shapes: sh, ask: askNot ? 'not' : 'def' });
  }
  K.lesson('5.7', { title: 'Properties of Matrices', std: 'Lial 12e · Section 5.7', levels: [[g571a, g571b, g571c], [g572a, g572b, g572c], [g573a, g573b, g573c]] });

  /* ================= 5.8 Matrix Inverses ================= */
  function uni2(lo, hi) { var A; do { A = rmat(2, 2, lo, hi); } while (Math.abs(A[0][0] * A[1][1] - A[0][1] * A[1][0]) !== 1 || A[0][0] === A[1][1] || A[0][1] === 0 || A[1][0] === 0 || A[0][1] === A[1][0]); return A; }
  function uni3() {
    var A, Ai, g = 0;
    do {
      A = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
      for (var t = 0; t < 4; t++) { var i = ri(0, 2), j; do { j = ri(0, 2); } while (j === i); var k = pick([1, -1, 2, -2]); A[i] = A[i].map(function (v, c) { return v + k * A[j][c]; }); }
      if (K.coin()) { var a = ri(0, 2), b = (a + ri(1, 2)) % 3, tmp = A[a]; A[a] = A[b]; A[b] = tmp; }
      Ai = inv(A);
    } while ((A.some(function (r) { return r.some(function (v) { return Math.abs(v) > 5; }); }) || Ai.some(function (r) { return r.some(function (v) { return Math.abs(R(v).val()) > 6; }); }) || A.filter(function (r) { return r.filter(function (v) { return v !== 0; }).length >= 2; }).length < 2 || JSON.stringify(tr(Ai)) === JSON.stringify(Ai)) && g++ < 400);
    return [A, Ai];
  }
  function adj2(A) { return [[A[1][1], -A[0][1]], [-A[1][0], A[0][0]]]; }
  function scl(A, k) { return mmap(A, function (v) { return num(R(v).mul(k)); }); }
  // L1: inverse with determinant ±1
  function g581a() {
    var A = uni2(-6, 7), d = A[0][0] * A[1][1] - A[0][1] * A[1][0], Ai = inv(A), ad = adj2(A);
    var w = [scl([[A[0][0], -A[0][1]], [-A[1][0], A[1][1]]], d), scl([[A[1][1], A[0][1]], [A[1][0], A[0][0]]], d), scl(Ai, -1), d === -1 ? ad : tr(Ai)];
    return QQ({ q: 'Find ' + m('<i>A</i><sup>' + M + '1</sup>') + ' for the matrix below.' + ctr(mlab('A', A)),
      mc: mcR(Ai, w, fMat, mEx(Ai)),
      why: ['The determinant is ' + d2txt(A) + ' = ' + n(d) + ', which is not 0, so the inverse exists.', 'Swap ' + n(A[0][0]) + ' and ' + n(A[1][1]) + ', and change the signs of ' + n(A[0][1]) + ' and ' + n(A[1][0]) + ': ' + K.mat(ad) + '.',
        (d === 1 ? 'Since the determinant is 1, that matrix is already the inverse: ' : 'Divide every entry by the determinant, ' + M + '1, which changes every sign: ') + m('<i>A</i><sup>' + M + '1</sup> = ') + K.mat(Ai) + '. Check: ' + m('<i>AA</i><sup>' + M + '1</sup> = <i>I</i>') + '.'] }, { t: 'inv', A: A });
  }
  // L1: which matrix has no inverse
  function g581b() {
    var a = rnz(-6, 6), b = rnz(-6, 6), k = pick([2, 3, -2, -1, R(1, 2), -3]), sing;
    if (K.coin()) sing = [[a, b], [num(R(a).mul(k)), num(R(b).mul(k))]]; else sing = [[a, num(R(a).mul(k))], [b, num(R(b).mul(k))]];
    if (sing.some(function (r) { return r.some(function (v) { return !(typeof v === 'number'); }); })) return g581b();
    var others = [], g = 0;
    while (others.length < 3 && g++ < 200) { var B = rmat(2, 2, -6, 7); var dd = B[0][0] * B[1][1] - B[0][1] * B[1][0]; if (dd !== 0 && Math.abs(dd) <= 6) others.push(B); }
    var sd = sing[0][0] * sing[1][1] - sing[0][1] * sing[1][0];
    return QQ({ q: 'Which matrix has no inverse?', mc: mcR(sing, others, fMat, function () { var B; do { B = rmat(2, 2, -6, 7); } while (B[0][0] * B[1][1] - B[0][1] * B[1][0] === 0); return B; }),
      why: ['A 2 × 2 matrix has an inverse exactly when its determinant ' + m('<i>ad</i> ' + M + ' <i>bc</i>') + ' is not 0.', 'For ' + K.mat(sing) + ': ' + d2txt(sing) + ' = ' + n(sd) + ', so it is singular and has no inverse.', 'The other matrices have nonzero determinants, so each of them has an inverse.'] }, { t: 'sing' });
  }
  // L1: write the system as AX = B
  function g581c() {
    var three = K.coin(), t = three ? [ri(-4, 4), ri(-4, 4), ri(-4, 4)] : [ri(-5, 5), ri(-5, 5)], S;
    if (three) S = rSys3(t, false); else S = rSys2(t[0], t[1], -6, 6, function (a1, b1, a2, b2) { return b1 !== a2 && a1 !== b1; });
    var A = coefM(S), Bc = constC(S).map(function (v) { return [v]; }), nv = A.length;
    if (JSON.stringify(tr(A)) === JSON.stringify(A)) return g581c();
    var Xv = (nv === 3 ? [X, Y, Z] : [X, Y]).map(function (v) { return [v]; });
    var fmt = function (r) { return K.mat(r[0]) + K.mat(Xv) + ' ' + m('=') + ' ' + K.mat(r[1]); };
    var sw = A.map(function (r) { var u = r.slice(); var tmp = u[0]; u[0] = u[1]; u[1] = tmp; return u; });
    return QQ({ q: 'Which matrix equation represents the system?' + sys(S.map(eqR)),
      mc: mcR([A, Bc], [[tr(A), Bc], [A, Bc.map(function (r) { return [-r[0]]; })], [sw, Bc]], fmt, function () { var A2 = A.map(function (r) { return r.slice(); }); A2[ri(0, nv - 1)][ri(0, nv - 1)] += rnz(-2, 2); return [A2, Bc]; }),
      why: [iv('A') + ' holds the coefficients, one row per equation: ' + K.mat(A) + '.', iv('X') + ' is the column of variables and ' + iv('B') + ' is the column of constants: ' + K.mat(Bc) + '.', 'So ' + m('<i>AX</i> = <i>B</i>') + ' is ' + fmt([A, Bc]) + '.'] }, { t: 'mateq', eqs: S });
  }
  // L2: inverse with fractions
  function g582a() {
    var A, d;
    do { A = rmat(2, 2, -6, 7); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; } while ([2, 3, 4, 5].indexOf(Math.abs(d)) < 0 || A[0][0] === A[1][1] || A[0][1] === 0 || A[1][0] === 0 || A[0][1] === A[1][0]);
    var Ai = inv(A), ad = adj2(A);
    var w = [ad, scl([[A[0][0], -A[0][1]], [-A[1][0], A[1][1]]], R(1, d)), scl([[A[1][1], A[0][1]], [A[1][0], A[0][0]]], R(1, d)), scl(Ai, -1)];
    return QQ({ q: 'Find ' + m('<i>A</i><sup>' + M + '1</sup>') + ' for the matrix below.' + ctr(mlab('A', A)),
      mc: mcR(Ai, w, fMat, mEx(Ai)),
      why: ['The determinant is ' + d2txt(A) + ' = ' + n(d) + '.', 'Swap the diagonal entries and change the signs of the other two: ' + K.mat(ad) + '.', 'Multiply by ' + m(sfr(1, d)) + ': ' + m('<i>A</i><sup>' + M + '1</sup> = ') + K.mat(Ai) + '.'] }, { t: 'inv', A: A });
  }
  // L2: solve using a given inverse
  function g582b() {
    var A = uni2(-5, 6), Ai = inv(A), x = ri(-6, 6), y = ri(-6, 6), S = [[A[0][0], A[0][1], A[0][0] * x + A[0][1] * y], [A[1][0], A[1][1], A[1][0] * x + A[1][1] * y]], Bc = [S[0][2], S[1][2]];
    var rowW = [Bc[0] * Ai[0][0] + Bc[1] * Ai[1][0], Bc[0] * Ai[0][1] + Bc[1] * Ai[1][1]], AB = [A[0][0] * Bc[0] + A[0][1] * Bc[1], A[1][0] * Bc[0] + A[1][1] * Bc[1]];
    return QQ({ q: 'The coefficient matrix ' + iv('A') + ' of the system has the inverse shown. Use it to solve the system.' + sys(S.map(eqR)) + ctr(lab('<i>A</i><sup>' + M + '1</sup>', K.mat(Ai))),
      mc: mcR([x, y], [[y, x], rowW, AB], fPt, pEx(x, y)),
      why: ['Write the system as ' + m('<i>AX</i> = <i>B</i>') + ' with ' + m('<i>B</i> = ') + K.mat([[Bc[0]], [Bc[1]]]) + ', so ' + m('<i>X</i> = <i>A</i><sup>' + M + '1</sup><i>B</i>') + '.', 'Row 1: ' + dot(Ai[0], Bc) + '. Row 2: ' + dot(Ai[1], Bc) + '.', 'So ' + m('<i>x</i> = ' + n(x)) + ' and ' + m('<i>y</i> = ' + n(y)) + ': the solution is ' + K.pt(x, y) + '.'] },
      { t: 'solinv', eqs: S, Ainv: Ai });
  }
  // L2: find the inverse, then solve
  function g582c() {
    var A, d;
    do { A = rmat(2, 2, -6, 7); d = A[0][0] * A[1][1] - A[0][1] * A[1][0]; } while ([1, 2].indexOf(Math.abs(d)) < 0 || A[0][1] === 0 || A[1][0] === 0);
    var Ai = inv(A), x = ri(-6, 6), y = ri(-6, 6), Bc = [A[0][0] * x + A[0][1] * y, A[1][0] * x + A[1][1] * y], S = [[A[0][0], A[0][1], Bc[0]], [A[1][0], A[1][1], Bc[1]]];
    var ad = adj2(A), adjB = [ad[0][0] * Bc[0] + ad[0][1] * Bc[1], ad[1][0] * Bc[0] + ad[1][1] * Bc[1]];
    return QQ({ q: 'Solve the system by using the inverse of the coefficient matrix. Write the solution as an ordered pair.' + sys(S.map(eqR)),
      mc: mcR([x, y], [[y, x], adjB, [-x, -y]], fPt, pEx(x, y)),
      why: [m('<i>A</i> = ') + K.mat(A) + ' has determinant ' + n(d) + ', so ' + m('<i>A</i><sup>' + M + '1</sup> = ') + K.mat(Ai) + '.', m('<i>X</i> = <i>A</i><sup>' + M + '1</sup><i>B</i>') + ': row 1 gives ' + dot(Ai[0], Bc) + ' and row 2 gives ' + dot(Ai[1], Bc) + '.', 'The solution is ' + K.pt(x, y) + '. Check it in both equations.'] },
      { t: 'sol', eqs: S });
  }
  // L3: 3 × 3 inverse
  function g583a() {
    var U = uni3(), A = U[0], Ai = U[1], dA = dv(A);
    var fl = Ai.map(function (r) { return r.slice(); }); var p = fl[0][1] !== 0 ? [0, 1] : fl[1][0] !== 0 ? [1, 0] : [0, 2]; fl[p[0]][p[1]] = -fl[p[0]][p[1]];
    var col = Ai.map(function (r) { return r[0]; });
    return QQ({ q: 'Find ' + m('<i>A</i><sup>' + M + '1</sup>') + ' for the matrix below.' + ctr(mlab('A', A)),
      mc: mcR(Ai, [tr(Ai), scl(Ai, -1), fl], fMat, mEx(Ai)),
      why: ['Row-reduce ' + m('[<i>A</i> | <i>I</i>]') + ' until the left side is ' + iv('I') + ' (det ' + iv('A') + ' = ' + n(dA) + ', so the inverse exists).', 'The right side is then ' + m('<i>A</i><sup>' + M + '1</sup> = ') + K.mat(Ai) + '.',
        'Check one entry of ' + m('<i>AA</i><sup>' + M + '1</sup>') + ': row 1 of ' + iv('A') + ' times column 1 of ' + m('<i>A</i><sup>' + M + '1</sup>') + ' is ' + dot(A[0], col) + ', the 1 in ' + iv('I') + '.'] }, { t: 'inv', A: A });
  }
  // L3: solve a 3 × 3 system with a given inverse
  function g583b() {
    var U = uni3(), A = U[0], Ai = U[1], t = [ri(-4, 4), ri(-4, 4), ri(-4, 4)];
    var Bc = A.map(function (r) { return r[0] * t[0] + r[1] * t[1] + r[2] * t[2]; }), S = A.map(function (r, i) { return r.concat([Bc[i]]); });
    var AB = A.map(function (r) { return r[0] * Bc[0] + r[1] * Bc[1] + r[2] * Bc[2]; }), rowW = [0, 1, 2].map(function (j) { return num(dsum(Bc, Ai.map(function (r) { return r[j]; }))); });
    return QQ({ q: 'The coefficient matrix ' + iv('A') + ' of the system has the inverse shown. Use it to solve the system.' + sys(S.map(eqR)) + ctr(lab('<i>A</i><sup>' + M + '1</sup>', K.mat(Ai))),
      mc: mcR(t, [AB, rowW, [t[1], t[0], t[2]], [t[2], t[1], t[0]]], fTri, tEx(t)),
      why: [m('<i>X</i> = <i>A</i><sup>' + M + '1</sup><i>B</i>') + ' with ' + m('<i>B</i> = ') + K.mat(Bc.map(function (v) { return [v]; })) + '.', 'Row 1: ' + dot(Ai[0], Bc) + '. Row 2: ' + dot(Ai[1], Bc) + '. Row 3: ' + dot(Ai[2], Bc) + '.', 'The solution is ' + fTri(t) + '.'] },
      { t: 'solinv', eqs: S, Ainv: Ai });
  }
  // L3: value of k that makes a matrix singular
  function g583c() {
    var Kk = iv('k'), A, ks, why, w, fmt = function (r) { var s = r.slice().sort(function (u, v) { return R(v).val() - R(u).val(); }); return s.map(function (v) { return m(Kk + ' = ' + rh(v)); }).join(' or '); };
    if (K.coin()) {
      var a, b, c; do { a = rnz(-6, 6); b = rnz(-6, 6); c = rnz(-6, 6); } while ((a * b) % c !== 0 || Math.abs(c) === 1);
      var k = a * b / c; A = [[Kk, a], [b, c]]; ks = [k];
      w = [[-k], [a * b], [R(c, a * b)], [k, -k]];
      why = ['A matrix has no inverse when its determinant is 0.', 'det = ' + m(Kk + '(' + n(c) + ') ' + M + ' ' + sub(a) + '(' + n(b) + ') = ' + P([[c, Kk], [-a * b, '']])) + '.', 'Set it equal to 0: ' + m(P([[c, Kk]]) + ' = ' + n(a * b)) + ', so ' + m(Kk + ' = ' + n(k)) + '.'];
    } else {
      var t = ri(2, 6), sq = t * t, divs = []; for (var i = 1; i <= sq; i++) if (sq % i === 0) divs.push(i);
      var p = pick(divs), q = sq / p, sg = K.coin() ? 1 : -1; p *= sg; q *= sg;
      A = [[Kk, p], [q, Kk]]; ks = t === 0 ? [0] : [t, -t];
      w = [[t], [-t], [sq], [sq, -sq]];
      why = ['A matrix has no inverse when its determinant is 0.', 'det = ' + m(Kk + '<sup>2</sup> ' + M + ' ' + sub(p) + '(' + n(q) + ') = ' + Kk + '<sup>2</sup> ' + M + ' ' + sq) + '.', 'Set it equal to 0: ' + m(Kk + '<sup>2</sup> = ' + sq) + ', so ' + m(Kk + ' = ' + t) + ' or ' + m(Kk + ' = ' + M + t) + '.'];
    }
    return QQ({ q: 'For which value(s) of ' + Kk + ' does the matrix have no inverse?' + ctr(K.mat(A)), mc: mcR(ks, w, fmt, function () { return [ks[0] + rnz(-3, 3)]; }), why: why },
      { t: 'ksing', A: A.map(function (r) { return r.map(function (v) { return v === Kk ? 'k' : v; }); }) });
  }
  // L3: decode a message
  function g583d() {
    var A, Ai;
    do { A = uni2(-3, 5); Ai = inv(A); } while (A.some(function (r) { return r.some(function (v) { return v < 0; }); }) && K.coin());
    var x1, x2, Yc;
    do { x1 = ri(1, 26); x2 = ri(1, 26); Yc = [A[0][0] * x1 + A[0][1] * x2, A[1][0] * x1 + A[1][1] * x2]; } while (x1 === x2);
    var cor = [[x1], [x2]], AY = [[A[0][0] * Yc[0] + A[0][1] * Yc[1]], [A[1][0] * Yc[0] + A[1][1] * Yc[1]]];
    var ad = [[A[1][1], A[0][1]], [A[1][0], A[0][0]]], dd = A[0][0] * A[1][1] - A[0][1] * A[1][0];
    var bad = [[num(R(ad[0][0] * Yc[0] + ad[0][1] * Yc[1]).div(dd))], [num(R(ad[1][0] * Yc[0] + ad[1][1] * Yc[1]).div(dd))]];
    var L = function (v) { return String.fromCharCode(64 + v); };
    return QQ({ q: 'A message is coded by replacing each letter with its position in the alphabet (A = 1, B = 2, …, Z = 26), writing the numbers in pairs as columns, and multiplying each column on the left by the matrix ' + iv('A') + ' below. One coded column is ' + iv('C') + '. What was the original column?' + ctr(mlab('A', A) + mlab('C', Yc.map(function (v) { return [v]; }))),
      mc: mcR(cor, [AY, [[x2], [x1]], bad], fMat, mEx(cor)),
      why: ['Undo the coding with the inverse: det ' + iv('A') + ' = ' + d2txt(A) + ' = ' + n(dd) + ', so ' + m('<i>A</i><sup>' + M + '1</sup> = ') + K.mat(Ai) + '.', m('<i>A</i><sup>' + M + '1</sup><i>C</i>') + ': row 1 gives ' + dot(Ai[0], Yc) + ' and row 2 gives ' + dot(Ai[1], Yc) + '.', 'The original column is ' + K.mat(cor) + ', the letters ' + L(x1) + ' and ' + L(x2) + '.'] },
      { t: 'decode', A: A, Y: Yc });
  }
  K.lesson('5.8', { title: 'Matrix Inverses', std: 'Lial 12e · Section 5.8', levels: [[g581a, g581b, g581c], [g582a, g582b, g582c], [g583a, g583b, g583c, g583d]] });

  K.review('5', 'Chapter 5 Review: Systems and Matrices');
})(typeof window !== 'undefined' ? window.KCEP : globalThis.KCEP);
