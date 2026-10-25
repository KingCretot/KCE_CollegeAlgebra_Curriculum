/* KCE College Algebra Practice — Chapter 1: Equations and Inequalities
   Lial, Essentials of College Algebra 12e, Sections 1.1–1.8.
   Each lesson: Level 1 Warm-Up, Level 2 Building, Level 3 Exam Challenge (3+ generators per level).
   Every question carries its raw problem data in q.p for the independent check in verify-c1.py. */
(function (K) {
  var ri = K.ri, rnz = K.rnz, pick = K.pick, n = K.n, P = K.poly, X = K.x, Q = K.Q, mc = K.mc, M = K.MINUS, m = K.m, fr = K.frx, R = K.R;
  var X2 = K.xp(2), X4 = K.xp(4), NEGINF = '(' + M + '∞';

  /* ---------- shared helpers ---------- */
  function rh(v) { return R(v).html(); }
  function sub(v) { v = R(v); return v.n < 0 ? '(' + v.html() + ')' : v.html(); }   // parenthesize negatives
  function xeq(v) { return m('<i>x</i> = ' + rh(v)); }
  function lin(a, b, v) { return P([[a, v || X], [b, '']]); }
  function quad(a, b, c, v) { v = v || 'x'; return P([[a, K.xp(2, v)], [b, K.xp(1, v)], [c, '']]); }
  function cont(terms) { var s = P(terms); if (s === '0') return ''; return s.charAt(0) === M ? ' ' + M + ' ' + s.slice(1) : ' + ' + s; }
  function cpar(a) { return a === 1 ? '' : a === -1 ? M : n(a); }          // coefficient written before '('
  function fp(v) { return v === 0 ? X : '(' + lin(1, v) + ')'; }          // factor (x + v)
  function withP(o, p) { o.p = p; return o; }
  function nint(v) { return Math.abs(v - Math.round(v)) < 1e-9; }
  function dec2(v) { return Math.abs(v * 100 - Math.round(v * 100)) < 1e-7; }  // at most 2 decimals
  function dol(v) { return nint(v) ? '$' + K.comma(Math.round(v)) : K.money(v); }
  function L(s) { return s.replace(/[A-Za-z]/g, '<i>$&</i>').replace(/\^2/g, '<sup>2</sup>'); } // italic letters
  function pl(v, w) { return n(v) + ' ' + w + (v === 1 ? '' : 's'); }       // 1 hour / 2 hours
  // article before a number: "an 8-ft", "an 11%", "an 80-ft", "a 25-ft"
  function an(v) { var d = String(v).replace(/,/g, '').replace(/^\D+/, '').split('.')[0], lead = d.slice(0, d.length % 3 || 3); return (d.charAt(0) === '8' || lead === '11' || lead === '18') ? 'an' : 'a'; }
  function An(v) { return an(v) === 'an' ? 'An' : 'A'; }
  // "Subtract 5x from both sides" / "Add 5x to both sides" (never "subtract −5x")
  function addSubX(c, v) { v = v || X; return c < 0 ? 'Add ' + m(P([[-c, v]])) + ' to' : 'Subtract ' + m(P([[c, v]])) + ' from'; }
  function cmul(k, inner) { return k === 1 ? inner : n(k) + '(' + inner + ')'; }   // numeric k(inner), with k = 1 dropped
  function sqrtF(h) { return '<span class="rad">√<span class="rc" style="display:inline-block;vertical-align:middle;padding-top:1px">' + h + '</span></span>'; } // radical over a stacked fraction

  // value-keyed multiple choice: c and wrong items are [html, values]; values are numbers, R, or [re, im]
  function cv(v) { return Array.isArray(v) ? v : (typeof v === 'number' ? [v, 0] : [R(v).val(), 0]); }
  function vkey(vals) { return vals.map(function (v) { v = cv(v); return K.round(v[0], 6) + ':' + K.round(v[1], 6); }).sort().join('|'); }
  function mcV(c, wrong, extra) {
    var seen = {}, ws = []; seen[vkey(c[1])] = 1;
    var add = function (w) { if (!w || ws.length >= 3) return; var k = vkey(w[1]); if (!seen[k]) { seen[k] = 1; ws.push(w[0]); } };
    (wrong || []).forEach(add);
    var g = 0; while (ws.length < 3 && extra && g++ < 300) add(extra(g));
    return mc(c[0], ws);
  }
  function xi(v) { return [xeq(v), [R(v).val()]]; }
  // solution set of rationals
  function setH(arr) {
    var u = []; arr.forEach(function (v) { v = R(v); if (!u.some(function (w) { return w.eq(v); })) u.push(v); });
    u.sort(function (a, b) { return a.val() - b.val(); });
    return [m(u.length ? '{' + u.map(function (v) { return v.html(); }).join(', ') + '}' : '∅'), u.map(function (v) { return v.val(); })];
  }
  var EMPTY = [m('∅'), []];

  // radicals
  function sqf(N) { var s = 1, r = N; for (var k = 2; k * k <= r; k++) while (r % (k * k) === 0) { r /= k * k; s *= k; } return [s, r]; }
  function radH(s, r) { return r === 1 ? n(s) : (s === 1 ? '' : n(s)) + K.sqrt(r); }
  function rootPos(k) { var q = sqf(Math.abs(k)); if (k > 0) return radH(q[0], q[1]); return q[1] === 1 ? (q[0] === 1 ? '' : n(q[0])) + 'i' : (q[0] === 1 ? '' : n(q[0])) + 'i' + K.sqrt(q[1]); }
  function rootVal(k) { return k >= 0 ? [Math.sqrt(k), 0] : [0, Math.sqrt(-k)]; }
  // solution set of (p ± √D)/d in simplest form (D may be negative → a ± bi form)
  function pmGen(p, D, d) {
    if (d < 0) { p = -p; d = -d; }
    if (D === 0) return setH([R(p, d)]);
    var q, s, r, g;
    if (D > 0) {
      q = sqf(D); s = q[0]; r = q[1];
      if (r === 1) return setH([R(p - s, d), R(p + s, d)]);
      g = K.gcd(K.gcd(Math.abs(p), s), d); var p2 = p / g, s2 = s / g, d2 = d / g;
      var h = p2 === 0 ? '±' + (d2 === 1 ? radH(s2, r) : fr(radH(s2, r), d2)) : (d2 === 1 ? n(p2) + ' ± ' + radH(s2, r) : fr(n(p2) + ' ± ' + radH(s2, r), d2));
      var a = p / d, b = s * Math.sqrt(r) / d;
      return [m('{' + h + '}'), [a - b, a + b]];
    }
    q = sqf(-D); s = q[0]; r = q[1];
    var re = R(p, d), imH;
    if (r === 1) { var im = R(s, d); imH = (im.eq(1) ? '' : im.html()) + 'i'; }
    else { g = K.gcd(s, d); var s3 = s / g, d3 = d / g; imH = d3 === 1 ? (s3 === 1 ? '' : n(s3)) + 'i' + K.sqrt(r) : fr(radH(s3, r), d3) + 'i'; }
    var bb = s * Math.sqrt(r) / d;
    return [m('{' + (re.n === 0 ? '±' : re.html() + ' ± ') + imH + '}'), [[re.val(), -bb], [re.val(), bb]]];
  }
  // complex numbers a + bi
  function cx(a, b) {
    a = R(a); b = R(b); if (b.n === 0) return a.html();
    var ab = b.abs(), im = (ab.eq(1) ? '' : ab.html()) + 'i';
    if (a.n === 0) return (b.n < 0 ? M : '') + im;
    return a.html() + (b.n < 0 ? ' ' + M + ' ' : ' + ') + im;
  }
  function cxv(a, b) { return [m(cx(a, b)), [[R(a).val(), R(b).val()]]]; }
  function cpr(a, b) { return '(' + cx(a, b) + ')'; }
  // intervals
  function ivl(lo, loC, hi, hiC) { return (lo === null ? NEGINF : (loC ? '[' : '(') + rh(lo)) + ', ' + (hi === null ? '∞)' : rh(hi) + (hiC ? ']' : ')')); }
  function ray(x0, dir, cl) { return m(dir > 0 ? ivl(x0, cl, null, false) : ivl(null, false, x0, cl)); }
  function cmp(v, sym) { v = R(v); return sym === '<' ? v.n < 0 : sym === '<=' ? v.n <= 0 : sym === '>' ? v.n > 0 : v.n >= 0; }
  var SYM = K.ineqSym, FLIP = K.flipSym, STR = { '<': '<=', '<=': '<', '>': '>=', '>=': '>' }, OPP = { '<': '>=', '<=': '>', '>': '<=', '>=': '<' };
  // solution set of a one-variable inequality from its critical values; test(R) → true/false
  function ivSet(test, crit) {
    var c = [];
    crit.forEach(function (v) { v = R(v); if (!c.some(function (w) { return w.eq(v); })) c.push(v); });
    c.sort(function (a, b) { return a.val() - b.val(); });
    if (!c.length) return m(test(R(0)) ? NEGINF + ', ∞)' : '∅');
    var at = [{ lo: null, hi: c[0], t: !!test(c[0].sub(1)) }];
    c.forEach(function (v, i) {
      at.push({ pt: v, t: !!test(v) });
      var nx = c[i + 1];
      at.push({ lo: v, hi: nx || null, t: !!test(nx ? v.add(nx).div(2) : v.add(1)) });
    });
    var out = [], cur = null, bad = false;
    at.forEach(function (a) {
      if (a.t) { if (!cur) cur = a.pt ? { lo: a.pt, loC: true } : { lo: a.lo, loC: false }; cur.end = a; }
      else if (cur) { out.push(cur); cur = null; }
    });
    if (cur) out.push(cur);
    var parts = out.map(function (s) {
      var e = s.end; if (e.pt && s.lo === e.pt) bad = true;
      return ivl(s.lo, s.loC, e.pt ? e.pt : e.hi, !!e.pt);
    });
    if (bad) return null;
    return m(parts.length ? parts.join(' ∪ ') : '∅');
  }
  function words(t) { return { '<': 'less than', '<=': 'less than or equal to', '>': 'greater than', '>=': 'greater than or equal to' }[t]; }

  /* ================= 1.1 Linear Equations ================= */
  var ID = 'Identity; solution set {all real numbers}', CO = 'Contradiction; solution set ∅';
  function CD(v) { return 'Conditional; solution set ' + m('{' + rh(v) + '}'); }
  // equation simplifies to A1 x + B1 = A2 x + B2 (A1 ≠ 0)
  function classifyQ(eq, A1, B1, A2, B2, first) {
    var steps = [first], ans, wr;
    if (A1 === A2) {
      steps.push(addSubX(A1) + ' both sides: ' + m(n(B1) + ' = ' + n(B2)) + '.');
      if (B1 === B2) {
        steps.push('That statement is always true, so every real number is a solution. The equation is an <b>identity</b>.');
        var z = ri(1, 5); ans = ID; wr = [CO, CD(0), CD(z)];
      } else {
        steps.push('That statement is false, so no value of ' + X + ' works. The equation is a <b>contradiction</b> with solution set ∅.');
        ans = CO; wr = [ID, CD(R(B2 - B1, A1)), CD(0)];
      }
    } else {
      var x0 = R(B2 - B1, A1 - A2);
      steps.push('Collect terms: ' + m(P([[A1 - A2, X]]) + ' = ' + n(B2 - B1)) + (A1 - A2 === 1 ? '' : ', so ' + m('<i>x</i> = ' + x0.html())) + '.');
      steps.push('Exactly one value works, so the equation is <b>conditional</b>.');
      ans = CD(x0); wr = [ID, CO, CD(x0.n === 0 ? R(1) : x0.neg())];
    }
    return withP(Q({ q: 'Solve and classify the equation ' + eq + ' as an identity, a conditional equation, or a contradiction.', mc: mc(ans, wr), why: steps }), { k: 'classify', e: eq });
  }
  // literal equations: [equation, variable, answer, wrongs, why]
  var LIT = [
    [L('P = 2l + 2w'), 'w', fr(L('P − 2l'), '2'), [L('P − 2l'), fr(L('P − l'), '2'), fr(L('P'), '2') + L(' − 2l')], ['Subtract ' + m(L('2l')) + ' from both sides: ' + m(L('P − 2l = 2w')) + '.', 'Divide both sides by 2: ' + m(L('w = ') + fr(L('P − 2l'), '2')) + '.']],
    [L('P = 2l + 2w'), 'l', fr(L('P − 2w'), '2'), [L('P − 2w'), fr(L('P − w'), '2'), fr(L('P'), '2') + L(' − 2w')], ['Subtract ' + m(L('2w')) + ' from both sides: ' + m(L('P − 2w = 2l')) + '.', 'Divide both sides by 2: ' + m(L('l = ') + fr(L('P − 2w'), '2')) + '.']],
    [L('A = P(1 + rt)'), 't', fr(L('A − P'), L('Pr')), [fr(L('A − P'), L('r')), fr(L('A'), L('Pr')) + ' − 1', fr(L('A − 1'), L('Pr'))], ['Distribute: ' + m(L('A = P + Prt')) + '.', 'Subtract ' + m(L('P')) + ': ' + m(L('A − P = Prt')) + '.', 'Divide by ' + m(L('Pr')) + ': ' + m(L('t = ') + fr(L('A − P'), L('Pr'))) + '.']],
    [L('A = P(1 + rt)'), 'r', fr(L('A − P'), L('Pt')), [fr(L('A − P'), L('t')), fr(L('A'), L('Pt')) + ' − 1', fr(L('A − P'), L('P')) + L(' − t')], ['Distribute: ' + m(L('A = P + Prt')) + '.', 'Subtract ' + m(L('P')) + ': ' + m(L('A − P = Prt')) + '.', 'Divide by ' + m(L('Pt')) + ': ' + m(L('r = ') + fr(L('A − P'), L('Pt'))) + '.']],
    [L('F = ') + fr(9, 5) + L('C + 32'), 'C', fr(5, 9) + L('(F − 32)'), [fr(5, 9) + L('F − 32'), fr(9, 5) + L('(F − 32)'), fr(5, 9) + L('(F + 32)')], ['Subtract 32 from both sides: ' + m(L('F − 32 = ') + fr(9, 5) + L('C')) + '.', 'Multiply both sides by ' + m(fr(5, 9)) + ', the reciprocal of ' + m(fr(9, 5)) + ': ' + m(L('C = ') + fr(5, 9) + L('(F − 32)')) + '.']],
    [L('A = ') + fr(1, 2) + L('h(a + b)'), 'h', fr(L('2A'), L('a + b')), [fr(L('A'), L('2(a + b)')), L('2A − a − b'), fr(L('2A'), L('a')) + L(' + b')], ['Multiply both sides by 2: ' + m(L('2A = h(a + b)')) + '.', 'Divide both sides by ' + m(L('a + b')) + ': ' + m(L('h = ') + fr(L('2A'), L('a + b'))) + '.']],
    [L('V = ') + fr(1, 3) + 'π' + L('r^2h'), 'h', fr(L('3V'), 'π' + L('r^2')), [fr(L('V'), '3π' + L('r^2')), L('3V − ') + 'π' + L('r^2'), fr(L('3V') + 'π', L('r^2'))], ['Multiply both sides by 3: ' + m(L('3V = ') + 'π' + L('r^2h')) + '.', 'Divide both sides by ' + m('π' + L('r^2')) + ': ' + m(L('h = ') + fr(L('3V'), 'π' + L('r^2'))) + '.']],
    [L('S = 2') + 'π' + L('rh + 2') + 'π' + L('r^2'), 'h', fr(L('S − 2') + 'π' + L('r^2'), '2π' + L('r')), [fr(L('S'), '2π' + L('r')) + ' − 2π' + L('r^2'), L('S − 2') + 'π' + L('r^2') + ' − 2π' + L('r'), fr(L('S − 2') + 'π' + L('r'), '2π' + L('r^2'))], ['Subtract ' + m('2π' + L('r^2')) + ': ' + m(L('S − 2') + 'π' + L('r^2') + ' = 2π' + L('rh')) + '.', 'Divide both sides by ' + m('2π' + L('r')) + ': ' + m(L('h = ') + fr(L('S − 2') + 'π' + L('r^2'), '2π' + L('r'))) + '.']],
    [L('I = Prt'), 't', fr(L('I'), L('Pr')), [L('IPr'), fr(L('Pr'), L('I')), L('I − Pr')], ['The variable ' + m(L('t')) + ' is multiplied by ' + m(L('Pr')) + '.', 'Divide both sides by ' + m(L('Pr')) + ': ' + m(L('t = ') + fr(L('I'), L('Pr'))) + '.']],
    [L('y = mx + b'), 'x', fr(L('y − b'), L('m')), [fr(L('y + b'), L('m')), L('m(y − b)'), fr(L('y'), L('m')) + L(' − b')], ['Subtract ' + m(L('b')) + ': ' + m(L('y − b = mx')) + '.', 'Divide both sides by ' + m(L('m')) + ': ' + m(L('x = ') + fr(L('y − b'), L('m'))) + '.']]
  ];

  var c11 = [
    [
      function () { // ax + b = cx + d
        var x = ri(-9, 9), a, c, b = rnz(-12, 12);
        do { a = rnz(-9, 9); c = rnz(-9, 9); } while (a === c);
        var d = (a - c) * x + b, e = m(lin(a, b) + ' = ' + lin(c, d));
        var w = [xi(-x), xi(R(d + b, a - c))]; if (a + c !== 0) w.push(xi(R(d - b, a + c)));
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(xi(x), w, function () { return xi(x + rnz(-4, 4)); }), why: [addSubX(c) + ' both sides: ' + m(lin(a - c, b) + ' = ' + n(d)) + '.', (b > 0 ? 'Subtract ' + n(b) : 'Add ' + n(-b)) + ' on both sides: ' + m(P([[a - c, X]]) + ' = ' + n(d - b)) + '.', (a - c === 1 ? '' : 'Divide by ' + n(a - c) + ': ' + xeq(x) + '. ') + 'Check: ' + m(K.lin([[a, n(x)]]) + K.plusK(b) + ' = ' + n(a * x + b)) + ' and ' + m(K.lin([[c, n(x)]]) + K.plusK(d) + ' = ' + n(c * x + d)) + ' ✓'] }), { k: 'solve', e: e });
      },
      function () { // x/A + p = q
        var A = ri(2, 9), t = ri(-9, 9), x = A * t, p = rnz(-9, 9), q = t + p;
        var e = m(fr(X, A) + K.plusK(p) + ' = ' + n(q));
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(xi(x), [xi(q - p), xi(A * (q + p)), xi(R(q - p, A))], function () { return xi(x + rnz(-5, 5)); }), why: [(p > 0 ? 'Subtract ' + n(p) : 'Add ' + n(-p)) + ' on both sides: ' + m(fr(X, A) + ' = ' + n(t)) + '.', 'Multiply both sides by ' + A + ': ' + m('<i>x</i> = ' + A + '(' + n(t) + ') = ' + n(x)) + '.', 'Check: ' + m(fr(n(x), A) + K.plusK(p) + ' = ' + n(t) + K.plusK(p) + ' = ' + n(q)) + ' ✓'] }), { k: 'solve', e: e });
      },
      function () { // k(x + p) = kx + q, or a conditional version
        var k = pick([-5, -4, -3, -2, 2, 3, 4, 5, 6]), p = rnz(-8, 8), v = ri(0, 2), rhsA = k, rhsB;
        if (v === 0) rhsB = k * p;
        else if (v === 1) rhsB = k * p + rnz(-6, 6);
        else { do { rhsA = rnz(-6, 6); } while (rhsA === k); rhsB = (k - rhsA) * ri(-6, 6) + k * p; }
        var eq = m(cpar(k) + '(' + lin(1, p) + ') = ' + lin(rhsA, rhsB));
        return classifyQ(eq, k, k * p, rhsA, rhsB, 'Distribute on the left: ' + m(lin(k, k * p) + ' = ' + lin(rhsA, rhsB)) + '.');
      }
    ],
    [
      function () { // (x + p)/A ± (x + q)/B = C
        var A, B, s, p, q, C, Lc, cA, cB, coef, rhs, x;
        do {
          A = pick([2, 3, 4, 5, 6]); B = pick([2, 3, 4, 5, 6]); s = pick([1, -1]); p = rnz(-6, 6); q = rnz(-6, 6); C = ri(-4, 6);
          Lc = K.lcm(A, B); cA = Lc / A; cB = s * Lc / B; coef = cA + cB; rhs = Lc * C - cA * p - cB * q;
          x = coef !== 0 ? R(rhs, coef) : null;
        } while (A === B || coef === 0 || x.d > 6 || Math.abs(x.val()) > 20);
        var e = m(fr(lin(1, p), A) + (s > 0 ? ' + ' : ' ' + M + ' ') + fr(lin(1, q), B) + ' = ' + n(C));
        var w = [xi(R(C - cA * p - cB * q, coef)), xi(R(Lc * C - cA * p + cB * q, coef))];
        var c2 = Lc / B + s * Lc / A; if (c2 !== 0) w.push(xi(R(Lc * C - (Lc / B) * p - s * (Lc / A) * q, c2)));
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(xi(x), w, function () { return xi(x.add(rnz(-3, 3))); }), why: ['Multiply every term by the LCD, ' + Lc + ': ' + m(K.lin([[cA, lin(1, p)], [cB, lin(1, q)]]) + ' = ' + n(Lc * C)) + '.', 'Distribute and combine like terms: ' + m(lin(coef, cA * p + cB * q) + ' = ' + n(Lc * C)) + '.', 'Isolate ' + X + ': ' + (coef === 1 ? xeq(x) : m(P([[coef, X]]) + ' = ' + n(rhs)) + ', so ' + xeq(x)) + '.'] }), { k: 'solve', e: e });
      },
      function () { // decimals: r1 x + r2(T − x) = r3 T
        var r1, r2, r3, T, x, base, g;
        do {
          r1 = ri(2, 12); r2 = ri(2, 12); if (Math.abs(r1 - r2) < 2) continue;
          r3 = ri(Math.min(r1, r2) + 1, Math.max(r1, r2) - 1);
          g = K.gcd(r3 - r2, r1 - r2); base = Math.abs(r1 - r2) / g; T = base * ri(1, Math.max(1, Math.floor(60 / base)));
          x = T * (r3 - r2) / (r1 - r2);
        } while (Math.abs(r1 - r2) < 2 || T < 5 || T > 60 || !nint(x));
        var d = function (r) { return n(r / 100); };
        var e = m(d(r1) + X + ' + ' + d(r2) + '(' + n(T) + ' ' + M + ' ' + X + ') = ' + d(r3) + '(' + n(T) + ')');
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(xi(x), [xi(T - x), xi(R((r3 - r2) * T, r1 + r2)), xi(-x)], function () { return xi(x + rnz(-5, 5)); }), why: ['Multiply every term by 100 to clear the decimals: ' + m(r1 + X + ' + ' + r2 + '(' + T + ' ' + M + ' ' + X + ') = ' + r3 + '(' + T + ')') + '.', 'Distribute: ' + m(r1 + X + ' + ' + r2 * T + ' ' + M + ' ' + r2 + X + ' = ' + r3 * T) + ', so ' + m(P([[r1 - r2, X]]) + ' = ' + n((r3 - r2) * T)) + '.', 'Divide by ' + n(r1 - r2) + ': ' + xeq(x) + '.'] }), { k: 'solve', e: e });
      },
      function () { // ax + by = c for y
        var a, b, c;
        do { a = rnz(-9, 9); b = rnz(-9, 9); c = rnz(-24, 24); } while (Math.abs(a) === Math.abs(b) || Math.abs(b) < 2);
        var e = m(P([[a, X], [b, K.y]]) + ' = ' + n(c)), Y = '<i>y</i> = ';
        var cor = m(K.lineEq(R(-a, b), R(c, b)));
        return withP(Q({ q: 'Solve ' + e + ' for ' + K.y + '.', mc: mc(cor, [m(K.lineEq(R(a, b), R(c, b))), m(K.lineEq(R(-a, b), R(c))), m(K.lineEq(R(-b, a), R(c, b))), m(K.lineEq(R(-a, b), R(-c, b)))]), why: [(a > 0 ? 'Subtract ' + m(P([[a, X]])) : 'Add ' + m(P([[-a, X]]))) + ' on both sides: ' + m(P([[b, K.y]]) + ' = ' + P([[-a, X], [c, '']])) + '.', 'Divide every term by ' + n(b) + ': ' + m(K.lineEq(R(-a, b), R(c, b))) + '.'] }), { k: 'formula', e: e, v: 'y' });
      },
      function () { // classify after distributing and combining
        var a, p, c, q, A1, B1, v = ri(0, 2), A2, B2;
        do { a = pick([-5, -4, -3, -2, 2, 3, 4, 5]); p = rnz(-6, 6); c = rnz(-4, 4); q = rnz(-9, 9); A1 = a + c; } while (A1 === 0);
        B1 = a * p + q;
        if (v === 0) { A2 = A1; B2 = B1; } else if (v === 1) { A2 = A1; B2 = B1 + rnz(-7, 7); } else { do { A2 = A1 + rnz(-3, 3); } while (A2 === A1); B2 = (A1 - A2) * ri(-6, 6) + B1; }
        var eq = m(cpar(a) + '(' + lin(1, p) + ')' + cont([[c, X], [q, '']]) + ' = ' + lin(A2, B2));
        return classifyQ(eq, A1, B1, A2, B2, 'Distribute and combine like terms on the left: ' + m(lin(A1, B1) + ' = ' + lin(A2, B2)) + '.');
      }
    ],
    [
      function () { // value of k for no solution / identity
        var a = pick([-4, -3, -2, 2, 3, 4, 5]), b = rnz(-6, 6), c, none = K.coin();
        do { c = rnz(-6, 6); } while (c === a);
        var d = none ? a * b + rnz(-6, 6) : a * b, k = c - a;
        var e = m(cpar(a) + '(' + lin(1, b) + ') + <i>kx</i> = ' + lin(c, d));
        var kv = function (v) { return [m('<i>k</i> = ' + n(v)), [v]]; };
        return withP(Q({ q: 'For what value of ' + m('<i>k</i>') + ' does the equation ' + e + ' have ' + (none ? '<b>no solution</b>' : '<b>infinitely many solutions</b> (an identity)') + '?', mc: mcV(kv(k), [kv(a - c), kv(a + c), kv(c), kv(-c - a)], function () { return kv(k + rnz(-4, 4)); }), why: ['Distribute and collect the ' + X + '-terms: ' + m('(' + n(a) + ' + <i>k</i>)<i>x</i>' + K.plusK(a * b) + ' = ' + lin(c, d)) + '.', 'For ' + (none ? 'no solution' : 'an identity') + ', the ' + X + '-terms must cancel: ' + m(n(a) + ' + <i>k</i> = ' + n(c)) + ', so ' + m('<i>k</i> = ' + n(k)) + '.', 'Then the equation becomes ' + m(n(a * b) + ' = ' + n(d)) + ', which is ' + (none ? 'false, so there is no solution.' : 'true for every ' + X + '.') + ' Any other ' + m('<i>k</i>') + ' gives exactly one solution.'] }), { k: 'kval', e: e, want: none ? 'none' : 'all' });
      },
      function () { // literal equation
        var f = pick(LIT), v = L(f[1]);
        return withP(Q({ q: 'Solve ' + m(f[0]) + ' for ' + m(v) + '.', mc: mc(m(v + ' = ' + f[2]), f[3].map(function (w) { return m(v + ' = ' + w); })), why: f[4] }), { k: 'formula', e: m(f[0]), v: f[1] });
      },
      function () { // three fractions
        var A, B, C, a1, b1, a2, b2, a3, b3, Lc, coef, rhs, x;
        do {
          A = pick([2, 3, 4, 6]); B = pick([2, 3, 4, 6]); C = pick([2, 3, 4, 6, 12]); a1 = ri(1, 3); a2 = ri(1, 3); a3 = ri(1, 3); b1 = rnz(-6, 6); b2 = rnz(-6, 6); b3 = rnz(-6, 6);
          Lc = K.lcm(K.lcm(A, B), C); coef = a1 * Lc / A - a2 * Lc / B - a3 * Lc / C; rhs = b3 * Lc / C - b1 * Lc / A + b2 * Lc / B;
          x = coef !== 0 ? R(rhs, coef) : null;
        } while (A === B || coef === 0 || x.d > 9 || Math.abs(x.val()) > 30);
        var e = m(fr(lin(a1, b1), A) + ' ' + M + ' ' + fr(lin(a2, b2), B) + ' = ' + fr(lin(a3, b3), C));
        var w = [xi(R(b3 * Lc / C - b1 * Lc / A - b2 * Lc / B, coef)), xi(x.neg())];
        var cf2 = a1 * Lc / A - a2 * Lc / B - a3; if (cf2 !== 0) w.push(xi(R(b3 - b1 * Lc / A + b2 * Lc / B, cf2)));
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(xi(x), w, function () { return xi(x.add(rnz(-3, 3))); }), why: ['Multiply every term by the LCD, ' + Lc + ': ' + m(K.lin([[Lc / A, lin(a1, b1)], [-Lc / B, lin(a2, b2)]]) + ' = ' + K.lin([[Lc / C, lin(a3, b3)]])) + '. The minus sign applies to the whole second numerator.', 'Distribute: ' + m(P([[a1 * Lc / A - a2 * Lc / B, X], [b1 * Lc / A - b2 * Lc / B, '']]) + ' = ' + lin(a3 * Lc / C, b3 * Lc / C)) + '.', 'Collect terms: ' + (coef === 1 ? xeq(x) : m(P([[coef, X]]) + ' = ' + n(rhs)) + ', so ' + xeq(x)) + '.'] }), { k: 'solve', e: e });
      },
      function () { // simple interest: solve A = P(1 + rt) for t numerically
        var Pp = ri(10, 90) * 100, r = ri(2, 8), t = ri(2, 12), A = Pp + Pp * r * t / 100, I = A - Pp;
        var yr = function (v) { return [m(pl(v, 'year')), [v]]; };
        return withP(Q({ q: 'Use ' + m(L('A = P(1 + rt)')) + '. How many years does it take ' + dol(Pp) + ' invested at ' + r + '% simple interest to grow to ' + dol(A) + '?', mc: mcV(yr(t), [yr(t / 100), dec2(A / (Pp * r / 100)) ? yr(A / (Pp * r / 100)) : null, yr(t + 1)], function () { var z = t + rnz(-3, 3); return z > 0 ? yr(z) : null; }), why: ['Substitute: ' + m(K.comma(A) + ' = ' + K.comma(Pp) + '(1 + ' + n(r / 100) + L('t') + ')') + '. Write the rate as a decimal: ' + r + '% = ' + n(r / 100) + '.', 'Distribute and subtract ' + K.comma(Pp) + ': ' + m(K.comma(I) + ' = ' + K.comma(Pp * r / 100) + L('t')) + '.', 'Divide: ' + m(L('t = ') + n(t)) + (t === 1 ? ' year.' : ' years.')] }), { k: 'word', w: 'interestT', A: A, P: Pp, r: r });
      }
    ]
  ];
  K.lesson('1.1', { title: 'Linear Equations', std: 'Lial 12e · Section 1.1', levels: c11 });

  /* ================= 1.2 Applications and Modeling with Linear Equations ================= */
  function numC(v, unit) { return [n(v) + (unit ? ' ' + unit : ''), [v]]; }
  var NAMES = [['Jada', 'Malik'], ['Ana', 'Ben'], ['Priya', 'Luis'], ['Kim', 'Omar'], ['Sofia', 'Dev']];
  var c12 = [
    [
      function () { // simple interest
        var Pp = ri(10, 90) * 100, r = ri(15, 80) / 10, t = ri(2, 6), I = K.round(Pp * r * t / 100, 2);
        return withP(Q({ q: 'How much simple interest does ' + dol(Pp) + ' earn at ' + n(r) + '% per year for ' + t + ' years?', mc: mcV([dol(I), [I]], [[dol(K.round(I / t, 2)), [K.round(I / t, 2)]], [dol(Pp + I), [Pp + I]], [dol(K.round(Pp * r * t, 2)), [Pp * r * t]]]), why: ['Use ' + m(L('I = Prt')) + ' with the rate as a decimal: ' + n(r) + '% = ' + n(r / 100) + '.', m(L('I = ') + K.comma(Pp) + '(' + n(r / 100) + ')(' + t + ') = ' + K.comma(I)) + ', so the interest is ' + dol(I) + '.', 'The total amount would be ' + dol(Pp + I) + ', but the question asks only for the interest.'] }), { k: 'word', w: 'interest', P: Pp, r: r, t: t });
      },
      function () { // linear model: fee + per-unit
        var F = ri(5, 20), c = ri(2, 6), x = ri(3, 15), B = F + c * x;
        var w = []; [B / c, (B + F) / c, B - F].forEach(function (v) { if (nint(v)) w.push(numC(v)); });
        return withP(Q({ q: 'A streaming plan costs ' + dol(F) + ' per month plus ' + dol(c) + ' per movie rental. How many rentals make the monthly bill ' + dol(B) + '?', mc: mcV(numC(x), w, function () { var z = x + rnz(-4, 4); return z > 0 ? numC(z) : null; }), why: ['Model: ' + m(L('C = ') + c + X + ' + ' + F) + ', where ' + X + ' is the number of rentals.', 'Set ' + m(c + X + ' + ' + F + ' = ' + B) + ', so ' + m(c + X + ' = ' + (B - F)) + '.', 'Divide by ' + c + ': ' + xeq(x) + (x === 1 ? ' rental.' : ' rentals.')] }), { k: 'word', w: 'plan', F: F, c: c, B: B });
      },
      function () { // rectangle perimeter, length = w + d
        var wv = ri(3, 20), d = ri(1, 9), Lv = wv + d, Pv = 2 * (wv + Lv);
        var w = [numC(Lv, 'cm')]; [Pv / 4, (Pv - d) / 2, (Pv - 2 * d) / 2].forEach(function (v) { if (nint(v)) w.push(numC(v, 'cm')); });
        return withP(Q({ q: 'A rectangle has a perimeter of ' + Pv + ' cm, and its length is ' + d + ' cm more than its width. What is the width?', mc: mcV(numC(wv, 'cm'), w, function () { var z = wv + rnz(-3, 3); return z > 0 ? numC(z, 'cm') : null; }), why: ['Let the width be ' + m(L('w')) + '; the length is ' + m(L('w + ') + d) + '.', m(L('2w + 2(w + ') + d + ') = ' + Pv) + ', so ' + m(L('4w + ') + 2 * d + ' = ' + Pv) + '.', m(L('4w = ') + (Pv - 2 * d)) + ', so the width is ' + wv + ' cm (and the length is ' + Lv + ' cm).'] }), { k: 'word', w: 'rectP', P: Pv, d: d });
      },
      function () { // opposite directions
        var r1 = ri(6, 14) * 5, r2 = ri(6, 14) * 5, t = pick([2, 2.5, 3, 4, 5, 6]), D = (r1 + r2) * t;
        var hrs = function (v) { return [m(pl(v, 'hour')), [v]]; }, w = [];
        [D / r1, D / r2, r1 !== r2 ? D / Math.abs(r2 - r1) : 0].forEach(function (v) { if (v > 0 && Math.abs(v * 10 - Math.round(v * 10)) < 1e-9) w.push(hrs(v)); });
        return withP(Q({ q: 'Two cars leave the same point at the same time and travel in opposite directions, one at ' + r1 + ' mph and the other at ' + r2 + ' mph. After how many hours are they ' + K.comma(D) + ' miles apart?', mc: mcV(hrs(t), w, function () { var z = t + pick([-1, 1, -0.5, 0.5, 2]); return z > 0 ? hrs(z) : null; }), why: ['In ' + m(L('t')) + ' hours the cars travel ' + m(r1 + L('t')) + ' and ' + m(r2 + L('t')) + ' miles.', 'Opposite directions means the distances add: ' + m(r1 + L('t') + ' + ' + r2 + L('t') + ' = ' + K.comma(D)) + '.', m((r1 + r2) + L('t') + ' = ' + K.comma(D)) + ', so ' + m(L('t = ') + n(t)) + (t === 1 ? ' hour.' : ' hours.')] }), { k: 'word', w: 'opposite', r1: r1, r2: r2, D: D });
      }
    ],
    [
      function () { // rectangle, length = k·w + d
        var k = pick([2, 3]), d = rnz(-4, 6), wv, Lv, Pv;
        do { wv = ri(3, 15); Lv = k * wv + d; } while (Lv <= wv);
        Pv = 2 * (wv + Lv);
        var dim = function (a, b) { return ['Width ' + n(a) + ' m, length ' + n(b) + ' m', [a, b * 1000]]; };
        var w = [dim(Lv, wv)], w1 = (Pv - 2 * d) / (2 * k + 1), w2 = (Pv - d) / (k + 1);
        if (nint(w1) && w1 > 0 && k * w1 + d > 0) w.push(dim(w1, k * w1 + d)); if (nint(w2) && w2 > 0 && k * w2 + d > 0) w.push(dim(w2, k * w2 + d));
        var desc = (k === 2 ? 'twice' : 'three times') + ' its width' + (d > 0 ? ' plus ' + d + ' m' : ' minus ' + (-d) + ' m');
        return withP(Q({ q: 'A rectangle’s length is ' + desc + ', and its perimeter is ' + Pv + ' m. Find its dimensions.', mc: mcV(dim(wv, Lv), w, function () { var z = wv + rnz(-3, 3); return z > 0 && k * z + d > 0 ? dim(z, k * z + d) : null; }), why: ['Let the width be ' + m(L('w')) + '; the length is ' + m(lin(k, d, L('w'))) + '.', 'Perimeter: ' + m('2(' + lin(k, d, L('w')) + ') + ' + L('2w') + ' = ' + Pv) + ', so ' + m(lin(2 * k + 2, 2 * d, L('w')) + ' = ' + Pv) + '.', m(L('w = ') + wv) + ' m and the length is ' + m(k + '(' + wv + ')' + K.plusK(d) + ' = ' + Lv) + ' m. Check: ' + m('2(' + wv + ') + 2(' + Lv + ') = ' + Pv) + ' ✓'] }), { k: 'word', w: 'rectKP', P: Pv, kk: k, d: d });
      },
      function () { // investment split
        var T = ri(5, 20) * 1000, r1 = ri(2, 6), r2 = r1 + ri(1, 3), x;
        do { x = ri(1, T / 500 - 1) * 500; } while (x === T - x);
        var I = (r1 * x + r2 * (T - x)) / 100;
        var dv = function (v) { return [dol(v), [v]]; };
        return withP(Q({ q: dol(T) + ' is split between two accounts paying ' + r1 + '% and ' + r2 + '% simple interest. The total interest after one year is ' + dol(I) + '. How much is invested at ' + r1 + '%?', mc: mcV(dv(x), [dv(T - x)], function () { var z = x + 500 * rnz(-4, 4); return z > 0 && z < T ? dv(z) : null; }), why: ['Let ' + X + ' be the amount at ' + r1 + '%; then ' + m(K.comma(T) + ' ' + M + ' ' + X) + ' is at ' + r2 + '%.', 'Interest equation: ' + m(n(r1 / 100) + X + ' + ' + n(r2 / 100) + '(' + K.comma(T) + ' ' + M + ' ' + X + ') = ' + K.comma(I)) + '.', 'Simplify: ' + m(K.comma(r2 * T / 100) + ' ' + M + ' ' + n((r2 - r1) / 100) + X + ' = ' + K.comma(I)) + ', so ' + m('<i>x</i> = ' + K.comma(x)) + '. ' + dol(x) + ' is at ' + r1 + '% and ' + dol(T - x) + ' at ' + r2 + '%.'] }), { k: 'word', w: 'split', T: T, r1: r1, r2: r2, I: I });
      },
      function () { // mixture: add x L of p1% to V L of p2%
        var p1, p2, p3, V, x, dil = K.coin();
        do {
          p1 = ri(0, 6) * 5; p2 = ri(2, 12) * 5; if (!dil) { var t = p1; p1 = p2; p2 = t; }
          p3 = ri(Math.min(p1, p2) / 5 + 1, Math.max(p1, p2) / 5 - 1) * 5; V = ri(2, 20) * 5;
          x = V * (p2 - p3) / (p3 - p1);
        } while (p1 === p2 || p2 === 0 || Math.abs(p1 - p2) < 10 || !nint(x) || x <= 0 || x > 100);
        var lit = function (v) { return [m(n(v) + ' L'), [v]]; };
        var what = p1 === 0 ? 'pure water' : p1 + '% acid solution';
        var before = p1 === 0 ? m(n(p2 / 100) + '(' + V + ')') + ' (the water adds no acid)' : m(n(p1 / 100) + X + ' + ' + n(p2 / 100) + '(' + V + ')');
        return withP(Q({ q: 'How many liters of ' + what + ' must be added to ' + V + ' L of ' + an(p2) + ' ' + p2 + '% acid solution to make ' + an(p3) + ' ' + p3 + '% acid solution?', mc: mcV(lit(x), [lit(x + V), lit(V * (p3 - p1) / (p2 - p3))], function () { var z = x + 5 * rnz(-3, 3); return z > 0 ? lit(z) : null; }), why: ['Pure acid before mixing: ' + before + '. Pure acid after: ' + m(n(p3 / 100) + '(' + X + ' + ' + V + ')') + '.', 'Multiply by 100: ' + m((p1 ? P([[p1, X]]) + ' + ' : '') + p2 * V + ' = ' + p3 + X + ' + ' + p3 * V) + '.', m(n(p2 * V - p3 * V) + ' = ' + P([[p3 - p1, X]])) + (p3 - p1 === 1 ? '' : ', so ' + xeq(x)) + ': add ' + pl(x, 'liter') + '.'] }), { k: 'word', w: 'mixAdd', p1: p1, p2: p2, p3: p3, V: V });
      },
      function () { // two legs of a trip
        var t1 = ri(1, 5), t2 = ri(1, 5), r = ri(6, 14) * 5, d = ri(1, 4) * 5, D = t1 * r + t2 * (r + d);
        var mph = function (v) { return [m(n(v) + ' mph'), [v]]; }, w = [mph(r + d)];
        [D / (t1 + t2), (D + t2 * d) / (t1 + t2), (D - d) / (t1 + t2)].forEach(function (v) { if (Math.abs(v * 10 - Math.round(v * 10)) < 1e-9) w.push(mph(v)); });
        return withP(Q({ q: 'A train travels ' + t1 + ' hour' + (t1 > 1 ? 's' : '') + ' at ' + m(L('r')) + ' mph and then ' + t2 + ' hour' + (t2 > 1 ? 's' : '') + ' at a speed ' + d + ' mph faster, covering ' + D + ' miles in all. What is ' + m(L('r')) + '?', mc: mcV(mph(r), w, function () { return mph(r + 5 * rnz(-3, 3)); }), why: ['Distance = rate × time for each part: ' + m(P([[t1, L('r')]]) + ' + ' + cpar(t2) + L('(r + ') + d + ') = ' + D) + '.', 'Simplify: ' + m((t1 + t2) + L('r') + ' + ' + t2 * d + ' = ' + D) + ', so ' + m((t1 + t2) + L('r') + ' = ' + (D - t2 * d)) + '.', m(L('r = ') + r) + ' mph. Check: ' + m(cmul(t1, r) + ' + ' + cmul(t2, r + d) + ' = ' + D) + ' ✓'] }), { k: 'word', w: 'twoLegs', t1: t1, t2: t2, d: d, D: D });
      }
    ],
    [
      function () { // mixture to a total
        var p1, p2, p3, V, a;
        do { p1 = ri(1, 10) * 5; p2 = ri(1, 10) * 5; p3 = ri(1, 10) * 5; V = ri(2, 12) * 10; a = V * (p3 - p2) / (p1 - p2); }
        while (!(p3 > Math.min(p1, p2) && p3 < Math.max(p1, p2)) || !nint(a) || a <= 0 || a >= V || a === V - a);
        var b = V - a;
        var two = function (u, v) { return [n(u) + ' L of ' + p1 + '% and ' + n(v) + ' L of ' + p2 + '%', [u, v * 1000]]; };
        return withP(Q({ q: 'A chemist mixes ' + an(p1) + ' ' + p1 + '% solution with ' + an(p2) + ' ' + p2 + '% solution to make ' + V + ' L of ' + an(p3) + ' ' + p3 + '% solution. How many liters of each are used?', mc: mcV(two(a, b), [two(b, a), two(V / 2, V / 2)], function () { var z = a + rnz(-8, 8); return z > 0 && z < V ? two(z, V - z) : null; }), why: ['Let ' + X + ' = liters of ' + p1 + '%; then ' + m(V + ' ' + M + ' ' + X) + ' liters are ' + p2 + '%.', 'Pure substance: ' + m(n(p1 / 100) + X + ' + ' + n(p2 / 100) + '(' + V + ' ' + M + ' ' + X + ') = ' + n(p3 / 100) + '(' + V + ')') + '.', 'Multiply by 100: ' + m(P([[p1 - p2, X]]) + ' + ' + p2 * V + ' = ' + p3 * V) + ', so ' + xeq(a) + '. Use ' + a + ' L of ' + p1 + '% and ' + b + ' L of ' + p2 + '%.'] }), { k: 'word', w: 'mixTotal', p1: p1, p2: p2, p3: p3, V: V });
      },
      function () { // catch-up
        var r1, r2, h, t;
        do { r1 = ri(8, 12) * 5; r2 = r1 + ri(1, 6) * 5; h = ri(1, 3); t = r1 * h / (r2 - r1); } while (!nint(t) || t > 10);
        var hrs = function (v) { return [m(pl(v, 'hour')), [v]]; }, w = [hrs(t + h)];
        var v2 = r1 * h / (r1 + r2); if (dec2(v2)) w.push(hrs(v2));
        return withP(Q({ q: 'A truck leaves a depot traveling ' + r1 + ' mph. ' + h + ' hour' + (h > 1 ? 's' : '') + ' later, a car leaves the same depot on the same road traveling ' + r2 + ' mph. How many hours after the car leaves does it catch up to the truck?', mc: mcV(hrs(t), w, function () { var z = t + rnz(-3, 3); return z > 0 ? hrs(z) : null; }), why: ['Let ' + m(L('t')) + ' be the car’s driving time in hours; by then the truck has been driving for ' + m(L('(t + ') + h + ')') + ' hours.', 'At the catch-up point the distances are equal: ' + m(r2 + L('t = ') + r1 + L('(t + ') + h + ')') + '.', m((r2 - r1) + L('t = ') + r1 * h) + ', so ' + m(L('t = ') + n(t)) + (t === 1 ? ' hour.' : ' hours.')] }), { k: 'word', w: 'catch', r1: r1, r2: r2, h: h });
      },
      function () { // two plans cost the same
        var F1, F2, c1, c2, x;
        do { c2 = ri(2, 9); c1 = c2 + ri(1, 6); F1 = ri(0, 10) * 5; x = ri(4, 30); F2 = F1 + (c1 - c2) * x; } while (F2 > 300);
        var mo = function (v) { return [m(pl(v, 'month')), [v]]; }, w = [];
        [(F2 + F1) / (c1 + c2), F2 / c1, (F2 - F1) / c2].forEach(function (v) { if (nint(v) && v > 0) w.push(mo(v)); });
        return withP(Q({ q: 'Gym A charges ' + (F1 ? an(F1) + ' ' + dol(F1) + ' sign-up fee plus ' + dol(c1) + ' per month' : 'no sign-up fee, just ' + dol(c1) + ' per month') + '. Gym B charges ' + an(F2) + ' ' + dol(F2) + ' sign-up fee plus ' + dol(c2) + ' per month. After how many months is the total cost the same?', mc: mcV(mo(x), w, function () { var z = x + rnz(-4, 4); return z > 0 ? mo(z) : null; }), why: ['Costs after ' + X + ' months: A = ' + m(c1 + X + (F1 ? ' + ' + F1 : '')) + ', B = ' + m(c2 + X + ' + ' + F2) + '.', 'Set them equal: ' + m(c1 + X + (F1 ? ' + ' + F1 : '') + ' = ' + c2 + X + ' + ' + F2) + ', so ' + m(P([[c1 - c2, X]]) + ' = ' + (F2 - F1)) + '.', xeq(x) + ' months (both cost ' + dol(F1 + c1 * x) + ').'] }), { k: 'word', w: 'plans', F1: F1, c1: c1, F2: F2, c2: c2 });
      },
      function () { // overall rate
        var A, r1, r2, r3, y;
        do { r1 = ri(2, 5); r3 = r1 + ri(1, 3); r2 = r3 + ri(1, 4); A = ri(2, 20) * 1000; y = A * (r3 - r1) / (r2 - r3); } while (!nint(y) || y % 100 !== 0 || y === A);
        var dv = function (v) { return [dol(v), [v]]; };
        return withP(Q({ q: 'An investor has ' + dol(A) + ' earning ' + r1 + '% simple interest. How much more must be invested at ' + r2 + '% so that the total investment earns ' + r3 + '% overall per year?', mc: mcV(dv(y), [dv(y + A), dv(A * (r3 - r1) / (r2 - r1)), dv(A)], function () { var z = y + 500 * rnz(-4, 4); return z > 0 ? dv(z) : null; }), why: ['Let ' + X + ' be the new amount. Interest: ' + m(n(r1 / 100) + '(' + K.comma(A) + ') + ' + n(r2 / 100) + X) + ' ' + m('= ' + n(r3 / 100) + '(' + K.comma(A) + ' + ' + X + ')') + '.', 'Multiply by 100: ' + m(K.comma(r1 * A) + ' + ' + r2 + X) + ' ' + m('= ' + K.comma(r3 * A) + ' + ' + r3 + X) + '.', m(P([[r2 - r3, X]]) + ' = ' + K.comma((r3 - r1) * A)) + (r2 - r3 === 1 ? '' : ', so ' + m(X + ' = ' + K.comma(y))) + '. Invest ' + dol(y) + ' more at ' + r2 + '%.'] }), { k: 'word', w: 'overall', A: A, r1: r1, r2: r2, r3: r3 });
      }
    ]
  ];
  K.lesson('1.2', { title: 'Applications and Modeling with Linear Equations', std: 'Lial 12e · Section 1.2', levels: c12 });

  /* ================= 1.3 Complex Numbers ================= */
  function cterm(v, first) { var a = Math.abs(v), body = (a === 1 ? '' : n(a)) + 'i'; return first ? (v < 0 ? M : '') + body : (v < 0 ? ' ' + M + ' ' : ' + ') + body; }
  function iPow(e) { return [[1, 0], [0, 1], [-1, 0], [0, -1]][((e % 4) + 4) % 4]; }
  var IP = [cxv(1, 0), cxv(0, 1), cxv(-1, 0), cxv(0, -1)];
  var c13 = [
    [
      function () { // √−n
        var s, r, N;
        do { s = ri(1, 10); r = pick([1, 1, 2, 3, 5, 6, 7]); N = s * s * r; } while (N > 300 || N < 4);
        var e = m(K.sqrt(M + N)), val = s * Math.sqrt(r), cor = [m(rootPos(-N)), [[0, val]]];
        var w = [[m(M + radH(s, r)), [-val]], [m(radH(s, r)), [val]], [m(M + rootPos(-N)), [[0, -val]]]];
        return withP(Q({ q: 'Write ' + e + ' in terms of i, in simplest form.', mc: mcV(cor, w), why: ['For ' + m('<i>a</i> &gt; 0') + ', ' + m(K.sqrt(M + '<i>a</i>') + ' = i' + K.sqrt('<i>a</i>')) + '. So ' + m(e + ' = i' + K.sqrt(N)) + '.', r === 1 ? m(K.sqrt(N) + ' = ' + s) + ', so the answer is ' + m(rootPos(-N)) + '.' : s === 1 ? N + ' has no perfect-square factor, so ' + m(K.sqrt(N)) + ' is already simplified and the answer is ' + m(rootPos(-N)) + '.' : 'Simplify: ' + m(K.sqrt(N) + ' = ' + K.sqrt(s * s + ' · ' + r) + ' = ' + radH(s, r)) + ', so the answer is ' + m(rootPos(-N)) + '.', 'A real number like ' + m(M + radH(s, r)) + ' cannot be the answer: its square is positive.'] }), { k: 'cx', e: e });
      },
      function () { // add / subtract
        var a = rnz(-9, 9), b = rnz(-9, 9), c = rnz(-9, 9), d = rnz(-9, 9), plus = K.coin(), s = plus ? 1 : -1;
        var e = m(cpr(a, b) + (plus ? ' + ' : ' ' + M + ' ') + cpr(c, d));
        var w = plus ? [cxv(a + c, b - d), cxv(a - c, b + d), [m(n(a + b + c + d)), [a + b + c + d]]] : [cxv(a - c, b + d), cxv(a + c, b - d), cxv(a - c, d - b)];
        return withP(Q({ q: 'Simplify ' + e + '. Write the answer in ' + m('<i>a</i> + <i>b</i>i') + ' form.', mc: mcV(cxv(a + s * c, b + s * d), w, function () { return cxv(a + s * c + rnz(-2, 2), b + s * d + rnz(-2, 2)); }), why: [plus ? 'Add real parts and imaginary parts separately.' : 'Distribute the minus sign to <b>both</b> parts of ' + cpr(c, d) + '.', 'Real part: ' + m(n(a) + (plus ? ' + ' : ' ' + M + ' ') + sub(c) + ' = ' + n(a + s * c)) + '. Imaginary part: ' + m(n(b) + (plus ? ' + ' : ' ' + M + ' ') + sub(d) + ' = ' + n(b + s * d)) + '.', 'Result: ' + m(cx(a + s * c, b + s * d)) + '.'] }), { k: 'cx', e: e });
      },
      function () { // powers of i
        var e = ri(5, 99), v = iPow(e), idx = ((e % 4) + 4) % 4;
        var cor = [cxv(1, 0), cxv(0, 1), cxv(-1, 0), cxv(0, -1)][idx];
        var ex = m('i<sup>' + e + '</sup>');
        return withP(Q({ q: 'Simplify ' + ex + '.', mc: mcV(cor, IP), why: ['Powers of i repeat every 4: ' + m('i<sup>1</sup> = i, i<sup>2</sup> = ' + M + '1, i<sup>3</sup> = ' + M + 'i, i<sup>4</sup> = 1') + '.', e + ' ÷ 4 = ' + Math.floor(e / 4) + ' remainder ' + idx + ', so ' + m(ex + ' = (i<sup>4</sup>)<sup>' + Math.floor(e / 4) + '</sup>' + (idx === 0 ? '' : ' · ' + (idx === 1 ? 'i' : 'i<sup>' + idx + '</sup>')) + ' = ' + (idx === 0 ? '1' : idx === 1 ? 'i' : 'i<sup>' + idx + '</sup>')) + '.', 'Answer: ' + m(cx(v[0], v[1])) + '.'] }), { k: 'cx', e: ex });
      }
    ],
    [
      function () { // multiply
        var a, b, c, d;
        do { a = rnz(-7, 7); b = rnz(-7, 7); c = rnz(-7, 7); d = rnz(-7, 7); } while (a === c && b === -d);
        var e = m(cpr(a, b) + cpr(c, d)), re = a * c - b * d, im = a * d + b * c;
        return withP(Q({ q: 'Multiply ' + e + '. Write the answer in ' + m('<i>a</i> + <i>b</i>i') + ' form.', mc: mcV(cxv(re, im), [cxv(a * c + b * d, im), cxv(a * c, b * d), cxv(re, a * d - b * c)], function () { return cxv(re + rnz(-3, 3), im + rnz(-3, 3)); }), why: ['FOIL: ' + m(n(a * c) + cterm(a * d) + cterm(b * c) + (b * d < 0 ? ' ' + M + ' ' : ' + ') + (Math.abs(b * d) === 1 ? '' : Math.abs(b * d)) + 'i<sup>2</sup>') + '.', 'Replace ' + m('i<sup>2</sup>') + ' with ' + m(M + '1') + ': the last term becomes ' + m(n(-b * d)) + '.', 'Combine: ' + m(n(a * c) + ' + ' + sub(-b * d) + ' = ' + n(re)) + ' and ' + m(n(a * d) + ' + ' + sub(b * c) + ' = ' + n(im)) + ', so the product is ' + m(cx(re, im)) + '.'] }), { k: 'cx', e: e });
      },
      function () { // √−a · √−b
        var r = pick([1, 2, 3, 5]), s1 = ri(1, 6), s2 = ri(1, 6); if (r === 1 && s1 === 1) s1 = 2;
        var A = s1 * s1 * r, B = s2 * s2 * r, v = -s1 * s2 * r;
        var e = m(K.sqrt(M + A) + ' · ' + K.sqrt(M + B));
        return withP(Q({ q: 'Simplify ' + e + '.', mc: mcV([m(n(v)), [v]], [[m(n(-v)), [-v]], cxv(0, -v), cxv(0, v)]), why: ['Rewrite each radical with i first: ' + m(K.sqrt(M + A) + ' = ' + rootPos(-A)) + ' and ' + m(K.sqrt(M + B) + ' = ' + rootPos(-B)) + '.', 'Multiply: ' + m('(' + rootPos(-A) + ')(' + rootPos(-B) + ') = ' + (s1 * s2 * (r === 1 ? 1 : r)) + 'i<sup>2</sup> = ' + n(v)) + '.', 'Multiplying under one radical first, ' + m(K.sqrt(A * B) + ' = ' + n(-v)) + ', is the classic mistake.'] }), { k: 'cx', e: e });
      },
      function () { // conjugates
        var a = rnz(-9, 9), b = ri(1, 9), v = a * a + b * b;
        var e = m(cpr(a, b) + cpr(a, -b));
        return withP(Q({ q: 'Multiply ' + e + '.', mc: mcV([m(n(v)), [v]], [[m(n(a * a - b * b)), [a * a - b * b]], cxv(a * a, b * b), cxv(0, v)]), why: ['These are conjugates, so the product is ' + m('<i>a</i><sup>2</sup> + <i>b</i><sup>2</sup>') + '.', 'FOIL check: ' + m(n(a * a) + cterm(-a * b) + cterm(a * b) + ' ' + M + ' ' + (b * b === 1 ? '' : b * b) + 'i<sup>2</sup>') + '; the middle terms cancel.', m(n(a * a) + ' + ' + b * b + ' = ' + v) + ', a real number.'] }), { k: 'cx', e: e });
      },
      function () { // square
        var a = rnz(-6, 6), b = rnz(-6, 6), re = a * a - b * b, im = 2 * a * b;
        var e = m(cpr(a, b) + '<sup>2</sup>');
        return withP(Q({ q: 'Simplify ' + e + '. Write the answer in ' + m('<i>a</i> + <i>b</i>i') + ' form.', mc: mcV(cxv(re, im), [[m(n(a * a + b * b)), [a * a + b * b]], cxv(a * a + b * b, im), cxv(a * a, b * b), [m(n(re)), [re]]], function () { return cxv(re + rnz(-3, 3), im + rnz(-2, 2)); }), why: ['Square a binomial: ' + m('(<i>a</i> + <i>b</i>i)<sup>2</sup> = <i>a</i><sup>2</sup> + 2<i>ab</i>i + <i>b</i><sup>2</sup>i<sup>2</sup>') + '.', m(sub(a) + '<sup>2</sup> = ' + a * a) + ', ' + m('2(' + n(a) + ')(' + n(b) + ') = ' + n(im)) + ', and ' + m(sub(b) + '<sup>2</sup>i<sup>2</sup> = ' + n(-b * b)) + '.', 'Combine: ' + m(cx(re, im)) + '.'] }), { k: 'cx', e: e });
      }
    ],
    [
      function () { // divide
        var a, b, c, d, D, re, im;
        do {
          c = K.coin() ? 0 : rnz(-4, 4); d = rnz(-4, 4); a = ri(-8, 8); b = ri(-8, 8);
          D = c * c + d * d; re = R(a * c + b * d, D); im = R(b * c - a * d, D);
        } while ((a === 0 && b === 0) || re.d > 10 || im.d > 10 || (b === 0 && c === 0));
        var e = m(fr(cx(a, b), cx(c, d)));
        var w = [cxv(R(a * c - b * d, D), R(b * c + a * d, D)), cxv(re, im.neg())];
        if (c * c !== d * d) w.push(cxv(R(a * c + b * d, c * c - d * d), R(b * c - a * d, c * c - d * d)));
        if (c !== 0) w.push(cxv(R(a, c), R(b, d)));
        return withP(Q({ q: 'Write ' + e + ' in ' + m('<i>a</i> + <i>b</i>i') + ' form.', mc: mcV(cxv(re, im), w, function () { return cxv(re.add(rnz(-2, 2)), im.add(rnz(-2, 2))); }), why: ['Multiply the numerator and denominator by the conjugate of the denominator, ' + m(cpr(c, -d)) + '.', 'Numerator: ' + m(cpr(a, b) + cpr(c, -d) + ' = ' + cx(a * c + b * d, b * c - a * d)) + '. Denominator: ' + m(cpr(c, d) + cpr(c, -d) + ' = ' + (c ? c * c + ' + ' + d * d + ' = ' : '') + D) + '.', (D === 1 ? 'The denominator is 1, so the result is ' : 'Divide each part by ' + D + ': ') + m(cx(re, im)) + '.'] }), { k: 'cx', e: e });
      },
      function () { // sum of powers of i
        var p = ri(5, 60), q = ri(5, 60), r = ri(5, 60);
        var A = iPow(p), B = iPow(q), C = iPow(r), re = A[0] + B[0] - C[0], im = A[1] + B[1] - C[1];
        var e = m('i<sup>' + p + '</sup> + i<sup>' + q + '</sup> ' + M + ' i<sup>' + r + '</sup>');
        var A2 = iPow(p + 1), B2 = iPow(q + 1), C2 = iPow(r + 1);
        return withP(Q({ q: 'Simplify ' + e + '.', mc: mcV(cxv(re, im), [cxv(A2[0] + B2[0] - C2[0], A2[1] + B2[1] - C2[1]), cxv(A[0] + B[0] + C[0], A[1] + B[1] + C[1])], function () { return cxv(ri(-3, 3), ri(-3, 3)); }), why: ['Reduce each exponent mod 4 (powers of i repeat every 4).', m('i<sup>' + p + '</sup> = ' + cx(A[0], A[1]) + ', i<sup>' + q + '</sup> = ' + cx(B[0], B[1]) + ', i<sup>' + r + '</sup> = ' + cx(C[0], C[1])) + '.', 'Combine: ' + m('(' + cx(A[0], A[1]) + ') + (' + cx(B[0], B[1]) + ') ' + M + ' (' + cx(C[0], C[1]) + ') = ' + cx(re, im)) + '.'] }), { k: 'cx', e: e });
      },
      function () { // (a + √−s²)(c − √−t²)
        var a = rnz(-6, 6), c = rnz(-6, 6), s = ri(1, 5), t = ri(1, 5);
        var e = m('(' + n(a) + ' + ' + K.sqrt(M + s * s) + ')(' + n(c) + ' ' + M + ' ' + K.sqrt(M + t * t) + ')');
        var re = a * c + s * t, im = s * c - a * t;
        return withP(Q({ q: 'Simplify ' + e + '. Write the answer in ' + m('<i>a</i> + <i>b</i>i') + ' form.', mc: mcV(cxv(re, im), [[m(n((a - s) * (c + t))), [(a - s) * (c + t)]], cxv(a * c - s * t, im), cxv(re, a * t - s * c)], function () { return cxv(re + rnz(-3, 3), im + rnz(-3, 3)); }), why: ['Rewrite with i first: ' + m(K.sqrt(M + s * s) + ' = ' + cx(0, s)) + ' and ' + m(K.sqrt(M + t * t) + ' = ' + cx(0, t)) + '.', 'Multiply ' + m(cpr(a, s) + cpr(c, -t)) + ': ' + m(n(a * c) + cterm(-a * t) + cterm(s * c) + ' ' + M + ' ' + (s * t === 1 ? '' : s * t) + 'i<sup>2</sup>') + '.', 'Since ' + m('i<sup>2</sup> = ' + M + '1') + ': ' + m(cx(re, im)) + '.'] }), { k: 'cx', e: e });
      }
    ]
  ];
  K.lesson('1.3', { title: 'Complex Numbers', std: 'Lial 12e · Section 1.3', levels: c13 });

  /* ================= 1.4 Quadratic Equations ================= */
  var DESC = ['Two distinct rational solutions', 'Two distinct irrational solutions', 'One rational solution (a double solution)', 'Two nonreal complex solutions'];
  function dcat(D) { if (D < 0) return 3; if (D === 0) return 2; var s = Math.round(Math.sqrt(D)); return s * s === D ? 0 : 1; }
  function discQ(a, b, c, eqH, first) {
    var D = b * b - 4 * a * c, k = dcat(D);
    var why = (first ? [first] : []).concat(['Here ' + m('<i>a</i> = ' + n(a) + ', <i>b</i> = ' + n(b) + ', <i>c</i> = ' + n(c)) + '.', 'Discriminant: ' + m('<i>b</i><sup>2</sup> ' + M + ' 4<i>ac</i> = ' + sub(b) + '<sup>2</sup> ' + M + ' 4(' + n(a) + ')(' + n(c) + ') = ' + n(D)) + '.', [D + ' is a positive perfect square, so there are two distinct rational solutions.', n(D) + ' is positive but not a perfect square, so there are two distinct irrational solutions.', 'A discriminant of 0 means one rational (double) solution.', 'A negative discriminant means two nonreal complex solutions.'][k]]);
    return withP(Q({ q: 'Use the discriminant to describe the solutions of ' + eqH + '.', mc: mc(DESC[k], DESC.filter(function (z, i) { return i !== k; })), why: why }), { k: 'disc', e: eqH });
  }
  function qform(a, b, D) { return fr(n(-b) + ' ± ' + K.sqrt(n(D)), n(2 * a)); }
  function pickDisc(cat, aMax) {
    var a, b, c, t = 0;
    do { a = ri(1, aMax); b = ri(-9, 9); c = rnz(-9, 9); t++; } while (dcat(b * b - 4 * a * c) !== cat && t < 4000);
    if (dcat(b * b - 4 * a * c) !== cat) { var p = ri(1, 3), q = ri(1, 4); return [p * p, 2 * p * q, q * q]; }
    return [a, b, c];
  }
  var ALL = '(include any nonreal complex solutions)';
  var c14 = [
    [
      function () { // factor monic
        var r1, r2; do { r1 = ri(-9, 9); r2 = ri(-9, 9); } while (r1 === r2);
        var b = -(r1 + r2), c = r1 * r2, e = m(quad(1, b, c) + ' = 0');
        var fac = (r1 === 0 || r2 === 0) ? X + fp(-(r1 || r2)) : fp(-r1) + fp(-r2);
        return withP(Q({ q: 'Solve ' + e + ' by factoring.', mc: mcV(setH([r1, r2]), [setH([-r1, -r2]), setH([r1, -r2]), setH([-r1, r2])], function () { return setH([r1 + rnz(-3, 3), r2]); }), why: ['Factor: ' + m(fac + ' = 0') + ' (the numbers multiply to ' + n(c) + ' and add to ' + n(b) + ').', 'Zero-factor property: ' + m('<i>x</i> = ' + n(Math.min(r1, r2))) + ' or ' + m('<i>x</i> = ' + n(Math.max(r1, r2))) + '.', 'Solution set: ' + setH([r1, r2])[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // x² = k
        var k; do { k = pick([1, -1]) * ri(2, 100); } while (sqf(Math.abs(k))[0] === 1 && sqf(Math.abs(k))[1] === Math.abs(k) && K.coin());
        var e = m(X2 + ' = ' + n(k)), cor = pmGen(0, 4 * k, 2);
        var one = [m('{' + rootPos(k) + '}'), [rootVal(k)]];
        var w = [pmGen(0, -4 * k, 2), one, k > 0 ? setH([-k, k]) : EMPTY];
        return withP(Q({ q: 'Solve ' + e + ' ' + ALL + '.', mc: mcV(cor, w, function () { return pmGen(0, 4 * (k + rnz(-3, 3)), 2); }), why: ['Square root property: if ' + m('<i>x</i><sup>2</sup> = <i>k</i>') + ', then ' + m('<i>x</i> = ±' + K.sqrt('<i>k</i>')) + '. Do not forget the ±.', m('<i>x</i> = ±' + K.sqrt(n(k)) + ' = ±' + rootPos(k)) + '.', 'Solution set: ' + cor[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // (x − h)² = s²
        var h = rnz(-9, 9), s = ri(1, 9), e = m('(' + lin(1, -h) + ')<sup>2</sup> = ' + s * s);
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([h - s, h + s]), [setH([h + s]), setH([-h - s, -h + s]), setH([h - s * s, h + s * s])], function () { return setH([h - s + rnz(-2, 2), h + s]); }), why: ['Square root property: ' + m(lin(1, -h) + ' = ±' + s) + '.', m(lin(1, -h) + ' = ' + s) + ' gives ' + xeq(h + s) + '; ' + m(lin(1, -h) + ' = ' + M + s) + ' gives ' + xeq(h - s) + '.', 'Solution set: ' + setH([h - s, h + s])[0] + '. Dropping the ± loses a solution.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // discriminant
        var t = pickDisc(ri(0, 3), 3);
        return discQ(t[0], t[1], t[2], m(quad(t[0], t[1], t[2]) + ' = 0'));
      }
    ],
    [
      function () { // rational roots, a ≠ 1
        var q1, q2, p1, p2;
        do { q1 = ri(1, 5); q2 = ri(1, 5); p1 = rnz(-7, 7); p2 = rnz(-7, 7); }
        while ((q1 === 1 && q2 === 1) || K.gcd(p1, q1) !== 1 || K.gcd(p2, q2) !== 1 || R(p1, q1).eq(R(p2, q2)));
        var A = q1 * q2, B = -(q1 * p2 + q2 * p1), C = p1 * p2, e = m(quad(A, B, C) + ' = 0');
        var r1 = R(p1, q1), r2 = R(p2, q2);
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([r1, r2]), [setH([r1.neg(), r2.neg()]), setH([R(q1, p1), R(q2, p2)]), setH([r1, r2.neg()]), setH([p1, p2])], function () { return setH([r1.add(rnz(-2, 2)), r2]); }), why: ['Factor: ' + m('(' + lin(q1, -p1) + ')(' + lin(q2, -p2) + ') = 0') + '.', 'Set each factor equal to 0: ' + m(lin(q1, -p1) + ' = 0') + ' gives ' + xeq(r1) + '; ' + m(lin(q2, -p2) + ' = 0') + ' gives ' + xeq(r2) + '.', 'Solution set: ' + setH([r1, r2])[0] + '. (The quadratic formula gives the same result.)'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // completing the square
        var h = rnz(-6, 6), k; do { k = ri(2, 40); } while (k === h * h);
        var c = k - h * h, e = m(P([[1, X2], [2 * h, X]]) + ' = ' + n(c)), cor = pmGen(-2 * h, 4 * k, 2);
        return withP(Q({ q: 'Solve ' + e + ' by completing the square ' + ALL + '.', mc: mcV(cor, [pmGen(2 * h, 4 * k, 2), pmGen(-2 * h, 4 * c, 2), pmGen(-2 * h, 4 * (c + 4 * h * h), 2)], function () { return pmGen(-2 * h, 4 * (k + rnz(1, 5)), 2); }), why: ['Add ' + m('(' + fr(n(2 * h), 2) + ')<sup>2</sup> = ' + h * h) + ' to both sides: ' + m(P([[1, X2], [2 * h, X], [h * h, '']]) + ' = ' + n(c) + ' + ' + h * h) + '.', 'Write the left side as a square: ' + m('(' + lin(1, h) + ')<sup>2</sup> = ' + k) + '.', 'Square root property: ' + m(lin(1, h) + ' = ±' + rootPos(k)) + ', so the solution set is ' + cor[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // quadratic formula, irrational
        var a, b, c, D; do { a = ri(1, 4); b = ri(-9, 9); c = rnz(-9, 9); D = b * b - 4 * a * c; } while (dcat(D) !== 1);
        var e = m(quad(a, b, c) + ' = 0'), cor = pmGen(-b, D, 2 * a), w = [pmGen(b, D, 2 * a), pmGen(-b, D, a)];
        if (b * b + 4 * a * c !== D) w.push(pmGen(-b, b * b + 4 * a * c, 2 * a));
        return withP(Q({ q: 'Solve ' + e + ' using the quadratic formula. Give the solutions in simplest form.', mc: mcV(cor, w, function () { return pmGen(-b + rnz(-2, 2), D, 2 * a); }), why: [m('<i>a</i> = ' + n(a) + ', <i>b</i> = ' + n(b) + ', <i>c</i> = ' + n(c)) + '; ' + m('<i>b</i><sup>2</sup> ' + M + ' 4<i>ac</i> = ' + n(D)) + '.', m('<i>x</i> = ' + qform(a, b, D)) + '. The fraction bar goes under the whole numerator, including ' + m(M + '<i>b</i>') + '.', 'Simplify the radical and reduce: ' + cor[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // discriminant, not in standard form
        var t = pickDisc(ri(0, 3), 5), a = t[0], b = t[1], c = t[2];
        var eqH = m(P([[a, X2]]) + ' = ' + lin(-b, -c));
        return discQ(a, b, c, eqH, 'First write the equation in standard form: ' + m(quad(a, b, c) + ' = 0') + '.');
      }
    ],
    [
      function () { // nonreal solutions
        var a, b, c, D; do { a = ri(1, 5); b = ri(-8, 8); c = ri(1, 12); D = b * b - 4 * a * c; } while (D >= 0);
        var e = m(quad(a, b, c) + ' = 0'), cor = pmGen(-b, D, 2 * a);
        return withP(Q({ q: 'Solve ' + e + '. Write the solutions in ' + m('<i>a</i> ± <i>b</i>i') + ' form.', mc: mcV(cor, [pmGen(-b, -D, 2 * a), pmGen(b, D, 2 * a), pmGen(-b, D, a)], function () { return pmGen(-b + rnz(-2, 2), D, 2 * a); }), why: [m('<i>a</i> = ' + n(a) + ', <i>b</i> = ' + n(b) + ', <i>c</i> = ' + n(c)) + '; ' + m('<i>b</i><sup>2</sup> ' + M + ' 4<i>ac</i> = ' + n(D)) + ' &lt; 0, so the solutions are nonreal.', m('<i>x</i> = ' + qform(a, b, D)) + ', and ' + m(K.sqrt(n(D)) + ' = ' + rootPos(D)) + '.', 'Split into real and imaginary parts: ' + cor[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // (x + p)(x + q) = K
        var r1, r2, p, q, Kv;
        do { r1 = ri(-8, 8); r2 = ri(-8, 8); p = rnz(-6, 6); q = -(r1 + r2) - p; Kv = p * q - r1 * r2; } while (r1 === r2 || q === 0 || Kv === 0);
        var e = m(fp(p) + fp(q) + ' = ' + n(Kv)), b = p + q, c = p * q - Kv;
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([r1, r2]), [setH([Kv - p, Kv - q]), setH([-p, -q]), setH([-r1, -r2])], function () { return setH([r1 + rnz(-3, 3), r2]); }), why: ['Multiply out: ' + m(quad(1, p + q, p * q) + ' = ' + n(Kv)) + '. (Setting each factor equal to ' + n(Kv) + ' is not allowed; the zero-factor property needs 0.)', (Kv < 0 ? 'Add ' + n(-Kv) : 'Subtract ' + n(Kv)) + ' on both sides: ' + m(quad(1, b, c) + ' = 0') + '.', 'Factor: ' + m(fp(-r1) + fp(-r2) + ' = 0').replace(/\(<i>x<\/i>\)/g, X) + ', so the solution set is ' + setH([r1, r2])[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // value of k for exactly one solution
        if (K.coin()) {
          var s = ri(2, 7), e = m(X2 + ' + <i>kx</i> + ' + s * s + ' = 0');
          var kk = function (vals, txt) { return [txt, vals]; };
          var two = function (v) { return m('<i>k</i> = ' + n(-v)) + ' or ' + m('<i>k</i> = ' + n(v)); };
          return withP(Q({ q: 'For what value(s) of ' + m('<i>k</i>') + ' does ' + e + ' have exactly one solution?', mc: mcV(kk([-2 * s, 2 * s], two(2 * s)), [kk([2 * s], m('<i>k</i> = ' + 2 * s) + ' only'), kk([-s, s], two(s)), kk([-2 * s * s, 2 * s * s], two(2 * s * s))]), why: ['One solution means the discriminant is 0: ' + m('<i>k</i><sup>2</sup> ' + M + ' 4(1)(' + s * s + ') = 0') + '.', m('<i>k</i><sup>2</sup> = ' + 4 * s * s) + ', so ' + m('<i>k</i> = ±' + 2 * s) + '.', 'Both values work: ' + m(X2 + ' ± ' + 2 * s + '<i>x</i> + ' + s * s + ' = (<i>x</i> ± ' + s + ')<sup>2</sup>') + '.'] }), { k: 'kdisc', e: e });
        }
        var a = ri(1, 5), b = rnz(-9, 9), kv = R(b * b, 4 * a), e2 = m(P([[a, X2], [b, X]]) + ' + <i>k</i> = 0');
        var one = function (v) { return [m('<i>k</i> = ' + R(v).html()), [R(v).val()]]; };
        return withP(Q({ q: 'For what value of ' + m('<i>k</i>') + ' does ' + e2 + ' have exactly one solution?', mc: mcV(one(kv), [one(kv.neg()), one(R(b * b, 2 * a)), one(R(b, 4 * a))], function () { return one(kv.add(rnz(-3, 3))); }), why: ['One solution means ' + m('<i>b</i><sup>2</sup> ' + M + ' 4<i>ac</i> = 0') + ' with ' + m('<i>a</i> = ' + a + ', <i>b</i> = ' + n(b) + ', <i>c</i> = <i>k</i>') + '.', m(sub(b) + '<sup>2</sup> ' + M + ' 4(' + a + ')<i>k</i> = 0') + ', so ' + m(b * b + ' = ' + 4 * a + '<i>k</i>') + '.', m('<i>k</i> = ' + kv.html()) + '.'] }), { k: 'kdisc', e: e2 });
      },
      function () { // solve a formula for a variable (square root)
        var F = pick([
          [L('A = ') + 'π' + L('r^2'), 'r', sqrtF(fr(L('A'), 'π')), [fr(L('A'), 'π'), fr(K.sqrt(L('A')), 'π'), K.sqrt(L('A') + 'π')], 'Divide by π, then take the positive square root (a radius is positive).'],
          [L('s = ') + fr(1, 2) + L('gt^2'), 't', sqrtF(fr(L('2s'), L('g'))), [sqrtF(fr(L('s'), L('2g'))), fr(L('2s'), L('g')), fr(K.sqrt(L('2s')), L('g'))], 'Multiply by 2, divide by ' + m(L('g')) + ', then take the positive square root (time is positive).'],
          [L('a^2 + b^2 = c^2'), 'b', K.sqrt(L('c^2 − a^2')), [L('c − a'), K.sqrt(L('c^2 + a^2')), L('c^2 − a^2')], 'Subtract ' + m(L('a^2')) + ', then take the positive square root (a length is positive). Note that ' + m(K.sqrt(L('c^2 − a^2'))) + ' is not ' + m(L('c − a')) + '.'],
          [L('V = ') + 'π' + L('r^2h'), 'r', sqrtF(fr(L('V'), 'π' + L('h'))), [fr(L('V'), 'π' + L('h')), K.sqrt(L('V') + 'π' + L('h')), fr(K.sqrt(L('V')), 'π' + L('h'))], 'Divide by ' + m('π' + L('h')) + ', then take the positive square root (a radius is positive).'],
          [L('E = mc^2'), 'c', sqrtF(fr(L('E'), L('m'))), [fr(L('E'), L('m')), K.sqrt(L('Em')), fr(K.sqrt(L('E')), L('m'))], 'Divide by ' + m(L('m')) + ', then take the positive square root (' + m(L('c')) + ' is a positive speed).']
        ]);
        var v = L(F[1]);
        return withP(Q({ q: 'Solve ' + m(F[0]) + ' for ' + m(v) + ', where all variables are positive.', mc: mc(m(v + ' = ' + F[2]), F[3].map(function (w) { return m(v + ' = ' + w); })), why: ['Isolate ' + m(v + '<sup>2</sup>') + ' first. ' + F[4], 'Result: ' + m(v + ' = ' + F[2]) + '.', 'Check by squaring: substituting back gives the original formula.'] }), { k: 'formula', e: m(F[0]), v: F[1], pos: 1 });
      }
    ]
  ];
  K.lesson('1.4', { title: 'Quadratic Equations', std: 'Lial 12e · Section 1.4', levels: c14 });

  /* ================= 1.5 Applications and Modeling with Quadratic Equations ================= */
  var TRIP = [[3, 4, 5], [5, 12, 13], [8, 15, 17], [7, 24, 25], [20, 21, 29], [9, 12, 15]];
  function sec(v) { return [m(L('t = ') + n(v)) + (v === 1 ? ' second' : ' seconds'), [v]]; }
  var c15 = [
    [
      function () { // ladder
        var T = pick(TRIP), k = ri(1, 3), legs = K.shuffle([T[0] * k, T[1] * k]), b = legs[0], h = legs[1], c = T[2] * k;
        var ft = function (v) { return [m(n(v) + ' ft'), [v]]; };
        return withP(Q({ q: An(c) + ' ' + c + '-ft ladder leans against a wall with its base ' + b + ' ft from the wall. How high up the wall does it reach?', mc: mcV(ft(h), [ft(c + b), ft(c - b), ft(c * c - b * b)], function () { var z = h + rnz(-3, 3); return z > 0 ? ft(z) : null; }), why: ['The ladder is the hypotenuse: ' + m(L('h^2 + ') + b + '<sup>2</sup> = ' + c + '<sup>2</sup>') + '.', m(L('h^2 = ') + c * c + ' ' + M + ' ' + b * b + ' = ' + h * h) + '.', m(L('h = ') + h) + ' ft (a height is positive).'] }), { k: 'word', w: 'ladder', c: c, b: b });
      },
      function () { // ground launch
        var t = ri(2, 8), v = 16 * t, s = m(L('s = ') + quad(-16, v, 0, 't'));
        return withP(Q({ q: 'A ball is thrown straight up from ground level. Its height in feet after ' + m(L('t')) + ' seconds is ' + s + '. When does it hit the ground?', mc: mcV(sec(t), [sec(t / 2), sec(2 * t), sec(v / 32 + t)], function () { var z = t + rnz(-2, 2); return z > 0 ? sec(z) : null; }), why: ['It is on the ground when ' + m(L('s = 0')) + ': ' + m(quad(-16, v, 0, 't') + ' = 0') + '.', 'Factor: ' + m(M + '16' + L('t(t − ') + t + ') = 0') + ', so ' + m(L('t = 0')) + ' or ' + m(L('t = ') + t) + '.', m(L('t = 0')) + ' is the launch, so it lands after ' + t + ' seconds. (Halfway, ' + n(t / 2) + ' s, is when it is highest.)'] }), { k: 'word', w: 'ground', v: v });
      },
      function () { // rectangle area
        var wv = ri(3, 15), d = ri(1, 8), A = wv * (wv + d);
        var dim = function (a) { return ['Width ' + n(a) + ' ft, length ' + n(a + d) + ' ft', [a]]; };
        return withP(Q({ q: 'A rectangle’s length is ' + d + ' ft more than its width, and its area is ' + A + ' ft². Find its dimensions.', mc: mcV(dim(wv), [dim(wv + d), dim(wv - 1), dim(wv + 1)], function () { var z = wv + rnz(-4, 4); return z > 0 ? dim(z) : null; }), why: ['Let the width be ' + m(L('w')) + ': ' + m(L('w(w + ') + d + ') = ' + A) + '.', 'Standard form: ' + m(quad(1, d, -A, 'w') + ' = 0') + ', which factors as ' + m(L('(w + ') + (wv + d) + L(')(w − ') + wv + ') = 0') + '.', m(L('w = ') + M + (wv + d)) + ' is impossible for a width, so the width is ' + wv + ' ft and the length is ' + (wv + d) + ' ft.'] }), { k: 'word', w: 'area', d: d, A: A });
      },
      function () { // consecutive integers
        var a = ri(4, 20), pr = a * (a + 1);
        var pair = function (u) { return [n(u) + ' and ' + n(u + 1), [u]]; };
        return withP(Q({ q: 'The product of two consecutive positive integers is ' + pr + '. What are the integers?', mc: mcV(pair(a), [pair(-a - 1), pair(a + 1), pair(a - 1)], function () { var z = a + rnz(-4, 4); return z > 0 ? pair(z) : null; }), why: ['Let the integers be ' + m(L('n')) + ' and ' + m(L('n + 1')) + ': ' + m(L('n(n + 1) = ') + pr) + '.', m(quad(1, 1, -pr, 'n') + ' = 0') + ' factors as ' + m(L('(n + ') + (a + 1) + L(')(n − ') + a + ') = 0') + '.', 'The integers are positive, so ' + m(L('n = ') + a) + ': the integers are ' + a + ' and ' + (a + 1) + '.'] }), { k: 'word', w: 'consec', pr: pr });
      }
    ],
    [
      function () { // launch from a height
        var T, q; do { T = ri(2, 8); q = ri(1, 3); } while (T <= q);
        var v = 16 * (T - q), s0 = 16 * T * q, s = m(L('s = ') + quad(-16, v, s0, 't'));
        return withP(Q({ q: 'A ball is thrown upward from the top of ' + an(s0) + ' ' + s0 + '-ft building. Its height after ' + m(L('t')) + ' seconds is ' + s + '. When does it hit the ground?', mc: mcV(sec(T), [sec(q), sec((T - q) / 2), sec(T + q)], function () { var z = T + rnz(-2, 2); return z > 0 ? sec(z) : null; }), why: ['Set ' + m(L('s = 0')) + ' and divide by ' + m(M + '16') + ': ' + m(quad(1, -(T - q), -T * q, 't') + ' = 0') + '.', 'Factor: ' + m(L('(t − ') + T + L(')(t + ') + q + ') = 0') + ', so ' + m(L('t = ') + T) + ' or ' + m(L('t = ') + M + q) + '.', 'Time cannot be negative, so it hits the ground after ' + T + ' seconds.'] }), { k: 'word', w: 'height0', v: v, s0: s0 });
      },
      function () { // both times at a height
        var t1 = ri(1, 4), t2 = t1 + ri(1, 3), s0 = pick([0, 0, 16, 32, 48]), v = 16 * (t1 + t2), h = s0 + 16 * t1 * t2;
        var s = m(L('s = ') + quad(-16, v, s0, 't'));
        var two = function (a, b) { return [m(L('t = ') + n(a)) + ' s and ' + m(L('t = ') + n(b)) + ' s', [a, b]]; };
        var one = function (a) { return [m(L('t = ') + n(a)) + ' s only', [a]]; };
        return withP(Q({ q: 'An object’s height in feet after ' + m(L('t')) + ' seconds is ' + s + '. At what times is it ' + h + ' ft above the ground?', mc: mcV(two(t1, t2), [one(t1), one(t2), one((t1 + t2) / 2)]), why: ['Set ' + m(quad(-16, v, s0, 't') + ' = ' + h) + ', then subtract ' + h + ' and divide by ' + m(M + '16') + ': ' + m(quad(1, -(t1 + t2), t1 * t2, 't') + ' = 0') + '.', 'Factor: ' + m(L('(t − ') + t1 + L(')(t − ') + t2 + ') = 0') + '.', 'Both times make sense: ' + t1 + ' s on the way up and ' + t2 + ' s on the way down.'] }), { k: 'word', w: 'heightTimes', v: v, s0: s0, h: h });
      },
      function () { // legs x and x + d
        var T = pick(TRIP.slice(0, 5)), k = T[2] <= 13 ? ri(1, 2) : 1, a = T[0] * k, b = T[1] * k, c = T[2] * k, d = b - a;
        var pr = function (u) { return [n(u) + ' and ' + n(u + d), [u]]; };
        return withP(Q({ q: 'A right triangle has legs ' + m(X) + ' and ' + m(lin(1, d)) + ' and hypotenuse ' + c + '. Find the lengths of the legs.', mc: mcV(pr(a), [pr(b), pr(c - d), pr(a + 1)], function () { var z = a + rnz(-3, 3); return z > 0 ? pr(z) : null; }), why: ['Pythagorean theorem: ' + m(X2 + ' + (' + lin(1, d) + ')<sup>2</sup> = ' + c + '<sup>2</sup>') + '.', 'Expand: ' + m(quad(2, 2 * d, d * d - c * c) + ' = 0') + '; divide by 2: ' + m(quad(1, d, (d * d - c * c) / 2) + ' = 0') + ', so ' + m('(' + lin(1, b) + ')(' + lin(1, -a) + ') = 0') + '.', 'A length is positive, so ' + xeq(a) + ': the legs are ' + a + ' and ' + b + '.'] }), { k: 'word', w: 'legs', d: d, c: c });
      },
      function () { // uniform border
        var Lg = ri(6, 20), Wg = ri(6, 20), x = pick([1, 1.5, 2, 2.5, 3, 4]), T = (Lg + 2 * x) * (Wg + 2 * x);
        var ft = function (v) { return [m(n(v) + ' ft'), [v]]; };
        return withP(Q({ q: An(Wg) + ' ' + Wg + ' ft by ' + Lg + ' ft garden is surrounded by a border of uniform width ' + m(X) + '. The garden and border together cover ' + n(T) + ' ft². How wide is the border?', mc: mcV(ft(x), [ft(2 * x), ft(x / 2), ft(x + 1)], function () { return ft(x + pick([-0.5, 0.5, 1.5, 2])); }), why: ['With the border, the outer dimensions are ' + m('(' + lin(2, Wg) + ')') + ' and ' + m('(' + lin(2, Lg) + ')') + ': ' + m('(' + lin(2, Wg) + ')(' + lin(2, Lg) + ') = ' + n(T)) + '.', 'Expand: ' + m(quad(4, 2 * (Lg + Wg), Lg * Wg - T) + ' = 0') + '. Solve (by factoring or the quadratic formula).', 'The positive solution is ' + xeq(x) + ' ft; the negative one is rejected. Check: ' + m(n(Wg + 2 * x) + ' × ' + n(Lg + 2 * x) + ' = ' + n(T)) + ' ✓'] }), { k: 'word', w: 'border', Lg: Lg, Wg: Wg, T: T });
      }
    ],
    [
      function () { // round to nearest tenth
        var v, s0, rt, fa;
        do { v = ri(20, 90); s0 = ri(5, 100); rt = (v + Math.sqrt(v * v + 64 * s0)) / 32; fa = Math.abs(rt * 10 - Math.floor(rt * 10) - 0.5); } while (fa < 0.05 || nint(Math.sqrt(v * v + 64 * s0)));
        var r1 = function (x) { return Math.round(x * 10) / 10; };
        var tc = function (x) { return ['About ' + r1(x).toFixed(1) + ' seconds', [r1(x)]]; };
        var other = (Math.sqrt(v * v + 64 * s0) - v) / 32, D = v * v + 64 * s0;
        return withP(Q({ q: 'A rock is thrown upward from ' + an(s0) + ' ' + s0 + '-ft cliff. Its height in feet after ' + m(L('t')) + ' seconds is ' + m(L('s = ') + quad(-16, v, s0, 't')) + '. When does it hit the ground below? Round to the nearest tenth of a second.', mc: mcV(tc(rt), [tc(other), tc(v / 32), tc(v / 16)], function () { return tc(rt + pick([-0.4, -0.2, 0.2, 0.4, 0.6])); }), why: ['Set ' + m(quad(-16, v, s0, 't') + ' = 0') + ' and use the quadratic formula with ' + m('<i>a</i> = ' + M + '16, <i>b</i> = ' + v + ', <i>c</i> = ' + s0) + '.', m(L('t = ') + fr(M + v + ' ± ' + K.sqrt(v + '<sup>2</sup> + 64(' + s0 + ')'), M + '32')) + ' ' + m('= ' + fr(M + v + ' ± ' + K.sqrt(D), M + '32')) + '.', 'The solutions are about ' + m(n(K.round(-other, 2))) + ' and ' + m(n(K.round(rt, 2))) + '. Reject the negative time: about ' + r1(rt).toFixed(1) + ' seconds.'] }), { k: 'word', w: 'cliff', v: v, s0: s0 });
      },
      function () { // open box
        var c = ri(1, 4), b = ri(4, 14), S = b + 2 * c, V = c * b * b;
        var inch = function (v) { return [m(n(v) + ' in.'), [v]]; };
        return withP(Q({ q: 'Squares ' + c + ' in. on a side are cut from each corner of a square sheet of metal, and the sides are folded up to make an open box with volume ' + V + ' in³. What was the side length of the original sheet?', mc: mcV(inch(S), [inch(b), inch(b + c), inch(b + 4 * c)], function () { return inch(S + rnz(-3, 3)); }), why: ['If the sheet has side ' + X + ', the base is ' + m(lin(1, -2 * c)) + ' on a side and the height is ' + c + ': ' + m(cpar(c) + '(' + lin(1, -2 * c) + ')<sup>2</sup> = ' + V) + '.', (c === 1 ? 'Take the square root: ' : m('(' + lin(1, -2 * c) + ')<sup>2</sup> = ' + b * b) + ', so ') + m(lin(1, -2 * c) + ' = ' + b) + ' (the negative root gives a negative length).', xeq(S) + ': the sheet was ' + S + ' in. on a side.'] }), { k: 'word', w: 'box', c: c, V: V });
      },
      function () { // perimeter and area
        var wv, Lv; do { wv = ri(4, 25); Lv = ri(5, 30); } while (Lv <= wv);
        var Pv = 2 * (wv + Lv), A = wv * Lv, half = wv + Lv;
        var dim = function (a, b) { return [n(a) + ' m by ' + n(b) + ' m', [a, b * 1000]]; };
        return withP(Q({ q: 'A rectangular lot has a perimeter of ' + Pv + ' m and an area of ' + A + ' m². What are its dimensions?', mc: mcV(dim(wv, Lv), [dim(wv + 1, Lv - 1), dim(wv - 1, Lv + 1), dim(half / 2, half / 2)], function () { var z = wv + rnz(-4, 4); return z > 0 && z < half - z ? dim(z, half - z) : null; }), why: ['Width ' + m(L('w')) + ', length ' + m(half + ' ' + M + ' ' + L('w')) + ' (half the perimeter is ' + half + ').', m(L('w(') + half + ' ' + M + ' ' + L('w) = ') + A) + ' gives ' + m(quad(1, -half, A, 'w') + ' = 0') + ', so ' + m(L('(w − ') + wv + L(')(w − ') + Lv + ') = 0') + '.', 'Either root gives the same rectangle: ' + wv + ' m by ' + Lv + ' m. Check: ' + m(wv + ' × ' + Lv + ' = ' + A) + ' ✓'] }), { k: 'word', w: 'lot', P: Pv, A: A });
      },
      function () { // on the way down
        var t1 = ri(1, 4), t2 = t1 + ri(1, 4), s0 = pick([16, 32, 48, 64, 80]), v = 16 * (t1 + t2), h = s0 + 16 * t1 * t2;
        return withP(Q({ q: 'A ball is thrown upward from ' + an(s0) + ' ' + s0 + '-ft platform. Its height in feet after ' + m(L('t')) + ' seconds is ' + m(L('s = ') + quad(-16, v, s0, 't')) + '. At what time is the ball ' + h + ' ft high <b>on its way down</b>?', mc: mcV(sec(t2), [sec(t1), sec((t1 + t2) / 2), sec(t1 + t2)]), why: ['Set ' + m(quad(-16, v, s0, 't') + ' = ' + h) + ': ' + m(quad(-16, v, s0 - h, 't') + ' = 0') + '.', 'Divide by ' + m(M + '16') + ' and factor: ' + m(L('(t − ') + t1 + L(')(t − ') + t2 + ') = 0') + '.', 'The ball passes ' + h + ' ft at ' + t1 + ' s going up and at ' + t2 + ' s coming down, so the answer is ' + t2 + ' seconds.'] }), { k: 'word', w: 'down', v: v, s0: s0, h: h });
      }
    ]
  ];
  K.lesson('1.5', { title: 'Applications and Modeling with Quadratic Equations', std: 'Lial 12e · Section 1.5', levels: c15 });

  /* ================= 1.6 Other Types of Equations and Applications ================= */
  function sx(v) { return v === null ? EMPTY : setH([v]); }
  var c16 = [
    [
      function () { // A/x + B/k = C/k
        var x0, k, eD, A, B, C;
        do { x0 = rnz(-9, 9); k = ri(2, 6); eD = rnz(-5, 5); A = x0 * eD / k; } while (!nint(A) || A === 0);
        B = rnz(-5, 5); C = B + eD;
        var e = m((A < 0 ? M : '') + fr(n(Math.abs(A)), X) + (B > 0 ? ' + ' : ' ' + M + ' ') + R(Math.abs(B), k).html() + ' = ' + R(C, k).html());
        var Lk = K.lcm(R(B, k).d, R(C, k).d);
        var w = [setH([-x0]), setH([R(A, eD)])]; if (C + B !== 0) w.push(setH([R(k * A, C + B)]));
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([x0]), w, function () { var z = x0 + rnz(-4, 4); return z ? setH([z]) : null; }), why: ['Note ' + m('<i>x</i> ≠ 0') + '. ' + (Lk === 1 ? 'Multiply every term by ' + X : 'The LCD is ' + m(Lk + X) + '. Multiply every term by ' + m(Lk + X)) + ': ' + m(n(A * Lk) + cont([[B * Lk / k, X]]) + ' = ' + P([[C * Lk / k, X]])) + '.', 'Collect the ' + X + '-terms: ' + m(n(A * Lk) + ' = ' + P([[eD * Lk / k, X]])) + (eD * Lk / k === 1 ? '' : ', so ' + xeq(x0)) + '.', n(x0) + ' is not excluded, so the solution set is ' + setH([x0])[0] + '.'] }), { k: 'solve', e: e });
      },
      function () { // √(ax + b) = c
        var a = ri(1, 5), x0 = ri(-5, 12), c = ri(1, 9), b = c * c - a * x0, neg = ri(1, 5) === 1;
        var cc = neg ? -c : c, e = m(K.sqrt(lin(a, b)) + ' = ' + n(cc)), xs = R(c * c - b, a);
        if (!neg) return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([xs]), [setH([R(c - b, a)]), setH([R(c * c + b, a)]), EMPTY], function () { return setH([xs.add(rnz(-3, 3))]); }), why: ['Square both sides: ' + m(lin(a, b) + ' = ' + c * c) + '.', (a === 1 ? 'Solve: ' + xeq(xs) + '.' : 'Solve: ' + m(P([[a, X]]) + ' = ' + n(c * c - b)) + ', so ' + xeq(xs) + '.'), 'Check: ' + m(K.sqrt(n(a * xs.val() + b)) + ' = ' + c) + ' ✓. Solution set ' + setH([xs])[0] + '.'] }), { k: 'solve', e: e });
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(EMPTY, [setH([xs]), setH([R(-c - b, a)]), setH([R(-c * c - b, a)])], function () { return setH([xs.add(rnz(-4, 4))]); }), why: ['A principal square root is never negative, so it cannot equal ' + n(cc) + '.', 'Squaring gives ' + xeq(xs) + ', but the check fails: ' + m(K.sqrt(n(a * xs.val() + b)) + ' = ' + c + ' ≠ ' + n(cc)) + '.', 'The solution set is ∅.'] }), { k: 'solve', e: e });
      },
      function () { // work together
        var a, b, t; do { a = ri(2, 12); b = ri(2, 12); t = a * b / (a + b); } while (a === b || !dec2(t));
        var nm = pick(NAMES), hr = function (v) { return [m(pl(v, 'hour')), [v]]; };
        return withP(Q({ q: nm[0] + ' can paint a room in ' + a + ' hours, and ' + nm[1] + ' can paint it in ' + b + ' hours. How long does it take them working together?', mc: mcV(hr(t), [hr((a + b) / 2), hr(a + b), hr(Math.abs(a - b)), hr(Math.min(a, b))], function () { var z = t + pick([-1, 1, 0.5, -0.5, 2]); return z > 0 ? hr(z) : null; }), why: ['Rates: ' + nm[0] + ' paints ' + m(fr(1, a)) + ' of the room per hour and ' + nm[1] + ' paints ' + m(fr(1, b)) + '.', 'Together: ' + m(fr(1, a) + ' + ' + fr(1, b) + ' = ' + R(a + b, a * b).html()) + ' of the room per hour.', 'Time = ' + m('1 ÷ ' + R(a + b, a * b).html() + ' = ' + R(a * b, a + b).html() + (nint(t) ? '' : ' = ' + n(t))) + ' ' + (t === 1 ? 'hour' : 'hours') + ' (faster than either person alone).'] }), { k: 'word', w: 'work', a: a, b: b });
      },
      function () { // excluded values
        var p, q; do { p = rnz(-7, 7); q = rnz(-7, 7); } while (p === -q);
        var A = ri(1, 6), B = ri(1, 6), C = ri(1, 9);
        var e = m(fr(n(A), lin(1, -p)) + ' ' + M + ' ' + fr(n(B), lin(1, q)) + ' = ' + C);
        var ex = function (vals) { vals = vals.slice().sort(function (u, v) { return u - v; }); return [vals.map(function (v) { return m('<i>x</i> ≠ ' + n(v)); }).join(' and '), vals]; };
        return withP(Q({ q: 'Which values of ' + X + ' must be excluded as possible solutions of ' + e + '?', mc: mcV(ex([p, -q]), [ex([-p, q]), ex([p]), ex([0]), ex([-q])]), why: ['A solution can never make a denominator 0.', m(lin(1, -p) + ' = 0') + ' when ' + xeq(p) + ', and ' + m(lin(1, q) + ' = 0') + ' when ' + xeq(-q) + '.', 'So ' + m('<i>x</i> ≠ ' + n(Math.min(p, -q))) + ' and ' + m('<i>x</i> ≠ ' + n(Math.max(p, -q))) + '.'] }), { k: 'excl', e: e });
      }
    ],
    [
      function () { // radical with an extraneous root
        var r1, r2, e, steps;
        if (K.coin()) {
          var q, p; do { r1 = ri(-2, 10); r2 = ri(-8, 6); } while (r1 - r2 < 3 || (r1 + r2) % 2 === 0);
          q = (r1 + r2 - 1) / 2; p = q * q - r1 * r2;
          e = m(K.sqrt(lin(1, p)) + K.plusK(q) + ' = ' + X);
          steps = ['Isolate the radical: ' + m(K.sqrt(lin(1, p)) + ' = ' + lin(1, -q)) + '.', 'Square both sides: ' + m(lin(1, p) + ' = ' + quad(1, -2 * q, q * q)) + ', so ' + m(quad(1, -(r1 + r2), r1 * r2) + ' = 0') + ' and ' + m('<i>x</i> = ' + n(r1)) + ' or ' + m('<i>x</i> = ' + n(r2)) + '.', 'Check: ' + xeq(r1) + ' gives ' + m(K.sqrt(n(r1 + p)) + K.plusK(q) + ' = ' + n(r1)) + ' ✓; ' + xeq(r2) + ' gives ' + m(K.sqrt(n(r2 + p)) + K.plusK(q) + ' = ' + n(Math.sqrt(r2 + p) + q) + ' ≠ ' + n(r2)) + ' ✗. Solution set ' + setH([r1])[0] + '.'];
        } else {
          do { r1 = ri(1, 9); r2 = -ri(1, 6); } while (r1 + r2 === 0);
          var a = r1 + r2, b = -r1 * r2;
          e = m(K.sqrt(lin(a, b)) + ' = ' + X);
          steps = ['Square both sides: ' + m(lin(a, b) + ' = ' + X2) + ', so ' + m(quad(1, -a, -b) + ' = 0') + '.', 'Factor: ' + m(fp(-r1) + fp(-r2) + ' = 0') + ', so ' + m('<i>x</i> = ' + n(r1)) + ' or ' + m('<i>x</i> = ' + n(r2)) + '.', 'Check: ' + m(K.sqrt(n(a * r1 + b)) + ' = ' + r1) + ' ✓, but ' + m(K.sqrt(n(a * r2 + b)) + ' = ' + (-r2) + ' ≠ ' + n(r2)) + ' ✗ (a square root cannot be negative). Solution set ' + setH([r1])[0] + '.'];
        }
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([r1]), [setH([r1, r2]), setH([r2]), EMPTY]), why: steps }), { k: 'solve', e: e });
      },
      function () { // x⁴ − (a² + b²)x² + a²b² = 0
        var a, b; do { a = ri(1, 5); b = ri(1, 5); } while (a >= b);
        var e = m(P([[1, X4], [-(a * a + b * b), X2], [a * a * b * b, '']]) + ' = 0');
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([-b, -a, a, b]), [setH([a * a, b * b]), setH([a, b]), setH([-b * b, -a * a, a * a, b * b])]), why: ['Let ' + m('<i>u</i> = ' + X2) + ': ' + m(P([[1, '<i>u</i><sup>2</sup>'], [-(a * a + b * b), '<i>u</i>'], [a * a * b * b, '']]) + ' = 0') + '.', 'Factor: ' + m('(<i>u</i> ' + M + ' ' + a * a + ')(<i>u</i> ' + M + ' ' + b * b + ') = 0') + ', so ' + m('<i>u</i> = ' + a * a) + ' or ' + m('<i>u</i> = ' + b * b) + '.', 'Replace ' + m('<i>u</i>') + ' with ' + m(X2) + ': ' + m('<i>x</i> = ±' + a) + ' or ' + m('<i>x</i> = ±' + b) + '. Four solutions: ' + setH([-b, -a, a, b])[0] + '.'] }), { k: 'solve', e: e, dom: 'C' });
      },
      function () { // rational exponent
        var t = pick([[2, 3], [3, 2], [4, 3], [3, 4]]), mm = t[0], nn = t[1], s = mm * nn >= 12 ? ri(2, 3) : ri(2, 4), xv = Math.pow(s, nn), k = Math.pow(s, mm), even = mm % 2 === 0;
        var e = m(X + '<sup>' + mm + '/' + nn + '</sup> = ' + k);
        var cor = even ? setH([-xv, xv]) : setH([xv]);
        var w = even ? [setH([xv]), setH([-Math.pow(s, mm), Math.pow(s, mm)]), setH([-k * k, k * k])] : [setH([-xv, xv]), setH([Math.pow(s, mm)]), setH([k * k])];
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(cor, w), why: ['Write ' + m(X + '<sup>' + mm + '/' + nn + '</sup> = (' + X + '<sup>1/' + nn + '</sup>)<sup>' + mm + '</sup>') + ', so ' + m('(' + X + '<sup>1/' + nn + '</sup>)<sup>' + mm + '</sup> = ' + k) + '.', even ? 'Take the ' + (mm === 2 ? 'square' : 'fourth') + ' root (±): ' + m(X + '<sup>1/' + nn + '</sup> = ±' + s) + '. Raise to the power ' + nn + ': ' + m('<i>x</i> = ±' + xv) + '.' : 'Take the cube root: ' + m(X + '<sup>1/' + nn + '</sup> = ' + s) + ' (an even root cannot be negative). Raise to the power ' + nn + ': ' + xeq(xv) + '.', 'Check in the original equation; solution set ' + cor[0] + '.'] }), { k: 'ratexp', mm: mm, nn: nn, kk: k, e: e });
      },
      function () { // rational equation with an excluded root
        var a = rnz(-6, 6), e, cor, w, steps;
        if (K.coin()) {
          var b; do { b = rnz(-6, 6); } while (b === -a || -a - b === a);
          var r = -a - b, num = a * a + a * b;
          e = m(fr(P([[1, X2], [b, X]]), lin(1, -a)) + ' = ' + fr(n(num), lin(1, -a)));
          cor = setH([r]); w = [setH([a, r]), setH([a]), EMPTY];
          steps = ['Excluded value: ' + m('<i>x</i> ≠ ' + n(a)) + '. Multiply both sides by ' + m(lin(1, -a)) + ': ' + m(P([[1, X2], [b, X]]) + ' = ' + n(num)) + '.', m(quad(1, b, -num) + ' = 0') + ' factors as ' + m(fp(-a) + fp(-r) + ' = 0') + ', so ' + m('<i>x</i> = ' + n(a)) + ' or ' + m('<i>x</i> = ' + n(r)) + '.', n(a) + ' is excluded (it makes a denominator 0), so the solution set is ' + cor[0] + '.'];
        } else {
          var k = pick([2, 3, 4]);
          e = m(fr(X, lin(1, -a)) + ' = ' + fr(n(a), lin(1, -a)) + ' + ' + k);
          cor = EMPTY; w = [setH([a]), setH([-a]), setH([a + k])];
          steps = ['Excluded value: ' + m('<i>x</i> ≠ ' + n(a)) + '. Multiply every term by ' + m(lin(1, -a)) + ': ' + m('<i>x</i> = ' + n(a) + ' + ' + k + '(' + lin(1, -a) + ')') + '.', 'Solve: ' + m('<i>x</i> = ' + lin(k, a - k * a)) + ', so ' + m(P([[1 - k, X]]) + ' = ' + n(a - k * a)) + ' and ' + xeq(a) + '.', n(a) + ' is excluded, so there is no solution: ∅.'];
        }
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(cor, w, function () { return setH([a + rnz(-5, 5)]); }), why: steps }), { k: 'solve', e: e });
      }
    ],
    [
      function () { // two radicals
        var a, b, c, d, x0, x1, ok, K2, A2, B2, C2, g, D2, u, v;
        do {
          a = ri(2, 4); d = ri(1, 2); v = ri(0, 5); u = v + d; x0 = ri(-3, 8); c = v * v - x0; b = u * u - a * x0;
          K2 = b - c - d * d; A2 = (a - 1) * (a - 1); B2 = 2 * (a - 1) * K2 - 4 * d * d; C2 = K2 * K2 - 4 * d * d * c;
          D2 = B2 * B2 - 4 * A2 * C2; ok = D2 >= 0 && nint(Math.sqrt(D2));
          if (ok) { var sD = Math.round(Math.sqrt(D2)), ra = R(-B2 + sD, 2 * A2), rb = R(-B2 - sD, 2 * A2); x1 = ra.eq(x0) ? rb : ra; ok = x1.isInt(); }
        } while (!ok || b === 0 || c === 0);
        x1 = x1.n;
        var valid = function (x) { return a * x + b >= 0 && x + c >= 0 && (a - 1) * x + K2 >= 0; };
        var sol = [x0]; if (x1 !== x0 && valid(x1)) sol.push(x1);
        g = K.gcd(K.gcd(A2, B2), C2);
        var e = m(K.sqrt(lin(a, b)) + ' ' + M + ' ' + K.sqrt(lin(1, c)) + ' = ' + d);
        var chk = function (x) { var ok2 = valid(x); return xeq(x) + (ok2 ? ' ✓' : ' ✗ (extraneous)'); };
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH(sol), [setH([x0, x1]), setH([x1]), setH([x0]), EMPTY], function () { return setH([x0 + rnz(-3, 3)]); }), why: ['Isolate one radical: ' + m(K.sqrt(lin(a, b)) + ' = ' + d + ' + ' + K.sqrt(lin(1, c))) + '. Square: ' + m(lin(a, b) + ' = ' + (d * d) + ' + ' + (2 * d) + K.sqrt(lin(1, c)) + ' + ' + lin(1, c)) + '.', 'Isolate the remaining radical: ' + m(lin(a - 1, K2) + ' = ' + 2 * d + K.sqrt(lin(1, c))) + '. Square again: ' + m(quad(A2 / g, B2 / g, C2 / g) + ' = 0') + ', so ' + m('<i>x</i> = ' + n(x0)) + (x1 !== x0 ? ' or ' + m('<i>x</i> = ' + n(x1)) : '') + '.', 'Check each in the original equation: ' + chk(x0) + (x1 !== x0 ? '; ' + chk(x1) : '') + '. Solution set ' + setH(sol)[0] + '.'] }), { k: 'solve', e: e });
      },
      function () { // quadratic in form
        if (K.coin()) {
          var u1, u2; do { u1 = rnz(-4, 4); u2 = rnz(-4, 4); } while (u1 === u2 || u1 + u2 === 0 || (Math.abs(u1) === 1 && Math.abs(u2) === 1));
          var e = m(X + '<sup>2/3</sup>' + cont([[-(u1 + u2), X + '<sup>1/3</sup>'], [u1 * u2, '']]) + ' = 0');
          var cub = function (z) { return z * z * z; };
          return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(setH([cub(u1), cub(u2)]), [setH([u1, u2]), setH([-cub(u1), -cub(u2)]), setH([u1 * u1, u2 * u2])], function () { return setH([cub(u1) + rnz(-3, 3), cub(u2)]); }), why: ['Let ' + m('<i>u</i> = ' + X + '<sup>1/3</sup>') + ', so ' + m('<i>u</i><sup>2</sup> = ' + X + '<sup>2/3</sup>') + ': ' + m(P([[1, '<i>u</i><sup>2</sup>'], [-(u1 + u2), '<i>u</i>'], [u1 * u2, '']]) + ' = 0') + '.', 'Factor: ' + m('(<i>u</i>' + K.plusK(-u1) + ')(<i>u</i>' + K.plusK(-u2) + ') = 0') + ', so ' + m('<i>u</i> = ' + n(u1)) + ' or ' + m('<i>u</i> = ' + n(u2)) + '.', 'Cube to undo ' + m(X + '<sup>1/3</sup>') + ': ' + m('<i>x</i> = ' + n(cub(u1))) + ' or ' + m('<i>x</i> = ' + n(cub(u2))) + '. Both check, so the solution set is ' + setH([cub(u1), cub(u2)])[0] + '.'] }), { k: 'ratexp2', u1: u1, u2: u2, e: e });
        }
        var p, q; do { p = ri(1, 5); q = ri(1, 5); } while (p === q);
        var e2 = m(P([[1, X4], [q * q - p * p, X2], [-p * p * q * q, '']]) + ' = 0');
        var iq = function (s) { return (s < 0 ? M : '') + (Math.abs(s) === 1 ? '' : Math.abs(s)) + 'i'; };
        var cset = function (r, im) { return [m('{' + [n(-r), n(r), iq(-im), iq(im)].join(', ') + '}'), [-r, r, [0, -im], [0, im]]]; };
        return withP(Q({ q: 'Find all complex solutions of ' + e2 + '.', mc: mcV(cset(p, q), [setH([-p, p]), setH([-q * q, p * p]), cset(q, p)]), why: ['Let ' + m('<i>u</i> = ' + X2) + ': ' + m(P([[1, '<i>u</i><sup>2</sup>'], [q * q - p * p, '<i>u</i>'], [-p * p * q * q, '']]) + ' = 0') + ', which factors as ' + m('(<i>u</i> ' + M + ' ' + p * p + ')(<i>u</i> + ' + q * q + ') = 0') + '.', m(X2 + ' = ' + p * p) + ' gives ' + m('<i>x</i> = ±' + p) + '; ' + m(X2 + ' = ' + M + q * q) + ' gives ' + m('<i>x</i> = ±' + iq(q)) + '.', 'Four solutions: ' + cset(p, q)[0] + '.'] }), { k: 'solve', e: e2, dom: 'C' });
      },
      function () { // work: unknown time, or fill and drain
        var hr = function (v) { return [m(pl(v, 'hour')), [v]]; };
        if (K.coin()) {
          var a, B, T; do { a = ri(2, 12); B = ri(2, 20); T = a * B / (a + B); } while (a === B || !nint(T * 10));
          var w = []; [a - T, 2 * T, a + T].forEach(function (v) { if (v > 0 && dec2(v)) w.push(hr(v)); });
          return withP(Q({ q: 'Working together, two pumps empty a pool in ' + n(T) + ' hours. The first pump alone takes ' + a + ' hours. How long would the second pump take alone?', mc: mcV(hr(B), w, function () { var z = B + rnz(-4, 4); return z > 0 ? hr(z) : null; }), why: ['Let ' + X + ' be the second pump’s time. Rates add: ' + m(fr(1, a) + ' + ' + fr(1, X) + ' = ' + fr(1, n(T))) + '.', m(fr(1, X) + ' = ' + fr(1, n(T)) + ' ' + M + ' ' + fr(1, a) + ' = ' + R(1, B).html()) + '.', 'So ' + xeq(B) + ' hours.'] }), { k: 'word', w: 'workB', a: a, T: T });
        }
        var f, dr, t; do { f = ri(2, 10); dr = ri(3, 20); t = f * dr / (dr - f); } while (dr <= f || !dec2(t));
        var w2 = []; [f * dr / (f + dr), dr - f, (f + dr) / 2].forEach(function (v) { if (v > 0 && dec2(v)) w2.push(hr(v)); });
        return withP(Q({ q: 'An inlet pipe fills a tank in ' + f + ' hours. A drain empties the full tank in ' + dr + ' hours. If both are open, how long does it take to fill the empty tank?', mc: mcV(hr(t), w2, function () { var z = t + rnz(-3, 3); return z > 0 ? hr(z) : null; }), why: ['The inlet adds ' + m(fr(1, f)) + ' of the tank per hour; the drain removes ' + m(fr(1, dr)) + '.', 'Net rate: ' + m(fr(1, f) + ' ' + M + ' ' + fr(1, dr) + ' = ' + R(dr - f, f * dr).html()) + ' of the tank per hour.', 'Time = ' + m('1 ÷ ' + R(dr - f, f * dr).html() + ' = ' + n(t)) + ' hours.'] }), { k: 'word', w: 'drain', f: f, dr: dr });
      },
      function () { // p/(x − a) + q/(x + a) = k/(x² − a²)
        var a = ri(1, 6), p, q, x0, k, mode = ri(0, 3);
        do { p = rnz(-4, 4); q = rnz(-4, 4); x0 = mode === 0 ? pick([a, -a]) : rnz(-9, 9); k = (p + q) * x0 + p * a - q * a; } while (p + q === 0 || k === 0 || (mode !== 0 && Math.abs(x0) === a));
        var bad = Math.abs(x0) === a;
        var e = m((p < 0 ? M : '') + fr(n(Math.abs(p)), lin(1, -a)) + (q < 0 ? ' ' + M + ' ' : ' + ') + fr(n(Math.abs(q)), lin(1, a)) + ' = ' + (k < 0 ? M : '') + fr(n(Math.abs(k)), quad(1, 0, -a * a)));
        var cor = bad ? EMPTY : setH([x0]);
        var w = [setH([x0]), setH([R(k, p + q)]), bad ? setH([-x0]) : EMPTY, setH([-a, a])];
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(cor, w, function () { var z = x0 + rnz(-3, 3); return setH([z]); }), why: ['Factor ' + m(quad(1, 0, -a * a) + ' = ' + fp(-a) + fp(a)) + ', so ' + m('<i>x</i> ≠ ' + a) + ' and ' + m('<i>x</i> ≠ ' + M + a) + '.', 'Multiply every term by ' + m(fp(-a) + fp(a)) + ': ' + m(cpar(p) + fp(a) + (q < 0 ? ' ' + M + ' ' + cpar(-q) : ' + ' + cpar(q)) + fp(-a) + ' = ' + n(k)) + ', so ' + m(lin(p + q, p * a - q * a) + ' = ' + n(k)) + ' and ' + xeq(x0) + '.', bad ? n(x0) + ' is an excluded value, so there is no solution: ∅.' : n(x0) + ' is not excluded, so the solution set is ' + cor[0] + '.'] }), { k: 'solve', e: e });
      }
    ]
  ];
  K.lesson('1.6', { title: 'Other Types of Equations and Applications', std: 'Lial 12e · Section 1.6', levels: c16 });

  /* ================= 1.7 Inequalities ================= */
  function linIneq(a, b, sym, c) { return m(lin(a, b) + ' ' + SYM[sym] + ' ' + n(c)); }
  function intervalTests(crit, f) { // describe test points
    var c = crit.slice().sort(function (u, v) { return R(u).val() - R(v).val(); }), pts = [R(c[0]).sub(1)];
    for (var i = 0; i + 1 < c.length; i++) pts.push(R(c[i]).add(R(c[i + 1])).div(2));
    pts.push(R(c[c.length - 1]).add(1));
    return pts.map(function (t) { var v = f(t); return m('<i>x</i> = ' + t.html()) + ': ' + (v ? '✓' : '✗'); }).join('; ');
  }
  var c17 = [
    [
      function () { // linear, maybe flip
        var a = pick([-6, -5, -4, -3, -2, 2, 3, 4, 5, 6]), b = rnz(-9, 9), x0 = ri(-8, 8), c = a * x0 + b, sym = pick(['<', '<=', '>', '>=']);
        var s2 = a < 0 ? FLIP[sym] : sym, dir = (s2 === '>' || s2 === '>=') ? 1 : -1, cl = s2.length === 2;
        var e = linIneq(a, b, sym, c), cor = ray(x0, dir, cl);
        var w = [ray(x0, -dir, cl), ray(x0, dir, !cl), x0 !== 0 ? ray(-x0, dir, cl) : ray(x0, -dir, !cl)];
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w), why: [(b > 0 ? 'Subtract ' + b : 'Add ' + (-b)) + ' on both sides: ' + m(P([[a, X]]) + ' ' + SYM[sym] + ' ' + n(c - b)) + '.', 'Divide by ' + n(a) + (a < 0 ? ' and <b>reverse</b> the symbol (dividing by a negative)' : '') + ': ' + m('<i>x</i> ' + SYM[s2] + ' ' + n(x0)) + '.', 'Interval notation: ' + cor + (cl ? ' (bracket: ' + n(x0) + ' is included).' : ' (parenthesis: ' + n(x0) + ' is not included).')] }), { k: 'ineq', e: e });
      },
      function () { // three-part, positive coefficient
        var a = ri(2, 5), b = rnz(-8, 8), x1 = ri(-6, 3), x2 = x1 + ri(2, 7), s1 = pick(['<', '<=']), s2 = pick(['<', '<=']);
        var lo = a * x1 + b, hi = a * x2 + b, e = m(n(lo) + ' ' + SYM[s1] + ' ' + lin(a, b) + ' ' + SYM[s2] + ' ' + n(hi));
        var c1 = s1 === '<=', c2 = s2 === '<=', cor = m(ivl(x1, c1, x2, c2));
        var w = [m(ivl(x1, !c1, x2, !c2)), m(ivl(R(lo + b, a), c1, R(hi + b, a), c2)), m(ivl(lo - b, c1, hi - b, c2))];
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w, function () { return m(ivl(x1 + rnz(-2, 2), c1, x2, c2)); }), why: [(b > 0 ? 'Subtract ' + b : 'Add ' + (-b)) + ' in all three parts: ' + m(n(lo - b) + ' ' + SYM[s1] + ' ' + a + X + ' ' + SYM[s2] + ' ' + n(hi - b)) + '.', 'Divide all three parts by ' + a + ': ' + m(n(x1) + ' ' + SYM[s1] + ' <i>x</i> ' + SYM[s2] + ' ' + n(x2)) + '.', 'A ' + m('&lt;') + ' side gets a parenthesis and a ' + m('≤') + ' side gets a bracket: ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // read a number line
        var t = ri(0, 2), a = ri(-6, 4), b = a + ri(2, 6), ca = K.coin(), cb = K.coin(), o, cor, w;
        if (t === 0) { o = { min: a - 4, max: a + 5, pts: [{ x: a, open: !ca }], rays: [{ from: a, dir: 1 }] }; cor = ray(a, 1, ca); w = [ray(a, 1, !ca), ray(a, -1, ca), ray(a, -1, !ca)]; }
        else if (t === 1) { o = { min: a - 5, max: a + 4, pts: [{ x: a, open: !ca }], rays: [{ from: a, dir: -1 }] }; cor = ray(a, -1, ca); w = [ray(a, -1, !ca), ray(a, 1, ca), ray(a, 1, !ca)]; }
        else { o = { min: a - 2, max: b + 2, pts: [{ x: a, open: !ca }, { x: b, open: !cb }], segs: [{ a: a, b: b }] }; cor = m(ivl(a, ca, b, cb)); w = [m(ivl(a, !ca, b, !cb)), m(ivl(a, ca, b, !cb)), m(NEGINF + ', ' + n(a) + (ca ? ']' : ')') + ' ∪ ' + (cb ? '[' : '(') + n(b) + ', ∞)')]; }
        var g = K.numberLine(o);
        return withP(Q({ q: 'Which interval notation describes the set graphed on the number line?', graph: g, mc: mc(cor, w), why: ['A closed (filled) dot means the endpoint is included: use a bracket. An open dot means it is not included: use a parenthesis.', t === 2 ? 'The graph is the segment between ' + n(a) + ' and ' + n(b) + '.' : 'The arrow points ' + (t === 0 ? 'right, toward ∞' : 'left, toward ' + M + '∞') + ', and ∞ always gets a parenthesis.', 'So the set is ' + cor + '.'] }), { k: 'nl' });
      }
    ],
    [
      function () { // linear with distribution on one side
        var a, c, p, d, kk;
        do { a = rnz(-6, 6); c = rnz(-6, 6); p = rnz(-6, 6); d = rnz(-12, 12); kk = a - c; } while (kk === 0 || Math.abs(a) < 2);
        var sym = pick(['<', '<=', '>', '>=']), x0 = R(d - a * p, kk), s2 = kk < 0 ? FLIP[sym] : sym, dir = (s2 === '>' || s2 === '>=') ? 1 : -1, cl = s2.length === 2;
        var e = m(cpar(a) + '(' + lin(1, p) + ') ' + SYM[sym] + ' ' + lin(c, d)), cor = ray(x0, dir, cl);
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [ray(x0, -dir, cl), ray(x0, dir, !cl), ray(R(d + a * p, kk), dir, cl)], function () { return ray(x0.add(rnz(-3, 3)), dir, cl); }), why: ['Distribute: ' + m(lin(a, a * p) + ' ' + SYM[sym] + ' ' + lin(c, d)) + '.', 'Collect terms: ' + m(P([[kk, X]]) + ' ' + SYM[sym] + ' ' + n(d - a * p)) + '.', (kk === 1 ? 'So' : 'Divide by ' + n(kk) + (kk < 0 ? ' and reverse the symbol' : '') + ': ' + m('<i>x</i> ' + SYM[s2] + ' ' + x0.html()) + ', so') + ' the solution set is ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // factorable quadratic
        var r1, r2; do { r1 = ri(-7, 7); r2 = ri(-7, 7); } while (r1 >= r2);
        var sym = pick(['<', '<=', '>', '>=']), f = function (x) { return x.sub(r1).mul(x.sub(r2)); };
        var mk = function (s, a1, a2) { return ivSet(function (x) { return cmp(x.sub(a1).mul(x.sub(a2)), s); }, [a1, a2]); };
        var e = m(quad(1, -(r1 + r2), r1 * r2) + ' ' + SYM[sym] + ' 0'), cor = mk(sym, r1, r2);
        var w = [mk(OPP[sym], r1, r2), mk(STR[sym], r1, r2), mk(sym, -r2, -r1)];
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w, function () { return mk(sym, r1 + rnz(-2, 2), r2 + rnz(1, 2)); }), why: ['Factor: ' + m(fp(-r1) + fp(-r2) + ' ' + SYM[sym] + ' 0').replace(/\(<i>x<\/i>\)/g, X) + '. The critical values are ' + n(r1) + ' and ' + n(r2) + '.', 'Test one value in each interval: ' + intervalTests([r1, r2], function (x) { return cmp(f(x), sym); }) + '.', (sym.length === 2 ? 'The endpoints make the expression 0, so they are included' : 'The inequality is strict, so the endpoints are excluded') + ': ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // three-part with negative coefficient
        var a = ri(2, 5), b = rnz(-9, 9), x1 = ri(-6, 3), x2 = x1 + ri(2, 6), s1 = pick(['<', '<=']), s2 = pick(['<', '<=']);
        var lo = b - a * x2, hi = b - a * x1, mid = P([[b, ''], [-a, X]]), e = m(n(lo) + ' ' + SYM[s1] + ' ' + mid + ' ' + SYM[s2] + ' ' + n(hi));
        var c1 = s1 === '<=', c2 = s2 === '<=', cor = m(ivl(x1, c2, x2, c1));
        var w = [m(ivl(-x2, c1, -x1, c2)), m(ivl(x1, !c2, x2, !c1)), c1 !== c2 ? m(ivl(x1, c1, x2, c2)) : m(ivl(x1, !c2, x2, c1))];
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w, function () { return m(ivl(x1 + rnz(-2, 2), c2, x2, c1)); }), why: [(b > 0 ? 'Subtract ' + b : 'Add ' + (-b)) + ' in all three parts: ' + m(n(lo - b) + ' ' + SYM[s1] + ' ' + P([[-a, X]]) + ' ' + SYM[s2] + ' ' + n(hi - b)) + '.', 'Divide by ' + n(-a) + ' and reverse both symbols: ' + m(n(x2) + ' ' + SYM[FLIP[s1]] + ' <i>x</i> ' + SYM[FLIP[s2]] + ' ' + n(x1)) + '.', 'Rewrite from smallest to largest: ' + m(n(x1) + ' ' + SYM[s2] + ' <i>x</i> ' + SYM[s1] + ' ' + n(x2)) + ', which is ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // (x − a)/(x − b) sym 0
        var a, b; do { a = ri(-7, 7); b = ri(-7, 7); } while (a === b);
        var sym = pick(['<', '<=', '>', '>=']);
        var mk = function (s, aa, bb, incB) { return ivSet(function (x) { var den = x.sub(bb); if (den.n === 0) return !!incB; return cmp(x.sub(aa).div(den), s); }, [aa, bb]); };
        var e = m(fr(lin(1, -a), lin(1, -b)) + ' ' + SYM[sym] + ' 0'), cor = mk(sym, a, b);
        var w = [mk(sym, a, b, true), mk(OPP[sym], a, b), mk(sym, -a, -b), mk(STR[sym], a, b)];
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w), why: ['Critical values: ' + xeq(a) + ' (numerator is 0) and ' + xeq(b) + ' (denominator is 0).', 'Test one value in each interval: ' + intervalTests([a, b], function (x) { var den = x.sub(b); return den.n !== 0 && cmp(x.sub(a).div(den), sym); }) + '.', n(b) + ' is never included because it makes the denominator 0' + (sym.length === 2 ? '; ' + n(a) + ' is included because the quotient equals 0 there' : '') + '. Answer: ' + cor + '.'] }), { k: 'ineq', e: e });
      }
    ],
    [
      function () { // (x + a)/(x − b) sym k
        var a, b, k, z; do { a = rnz(-6, 6); b = rnz(-6, 6); k = pick([-2, -1, 2, 3]); z = R(a + k * b, k - 1); } while (z.eq(b) || a === -b);
        var sym = pick(['<', '<=', '>', '>=']);
        var orig = function (s, incB) { return function (x) { var den = x.sub(b); if (den.n === 0) return !!incB; return cmp(x.add(a).div(den).sub(k), s); }; };
        var e = m(fr(lin(1, a), lin(1, -b)) + ' ' + SYM[sym] + ' ' + n(k)), cor = ivSet(orig(sym), [z, b]);
        var cross = ivSet(function (x) { return cmp(x.add(a).sub(x.sub(b).mul(k)), sym); }, [z]);
        var w = [cross, ivSet(orig(sym, true), [z, b]), ivSet(orig(OPP[sym]), [z, b]), ivSet(orig(STR[sym]), [z, b])];
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w), why: ['Do not multiply by ' + m(lin(1, -b)) + ' (its sign is unknown). ' + (k > 0 ? 'Subtract ' + k : 'Add ' + (-k)) + ' on both sides instead: ' + m(fr(lin(1, a), lin(1, -b)) + (k > 0 ? ' ' + M + ' ' + k : ' + ' + (-k)) + ' ' + SYM[sym] + ' 0') + '.', 'Common denominator: ' + m(fr(lin(1 - k, a + k * b), lin(1, -b)) + ' ' + SYM[sym] + ' 0') + '. Critical values: ' + xeq(z) + ' and ' + xeq(b) + '.', 'Test intervals: ' + intervalTests([z, b], orig(sym)) + '. ' + n(b) + ' is excluded (denominator 0). Answer: ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // x² sym k (irrational) or no real zeros
        var sym = pick(['<', '<=', '>', '>=']), cl = sym.length === 2, lt = sym.charAt(0) === '<';
        if (K.coin()) {
          var k; do { k = ri(2, 60); } while (sqf(k)[1] === 1);
          var r = radH(sqf(k)[0], sqf(k)[1]), e = m(X2 + ' ' + SYM[sym] + ' ' + k);
          var ins = function (c) { return m((c ? '[' : '(') + M + r + ', ' + r + (c ? ']' : ')')); }, out = function (c) { return m(NEGINF + ', ' + M + r + (c ? ']' : ')') + ' ∪ ' + (c ? '[' : '(') + r + ', ∞)'); };
          var cor = lt ? ins(cl) : out(cl), w = lt ? [out(!cl), ins(!cl), m(NEGINF + ', ' + r + (cl ? ']' : ')'))] : [ins(!cl), out(!cl), m((cl ? '[' : '(') + r + ', ∞)')];
          return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, w), why: ['Rewrite: ' + m(X2 + ' ' + M + ' ' + k + ' ' + SYM[sym] + ' 0') + '. The zeros are ' + m('<i>x</i> = ±' + K.sqrt(k) + (sqf(k)[0] > 1 ? ' = ±' + r : '')) + '.', 'Test 0: ' + m('0 ' + M + ' ' + k + ' &lt; 0') + ', so the middle interval makes ' + m(X2 + ' ' + M + ' ' + k) + ' negative and the outer intervals make it positive.', 'So the solution set is ' + cor + (cl ? ', endpoints included.' : ', endpoints excluded.')] }), { k: 'ineq', e: e });
        }
        var b, c; do { b = ri(-6, 6); c = ri(1, 15); } while (b * b - 4 * c >= 0);
        var e2 = m(quad(1, b, c) + ' ' + SYM[sym] + ' 0'), all = m(NEGINF + ', ∞)'), none = m('∅'), h = R(-b, 2);
        return withP(Q({ q: 'Solve ' + e2 + '. Write the solution set in interval notation.', mc: mc(lt ? none : all, [lt ? all : none, m(NEGINF + ', ' + h.html() + ')'), m('(' + h.html() + ', ∞)')]), why: ['Discriminant: ' + m(sub(b) + '<sup>2</sup> ' + M + ' 4(1)(' + c + ') = ' + n(b * b - 4 * c)) + ' &lt; 0, so ' + m(quad(1, b, c)) + ' is never 0.', 'A quadratic with no real zeros keeps one sign. Test ' + xeq(0) + ': the value is ' + c + ' &gt; 0, so it is positive for every ' + X + '.', lt ? 'It is never ' + words(sym) + ' 0: the solution set is ∅.' : 'It is always ' + words(sym) + ' 0: the solution set is ' + all + '.'] }), { k: 'ineq', e: e2 });
      },
      function () { // applications
        var t = ri(0, 2);
        if (t === 0) {
          var p, c, F, N; do { c = ri(5, 30); p = c + ri(3, 20); N = ri(5, 60) * 10; F = (p - c) * N; } while (F > 20000);
          var u = function (s, v) { return s + ' ' + K.comma(v) + ' units'; };
          return withP(Q({ q: 'A company’s revenue is ' + m(L('R = ') + p + X) + ' and its cost is ' + m(L('C = ') + c + X + ' + ' + K.comma(F)) + ', where ' + X + ' is the number of units. For which numbers of units does the company make a profit?', mc: mc(u('More than', N), [u('At least', N), u('Fewer than', N), u('More than', F)]), why: ['Profit means revenue exceeds cost: ' + m(p + X + ' &gt; ' + c + X + ' + ' + K.comma(F)) + '.', 'Subtract ' + m(c + X) + ': ' + m((p - c) + X + ' &gt; ' + K.comma(F)) + ', so ' + m('<i>x</i> &gt; ' + K.comma(N)) + '.', 'At exactly ' + K.comma(N) + ' units the company only breaks even, so the answer is more than ' + K.comma(N) + ' units.'] }), { k: 'word', w: 'profit', p: p, c: c, F: F });
        }
        if (t === 1) {
          var G, s1, s2, s3, need; do { G = pick([70, 75, 80, 85, 90]); s1 = ri(60, 100); s2 = ri(60, 100); s3 = ri(60, 100); need = 4 * G - s1 - s2 - s3; } while (need < 40 || need > 100 || need === G);
          return withP(Q({ q: 'A student has scores of ' + s1 + ', ' + s2 + ', and ' + s3 + ' on three tests. Each test is worth at most 100 points. What scores on the fourth test give an average of at least ' + G + '? Write the answer in interval notation.', mc: mc(m('[' + need + ', 100]'), [m('(' + need + ', 100]'), m('[' + G + ', 100]'), m('[' + need + ', ∞)')]), why: ['Average of four tests: ' + m(fr(s1 + ' + ' + s2 + ' + ' + s3 + ' + ' + X, 4) + ' ≥ ' + G) + '.', 'Multiply by 4: ' + m((s1 + s2 + s3) + ' + ' + X + ' ≥ ' + 4 * G) + ', so ' + m('<i>x</i> ≥ ' + need) + '.', 'A score cannot exceed 100, so the scores are ' + m('[' + need + ', 100]') + '.'] }), { k: 'word', w: 'avg', s: [s1, s2, s3], G: G });
        }
        var t1 = ri(1, 3), t2 = t1 + ri(1, 4), s0 = pick([0, 16, 32]), v = 16 * (t1 + t2), h = s0 + 16 * t1 * t2;
        return withP(Q({ q: 'A ball’s height in feet after ' + m(L('t')) + ' seconds is ' + m(L('s = ') + quad(-16, v, s0, 't')) + '. During what time interval is the ball <b>more than</b> ' + h + ' ft high?', mc: mc(m('(' + t1 + ', ' + t2 + ')'), [m('[' + t1 + ', ' + t2 + ']'), m('(0, ' + t1 + ')'), m('(' + t1 + ', ' + n((t1 + t2) / 2) + ')')]), why: ['Solve ' + m(quad(-16, v, s0, 't') + ' &gt; ' + h) + ', which is ' + m(quad(-16, v, s0 - h, 't') + ' &gt; 0') + '.', 'Divide by ' + m(M + '16') + ' (reverse the symbol): ' + m(quad(1, -(t1 + t2), t1 * t2, 't') + ' &lt; 0') + ', or ' + m(L('(t − ') + t1 + L(')(t − ') + t2 + ') &lt; 0') + '.', 'The product is negative between the zeros, so the ball is above ' + h + ' ft for ' + m(L('t')) + ' in ' + m('(' + t1 + ', ' + t2 + ')') + ' seconds.'] }), { k: 'word', w: 'above', v: v, s0: s0, h: h });
      },
      function () { // non-monic quadratic, maybe rearranged
        var q1, q2, p1, p2; do { q1 = ri(1, 4); q2 = ri(1, 3); p1 = ri(-7, 7); p2 = ri(-7, 7); } while ((q1 === 1 && q2 === 1) || K.gcd(p1, q1) !== 1 || K.gcd(p2, q2) !== 1 || R(p1, q1).eq(R(p2, q2)) || p1 * p2 === 0);
        var A = q1 * q2, B = -(q1 * p2 + q2 * p1), C = p1 * p2, r1 = R(p1, q1), r2 = R(p2, q2), sym = pick(['<', '<=', '>', '>=']);
        var mk = function (s, u1, u2) { return ivSet(function (x) { return cmp(x.mul(x).mul(A).sub(x.mul(u1.add(u2)).mul(A)).add(u1.mul(u2).mul(A)), s); }, [u1, u2]); };
        var e = m(P([[A, X2], [B, X]]) + ' ' + SYM[sym] + ' ' + n(-C)), cor = mk(sym, r1, r2);
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [mk(OPP[sym], r1, r2), mk(STR[sym], r1, r2), mk(sym, r1.neg(), r2.neg())], function () { return mk(sym, r1.add(rnz(-2, 2)), r2); }), why: ['Get 0 on one side: ' + m(quad(A, B, C) + ' ' + SYM[sym] + ' 0') + '.', 'Factor: ' + m('(' + lin(q1, -p1) + ')(' + lin(q2, -p2) + ') ' + SYM[sym] + ' 0') + '; critical values ' + m(r1.html()) + ' and ' + m(r2.html()) + '.', 'Test intervals: ' + intervalTests([r1, r2], function (x) { return cmp(x.mul(x).mul(A).add(x.mul(B)).add(C), sym); }) + '. Answer: ' + cor + '.'] }), { k: 'ineq', e: e });
      }
    ]
  ];
  K.lesson('1.7', { title: 'Inequalities', std: 'Lial 12e · Section 1.7', levels: c17 });

  /* ================= 1.8 Absolute Value Equations and Inequalities ================= */
  function absH(a, b) { return '|' + lin(a, b) + '|'; }
  function absSet(a, b, c) { return setH([R(c - b, a), R(-c - b, a)]); }
  function absIv(a, b, sym, c) { return ivSet(function (x) { return cmp(x.mul(a).add(b).abs().sub(c), sym); }, [R(c - b, a), R(-c - b, a)]); }
  var c18 = [
    [
      function () { // |ax + b| = c
        var a = pick([1, 1, 2, 3, 4, 5, -2, -3]), b = rnz(-9, 9), c = ri(1, 12), e = m(absH(a, b) + ' = ' + c), cor = absSet(a, b, c);
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(cor, [setH([R(c - b, a)]), setH([R(c - b, a), R(c + b, a)]), setH([R(b - c, a), R(b + c, a)])], function () { return setH([R(c - b, a), R(-c - b + rnz(-3, 3), a)]); }), why: ['Absolute value ' + c + ' means a distance of ' + c + ' from 0: ' + m(lin(a, b) + ' = ' + c) + ' or ' + m(lin(a, b) + ' = ' + M + c) + '.', 'Solve each: ' + xeq(R(c - b, a)) + ' or ' + xeq(R(-c - b, a)) + '.', 'Solution set: ' + cor[0] + '.'] }), { k: 'solve', e: e });
      },
      function () { // |x − h| < c
        var h = rnz(-8, 8), c = ri(1, 9), sym = pick(['<', '<=']), cl = sym === '<=', e = m(absH(1, -h) + ' ' + SYM[sym] + ' ' + c);
        var cor = m(ivl(h - c, cl, h + c, cl));
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [m(NEGINF + ', ' + n(h - c) + (cl ? ')' : ']') + ' ∪ ' + (cl ? '(' : '[') + n(h + c) + ', ∞)'), m(ivl(h - c, !cl, h + c, !cl)), m(ivl(-h - c, cl, -h + c, cl))]), why: ['“Less than” means “between”: ' + m(M + c + ' ' + SYM[sym] + ' ' + lin(1, -h) + ' ' + SYM[sym] + ' ' + c) + '.', (h > 0 ? 'Add ' + h : 'Subtract ' + (-h)) + ' in all three parts: ' + m(n(h - c) + ' ' + SYM[sym] + ' <i>x</i> ' + SYM[sym] + ' ' + n(h + c)) + '.', 'Interval notation: ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // |x − h| > c
        var h = rnz(-8, 8), c = ri(1, 9), sym = pick(['>', '>=']), cl = sym === '>=', e = m(absH(1, -h) + ' ' + SYM[sym] + ' ' + c);
        var un = function (u, v, cc) { return m(NEGINF + ', ' + n(u) + (cc ? ']' : ')') + ' ∪ ' + (cc ? '[' : '(') + n(v) + ', ∞)'); };
        var cor = un(h - c, h + c, cl);
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [m(ivl(h - c, !cl, h + c, !cl)), un(h - c, h + c, !cl), un(-h - c, -h + c, cl)]), why: ['“Greater than” gives two pieces joined by “or”: ' + m(lin(1, -h) + ' ' + SYM[FLIP[sym]] + ' ' + M + c) + ' or ' + m(lin(1, -h) + ' ' + SYM[sym] + ' ' + c) + '.', 'Solve each: ' + m('<i>x</i> ' + SYM[FLIP[sym]] + ' ' + n(h - c)) + ' or ' + m('<i>x</i> ' + SYM[sym] + ' ' + n(h + c)) + '.', '“Or” means union: ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // equivalent compound statement
        var a = pick([1, 2, 3, 4]), b = rnz(-9, 9), c = ri(1, 9), sym = pick(['<', '<=', '>', '>=']), u = lin(a, b), lt = sym.charAt(0) === '<';
        var e = m(absH(a, b) + ' ' + SYM[sym] + ' ' + c), S = SYM[sym], F = SYM[FLIP[sym]];
        var between = m(M + c + ' ' + S.replace('&gt;', '&lt;').replace('≥', '≤') + ' ' + u + ' ' + S.replace('&gt;', '&lt;').replace('≥', '≤') + ' ' + c);
        var orS = function (s1, s2) { return m(u + ' ' + s1 + ' ' + M + c) + ' or ' + m(u + ' ' + s2 + ' ' + c); };
        var cor, w;
        if (lt) { cor = between; w = [orS(S, F), m(u + ' ' + S + ' ' + c), m(u + ' ' + S + ' ' + M + c) + ' and ' + m(u + ' ' + F + ' ' + c)]; }
        else { cor = orS(F, S); w = [m(M + c + ' ' + F + ' ' + u + ' ' + F + ' ' + c), m(u + ' ' + S + ' ' + c), orS(S, F)]; }
        return withP(Q({ q: 'Which statement is equivalent to ' + e + '?', mc: mc(cor, w), why: [lt ? '|' + K.v('u') + '| less than ' + c + ' means ' + K.v('u') + ' is within ' + c + ' of 0: between ' + M + c + ' and ' + c + ', one three-part inequality (“and”).' : '|' + K.v('u') + '| greater than ' + c + ' means ' + K.v('u') + ' is more than ' + c + ' from 0: below ' + M + c + ' <b>or</b> above ' + c + '.', 'With ' + m(K.v('u') + ' = ' + u) + ', that is ' + cor + '.', 'Absolute value equations and inequalities always split around both ' + c + ' and ' + M + c + '.'] }), { k: 'stmt', e: e });
      }
    ],
    [
      function () { // k|ax + b| + d = e
        var k = ri(2, 4), a = pick([1, 2, 3, -2]), b = rnz(-8, 8), c = ri(1, 8), d = rnz(-9, 9), ev = k * c + d;
        var e = m(k + absH(a, b) + K.plusK(d) + ' = ' + n(ev)), cor = absSet(a, b, c);
        var w = [absSet(a, b, ev - d), setH([R(c - b, a)])]; if (ev + d > 0 && (ev + d) % k === 0) w.push(absSet(a, b, (ev + d) / k));
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(cor, w, function () { return absSet(a, b, c + rnz(1, 3)); }), why: ['Isolate the absolute value first: ' + m(k + absH(a, b) + ' = ' + n(ev - d)) + ', so ' + m(absH(a, b) + ' = ' + c) + '.', 'Split: ' + m(lin(a, b) + ' = ' + c) + ' or ' + m(lin(a, b) + ' = ' + M + c) + '.', 'Solve: ' + xeq(R(c - b, a)) + ' or ' + xeq(R(-c - b, a)) + '. Solution set ' + cor[0] + '.'] }), { k: 'solve', e: e });
      },
      function () { // |ax + b| ≤ c with fractions
        var a, b, c; do { a = pick([2, 3, 4, 5, -2, -3, -4]); b = rnz(-9, 9); c = ri(1, 9); } while (R(c - b, a).isInt() && R(-c - b, a).isInt());
        var sym = pick(['<', '<=']), useBA = a < 0 && K.coin(), uH = useBA ? P([[b, ''], [a, X]]) : lin(a, b), e = m('|' + uH + '| ' + SYM[sym] + ' ' + c);
        var cor = absIv(a, b, sym, c), lo = R(Math.min(R(c - b, a).val(), R(-c - b, a).val()) === R(c - b, a).val() ? c - b : -c - b, a), hi = lo.eq(R(c - b, a)) ? R(-c - b, a) : R(c - b, a);
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [absIv(a, -b, sym, c), absIv(a, b, OPP[sym], c), absIv(a, b, STR[sym], c)]), why: ['Rewrite as a three-part inequality: ' + m(M + c + ' ' + SYM[sym] + ' ' + uH + ' ' + SYM[sym] + ' ' + c) + '.', (b > 0 ? 'Subtract ' + b : 'Add ' + (-b)) + ', then divide all three parts by ' + n(a) + (a < 0 ? ' and reverse the symbols' : '') + '.', 'The endpoints are ' + m(lo.html()) + ' and ' + m(hi.html()) + ': ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // |ax + b| > c with fractions
        var a, b, c; do { a = pick([2, 3, 4, 5, 6, 8, -2, -3, -4, -8]); b = rnz(-9, 9); c = ri(1, 9); } while (R(c - b, a).isInt() && R(-c - b, a).isInt());
        var sym = pick(['>', '>=']), useBA = a < 0 && K.coin(), uH = useBA ? P([[b, ''], [a, X]]) : lin(a, b), e = m('|' + uH + '| ' + SYM[sym] + ' ' + c);
        var cor = absIv(a, b, sym, c), r1 = R(c - b, a), r2 = R(-c - b, a);
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [absIv(a, b, OPP[sym], c), absIv(a, -b, sym, c), absIv(a, b, STR[sym], c)]), why: ['Two pieces joined by “or”: ' + m(uH + ' ' + SYM[sym] + ' ' + c) + ' or ' + m(uH + ' ' + SYM[FLIP[sym]] + ' ' + M + c) + '.', 'Solve each piece' + (a < 0 ? ', reversing the symbol when dividing by ' + n(a) : '') + ': the boundary values are ' + m(r1.html()) + ' and ' + m(r2.html()) + '.', '“Or” means union of the two outer pieces: ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // |ax + b| = |cx + d|
        var a, b, c, d; do { a = rnz(-5, 5); c = rnz(-5, 5); b = rnz(-9, 9); d = rnz(-9, 9); } while (Math.abs(a) === Math.abs(c) || b === d);
        var e = m(absH(a, b) + ' = ' + absH(c, d)), s1 = R(d - b, a - c), s2 = R(-d - b, a + c), cor = setH([s1, s2]);
        return withP(Q({ q: 'Solve ' + e + '.', mc: mcV(cor, [setH([s1]), setH([s1, R(d + b, a + c)]), setH([s1.neg(), s2.neg()])], function () { return setH([s1, s2.add(rnz(-3, 3))]); }), why: ['Equal absolute values means the expressions are equal or opposites.', m(lin(a, b) + ' = ' + lin(c, d)) + ' gives ' + xeq(s1) + '; ' + m(lin(a, b) + ' = ' + M + '(' + lin(c, d) + ')') + ' gives ' + xeq(s2) + '.', 'Solution set: ' + cor[0] + '.'] }), { k: 'solve', e: e });
      }
    ],
    [
      function () { // special cases
        var a = pick([1, 2, 3, 4, 5, -2, -3]), b = rnz(-9, 9), k = ri(1, 4), d = rnz(-9, 9), t = ri(0, 5), rhs, sym;
        if (t === 0) { sym = pick(['>', '>=']); rhs = -ri(1, 6); } else if (t === 1) { sym = pick(['<', '<=']); rhs = -ri(1, 6); } else if (t === 2) { sym = '<='; rhs = 0; } else if (t === 3) { sym = '>'; rhs = 0; } else if (t === 4) { sym = '<'; rhs = 0; } else { sym = '>='; rhs = 0; }
        var v = R(-b, a), ev = k * rhs + d, e = m((k === 1 ? '' : k) + absH(a, b) + K.plusK(d) + ' ' + SYM[sym] + ' ' + n(ev));
        var all = m(NEGINF + ', ∞)'), none = m('∅'), pt = m('{' + v.html() + '}'), hole = m(NEGINF + ', ' + v.html() + ') ∪ (' + v.html() + ', ∞)');
        var cor = rhs < 0 ? (t === 0 ? all : none) : (sym === '<=' ? pt : sym === '>' ? hole : sym === '<' ? none : all);
        var reason = rhs < 0 ? 'An absolute value is never negative, so it is always greater than ' + n(rhs) + ' and never less than it.' : (sym === '<=' ? 'An absolute value is never negative, so ' + m(absH(a, b) + ' ≤ 0') + ' only when it equals 0.' : sym === '>' ? 'An absolute value is positive except where it equals 0.' : sym === '<' ? 'An absolute value is never less than 0.' : 'An absolute value is always at least 0.');
        return withP(Q({ q: 'Solve ' + e + '.', mc: mc(cor, [all, none, pt, hole].filter(function (z) { return z !== cor; })), why: ['Isolate the absolute value: ' + m(absH(a, b) + ' ' + SYM[sym] + ' ' + n(rhs)) + '.', reason, (rhs === 0 && (sym === '<=' || sym === '>') ? m(lin(a, b) + ' = 0') + ' at ' + xeq(v) + '. ' : '') + 'Solution set: ' + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // tolerance
        var C = pick([['A bolt', 'mm', 20, [0.05, 0.1, 0.2]], ['A cereal box', 'oz', 16, [0.25, 0.5]], ['A metal rod', 'cm', 45, [0.1, 0.3, 0.5]], ['A water bottle', 'mL', 500, [2, 5, 8]], ['A machine part', 'in.', 3, [0.01, 0.02, 0.05]]]);
        var T = C[2] + (C[3][0] >= 1 ? ri(-2, 2) * 5 : ri(-3, 3)), t = pick(C[3]);
        if (T <= 1) T = C[2];
        var lo = K.round(T - t, 4), hi = K.round(T + t, 4), lo2 = K.round(T - 2 * t, 4), hi2 = K.round(T + 2 * t, 4);
        return withP(Q({ q: C[0] + ' must measure ' + n(T) + ' ' + C[1] + ', with a tolerance of ' + n(t) + ' ' + C[1] + ': its measurement ' + m(X) + ' must satisfy ' + m('|' + X + ' ' + M + ' ' + n(T) + '| ≤ ' + n(t)) + '. Which measurements are acceptable?', mc: mc(m('[' + n(lo) + ', ' + n(hi) + ']'), [m('(' + n(lo) + ', ' + n(hi) + ')'), m(NEGINF + ', ' + n(lo) + '] ∪ [' + n(hi) + ', ∞)'), m('[' + n(lo2) + ', ' + n(hi2) + ']')]), why: ['“Less than or equal to” means between: ' + m(M + n(t) + ' ≤ <i>x</i> ' + M + ' ' + n(T) + ' ≤ ' + n(t)) + '.', 'Add ' + n(T) + ' to all three parts: ' + m(n(lo) + ' ≤ <i>x</i> ≤ ' + n(hi)) + '.', 'The endpoints are allowed (≤), so the interval is ' + m('[' + n(lo) + ', ' + n(hi) + ']') + ' ' + C[1] + '.'] }), { k: 'word', w: 'tol', T: T, t: t });
      },
      function () { // −k|x − h| + d sym e (flip)
        var k = ri(2, 5), h = rnz(-7, 7), c = ri(1, 7), d = rnz(-9, 9), sym = pick(['<', '<=', '>', '>=']), ev = d - k * c;
        var e = m(M + k + absH(1, -h) + K.plusK(d) + ' ' + SYM[sym] + ' ' + n(ev)), s2 = FLIP[sym];
        var cor = absIv(1, -h, s2, c);
        return withP(Q({ q: 'Solve ' + e + '. Write the solution set in interval notation.', mc: mc(cor, [absIv(1, -h, sym, c), absIv(1, -h, OPP[s2], c), absIv(1, h, s2, c)]), why: [(d > 0 ? 'Subtract ' + d : 'Add ' + (-d)) + ': ' + m(M + k + absH(1, -h) + ' ' + SYM[sym] + ' ' + n(ev - d)) + '.', 'Divide by ' + m(M + k) + ' and <b>reverse</b> the symbol: ' + m(absH(1, -h) + ' ' + SYM[s2] + ' ' + c) + '.', (s2.charAt(0) === '>' ? 'Greater than → two pieces (“or”): ' : 'Less than → between: ') + cor + '.'] }), { k: 'ineq', e: e });
      },
      function () { // describe in words
        var h, c; do { h = rnz(-8, 8); c = ri(1, 9); } while (Math.abs(h) === c);
        var rel = pick(['<', '<=', '>', '>=']), phrase = { '<': 'less than', '<=': 'at most', '>': 'more than', '>=': 'at least' }[rel];
        var st = function (hh, cc, s) { return m('|' + lin(1, -hh) + '| ' + SYM[s] + ' ' + cc); };
        return withP(Q({ q: 'Which inequality describes all numbers ' + m(X) + ' whose distance from ' + n(h) + ' is ' + phrase + ' ' + c + '?', mc: mc(st(h, c, rel), [st(-h, c, rel), st(h, c, OPP[rel]), m('|' + lin(1, -c) + '| ' + SYM[rel] + ' ' + n(Math.abs(h)))]), why: ['The distance between ' + m(X) + ' and ' + n(h) + ' is ' + m('|' + lin(1, -h) + '|') + '.', '“' + phrase.charAt(0).toUpperCase() + phrase.slice(1) + '” means ' + m(SYM[rel]) + '.', 'So the inequality is ' + st(h, c, rel) + '.'] }), { k: 'stmt', ref: { h: h, c: c, rel: rel } });
      }
    ]
  ];
  K.lesson('1.8', { title: 'Absolute Value Equations and Inequalities', std: 'Lial 12e · Section 1.8', levels: c18 });

  K.review('1', 'Chapter 1 Review: Equations and Inequalities');
})(typeof window !== 'undefined' ? window.KCEP : globalThis.KCEP);
