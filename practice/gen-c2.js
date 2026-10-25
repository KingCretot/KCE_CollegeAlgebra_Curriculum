/* Chapter 2 — Graphs and Functions (Lial, Essentials of College Algebra 12e, Sections 2.1–2.8) */
(function (K) {
  var ri = K.ri, rnz = K.rnz, pick = K.pick, n = K.n, R = K.R, P = K.poly, X = K.x, Y = K.y, Q = K.Q, mc = K.mc, M = K.MINUS, m = K.m, C = K.COL;
  var SL = [R(1), R(2), R(3), R(-1), R(-2), R(-3), R(1, 2), R(-1, 2), R(1, 3), R(-1, 3), R(2, 3), R(-2, 3), R(3, 2), R(-3, 2)];
  var TRI = [[3, 4, 5], [4, 3, 5], [6, 8, 10], [8, 6, 10], [5, 12, 13], [12, 5, 13], [8, 15, 17], [9, 12, 15], [12, 9, 15]];
  var I = function (v) { return '<i>' + v + '</i>'; };
  var H = function (v) { return R(v).html(); };
  // value in parentheses when negative or a fraction (for substitution steps)
  function sb(v) { v = R(v); return (v.n < 0 || v.d !== 1) ? '(' + v.html() + ')' : v.html(); }
  function fx(name, body, v) { return m(I(name) + '(' + I(v || 'x') + ') = ' + body); }
  function sq(v, h) { h = R(h); return h.n === 0 ? I(v) + '<sup>2</sup>' : '(' + K.minusH(I(v), h) + ')<sup>2</sup>'; }
  function circEq(h, k, rhs) { return m(sq('x', h) + ' + ' + sq('y', k) + ' = ' + (typeof rhs === 'number' ? n(rhs) : rhs)); }
  // simplest radical form of √N
  function rad(N) {
    var a = 1, b = N;
    for (var f = 2; f * f <= b; f++) while (b % (f * f) === 0) { b /= f * f; a *= f; }
    return { a: a, b: b, v: Math.sqrt(N), html: b === 1 ? n(a) : (a === 1 ? '' : n(a)) + K.sqrt(String(b)) };
  }
  // multiple choice where wrong answers are rejected if NUMERICALLY equal to the correct one
  function mcV(cH, cV, wr, extra) {
    var ok = function (z) { return z && isFinite(z[1]) && Math.abs(z[1] - cV) > 1e-9; };
    return mc(cH, wr.filter(ok).map(function (z) { return z[0]; }), extra ? function (i) { var z = extra(i); return ok(z) ? z[0] : ''; } : undefined);
  }
  function nx(c) { return function (i) { var v = c + K.rnz(-4, 4) * (1 + Math.floor(i / 20)); return [n(v), v]; }; }
  // interval notation
  function ep(v) { return v === Infinity ? '∞' : v === -Infinity ? M + '∞' : R(v).html(); }
  function iv(a, b, lc, rc) { return (lc && a !== -Infinity ? '[' : '(') + ep(a) + ', ' + ep(b) + (rc && b !== Infinity ? ']' : ')'); }
  var ALL = '(' + M + '∞, ∞)';
  function cup(a) { return a.join(' ∪ '); }
  function setH(arr) { var s = arr.slice().sort(function (a, b) { return a - b; }).filter(function (v, i, A) { return i === 0 || A[i - 1] !== v; }); return '{' + s.map(n).join(', ') + '}'; }
  // piecewise display; rows = [[exprHtml, condHtml], ...]
  function pw(name, rows) {
    return '<span class="mth pw" style="display:inline-flex;align-items:center;gap:6px;vertical-align:middle"><span>' + name + ' =</span><span style="font-size:' + (rows.length > 2 ? 3.6 : 2.5) + 'em;line-height:1;font-weight:300">{</span><span style="display:inline-grid;grid-template-columns:auto auto;column-gap:14px;row-gap:3px;text-align:left">' +
      rows.map(function (r) { return '<span class="pe">' + r[0] + '</span><span class="pc">if ' + r[1] + '</span>'; }).join('') + '</span></span>';
  }
  function desc(s) { if (K._gd.length) K._gd[K._gd.length - 1] = 'graph: ' + s; }
  function circSegs(h, k, r, col, dash) {
    var s = [], N = 120;
    for (var i = 0; i < N; i++) { var a = 2 * Math.PI * i / N, b = 2 * Math.PI * (i + 1) / N; s.push({ x1: h + r * Math.cos(a), y1: k + r * Math.sin(a), x2: h + r * Math.cos(b), y2: k + r * Math.sin(b), color: col || C.blue, dash: dash }); }
    return s;
  }
  var LE = { '<': '&lt;', '<=': '≤', '>': '&gt;', '>=': '≥' };
  function cond(op, c) { return m(I('x') + ' ' + LE[op] + ' ' + H(c)); }
  function test(op, x, c) { return op === '<' ? x < c : op === '<=' ? x <= c : op === '>' ? x > c : x >= c; }
  function lin(a, b) { return P([[a, X], [b, '']]); }
  function quad(a, b, c) { return P([[a, K.xp(2)], [b, X], [c, '']]); }
  function attach(o, p) { o.p = p; return o; }
  /* ---- shared text helpers (added in review fixes) ---- */
  // a = b = c chain that drops a step identical to the one before it (no "1/2 = 1/2")
  function eqs() { var a = [].slice.call(arguments), out = [a[0]]; for (var i = 1; i < a.length; i++) if (K.plain(a[i]) !== K.plain(out[out.length - 1])) out.push(a[i]); return out.join(' = '); }
  // quotient of two integers as shown in a step: never a negative denominator under a fraction bar
  function frq(a, b) { return b < 0 ? n(a) + ' ÷ (' + n(b) + ')' : K.frx(n(a), n(b)); }
  // indefinite article for a number that follows it ("an 8-mile", "an 11-mile", "a 12-mile")
  function art(v) { var s = String(v).replace(/[^0-9]/g, ''); return /^8/.test(s) || (/^1[18]/.test(s) && s.length % 3 === 2) ? 'an' : 'a'; }
  // count + noun with the right number ("1 year", "3 years")
  function cnt(v, one, many) { return n(v) + ' ' + (Math.abs(v) === 1 ? one : (many || one + 's')); }
  // math that may wrap between top-level terms or factors (never inside parentheses or a fraction)
  function brk(s) {
    var chunks = [], seps = [], cur = '', dp = 0, ds = 0, i = 0;
    while (i < s.length) {
      if (s.substr(i, 5) === '<span') ds++; else if (s.substr(i, 6) === '</span') ds--;
      var ch = s.charAt(i), op = s.substr(i, 3);
      if (dp === 0 && ds === 0 && cur.trim() && (op === ' + ' || op === ' ' + K.MINUS + ' ' || op === ' = ' || op === ' ÷ ')) { chunks.push(cur.trim()); seps.push(' '); cur = ''; }
      if (ch === '(') dp++; else if (ch === ')') dp--;
      cur += ch; i++;
      if (dp === 0 && ds === 0 && ch === ')' && s.charAt(i) === '(') { chunks.push(cur.trim()); seps.push('<wbr>'); cur = ''; }
    }
    if (cur.trim()) chunks.push(cur.trim());
    return chunks.map(function (c, j) { return (j ? seps[j - 1] : '') + K.m(c); }).join('');
  }
  // Graph point labels: choose a side for each label so it does not sit on a tick label, an axis,
  // an asymptote, the curve, another point or another label. P.pref lists preferred positions
  // ('ne','se','nw','sw','e','w'); the lowest-collision position wins, earlier ones on ties. Mutates o.pts; returns o.
  function place(o) {
    var x0 = o.x[0], x1 = o.x[1], y0 = o.y[0], y1 = o.y[1], W = o.w || 320, H = o.h || 320, pad = o.pad || 30, padB = o.xlab ? 40 : pad, padL = o.ylab ? 44 : pad, pw = W - padL - pad, ph = H - pad - padB;
    var X = function (x) { return padL + (x - x0) / (x1 - x0) * pw; }, Y = function (y) { return pad + (y1 - y) / (y1 - y0) * ph; };
    var ax = (y0 <= 0 && y1 >= 0) ? Y(0) : (y0 > 0 ? pad + ph : pad), ay = (x0 <= 0 && x1 >= 0) ? X(0) : (x0 > 0 ? padL : padL + pw);
    var gx = o.stepX || o.step || 1, gy = o.stepY || o.step || 1, lx = o.labX || o.lab || (gx * ((x1 - x0) / gx > 12 ? 2 : 1)), ly = o.labY || o.lab || (gy * ((y1 - y0) / gy > 12 ? 2 : 1));
    var obs = []; // [rect, penalty]
    var tw = function (v) { return 6.2 * K.n(K.round(v, 6)).length + 2; };
    for (var v = Math.ceil(x0 / lx) * lx; v <= x1 + 1e-9; v += lx) if (!(Math.abs(v) < 1e-9 && (x0 < 0 || y0 >= 0))) obs.push([[X(v) - tw(v) / 2, ax + 6, X(v) + tw(v) / 2, ax + 16], 10]);
    for (v = Math.ceil(y0 / ly) * ly; v <= y1 + 1e-9; v += ly) if (Math.abs(v) > 1e-9) obs.push([[ay - 6 - tw(v), Y(v) - 5, ay - 6, Y(v) + 5], 10]);
    obs.push([[padL - 8, ax - 1.5, padL + pw + 8, ax + 1.5], 3], [[ay - 1.5, pad - 8, ay + 1.5, pad + ph + 8], 3]);
    (o.lines || []).forEach(function (L) { if (L.vx !== undefined) obs.push([[X(L.vx) - 2, pad, X(L.vx) + 2, pad + ph], 6]); else if (K.R(L.m).n === 0) { var yb = Y(K.R(L.b).val()); obs.push([[padL, yb - 2, padL + pw, yb + 2], 6]); } });
    (o.pts || []).forEach(function (P) { obs.push([[X(P.x) - 5, Y(P.y) - 5, X(P.x) + 5, Y(P.y) + 5], 10]); });
    var curves = [];
    (o.fns || []).forEach(function (F) { curves.push(function (px) { var x = x0 + (px - padL) / pw * (x1 - x0); if (F.from !== undefined && x < F.from) return NaN; if (F.to !== undefined && x > F.to) return NaN; return Y(F.f(x)); }); });
    (o.lines || []).forEach(function (L) { if (L.vx === undefined && K.R(L.m).n !== 0) { var mm = K.R(L.m).val(), bb = K.R(L.b).val(); curves.push(function (px) { var x = x0 + (px - padL) / pw * (x1 - x0); return Y(mm * x + bb); }); } });
    var hit = function (r, s) { return !(r[2] < s[0] || r[0] > s[2] || r[3] < s[1] || r[1] > s[3]); };
    var segHit = function (r) { return (o.segs || []).some(function (S) { for (var t = 0; t <= 1; t += 0.01) { var px = X(S.x1 + (S.x2 - S.x1) * t), py = Y(S.y1 + (S.y2 - S.y1) * t); if (px >= r[0] - 1 && px <= r[2] + 1 && py >= r[1] - 1 && py <= r[3] + 1) return true; } return false; }); };
    var curveHit = function (r) { return curves.some(function (c) { for (var px = r[0] - 1; px <= r[2] + 1; px += 1) { var py = c(px), py2 = c(px + 1); if (!isFinite(py)) continue; if (py >= r[1] - 1 && py <= r[3] + 1) return true; if (isFinite(py2) && Math.min(py, py2) <= r[1] && Math.max(py, py2) >= r[3]) return true; } return false; }); };
    // [horizontal side, dy]  (side +1: text starts right of the point; −1: text ends left of it)
    var OFF = { ne: [1, -7], se: [1, 17], nw: [-1, -7], sw: [-1, 17], e: [1, 4], w: [-1, 4] };
    (o.pts || []).forEach(function (P) {
      if (!P.label || P.dx !== undefined) return;
      var w = 6.6 * String(P.label).length + 2, px = X(P.x), py = Y(P.y), best = null;
      var order = (P.pref || []).concat(['ne', 'se', 'nw', 'sw', 'e', 'w']), cands = [];
      order.forEach(function (c) { var f = OFF[c]; cands.push([f[0], (c === 'e' || c === 'w' ? 9 : 7), f[1], 0]); });
      [[7, -22], [7, 32], [18, -7], [18, 17], [18, -22], [18, 32], [7, -36], [7, 46], [30, -7], [30, 17], [30, 4]].forEach(function (d) { [1, -1].forEach(function (sd) { cands.push([sd, d[0], d[1], 1 + (d[0] > 7 ? 0.5 : 0) + (d[0] > 20 ? 2 : 0) + (Math.abs(d[1] - 5) > 35 ? 0.5 : 0)]); }); });
      cands.forEach(function (cd, idx) {
        var dx = cd[1] * cd[0], dy = cd[2], r = cd[0] > 0 ? [px + dx, py + dy - 10, px + dx + w, py + dy + 1] : [px + dx - w, py + dy - 10, px + dx, py + dy + 1];
        var across = (o.lines || []).some(function (L) { if (L.vx !== undefined) { var xv = X(L.vx); return (px < xv && r[2] > xv) || (px > xv && r[0] < xv); } if (K.R(L.m).n !== 0) return false; var yh = Y(K.R(L.b).val()); return (py < yh && r[3] > yh) || (py > yh && r[1] < yh); });
        var sc = (across ? 6 : 0) + obs.reduce(function (s, b) { return s + (hit(r, b[0]) ? b[1] : 0); }, 0) + (curveHit(r) ? 8 : 0) + (segHit(r) ? 8 : 0) + (r[0] < 2 || r[2] > W - 2 || r[1] < 2 || r[3] > H - 2 ? 50 : 0) + cd[3] + idx * 0.001;
        if (!best || sc < best.sc) best = { sc: sc, sd: cd[0], r: r, dx: dx, dy: dy };
      });
      P.anchor = best.sd > 0 ? 'start' : 'end'; P.dx = best.dx; P.dy = best.dy; obs.push([best.r, 10]);
    });
    return o;
  }

  /* ================= 2.1 Rectangular Coordinates and Graphs ================= */
  var QN = ['Quadrant I', 'Quadrant II', 'Quadrant III', 'Quadrant IV'];
  function quadOf(x, y) { return x > 0 ? (y > 0 ? 0 : 3) : (y > 0 ? 1 : 2); }
  function lr(v) { return v > 0 ? 'right ' + v : 'left ' + (-v); }
  function ud(v) { return v > 0 ? 'up ' + v : 'down ' + (-v); }
  var c21 = [
    [
      function () { // read a point from the graph
        var x = rnz(-6, 6), y = rnz(-6, 6);
        var g = K.plane(place({ x: [-7, 7], y: [-7, 7], pts: [{ x: x, y: y, label: 'P', color: C.red }] }));
        return attach(Q({ q: 'What are the coordinates of point ' + I('P') + ' in the graph?', graph: g, mc: mc(K.pt(x, y), [K.pt(y, x), K.pt(-x, y), K.pt(x, -y)], function () { return K.pt(x + rnz(-2, 2), y + rnz(-2, 2)); }), why: ['Start at the origin. Move ' + lr(x) + ' along the ' + X + '-axis, so ' + m(I('x') + ' = ' + n(x)) + '.', 'Then move ' + ud(y) + ' parallel to the ' + Y + '-axis, so ' + m(I('y') + ' = ' + n(y)) + '.', 'The ' + X + '-coordinate is always written first: ' + I('P') + K.pt(x, y) + '.'] }), { kind: 'pt', x: x, y: y });
      },
      function () { // quadrant
        var x = rnz(-9, 9), y = rnz(-9, 9), qd = quadOf(x, y);
        return attach(Q({ q: 'In which quadrant does the point ' + K.pt(x, y) + ' lie?', mc: mc(QN[qd], QN.filter(function (z, i) { return i !== qd; })), why: ['The ' + X + '-coordinate ' + n(x) + ' is ' + (x > 0 ? 'positive (right of the ' + Y + '-axis)' : 'negative (left of the ' + Y + '-axis)') + '.', 'The ' + Y + '-coordinate ' + n(y) + ' is ' + (y > 0 ? 'positive (above the ' + X + '-axis)' : 'negative (below the ' + X + '-axis)') + '.', 'Quadrants are numbered I to IV counterclockwise from the upper right, so the point is in ' + QN[qd] + '.'] }), { kind: 'quad', x: x, y: y });
      },
      function () { // distance, whole-number answer
        var t = pick(TRI), x1 = ri(-6, 6), y1 = ri(-6, 6), x2 = x1 + (K.coin() ? t[0] : -t[0]), y2 = y1 + (K.coin() ? t[1] : -t[1]);
        var dx = x2 - x1, dy = y2 - y1, d = t[2], s2 = (x2 + x1) * (x2 + x1) + (y2 + y1) * (y2 + y1), rs = rad(s2);
        return attach(Q({ q: 'Find the distance between ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + '.', mc: mcV(n(d), d, [[n(d * d), d * d], [n(Math.abs(dx) + Math.abs(dy)), Math.abs(dx) + Math.abs(dy)], [rs.html, rs.v]], nx(d)), why: ['Differences: ' + m(n(x2) + ' ' + M + ' ' + sb(x1) + ' = ' + n(dx)) + ' and ' + m(n(y2) + ' ' + M + ' ' + sb(y1) + ' = ' + n(dy)) + '.', 'Square and add: ' + m(sb(dx) + '<sup>2</sup> + ' + sb(dy) + '<sup>2</sup> = ' + (dx * dx) + ' + ' + (dy * dy) + ' = ' + (d * d)) + '.', 'Take the square root: ' + m(I('d') + ' = ' + K.sqrt(String(d * d)) + ' = ' + d) + '.'] }), { kind: 'dist', x1: x1, y1: y1, x2: x2, y2: y2 });
      },
      function () { // midpoint
        var x1 = ri(-9, 9), y1 = ri(-9, 9), x2, y2;
        do { x2 = x1 + 2 * rnz(-6, 6); } while (Math.abs(x2) > 12);
        do { y2 = y1 + 2 * rnz(-6, 6); } while (Math.abs(y2) > 12);
        var mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
        return attach(Q({ q: 'Find the midpoint of the segment with endpoints ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + '.', mc: mc(K.pt(mx, my), [K.pt((x2 - x1) / 2, (y2 - y1) / 2), K.pt(x1 + x2, y1 + y2), K.pt(my, mx)], function () { return K.pt(mx + rnz(-2, 2), my + rnz(-2, 2)); }), why: ['Average the ' + X + '-values: ' + m(K.frx(n(x1) + ' + ' + sb(x2), '2') + ' = ' + K.frx(n(x1 + x2), '2') + ' = ' + n(mx)) + '.', 'Average the ' + Y + '-values: ' + m(K.frx(n(y1) + ' + ' + sb(y2), '2') + ' = ' + K.frx(n(y1 + y2), '2') + ' = ' + n(my)) + '.', 'The midpoint is ' + K.pt(mx, my) + '.'] }), { kind: 'mid', x1: x1, y1: y1, x2: x2, y2: y2 });
      }
    ],
    [
      function () { // distance in simplest radical form
        var dx, dy, N;
        do { dx = rnz(-7, 7); dy = rnz(-7, 7); N = dx * dx + dy * dy; } while (Math.round(Math.sqrt(N)) * Math.round(Math.sqrt(N)) === N);
        var x1 = ri(-6, 6), y1 = ri(-6, 6), x2 = x1 + dx, y2 = y1 + dy, r = rad(N);
        var se = (x2 + x1) * (x2 + x1) + (y2 + y1) * (y2 + y1), rse = rad(se);
        var wr = [[n(N), N], [n(Math.abs(dx) + Math.abs(dy)), Math.abs(dx) + Math.abs(dy)], [rse.html, rse.v]];
        if (r.a > 1) wr.unshift([n(r.a * r.a) + K.sqrt(String(r.b)), r.a * r.a * Math.sqrt(r.b)]);
        return attach(Q({ q: 'Find the distance between ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + '. Give the answer in simplest radical form.', mc: mcV(r.html, r.v, wr, function (i) { var z = rad(N + i); return [z.html, z.v]; }), why: ['Differences: ' + m(I('x') + ': ' + n(dx)) + ' and ' + m(I('y') + ': ' + n(dy)) + '.', 'Square and add: ' + m(sb(dx) + '<sup>2</sup> + ' + sb(dy) + '<sup>2</sup> = ' + (dx * dx) + ' + ' + (dy * dy) + ' = ' + N) + '.', 'Simplify: ' + m(I('d') + ' = ' + K.sqrt(String(N)) + (r.a > 1 ? ' = ' + K.sqrt(r.a * r.a + ' · ' + r.b) + ' = ' + r.html : '')) + (r.a > 1 ? '.' : ', which is already in simplest form.')] }), { kind: 'dist', x1: x1, y1: y1, x2: x2, y2: y2 });
      },
      function () { // other endpoint from midpoint
        var x1 = ri(-8, 8), y1 = ri(-8, 8), mx, my;
        do { mx = ri(-6, 6); my = ri(-6, 6); } while (mx === x1 && my === y1);
        var bx = 2 * mx - x1, by = 2 * my - y1;
        return attach(Q({ q: 'The midpoint of segment ' + I('AB') + ' is ' + I('M') + K.pt(mx, my) + '. Endpoint ' + I('A') + ' is ' + K.pt(x1, y1) + '. Find endpoint ' + I('B') + '.', mc: mc(K.pt(bx, by), [K.pt(R(x1 + mx, 2), R(y1 + my, 2)), K.pt(2 * mx + x1, 2 * my + y1), K.pt(mx - x1, my - y1)], function () { return K.pt(bx + rnz(-2, 2), by + rnz(-2, 2)); }), why: ['Let ' + I('B') + ' = (' + I('x') + ', ' + I('y') + '). The midpoint averages the endpoints: ' + m(K.frx(n(x1) + ' + ' + I('x'), '2') + ' = ' + n(mx)) + ' and ' + m(K.frx(n(y1) + ' + ' + I('y'), '2') + ' = ' + n(my)) + '.', 'Multiply by 2: ' + m(n(x1) + ' + ' + I('x') + ' = ' + n(2 * mx)) + ', so ' + m(I('x') + ' = ' + n(bx)) + '; ' + m(n(y1) + ' + ' + I('y') + ' = ' + n(2 * my)) + ', so ' + m(I('y') + ' = ' + n(by)) + '.', 'Check: the midpoint of ' + K.pt(x1, y1) + ' and ' + K.pt(bx, by) + ' is ' + K.pt(mx, my) + '. So ' + I('B') + K.pt(bx, by) + '.'] }), { kind: 'endpt', x1: x1, y1: y1, mx: mx, my: my });
      },
      function () { // intercepts of ax + by = c
        var a, b, c, p, q;
        do { a = rnz(-5, 5); b = rnz(-5, 5); c = K.lcm(a, b) * rnz(-2, 2); p = c / a; q = c / b; } while (Math.abs(p) > 10 || Math.abs(q) > 10 || p === q || p === -q);
        var ch = function (u, v) { return m(I('x') + '-intercept ' + K.pt(u, 0)) + '; ' + m(I('y') + '-intercept ' + K.pt(0, v)); };
        return attach(Q({ q: 'Find the ' + X + '- and ' + Y + '-intercepts of the graph of ' + m(P([[a, X], [b, Y]]) + ' = ' + n(c)) + '.', mc: mc(ch(p, q), [ch(q, p), ch(-p, -q), ch(c, c)], function () { return ch(p + rnz(-2, 2), q + rnz(-2, 2)); }), why: [X + '-intercept: set ' + m(I('y') + ' = 0') + ': ' + m(P([[a, X]]) + ' = ' + n(c)) + ', so ' + m(I('x') + ' = ' + n(p)) + '. Point ' + K.pt(p, 0) + '.', Y + '-intercept: set ' + m(I('x') + ' = 0') + ': ' + m(P([[b, Y]]) + ' = ' + n(c)) + ', so ' + m(I('y') + ' = ' + n(q)) + '. Point ' + K.pt(0, q) + '.', 'To find one intercept, set the other variable equal to 0.'] }), { kind: 'icpt', a: a, b: b, c: c });
      },
      function () { // which point is on the graph
        var a = pick([1, -1, 2]), b = ri(-3, 3), c = ri(-5, 5), f = function (x) { return a * x * x + b * x + c; };
        var xs = K.sample([-3, -2, -1, 0, 1, 2, 3], 4), x0 = xs[0], wrong = [];
        xs.slice(1).forEach(function (x) { var y = K.coin() ? -a * x * x + b * x + c : f(x) + rnz(-3, 3); if (y === f(x)) y = f(x) + 2; wrong.push(K.pt(x, y)); });
        var negs = xs.filter(function (x) { return x < 0; }), xn = x0 < 0 ? x0 : negs[0];
        return attach(Q({ q: 'Which point lies on the graph of ' + m(I('y') + ' = ' + quad(a, b, c)) + '?', mc: mc(K.pt(x0, f(x0)), wrong), why: ['A point is on the graph when its coordinates make the equation true.', 'Test ' + K.pt(x0, f(x0)) + ': ' + m(eqs(K.subst([[a, 2], [b, 1], [c, 0]], n(x0)), n(f(x0)))) + ' ✔.', 'Each of the other points gives a different ' + Y + '-value when its ' + X + '-value is substituted.' + (xn !== undefined ? ' Remember ' + m('(' + n(xn) + ')<sup>2</sup> = ' + xn * xn) + ', not ' + m(n(-xn * xn)) + '.' : '')] }), { kind: 'onGraph', a: a, b: b, c: c });
      }
    ],
    [
      function () { // right triangle?
        var vx = ri(-4, 4), vy = ri(-4, 4), u, v, t, A, B, Cc, isR = K.coin(), pts, ok;
        do {
          u = [rnz(-4, 4), rnz(-4, 4)]; t = pick([1, 2, -1, -2]); v = [-u[1] * t, u[0] * t];
          A = [vx + u[0], vy + u[1]]; B = [vx, vy]; Cc = [vx + v[0], vy + v[1]];
          if (!isR) { Cc = [Cc[0] + pick([-1, 1]), Cc[1] + pick([-1, 0, 1])]; }
          pts = [A, B, Cc];
          var d = function (p1, p2) { return (p1[0] - p2[0]) * (p1[0] - p2[0]) + (p1[1] - p2[1]) * (p1[1] - p2[1]); };
          var cr = (A[0] - B[0]) * (Cc[1] - B[1]) - (A[1] - B[1]) * (Cc[0] - B[0]);
          var dots = [0, 1, 2].map(function (i) { var p = pts[i], q1 = pts[(i + 1) % 3], q2 = pts[(i + 2) % 3]; return (q1[0] - p[0]) * (q2[0] - p[0]) + (q1[1] - p[1]) * (q2[1] - p[1]); });
          ok = cr !== 0 && pts.every(function (p) { return Math.abs(p[0]) <= 9 && Math.abs(p[1]) <= 9; }) && (isR ? dots.filter(function (z) { return z === 0; }).length === 1 : dots.every(function (z) { return z !== 0; }));
        } while (!ok);
        var names = K.shuffle(['A', 'B', 'C']), lab = {}; // pts[1] is the candidate right-angle vertex
        var order = [0, 1, 2].sort(function (i, j) { return names[i] < names[j] ? -1 : 1; });
        var dd = function (i, j) { var p = pts[i], q = pts[j]; return (p[0] - q[0]) * (p[0] - q[0]) + (p[1] - q[1]) * (p[1] - q[1]); };
        var sides = [[0, 1], [1, 2], [0, 2]].map(function (s) { var nm = [names[s[0]], names[s[1]]].sort().join(''); return { nm: nm, v: dd(s[0], s[1]), opp: names[3 - s[0] - s[1]] }; }).sort(function (a, b) { return a.v - b.v; });
        var right = isR ? 'A right triangle with the right angle at ' + I(names[1]) : 'Not a right triangle';
        var all = ['A', 'B', 'C'].map(function (L) { return 'A right triangle with the right angle at ' + I(L); }).concat(['Not a right triangle']);
        var vtx = order.map(function (i) { return I(names[i]) + K.pt(pts[i][0], pts[i][1]); }).join(', ');
        return attach(Q({ q: 'A triangle has vertices ' + vtx + '. Use the distance formula to decide whether it is a right triangle.', mc: mc(right, all.filter(function (z) { return z !== right; })), why: ['Squared side lengths: ' + sides.map(function (s) { return m(s.nm + '<sup>2</sup> = ' + s.v); }).join(', ') + '.', 'Check the Pythagorean theorem with the longest side: ' + m(sides[0].v + ' + ' + sides[1].v + ' = ' + (sides[0].v + sides[1].v)) + (sides[0].v + sides[1].v === sides[2].v ? ', which equals ' + m(sides[2].nm + '<sup>2</sup>') + ' ✔.' : ', which is not ' + m(sides[2].nm + '<sup>2</sup> = ' + sides[2].v) + '.'), isR ? 'So it is a right triangle. The right angle is opposite the longest side ' + sides[2].nm + ', at vertex ' + I(sides[2].opp) + '.' : 'The theorem fails, so it is not a right triangle.'] }), { kind: 'rtri', pts: order.map(function (i) { return [names[i], pts[i][0], pts[i][1]]; }) });
      },
      function () { // unknown coordinate from a distance
        var t = pick(TRI), x1 = rnz(-5, 5), y1 = rnz(-6, 6), x2 = x1 + (K.coin() ? t[0] : -t[0]), lo = y1 - t[1], hi = y1 + t[1];
        var ch = function (a, b) { return m(I('y') + ' = ' + n(Math.min(a, b)) + ' or ' + I('y') + ' = ' + n(Math.max(a, b))); };
        return attach(Q({ q: 'Find all values of ' + Y + ' so that the distance between ' + K.pt(x1, y1) + ' and ' + '(' + n(x2) + ', ' + I('y') + ')' + ' is ' + t[2] + '.', mc: mc(ch(lo, hi), [ch(y1 - t[0], y1 + t[0]), ch(-y1 - t[1], -y1 + t[1]), m(I('y') + ' = ' + n(hi)) + ' only'], function () { return ch(lo + rnz(-2, 2), hi); }), why: ['Distance formula: ' + m('(' + n(x2) + ' ' + M + ' ' + sb(x1) + ')<sup>2</sup> + (' + I('y') + ' ' + M + ' ' + sb(y1) + ')<sup>2</sup> = ' + t[2] + '<sup>2</sup>') + '.', m(t[0] * t[0] + ' + (' + K.minusH(I('y'), y1) + ')<sup>2</sup> = ' + t[2] * t[2]) + ', so ' + m('(' + K.minusH(I('y'), y1) + ')<sup>2</sup> = ' + t[1] * t[1]) + '.', 'Square root property: ' + m(K.minusH(I('y'), y1) + ' = ±' + t[1]) + ', so ' + m(I('y') + ' = ' + n(lo)) + ' or ' + m(I('y') + ' = ' + n(hi)) + '.'] }), { kind: 'findy', x1: x1, y1: y1, x2: x2, d: t[2] });
      },
      function () { // meet halfway
        var t = pick(TRI), s = (t[0] % 2 === 0 && t[1] % 2 === 0) ? 1 : 2, a = t[0] * s, b = t[1] * s, x1 = ri(0, 4), y1 = ri(0, 4), sx = K.coin() ? 1 : -1, sy = K.coin() ? 1 : -1;
        if (sx < 0) x1 += a; if (sy < 0) y1 += b;
        var x2 = x1 + sx * a, y2 = y1 + sy * b, d = t[2] * s, mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
        var ch = function (px, py, dd) { return 'Meet at ' + K.pt(px, py) + '; each drives ' + n(dd) + ' miles'; };
        return attach(Q({ q: 'On a city map measured in miles, Dana lives at ' + K.pt(x1, y1) + ' and Eli lives at ' + K.pt(x2, y2) + '. They agree to meet at the midpoint of the straight segment between their homes. Where do they meet, and how far (straight line) does each one travel?', mc: mc(ch(mx, my, d / 2), [ch(mx, my, d), ch(Math.abs(x2 - x1) / 2, Math.abs(y2 - y1) / 2, d / 2), ch(mx, my, (a + b) / 2)], function () { return ch(mx, my, d / 2 + rnz(1, 4)); }), why: ['Midpoint: ' + m('(' + K.frx(x1 + ' + ' + x2, '2') + ', ' + K.frx(y1 + ' + ' + y2, '2') + ') = ' + K.pt(mx, my).replace(/^\(/, '(')) + '.', 'Total distance: ' + m(K.sqrt(a + '<sup>2</sup> + ' + b + '<sup>2</sup>') + ' = ' + K.sqrt(String(a * a + b * b)) + ' = ' + d) + ' miles.', 'Each travels half of that: ' + m(d + ' ÷ 2 = ' + n(d / 2)) + ' miles.'] }), { kind: 'meet', x1: x1, y1: y1, x2: x2, y2: y2 });
      }
    ]
  ];
  K.lesson('2.1', { title: 'Rectangular Coordinates and Graphs', std: 'Lial 12e · Section 2.1', levels: c21 });

  /* ================= 2.2 Circles ================= */
  function cr(h, k, rh) { return 'Center ' + K.pt(h, k) + ', radius ' + rh; }
  function genForm(h, k, F, c) { c = c || 1; return m(P([[c, K.xp(2)], [c, K.xp(2, 'y')], [-2 * h * c, X], [-2 * k * c, Y], [F * c, '']]) + ' = 0'); }
  function circGraph(h, k, r, win) {
    win = win || 10;
    var g = K.plane({ x: [-win, win], y: [-win, win], segs: circSegs(h, k, r), pts: [{ x: h, y: k, color: C.red }] });
    desc('circle with center (' + n(h) + ', ' + n(k) + ') and radius ' + r);
    return g;
  }
  function crWhy(h, k) { return 'The signs inside flip: ' + m(sq('x', h)) + ' gives ' + m(I('h') + ' = ' + n(h)) + ' and ' + m(sq('y', k)) + ' gives ' + m(I('k') + ' = ' + n(k)) + '.'; }
  var c22 = [
    [
      function () { // write the equation
        var h, k; do { h = ri(-6, 6); k = ri(-6, 6); } while (h === 0 && k === 0);
        var r = ri(2, 9);
        return attach(Q({ q: 'Write the center-radius form of the equation of the circle with center ' + K.pt(h, k) + ' and radius ' + r + '.', mc: mc(circEq(h, k, r * r), [circEq(-h, -k, r * r), circEq(h, k, r), circEq(-h, -k, r)]), why: ['Center-radius form: ' + m('(' + I('x') + ' ' + M + ' ' + I('h') + ')<sup>2</sup> + (' + I('y') + ' ' + M + ' ' + I('k') + ')<sup>2</sup> = ' + I('r') + '<sup>2</sup>') + '.', 'Substitute ' + m(I('h') + ' = ' + n(h)) + ', ' + m(I('k') + ' = ' + n(k)) + ', ' + m(I('r') + ' = ' + r) + ': ' + m('(' + I('x') + ' ' + M + ' ' + sb(h) + ')<sup>2</sup> + (' + I('y') + ' ' + M + ' ' + sb(k) + ')<sup>2</sup> = ' + r + '<sup>2</sup>') + '.', 'Simplify: ' + circEq(h, k, r * r) + '. The right side is ' + I('r') + '<sup>2</sup>, not ' + I('r') + '.'] }), { kind: 'circEq', h: h, k: k, r2: r * r });
      },
      function () { // center & radius from center-radius form
        var h, k; do { h = rnz(-7, 7); k = rnz(-7, 7); } while (h === k);
        var r = ri(2, 9);
        return attach(Q({ q: 'Find the center and radius of the circle ' + circEq(h, k, r * r) + '.', mc: mc(cr(h, k, r), [cr(-h, -k, r), cr(h, k, r * r), cr(-h, -k, r * r)]), why: [crWhy(h, k), 'The right side is ' + m(I('r') + '<sup>2</sup> = ' + r * r) + ', so ' + m(I('r') + ' = ' + K.sqrt(String(r * r)) + ' = ' + r) + '.', 'Center ' + K.pt(h, k) + ', radius ' + r + '.'] }), { kind: 'cr', h: h, k: k, r2: r * r });
      },
      function () { // equation from the graph
        var r = ri(2, 5), h = ri(-9 + r, 9 - r), k = ri(-9 + r, 9 - r);
        if (h === 0 && k === 0) h = r === 5 ? 1 : 2;
        var g = circGraph(h, k, r);
        return attach(Q({ q: 'The graph shows a circle with its center marked. Which equation matches the graph?', graph: g, mc: mc(circEq(h, k, r * r), [circEq(-h, -k, r * r), circEq(h, k, r), circEq(-h, -k, r)]), why: ['Read the center from the graph: ' + K.pt(h, k) + '.', 'Count from the center to the circle (left, right, up, or down): the radius is ' + r + '.', 'So ' + circEq(h, k, r * r) + '. Inside the parentheses the signs are the opposite of the center’s coordinates.'] }), { kind: 'circEq', h: h, k: k, r2: r * r, gh: h, gk: k, gr: r });
      }
    ],
    [
      function () { // radius not a perfect square
        var h, k; do { h = rnz(-7, 7); k = rnz(-7, 7); } while (h === k);
        var N = pick([8, 12, 18, 20, 24, 27, 28, 32, 40, 44, 45, 48, 50, 52, 54, 63, 72, 75]), r = rad(N);
        var opts = [[cr(-h, -k, r.html), 1], [cr(h, k, n(N / 2)), 2], [cr(h, k, n(N)), 3]];
        return attach(Q({ q: 'Find the center and radius of the circle ' + circEq(h, k, N) + '. Give the radius in simplest radical form.', mc: mc(cr(h, k, r.html), opts.map(function (z) { return z[0]; })), why: [crWhy(h, k), m(I('r') + '<sup>2</sup> = ' + N) + ', so ' + m(I('r') + ' = ' + K.sqrt(String(N)) + ' = ' + K.sqrt(r.a * r.a + ' · ' + r.b) + ' = ' + r.html) + '.', 'Do not halve or keep ' + N + ': the radius is the square root of the right side.'] }), { kind: 'cr', h: h, k: k, r2: N });
      },
      function () { // general form -> center, radius
        var h = rnz(-6, 6), k = rnz(-6, 6), r = ri(2, 7), F = h * h + k * k - r * r;
        if (h === k) k = -k === h ? k + 1 : -k; if (k === 0) k = 2;
        F = h * h + k * k - r * r;
        var wr = [cr(-h, -k, n(r)), cr(h, k, n(r * r)), cr(-2 * h, -2 * k, n(r))];
        return attach(Q({ q: 'Find the center and radius of the circle ' + genForm(h, k, F) + '.', mc: mc(cr(h, k, n(r)), wr, function () { return cr(h, k, n(r + rnz(1, 3))); }), why: ['Group and move the constant: ' + m('(' + P([[1, K.xp(2)], [-2 * h, X]]) + ') + (' + P([[1, K.xp(2, 'y')], [-2 * k, Y]]) + ') = ' + n(-F)) + '.', 'Complete each square: add ' + m('(' + K.frx(n(-2 * h), '2') + ')<sup>2</sup> = ' + h * h) + ' and ' + m('(' + K.frx(n(-2 * k), '2') + ')<sup>2</sup> = ' + k * k) + ' to both sides: ' + circEq(h, k, n(-F) + ' + ' + h * h + ' + ' + k * k) + '.', 'So ' + circEq(h, k, r * r) + ': center ' + K.pt(h, k) + ', radius ' + m(K.sqrt(String(r * r)) + ' = ' + r) + '.'] }), { kind: 'crGen', D: -2 * h, E: -2 * k, F: F, c: 1 });
      },
      function () { // center and a point
        var h = ri(-5, 5), k = ri(-5, 5), a, b, N;
        do { a = ri(-6, 6); b = ri(-6, 6); N = a * a + b * b; } while (N < 2);
        var px = h + a, py = k + b, rr = rad(N);
        return attach(Q({ q: 'A circle has center ' + K.pt(h, k) + ' and passes through ' + K.pt(px, py) + '. Write its equation in center-radius form.', mc: mc(circEq(h, k, N), [circEq(px, py, N), circEq(-h, -k, N), circEq(h, k, rr.html)], function () { return circEq(h, k, N + rnz(1, 6)); }), why: ['The radius is the distance from the center to the point: ' + m(I('r') + '<sup>2</sup> = ' + sb(a) + '<sup>2</sup> + ' + sb(b) + '<sup>2</sup> = ' + N) + '.', 'You need ' + m(I('r') + '<sup>2</sup>') + ' for the equation, so there is no need to take the square root.', 'Equation: ' + circEq(h, k, N) + '.'] }), { kind: 'circPt', h: h, k: k, px: px, py: py });
      },
      function () { // diameter endpoints
        var x1 = ri(-7, 7), y1 = ri(-7, 7), dx, dy;
        do { dx = 2 * rnz(-4, 4); dy = 2 * ri(-4, 4); } while (Math.abs(x1 + dx) > 9 || Math.abs(y1 + dy) > 9);
        var x2 = x1 + dx, y2 = y1 + dy, h = (x1 + x2) / 2, k = (y1 + y2) / 2, r2 = (dx * dx + dy * dy) / 4;
        return attach(Q({ q: 'The endpoints of a diameter of a circle are ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + '. Write the equation of the circle in center-radius form.', mc: mc(circEq(h, k, r2), [circEq(h, k, 4 * r2), circEq(-h, -k, r2), circEq(x1, y1, r2)], function () { return circEq(h, k, r2 + rnz(1, 5)); }), why: ['The center is the midpoint: ' + m('(' + K.frx(n(x1) + ' + ' + sb(x2), '2') + ', ' + K.frx(n(y1) + ' + ' + sb(y2), '2') + ')') + ' = ' + K.pt(h, k) + '.', 'The diameter is ' + m(K.sqrt(sb(dx) + '<sup>2</sup> + ' + sb(dy) + '<sup>2</sup>') + ' = ' + K.sqrt(String(4 * r2))) + ', so ' + m(I('r') + '<sup>2</sup> = ' + K.frx(String(4 * r2), '4') + ' = ' + r2) + '.', 'Equation: ' + circEq(h, k, r2) + '. Using the full diameter as the radius gives ' + 4 * r2 + ' on the right, which is too big.'] }), { kind: 'circDiam', x1: x1, y1: y1, x2: x2, y2: y2 });
      }
    ],
    [
      function () { // circle, point, or no graph
        var h = rnz(-6, 6), k = rnz(-6, 6), type = pick(['c', 'c', 'p', 'n']), s;
        if (h === k) k = -k;
        s = type === 'p' ? 0 : type === 'c' ? pick([4, 9, 16, 25, 8, 12, 20]) : -pick([1, 4, 9, 5, 7, 16]);
        var F = h * h + k * k - s, rr = rad(Math.abs(s) || 1);
        var circ = function (a, b) { return 'A circle with center ' + K.pt(a, b) + ' and radius ' + rr.html; };
        var pnt = function (a, b) { return 'The single point ' + K.pt(a, b); }, none = 'No graph: no points satisfy the equation';
        var right = type === 'c' ? circ(h, k) : type === 'p' ? pnt(h, k) : none;
        var wr = type === 'c' ? [pnt(h, k), none, circ(-h, -k)] : type === 'p' ? [none, pnt(-h, -k), 'A circle with center ' + K.pt(h, k) + ' and radius ' + rad(h * h + k * k).html] : [circ(h, k), pnt(h, k), circ(-h, -k)];
        return attach(Q({ q: 'Describe the graph of ' + genForm(h, k, F) + '.', mc: mc(right, wr), why: ['Group and complete both squares: add ' + h * h + ' and ' + k * k + ' to both sides.', 'Result: ' + circEq(h, k, s) + '.', type === 'c' ? 'The right side is positive, so it is a circle: center ' + K.pt(h, k) + ', radius ' + m(K.sqrt(String(s)) + (rr.a > 1 || rr.b === 1 ? ' = ' + rr.html : '')) + '.' : type === 'p' ? 'The right side is 0. A sum of squares is 0 only when both are 0, so the graph is the single point ' + K.pt(h, k) + '.' : 'The right side is negative. A sum of squares can never be negative, so no point satisfies the equation.'] }), { kind: 'circType', D: -2 * h, E: -2 * k, F: F });
      },
      function () { // coverage application
        var h = ri(0, 8), k = ri(0, 8), R0 = ri(6, 12), dx, dy, d;
        do { dx = rnz(-12, 12); dy = rnz(-12, 12); d = Math.sqrt(dx * dx + dy * dy); } while (Math.abs(d - R0) < 0.25 || Math.abs(d - R0) > 4);
        var a = h + dx, b = k + dy, inside = d <= R0, ds = d.toFixed(1), N = dx * dx + dy * dy, L1 = Math.abs(dx) + Math.abs(dy);
        var ch = function (dist, ins) { return 'About ' + dist + ' mi; ' + (ins ? 'inside the coverage area' : 'outside the coverage area'); };
        return attach(Q({ q: 'A cell tower at ' + K.pt(h, k) + ' on a map grid measured in miles covers everything within ' + R0 + ' miles. Its boundary is ' + circEq(h, k, R0 * R0) + '. A house is at ' + K.pt(a, b) + '. How far is the house from the tower (to the nearest tenth of a mile), and is it covered?', mc: mc(ch(ds, inside), [ch(ds, !inside), ch(L1.toFixed(1), L1 <= R0), ch((N / 2).toFixed(1), N / 2 <= R0)], function () { var z = d + ri(1, 4) + 0.5; return ch(z.toFixed(1), z <= R0); }), why: ['Distance: ' + m(K.sqrt(sb(a - h) + '<sup>2</sup> + ' + sb(b - k) + '<sup>2</sup>') + ' = ' + K.sqrt(String(N)) + ' ≈ ' + ds) + ' miles.', 'Compare with the radius ' + R0 + ': ' + m(ds + (inside ? ' ≤ ' : ' &gt; ') + R0) + '.', inside ? 'The house is inside the circle, so it is covered.' : 'The house is outside the circle, so it is not covered.'] }), { kind: 'tower', h: h, k: k, R: R0, a: a, b: b });
      },
      function () { // leading coefficient not 1
        var h = rnz(-5, 5), k = rnz(-5, 5), c = pick([2, 3, 4]), N = pick([4, 9, 16, 25, 5, 8, 10, 13, 20]), F = h * h + k * k - N, rr = rad(N);
        if (h === k) k = -k;
        F = h * h + k * k - N;
        var wrongN = h * h + k * k - c * F, wr = [cr(-h, -k, rr.html), cr(h, k, n(N))];
        if (wrongN > 0 && wrongN !== N) wr.push(cr(h, k, rad(wrongN).html)); else wr.push(cr(c * h, c * k, rr.html));
        return attach(Q({ q: 'Find the center and radius of the circle ' + genForm(h, k, F, c) + '.', mc: mc(cr(h, k, rr.html), wr), why: ['Divide every term by ' + c + ' first: ' + genForm(h, k, F) + '.', 'Complete the squares (add ' + h * h + ' and ' + k * k + ' to both sides): ' + circEq(h, k, N) + '.', 'Center ' + K.pt(h, k) + ', radius ' + m(K.sqrt(String(N)) + (rr.a > 1 || rr.b === 1 ? ' = ' + rr.html : '')) + '.'] }), { kind: 'crGen', D: -2 * h * c, E: -2 * k * c, F: F * c, c: c });
      },
      function () { // tangent to an axis
        var h, k; do { h = rnz(-7, 7); k = rnz(-7, 7); } while (Math.abs(h) === Math.abs(k));
        var ax = K.coin() ? 'x' : 'y', r = ax === 'x' ? Math.abs(k) : Math.abs(h), o = ax === 'x' ? Math.abs(h) : Math.abs(k);
        return attach(Q({ q: 'A circle has center ' + K.pt(h, k) + ' and is tangent to (touches at exactly one point) the ' + I(ax) + '-axis. Write its equation in center-radius form.', mc: mc(circEq(h, k, r * r), [circEq(h, k, o * o), circEq(-h, -k, r * r), circEq(h, k, r)], function () { return circEq(h, k, (r + rnz(1, 3)) * (r + rnz(1, 3))); }), why: ['The ' + I(ax) + '-axis is the line ' + m(I(ax === 'x' ? 'y' : 'x') + ' = 0') + '. The radius is the distance from the center to that line.', 'That distance is the absolute value of the ' + I(ax === 'x' ? 'y' : 'x') + '-coordinate: ' + m(I('r') + ' = |' + n(ax === 'x' ? k : h) + '| = ' + r) + '.', 'Equation: ' + circEq(h, k, r * r) + '.'] }), { kind: 'tangent', h: h, k: k, ax: ax });
      }
    ]
  ];
  K.lesson('2.2', { title: 'Circles', std: 'Lial 12e · Section 2.2', levels: c22 });

  /* ================= 2.3 Functions ================= */
  function pairsH(ps) { return '{' + ps.map(function (p) { return K.pt(p[0], p[1]); }).join(', ') + '}'; }
  function relSet(isFn) {
    var xs = K.sample([-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6], 3), ps;
    if (isFn) { var ys = xs.map(function () { return ri(-6, 6); }); if (K.coin()) ys[2] = ys[0]; ps = xs.map(function (x, i) { return [x, ys[i]]; }); }
    else { var y1 = ri(-6, 6), y2; do { y2 = ri(-6, 6); } while (y2 === y1); ps = [[xs[0], y1], [xs[0], y2], [xs[1], ri(-6, 6)]]; }
    return K.shuffle(ps);
  }
  function DR(d, r) { return 'Domain ' + m(d) + '; range ' + m(r); }
  var c23 = [
    [
      function () { // function or not (ordered pairs)
        var askNot = K.coin(), right = relSet(!askNot), wr = [relSet(askNot), relSet(askNot), relSet(askNot)];
        var bad = askNot ? right : wr[0], rep = null;
        bad.forEach(function (p) { bad.forEach(function (q2) { if (p[0] === q2[0] && p[1] !== q2[1]) rep = [p, q2]; }); });
        return attach(Q({ q: 'Which relation is ' + (askNot ? '<b>not</b> a function' : 'a function') + '?', mc: mc(pairsH(right), wr.map(pairsH), function () { return pairsH(relSet(askNot)); }), why: ['A relation is a function when no ' + X + '-value is paired with two different ' + Y + '-values. Repeated ' + Y + '-values are fine.', 'In ' + pairsH(bad) + ', the input ' + n(rep[0][0]) + ' goes to both ' + n(rep[0][1]) + ' and ' + n(rep[1][1]) + ', so that relation is not a function.', askNot ? 'In every other relation, each ' + X + '-value appears only once.' : 'In ' + pairsH(right) + ', each ' + X + '-value appears only once, so it is the function.'] }), { kind: 'isFn', askNot: askNot });
      },
      function () { // evaluate f(a)
        var a = pick([1, 2, 3, -1, -2, -3]), b = rnz(-6, 6), c = ri(-9, 9), v = ri(-4, -1), f = a * v * v + b * v + c;
        return attach(Q({ q: 'Let ' + fx('f', quad(a, b, c)) + '. Find ' + m(I('f') + '(' + n(v) + ')') + '.', mc: mcV(n(f), f, [[n(-a * v * v + b * v + c), -a * v * v + b * v + c], [n(a * v * v - b * v + c), a * v * v - b * v + c], [n(a * 2 * v + b * v + c), a * 2 * v + b * v + c]], nx(f)), why: ['Replace every ' + X + ' with ' + m('(' + n(v) + ')') + ': ' + m(K.subst([[a, 2], [b, 1], [c, 0]], n(v))) + '.', 'Square first: ' + m('(' + n(v) + ')<sup>2</sup> = ' + v * v) + ' (not ' + n(-v * v) + ').', 'Then ' + m(n(a * v * v) + K.plusK(b * v) + K.plusK(c) + ' = ' + n(f)) + '.'] }), { kind: 'fval', fq: true, x: v });
      },
      function () { // domain or range of a set of pairs
        var xs = K.sample([-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8], 4), ys = xs.map(function () { return ri(-9, 9); });
        ys[3] = ys[K.ri(0, 2)];
        var ps = xs.map(function (x, i) { return [x, ys[i]]; }), askD = K.coin(), mine = askD ? xs : ys, other = askD ? ys : xs;
        var drop = setH(mine).replace(/[{}]/g, '').split(', '); drop.splice(ri(0, drop.length - 1), 1);
        return attach(Q({ q: 'Give the ' + (askD ? 'domain' : 'range') + ' of the relation ' + pairsH(ps) + '.', mc: mc(setH(mine), [setH(other), setH(mine.concat(other)), drop.length ? '{' + drop.join(', ') + '}' : null], function () { return setH(mine.map(function (v, i) { return i === 0 ? v + rnz(1, 3) : v; })); }), why: ['The ' + (askD ? 'domain is the set of first coordinates (' + X + '-values)' : 'range is the set of second coordinates (' + Y + '-values)') + '.', 'List each value once, even if it repeats: ' + setH(mine) + '.', 'The ' + (askD ? 'range' : 'domain') + ' would be ' + setH(other) + '.'] }), { kind: 'drSet', pairs: ps, askD: askD });
      },
      function () { // vertical line test
        var t = pick(['par', 'abs', 'cub', 'side', 'circ', 'side']), h = ri(-2, 2), k = ri(-2, 2), fns = [], segs = [];
        if (t === 'par') fns.push({ f: function (x) { return (x - h) * (x - h) + k - 3; } });
        if (t === 'abs') fns.push({ f: function (x) { return Math.abs(x - h) + k - 2; } });
        if (t === 'cub') fns.push({ f: function (x) { return (x - h) * (x - h) * (x - h) / 2 + k; } });
        if (t === 'side') { fns.push({ f: function (x) { return k + Math.sqrt(x - h + 3); }, from: h - 3, to: 7 }); fns.push({ f: function (x) { return k - Math.sqrt(x - h + 3); }, from: h - 3, to: 7 }); }
        if (t === 'circ') segs = circSegs(h, k, 3);
        var g = K.plane({ x: [-7, 7], y: [-7, 7], fns: fns, segs: segs });
        desc(t === 'side' ? 'sideways parabola opening right' : t === 'circ' ? 'circle of radius 3' : 'a curve: ' + t);
        var isF = t === 'par' || t === 'abs' || t === 'cub';
        var A = ['Yes, because no vertical line crosses the graph more than once', 'No, because some vertical line crosses the graph more than once', 'Yes, because no horizontal line crosses the graph more than once', 'No, because some horizontal line crosses the graph more than once'];
        return attach(Q({ q: 'Does the graph represent ' + Y + ' as a function of ' + X + '?', graph: g, mc: mc(A[isF ? 0 : 1], A.filter(function (z, i) { return i !== (isF ? 0 : 1); })), why: ['Use the <b>vertical</b> line test: a vertical line is one ' + X + '-value.', isF ? 'Every vertical line crosses this graph at most once, so each ' + X + ' has exactly one ' + Y + '.' : 'A vertical line such as ' + m(I('x') + ' = ' + n(h + 1)) + ' crosses this graph twice, so one ' + X + '-value has two ' + Y + '-values.', isF ? 'So it is a function. (The horizontal line test is not the test for a function.)' : 'So it is not a function.'] }), { kind: 'vlt', t: t });
      },
      function () { // read f(c) from a graph
        var lin2 = K.coin(), h = ri(-2, 2), k = ri(-3, 2), s = pick([1, -1]), mm = pick([1, 2, -1, -2, 3, -3]), b = ri(-3, 3), f, c;
        if (lin2) f = function (x) { return mm * x + b; }; else f = function (x) { return s * (x - h) * (x - h) + (s > 0 ? k - 2 : k + 3); };
        if (lin2 && mm === 1 && b === 0) b = 2;
        do { c = rnz(-4, 4); } while (Math.abs(f(c)) > 7 || c === f(c));
        var g = K.plane({ x: [-8, 8], y: [-8, 8], fns: [{ f: f }] });
        return attach(Q({ q: 'The graph of ' + m(I('y') + ' = ' + I('f') + '(' + I('x') + ')') + ' is shown. Find ' + m(I('f') + '(' + n(c) + ')') + '.', graph: g, mc: mcV(n(f(c)), f(c), [[n(c), c], [n(f(-c)), f(-c)], [n(-f(c)), -f(c)]], nx(f(c))), why: [m(I('f') + '(' + n(c) + ')') + ' is the height of the graph above (or below) ' + m(I('x') + ' = ' + n(c)) + '.', 'Go to ' + m(I('x') + ' = ' + n(c)) + ' on the ' + X + '-axis' + (f(c) === 0 ? ': the graph meets the ' + X + '-axis right there, so the point is ' : ' and move ' + (f(c) > 0 ? 'up' : 'down') + ' to the graph: the point is ') + K.pt(c, f(c)) + '.', 'So ' + m(I('f') + '(' + n(c) + ') = ' + n(f(c))) + '.'] }), { kind: 'readF', lin: lin2, mm: mm, b: b, h: h, kk: s > 0 ? k - 2 : k + 3, s: s, c: c });
      }
    ],
    [
      function () { // domain & range from a graph
        var t = pick(['par', 'sqrt', 'seg', 'seg']), d, r, wr = [], g, p;
        if (t === 'par') {
          var s = pick([1, -1]), h = ri(-4, 4), k; do { k = ri(-4, 4); } while (k === h);
          g = K.plane({ x: [-8, 8], y: [-8, 8], fns: [{ f: function (x) { return s * (x - h) * (x - h) + k; } }], pts: [{ x: h, y: k }] });
          d = ALL; r = s > 0 ? iv(k, Infinity, true) : iv(-Infinity, k, false, true);
          wr = [DR(r, d), DR(d, s > 0 ? iv(k, Infinity, false) : iv(-Infinity, k)), DR(d, s > 0 ? iv(h, Infinity, true) : iv(-Infinity, h, false, true))];
          p = { t: t, s: s, h: h, k: k };
        } else if (t === 'sqrt') {
          var s2 = pick([1, -1]), h2 = ri(-6, 0), k2 = ri(-3, 3); if (h2 === k2) k2 = k2 + 1;
          g = K.plane({ x: [-8, 8], y: [-8, 8], fns: [{ f: function (x) { return s2 * Math.sqrt(x - h2) + k2; }, from: h2 }], pts: [{ x: h2, y: k2 }] });
          d = iv(h2, Infinity, true); r = s2 > 0 ? iv(k2, Infinity, true) : iv(-Infinity, k2, false, true);
          wr = [DR(r, d), DR(ALL, r), DR(iv(h2, Infinity, false), s2 > 0 ? iv(k2, Infinity, false) : iv(-Infinity, k2))];
          p = { t: t, s: s2, h: h2, k: k2 };
        } else {
          var x1 = ri(-7, -1), x2 = ri(1, 7), y1, y2; do { y1 = ri(-6, 6); y2 = ri(-6, 6); } while (y1 === y2);
          var c1 = K.coin(), c2 = K.coin();
          g = K.plane({ x: [-8, 8], y: [-8, 8], segs: [{ x1: x1, y1: y1, x2: x2, y2: y2 }], pts: [{ x: x1, y: y1, open: !c1 }, { x: x2, y: y2, open: !c2 }] });
          d = iv(x1, x2, c1, c2);
          r = y1 < y2 ? iv(y1, y2, c1, c2) : iv(y2, y1, c2, c1);
          wr = [DR(r, d), DR(iv(x1, x2, !c1, c2), r), DR(d, y1 < y2 ? iv(y1, y2, !c1, c2) : iv(y2, y1, !c2, c1)), DR(iv(x1, x2, !c1, !c2), r)];
          p = { t: t, x1: x1, y1: y1, x2: x2, y2: y2, c1: c1, c2: c2 };
        }
        p.kind = 'drGraph';
        return attach(Q({ q: 'Use the graph to find the domain and range of the function. Write each in interval notation.' + (t === 'seg' ? ' (A closed dot is included; an open dot is not.)' : ' (The graph continues without end in the direction it is heading.)'), graph: g, mc: mc(DR(d, r), wr, function () { return DR(d, iv(ri(-6, 6), Infinity, true)); }), why: ['Domain: read the ' + X + '-values the graph covers from left to right: ' + m(d) + '.', 'Range: read the ' + Y + '-values the graph covers from bottom to top: ' + m(r) + '.', t === 'seg' ? 'Use a bracket for an endpoint with a closed dot and a parenthesis for an open dot.' : 'Use a bracket where the graph reaches its starting value; ∞ always gets a parenthesis.'] }), p);
      },
      function () { // domain from a formula
        var t = pick(['s1', 's2', 'q', 'qs', 'lin']), a = rnz(-6, 6), c = rnz(-5, 5), f, d, wr, why;
        if (t === 's1') { f = K.sqrt(K.minusH(I('x'), a)); d = iv(a, Infinity, true); wr = [iv(a, Infinity), iv(-Infinity, a, false, true), iv(-a, Infinity, true)]; why = ['The expression under a square root must be nonnegative: ' + m(K.minusH(I('x'), a) + ' ≥ 0') + '.', 'So ' + m(I('x') + ' ≥ ' + n(a)) + '.']; }
        if (t === 's2') { f = K.sqrt(P([[a, ''], [-1, X]])); d = iv(-Infinity, a, false, true); wr = [iv(a, Infinity, true), iv(-Infinity, a), iv(-Infinity, -a, false, true)]; why = ['The expression under a square root must be nonnegative: ' + m(P([[a, ''], [-1, X]]) + ' ≥ 0') + '.', 'So ' + m(n(a) + ' ≥ ' + I('x')) + ', that is, ' + m(I('x') + ' ≤ ' + n(a)) + '.']; }
        if (t === 'q') { f = K.frx(n(c), K.minusH(I('x'), a)); d = cup([iv(-Infinity, a), iv(a, Infinity)]); wr = [ALL, cup([iv(-Infinity, -a), iv(-a, Infinity)]), iv(a, Infinity)]; why = ['A denominator cannot be 0: ' + m(K.minusH(I('x'), a) + ' ≠ 0') + ', so ' + m(I('x') + ' ≠ ' + n(a)) + '.', 'Every other real number works.']; }
        if (t === 'qs') { f = K.frx(n(c), K.sqrt(K.minusH(I('x'), a))); d = iv(a, Infinity); wr = [iv(a, Infinity, true), cup([iv(-Infinity, a), iv(a, Infinity)]), ALL]; why = ['Under the root: ' + m(K.minusH(I('x'), a) + ' ≥ 0') + '. In the denominator: the root cannot be 0.', 'Together: ' + m(K.minusH(I('x'), a) + ' &gt; 0') + ', so ' + m(I('x') + ' &gt; ' + n(a)) + '.']; }
        if (t === 'lin') { var b = pick([2, 3, 4, 5]), tt = rnz(-5, 5); f = K.sqrt(lin(b, -b * tt)); d = iv(tt, Infinity, true); wr = [iv(-tt, Infinity, true), iv(-Infinity, tt, false, true), iv(-b * tt, Infinity, true)]; why = ['Set the radicand ≥ 0: ' + m(lin(b, -b * tt) + ' ≥ 0') + '.', 'So ' + m(P([[b, X]]) + ' ≥ ' + n(b * tt)) + ' and ' + m(I('x') + ' ≥ ' + n(tt)) + '.']; }
        return attach(Q({ q: 'Find the domain of ' + fx('f', f) + '. Write it in interval notation.', mc: mc(m(d), wr.map(m), function () { return m(iv(a + rnz(1, 3), Infinity, true)); }), why: why.concat(['Domain: ' + m(d) + '.']) }), { kind: 'domF', fq: true });
      },
      function () { // f(-x)
        var a = rnz(-5, 5), b = rnz(-7, 7), c = rnz(-9, 9);
        return attach(Q({ q: 'Let ' + fx('f', quad(a, b, c)) + '. Find ' + m(I('f') + '(' + M + I('x') + ')') + ' and simplify.', mc: mc(m(quad(a, -b, c)), [m(quad(-a, -b, -c)), m(quad(a, b, c)), m(quad(-a, -b, c))]), why: ['Replace each ' + X + ' with ' + m('(' + M + I('x') + ')') + ': ' + m(K.coef(a, true) + '(' + M + I('x') + ')<sup>2</sup>' + K.coef(b) + '(' + M + I('x') + ')' + K.plusK(c)) + '.', m('(' + M + I('x') + ')<sup>2</sup> = ' + I('x') + '<sup>2</sup>') + ', and ' + m(K.coef(b, true) + '(' + M + I('x') + ') = ' + P([[-b, X]])) + '.', 'So ' + m(I('f') + '(' + M + I('x') + ') = ' + quad(a, -b, c)) + '. Only the odd-power term changed sign.'] }), { kind: 'fneg', fq: true });
      },
      function () { // rewrite as f(x) and evaluate
        var a = rnz(-6, 6), b = pick([2, 3, 4, -2, -3, -4]), c = b * rnz(-5, 5), k = b * ri(-3, 3);
        var mm = R(-a, b), bb = R(c, b), fk = mm.mul(k).add(bb);
        var ch = function (s1, b1) { return m(I('f') + '(' + I('x') + ') = ' + lin(s1, b1)) + '; ' + m(I('f') + '(' + n(k) + ') = ' + R(s1).mul(k).add(b1).html()); };
        return attach(Q({ q: 'Solve ' + m(P([[a, X], [b, Y]]) + ' = ' + n(c)) + ' for ' + Y + ', write it with function notation ' + m(I('f') + '(' + I('x') + ')') + ', and find ' + m(I('f') + '(' + n(k) + ')') + '.', mc: mc(ch(mm, bb), [ch(mm.neg(), bb), ch(mm, R(c)), ch(mm, bb.neg())], function () { return ch(mm, bb.add(rnz(1, 3))); }), why: ['Isolate the ' + Y + '-term: ' + m(P([[b, Y]]) + ' = ' + lin(-a, c)) + '.', 'Divide every term by ' + n(b) + ': ' + m(I('y') + ' = ' + lin(mm, bb)) + ', so ' + m(I('f') + '(' + I('x') + ') = ' + lin(mm, bb)) + '.', m(I('f') + '(' + n(k) + ') = ' + K.lin([[mm, n(k)]]) + K.plusK(bb) + ' = ' + fk.html()) + '.'] }), { kind: 'rewrite', a: a, b: b, c: c, x: k });
      }
    ],
    [
      function () { // increasing / decreasing / constant intervals
        var beh, ok, xs, ys;
        do {
          beh = [pick(['i', 'd', 'c'])]; while (beh.length < 4) { var nb = pick(['i', 'd', 'c']); if (nb !== beh[beh.length - 1]) beh.push(nb); }
          xs = [ri(-8, -6)]; for (var i = 0; i < 4; i++) xs.push(xs[i] + ri(2, 4));
          ys = [ri(-3, 3)]; for (i = 0; i < 4; i++) ys.push(ys[i] + (beh[i] === 'i' ? ri(1, 4) : beh[i] === 'd' ? -ri(1, 4) : 0));
          ok = xs[4] <= 8 && ys.every(function (y) { return Math.abs(y) <= 7; });
        } while (!ok);
        var ask = pick(beh), W = { i: 'increasing', d: 'decreasing', c: 'constant' };
        var ivs = function (b) { var out = []; beh.forEach(function (z, i) { if (z === b) out.push(iv(xs[i], xs[i + 1])); }); return out.length ? cup(out) : null; };
        var segs = [], pts = [{ x: xs[0], y: ys[0] }, { x: xs[4], y: ys[4] }];
        for (i = 0; i < 4; i++) segs.push({ x1: xs[i], y1: ys[i], x2: xs[i + 1], y2: ys[i + 1] });
        var g = K.plane({ x: [-9, 9], y: [-8, 8], segs: segs, pts: pts });
        desc('polyline through ' + xs.map(function (x, i) { return '(' + n(x) + ', ' + n(ys[i]) + ')'; }).join(' '));
        var wr = ['i', 'd', 'c'].filter(function (b) { return b !== ask && ivs(b); }).map(function (b) { return m(ivs(b)); });
        var j = beh.indexOf(ask); if (ask !== 'c') wr.push(m(iv(Math.min(ys[j], ys[j + 1]), Math.max(ys[j], ys[j + 1]))));
        wr.push(m(iv(xs[0], xs[4])));
        return attach(Q({ q: 'The graph of a function ' + I('f') + ' is shown. On what open interval(s) is ' + I('f') + ' <b>' + W[ask] + '</b>?', graph: g, mc: mc(m(ivs(ask)), wr, function () { var i0 = ri(0, 3), j0 = ri(i0 + 1, 4); return m(iv(xs[i0], xs[j0])); }), why: ['Read the graph from left to right and watch the ' + Y + '-values.', beh.map(function (z, i) { return m(iv(xs[i], xs[i + 1])) + ': ' + W[z]; }).join('; ') + '.', 'Intervals are stated with ' + X + '-values, so ' + I('f') + ' is ' + W[ask] + ' on ' + m(ivs(ask)) + '.'] }), { kind: 'incdec', xs: xs, ys: ys, ask: ask });
      },
      function () { // taxi application
        var r = pick([1.5, 2, 2.25, 2.5, 2.75, 3]), b = pick([2.5, 3, 3.5, 4, 5]), k = ri(4, 15), v = b + r * k;
        var ch = function (s1, b1, val) { return m(I('C') + '(' + I('x') + ') = ' + n(s1) + I('x') + (b1 ? ' + ' + n(b1) : '')) + '; ' + m(I('C') + '(' + k + ') = ' + K.money(val)); };
        return attach(Q({ q: 'A taxi charges a base fare of ' + K.money(b) + ' plus ' + K.money(r) + ' per mile. Write the cost ' + m(I('C') + '(' + I('x') + ')') + ' in dollars for a ride of ' + X + ' miles, and find the cost of ' + art(k) + ' ' + k + '-mile ride.', mc: mc(ch(r, b, v), [ch(b, r, b * k + r), ch(r, b, r * k), ch(r + b, 0, (r + b) * k)], function () { return ch(r, b, v + rnz(1, 6)); }), why: ['The fixed part is the base fare ' + K.money(b) + '; the per-mile rate ' + K.money(r) + ' is the slope.', 'So ' + m(I('C') + '(' + I('x') + ') = ' + n(r) + I('x') + ' + ' + n(b)) + '.', brk(I('C') + '(' + k + ') = ' + n(r) + '(' + k + ') + ' + n(b) + ' = ' + n(r * k) + ' + ' + n(b) + ' = ' + n(v)) + ', so the ride costs ' + K.money(v) + '.'] }), { kind: 'taxi', r: r, b: b, x: k });
      },
      function () { // domain of sqrt over linear
        var a = ri(-6, 6), b; do { b = ri(-6, 6); } while (b === a);
        var f = K.frx(K.sqrt(K.minusH(I('x'), a)), K.minusH(I('x'), b));
        var d = b > a ? cup([iv(a, b, true), iv(b, Infinity)]) : iv(a, Infinity, true);
        var pool = [iv(a, Infinity, true), iv(a, Infinity), cup([iv(-Infinity, b), iv(b, Infinity)]), iv(b, Infinity, true), iv(b, Infinity)];
        if (b > a) pool.push(cup([iv(a, b), iv(b, Infinity)]));
        return attach(Q({ q: 'Find the domain of ' + fx('f', f) + '. Write it in interval notation.', mc: mc(m(d), K.shuffle(pool.filter(function (z) { return z !== d; })).map(m)), why: ['Numerator: the radicand must be nonnegative, so ' + m(I('x') + ' ≥ ' + n(a)) + '.', 'Denominator: ' + m(K.minusH(I('x'), b) + ' ≠ 0') + ', so ' + m(I('x') + ' ≠ ' + n(b)) + '.', b > a ? 'The value ' + n(b) + ' is in ' + m(iv(a, Infinity, true)) + ', so remove it: ' + m(d) + '.' : 'The value ' + n(b) + ' is already excluded by ' + m(I('x') + ' ≥ ' + n(a)) + ', so the domain is ' + m(d) + '.'] }), { kind: 'domF', fq: true });
      },
      function () { // find a constant from a function value
        var t = rnz(-4, 4), k = rnz(-6, 6), c = ri(-8, 8), v = t * t + k * t + c;
        var w1 = R(v + t * t - c, t), w2 = R(v - t * t + c, t), w3 = R(-(v - t * t - c), t);
        return attach(Q({ q: 'Let ' + fx('f', P([[1, K.xp(2)], [1, I('k') + I('x')], [c, '']])) + ', where ' + I('k') + ' is a constant. If ' + m(I('f') + '(' + n(t) + ') = ' + n(v)) + ', what is ' + I('k') + '?', mc: mcV(n(k), k, [[w1.html(), w1.val()], [w2.html(), w2.val()], [w3.html(), w3.val()]], nx(k)), why: ['Substitute ' + m(I('x') + ' = ' + n(t)) + ': ' + m(sb(t) + '<sup>2</sup>' + K.coef(t) + I('k') + K.plusK(c) + ' = ' + n(v)) + '.', 'Simplify: ' + m(P([[t, I('k')], [t * t + c, '']]) + ' = ' + n(v)) + ', so ' + m(P([[t, I('k')]]) + ' = ' + n(v - t * t - c)) + '.', 'Divide by ' + n(t) + ': ' + m(I('k') + ' = ' + n(k)) + '.'] }), { kind: 'findk', t: t, c: c, v: v });
      }
    ]
  ];
  K.lesson('2.3', { title: 'Functions', std: 'Lial 12e · Section 2.3', levels: c23 });

  /* ================= 2.4 Linear Functions ================= */
  function icH(px, qy) { return m(I('x') + '-intercept ' + K.pt(px, 0)) + '; ' + m(I('y') + '-intercept ' + K.pt(0, qy)); }
  function slopeOpts(mm) { return [[mm.neg().html(), mm.neg().val()], mm.n ? [R(mm.d, mm.n).html(), mm.d / mm.n] : null, mm.n ? [R(-mm.d, mm.n).html(), -mm.d / mm.n] : null].filter(Boolean); }
  function slopeX(mm) { return function (i) { var z = mm.add(R(K.rnz(-3, 3), K.pick([1, 2]))); return [z.html(), z.val()]; }; }
  var c24 = [
    [
      function () { // slope through two points
        var x1 = ri(-7, 7), y1 = ri(-7, 7), x2, y2;
        do { x2 = ri(-7, 7); y2 = ri(-7, 7); } while (x2 === x1 || y2 === y1);
        var mm = R(y2 - y1, x2 - x1);
        return attach(Q({ q: 'Find the slope of the line through ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + '.', mc: mcV(mm.html(), mm.val(), slopeOpts(mm), slopeX(mm)), why: ['Change in ' + Y + ': ' + m(n(y2) + ' ' + M + ' ' + sb(y1) + ' = ' + n(y2 - y1)) + '. Change in ' + X + ': ' + m(n(x2) + ' ' + M + ' ' + sb(x1) + ' = ' + n(x2 - x1)) + '.', m(I('m') + ' = ' + eqs(frq(y2 - y1, x2 - x1), mm.html())) + '.', 'Keep the ' + Y + '-change on top and subtract in the same order.'] }), { kind: 'slope2', x1: x1, y1: y1, x2: x2, y2: y2 });
      },
      function () { // horizontal/vertical slope
        var c = pick([2, 3, 4, 5, 6, 7, -2, -3, -4, -5, -6, -7]), vert = K.coin();
        var right = vert ? 'Undefined' : '0', all = ['0', 'Undefined', n(c), n(-c)];
        return attach(Q({ q: 'What is the slope of the line ' + m(I(vert ? 'x' : 'y') + ' = ' + n(c)) + '?', mc: mc(right, all.filter(function (z) { return z !== right; })), why: [vert ? 'Every point on ' + m(I('x') + ' = ' + n(c)) + ' has ' + X + '-coordinate ' + n(c) + ', so the line is vertical.' : 'Every point on ' + m(I('y') + ' = ' + n(c)) + ' has ' + Y + '-coordinate ' + n(c) + ', so the line is horizontal.', vert ? 'The run is ' + m(I('x') + '<sub>2</sub> ' + M + ' ' + I('x') + '<sub>1</sub> = 0') + ', and division by 0 is not defined.' : 'The rise is 0, so the slope is ' + m('0 ÷ run = 0') + '.', vert ? 'A vertical line has no defined slope, so the answer is Undefined.' : 'So the slope is 0.'] }), { kind: 'hv', vert: vert, c: c });
      },
      function () { // x-intercept of f(x) = ax + b
        var r = rnz(-6, 6), a = rnz(-5, 5), b = -a * r;
        return attach(Q({ q: 'Find the ' + X + '-intercept of the graph of ' + fx('f', lin(a, b)) + '.', mc: mc(K.pt(r, 0), [K.pt(0, b), K.pt(-r, 0), K.pt(b, 0)], function () { return K.pt(r + rnz(-3, 3), 0); }), why: ['At the ' + X + '-intercept, ' + m(I('f') + '(' + I('x') + ') = 0') + ': ' + m(lin(a, b) + ' = 0') + '.', a === 1 ? (b > 0 ? 'Subtract ' + b + ' from' : 'Add ' + (-b) + ' to') + ' both sides: ' + m(I('x') + ' = ' + n(r)) + '.' : m(P([[a, X]]) + ' = ' + n(-b)) + ', so ' + m(I('x') + ' = ' + n(r)) + '.', 'The ' + X + '-intercept is ' + K.pt(r, 0) + '. (' + K.pt(0, b) + ' is the ' + Y + '-intercept.)'] }), { kind: 'xint', fq: true });
      },
      function () { // slope from the graph
        var mm = pick(SL), b = ri(-3, 3), xs = [], x;
        for (x = -6; x <= 6; x++) { var yv = mm.mul(x).add(b); if (yv.isInt() && Math.abs(yv.val()) <= 6) xs.push(x); }
        var xa = xs[ri(0, Math.max(0, xs.length - 2))], xb = xs[xs.indexOf(xa) + 1] !== undefined ? xs[xs.indexOf(xa) + 1] : xs[0];
        var g = K.plane({ x: [-7, 7], y: [-7, 7], lines: [{ m: mm, b: b }], pts: [{ x: xa, y: mm.mul(xa).add(b).val() }, { x: xb, y: mm.mul(xb).add(b).val() }] });
        var rise = mm.mul(xb - xa).val(), run = xb - xa;
        return attach(Q({ q: 'Find the slope of the line in the graph. (Two points on the line are marked.)', graph: g, mc: mcV(mm.html(), mm.val(), slopeOpts(mm), slopeX(mm)), why: ['The marked points are ' + K.pt(xa, mm.mul(xa).add(b)) + ' and ' + K.pt(xb, mm.mul(xb).add(b)) + '.', 'Rise ' + n(rise) + ', run ' + n(run) + ': ' + m(I('m') + ' = ' + eqs(frq(rise, run), mm.html())) + '.', 'The line ' + (mm.n > 0 ? 'rises' : 'falls') + ' from left to right, so the slope is ' + (mm.n > 0 ? 'positive' : 'negative') + '.'] }), { kind: 'lineSlope', m: [mm.n, mm.d], b: b });
      }
    ],
    [
      function () { // slope from standard form
        var A = rnz(-6, 6), B = rnz(-6, 6), Cc = ri(-12, 12), mm = R(-A, B);
        return attach(Q({ q: 'Find the slope of the line ' + m(P([[A, X], [B, Y]]) + ' = ' + n(Cc)) + '.', mc: mcV(mm.html(), mm.val(), [[R(A, B).html(), A / B], [R(-B, A).html(), -B / A], [R(B, A).html(), B / A]], slopeX(mm)), why: ['Solve for ' + Y + ': ' + m(P([[B, Y]]) + ' = ' + lin(-A, Cc)) + '.', 'Divide by ' + n(B) + ': ' + m(I('y') + ' = ' + lin(mm, R(Cc, B))) + '.', 'The slope is the coefficient of ' + X + ': ' + m(I('m') + ' = ' + mm.html()) + '. (Shortcut: ' + m(I('m') + ' = ' + M + K.frx(I('A'), I('B'))) + '.)'] }), { kind: 'stdSlope', A: A, B: B, C: Cc });
      },
      function () { // average rate of change
        var y1 = ri(2004, 2014), dt = pick([4, 5, 8, 10]), r = pick([20, 35, 45, 60, 80, 120, -20, -35, -45, -60]), p1 = ri(12, 40) * 100, p2 = p1 + r * dt;
        var u = ' residents per year', f1 = function (v) { return n(v, 1) + u; };
        return attach(Q({ q: 'A town had ' + K.comma(p1) + ' residents in ' + y1 + ' and ' + K.comma(p2) + ' residents in ' + (y1 + dt) + '. Find the average rate of change of the population per year.', mc: mcV(f1(r), r, [[f1(r * dt), r * dt], [f1(-r), -r], [f1(K.round(p2 / dt, 1)), K.round(p2 / dt, 1)]], function () { var z = r + rnz(-9, 9); return [f1(z), z]; }), why: ['Average rate of change = ' + m(K.frx('change in population', 'change in years')) + '.', m(K.frx(K.comma(p2) + ' ' + M + ' ' + K.comma(p1), (y1 + dt) + ' ' + M + ' ' + y1) + ' = ' + K.frx(n(r * dt), String(dt)) + ' = ' + n(r)) + '.', 'The population ' + (r > 0 ? 'grew' : 'fell') + ' by an average of ' + Math.abs(r) + ' residents per year.'] }), { kind: 'roc', p1: p1, p2: p2, t1: y1, t2: y1 + dt });
      },
      function () { // which function is graphed
        var mm = pick(SL), b = rnz(-4, 4), x2 = mm.d * (Math.abs(mm.n) > 2 ? 1 : pick([1, 2])), y2 = mm.mul(x2).add(b).val();
        if (Math.abs(y2) > 6) x2 = -x2, y2 = mm.mul(x2).add(b).val();
        var g = K.plane({ x: [-7, 7], y: [-7, 7], lines: [{ m: mm, b: b }], pts: [{ x: 0, y: b }, { x: x2, y: y2 }] });
        var ch = function (s1, b1) { return fx('f', lin(s1, b1)); };
        return attach(Q({ q: 'Which linear function is graphed? (Two points on the line are marked.)', graph: g, mc: mc(ch(mm, b), [ch(mm.neg(), b), ch(R(mm.d, mm.n), b), ch(mm, -b)], function () { return ch(mm, b + rnz(-2, 2)); }), why: ['The line crosses the ' + Y + '-axis at ' + K.pt(0, b) + ', so ' + m(I('b') + ' = ' + n(b)) + '.', 'From ' + K.pt(0, b) + ' to ' + K.pt(x2, y2) + ': rise ' + n(y2 - b) + ', run ' + n(x2) + ', so ' + m(I('m') + ' = ' + eqs(frq(y2 - b, x2), mm.html())) + '.', 'So ' + ch(mm, b) + '.'] }), { kind: 'lineFromGraph', m: [mm.n, mm.d], b: b });
      },
      function () { // both intercepts, fraction possible
        var a = pick([2, 3, 4, 5, -2, -3, -4, -5]), b; do { b = rnz(-9, 9); } while (b % a === 0);
        var r = R(-b, a);
        var ch = function (px, qy) { return icH(px, qy); };
        return attach(Q({ q: 'Find the ' + X + '- and ' + Y + '-intercepts of the graph of ' + fx('f', lin(a, b)) + '.', mc: mc(ch(r, b), [ch(r.neg(), b), ch(R(-a, b), b), ch(r, a)]), why: [Y + '-intercept: ' + m(I('f') + '(0) = ' + n(b)) + ', so ' + K.pt(0, b) + '.', X + '-intercept: ' + m(lin(a, b) + ' = 0') + ' gives ' + m(P([[a, X]]) + ' = ' + n(-b)) + ', so ' + m(I('x') + ' = ' + r.html()) + '.', 'Intercepts: ' + K.pt(r, 0) + ' and ' + K.pt(0, b) + '.'] }), { kind: 'icptF', fq: true });
      }
    ],
    [
      function () { // data plan: rate and fixed fee
        var r = pick([3, 4, 5, 6, 8, 10]), f = pick([15, 20, 25, 30, 35, 40]), g1 = ri(1, 4), g2 = g1 + ri(2, 5), c1 = f + r * g1, c2 = f + r * g2;
        var ch = function (rr, ff) { return K.money(rr).replace('.00', '') + ' per GB; fixed fee ' + K.money(ff).replace('.00', ''); };
        return attach(Q({ q: 'A phone plan’s monthly cost is a linear function of the data used. Using ' + g1 + ' GB costs ' + K.money(c1).replace('.00', '') + ', and using ' + g2 + ' GB costs ' + K.money(c2).replace('.00', '') + '. Find the rate of change (cost per GB) and the fixed monthly fee.', mc: mc(ch(r, f), [ch(c2 - c1, f), ch(r, c1), ch(f, r)]), why: ['Rate of change (slope): ' + m(K.frx(c2 + ' ' + M + ' ' + c1, g2 + ' ' + M + ' ' + g1) + ' = ' + K.frx(String(c2 - c1), String(g2 - g1)) + ' = ' + r) + ' dollars per GB.', 'Fixed fee (the value at 0 GB): ' + m(c1 + ' ' + M + ' ' + r + '(' + g1 + ') = ' + f) + ' dollars.', 'So ' + m(I('C') + '(' + I('x') + ') = ' + r + I('x') + ' + ' + f) + ': each extra GB adds ' + K.money(r).replace('.00', '') + '.'] }), { kind: 'plan', g1: g1, g2: g2, c1: c1, c2: c2 });
      },
      function () { // find k for a given slope
        var mm = pick(SL), x2 = ri(-6, 6), y2 = ri(-6, 6), run = mm.d * pick([1, 2, -1, -2]), k = x2 - run, y1 = y2 - mm.mul(run).val();
        var w1 = x2 + run, w2 = R(x2).sub(mm.mul(y2 - y1)), w3 = R(run);
        return attach(Q({ q: 'Find ' + I('k') + ' so that the line through ' + '(' + I('k') + ', ' + n(y1) + ')' + ' and ' + K.pt(x2, y2) + ' has slope ' + m(mm.html()) + '.', mc: mcV(n(k), k, [[n(w1), w1], [w2.html(), w2.val()], [w3.html(), w3.val()]], nx(k)), why: ['Slope formula: ' + m(K.frx(n(y2) + ' ' + M + ' ' + sb(y1), n(x2) + ' ' + M + ' ' + I('k')) + ' = ' + mm.html()) + ', so ' + m(K.frx(n(y2 - y1), n(x2) + ' ' + M + ' ' + I('k')) + ' = ' + mm.html()) + '.', 'Solve for the denominator: ' + m(n(x2) + ' ' + M + ' ' + I('k') + ' = ' + n(y2 - y1) + ' ÷ ' + sb(mm) + ' = ' + n(run)) + '.', 'So ' + m(I('k') + ' = ' + n(x2) + ' ' + M + ' ' + sb(run) + ' = ' + n(k)) + '.'] }), { kind: 'findkSlope', y1: y1, x2: x2, y2: y2, m: [mm.n, mm.d] });
      },
      function () { // linear function from a table
        var mm = pick(SL), s = mm.d, x0 = mm.d * ri(-2, 1), b = ri(-6, 6), xs = [0, 1, 2, 3].map(function (i) { return x0 + i * s; }), ys = xs.map(function (x) { return mm.mul(x).add(b).val(); });
        var ch = function (s1, b1) { return fx('f', lin(s1, b1)); };
        return attach(Q({ q: 'The table shows values of a linear function ' + I('f') + '. Find ' + m(I('f') + '(' + I('x') + ')') + '.<div class="center">' + K.xyTable(xs, ys, X, m(I('f') + '(' + I('x') + ')')) + '</div>', mc: mc(ch(mm, b), [ch(R(mm.d, mm.n), b), ch(mm, ys[0]), ch(mm.mul(s), b)], function () { return ch(mm, b + rnz(-3, 3)); }), why: ['Each time ' + X + ' increases by ' + s + ', ' + I('f') + ' changes by ' + n(ys[1] - ys[0]) + ', so ' + m(I('m') + ' = ' + eqs(frq(ys[1] - ys[0], s), mm.html())) + '.', 'Use ' + K.pt(xs[0], ys[0]) + ': ' + m(n(ys[0]) + ' = ' + K.lin([[mm, n(xs[0])]]) + ' + ' + I('b')) + ', so ' + m(I('b') + ' = ' + n(b)) + '.', 'So ' + ch(mm, b) + '.'] }), { kind: 'table', xs: xs, ys: ys });
      },
      function () { // depreciation
        var V, d, t, Xv; do { V = ri(18, 40) * 1000; d = ri(15, 40) * 100; t = ri(3, 8); Xv = V - d * t; } while (Xv < 2000);
        var ch = function (v) { return 'After ' + cnt(K.round(v, 1), 'year'); };
        return attach(Q({ q: 'A car worth ' + K.money(V).replace('.00', '') + ' loses ' + K.money(d).replace('.00', '') + ' in value each year, so its value after ' + I('t') + ' years is ' + m(I('V') + '(' + I('t') + ') = ' + K.comma(V) + ' ' + M + ' ' + K.comma(d) + I('t')) + '. When will the car be worth ' + K.money(Xv).replace('.00', '') + '?', mc: mcV(ch(t), t, [[ch(K.round(Xv / d, 1)), K.round(Xv / d, 1)], [ch(K.round((V + Xv) / d, 1)), K.round((V + Xv) / d, 1)], [ch(t + 1), t + 1]], function () { var z = t + rnz(-2, 3); return [ch(z), z]; }), why: ['Set ' + m(I('V') + '(' + I('t') + ') = ' + K.comma(Xv)) + ': ' + m(K.comma(V) + ' ' + M + ' ' + K.comma(d) + I('t') + ' = ' + K.comma(Xv)) + '.', 'Subtract ' + K.comma(V) + ': ' + m(M + K.comma(d) + I('t') + ' = ' + M + K.comma(V - Xv)) + '.', 'Divide: ' + m(I('t') + ' = ' + t) + '. The car is worth ' + K.money(Xv).replace('.00', '') + ' after ' + t + ' years.'] }), { kind: 'deprec', V: V, d: d, X: Xv });
      }
    ]
  ];
  K.lesson('2.4', { title: 'Linear Functions', std: 'Lial 12e · Section 2.4', levels: c24 });

  /* ================= 2.5 Equations of Lines and Linear Models ================= */
  function le(mm, b) { return m(K.lineEq(R(mm), R(b))); }
  function thru(mm, px, py) { mm = R(mm); return R(py).sub(mm.mul(px)); } // intercept of slope mm through (px, py)
  function psF(mm, x1, y1) { mm = R(mm); return m(K.minusH(I('y'), y1) + ' = ' + (R(x1).n === 0 ? K.coef(mm, true) + I('x') : (mm.d === 1 ? K.coef(mm, true) : '(' + mm.html() + ')') + '(' + K.minusH(I('x'), x1) + ')')); }
  var SLn1 = SL.filter(function (s) { return Math.abs(s.n) !== s.d; });
  var c25 = [
    [
      function () { // point-slope -> slope-intercept
        var x1 = rnz(-6, 6), y1 = ri(-6, 6), mm = rnz(-5, 5), b = y1 - mm * x1;
        return attach(Q({ q: 'Write the equation of the line through ' + K.pt(x1, y1) + ' with slope ' + n(mm) + ' in slope-intercept form.', mc: mc(le(mm, b), [le(mm, y1), le(mm, -mm * x1 - y1), le(mm, y1 - x1)], function () { return le(mm, b + rnz(-3, 3)); }), why: ['Point-slope form: ' + psF(mm, x1, y1) + '.', 'Distribute: ' + m(K.minusH(I('y'), y1) + ' = ' + lin(mm, -mm * x1)) + '.', (y1 ? (y1 > 0 ? 'Add ' + y1 + ' to' : 'Subtract ' + (-y1) + ' from') + ' both sides: ' : 'So ') + le(mm, b) + '.'] }), { kind: 'lineThru', pts: [[x1, y1]], m: [mm, 1] });
      },
      function () { // parallel / perpendicular slope
        var mm = pick(SLn1), b = ri(-5, 5), perp = K.coin(), ans = perp ? R(-mm.d, mm.n) : mm;
        var all = [mm, mm.neg(), R(mm.d, mm.n), R(-mm.d, mm.n)].map(function (z) { return m(z.html()); });
        return attach(Q({ q: 'What is the slope of a line <b>' + (perp ? 'perpendicular' : 'parallel') + '</b> to ' + le(mm, b) + '?', mc: mc(m(ans.html()), all.filter(function (z) { return z !== m(ans.html()); })), why: ['The given line has slope ' + m(mm.html()) + '.', perp ? 'Perpendicular slopes are negative reciprocals: flip the fraction and change the sign.' : 'Parallel lines have equal slopes.', perp ? 'So the slope is ' + m(ans.html()) + '. Check: ' + m(mm.html() + ' · ' + sb(ans) + ' = ' + M + '1') + '.' : 'So the slope is ' + m(ans.html()) + '.'] }), { kind: 'ppSlope', m: [mm.n, mm.d], perp: perp });
      },
      function () { // vertical / horizontal line through a point
        var a = rnz(-8, 8), b; do { b = rnz(-8, 8); } while (b === a || b === -a);
        var vert = K.coin(), right = m(I(vert ? 'x' : 'y') + ' = ' + n(vert ? a : b));
        var all = [m(I('x') + ' = ' + n(a)), m(I('y') + ' = ' + n(b)), m(I('x') + ' = ' + n(b)), m(I('y') + ' = ' + n(a))];
        return attach(Q({ q: 'Write the equation of the <b>' + (vert ? 'vertical' : 'horizontal') + '</b> line through ' + K.pt(a, b) + '.', mc: mc(right, all.filter(function (z) { return z !== right; })), why: [vert ? 'On a vertical line every point has the same ' + X + '-coordinate.' : 'On a horizontal line every point has the same ' + Y + '-coordinate.', 'The point ' + K.pt(a, b) + ' has ' + (vert ? X + '-coordinate ' + n(a) : Y + '-coordinate ' + n(b)) + '.', 'So the line is ' + right + '.'] }), { kind: 'hvLine', a: a, b: b, vert: vert });
      }
    ],
    [
      function () { // through two points
        var mm = pick(SL), x1 = ri(-5, 5), y1 = ri(-5, 5), run = mm.d * pick([1, 2, -1, -2]), x2 = x1 + run, y2 = mm.mul(run).add(y1).val(), b = thru(mm, x1, y1);
        var inv = R(mm.d, mm.n);
        return attach(Q({ q: 'Write the equation of the line through ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + ' in slope-intercept form.', mc: mc(le(mm, b), [le(inv, thru(inv, x1, y1)), le(mm, b.neg()), le(mm.neg(), thru(mm.neg(), x1, y1))], function () { return le(mm, b.add(rnz(-3, 3))); }), why: ['Slope: ' + m(I('m') + ' = ' + K.frx(n(y2) + ' ' + M + ' ' + sb(y1), n(x2) + ' ' + M + ' ' + sb(x1)) + ' = ' + eqs(frq(y2 - y1, run), mm.html())) + '.', 'Point-slope with ' + K.pt(x1, y1) + ': ' + psF(mm, x1, y1) + '.', 'Solve for ' + Y + ': ' + le(mm, b) + '. Check ' + K.pt(x2, y2) + ': ' + m(K.lin([[mm, n(x2)]]) + K.plusK(b) + ' = ' + n(y2)) + ' ✔'] }), { kind: 'lineThru', pts: [[x1, y1], [x2, y2]] });
      },
      function () { // parallel to a standard-form line
        var A = rnz(-5, 5), B = rnz(-5, 5), Cc = ri(-10, 10), px, py; do { px = ri(-5, 5); py = ri(-5, 5); } while (A * px + B * py === Cc);
        var mm = R(-A, B), pp = R(B, A), b = thru(mm, px, py);
        return attach(Q({ q: 'Write the equation, in slope-intercept form, of the line through ' + K.pt(px, py) + ' that is <b>parallel</b> to ' + m(P([[A, X], [B, Y]]) + ' = ' + n(Cc)) + '.', mc: mc(le(mm, b), [le(pp, thru(pp, px, py)), le(mm.neg(), thru(mm.neg(), px, py)), le(mm, R(Cc, B))], function () { return le(mm, b.add(rnz(-3, 3))); }), why: ['Solve the given equation for ' + Y + ': ' + le(mm, R(Cc, B)) + ', so its slope is ' + m(mm.html()) + '.', 'A parallel line has the same slope: ' + psF(mm, px, py) + '.', 'Solve for ' + Y + ': ' + le(mm, b) + '.'] }), { kind: 'parPerp', A: A, B: B, C: Cc, px: px, py: py, perp: false });
      },
      function () { // perpendicular to y = mx + b
        var mm = pick(SL), b0 = ri(-5, 5), pp = R(-mm.d, mm.n), px = pp.d * ri(-2, 2), py = ri(-5, 5), b = thru(pp, px, py);
        if (b.eq(b0)) py += 1, b = thru(pp, px, py);
        return attach(Q({ q: 'Write the equation, in slope-intercept form, of the line through ' + K.pt(px, py) + ' that is <b>perpendicular</b> to ' + le(mm, b0) + '.', mc: mc(le(pp, b), [le(mm, thru(mm, px, py)), le(pp.neg(), thru(pp.neg(), px, py)), le(pp, b0)], function () { return le(pp, b.add(rnz(-3, 3))); }), why: ['The given slope is ' + m(mm.html()) + ', so the perpendicular slope is its negative reciprocal, ' + m(pp.html()) + '.', 'Point-slope form: ' + psF(pp, px, py) + '.', 'Solve for ' + Y + ': ' + le(pp, b) + '.'] }), { kind: 'parPerp', A: mm.n, B: -mm.d, C: -b0 * mm.d, px: px, py: py, perp: true });
      },
      function () { // standard form
        var q = pick([2, 3, 4, 5]), p, r = rnz(-6, 6); do { p = rnz(-7, 7); } while (K.gcd(p, q) !== 1);
        var s = p > 0 ? -1 : 1, A = -p * s, B = q * s, Cc = q * r * s;
        var ch = function (a, b, c) { return m(P([[a, X], [b, Y]]) + ' = ' + n(c)); };
        return attach(Q({ q: 'Write ' + m(I('y') + ' = ' + lin(R(p, q), r)) + ' in standard form ' + m(I('A') + I('x') + ' + ' + I('B') + I('y') + ' = ' + I('C')) + ', with integers ' + I('A') + ', ' + I('B') + ', ' + I('C') + ' and ' + m(I('A') + ' &gt; 0') + '.', mc: mc(ch(A, B, Cc), [ch(A, B, -Cc), ch(A, B, r * s), ch(A, -B, Cc)]), why: ['Multiply every term by ' + q + ' to clear the fraction: ' + m(q + I('y') + ' = ' + lin(p, q * r)) + '.', 'Move the ' + X + '-term to the left: ' + m(P([[-p, X], [q, Y]]) + ' = ' + n(q * r)) + '.', s < 0 ? 'Multiply by ' + M + '1 so ' + I('A') + ' is positive: ' + ch(A, B, Cc) + '.' : 'The ' + X + '-coefficient is already positive: ' + ch(A, B, Cc) + '.'] }), { kind: 'stdForm', p: p, q: q, r: r });
      }
    ],
    [
      function () { // perpendicular through P, line read from the graph
        var mm = pick(SL), b = ri(-3, 3), pp = R(-mm.d, mm.n), px, py, tries = 0;
        do { px = pp.d * ri(-3, 3); py = ri(-5, 5); tries++; } while ((mm.mul(px).add(b).eq(py) || Math.abs(px) > 6) && tries < 50);
        var xs = []; for (var x = -6; x <= 6; x++) { var yv = mm.mul(x).add(b); if (yv.isInt() && Math.abs(yv.val()) <= 6) xs.push(x); }
        var xa = xs[0], xb = xs[1];
        var g = K.plane(place({ x: [-7, 7], y: [-7, 7], lines: [{ m: mm, b: b }], pts: [{ x: xa, y: mm.mul(xa).add(b).val() }, { x: xb, y: mm.mul(xb).add(b).val() }, { x: px, y: py, color: C.red, label: 'P' }] }));
        var bb = thru(pp, px, py);
        return attach(Q({ q: 'Point ' + I('P') + K.pt(px, py) + ' is shown in red. Write the equation, in slope-intercept form, of the line through ' + I('P') + ' that is perpendicular to the blue line.', graph: g, mc: mc(le(pp, bb), [le(mm, thru(mm, px, py)), le(pp.neg(), thru(pp.neg(), px, py)), le(pp, b)], function () { return le(pp, bb.add(rnz(-3, 3))); }), why: ['Blue line: from ' + K.pt(xa, mm.mul(xa).add(b)) + ' to ' + K.pt(xb, mm.mul(xb).add(b)) + ' the slope is ' + m(mm.html()) + '.', 'Perpendicular slope: ' + m(pp.html()) + '. Point-slope: ' + psF(pp, px, py) + '.', 'Solve for ' + Y + ': ' + le(pp, bb) + '.'] }), { kind: 'parPerp', A: mm.n, B: -mm.d, C: -b * mm.d, px: px, py: py, perp: true });
      },
      function () { // linear model prediction
        var t1 = ri(2010, 2016), v1 = ri(20, 60) * 10, rate = pick([12, 15, 18, 25, 30, -8, -12]), t2 = t1 + pick([4, 5, 6]), v2 = v1 + rate * (t2 - t1), t3 = t2 + ri(3, 8), v3 = v1 + rate * (t3 - t1);
        var u = function (v) { return n(v) + ' members'; };
        return attach(Q({ q: 'A hiking club had ' + v1 + ' members in ' + t1 + ' and ' + v2 + ' members in ' + t2 + '. Assume membership changes linearly. Write a linear model and use it to predict the membership in ' + t3 + '.', mc: mcV(u(v3), v3, [[u(v2 + (v2 - v1)), 2 * v2 - v1], [u(v1 + rate * (t3 - t2)), v1 + rate * (t3 - t2)], [u(v2 + rate * (t3 - t1)), v2 + rate * (t3 - t1)]], function () { var z = v3 + rnz(-3, 3) * Math.abs(rate); return [u(z), z]; }), why: ['Rate of change: ' + m(K.frx(v2 + ' ' + M + ' ' + v1, t2 + ' ' + M + ' ' + t1) + ' = ' + n(rate)) + ' members per year.', 'Let ' + I('x') + ' = years after ' + t1 + ': ' + m(I('y') + ' = ' + lin(rate, v1)) + '.', t3 + ' is ' + m(I('x') + ' = ' + (t3 - t1)) + ': ' + m(I('y') + ' = ' + n(rate) + '(' + (t3 - t1) + ') + ' + v1 + ' = ' + n(v3)) + '.'] }), { kind: 'model', t1: t1, v1: v1, t2: t2, v2: v2, t3: t3 });
      },
      function () { // find k: parallel or perpendicular
        var b = ri(1, 4), d = ri(1, 4), s = pick([1, -1]), a = b * d * s, perp = K.coin(), c1 = rnz(-9, 9), e = rnz(-9, 9);
        var kPar = -a * b / d, kPerp = a * d / b, k = perp ? kPerp : kPar, sk = a > 0 ? M + K.frx(I('k'), n(a)) : K.frx(I('k'), n(-a));
        return attach(Q({ q: 'Find ' + I('k') + ' so that the line ' + m(P([[1, I('k') + I('x')], [a, Y]]) + ' = ' + n(c1)) + ' is <b>' + (perp ? 'perpendicular' : 'parallel') + '</b> to the line ' + m(P([[b, X], [-d, Y]]) + ' = ' + n(e)) + '.', mc: mcV(n(k), k, [[n(perp ? kPar : kPerp), perp ? kPar : kPerp], [n(-k), -k], [n(-(perp ? kPar : kPerp)), -(perp ? kPar : kPerp)]], nx(k)), why: ['Second line: ' + m(I('y') + ' = ' + lin(R(b, d), R(-e, d))) + ', slope ' + m(R(b, d).html()) + '.', 'First line: solving for ' + Y + ' gives slope ' + m(sk) + '.', perp ? 'Perpendicular: ' + m('(' + sk + ')(' + R(b, d).html() + ') = ' + M + '1') + ', so ' + m(I('k') + ' = ' + n(k)) + '.' : 'Parallel: ' + m(sk + ' = ' + R(b, d).html()) + ', so ' + m(I('k') + ' = ' + n(k)) + '.'] }), { kind: 'kLines', a: a, b: b, d: d, perp: perp });
      },
      function () { // perpendicular bisector
        var x1 = ri(-6, 6), y1 = ri(-6, 6), dx = 2 * rnz(-3, 3), dy = 2 * rnz(-3, 3), x2 = x1 + dx, y2 = y1 + dy, mx = x1 + dx / 2, my = y1 + dy / 2;
        var mAB = R(dy, dx), pp = R(-dx, dy), b = thru(pp, mx, my);
        return attach(Q({ q: 'Find the equation, in slope-intercept form, of the perpendicular bisector of the segment with endpoints ' + K.pt(x1, y1) + ' and ' + K.pt(x2, y2) + '.', mc: mc(le(pp, b), [le(mAB, thru(mAB, mx, my)), le(pp, thru(pp, x1, y1)), le(pp.neg(), thru(pp.neg(), mx, my))], function () { return le(pp, b.add(rnz(-3, 3))); }), why: ['The bisector passes through the midpoint ' + K.pt(mx, my) + '.', 'Slope of the segment: ' + m(eqs(frq(dy, dx), mAB.html())) + ', so the perpendicular slope is ' + m(pp.html()) + '.', psF(pp, mx, my) + ' simplifies to ' + le(pp, b) + '.'] }), { kind: 'perpBis', x1: x1, y1: y1, x2: x2, y2: y2 });
      }
    ]
  ];
  K.lesson('2.5', { title: 'Equations of Lines and Linear Models', std: 'Lial 12e · Section 2.5', levels: c25 });

  /* ================= 2.6 Graphs of Basic Functions ================= */
  var PAR = {
    id: { f: function (x) { return x; }, h: function (u) { return u; }, D: ALL, R: ALL, nm: 'identity' },
    sq: { f: function (x) { return x * x; }, h: function (u) { return u === X ? K.xp(2) : '(' + u + ')<sup>2</sup>'; }, D: ALL, R: iv(0, Infinity, true), nm: 'squaring' },
    cu: { f: function (x) { return x * x * x; }, h: function (u) { return u === X ? K.xp(3) : '(' + u + ')<sup>3</sup>'; }, D: ALL, R: ALL, nm: 'cubing' },
    sr: { f: function (x) { return x < 0 ? NaN : Math.sqrt(x); }, h: function (u) { return K.sqrt(u); }, D: iv(0, Infinity, true), R: iv(0, Infinity, true), nm: 'square root' },
    cr: { f: function (x) { return Math.cbrt(x); }, h: function (u) { return K.cbrt(u); }, D: ALL, R: ALL, nm: 'cube root' },
    ab: { f: function (x) { return Math.abs(x); }, h: function (u) { return '|' + u + '|'; }, D: ALL, R: iv(0, Infinity, true), nm: 'absolute value' }
  };
  function gi(v) { return Math.floor(v + 1e-9); }
  function pwFn(rows) { return pw(I('f') + '(' + I('x') + ')', rows); }
  function dotsAt(c, yIn, yOut, col) { return [{ x: c, y: yIn, color: col || C.blue }, { x: c, y: yOut, open: true, color: col || C.blue }]; }
  var c26 = [
    [
      function () { // domain or range of a basic function
        var key = pick(Object.keys(PAR)), pr = PAR[key], askD = K.coin(), right = askD ? pr.D : pr.R;
        var pool = [ALL, iv(0, Infinity, true), iv(0, Infinity), iv(-Infinity, 0, false, true)];
        return attach(Q({ q: 'What is the <b>' + (askD ? 'domain' : 'range') + '</b> of the ' + pr.nm + ' function ' + fx('f', pr.h(X)) + '?', mc: mc(m(right), pool.filter(function (z) { return z !== right; }).map(m)), why: [key === 'sr' ? 'You can take the square root only of 0 or a positive number, and the result is never negative.' : key === 'sq' || key === 'ab' ? 'Any real number can be input, but the output is never negative and equals 0 at ' + m(I('x') + ' = 0') + '.' : 'Any real number can be input, and every real number comes out as an output.', 'Domain ' + m(pr.D) + '; range ' + m(pr.R) + '.', 'So the ' + (askD ? 'domain' : 'range') + ' is ' + m(right) + '.'] }), { kind: 'parDR', key: key, askD: askD });
      },
      function () { // evaluate a piecewise function
        var c = ri(-3, 3), incl = K.coin(), a1 = rnz(-4, 4), b1 = ri(-5, 5), b2 = ri(-5, 5), lq = K.coin();
        var opL = incl ? '<=' : '<', opR = incl ? '>' : '>=';
        var f1 = function (x) { return a1 * x + b1; }, f2 = lq ? function (x) { return x * x + b2; } : function (x) { return -x + b2; };
        var e2 = lq ? P([[1, K.xp(2)], [b2, '']]) : lin(-1, b2), v = pick([c, c, c - ri(1, 3), c + ri(1, 3)]), useL = test(opL, v, c), val = useL ? f1(v) : f2(v), oth = useL ? f2(v) : f1(v);
        return attach(Q({ q: 'Let ' + pwFn([[lin(a1, b1), cond(opL, c)], [e2, cond(opR, c)]]) + '. Find ' + m(I('f') + '(' + n(v) + ')') + '.', mc: mcV(n(val), val, [[n(oth), oth], [n(val + oth), val + oth], [n(-val), -val]], nx(val)), why: ['Decide which piece ' + m(I('x') + ' = ' + n(v)) + ' belongs to: ' + m(n(v) + ' ' + LE[useL ? opL : opR] + ' ' + n(c)) + ' is true, so use the ' + (useL ? 'first' : 'second') + ' piece.', m(I('f') + '(' + n(v) + ') = ' + eqs(useL ? K.lin([[a1, n(v)]]) + K.plusK(b1) : lq ? sb(v) + '<sup>2</sup>' + K.plusK(b2) : (v === 0 ? '0' : M + sb(v)) + K.plusK(b2), n(val))) + '.', 'Never evaluate both pieces and choose: the ' + X + '-value picks exactly one piece.'] }), { kind: 'pwEval', fq: true, x: v });
      },
      function () { // greatest integer
        var ip = ri(-6, 6), fr0 = pick([0, 0.2, 0.3, 0.5, 0.7, 0.8, 0.25, 0.75, 0.9]); if (ip >= 0 && fr0 > 0 && K.coin()) ip = -ip - 1;
        var v = K.round(ip + fr0, 4), ans = gi(v), tr = v < 0 ? -Math.floor(-v + 1e-9) : gi(v), rd = Math.round(v), ce = Math.ceil(v - 1e-9);
        return attach(Q({ q: 'Evaluate ' + m('⟦' + n(v) + '⟧') + ', where ' + m('⟦' + I('x') + '⟧') + ' is the greatest integer function.', mc: mcV(n(ans), ans, [[n(tr), tr], [n(rd), rd], [n(ce), ce]], function (i) { var z = ans + rnz(-2, 2); return [n(z), z]; }), why: [m('⟦' + I('x') + '⟧') + ' is the greatest integer that is less than or equal to ' + X + '.', fr0 === 0 ? n(v) + ' is already an integer, so it is its own value.' : 'On a number line, the integers around ' + n(v) + ' are ' + n(ans) + ' and ' + n(ans + 1) + '. Round <b>down</b>' + (v < 0 ? ', which moves away from 0 for a negative number' : '') + '.', m('⟦' + n(v) + '⟧ = ' + n(ans)) + '.'] }), { kind: 'gint', v: v });
      },
      function () { // identify a basic graph
        var keys = Object.keys(PAR), key = pick(keys), pr = PAR[key];
        var g = K.plane({ x: [-5, 5], y: [-5, 5], fns: [{ f: pr.f, from: key === 'sr' ? 0 : -5 }], pts: [{ x: 0, y: 0, r: 3 }] });
        desc('graph of the ' + pr.nm + ' function');
        var wr = K.sample(keys.filter(function (z) { return z !== key; }), 3).map(function (z) { return fx('f', PAR[z].h(X)); });
        return attach(Q({ q: 'Which basic function is graphed?', graph: g, mc: mc(fx('f', pr.h(X)), wr), why: [key === 'cu' ? 'The curve passes through ' + K.pt(0, 0) + ' and ' + K.pt(1, 1) + ' but is not a line: it is flat at the origin, then shoots up steeply (at ' + m(I('x') + ' = 2') + ' it would already be at ' + m(I('y') + ' = 8') + ', off the top of the grid). It is symmetric about the origin.' : key === 'cr' ? 'The curve passes through ' + K.pt(0, 0) + ' and ' + K.pt(1, 1) + ' but is not a line: it is vertical at the origin, then levels off (it reaches only ' + m(I('y') + ' = 2') + ' at ' + m(I('x') + ' = 8') + '). Unlike the square root, it continues to the left of the origin.' : 'Check key points: ' + ({ id: [-3, 0, 3], sq: [-2, 0, 2], sr: [0, 1, 4], ab: [-3, 0, 3] })[key].map(function (x) { return K.pt(x, K.round(pr.f(x), 4)); }).join(', ') + ' lie on this graph' + (key === 'sr' ? ', and nothing is drawn for ' + m(I('x') + ' &lt; 0') : '') + '.', (key === 'cu' || key === 'cr' ? 'That shape matches' : 'Those points match') + ' the ' + pr.nm + ' function ' + fx('f', pr.h(X)) + '.', 'Shape guide: ' + ({ id: 'a straight line through the origin', sq: 'a U-shaped parabola', cu: 'an S-shape through the origin, steep at the ends', sr: 'a half-curve that starts at the origin and goes right', cr: 'an S-shape on its side, flat at the ends', ab: 'a V-shape with vertex at the origin' })[key] + '.'] }), { kind: 'parId', key: key });
      }
    ],
    [
      function () { // read a piecewise graph
        var c = ri(-3, 3), yL = ri(-4, 4), yR, m1 = pick([-2, -1, 0, 1, 2]), m2 = pick([-2, -1, 0, 1, 2]), closedL = K.coin();
        do { yR = ri(-4, 4); } while (yR === yL);
        var fL = function (x) { return yL + m1 * (x - c); }, fR = function (x) { return yR + m2 * (x - c); };
        var g = K.plane({ x: [-8, 8], y: [-8, 8], segs: [{ x1: -9, y1: fL(-9), x2: c, y2: yL }, { x1: c, y1: yR, x2: 9, y2: fR(9) }], pts: closedL ? dotsAt(c, yL, yR) : dotsAt(c, yR, yL) });
        desc('two rays meeting x = ' + n(c) + ': closed dot (' + n(c) + ', ' + n(closedL ? yL : yR) + '), open dot (' + n(c) + ', ' + n(closedL ? yR : yL) + ')');
        var bnd = K.coin() || K.coin(), v = bnd ? c : c + pick([-2, 2]); if (!bnd && Math.abs(v < c ? fL(v) : fR(v)) > 6) { bnd = true; v = c; } var val = bnd ? (closedL ? yL : yR) : (v < c ? fL(v) : fR(v)), oth = bnd ? (closedL ? yR : yL) : (v < c ? fR(v) : fL(v));
        return attach(Q({ q: 'The graph of a piecewise function ' + I('f') + ' is shown. (A closed dot is on the graph; an open dot is not.) Find ' + m(I('f') + '(' + n(v) + ')') + '.', graph: g, mc: mc(n(val), [n(oth), 'Undefined', n(v)].filter(function (z) { return z !== n(val); }), function () { return n(val + rnz(-3, 3)); }), why: bnd ? ['At ' + m(I('x') + ' = ' + n(c)) + ' there is a closed dot at ' + K.pt(c, val) + ' and an open dot at ' + K.pt(c, oth) + '.', 'Only the closed dot is a point of the graph.', 'So ' + m(I('f') + '(' + n(c) + ') = ' + n(val)) + '.'] : ['Go to ' + m(I('x') + ' = ' + n(v)) + ', which is on the ' + (v < c ? 'left' : 'right') + ' piece.', 'Read the height of that piece: the point ' + K.pt(v, val) + '.', 'So ' + m(I('f') + '(' + n(v) + ') = ' + n(val)) + '.'] }), { kind: 'pwGraphRead', c: c, yL: yL, yR: yR, m1: m1, m2: m2, closedL: closedL, x: v });
      },
      function () { // describe endpoints from the formula
        var c = ri(-3, 3), a1 = rnz(-3, 3), a2 = rnz(-3, 3), b1 = ri(-5, 5), b2, closedL = K.coin();
        do { b2 = ri(-5, 5); } while (a1 * c + b1 === a2 * c + b2);
        var A = a1 * c + b1, B = a2 * c + b2, opL = closedL ? '<=' : '<', opR = closedL ? '>' : '>=';
        var d = function (cA, cB) { return (cA ? 'Closed' : 'Open') + ' dot at ' + K.pt(c, A) + '; ' + (cB ? 'closed' : 'open') + ' dot at ' + K.pt(c, B); };
        return attach(Q({ q: 'When ' + pwFn([[lin(a1, b1), cond(opL, c)], [lin(a2, b2), cond(opR, c)]]) + ' is graphed, what appears at ' + m(I('x') + ' = ' + n(c)) + '?', mc: mc(d(closedL, !closedL), [d(!closedL, closedL), d(true, true), d(false, false)]), why: ['First piece at ' + m(I('x') + ' = ' + n(c)) + ': ' + m(K.lin([[a1, n(c)]]) + K.plusK(b1) + ' = ' + n(A)) + '. Its condition uses ' + m(LE[opL]) + ', so the dot is ' + (closedL ? 'closed' : 'open') + '.', 'Second piece at ' + m(I('x') + ' = ' + n(c)) + ': ' + m(K.lin([[a2, n(c)]]) + K.plusK(b2) + ' = ' + n(B)) + '. Its condition uses ' + m(LE[opR]) + ', so the dot is ' + (closedL ? 'open' : 'closed') + '.', 'Exactly one dot is closed, because each ' + X + '-value has one output.'] }), { kind: 'pwDots', fq: true, c: c });
      },
      function () { // three pieces, sum of two values
        var c1 = ri(-3, -1), c2 = ri(1, 3), a1 = rnz(-3, 3), b1 = ri(-4, 4), b2 = ri(-4, 4), a3 = rnz(-3, 3), b3 = ri(-4, 4);
        var F = [function (x) { return a1 * x + b1; }, function (x) { return x * x + b2; }, function (x) { return a3 * x + b3; }];
        var u = pick([c1, c1 - ri(1, 2)]), w = pick([c2, c2 + ri(1, 2)]);
        var pu = u < c1 ? 0 : 1, pwv = w <= c2 ? 1 : 2, val = F[pu](u) + F[pwv](w);
        var alt1 = F[u < c1 ? 1 : 0](u) + F[pwv](w), alt2 = F[pu](u) + F[w <= c2 ? 2 : 1](w), alt3 = F[pu](u) * F[pwv](w);
        return attach(Q({ q: 'Let ' + pwFn([[lin(a1, b1), cond('<', c1)], [P([[1, K.xp(2)], [b2, '']]), m(n(c1) + ' ≤ ' + I('x') + ' ≤ ' + n(c2))], [lin(a3, b3), cond('>', c2)]]) + '. Find ' + m(I('f') + '(' + n(u) + ') + ' + I('f') + '(' + n(w) + ')') + '.', mc: mcV(n(val), val, [[n(alt1), alt1], [n(alt2), alt2], [n(alt3), alt3]], nx(val)), why: [m(I('x') + ' = ' + n(u)) + ' satisfies ' + (pu === 0 ? m(I('x') + ' &lt; ' + n(c1)) : m(n(c1) + ' ≤ ' + I('x') + ' ≤ ' + n(c2))) + ', so ' + m(I('f') + '(' + n(u) + ') = ' + n(F[pu](u))) + '.', m(I('x') + ' = ' + n(w)) + ' satisfies ' + (pwv === 2 ? m(I('x') + ' &gt; ' + n(c2)) : m(n(c1) + ' ≤ ' + I('x') + ' ≤ ' + n(c2))) + ', so ' + m(I('f') + '(' + n(w) + ') = ' + n(F[pwv](w))) + '.', 'Sum: ' + m(n(F[pu](u)) + ' + ' + sb(F[pwv](w)) + ' = ' + n(val)) + '.'] }), { kind: 'pwSum', fq: true, u: u, w: w });
      }
    ],
    [
      function () { // parking step function
        var p = pick([4, 5, 6, 8]), q = pick([2, 3, 4]), h = ri(1, 6), mn = pick([5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55]), cost = p + q * h;
        var mon = function (v) { return K.money(v).replace('.00', ''); };
        return attach(Q({ q: 'A parking garage charges ' + mon(p) + ' for the first hour (or any part of it) and ' + mon(q) + ' for each additional hour or part of an hour. How much does it cost to park for ' + h + ' hour' + (h > 1 ? 's' : '') + ' ' + mn + ' minutes?', mc: mcV(mon(cost), cost, [[mon(p + q * (h - 1)), p + q * (h - 1)], [mon(p * (h + 1)), p * (h + 1)], [mon(p + q * (h + 1)), p + q * (h + 1)]], function () { var z = cost + q * rnz(-2, 2); return [mon(z), z]; }), why: ['Any part of an hour counts as a full hour, so ' + h + ' h ' + mn + ' min is billed as ' + (h + 1) + ' hours.', 'That is the first hour plus ' + h + ' additional hour' + (h > 1 ? 's' : '') + '.', 'Cost: ' + m(p + ' + ' + q + '(' + h + ') = ' + cost) + ', so ' + mon(cost) + '.'] }), { kind: 'parking', p: p, q: q, h: h, mn: mn });
      },
      function () { // piecewise formula from the graph
        var c = ri(-2, 2), yL = ri(-4, 4), yR, m1 = pick([-2, -1, 1, 2]), m2 = pick([-2, -1, 1, 2, 0]), closedL = K.coin();
        do { yR = ri(-4, 4); } while (yR === yL);
        var b1 = yL - m1 * c, b2 = yR - m2 * c, fL = function (x) { return m1 * x + b1; }, fR = function (x) { return m2 * x + b2; };
        var g = K.plane({ x: [-8, 8], y: [-8, 8], segs: [{ x1: -9, y1: fL(-9), x2: c, y2: yL }, { x1: c, y1: yR, x2: 9, y2: fR(9) }], pts: closedL ? dotsAt(c, yL, yR) : dotsAt(c, yR, yL) });
        desc('left ray slope ' + n(m1) + ' ending at (' + n(c) + ', ' + n(yL) + ') ' + (closedL ? 'closed' : 'open') + '; right ray slope ' + n(m2) + ' starting at (' + n(c) + ', ' + n(yR) + ') ' + (closedL ? 'open' : 'closed'));
        var oL = closedL ? '<=' : '<', oR = closedL ? '>' : '>=', sw = function (o) { return { '<=': '<', '<': '<=', '>': '>=', '>=': '>' }[o]; };
        var F = function (e1, o1, e2, o2) { return pwFn([[e1, cond(o1, c)], [e2, cond(o2, c)]]); };
        return attach(Q({ q: 'Which definition matches the graph of ' + I('f') + '? (A closed dot is on the graph; an open dot is not.)', graph: g, mc: mc(F(lin(m1, b1), oL, lin(m2, b2), oR), [F(lin(m1, b1), sw(oL), lin(m2, b2), sw(oR)), F(lin(m2, b2), oL, lin(m1, b1), oR), F(lin(-m1, b1), oL, lin(m2, b2), oR)]), why: ['Left piece: through ' + K.pt(c, yL) + ' with slope ' + n(m1) + ', so ' + m(I('y') + ' = ' + lin(m1, b1)) + '. Right piece: through ' + K.pt(c, yR) + ' with slope ' + n(m2) + ', so ' + m(I('y') + ' = ' + lin(m2, b2)) + '.', 'The closed dot is on the ' + (closedL ? 'left' : 'right') + ' piece, so that piece gets ' + (closedL ? '≤' : '≥') + ' and the other gets ' + (closedL ? '&gt;' : '&lt;') + '.', 'Swapping the pieces would put the wrong formula on each side of ' + m(I('x') + ' = ' + n(c)) + '.'] }), { kind: 'pwFromGraph', c: c, m1: m1, b1: b1, m2: m2, b2: b2, closedL: closedL });
      },
      function () { // continuity: find k
        var c = rnz(-3, 3), a = rnz(-4, 4), b = ri(-5, 5), k = a * c + b - c * c;
        return attach(Q({ q: 'Find the value of ' + I('k') + ' that makes ' + pwFn([[P([[1, K.xp(2)], [1, I('k')]]), cond('<', c)], [lin(a, b), cond('>=', c)]]) + ' continuous (no break in the graph at ' + m(I('x') + ' = ' + n(c)) + ').', mc: mcV(n(k), k, [[n(a * c + b + c * c), a * c + b + c * c], [n(-k), -k], [n(a * c + b), a * c + b]], nx(k)), why: ['For no break, both pieces must give the same value at ' + m(I('x') + ' = ' + n(c)) + '.', 'Left: ' + m(sb(c) + '<sup>2</sup> + ' + I('k') + ' = ' + c * c + ' + ' + I('k')) + '. Right: ' + m(K.lin([[a, n(c)]]) + K.plusK(b) + ' = ' + n(a * c + b)) + '.', 'Set equal: ' + m(c * c + ' + ' + I('k') + ' = ' + n(a * c + b)) + ', so ' + m(I('k') + ' = ' + n(k)) + '.'] }), { kind: 'contK', c: c, a: a, b: b });
      }
    ]
  ];
  K.lesson('2.6', { title: 'Graphs of Basic Functions', std: 'Lial 12e · Section 2.6', levels: c26 });

  /* ================= 2.7 Graphing Techniques ================= */
  // y = a·parent(x − h) + k as HTML
  function tf(key, a, h, k) { a = R(a); var inner = R(h).n === 0 ? X : K.minusH(X, h); var lead = a.eq(1) ? '' : a.eq(-1) ? M : a.html(); return lead + PAR[key].h(inner) + K.plusK(k); }
  function tfF(key, a, h, k) { a = R(a).val(); return function (x) { return a * PAR[key].f(x - h) + k; }; }
  function mv(h, k) { return 'Shift ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + ' and ' + (k > 0 ? 'up ' + k : 'down ' + (-k)); }
  var PW = { 5: K.xp(5), 4: K.xp(4), 3: K.xp(3), 2: K.xp(2), 1: X, 0: '' };
  function polyP(cs) { return P(Object.keys(cs).map(Number).sort(function (a, b) { return b - a; }).map(function (p) { return [cs[p], PW[p]]; })); }
  var EO = ['Even', 'Odd', 'Neither', 'Both even and odd'];
  var c27 = [
    [
      function () { // describe the shift
        var key = pick(['sq', 'ab', 'sr', 'cu']), h = rnz(-7, 7), k = rnz(-7, 7);
        return attach(Q({ q: 'How is the graph of ' + m(I('y') + ' = ' + tf(key, 1, h, k)) + ' obtained from the graph of ' + m(I('y') + ' = ' + PAR[key].h(X)) + '?', mc: mc(mv(h, k), [mv(-h, k), mv(h, -k), mv(-h, -k)]), why: ['Inside: ' + m(K.minusH(I('x'), h)) + ' moves the graph ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + ' (the sign works opposite inside).', 'Outside: ' + m(K.plusK(k).trim()) + ' moves the graph ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + '.', 'So: ' + mv(h, k).toLowerCase() + '.'] }), { kind: 'shiftDesc', fq: true, key: key });
      },
      function () { // vertex
        var key = pick(['sq', 'ab']), a = pick([1, -1, 2, -2, 3]), h = rnz(-7, 7), k = rnz(-7, 7);
        return attach(Q({ q: 'What is the vertex of the graph of ' + m(I('y') + ' = ' + tf(key, a, h, k)) + '?', mc: mc(K.pt(h, k), [K.pt(-h, k), K.pt(h, -k), K.pt(-h, -k)]), why: ['The parent ' + m(I('y') + ' = ' + PAR[key].h(X)) + ' has its vertex at ' + K.pt(0, 0) + '.', m(K.minusH(I('x'), h)) + ' inside shifts it ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + '; ' + m(K.plusK(k).trim()) + ' outside shifts it ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + '.', (a === -1 ? 'The negative sign in front flips the graph upside down, but it does not move the vertex. ' : a !== 1 ? 'The factor ' + n(a) + ' changes the width' + (a < 0 ? ' and flips the graph' : '') + ', not the vertex. ' : '') + 'Vertex: ' + K.pt(h, k) + '.'] }), { kind: 'vertex', fq: true, key: key });
      },
      function () { // even / odd / neither polynomial
        var type = pick(['e', 'o', 'n']), cs = {}, ps;
        ps = type === 'e' ? K.sample([4, 2, 0], 2) : type === 'o' ? K.sample([5, 3, 1], 2) : [pick([5, 3, 1]), pick([4, 2, 0])];
        if (type !== 'n' && K.coin()) ps.push(type === 'e' ? [4, 2, 0].filter(function (z) { return ps.indexOf(z) < 0; })[0] : [5, 3, 1].filter(function (z) { return ps.indexOf(z) < 0; })[0]);
        ps.forEach(function (p) { cs[p] = rnz(-6, 6); });
        var neg = {}; Object.keys(cs).forEach(function (p) { neg[p] = p % 2 ? -cs[p] : cs[p]; });
        var right = EO[type === 'e' ? 0 : type === 'o' ? 1 : 2];
        return attach(Q({ q: 'Is ' + fx('f', polyP(cs)) + ' even, odd, or neither?', mc: mc(right, EO.filter(function (z) { return z !== right; })), why: ['Find ' + m(I('f') + '(' + M + I('x') + ')') + ': every odd power of ' + m('(' + M + I('x') + ')') + ' changes sign; every even power does not.', m(I('f') + '(' + M + I('x') + ') = ' + polyP(neg)) + '.', type === 'e' ? 'This equals ' + m(I('f') + '(' + I('x') + ')') + ', so ' + I('f') + ' is even (symmetric about the ' + Y + '-axis).' : type === 'o' ? 'This equals ' + m(M + I('f') + '(' + I('x') + ')') + ', so ' + I('f') + ' is odd (symmetric about the origin).' : 'This equals neither ' + m(I('f') + '(' + I('x') + ')') + ' nor ' + m(M + I('f') + '(' + I('x') + ')') + ' (the powers are mixed), so ' + I('f') + ' is neither.'] }), { kind: 'evenOdd', fq: true });
      }
    ],
    [
      function () { // equation from the graph
        var key = pick(['sq', 'ab', 'sr']), a = pick([1, -1]), h = rnz(-4, 4), k = rnz(-4, 4);
        var g = K.plane({ x: [-8, 8], y: [-8, 8], fns: [{ f: PAR[key].f, color: C.gray, dash: true, from: key === 'sr' ? 0 : -8 }, { f: tfF(key, a, h, k), from: key === 'sr' ? h : -8 }], pts: [{ x: h, y: k }] });
        desc('dashed parent y = ' + (key === 'sq' ? 'x^2' : key === 'ab' ? '|x|' : 'sqrt(x)') + '; solid curve with key point (' + n(h) + ', ' + n(k) + ')' + (a < 0 ? ', reflected' : ''));
        var ch = function (aa, hh, kk) { return m(I('y') + ' = ' + tf(key, aa, hh, kk)); };
        return attach(Q({ q: 'The dashed gray graph is ' + m(I('y') + ' = ' + PAR[key].h(X)) + '. The solid blue graph is a transformation of it. Which equation gives the blue graph?', graph: g, mc: mc(ch(a, h, k), [ch(a, -h, k), ch(a, h, -k), ch(-a, h, k)]), why: ['The key point (' + (key === 'sr' ? 'starting point' : 'vertex') + ') moved from ' + K.pt(0, 0) + ' to ' + K.pt(h, k) + ': ' + mv(h, k).toLowerCase() + '.', a < 0 ? 'The graph ' + (key === 'sr' ? 'goes down' : 'opens down') + ', so it is reflected across the ' + X + '-axis: a negative sign in front.' : 'It ' + (key === 'sr' ? 'goes up' : 'opens up') + ' with the same shape, so there is no reflection or stretch.', (h > 0 ? 'Right ' + h : 'Left ' + (-h)) + ' means ' + m(K.minusH(I('x'), h)) + ' inside' + (h < 0 ? ' (left uses +)' : '') + ': ' + ch(a, h, k) + '.'] }), { kind: 'tfGraph', key: key, a: a, h: h, kk: k });
      },
      function () { // domain & range of a transformed square root
        var a = pick([1, -1, 2, -2]), h, k; do { h = rnz(-6, 6); k = rnz(-6, 6); } while (h === k || h === -k);
        var d = iv(h, Infinity, true), r = a > 0 ? iv(k, Infinity, true) : iv(-Infinity, k, false, true), r2 = a > 0 ? iv(-Infinity, k, false, true) : iv(k, Infinity, true);
        return attach(Q({ q: 'Find the domain and range of ' + fx('f', tf('sr', a, h, k)) + ' in interval notation.', mc: mc(DR(d, r), [DR(iv(-h, Infinity, true), r), DR(d, r2), DR(r, d)]), why: ['Domain: the radicand must be nonnegative: ' + m(K.minusH(I('x'), h) + ' ≥ 0') + ', so ' + m(I('x') + ' ≥ ' + n(h)) + ': ' + m(d) + '.', 'The graph starts at ' + K.pt(h, k) + ' and ' + (a > 0 ? 'rises' : 'falls (the negative in front reflects it)') + '.', 'Range: ' + m(r) + '.'] }), { kind: 'domRange', fq: true });
      },
      function () { // equation from a description
        var key = pick(['sr', 'ab', 'sq']), h = rnz(-6, 6), k = rnz(-6, 6), s = pick([1, -1]);
        var ch = function (ss, hh, kk) { return m(I('y') + ' = ' + tf(key, ss, hh, kk)); };
        var d = 'The graph of ' + m(I('y') + ' = ' + PAR[key].h(X)) + ' is shifted ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + ' unit' + (Math.abs(h) > 1 ? 's' : '') + (s < 0 ? ', reflected across the ' + X + '-axis,' : ',') + ' and then shifted ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + ' unit' + (Math.abs(k) > 1 ? 's' : '') + '. Which equation describes the new graph?';
        return attach(Q({ q: d, mc: mc(ch(s, h, k), [ch(s, -h, k), ch(s, h, -k), ch(-s, h, k)]), why: [(h > 0 ? 'Right ' + h : 'Left ' + (-h)) + ': replace ' + X + ' with ' + m(K.minusH(I('x'), h)) + '.', s < 0 ? 'Reflect across the ' + X + '-axis: put a negative sign in front of the function.' : 'No reflection, so no negative sign in front.', (k > 0 ? 'Up ' + k : 'Down ' + (-k)) + ': ' + (k > 0 ? 'add ' + k : 'subtract ' + (-k)) + ' at the end. Result: ' + ch(s, h, k) + '.'] }), { kind: 'tfDesc', key: key, s: s, h: h, kk: k });
      },
      function () { // image of a point
        var a = rnz(-6, 6), b = rnz(-6, 6), t = pick(['shift', 'negOut', 'negIn', 'stretch']), h = rnz(-5, 5), k = rnz(-5, 5), c = pick([2, 3, 4, -2, -3]), gH, ans, wr, why;
        var fI = function (inner) { return I('f') + '(' + inner + ')'; };
        if (t === 'shift') { gH = fI(K.minusH(X, h)) + K.plusK(k); ans = K.pt(a + h, b + k); wr = [K.pt(a - h, b + k), K.pt(a + h, b - k), K.pt(a - h, b - k)]; why = ['Inside ' + m(K.minusH(I('x'), h)) + ': ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + ', so add ' + n(h) + ' to the ' + X + '-coordinate.', 'Outside ' + m(K.plusK(k).trim()) + ': ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + ', so add ' + n(k) + ' to the ' + Y + '-coordinate.', K.pt(a, b) + ' moves to ' + ans + '.']; }
        if (t === 'negOut') { gH = M + fI(X); ans = K.pt(a, -b); wr = [K.pt(-a, b), K.pt(-a, -b), K.pt(b, a)]; why = [m(M + I('f') + '(' + I('x') + ')') + ' reflects the graph across the ' + X + '-axis.', 'The ' + X + '-coordinate stays and the ' + Y + '-coordinate changes sign.', K.pt(a, b) + ' moves to ' + ans + '.']; }
        if (t === 'negIn') { gH = fI(M + I('x')); ans = K.pt(-a, b); wr = [K.pt(a, -b), K.pt(-a, -b), K.pt(b, a)]; why = [m(I('f') + '(' + M + I('x') + ')') + ' reflects the graph across the ' + Y + '-axis.', 'The ' + X + '-coordinate changes sign and the ' + Y + '-coordinate stays.', K.pt(a, b) + ' moves to ' + ans + '.']; }
        if (t === 'stretch') { gH = n(c) + fI(X); ans = K.pt(a, c * b); wr = [K.pt(c * a, b), K.pt(a, b + c), K.pt(a, R(b, c))]; why = ['A factor in front multiplies the outputs: every ' + Y + '-coordinate is multiplied by ' + n(c) + '.', 'The ' + X + '-coordinate does not change.', K.pt(a, b) + ' moves to ' + ans + '.']; }
        return attach(Q({ q: 'The point ' + K.pt(a, b) + ' is on the graph of ' + m(I('y') + ' = ' + I('f') + '(' + I('x') + ')') + '. Which point must be on the graph of ' + m(I('y') + ' = ' + gH) + '?', mc: mc(ans, wr, function () { return K.pt(a + rnz(-3, 3), b + rnz(-3, 3)); }), why: why }), { kind: 'ptImage', a: a, b: b, t: t, h: h, kk: k, c: c });
      }
      ,
      function () { // horizontal stretch or shrink: image of a point under y = f(cx)
        var c = pick([2, 3, 4, R(1, 2), R(1, 3)]), cR = R(c), b = rnz(-6, 6), a, ans;
        if (cR.d === 1) { var t = rnz(-4, 4); a = cR.n * t; ans = [t, b]; } else { a = rnz(-4, 4); ans = [a * cR.d, b]; }
        var gH = I('f') + '(' + (cR.d === 1 ? n(cR.n) : cR.html()) + I('x') + ')';
        var wr = [K.pt(cR.mul(a), b), K.pt(a, cR.mul(b)), K.pt(a, R(b).div(cR))];
        return attach(Q({ q: 'The point ' + K.pt(a, b) + ' is on the graph of ' + m(I('y') + ' = ' + I('f') + '(' + I('x') + ')') + '. Which point must be on the graph of ' + m(I('y') + ' = ' + gH) + '?', mc: mc(K.pt(ans[0], ans[1]), wr, function () { return K.pt(ans[0] + rnz(-3, 3), b + rnz(-3, 3)); }), why: ['A number multiplying ' + X + ' <em>inside</em> the function changes the graph horizontally, and it works backward: each ' + X + '-coordinate is divided by ' + (cR.d === 1 ? n(cR.n) : cR.html()) + '.', 'The ' + Y + '-coordinate (the height) does not change.', m(n(a) + ' ÷ ' + (cR.d === 1 ? n(cR.n) : cR.html()) + ' = ' + n(ans[0])) + ', so ' + K.pt(a, b) + ' moves to ' + K.pt(ans[0], ans[1]) + '. The graph is ' + (cR.d === 1 ? 'shrunk horizontally (pulled toward the ' + Y + '-axis).' : 'stretched horizontally (pushed away from the ' + Y + '-axis).')] }), { kind: 'ptImage', a: a, b: b, t: 'hstretch' });
      },
      function () { // symmetry of an equation: x-axis, y-axis, origin
        var T = pick(['xq', 'xl', 'yq', 'ya', 'circ', 'ell', 'cub', 'xy']), a = rnz(-4, 4), c = rnz(-6, 6), eq, lab;
        var Y2 = Y + '<sup>2</sup>', lead = function (k) { return k === 1 ? '' : k === -1 ? M : n(k); };
        if (T === 'xq') { eq = X + ' = ' + P([[a, Y2], [c, '']]); lab = 'x'; }
        if (T === 'xl') { eq = Y2 + ' = ' + P([[a, X], [c, '']]); lab = 'x'; }
        if (T === 'yq') { eq = Y + ' = ' + P([[a, K.xp(2)], [c, '']]); lab = 'y'; }
        if (T === 'ya') { eq = Y + ' = ' + lead(a) + '|' + X + '|' + K.plusK(c); lab = 'y'; }
        if (T === 'circ') { eq = K.xp(2) + ' + ' + Y2 + ' = ' + n(ri(2, 7) * ri(2, 7)); lab = 'all'; }
        if (T === 'ell') { var u = ri(2, 5); eq = n(u) + K.xp(2) + ' + ' + Y2 + ' = ' + n(u * ri(2, 9)); lab = 'all'; }
        if (T === 'cub') { eq = Y + ' = ' + P([[a, K.xp(3)], [K.coin() ? rnz(-5, 5) : 0, X]]); lab = 'o'; }
        if (T === 'xy') { eq = X + Y + ' = ' + n(rnz(-9, 9)); lab = 'o'; }
        var L = { x: 'The ' + X + '-axis only', y: 'The ' + Y + '-axis only', o: 'The origin only', all: 'The ' + X + '-axis, the ' + Y + '-axis, and the origin' };
        var right = L[lab];
        var why = ['Test each symmetry on ' + m(eq) + ': replace ' + Y + ' with ' + m(M + I('y')) + ' (' + X + '-axis), replace ' + X + ' with ' + m(M + I('x')) + ' (' + Y + '-axis), or replace both (origin). Symmetry means the new equation is equivalent to the original.'];
        why.push(lab === 'x' ? 'Only ' + Y + ' is squared, and ' + m('(' + M + I('y') + ')<sup>2</sup> = ' + Y2) + ', so replacing ' + Y + ' with ' + m(M + I('y')) + ' changes nothing; replacing ' + X + ' with ' + m(M + I('x')) + ' changes the ' + X + '-term.'
          : lab === 'y' ? 'Every ' + X + ' appears as ' + (T === 'ya' ? m('|' + I('x') + '|') : K.xp(2)) + ', and ' + (T === 'ya' ? m('|' + M + I('x') + '| = |' + I('x') + '|') : m('(' + M + I('x') + ')<sup>2</sup> = ' + K.xp(2))) + ', so replacing ' + X + ' with ' + m(M + I('x')) + ' changes nothing; replacing ' + Y + ' with ' + m(M + I('y')) + ' does change the equation.'
          : lab === 'all' ? 'Both variables appear only squared, so every replacement gives the same equation.'
          : 'Replacing only one variable changes the sign of one side, but replacing both gives ' + (T === 'xy' ? m('(' + M + I('x') + ')(' + M + I('y') + ') = ' + X + Y) : m(M + I('y') + ' = ' + M + '(' + eq.split(' = ')[1] + ')')) + ', which is equivalent to the original.');
        why.push('So the graph is symmetric about ' + (lab === 'all' ? 'the ' + X + '-axis, the ' + Y + '-axis, and the origin.' : right.replace(' only', '').replace('The ', 'the ') + ' only.'));
        return attach(Q({ q: 'Which symmetry does the graph of ' + m(eq) + ' have?', mc: mc(right, Object.keys(L).filter(function (k) { return k !== lab; }).map(function (k) { return L[k]; })), why: why }), { kind: 'symEq', T: T });
      }
    ],
    [
      function () { // x-intercepts of a|x − h| + k
        var a = pick([1, 2, 3, -1, -2, -3]), t = ri(1, 5), h = rnz(-5, 5), k = -a * t;
        var ch = function (u, v) { return m(I('x') + ' = ' + n(Math.min(u, v)) + ' and ' + I('x') + ' = ' + n(Math.max(u, v))); };
        return attach(Q({ q: 'Find the ' + X + '-intercepts of the graph of ' + m(I('y') + ' = ' + tf('ab', a, h, k)) + '.', mc: mc(ch(h - t, h + t), [ch(-h - t, -h + t), ch(h - Math.abs(k), h + Math.abs(k)), 'There are no ' + X + '-intercepts'], function () { return ch(h - t - rnz(1, 2), h + t); }), why: ['Set ' + m(I('y') + ' = 0') + ': ' + m(tf('ab', a, h, k) + ' = 0') + ', so ' + m((a === 1 ? '' : a === -1 ? M : n(a)) + '|' + K.minusH(I('x'), h) + '| = ' + n(-k)) + ' and ' + m('|' + K.minusH(I('x'), h) + '| = ' + t) + '.', 'Two cases: ' + m(K.minusH(I('x'), h) + ' = ' + t) + ' or ' + m(K.minusH(I('x'), h) + ' = ' + M + t) + '.', 'So ' + ch(h - t, h + t) + '. (The graph ' + (a > 0 ? 'opens up from a vertex below' : 'opens down from a vertex above') + ' the ' + X + '-axis, so it crosses the axis twice.)'] }), { kind: 'absZeros', fq: true });
      },
      function () { // symmetry, non-polynomials
        var a = rnz(-5, 5), c = ri(1, 9), d, T = pick(['o1', 'o2', 'o3', 'e1', 'e2', 'e3', 'n1', 'n2', 'n3']), f, type;
        if (T === 'o1') { f = K.frx(P([[a, X]]), P([[1, K.xp(2)], [c, '']])); type = 1; }
        if (T === 'o2') { f = P([[a, X]]) + ' + ' + K.frx(String(c), X); type = 1; }
        if (T === 'o3') { f = P([[a, K.xp(3)]]) + ' ' + (K.coin() ? '+' : M) + ' ' + (c === 1 ? '' : c) + I('x'); type = 1; }
        if (T === 'e1') { f = '|' + X + '|' + K.coef(a) + K.xp(2); type = 0; }
        if (T === 'e2') { do { d = ri(1, 9); } while (d === c); f = K.frx(P([[1, K.xp(2)], [c, '']]), P([[1, K.xp(2)], [d, '']])); type = 0; }
        if (T === 'e3') { f = K.sqrt(P([[1, K.xp(2)], [c, '']])); type = 0; }
        if (T === 'n1') { f = P([[a, K.xp(3)]]) + ' + ' + (c === 1 ? '' : c) + '|' + X + '|'; type = 2; }
        if (T === 'n2') { f = '(' + P([[1, X], [K.coin() ? c : -c, '']]) + ')<sup>2</sup>'; type = 2; }
        if (T === 'n3') { f = P([[a, K.xp(3)], [K.coin() ? c : -c, '']]); type = 2; }
        var right = EO[type];
        return attach(Q({ q: 'Is ' + fx('f', f) + ' even, odd, or neither?', mc: mc(right, EO.filter(function (z) { return z !== right; })), why: ['Replace ' + X + ' with ' + m(M + I('x')) + ' and simplify. Use ' + m('|' + M + I('x') + '| = |' + I('x') + '|') + ' and ' + m('(' + M + I('x') + ')<sup>2</sup> = ' + K.xp(2)) + '.', type === 0 ? m(I('f') + '(' + M + I('x') + ') = ' + I('f') + '(' + I('x') + ')') + ' for every ' + X + ' in the domain.' : type === 1 ? m(I('f') + '(' + M + I('x') + ') = ' + M + I('f') + '(' + I('x') + ')') + ' for every ' + X + ' in the domain.' : 'For example, ' + m(I('f') + '(' + M + '1)') + ' equals neither ' + m(I('f') + '(1)') + ' nor ' + m(M + I('f') + '(1)') + '.', 'So ' + I('f') + ' is ' + (type === 0 ? 'even (symmetric about the ' + Y + '-axis)' : type === 1 ? 'odd (symmetric about the origin)' : 'neither even nor odd') + '.'] }), { kind: 'evenOdd', fq: true });
      },
      function () { // g in terms of f, from graphs
        var xs = [-3, -1, 1, 3], ys, h, k, s = K.coin() ? 1 : pick([1, -1]);
        do { ys = xs.map(function () { return ri(-2, 2); }); } while (ys[0] === ys[1] && ys[1] === ys[2]);
        do { h = rnz(-3, 3); k = rnz(-3, 3); } while (Math.abs(k) + 2 > 7);
        var gx = xs.map(function (x) { return x + h; }), gy = ys.map(function (y) { return s * y + k; });
        var segs = [], pts = [];
        for (var i = 0; i < 3; i++) { segs.push({ x1: xs[i], y1: ys[i], x2: xs[i + 1], y2: ys[i + 1], color: C.gray, dash: true }); segs.push({ x1: gx[i], y1: gy[i], x2: gx[i + 1], y2: gy[i + 1] }); }
        [0, 3].forEach(function (j) { pts.push({ x: xs[j], y: ys[j], color: C.gray }); pts.push({ x: gx[j], y: gy[j] }); });
        var g = K.plane({ x: [-8, 8], y: [-8, 8], segs: segs, pts: pts, texts: [{ x: xs[0] - 0.6, y: ys[0] + 0.7, t: 'f', color: C.gray }, { x: gx[3] + 0.6, y: gy[3] + 0.7, t: 'g', color: C.blue }] });
        desc('f (dashed gray) through ' + xs.map(function (x, j) { return '(' + n(x) + ', ' + n(ys[j]) + ')'; }).join(' ') + '; g (solid blue) through ' + gx.map(function (x, j) { return '(' + n(x) + ', ' + n(gy[j]) + ')'; }).join(' '));
        var ch = function (ss, hh, kk) { return m(I('g') + '(' + I('x') + ') = ' + (ss < 0 ? M : '') + I('f') + '(' + K.minusH(X, hh) + ')' + K.plusK(kk)); };
        return attach(Q({ q: 'The dashed gray graph is ' + m(I('y') + ' = ' + I('f') + '(' + I('x') + ')') + ' and the solid blue graph is ' + m(I('y') + ' = ' + I('g') + '(' + I('x') + ')') + '. Which equation describes ' + I('g') + '?', graph: g, mc: mc(ch(s, h, k), [ch(s, -h, k), ch(s, h, -k), ch(-s, h, k)]), why: ['Match corresponding points: ' + K.pt(xs[0], ys[0]) + ' on ' + I('f') + ' goes to ' + K.pt(gx[0], gy[0]) + ' on ' + I('g') + ', and ' + K.pt(xs[3], ys[3]) + ' goes to ' + K.pt(gx[3], gy[3]) + '.', 'Every point moves ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + (s < 0 ? '; the ' + Y + '-values are also flipped (reflection across the ' + X + '-axis) and then moved ' : ' and ') + (k > 0 ? 'up ' + k : 'down ' + (-k)) + '.', 'So ' + ch(s, h, k) + '.'] }), { kind: 'gFromF', xs: xs, ys: ys, gx: gx, gy: gy });
      },
      function () { // stretch factor from the graph
        var a = pick([R(2), R(-2), R(1, 2), R(-1, 2), R(3), R(-3)]), h = ri(-4, 4), k, dx = a.d === 2 ? 2 : 1;
        do { k = ri(-5, 5); } while (Math.abs(k + a.mul(dx * dx).val()) > 7);
        var f = tfF('sq', a, h, k), y2 = k + a.mul(dx * dx).val();
        var g = K.plane({ x: [-8, 8], y: [-8, 8], fns: [{ f: function (x) { return (x - h) * (x - h); }, color: C.gray, dash: true }, { f: f }], pts: [{ x: h, y: k }, { x: h + dx, y: y2 }, { x: h - dx, y: y2 }] });
        var ch = function (aa) { return m(I('y') + ' = ' + tf('sq', aa, h, k)); };
        return attach(Q({ q: 'The solid parabola has vertex ' + K.pt(h, k) + ' and passes through ' + K.pt(h + dx, y2) + ' (both marked). The dashed parabola is ' + m(I('y') + ' = ' + tf('sq', 1, h, 0)) + ' for comparison. Which equation gives the solid parabola?', graph: g, mc: mc(ch(a), [ch(R(a.d, a.n)), ch(a.neg()), ch(a.mul(2))]), why: ['The vertex gives ' + m(I('y') + ' = ' + I('a') + tf('sq', 1, h, k)) + '.', 'Substitute ' + K.pt(h + dx, y2) + ': ' + m(n(y2) + ' = ' + I('a') + '(' + dx + ')<sup>2</sup>' + K.plusK(k)) + ', so ' + (dx === 1 ? '' : m((dx * dx) + I('a') + ' = ' + n(y2 - k)) + ' and ') + m(I('a') + ' = ' + a.html()) + '.', (Math.abs(a.val()) > 1 ? 'Since ' + m('|' + I('a') + '| &gt; 1') + ', the graph is narrower than ' + m(I('y') + ' = ' + K.xp(2)) : 'Since ' + m('|' + I('a') + '| &lt; 1') + ', the graph is wider than ' + m(I('y') + ' = ' + K.xp(2))) + (a.n < 0 ? ', and it opens down.' : '.')] }), { kind: 'stretchA', h: h, kk: k, pts: [[h, k], [h + dx, y2]] });
      }
    ]
  ];
  K.lesson('2.7', { title: 'Graphing Techniques', std: 'Lial 12e · Section 2.7', levels: c27 });

  /* ================= 2.8 Function Operations and Composition ================= */
  function pArr(c) { var t = []; for (var i = c.length - 1; i >= 0; i--) t.push([c[i], K.xp(i)]); return P(t); } // c[i] = coefficient of x^i
  // narrower table cells so a 7-column table fits a phone screen
  function tight(h) { return h.replace(/<t([dh])>/g, '<t$1 style="padding:6px 9px">'); }
  function fg2(fH, gH) { return fx('f', fH) + ' and ' + fx('g', gH); }
  var OPS = { '+': ['(' + I('f') + ' + ' + I('g') + ')'], '−': ['(' + I('f') + ' ' + M + ' ' + I('g') + ')'], '·': ['(' + I('f') + I('g') + ')'], '/': ['(' + I('f') + '/' + I('g') + ')'] };
  var c28 = [
    [
      function () { // evaluate a sum/difference/product/quotient
        var a = rnz(-4, 4), b = ri(-6, 6), c = rnz(-6, 6), op = pick(['+', '−', '·', '/']), t, F, G;
        do { t = ri(-3, 3); F = a * t + b; G = t * t + c; } while (G === 0 || F === 0);
        var vals = { '+': R(F + G), '−': R(F - G), '·': R(F * G), '/': R(F, G) }, right = vals[op];
        return attach(Q({ q: 'Let ' + fg2(lin(a, b), P([[1, K.xp(2)], [c, '']])) + '. Find ' + m(OPS[op][0] + '(' + n(t) + ')') + '.', mc: mcV(right.html(), right.val(), Object.keys(vals).filter(function (o) { return o !== op; }).map(function (o) { return [vals[o].html(), vals[o].val()]; }), function () { var z = right.add(rnz(-4, 4)); return [z.html(), z.val()]; }), why: ['Evaluate each function: ' + m(I('f') + '(' + n(t) + ') = ' + K.lin([[a, n(t)]]) + K.plusK(b) + ' = ' + n(F)) + ' and ' + m(I('g') + '(' + n(t) + ') = ' + sb(t) + '<sup>2</sup>' + K.plusK(c) + ' = ' + n(G)) + '.', op === '/' ? 'Divide: ' + m(eqs(frq(F, G), right.html())) + '.' : 'Combine: ' + m(n(F) + ' ' + (op === '+' ? '+' : op === '−' ? M : '·') + ' ' + sb(G) + ' = ' + right.html()) + '.', 'So ' + m(OPS[op][0] + '(' + n(t) + ') = ' + right.html()) + '.'] }), { kind: 'opVal', fq: true, op: op, x: t });
      },
      function () { // composition at a number
        var a = rnz(-4, 4), b = ri(-6, 6), c = ri(-6, 6), t = ri(-3, 3), sw = K.coin();
        var lf = function (x) { return a * x + b; }, qf = function (x) { return x * x + c; };
        var f = sw ? qf : lf, g = sw ? lf : qf, fH = sw ? P([[1, K.xp(2)], [c, '']]) : lin(a, b), gH = sw ? lin(a, b) : P([[1, K.xp(2)], [c, '']]);
        var ans = f(g(t)), alt = g(f(t));
        return attach(Q({ q: 'Let ' + fg2(fH, gH) + '. Find ' + m('(' + I('f') + ' ∘ ' + I('g') + ')(' + n(t) + ')') + '.', mc: mcV(n(ans), ans, [[n(alt), alt], [n(f(t) * g(t)), f(t) * g(t)], [n(g(t)), g(t)]], nx(ans)), why: ['Work from the inside out: ' + m('(' + I('f') + ' ∘ ' + I('g') + ')(' + n(t) + ') = ' + I('f') + '(' + I('g') + '(' + n(t) + '))') + '.', 'Inside: ' + m(I('g') + '(' + n(t) + ') = ' + n(g(t))) + '.', 'Outside: ' + m(I('f') + '(' + n(g(t)) + ') = ' + n(ans)) + '.' + (alt !== ans ? ' (' + n(alt) + ' would be ' + m(I('g') + '(' + I('f') + '(' + n(t) + '))') + ', the other order.)' : '')] }), { kind: 'compVal', fq: true, x: t });
      },
      function () { // domain of f/g
        var p = ri(-6, 6), a = pick([1, 2, 3, -1, -2]), b = rnz(-6, 6), r = R(-b, a);
        if (r.eq(-p)) p = p + 1;
        var d = cup([iv(-Infinity, r), iv(r, Infinity)]);
        return attach(Q({ q: 'Let ' + fg2(lin(1, p), lin(a, b)) + '. Find the domain of ' + m('(' + I('f') + '/' + I('g') + ')(' + I('x') + ')') + ' in interval notation.', mc: mc(m(d), [m(cup([iv(-Infinity, -p), iv(-p, Infinity)])), m(ALL), m(iv(r, Infinity))]), why: ['Both ' + I('f') + ' and ' + I('g') + ' are defined for all real numbers.', 'The denominator cannot be 0: ' + m(lin(a, b) + ' = 0') + ' when ' + m(I('x') + ' = ' + r.html()) + '.', 'Domain: ' + m(d) + '. (The numerator being 0 is allowed.)'] }), { kind: 'domQ', fq: true });
      }
    ],
    [
      function () { // composition formula
        var a = rnz(-4, 4), b = rnz(-5, 5), c = rnz(-3, 3), d = ri(-6, 6), fog = K.coin();
        var FG = [a * d + b, 0, a * c], GF = [c * b * b + d, 2 * a * b * c, c * a * a], PR = [b * d, a * d, b * c, a * c];
        var right = fog ? FG : GF, w1 = fog ? GF : FG, w2 = PR, w3 = fog ? [b + d, 0, a * c] : [c * b * b + d, 0, c * a * a];
        var fH = lin(a, b), gH = P([[c, K.xp(2)], [d, '']]);
        var ch = function (cs) { return m(pArr(cs)); };
        return attach(Q({ q: 'Let ' + fg2(fH, gH) + '. Find ' + m('(' + I(fog ? 'f' : 'g') + ' ∘ ' + I(fog ? 'g' : 'f') + ')(' + I('x') + ')') + ' and simplify.', mc: mc(ch(right), [ch(w1), ch(w2), ch(w3)], function () { var z = right.slice(); z[0] += rnz(-3, 3); return ch(z); }), why: fog ? ['Put ' + I('g') + ' inside ' + I('f') + ': ' + m(I('f') + '(' + gH + ') = ' + K.coef(a, true) + '(' + gH + ')' + K.plusK(b)) + '.', 'Distribute: ' + m(P([[a * c, K.xp(2)], [a * d, '']]) + K.plusK(b)) + '.', 'Combine: ' + ch(FG) + '.'] : ['Put ' + I('f') + ' inside ' + I('g') + ': ' + m(I('g') + '(' + fH + ') = ' + K.coef(c, true) + '(' + fH + ')<sup>2</sup>' + K.plusK(d)) + '.', 'Square the binomial (with the middle term): ' + m('(' + fH + ')<sup>2</sup> = ' + pArr([b * b, 2 * a * b, a * a])) + '.', (function () { var t = (c === 1 ? '' : 'multiply by ' + n(c) + ', then ') + (d > 0 ? 'add ' + d : d < 0 ? 'subtract ' + (-d) : 'simplify'); return t.charAt(0).toUpperCase() + t.slice(1); })() + ': ' + ch(GF) + '.'] }), { kind: 'compF', fq: true, fog: fog });
      },
      function () { // difference quotient
        var a = rnz(-4, 4), b = rnz(-6, 6), c = ri(-6, 6);
        var ch = function (p, q, r) { return m(P([[p, X], [q, I('h')], [r, '']])); };
        return attach(Q({ q: 'Find and simplify the difference quotient ' + m(K.frx(I('f') + '(' + I('x') + ' + ' + I('h') + ') ' + M + ' ' + I('f') + '(' + I('x') + ')', I('h'))) + ', ' + m(I('h') + ' ≠ 0') + ', for ' + fx('f', quad(a, b, c)) + '.', mc: mc(ch(2 * a, a, b), [ch(2 * a, 0, b), ch(0, a, b), ch(2 * a, a, -b)]), why: [m(I('f') + '(' + I('x') + ' + ' + I('h') + ') = ' + K.coef(a, true) + '(' + I('x') + ' + ' + I('h') + ')<sup>2</sup>' + K.coef(b) + '(' + I('x') + ' + ' + I('h') + ')' + K.plusK(c)) + ' = ' + m(P([[a, K.xp(2)], [2 * a, I('x') + I('h')], [a, K.xp(2, 'h')], [b, X], [b, I('h')], [c, '']])) + '.', 'Subtract ' + m(I('f') + '(' + I('x') + ')') + ': ' + m(P([[2 * a, I('x') + I('h')], [a, K.xp(2, 'h')], [b, I('h')]])) + '.', 'Divide by ' + I('h') + ': ' + ch(2 * a, a, b) + '.'] }), { kind: 'diffQ', fq: true });
      },
      function () { // f − g
        var A = [ri(-6, 6), rnz(-6, 6), rnz(-4, 4)], B = [rnz(-6, 6), rnz(-6, 6), rnz(-4, 4)];
        if (A[2] === B[2]) A[2] += A[2] > 0 ? 1 : -1;
        var sub3 = function (u, v, s) { return u.map(function (z, i) { return z + s * v[i]; }); };
        var right = sub3(A, B, -1), w1 = [A[0] + B[0], A[1] + B[1], A[2] - B[2]], w2 = sub3(A, B, 1), w3 = sub3(B, A, -1);
        var ch = function (cs) { return m(pArr(cs)); };
        return attach(Q({ q: 'Let ' + fg2(pArr(A), pArr(B)) + '. Find ' + m('(' + I('f') + ' ' + M + ' ' + I('g') + ')(' + I('x') + ')') + '.', mc: mc(ch(right), [ch(w1), ch(w2), ch(w3)], function () { var z = right.slice(); z[0] += rnz(-3, 3); return ch(z); }), why: [m('(' + I('f') + ' ' + M + ' ' + I('g') + ')(' + I('x') + ') =') + ' ' + brk('(' + pArr(A) + ') ' + M + ' (' + pArr(B) + ')') + '.', 'Distribute the minus sign to <b>every</b> term of ' + I('g') + ': ' + brk(pArr(A) + ' ' + K.poly([[-B[2], K.xp(2)], [-B[1], X], [-B[0], '']]).replace(/^(−?)/, function (s0) { return s0 ? M + ' ' : '+ '; })) + '.', 'Combine like terms: ' + ch(right) + '.'] }), { kind: 'diffFG', fq: true });
      },
      function () { // composition from tables
        var S = [-2, -1, 0, 1, 2, 3], fv = S.map(function () { return pick(S); }), gv = S.map(function () { return pick(S); }), a = pick(S);
        var F = function (x) { return fv[S.indexOf(x)]; }, G = function (x) { return gv[S.indexOf(x)]; }, ans = F(G(a)), alt = G(F(a));
        return attach(Q({ q: 'Use the tables to find ' + m('(' + I('f') + ' ∘ ' + I('g') + ')(' + n(a) + ')') + '.<div class="center">' + tight(K.xyTable(S, fv, X, m(I('f') + '(' + I('x') + ')'))) + '</div><div class="center">' + tight(K.xyTable(S, gv, X, m(I('g') + '(' + I('x') + ')'))) + '</div>', mc: mcV(n(ans), ans, [[n(alt), alt], [n(G(a)), G(a)], [n(F(a)), F(a)], [n(F(a) * G(a)), F(a) * G(a)]], nx(ans)), why: [m('(' + I('f') + ' ∘ ' + I('g') + ')(' + n(a) + ') = ' + I('f') + '(' + I('g') + '(' + n(a) + '))') + ': start with ' + I('g') + '.', 'From the ' + I('g') + ' table: ' + m(I('g') + '(' + n(a) + ') = ' + n(G(a))) + '.', 'From the ' + I('f') + ' table: ' + m(I('f') + '(' + n(G(a)) + ') = ' + n(ans)) + '.'] }), { kind: 'tableComp', S: S, fv: fv, gv: gv, a: a });
      }
      ,
      function () { // decompose H(x) = f(g(x))
        var T = pick(['pow', 'sqrt', 'recip', 'abs']), a = pick([2, 3, 4, 5, 6, -2, -3]), b = rnz(-9, 9), pw = pick([2, 3, 4]);
        if (T === 'sqrt' && a < 0) b = ri(1, 9); // keep part of the domain on the visible number line
        var inner = lin(a, b), ax = lin(a, 0), outer, outerOn, Hh, wrong;
        if (T === 'pow') { outer = K.xp(pw); outerOn = function (u) { return '(' + u + ')<sup>' + pw + '</sup>'; }; wrong = [[inner, K.xp(pw)], [K.xp(pw), ax], [P([[1, K.xp(pw)], [b, '']]), ax]]; }
        if (T === 'sqrt') { outer = K.sqrt(X); outerOn = function (u) { return K.sqrt(u); }; wrong = [[inner, K.sqrt(X)], [K.sqrt(X), ax], [K.sqrt(X) + K.plusK(b), ax]]; }
        if (T === 'recip') { outer = K.frx('1', X); outerOn = function (u) { return K.frx('1', u); }; wrong = [[inner, K.frx('1', X)], [K.frx('1', X), ax], [K.frx('1', X) + K.plusK(b), ax]]; }
        if (T === 'abs') { outer = '|' + X + '|'; outerOn = function (u) { return '|' + u + '|'; }; wrong = [[inner, '|' + X + '|'], ['|' + X + '|', ax], ['|' + X + '|' + K.plusK(b), ax]]; }
        Hh = outerOn(inner);
        var ch = function (fH, gH) { return m(I('f') + '(' + I('x') + ') = ' + fH) + ', ' + m(I('g') + '(' + I('x') + ') = ' + gH); };
        return attach(Q({ q: 'Find functions ' + I('f') + ' and ' + I('g') + ' so that ' + m(I('H') + '(' + I('x') + ') = ' + Hh) + ' equals ' + m(I('f') + '(' + I('g') + '(' + I('x') + '))') + '.', mc: mc(ch(outer, inner), wrong.map(function (w) { return ch(w[0], w[1]); })), why: ['Ask what is calculated first: ' + m(inner) + '. That inside expression is ' + m(I('g') + '(' + I('x') + ')') + '.', 'The last step ' + (T === 'pow' ? 'raises it to the power ' + pw : T === 'sqrt' ? 'takes the square root' : T === 'recip' ? 'takes the reciprocal' : 'takes the absolute value') + ', so ' + m(I('f') + '(' + I('x') + ') = ' + outer) + '.', 'Check: ' + m(I('f') + '(' + I('g') + '(' + I('x') + ')) = ' + I('f') + '(' + inner + ') = ' + Hh) + '. (Other correct pairs exist, but only this choice works.)'] }), { kind: 'decomp', T: T });
      }
    ],
    [
      function () { // domain of a composition
        var T = pick(['T1', 'T2', 'T3']), fH, gH, d, wr, why;
        if (T === 'T1') {
          var b = pick([1, 2, 3, 4, -1, -2, -3]), t = rnz(-5, 5);
          fH = K.sqrt(X); gH = lin(b, -b * t);
          d = b > 0 ? iv(t, Infinity, true) : iv(-Infinity, t, false, true);
          wr = [iv(0, Infinity, true), ALL, b > 0 ? iv(-Infinity, t, false, true) : iv(t, Infinity, true)];
          why = [m('(' + I('f') + ' ∘ ' + I('g') + ')(' + I('x') + ') = ' + K.sqrt(lin(b, -b * t))) + '.', 'The radicand must be nonnegative: ' + m(lin(b, -b * t) + ' ≥ 0') + (b < 0 ? ' (dividing by a negative flips the inequality)' : '') + ', so ' + m(I('x') + (b > 0 ? ' ≥ ' : ' ≤ ') + n(t)) + '.'];
        } else if (T === 'T2') {
          var a = pick([2, 3, 4, -2, -3, -4]), kk = rnz(-6, 6), r = R(1, a), pts = [R(0), r].sort(function (u, v) { return u.val() - v.val(); });
          fH = K.frx(n(kk), K.minusH(X, a)); gH = K.frx('1', X);
          d = cup([iv(-Infinity, pts[0]), iv(pts[0], pts[1]), iv(pts[1], Infinity)]);
          var pa = [0, a].sort(function (u, v) { return u - v; });
          wr = [cup([iv(-Infinity, r), iv(r, Infinity)]), cup([iv(-Infinity, 0), iv(0, Infinity)]), cup([iv(-Infinity, pa[0]), iv(pa[0], pa[1]), iv(pa[1], Infinity)])];
          why = [I('x') + ' must be in the domain of ' + I('g') + ': ' + m(I('x') + ' ≠ 0') + '.', I('g') + '(' + I('x') + ') must be in the domain of ' + I('f') + ': ' + m(K.frx('1', X) + ' ≠ ' + n(a)) + ', so ' + m(I('x') + ' ≠ ' + r.html()) + '.'];
        } else {
          var s = ri(2, 6);
          fH = K.sqrt(X); gH = P([[s * s, ''], [-1, K.xp(2)]]);
          d = iv(-s, s, true, true);
          wr = [iv(0, s, true, true), iv(-s, s), iv(-s * s, s * s, true, true)];
          why = [m('(' + I('f') + ' ∘ ' + I('g') + ')(' + I('x') + ') = ' + K.sqrt(gH)) + '.', 'Need ' + m(gH + ' ≥ 0') + ', so ' + m(K.xp(2) + ' ≤ ' + s * s) + ' and ' + m(M + s + ' ≤ ' + I('x') + ' ≤ ' + s) + '.'];
        }
        return attach(Q({ q: 'Let ' + fg2(fH, gH) + '. Find the domain of ' + m('(' + I('f') + ' ∘ ' + I('g') + ')(' + I('x') + ')') + ' in interval notation.', mc: mc(m(d), wr.map(m)), why: why.concat(['Domain: ' + m(d) + '.']) }), { kind: 'domComp', fq: true });
      },
      function () { // order matters: (f ∘ g)(x) − (g ∘ f)(x)
        var a = pick([2, 3, -1, -2, -3]), b = rnz(-5, 5), c = rnz(-6, 6), fgFirst = K.coin();
        var FG = [b * b + c, 2 * a * b, a * a], GF = [a * c + b, 0, a], s = fgFirst ? 1 : -1;
        var comb = function (u, v, k) { return u.map(function (z, i) { return s * (z + k * v[i]); }); };
        var right = comb(FG, GF, -1), w1 = FG.map(function (z, i) { return z + GF[i]; }), w2 = right.map(function (z) { return -z; }), w3 = [right[0], 0, right[2]], w4 = comb(FG, [c + b, 0, a], -1);
        var fH = P([[1, K.xp(2)], [c, '']]), gH = lin(a, b), ch = function (cs) { return m(pArr(cs)); };
        var A1 = fgFirst ? 'f' : 'g', A2 = fgFirst ? 'g' : 'f', cmp = function (u, v) { return '(' + I(u) + ' ∘ ' + I(v) + ')(' + I('x') + ')'; };
        return attach(Q({ q: 'Let ' + fg2(fH, gH) + '. Find ' + m(cmp(A1, A2) + ' ' + M + ' ' + cmp(A2, A1)) + ' and simplify.', mc: mc(ch(right), K.shuffle([w1, w2, w3, w4]).map(ch), function (i) { var z = right.slice(); z[0] += (i % 2 ? i : -i); return ch(z); }), why: [m(cmp('f', 'g') + ' = ' + I('f') + '(' + gH + ') =') + ' ' + brk('(' + gH + ')<sup>2</sup>' + K.plusK(c) + ' = ' + pArr(FG)) + ' (square the binomial, middle term included).', m(cmp('g', 'f') + ' = ' + I('g') + '(' + fH + ') =') + ' ' + brk(K.coef(a, true) + '(' + fH + ')' + K.plusK(b) + ' = ' + pArr(GF)) + ' (distribute ' + n(a) + ' to both terms).', 'Subtract in the order asked, changing the sign of every term being subtracted: ' + brk('(' + pArr(fgFirst ? FG : GF) + ') ' + M + ' (' + pArr(fgFirst ? GF : FG) + ') = ' + pArr(right)) + '. The answer is not 0: order matters in composition.'] }), { kind: 'compDiff', fgFirst: fgFirst });
      },
      function () { // coupon and percent
        var Xp = ri(8, 24) * 5, D = pick([5, 10, 15, 20]), pc = pick([10, 20, 25, 30]), first = K.coin(), r = 1 - pc / 100;
        var ans = first ? (Xp - D) * r : Xp * r - D, alt = first ? Xp * r - D : (Xp - D) * r, mon = K.money;
        return attach(Q({ q: 'A store uses ' + m(I('c') + '(' + I('x') + ') = ' + I('x') + ' ' + M + ' ' + D) + ' for ' + art(D) + ' ' + mon(D).replace('.00', '') + ' coupon and ' + m(I('p') + '(' + I('x') + ') = ' + n(r) + I('x')) + ' for ' + pc + '% off. Find ' + m('(' + I(first ? 'p' : 'c') + ' ∘ ' + I(first ? 'c' : 'p') + ')(' + Xp + ')') + ', the final price of ' + art(Xp) + ' ' + mon(Xp).replace('.00', '') + ' item.', mc: mcV(mon(ans), ans, [[mon(alt), alt], [mon(Xp * r), Xp * r], [mon(Xp - D), Xp - D]], function () { var z = ans + rnz(-6, 6); return [mon(z), z]; }), why: ['Inside first: ' + (first ? m(I('c') + '(' + Xp + ') = ' + (Xp - D)) + ' (coupon first).' : m(I('p') + '(' + Xp + ') = ' + n(r) + '(' + Xp + ') = ' + n(Xp * r)) + ' (discount first).'), 'Then the outer function: ' + (first ? m(I('p') + '(' + (Xp - D) + ') = ' + n(r) + '(' + (Xp - D) + ') = ' + n(ans)) : m(I('c') + '(' + n(Xp * r) + ') = ' + n(Xp * r) + ' ' + M + ' ' + D + ' = ' + n(ans))) + '.', 'Final price: ' + mon(ans) + '. The other order gives ' + mon(alt) + ', so order matters.'] }), { kind: 'coupon', Xp: Xp, D: D, pc: pc, first: first });
      },
      function () { // ripple area
        var c = pick([3, 4, 5, 6]);
        var ch = function (co, tp) { return m('(' + I('A') + ' ∘ ' + I('r') + ')(' + I('t') + ') = ' + co + 'π' + I('t') + (tp > 1 ? '<sup>' + tp + '</sup>' : '')); };
        return attach(Q({ q: 'A stone dropped in a pond makes a circular ripple whose radius after ' + I('t') + ' seconds is ' + m(I('r') + '(' + I('t') + ') = ' + c + I('t')) + ' inches. The area of a circle is ' + m(I('A') + '(' + I('r') + ') = π' + I('r') + '<sup>2</sup>') + '. Find ' + m('(' + I('A') + ' ∘ ' + I('r') + ')(' + I('t') + ')') + '.', mc: mc(ch(c * c, 2), [ch(c, 2), ch(c * c, 1), ch(2 * c, 2)]), why: [m('(' + I('A') + ' ∘ ' + I('r') + ')(' + I('t') + ') = ' + I('A') + '(' + I('r') + '(' + I('t') + ')) = ' + I('A') + '(' + c + I('t') + ')') + '.', m('π(' + c + I('t') + ')<sup>2</sup> = π · ' + (c * c) + I('t') + '<sup>2</sup>') + ': square both the ' + c + ' and the ' + I('t') + '.', 'So the area is ' + ch(c * c, 2) + ' square inches, written in terms of time.'] }), { kind: 'ripple', c: c });
      }
    ]
  ];
  K.lesson('2.8', { title: 'Function Operations and Composition', std: 'Lial 12e · Section 2.8', levels: c28 });

  K.review('2', 'Chapter 2 Review: Graphs and Functions');
})(typeof window !== 'undefined' ? window.KCEP : globalThis.KCEP);
