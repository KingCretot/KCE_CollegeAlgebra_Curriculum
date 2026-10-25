/* KCE College Algebra — Chapter 3: Polynomial and Rational Functions
   Lial, Essentials of College Algebra 12e, Sections 3.1–3.6.
   Every generator randomizes its numbers. Each question also carries o.p (raw parameters)
   so verify-c3.js can check the math independently. */
(function (K) {
  var ri = K.ri, rnz = K.rnz, pick = K.pick, n = K.n, P = K.poly, Q = K.Q, mc = K.mc, M = K.MINUS, m = K.m, fr = K.frx, R = K.R, COL = K.COL;
  var FX = '<i>f</i>(<i>x</i>)', IX = '<i>x</i>', IY = '<i>y</i>', II = '<i>i</i>';
  function QP(o, p) { var q = Q(o); q.p = p; return q; }
  // math that may wrap between top-level terms or factors (never inside parentheses or a fraction)
  function brk(s) {
    var chunks = [], seps = [], cur = '', dp = 0, ds = 0, i = 0;
    while (i < s.length) {
      if (s.substr(i, 5) === '<span') ds++; else if (s.substr(i, 6) === '</span') ds--;
      var ch = s.charAt(i), op = s.substr(i, 3);
      if (dp === 0 && ds === 0 && cur.trim() && (op === ' + ' || op === ' ' + M + ' ' || op === ' = ' || op === ' ÷ ')) { chunks.push(cur.trim()); seps.push(' '); cur = ''; }
      if (ch === '(') dp++; else if (ch === ')') dp--;
      cur += ch; i++;
      if (dp === 0 && ds === 0 && ch === ')' && s.charAt(i) === '(') { chunks.push(cur.trim()); seps.push('<wbr>'); cur = ''; }
    }
    if (cur.trim()) chunks.push(cur.trim());
    return chunks.map(function (c, j) { return (j ? seps[j - 1] : '') + m(c); }).join('');
  }
  function fx(s) { return m(FX + ' =') + ' ' + brk(s); }
  function xe(v) { return m(IX + ' = ' + R(v).html()); }
  function ye(v) { return m(IY + ' = ' + R(v).html()); }
  function rh(v) { return R(v).html(); }
  function sub(v) { return v < 0 ? '(' + n(v) + ')' : n(v); }
  function sq(s) { return s + '<sup>2</sup>'; }
  function pd(c, v) { var d = c.length - 1; return P(c.map(function (t, i) { return [t, K.xp(d - i, v)]; })); }
  function pmul(a, b) { var r = []; for (var i = 0; i < a.length + b.length - 1; i++) r.push(0); a.forEach(function (x, i) { b.forEach(function (y, j) { r[i + j] += x * y; }); }); return r; }
  function fromRoots(rs, lead0) { var c = [lead0 === undefined ? 1 : lead0]; rs.forEach(function (r) { c = pmul(c, [1, -r]); }); return c; }
  function peval(c, x) { return c.reduce(function (s, t) { return s * x + t; }, 0); }
  function pfn(c) { return function (x) { return peval(c, x); }; }
  function synth(c, k) { var b = [c[0]], mids = []; for (var i = 1; i < c.length; i++) { mids.push(b[i - 1] * k); b.push(c[i] + b[i - 1] * k); } return { q: b.slice(0, -1), r: b[b.length - 1], mids: mids, bottom: b }; }
  function sv(c, x) { var d = c.length - 1; return K.subst(c.map(function (t, i) { return [t, d - i]; }), n(x)); }
  function lead(a) { a = R(a); return a.eq(1) ? '' : a.eq(-1) ? M : a.html(); }
  function dv(k) { return K.minusH(IX, k); }
  function fac(r, p) { var s = r === 0 ? IX : '(' + dv(r) + ')'; return p > 1 ? s + '<sup>' + p + '</sup>' : s; }
  function lin(a, b) { return '(' + P([[a, IX], [b, '']]) + ')'; }
  function vform(a, h, k) { var co = lead(a); return (h === 0 ? co + sq(IX) : co + sq('(' + dv(h) + ')')) + K.plusK(k); }
  function list(arr) { return arr.length === 1 ? arr[0] : arr.length === 2 ? arr[0] + ' and ' + arr[1] : arr.slice(0, -1).join(', ') + ', and ' + arr[arr.length - 1]; }
  function sortV(arr) { return arr.slice().sort(function (p, q) { return R(p).val() - R(q).val(); }); }
  function tail(terms) { var s = P(terms); if (s === '0') return ''; return s.charAt(0) === M ? ' ' + M + ' ' + s.slice(1) : ' + ' + s; }
  function money(v) { return (v < 0 ? M : '') + '$' + K.comma(Math.abs(v)); }
  function ep(v) { return v === Infinity ? '∞' : v === -Infinity ? M + '∞' : rh(v); }
  function iv(a, b, cl) { return (cl && isFinite(a) ? '[' : '(') + ep(a) + ', ' + ep(b) + (cl && isFinite(b) ? ']' : ')'); }
  function divisors(v) { v = Math.abs(v); var d = []; for (var i = 1; i <= v; i++) if (v % i === 0) d.push(i); return d; }
  function signs(c) { return c.filter(function (v) { return v !== 0; }).map(function (v) { return v > 0 ? '+' : M; }); }
  function changes(c) { var s = c.filter(function (v) { return v !== 0; }), k = 0; for (var i = 1; i < s.length; i++) if ((s[i] > 0) !== (s[i - 1] > 0)) k++; return k; }
  // degree of gcd(a, b) for integer coefficient lists (highest power first); > 0 means a common factor
  function gcdDeg(a, b) {
    var cl = function (p) { p = p.map(function (v) { return R(v); }); while (p.length && p[0].n === 0) p.shift(); return p; };
    a = cl(a); b = cl(b);
    while (b.length) {
      var r = a.slice();
      while (r.length >= b.length) { var f = r[0].div(b[0]); for (var i = 0; i < b.length; i++) r[i] = r[i].sub(f.mul(b[i])); r.shift(); while (r.length && r[0].n === 0) r.shift(); }
      a = b; b = r;
    }
    return a.length - 1;
  }
  function negX(c) { var d = c.length - 1; return c.map(function (v, i) { return (d - i) % 2 ? -v : v; }); }
  /* ---- shared text helpers (added in review fixes) ---- */
  // a = b = c chain that drops a step identical to the one before it (no "1/2 = 1/2")
  function eqs() { var a = [].slice.call(arguments), out = [a[0]]; for (var i = 1; i < a.length; i++) if (K.plain(a[i]) !== K.plain(out[out.length - 1])) out.push(a[i]); return out.join(' = '); }
  // quotient of two integers as shown in a step: never a negative denominator under a fraction bar
  function frq(a, b) { return b < 0 ? n(a) + ' ÷ (' + n(b) + ')' : K.frx(n(a), n(b)); }
  // indefinite article for a number that follows it ("an 8-mile", "an 11-mile", "a 12-mile")
  function art(v) { var s = String(v).replace(/[^0-9]/g, ''); return /^8/.test(s) || (/^1[18]/.test(s) && s.length % 3 === 2) ? 'an' : 'a'; }
  // count + noun with the right number ("1 year", "3 years")
  function cnt(v, one, many) { return n(v) + ' ' + (Math.abs(v) === 1 ? one : (many || one + 's')); }
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

  // multiple choice for expression answers: [html, fn] pairs; drops wrong choices numerically equal to another choice
  var TP = [-4.37, -2.71, -1.29, -0.43, 0.61, 1.57, 2.33, 3.83, 5.17];
  function same(f, g) { return TP.every(function (t) { var a = f(t), b = g(t); if (!isFinite(a) || !isFinite(b)) return !isFinite(a) && !isFinite(b); return Math.abs(a - b) <= 1e-7 * (1 + Math.abs(a)); }); }
  function mcF(cor, wrongs, extra) {
    var keep = [], all = [cor];
    var add = function (w) { if (w && all.every(function (k) { return !same(k[1], w[1]) && K.strip(k[0]) !== K.strip(w[0]); })) { keep.push(w); all.push(w); } };
    wrongs.forEach(add);
    for (var i = 1; keep.length < 3 && extra && i < 80; i++) add(extra(i));
    return mc(cor[0], keep.slice(0, 3).map(function (w) { return w[0]; }));
  }

  // synthetic division display
  function synTable(k, top, s) {
    var b = 'border:none;padding:4px 7px;text-align:right;background:#fff;color:#1a1a1a;';
    var kc = b + 'border-right:2px solid #0A1F3D;font-weight:700;color:#0047BA;';
    var r1 = '<tr><td style="' + kc + '">' + n(k) + '</td>' + top.map(function (v) { return '<td style="' + b + '">' + n(v) + '</td>'; }).join('') + '</tr>';
    var r2 = '<tr><td style="' + kc + '"></td><td style="' + b + '"></td>' + s.mids.map(function (v) { return '<td style="' + b + '">' + n(v) + '</td>'; }).join('') + '</tr>';
    var r3 = '<tr><td style="' + kc + '"></td>' + s.bottom.map(function (v, i) { var last = i === s.bottom.length - 1; return '<td style="' + b + 'border-top:2px solid #0A1F3D;font-weight:700;' + (last ? 'border-left:2px solid #DB2F30;color:#DB2F30;' : '') + '">' + n(v) + '</td>'; }).join('') + '</tr>';
    return '<table class="qt" style="border-collapse:collapse;margin:8px auto 12px;border:none;">' + r1 + r2 + r3 + '</table>';
  }

  /* ---------- graphs ---------- */
  function parab(a, h, k, extra) {
    var av = (a instanceof K.Rclass) ? a.val() : a, x0 = h - 6, x1 = h + 6;
    if (x0 > -2) { x0 = -2; x1 = 10; } if (x1 < 2) { x0 = -10; x1 = 2; }
    var y0 = av > 0 ? Math.min(k - 2, -2) : Math.min(k - 10, -3), y1 = av > 0 ? Math.max(k + 10, 3) : Math.max(k + 2, 2);
    var o = { x: [x0, x1], y: [y0, y1], h: Math.round(Math.min(430, 24 * (y1 - y0) + 60)), fns: [{ f: function (x) { return av * (x - h) * (x - h) + k; } }] };
    for (var t in extra) o[t] = extra[t];
    // labels go outside the parabola: below the vertex when it opens up, above when it opens down,
    // on the side away from the y-axis; other points are labeled on their outer side
    (o.pts || []).forEach(function (P) {
      if (!P.label) return;
      var v = av > 0 ? 's' : 'n', side = P.x === h ? (h >= 0 ? 'e' : 'w') : (P.x > h ? 'e' : 'w');
      P.pref = P.x === h ? [v + side, v + (side === 'e' ? 'w' : 'e')] : [v + side, side, v + (side === 'e' ? 'w' : 'e')];
    });
    return K.plane(place(o));
  }
  function ratGraph(f, vas, ha, o) {
    var x0 = o.x[0], x1 = o.x[1], cuts = [x0].concat(vas.slice().sort(function (a, b) { return a - b; })).concat([x1]), fns = [];
    for (var i = 0; i < cuts.length - 1; i++) fns.push({ f: f, from: cuts[i] + (i ? 0.004 : 0), to: cuts[i + 1] - (i < cuts.length - 2 ? 0.004 : 0) });
    var lines = vas.map(function (v) { return { vx: v, dash: true, color: COL.red }; });
    if (ha !== null && ha !== undefined) lines.push({ m: 0, b: ha, dash: true, color: COL.red });
    (o.pts || []).forEach(function (P) {
      if (!P.label) return;
      var e = vas.length && P.x < vas[0] ? 'w' : 'e', v = ha !== null && ha !== undefined && P.y < ha ? 's' : 'n';
      P.pref = [v + e, (v === 'n' ? 's' : 'n') + e, v + (e === 'e' ? 'w' : 'e')];
    });
    return K.plane(place({ x: o.x, y: o.y, fns: fns, lines: lines, pts: o.pts || [], h: o.h || 340 }));
  }
  var BEH = { uu: 'Rises on both ends', dd: 'Falls on both ends', du: 'Falls to the left, rises to the right', ud: 'Rises to the left, falls to the right' };
  function beh(deg, s) { return deg % 2 === 0 ? (s > 0 ? BEH.uu : BEH.dd) : (s > 0 ? BEH.du : BEH.ud); }

  /* ================= 3.1 Quadratic Functions and Models ================= */
  var A = [-3, -2, -1, 1, 2, 3];
  var c31 = [
    [
      function () {
        var a = pick([1, -1, 2, -2, 3, -3, R(1, 2), R(-1, 2)]), h = rnz(-7, 7), k = rnz(-9, 9), f = vform(a, h, k);
        return QP({ q: 'What is the vertex of the parabola ' + fx(f) + '?', mc: mc(K.pt(h, k), [K.pt(-h, k), K.pt(h, -k), K.pt(k, h)], function () { return K.pt(h + rnz(-3, 3), k + ri(-2, 2)); }),
          why: ['Vertex form is ' + m(FX + ' = <i>a</i>(<i>x</i> ' + M + ' <i>h</i>)<sup>2</sup> + <i>k</i>') + ', with vertex ' + m('(<i>h</i>, <i>k</i>)') + '.',
            m('(' + dv(h) + ')') + ' means ' + m('<i>h</i> = ' + n(h)) + (h < 0 ? ', since ' + m(dv(h) + ' = <i>x</i> ' + M + ' (' + n(h) + ')') : '') + ', and ' + m('<i>k</i> = ' + n(k)) + '.',
            'The vertex is ' + K.pt(h, k) + '.'] }, { t: 'vertex', f: f });
      },
      function () {
        var a = pick([1, -1, 2, -2, R(1, 2), R(-1, 2)]), h = rnz(-4, 4), k = rnz(-5, 5); if (h === k) k = -k;
        var av = R(a).val(), up = av > 0, fn = function (x) { return av * (x - h) * (x - h) + k; };
        var rg = function (v, u) { return m(u ? iv(v, Infinity, true) : iv(-Infinity, v, true)); };
        return QP({ q: 'The graph of a quadratic function <i>f</i> is shown, with its vertex marked. What is the range of <i>f</i> in interval notation?', graph: parab(av, h, k, { pts: [{ x: h, y: k, label: '(' + h + ', ' + k + ')' }] }),
          mc: mc(rg(k, up), [rg(k, !up), rg(h, up), m(iv(-Infinity, Infinity))]),
          why: ['The vertex ' + K.pt(h, k) + ' is the ' + (up ? 'lowest' : 'highest') + ' point, because the parabola opens ' + (up ? 'up' : 'down') + '.', 'So every <i>y</i>-value is ' + (up ? 'at least ' : 'at most ') + n(k) + ', and ' + n(k) + ' itself is reached at the vertex.', 'Range: ' + rg(k, up) + '. (The range uses the <i>y</i>-value of the vertex, not the <i>x</i>-value.)'] }, { t: 'range', fn: fn });
      },
      function () {
        var a = pick([1, -1, 2, -2, 3, -3, R(1, 2), R(-1, 2), R(1, 3), R(-1, 3)]), h = rnz(-6, 6), k = rnz(-9, 9); if (h === k) k = -k;
        var up = R(a).val() > 0, ext = up ? 'minimum' : 'maximum', dir = up ? 'up' : 'down', f = vform(a, h, k);
        return QP({ q: 'Which statement about ' + fx(f) + ' is true?', mc: mc('Opens ' + dir + '; ' + ext + ' value ' + n(k), ['Opens ' + (up ? 'down' : 'up') + '; ' + (up ? 'maximum' : 'minimum') + ' value ' + n(k), 'Opens ' + dir + '; ' + ext + ' value ' + n(h), 'Opens ' + dir + '; ' + (up ? 'maximum' : 'minimum') + ' value ' + n(k)]),
          why: [m('<i>a</i> = ' + rh(a)) + (up ? ' &gt; 0, so the parabola opens up and the vertex is its lowest point (a minimum).' : ' &lt; 0, so the parabola opens down and the vertex is its highest point (a maximum).'), 'The vertex is ' + K.pt(h, k) + '. The ' + ext + ' value is the <i>y</i>-coordinate, ' + n(k) + '.'] }, { t: 'openExt', f: f });
      }
    ],
    [
      function () {
        var a = pick(A), h = rnz(-5, 5), k = ri(-9, 9), b = -2 * a * h, c = a * h * h + k, cf = [a, b, c], f = pd(cf), fv = pfn(cf);
        return QP({ q: 'Use the vertex formula to find the vertex of ' + fx(f) + '.', mc: mc(K.pt(h, k), [K.pt(-h, fv(-h)), K.pt(2 * h, fv(2 * h)), K.pt(h, c)], function () { return K.pt(h, k + rnz(-4, 4)); }),
          why: [m(IX + ' = ' + fr(M + '<i>b</i>', '2<i>a</i>') + ' = ' + fr(M + '(' + n(b) + ')', '2(' + n(a) + ')') + ' = ' + n(h)) + '.', m('<i>f</i>(' + n(h) + ') = ' + sv(cf, h) + ' = ' + n(k)) + '.', 'The vertex is ' + K.pt(h, k) + '. (The vertex formula gives only the <i>x</i>-coordinate; you must substitute to get <i>y</i>.)'] }, { t: 'vertex', f: f });
      },
      function () {
        var a = pick([1, 1, 2, -1, 3, -2]), h = rnz(-6, 6), k = ri(-9, 9), b = -2 * a * h, c = a * h * h + k, cf = [a, b, c];
        var w = [fx(vform(a, -h, k)), fx(vform(a, h, a === 1 ? c + h * h : c - h * h)), fx(vform(a, h, c))];
        var steps = [];
        if (a !== 1) steps.push('Factor ' + n(a) + ' out of the <i>x</i>-terms: ' + fx(lead(a) + '(' + pd([1, -2 * h, 0]) + ')' + K.plusK(c)) + '.');
        steps.push('Half of ' + n(-2 * h) + ' is ' + n(-h) + ', and ' + sub(-h) + '<sup>2</sup> = ' + n(h * h) + '. Add and subtract it inside: ' + fx(lead(a) + '(' + pd([1, -2 * h, h * h]) + ' ' + M + ' ' + n(h * h) + ')' + K.plusK(c)) + '.');
        steps.push('Factor the trinomial' + (a !== 1 ? ' and multiply ' + n(a) + ' · ' + sub(-h * h) + ' = ' + n(-a * h * h) : '') + ': ' + fx(eqs(vform(a, h, 0) + K.plusK(-a * h * h) + K.plusK(c), vform(a, h, k))) + '.');
        return QP({ q: 'Complete the square to write ' + fx(pd(cf)) + ' in vertex form.', mc: mc(fx(vform(a, h, k)), w, function () { return fx(vform(a, h, k + rnz(-3, 3))); }), why: steps }, { t: 'eqexpr', f: pd(cf) });
      },
      function () {
        var a = pick(A), h = rnz(-5, 5), k = rnz(-9, 9); if (h === k) k = -k;
        var b = -2 * a * h, c = a * h * h + k, cf = [a, b, c], up = a > 0;
        var rg = function (v, u) { return m(u ? iv(v, Infinity, true) : iv(-Infinity, v, true)); };
        return QP({ q: 'What is the range of ' + fx(pd(cf)) + '? Write it in interval notation.', mc: mc(rg(k, up), [rg(k, !up), rg(h, up), m(iv(-Infinity, Infinity))]),
          why: ['Vertex: ' + m(IX + ' = ' + fr(M + '(' + n(b) + ')', '2(' + n(a) + ')') + ' = ' + n(h)) + ', and ' + m('<i>f</i>(' + n(h) + ') = ' + n(k)) + '.', m('<i>a</i> = ' + n(a)) + (up ? ' &gt; 0, so the parabola opens up and ' + n(k) + ' is the minimum value.' : ' &lt; 0, so the parabola opens down and ' + n(k) + ' is the maximum value.'), 'Range: ' + rg(k, up) + '.'] }, { t: 'rangeP', f: pd(cf) });
      },
      function () {
        var a = pick([1, -1, 2, -2]), h = rnz(-4, 4), k = rnz(-5, 5);
        var fn = function (x) { return a * (x - h) * (x - h) + k; };
        var cor = [fx(vform(a, h, k)), fn];
        var sd = h < 0 ? -1 : 1; // mark the second point on the side away from the y-axis, where its label has room
        var wr = [[fx(vform(a, -h, k)), function (x) { return a * (x + h) * (x + h) + k; }], [fx(vform(-a, h, k)), function (x) { return -a * (x - h) * (x - h) + k; }], [fx(vform(a, h, -k)), function (x) { return a * (x - h) * (x - h) - k; }]];
        return QP({ q: 'Which function is graphed below? The vertex and one other point are marked.', graph: parab(a, h, k, { pts: [{ x: h, y: k, label: '(' + h + ', ' + k + ')' }, { x: h + sd, y: k + a, label: '(' + (h + sd) + ', ' + (k + a) + ')' }] }), mc: mcF(cor, wr),
          why: ['The vertex is ' + K.pt(h, k) + ', so ' + fx('<i>a</i>' + sq('(' + dv(h) + ')') + K.plusK(k)) + '.', 'One unit to the ' + (sd > 0 ? 'right' : 'left') + ' of the vertex, the graph is at ' + n(k + a) + ', which is ' + n(Math.abs(a)) + (a > 0 ? ' above' : ' below') + ' the vertex, so ' + m('<i>a</i> = ' + n(a)) + '.', 'So ' + fx(vform(a, h, k)) + '.'] }, { t: 'graph', fn: fn });
      }
    ],
    [
      function () {
        var j = ri(1, 4), s0 = pick([4, 5, 6, 8, 10, 12, 20, 32, 48]), v0 = 32 * j, H = 16 * j * j + s0;
        var sx = P([[-16, K.xp(2, 't')], [v0, '<i>t</i>'], [s0, '']]);
        var ans = function (t, h) { return 'After ' + n(t) + (t === 1 ? ' second' : ' seconds') + '; ' + K.comma(h) + ' feet'; };
        return QP({ q: 'A ball is thrown upward from ' + art(s0) + ' ' + s0 + '-foot platform. Its height in feet after <i>t</i> seconds is ' + m('<i>s</i>(<i>t</i>) = ' + sx) + '. When does the ball reach its maximum height, and what is that height?',
          mc: mc(ans(j, H), [ans(2 * j, s0), ans(j, 16 * j * j), ans(j, 48 * j * j + s0)]),
          why: ['Since ' + m('<i>a</i> = ' + M + '16 &lt; 0') + ', the vertex is the highest point.', m('<i>t</i> = ' + fr(M + '<i>b</i>', '2<i>a</i>') + ' = ' + fr(M + v0, '2(' + M + '16)') + ' = ' + n(j)) + (j === 1 ? ' second.' : ' seconds.'), m('<i>s</i>(' + n(j) + ') = ' + M + '16(' + n(j) + ')<sup>2</sup> + ' + v0 + '(' + n(j) + ') + ' + s0 + ' = ' + K.comma(H)) + ' feet.'] }, { t: 'proj', f: sx });
      },
      function () {
        var mm = ri(1, 5), Pf = 24 * mm, river = K.coin(), vals = [72, 36, 64, 144].map(function (v) { return v * mm * mm; });
        var fmt = function (v) { return K.comma(v) + ' square feet'; };
        var cor = river ? vals[0] : vals[1], wr = (river ? [vals[1], vals[2], vals[3]] : [vals[0], vals[2], vals[3]]).map(fmt);
        var q = river ? 'A farmer has ' + Pf + ' feet of fencing to enclose a rectangular pen along a straight river. No fence is needed along the river. What is the largest area the pen can have?' : 'A gardener has ' + Pf + ' feet of fencing to enclose a rectangular garden on all four sides. What is the largest area the garden can have?';
        var why = river ? ['Let <i>x</i> be each side perpendicular to the river. The side parallel to the river is ' + m(Pf + ' ' + M + ' 2<i>x</i>') + ', so ' + m('<i>A</i>(<i>x</i>) = <i>x</i>(' + Pf + ' ' + M + ' 2<i>x</i>) = ' + M + '2<i>x</i><sup>2</sup> + ' + Pf + '<i>x</i>') + '.', 'Vertex: ' + m(IX + ' = ' + fr(M + Pf, '2(' + M + '2)') + ' = ' + n(6 * mm)) + ' feet, so the parallel side is ' + n(12 * mm) + ' feet.', 'Largest area: ' + m(n(6 * mm) + ' · ' + n(12 * mm) + ' = ' + K.comma(vals[0])) + ' square feet.']
          : ['Length plus width is half the perimeter: ' + n(12 * mm) + ' feet. So ' + m('<i>A</i>(<i>x</i>) = <i>x</i>(' + n(12 * mm) + ' ' + M + ' <i>x</i>) = ' + M + '<i>x</i><sup>2</sup> + ' + n(12 * mm) + '<i>x</i>') + '.', 'Vertex: ' + m(IX + ' = ' + fr(M + n(12 * mm), '2(' + M + '1)') + ' = ' + n(6 * mm)) + ', so the garden is ' + art(6 * mm) + ' ' + n(6 * mm) + ' by ' + n(6 * mm) + ' square.', 'Largest area: ' + m(n(6 * mm) + ' · ' + n(6 * mm) + ' = ' + K.comma(vals[1])) + ' square feet.'];
        return QP({ q: q, mc: mc(fmt(cor), wr), why: why }, { t: 'fence', P: Pf, river: river });
      },
      function () {
        var a = pick([1, 2]), h = 5 * ri(2, 12), b = 2 * a * h, mx = a * h * h, c = 50 * ri(1, Math.floor((mx - 50) / 50)), best = mx - c;
        var px = pd([-a, b, -c]);
        var ans = function (t, v) { return n(t) + ' items; ' + money(v); };
        return QP({ q: 'A company’s weekly profit, in dollars, from selling <i>x</i> items is ' + m('<i>P</i>(<i>x</i>) = ' + px) + '. How many items give the maximum profit, and what is that profit?',
          mc: mc(ans(h, best), [ans(2 * h, -c), ans(h, mx), ans(h, mx + c)]),
          why: [m('<i>a</i> = ' + n(-a) + ' &lt; 0') + ', so the vertex is a maximum.', m(IX + ' = ' + fr(M + '<i>b</i>', '2<i>a</i>') + ' = ' + fr(M + b, '2(' + n(-a) + ')') + ' = ' + n(h)) + ' items.', m('<i>P</i>(' + n(h) + ') =') + ' ' + brk(sv([-a, b, -c], h) + ' = ' + K.comma(best)) + ', so the maximum profit is ' + money(best) + '.'] }, { t: 'profit', f: px });
      },
      function () {
        var h, k, d, a, x1, y1;
        do { h = rnz(-4, 4); k = rnz(-6, 6); d = pick([-3, -2, -1, 1, 2, 3]); a = R(pick([1, -1, 2, -2, 3, -3, R(1, 2), R(-1, 2), R(1, 4), R(-1, 4)])); } while (!a.mul(d * d).isInt());
        x1 = h + d; y1 = k + a.mul(d * d).val();
        var wr = [R(y1 - k, d)]; if (x1 + h !== 0) wr.push(R(y1 - k, (x1 + h) * (x1 + h))); wr.push(R(y1 + k, d * d)); wr.push(a.neg());
        return QP({ q: 'A parabola has vertex ' + K.pt(h, k) + ' and passes through ' + K.pt(x1, y1) + '. Its equation is ' + fx('<i>a</i>(<i>x</i> ' + M + ' <i>h</i>)<sup>2</sup> + <i>k</i>') + '. What is <i>a</i>?',
          mc: mc(a.html(), wr.map(function (v) { return v.html(); }), function (i) { return a.add(R(i % 2 ? i : -i, 2)).html(); }),
          why: ['Use the vertex: ' + fx('<i>a</i>' + sq('(' + dv(h) + ')') + K.plusK(k)) + '.', 'Substitute the point ' + K.pt(x1, y1) + ': ' + m(n(y1) + ' = <i>a</i>(' + n(x1) + (h < 0 ? ' + ' + n(-h) : ' ' + M + ' ' + n(h)) + ')<sup>2</sup>' + K.plusK(k)) + ', so ' + m(n(y1 - k) + ' = ' + (d * d === 1 ? '' : n(d * d)) + '<i>a</i>') + '.', d * d === 1 ? 'So ' + m('<i>a</i> = ' + a.html()) + '.' : m('<i>a</i> = ' + eqs(frq(y1 - k, d * d), a.html())) + '.'] }, { t: 'findA', h: h, k: k, x1: x1, y1: y1 });
      }
    ]
  ];
  K.lesson('3.1', { title: 'Quadratic Functions and Models', std: 'Lial 12e · Section 3.1', levels: c31 });

  /* ================= 3.2 Synthetic Division ================= */
  function randPoly(deg, withZero) {
    var c = [pick([1, 1, 2, 3, -1, -2])];
    for (var i = 1; i <= deg; i++) c.push(rnz(-6, 6));
    if (withZero) c[ri(1, deg - 1)] = 0;
    return c;
  }
  function qr(qc, r, k) { return r === 0 ? pd(qc) : pd(qc) + (r > 0 ? ' + ' : ' ' + M + ' ') + fr(n(Math.abs(r)), dv(k)); }
  function qrFn(qc, r, k) { return function (x) { return peval(qc, x) + r / (x - k); }; }
  function setup(k, c) { return m('<b>' + n(k) + '</b>') + ' in the box; coefficients ' + m(c.map(n).join(', ')); }
  var c32 = [
    [
      function () {
        var c = [pick([1, 2, -1, 3]), ri(-6, 6), ri(-9, 9), rnz(-9, 9)], k = rnz(-3, 3), r = peval(c, k), s = synth(c, k);
        return QP({ q: 'What is the remainder when ' + fx(pd(c)) + ' is divided by ' + m(dv(k)) + '?', mc: mc(n(r), [n(peval(c, -k)), n(peval(c, 1)), n(c[3])], function () { return n(r + rnz(-6, 6)); }),
          why: ['By the remainder theorem, the remainder is ' + m('<i>f</i>(<i>k</i>)') + ' when dividing by ' + m('<i>x</i> ' + M + ' <i>k</i>') + '. ' + (k < 0 ? 'Since ' + m(dv(k) + ' = <i>x</i> ' + M + ' (' + n(k) + ')') + ', ' : 'Here ') + m('<i>k</i> = ' + n(k)) + '.', m('<i>f</i>(' + n(k) + ') =') + ' ' + brk(eqs(sv(c, k), n(r))) + '.', 'Synthetic division agrees: the last number in the bottom row is ' + n(r) + '.' + synTable(k, c, s)] }, { t: 'rem', f: pd(c), k: k });
      },
      function () {
        var deg = pick([3, 3, 4]), c = randPoly(deg, K.coin()), k = rnz(-3, 3), s = synth(c, k);
        var ans = function (qc, r) { return 'Quotient ' + brk(pd(qc)) + '; remainder ' + m(n(r)); };
        var wr = [ans(s.q.concat([0]), s.r), ans(s.bottom, 0)]; if (s.r !== 0) wr.push(ans(s.q, -s.r));
        return QP({ q: 'The synthetic division below divides ' + m(pd(c)) + ' by ' + m(dv(k)) + '. What are the quotient and the remainder?' + synTable(k, c, s),
          mc: mc(ans(s.q, s.r), wr, function (i) { var q2 = s.q.slice(); q2[q2.length - 1] += (i % 2 ? i : -i); return ans(q2, s.r); }),
          why: ['The last number in the bottom row is the remainder: ' + n(s.r) + '.', 'The other numbers ' + s.q.map(n).join(', ') + ' are the quotient’s coefficients. The quotient starts one degree lower than the dividend, at ' + m(K.xp(deg - 1) || '1') + '.', 'Quotient ' + m(pd(s.q)) + ', remainder ' + n(s.r) + '.'] }, { t: 'qr', f: pd(c), k: k });
      },
      function () {
        var deg = pick([3, 4]), c = randPoly(deg, true), k = rnz(-5, 5), nz = c.filter(function (v) { return v !== 0; });
        var zp = 0; c.forEach(function (v, i) { if (v === 0) zp = deg - i; });
        return QP({ q: 'You want to divide ' + m(pd(c)) + ' by ' + m(dv(k)) + ' with synthetic division. Which setup is correct?', mc: mc(setup(k, c), [setup(-k, c), setup(k, nz), setup(-k, nz)]),
          why: ['The number in the box makes the divisor 0: ' + m(dv(k) + ' = 0') + ' gives ' + m(IX + ' = ' + n(k)) + '.', 'List every coefficient from the highest power down, writing 0 for the missing ' + m(K.xp(zp)) + ' term: ' + c.map(n).join(', ') + '.'] }, { t: 'setup', f: pd(c), k: k });
      }
    ],
    [
      function () {
        var deg, c, k, s;
        do { deg = pick([3, 4]); c = randPoly(deg, true); k = rnz(-3, 3); s = synth(c, k); } while (s.r === 0);
        var nz = c.filter(function (v) { return v !== 0; }), s2 = synth(c, -k), s3 = synth(nz, k);
        var cor = [brk(qr(s.q, s.r, k)), qrFn(s.q, s.r, k)];
        var wr = [[brk(qr(s2.q, s2.r, k)), qrFn(s2.q, s2.r, k)], [brk(qr(s3.q, s3.r, k)), qrFn(s3.q, s3.r, k)], [brk(qr(s.q.concat([0]), s.r, k)), qrFn(s.q.concat([0]), s.r, k)]];
        return QP({ q: 'Use synthetic division to divide: ' + m('(' + pd(c) + ') ÷ (' + dv(k) + ')') + '.', mc: mcF(cor, wr, function (i) { var q2 = s.q.slice(); q2[0] += (i % 2 ? i : -i); return [brk(qr(q2, s.r, k)), qrFn(q2, s.r, k)]; }),
          why: ['Use ' + m('<i>k</i> = ' + n(k)) + ' and the coefficients ' + c.map(n).join(', ') + ' (0 holds the place of the missing term).' + synTable(k, c, s), 'The bottom row gives quotient ' + m(pd(s.q)) + ' and remainder ' + n(s.r) + '.', 'Answer: ' + brk(qr(s.q, s.r, k)) + '.'] }, { t: 'divexpr', f: pd(c), k: k });
      },
      function () {
        var c = randPoly(4, true), k = pick([-3, -2, -1, 2, 3]), s = synth(c, k), nz = c.filter(function (v) { return v !== 0; });
        return QP({ q: 'Use synthetic division and the remainder theorem to find ' + m('<i>f</i>(' + n(k) + ')') + ' for ' + fx(pd(c)) + '.', mc: mc(n(s.r), [n(synth(nz, k).r), n(peval(c, -k)), n(s.q[s.q.length - 1])], function () { return n(s.r + rnz(-9, 9)); }),
          why: ['Divide by ' + m(dv(k)) + ' using coefficients ' + c.map(n).join(', ') + '. Do not skip the 0.' + synTable(k, c, s), 'The remainder is ' + n(s.r) + ', so by the remainder theorem ' + m('<i>f</i>(' + n(k) + ') = ' + n(s.r)) + '.'] }, { t: 'fk', f: pd(c), k: k });
      },
      function () {
        var k, pp, qq, c;
        do { k = rnz(-5, 5); pp = ri(-5, 5); qq = rnz(-6, 6); } while (Math.sqrt(Math.max(0, pp * pp - 4 * qq)) % 1 === 0 && pp * pp - 4 * qq >= 0);
        c = pmul([1, -k], [1, pp, qq]);
        var cands = []; divisors(c[3]).forEach(function (d) { [d, -d].forEach(function (v) { if (v !== k && peval(c, v) !== 0) cands.push(v); }); });
        var wr = []; if (cands.indexOf(-k) >= 0) wr.push(-k); K.shuffle(cands).forEach(function (v) { if (wr.indexOf(v) < 0) wr.push(v); });
        var s = synth(c, k);
        return QP({ q: 'Which number is a zero of ' + fx(pd(c)) + '?', mc: mc(n(k), wr.slice(0, 3).map(n), function (i) { var v = k + 6 + i; return peval(c, v) !== 0 ? n(v) : n(k + 20 + i); }),
          why: ['A number <i>k</i> is a zero exactly when dividing by ' + m('<i>x</i> ' + M + ' <i>k</i>') + ' leaves remainder 0.', 'With ' + m('<i>k</i> = ' + n(k)) + ', the remainder is 0:' + synTable(k, c, s), 'So ' + m('<i>f</i>(' + n(k) + ') = 0') + ' and ' + n(k) + ' is a zero. ' + (wr.length ? 'For example, ' + m('<i>f</i>(' + n(wr[0]) + ') = ' + n(peval(c, wr[0]))) + ', not 0.' : '')] }, { t: 'zeroOf', f: pd(c) });
      }
    ],
    [
      function () {
        var c1 = ri(-9, 9), c0 = ri(-9, 9), b = rnz(-6, 6), k = pick([-3, -2, 2, 3]), r = k * k * k + b * k * k + c1 * k + c0;
        var fs = '<i>x</i><sup>3</sup> + <i>bx</i><sup>2</sup>' + tail([[c1, IX], [c0, '']]);
        var rest = k * k * k + c1 * k + c0, restN = -k * k * k - c1 * k + c0;
        return QP({ q: 'When ' + fx(fs) + ' is divided by ' + m(dv(k)) + ', the remainder is ' + n(r) + '. Find <i>b</i>.',
          mc: mc(n(b), [R(r - restN, k * k).html(), n(-b), R(r - rest, k).html()], function (i) { return n(b + (i % 2 ? i : -i)); }),
          why: ['By the remainder theorem, ' + m('<i>f</i>(' + n(k) + ') = ' + n(r)) + '.', m('(' + n(k) + ')<sup>3</sup> + <i>b</i>(' + n(k) + ')<sup>2</sup>' + (c1 ? (c1 < 0 ? ' ' + M + ' ' + n(-c1) : ' + ' + n(c1)) + '(' + n(k) + ')' : '') + K.plusK(c0) + ' = ' + n(r)) + ', which simplifies to ' + m(n(k * k) + '<i>b</i>' + K.plusK(rest) + ' = ' + n(r)) + '.', m(n(k * k) + '<i>b</i> = ' + n(r - rest)) + ', so ' + m('<i>b</i> = ' + n(b)) + '.'] }, { t: 'findB', k: k, r: r, c1: c1, c0: c0 });
      },
      function () {
        var a = pick([1, 2, 3]), r1, r2, s;
        do { r1 = rnz(-4, 4); r2 = rnz(-4, 4); s = rnz(-5, 5); } while (r1 === r2 || (a === 1 && (s === r1 || s === r2)) || (a > 1 && s % a === 0));
        var c = pmul(pmul([1, -r1], [1, -r2]), [a, -s]), sd = synth(c, r1);
        var f = function (x) { return peval(c, x); };
        var cor = [m(fac(r1) + fac(r2) + lin(a, -s)), f];
        var wr = [[m(fac(-r1) + fac(r2) + lin(a, -s)), function (x) { return (x + r1) * (x - r2) * (a * x - s); }], [m(fac(r1) + fac(-r2) + lin(a, s)), function (x) { return (x - r1) * (x + r2) * (a * x + s); }],
          a !== 1 ? [m(fac(r1) + fac(r2) + fac(s)), function (x) { return (x - r1) * (x - r2) * (x - s); }] : [m(fac(r1) + fac(r2) + lin(1, s)), function (x) { return (x - r1) * (x - r2) * (x + s); }]];
        return QP({ q: 'Given that ' + n(r1) + ' is a zero of ' + fx(pd(c)) + ', factor <i>f</i>(<i>x</i>) completely.', mc: mcF(cor, wr, function (i) { var t = s + i; return [m(fac(r1) + fac(r2) + lin(a, -t)), function (x) { return (x - r1) * (x - r2) * (a * x - t); }]; }),
          why: ['Divide by ' + m(dv(r1)) + ' using ' + m('<i>k</i> = ' + n(r1)) + ':' + synTable(r1, c, sd), 'Remainder 0 confirms the zero. The quotient is ' + m(pd(sd.q)) + '.', 'Factor the quotient: ' + m(pd(sd.q) + ' = ' + fac(r2) + lin(a, -s)) + '. So ' + fx(fac(r1) + fac(r2) + lin(a, -s)) + '.'] }, { t: 'eqexpr', f: pd(c) });
      },
      function () {
        var qc = [pick([1, 2, 3, -1, -2]), ri(-6, 6), ri(-6, 6)], k = rnz(-4, 4), r = rnz(-9, 9);
        var mk = function (kk, rr) { var f = pmul(qc, [1, -kk]); f[f.length - 1] += rr; return f; };
        var cor = mk(k, r);
        var cand = [mk(-k, r), mk(k, -r), mk(k, 0)].map(function (f) { return [fx(pd(f)), pfn(f)]; });
        return QP({ q: 'When a polynomial ' + m(FX) + ' is divided by ' + m(dv(k)) + ', the quotient is ' + m(pd(qc)) + ' and the remainder is ' + n(r) + '. What is ' + m(FX) + '?',
          mc: mcF([fx(pd(cor)), pfn(cor)], cand, function (i) { var f = mk(k, r + i); return [fx(pd(f)), pfn(f)]; }),
          why: ['Division algorithm: ' + m(FX + ' = (<i>x</i> ' + M + ' <i>k</i>) · <i>q</i>(<i>x</i>) + <i>r</i>') + '.', fx('(' + dv(k) + ')(' + pd(qc) + ')' + K.plusK(r)) + '.', 'Multiply and add the remainder: ' + fx(pd(cor)) + '.'] }, { t: 'divAlg', q: pd(qc), k: k, r: r });
      }
    ]
  ];
  K.lesson('3.2', { title: 'Synthetic Division', std: 'Lial 12e · Section 3.2', levels: c32 });

  /* ================= 3.3 Zeros of Polynomial Functions ================= */
  function cx(p, q) { var im = (Math.abs(q) === 1 ? '' : n(Math.abs(q))) + II; if (p === 0) return (q < 0 ? M : '') + im; return n(p) + (q < 0 ? ' ' + M + ' ' : ' + ') + im; }
  function pmS(p, body) { return (p === 0 ? '±' : n(p) + ' ± ') + body; }
  function possible(v) { var a = []; for (var t = v; t >= 0; t -= 2) a.push(t); return a; }
  function possStr(v) { var a = possible(v); return a.length === 1 ? 'Exactly ' + a[0] : a.length === 2 ? a[0] + ' or ' + a[1] : a.slice(0, -1).join(', ') + ', or ' + a[a.length - 1]; }
  function anyStr(arr) { return arr.length === 1 ? 'Exactly ' + arr[0] : arr.length === 2 ? arr[0] + ' or ' + arr[1] : arr.slice(0, -1).join(', ') + ', or ' + arr[arr.length - 1]; }
  function randSignPoly(deg) { var c = []; for (var i = 0; i <= deg; i++) c.push((K.coin() ? 1 : -1) * ri(1, 9)); for (var j = 1; j < deg; j++) if (ri(1, 5) === 1) c[j] = 0; return c; }
  var c33 = [
    [
      function () {
        var a = pick([2, 3, 4, 5, 6]), c0 = pick([1, 2, 3, 4, 5, 6, 8, 9, 10]) * pick([1, -1]), cf = [a, rnz(-7, 7), rnz(-9, 9), c0];
        var ps = divisors(c0), qs = divisors(a), mem = {}, members = [];
        ps.forEach(function (p) { qs.forEach(function (q) { [p, -p].forEach(function (pp) { var v = R(pp, q); if (!mem[v.toString()]) { mem[v.toString()] = 1; members.push(v); } }); }); });
        var non = [];
        qs.forEach(function (q) { ps.forEach(function (p) { [q, -q].forEach(function (qq) { var v = R(qq, p); if (!mem[v.toString()] && !non.some(function (u) { return u.eq(v); })) non.push(v); }); }); });
        if (!non.length) { var t = 0; while (non.length < 1 && t++ < 100) { var v = R(rnz(-12, 12), ri(1, 7)); if (!mem[v.toString()]) non.push(v); } }
        var ans = pick(non), wr = K.sample(members, 3);
        var why2 = !(Math.abs(c0) % Math.abs(ans.n) === 0) ? 'In lowest terms the answer is ' + m(ans.html()) + ', and its numerator ' + Math.abs(ans.n) + ' is not a factor of ' + n(c0) + '.' : 'In lowest terms the answer is ' + m(ans.html()) + ', and its denominator ' + ans.d + ' is not a factor of ' + a + '.';
        return QP({ q: 'By the rational zeros theorem, which number could NOT be a rational zero of ' + fx(pd(cf)) + '?', mc: mc(ans.html(), wr.map(function (v) { return v.html(); })),
          why: ['Every rational zero ' + m(fr('<i>p</i>', '<i>q</i>')) + ' has <i>p</i> a factor of the constant ' + n(c0) + ' (' + ps.map(function (v) { return '±' + v; }).join(', ') + ') and <i>q</i> a factor of the leading coefficient ' + a + ' (' + qs.map(function (v) { return '±' + v; }).join(', ') + ').', why2, 'Each other choice has the form (factor of ' + n(c0) + ')/(factor of ' + a + '), so it is on the list of candidates.'] }, { t: 'notCand', f: pd(cf) });
      },
      function () {
        var k, pp, qq, c;
        do { k = rnz(-4, 4); pp = ri(-4, 4); qq = rnz(-6, 6); } while (pp * pp - 4 * qq >= 0 && Math.sqrt(pp * pp - 4 * qq) % 1 === 0);
        c = pmul([1, -k], [1, pp, qq]);
        var vals = [-k]; divisors(c[3]).forEach(function (d) { [d, -d].forEach(function (v) { if (v !== k && vals.indexOf(v) < 0) vals.push(v); }); });
        vals = [vals[0]].concat(K.shuffle(vals.slice(1))).filter(function (v) { return peval(c, v) !== 0; });
        return QP({ q: 'Which binomial is a factor of ' + fx(pd(c)) + '?', mc: mc(m(dv(k)), vals.slice(0, 3).map(function (v) { return m(dv(v)); }), function (i) { return m(dv(k + 7 + i)); }),
          why: ['Factor theorem: ' + m('<i>x</i> ' + M + ' <i>k</i>') + ' is a factor exactly when ' + m('<i>f</i>(<i>k</i>) = 0') + '.', m('<i>f</i>(' + n(k) + ') =') + ' ' + brk(sv(c, k) + ' = 0') + ', so ' + m(dv(k)) + ' is a factor.', 'Watch the sign: ' + m(dv(-k)) + ' would need ' + m('<i>f</i>(' + n(-k) + ') = 0') + ', but ' + m('<i>f</i>(' + n(-k) + ') = ' + n(peval(c, -k))) + '.'] }, { t: 'factorOf', f: pd(c) });
      },
      function () {
        var deg = pick([3, 4, 5]), c = randSignPoly(deg), pos = K.coin(), v = changes(c), w = changes(negX(c)), cnt = pos ? v : w;
        var all = []; for (var t = cnt; t >= 0; t--) all.push(t);
        var wr = [possStr(pos ? w : v), anyStr(all), possStr(cnt + 1)];
        var why = pos ? ['Signs of the coefficients of ' + m(FX) + ': ' + signs(c).join(' ') + '. That is ' + v + ' sign change' + (v === 1 ? '' : 's') + '.'] : ['Find ' + m('<i>f</i>(' + M + '<i>x</i>) =') + ' ' + brk(pd(negX(c))) + '. Its signs: ' + signs(negX(c)).join(' ') + ', which is ' + w + ' sign change' + (w === 1 ? '' : 's') + '.'];
        why.push('Descartes’ rule: the number of ' + (pos ? 'positive' : 'negative') + ' real zeros is ' + cnt + ' or less than that by an even number: ' + possStr(cnt).toLowerCase() + '.');
        return QP({ q: 'By Descartes’ rule of signs, how many ' + (pos ? 'positive' : 'negative') + ' real zeros could ' + fx(pd(c)) + ' have?', mc: mc(possStr(cnt), wr, function (i) { return possStr(cnt + 1 + i); }), why: why }, { t: 'desc', f: pd(c), pos: pos });
      }
    ],
    [
      function () {
        var a = pick([2, 3]), b, r1, r2;
        do { b = rnz(-5, 5); r1 = rnz(-4, 4); r2 = rnz(-4, 4); } while (r1 === r2 || K.gcd(b, a) !== 1 || r2 === -r1);
        var c = pmul(pmul([1, -r1], [1, -r2]), [a, -b]), z = R(b, a), s1 = synth(c, r1);
        var fmtL = function (arr) { return list(sortV(arr).map(rh)); };
        var wr = [fmtL([-r1, -r2, z.neg()]), fmtL([r1, r2, R(a, b)]), fmtL([-r1, r2, z])];
        return QP({ q: 'Find all zeros of ' + fx(pd(c)) + '.', mc: mc(fmtL([r1, r2, z]), wr, function (i) { return fmtL([r1 + i, r2, z]); }),
          why: ['Rational zero candidates: ±(factors of ' + n(c[3]) + ')/(factors of ' + a + ').', 'Test ' + n(r1) + ': the remainder is 0, so ' + m(dv(r1)) + ' is a factor.' + synTable(r1, c, s1), 'Factor the quotient: ' + m(pd(s1.q) + ' = ' + fac(r2) + lin(a, -b)) + '. The zeros are ' + fmtL([r1, r2, z]) + '.'] }, { t: 'zeros', f: pd(c) });
      },
      function () {
        var rs, a = pick([-3, -2, -1, 2, 3]), x0;
        do { rs = [ri(-4, 4), ri(-4, 4), ri(-4, 4)]; } while (rs[0] === rs[1] || rs[1] === rs[2] || rs[0] === rs[2]);
        rs = sortV(rs).map(function (v) { return R(v).val(); });
        do { x0 = ri(-3, 3); } while (rs.indexOf(x0) >= 0);
        var base = fromRoots(rs, 1), v = a * peval(base, x0), cor = fromRoots(rs, a);
        // wrong leading coefficients: never 0 and never the correct a
        var leads = [1, -a, 2 * a, a + 1, a - 1, -2 * a, a + 2, a - 2].filter(function (L, i, arr) { return L !== 0 && L !== a && arr.indexOf(L) === i; });
        var cand = [fromRoots(rs, leads[0]), fromRoots(rs.map(function (r) { return -r; }), a), fromRoots(rs, leads[1])].map(function (f) { return [fx(pd(f)), pfn(f)]; });
        return QP({ q: 'Find the cubic polynomial ' + m(FX) + ' that has zeros ' + list(rs.map(n)) + ' and satisfies ' + m('<i>f</i>(' + n(x0) + ') = ' + n(v)) + '. Write it in standard form.',
          mc: mcF([fx(pd(cor)), pfn(cor)], cand, function (i) { var f = fromRoots(rs, leads[1 + i % (leads.length - 1)]); return [fx(pd(f)), pfn(f)]; }),
          why: ['Each zero <i>r</i> gives a factor ' + m('<i>x</i> ' + M + ' <i>r</i>') + ': ' + fx('<i>a</i>' + rs.map(function (r) { return fac(r); }).join('')) + '.', brk('<i>f</i>(' + n(x0) + ') = <i>a</i>' + rs.map(function (r) { return '(' + n(x0 - r) + ')'; }).join('') + ' = ' + lead(peval(base, x0)) + '<i>a</i> = ' + n(v)) + ', so ' + m('<i>a</i> = ' + n(a)) + '.', 'Multiply out: ' + fx(pd(cor)) + '.'] }, { t: 'fromZeros', zs: rs, x0: x0, v: v });
      },
      function () {
        var r = rnz(-4, 4), p = rnz(-3, 3), q = pick([1, 2, 3]), quad = [1, -2 * p, p * p + q * q], c = pmul([1, -r], quad);
        var cor = list([n(r), cx(p, q), cx(p, -q)]);
        var wr = [list([n(-r), cx(p, q), cx(p, -q)]), list([n(r), cx(p, q), cx(-p, -q)]), list([n(r), cx(p, q), cx(-p, q)])];
        return QP({ q: 'Given that ' + m(cx(p, q)) + ' is a zero of ' + fx(pd(c)) + ', find all zeros of <i>f</i>.', mc: mc(cor, wr),
          why: ['The coefficients are real, so the conjugate ' + m(cx(p, -q)) + ' is also a zero.', 'Multiply the conjugate factors: ' + brk('(<i>x</i> ' + M + ' (' + cx(p, q) + '))(<i>x</i> ' + M + ' (' + cx(p, -q) + ')) = ' + pd(quad)) + '.', 'Divide: ' + brk('(' + pd(c) + ') ÷ (' + pd(quad) + ') = ' + dv(r)) + ', so the third zero is ' + n(r) + '. Zeros: ' + cor + '.'] }, { t: 'zeros', f: pd(c) });
      }
    ],
    [
      function () {
        var cc = pick([2, 3, -1, -2]), r = rnz(-3, 3), p = ri(-2, 2), q = pick([1, 2]), x0;
        do { x0 = ri(-2, 2); } while (x0 === r);
        var quad = [1, -2 * p, p * p + q * q], base = pmul([1, -r], quad), v = cc * peval(base, x0), cor = base.map(function (t) { return cc * t; });
        var cand = [pmul([1, -r], [1, -2 * p, p * p - q * q]).map(function (t) { return cc * t; }), pmul([1, r], quad).map(function (t) { return cc * t; }), base].map(function (f) { return [fx(pd(f)), pfn(f)]; });
        return QP({ q: 'Find the cubic polynomial ' + m(FX) + ' with real coefficients that has zeros ' + n(r) + ' and ' + m(cx(p, q)) + ' and satisfies ' + m('<i>f</i>(' + n(x0) + ') = ' + n(v)) + '.',
          mc: mcF([fx(pd(cor)), pfn(cor)], cand, function (i) { var f = base.map(function (t) { return (cc + i) * t; }); return [fx(pd(f)), pfn(f)]; }),
          why: ['Real coefficients, so ' + m(cx(p, -q)) + ' is also a zero.', 'The conjugate pair multiplies to ' + m(sq(p === 0 ? IX : '(' + dv(p) + ')') + ' + ' + (q * q)) + (p === 0 ? '' : ' = ' + m(pd(quad))) + ' (remember ' + m('<i>i</i><sup>2</sup> = ' + M + '1') + ').', fx('<i>a</i>' + fac(r) + '(' + pd(quad) + ')') + '; ' + m('<i>f</i>(' + n(x0) + ') = ' + lead(peval(base, x0)) + '<i>a</i> = ' + n(v)) + ', so ' + m('<i>a</i> = ' + n(cc)) + '.', 'Multiply out: ' + fx(pd(cor)) + '.'] }, { t: 'cubicConj', r: r, p: p, q: q, x0: x0, v: v });
      },
      function () {
        var r1, r2, p = ri(-3, 3), irr = K.coin(), d = pick([2, 3, 5, 6, 7]), q = pick([1, 2, 3]);
        do { r1 = rnz(-3, 3); r2 = rnz(-3, 3); } while (r1 === r2 || r1 === -r2);
        var quad = irr ? [1, -2 * p, p * p - d] : [1, -2 * p, p * p + q * q], c = pmul(fromRoots([r1, r2]), quad);
        var body = irr ? K.sqrt(d) : (q === 1 ? '' : q) + II, swap = irr ? II + K.sqrt(d) : n(q);
        var rat = sortV([r1, r2]).map(n), ratN = sortV([-r1, -r2]).map(n);
        var cor = list(rat.concat([pmS(p, body)]));
        var wr = [list(ratN.concat([pmS(p, body)])), list(rat.concat([pmS(-p, body)])), list(rat.concat([pmS(p, swap)]))];
        var s1 = synth(c, r1), s2 = synth(s1.q, r2);
        var disc = 4 * p * p - 4 * (irr ? p * p - d : p * p + q * q);
        return QP({ q: 'Find all zeros of ' + fx(pd(c)) + '.', mc: mc(cor, wr, function (i) { return list(sortV([-r1, r2]).map(n).concat([pmS(p + i, body)])); }),
          why: ['Test rational candidates (factors of ' + n(c[4]) + '): ' + m('<i>f</i>(' + n(r1) + ') = 0') + ' and ' + m('<i>f</i>(' + n(r2) + ') = 0') + '.', 'Dividing by ' + m(dv(r1)) + ' and then by ' + m(dv(r2)) + ' leaves ' + m(pd(s2.q)) + '.', 'Quadratic formula: ' + m(IX + ' = ' + fr(n(2 * p) + ' ± ' + K.sqrt(n(disc)), '2') + ' = ' + pmS(p, body)) + '. All zeros: ' + cor + '.'] }, { t: 'zeros', f: pd(c) });
      },
      function () {
        var deg = pick([4, 5]), c = randSignPoly(deg), v = changes(c), w = changes(negX(c)), valid = [], bad = [];
        for (var pp = 0; pp <= deg; pp++) for (var nn = 0; nn + pp <= deg; nn++) {
          var cc = deg - pp - nn, ok = pp <= v && (v - pp) % 2 === 0 && nn <= w && (w - nn) % 2 === 0 && cc % 2 === 0;
          (ok ? valid : bad).push([pp, nn, cc]);
        }
        if (!valid.length || bad.length < 3) return c33[2][2]();
        var fmt = function (t) { return t[0] + ' positive, ' + t[1] + ' negative, ' + t[2] + ' nonreal'; };
        var cor = pick(valid), wr = K.sample(bad, 3);
        return QP({ q: 'For ' + fx(pd(c)) + ', which combination of positive real zeros, negative real zeros, and nonreal complex zeros is possible?', mc: mc(fmt(cor), wr.map(fmt)),
          why: [m(FX) + ' has signs ' + signs(c).join(' ') + ': ' + v + ' sign change' + (v === 1 ? '' : 's') + ', so ' + possStr(v).toLowerCase() + ' positive real zero' + (v === 1 ? '' : 's') + '.', m('<i>f</i>(' + M + '<i>x</i>)') + ' has signs ' + signs(negX(c)).join(' ') + ': ' + w + ' sign change' + (w === 1 ? '' : 's') + ', so ' + possStr(w).toLowerCase() + ' negative real zero' + (w === 1 ? '' : 's') + '.', 'The total is ' + deg + ', and nonreal zeros come in conjugate pairs (an even number). Of the choices, only ' + fmt(cor) + ' fits every rule.'] }, { t: 'combo', f: pd(c) });
      }
    ]
  ];
  K.lesson('3.3', { title: 'Zeros of Polynomial Functions', std: 'Lial 12e · Section 3.3', levels: c33 });

  /* ================= 3.4 Polynomial Functions: Graphs, Applications, and Models ================= */
  function distinctZeros(cnt, lo, hi) { var z; do { z = []; while (z.length < cnt) { var v = ri(lo, hi); if (z.indexOf(v) < 0) z.push(v); } } while (false); return z.sort(function (a, b) { return a - b; }); }
  function factored(a, zs, ms) { return lead(a) + zs.map(function (z, i) { return fac(z, ms[i]); }).join(''); }
  function minBump(f, zs) { var mn = Infinity; for (var j = 0; j < zs.length - 1; j++) { var b = 0; for (var i = 1; i < 60; i++) b = Math.max(b, Math.abs(f(zs[j] + (zs[j + 1] - zs[j]) * i / 60))); mn = Math.min(mn, b); } return mn; }
  function factFn(a, zs, ms) { var av = R(a).val(); return function (x) { var v = av; zs.forEach(function (z, i) { v *= Math.pow(x - z, ms[i]); }); return v; }; }
  var c34 = [
    [
      function () {
        var deg = ri(2, 7), a = rnz(-5, 5), terms = [[a, K.xp(deg)]], pw = [];
        for (var p = deg - 1; p >= 1; p--) if (K.coin()) pw.push(p);
        pw.slice(0, 2).forEach(function (p) { terms.push([rnz(-9, 9), K.xp(p)]); });
        terms.push([ri(-9, 9), '']);
        if (K.coin()) terms.reverse();
        var f = P(terms), cor = beh(deg, a);
        return QP({ q: 'Which describes the end behavior of the graph of ' + fx(f) + '?', mc: mc(cor, [BEH.uu, BEH.dd, BEH.du, BEH.ud].filter(function (s) { return s !== cor; })),
          why: ['Only the leading term matters for end behavior: ' + m(P([[a, K.xp(deg)]])) + '.', 'Degree ' + deg + ' is ' + (deg % 2 ? 'odd, so the ends go opposite ways' : 'even, so both ends go the same way') + '. The leading coefficient ' + n(a) + ' is ' + (a > 0 ? 'positive, so the right end rises.' : 'negative, so the right end falls.'), cor + '.'] }, { t: 'endb', f: f });
      },
      function () {
        var zs = distinctZeros(3, -5, 5), ms = K.shuffle([2, 1, pick([1, 3])]), s = pick([1, -1, 2, -2]), ie = ms.indexOf(2), te = zs[ie];
        var f = factored(s, zs, ms), others = zs.filter(function (z, i) { return i !== ie; });
        var wr = others.map(function (z) { return xe(z); }); if (zs.indexOf(-te) < 0) wr.push(xe(-te));
        return QP({ q: 'At which zero does the graph of ' + fx(f) + ' touch the <i>x</i>-axis and turn around instead of crossing it?', mc: mc(xe(te), wr, function (i) { return xe(te + 6 + i); }),
          why: ['The multiplicity of each zero is the exponent on its factor: ' + zs.map(function (z, i) { return n(z) + ' has multiplicity ' + ms[i]; }).join(', ') + '.', 'Even multiplicity: the graph touches and turns. Odd multiplicity: it crosses.', 'Only ' + n(te) + ' has even multiplicity, so the graph touches at ' + xe(te) + '.'] }, { t: 'touch', f: f });
      },
      function () {
        var f, deg, dz = null;
        if (K.coin()) {
          var cnt = pick([2, 3]), zs = distinctZeros(cnt, -5, 5), ms = zs.map(function () { return pick([1, 1, 2, 3]); });
          deg = ms.reduce(function (s, v) { return s + v; }, 0); dz = cnt; f = factored(pick([1, -1, 2, -3]), zs, ms);
        } else { deg = ri(3, 7); var c = [rnz(-6, 6)]; for (var i = 1; i <= deg; i++) c.push(ri(-9, 9)); f = pd(c); }
        var wr = [n(deg), n(deg + 1), deg >= 3 ? n(deg - 2) : n(deg + 2)]; if (dz !== null) wr.unshift(n(dz));
        return QP({ q: 'What is the greatest number of turning points the graph of ' + fx(f) + ' can have?', mc: mc(n(deg - 1), wr),
          why: [dz !== null ? 'The degree is the sum of the exponents on the factors: ' + deg + '.' : 'The highest power of <i>x</i> is ' + deg + ', so the degree is ' + deg + '.', 'A polynomial of degree <i>n</i> has at most ' + m('<i>n</i> ' + M + ' 1') + ' turning points.', 'At most ' + m(deg + ' ' + M + ' 1 = ' + (deg - 1)) + ' turning point' + (deg - 1 === 1 ? '' : 's') + '.'] }, { t: 'turn', f: f });
      }
    ],
    [
      function () {
        var zs, ms, base, Mx, den, s, tries = 0;
        do {
          zs = distinctZeros(pick([2, 3, 3]), -4, 4); ms = zs.length === 3 ? K.shuffle([1, 1, pick([1, 2, 2])]) : K.shuffle([pick([1, 2, 3]), pick([1, 2])]);
          base = factFn(1, zs, ms); Mx = 0;
          for (var i = 0; i <= 300; i++) { var x = zs[0] + (zs[zs.length - 1] - zs[0]) * i / 300; Mx = Math.max(Mx, Math.abs(base(x))); }
          den = 1; while (Mx / den > 9) den *= 2;
        } while ((Mx / den < 2.5 || minBump(base, zs) / den < 0.9) && tries++ < 200);
        s = pick([1, -1]); var a = R(s, den), f = factFn(a, zs, ms);
        var j = ri(0, zs.length - 1), ms2 = ms.slice(); ms2[j] = ms[j] === 1 ? 2 : ms[j] === 2 ? 1 : 2;
        var zs3 = zs.map(function (z) { return -z; });
        var cor = [fx(factored(a, zs, ms)), f];
        var wr = [[fx(factored(a, zs, ms2)), factFn(a, zs, ms2)], [fx(factored(a.neg(), zs, ms)), factFn(a.neg(), zs, ms)], [fx(factored(a, zs3, ms)), factFn(a, zs3, ms)]];
        var deg = ms.reduce(function (t, v) { return t + v; }, 0);
        return QP({ q: 'Which function could have the graph shown?', graph: K.plane({ x: [-5, 5], y: [-10, 10], h: 400, fns: [{ f: f }] }),
          mc: mcF(cor, wr, function (i) { var z2 = zs.slice(); z2[0] -= i; return [fx(factored(a, z2, ms)), factFn(a, z2, ms)]; }),
          why: ['The graph meets the <i>x</i>-axis at ' + list(zs.map(n)) + ', so those are the zeros.', zs.map(function (z, i) { return n(z) + ': ' + (ms[i] % 2 ? (ms[i] === 1 ? 'crosses (multiplicity 1)' : 'crosses and flattens (multiplicity 3)') : 'touches and turns (multiplicity 2)'); }).join('; ') + '.', 'Degree ' + deg + ' with ' + (s > 0 ? 'a positive' : 'a negative') + ' leading coefficient: ' + beh(deg, s).toLowerCase() + ', which matches ' + fx(factored(a, zs, ms)) + '.'] }, { t: 'graph', fn: f });
      },
      function () {
        var cnt = pick([2, 3]), zs = distinctZeros(cnt, -5, 5), ms = zs.map(function () { return pick([1, 2, 3]); }), rev = K.coin(), sR = rnz(-5, 5), c = pick([1, 2, 3, -1, -2]);
        if (rev) while (zs.indexOf(sR) >= 0) sR = rnz(-5, 5);
        var deg = ms.reduce(function (t, v) { return t + v; }, 0) + (rev ? 1 : 0), sg = (c > 0 ? 1 : -1) * (rev ? -1 : 1), nf = cnt + (rev ? 1 : 0);
        var f = lead(c) + zs.map(function (z, i) { return fac(z, ms[i]); }).join('') + (rev ? '(' + n(sR) + ' ' + M + ' ' + IX + ')' : '');
        var ans = function (d, b) { return 'Degree ' + d + '; ' + b.toLowerCase(); };
        var wr = [ans(nf === deg ? deg + 1 : nf, beh(deg, sg)), ans(deg, beh(deg, -sg)), ans(deg, beh(deg + 1, sg))];
        var lt = 'The leading term is ' + [c === 1 ? '' : m(n(c))].concat(zs.map(function (z, i) { return m(K.xp(ms[i])); })).concat(rev ? [m('(' + M + IX + ')')] : []).filter(Boolean).join(' · ');
        return QP({ q: 'What are the degree and the end behavior of ' + fx(f) + '?', mc: mc(ans(deg, beh(deg, sg)), wr),
          why: [lt + ' = ' + m(P([[sg * Math.abs(c), K.xp(deg)]])) + '.' + (rev ? ' The factor ' + m('(' + n(sR) + ' ' + M + ' ' + IX + ')') + ' contributes ' + m(M + IX) + ', which flips the sign.' : ''), 'Degree ' + deg + ' (' + (deg % 2 ? 'odd' : 'even') + ') with a ' + (sg > 0 ? 'positive' : 'negative') + ' leading coefficient.', ans(deg, beh(deg, sg)) + '.'] }, { t: 'degEnd', f: f });
      },
      function () {
        var a, b, c, d, cf, lo, tries = 0;
        do {
          a = pick([1, -1, 2]); b = ri(-6, 6); c = ri(-8, 8); d = rnz(-9, 9); cf = [a, b, c, d];
          var disc = 18 * a * b * c * d - 4 * b * b * b * d + b * b * c * c - 4 * a * c * c * c - 27 * a * a * d * d;
          lo = null;
          if (disc < 0) for (var t = -4; t <= 3; t++) if (peval(cf, t) * peval(cf, t + 1) < 0) lo = t;
        } while (lo === null && tries++ < 500);
        var others = []; for (var u = -4; u <= 3; u++) if (u !== lo) others.push(u);
        var iv2 = function (t) { return 'Between ' + n(t) + ' and ' + n(t + 1); };
        return QP({ q: 'By the intermediate value theorem, which interval must contain a real zero of ' + fx(pd(cf)) + '?', mc: mc(iv2(lo), K.sample(others, 3).map(iv2)),
          why: ['Evaluate at the endpoints: ' + m('<i>f</i>(' + n(lo) + ') = ' + n(peval(cf, lo))) + ' and ' + m('<i>f</i>(' + n(lo + 1) + ') = ' + n(peval(cf, lo + 1))) + '.', 'The signs are opposite, so the graph must cross the <i>x</i>-axis between ' + n(lo) + ' and ' + n(lo + 1) + '.', 'For the other intervals, <i>f</i> has the same sign at both endpoints, so the theorem guarantees nothing there (and this cubic has only one real zero).'] }, { t: 'ivt', f: pd(cf) });
      }
    ],
    [
      function () { // zeros, multiplicities and end behavior → which function
        var zs = distinctZeros(3, -4, 4), ms = K.shuffle([1, 2, pick([1, 3])]), s = pick([1, -1]);
        var c1 = zs.filter(function (z, i) { return ms[i] === 1; }), revZ = K.coin() ? (c1.filter(function (z) { return z !== 0; })[0]) : undefined;
        var degOf = function (mm) { return mm.reduce(function (a, b) { return a + b; }, 0); };
        var sig = function (ss, zz, mm) { return beh(degOf(mm), ss) + '|' + zz.map(function (z, i) { return z + ':' + mm[i]; }).sort().join(','); };
        var disp = function (ss, zz, mm, rz) { // true leading coefficient ss; one factor (rz − x) when rz is given
          var body = zz.map(function (z, i) { return z === rz && mm[i] === 1 ? '' : fac(z, mm[i]); }).join('') + (rz !== undefined && zz.indexOf(rz) >= 0 && mm[zz.indexOf(rz)] === 1 ? '(' + n(rz) + ' ' + M + ' ' + IX + ')' : '');
          var rv = rz !== undefined && zz.indexOf(rz) >= 0 && mm[zz.indexOf(rz)] === 1;
          return fx(lead(rv ? -ss : ss) + body);
        };
        var cor = disp(s, zs, ms, revZ), want = sig(s, zs, ms), it = ms.indexOf(2);
        var cands = [[-s, zs, ms], [s, zs.map(function (z) { return -z; }), ms], [s, zs, ms.map(function (v, i) { return i === it ? 1 : v === 1 && i === ms.indexOf(1) ? 2 : v; })], [s, zs, ms.map(function (v) { return v === 2 ? 1 : v; })], [s, zs, ms.map(function (v) { return v === 3 ? 1 : v; })]];
        var wr = [];
        cands.forEach(function (cd) { if (sig(cd[0], cd[1], cd[2]) !== want) wr.push(disp(cd[0], cd[1], cd[2], cd[1] === zs ? revZ : (revZ === undefined ? undefined : -revZ))); });
        var cross = [], touch = [], flat = [];
        zs.forEach(function (z, i) { (ms[i] === 1 ? cross : ms[i] === 2 ? touch : flat).push(n(z)); });
        var dsc = [beh(degOf(ms), s).toLowerCase(), 'crosses the <i>x</i>-axis at ' + list(cross)];
        if (flat.length) dsc.push('crosses and flattens out at ' + flat[0]);
        dsc.push('touches it at ' + touch[0]);
        var deg = degOf(ms), even = deg % 2 === 0, pos = s > 0;
        return QP({ q: 'Which function could have a graph that ' + list(dsc) + ' (and has no other <i>x</i>-intercepts)?', mc: mc(cor, K.shuffle(wr).slice(0, 3)),
          why: ['Each zero gives a factor, and the exponent matches what the graph does there: crosses → exponent 1, touches and turns → exponent 2, crosses and flattens → exponent 3. So the factors are ' + zs.map(function (z, i) { return m(fac(z, ms[i])); }).join(', ') + '.',
            'The degree is ' + ms.join(' + ') + ' = ' + deg + ' (' + (even ? 'even' : 'odd') + '). The graph ' + beh(deg, s).toLowerCase() + ', so the leading coefficient must be ' + (pos ? 'positive' : 'negative') + '.' + (revZ !== undefined ? ' The factor ' + m('(' + n(revZ) + ' ' + M + ' ' + IX + ')') + ' contributes ' + m(M + IX) + ', which flips the sign, so the constant in front is ' + (pos ? 'negative' : 'positive') + '.' : ''),
            'So ' + cor + ' fits every condition.'] }, { t: 'describe', f: cor });
      },
      function () {
        var r1, r2, a, v, fn, Mx, tries = 0;
        do {
          r1 = rnz(-4, 4); r2 = rnz(-4, 4); a = R(pick([1, -1, 2, -2, R(1, 2), R(-1, 2), R(1, 4), R(-1, 4)]));
          v = a.mul(-r1 * r2 * r2); fn = factFn(a, [r1, r2], [1, 2]); Mx = 0;
          var xa = Math.min(r1, r2, 0) - 0.3, xb = Math.max(r1, r2, 0) + 0.3;
          for (var i = 0; i <= 300; i++) Mx = Math.max(Mx, Math.abs(fn(xa + (xb - xa) * i / 300)));
        } while ((r1 === r2 || !v.isInt() || Math.abs(v.val()) > 9 || Mx > 9.5 || Mx < 2 || minBump(fn, [Math.min(r1, r2), Math.max(r1, r2)]) < 1) && tries++ < 2000);
        var cor = [fx(factored(a, [r1, r2], [1, 2])), fn];
        var wr = [[fx(factored(a, [r1, r2], [2, 1])), factFn(a, [r1, r2], [2, 1])], [fx(factored(a.neg(), [r1, r2], [1, 2])), factFn(a.neg(), [r1, r2], [1, 2])], [fx(factored(a.mul(2), [r1, r2], [1, 2])), factFn(a.mul(2), [r1, r2], [1, 2])], [fx(factored(a, [-r1, -r2], [1, 2])), factFn(a, [-r1, -r2], [1, 2])]];
        return QP({ q: 'The graph of a polynomial <i>f</i> of degree 3 is shown, with its <i>y</i>-intercept labeled. Which is ' + m(FX) + '?', graph: K.plane(place({ x: [-5, 5], y: [-10, 10], h: 400, fns: [{ f: fn }], pts: [{ x: 0, y: v.val(), label: '(0, ' + v.val() + ')' }, { x: r1, y: 0 }, { x: r2, y: 0 }] })),
          mc: mcF(cor, K.shuffle(wr)),
          why: ['The graph crosses at ' + n(r1) + ' (multiplicity 1) and touches at ' + n(r2) + ' (multiplicity 2): ' + fx('<i>a</i>' + fac(r1) + fac(r2, 2)) + '.', 'Use the <i>y</i>-intercept: ' + m('<i>f</i>(0) = <i>a</i>(' + n(-r1) + ')(' + n(-r2) + ')<sup>2</sup> = ' + lead(-r1 * r2 * r2) + '<i>a</i> = ' + v.html()) + ', so ' + m('<i>a</i> = ' + a.html()) + '.', 'So ' + fx(factored(a, [r1, r2], [1, 2])) + '.'] }, { t: 'graph', fn: fn });
      },
      function () {
        var W = pick([8, 10, 12, 14, 16]), L = W + 2 * ri(1, 5), d = pick([1, 2]);
        var V = function (x) { return x * (L - 2 * x) * (W - 2 * x); }, vd = V(d), v2 = d * (L - d) * (W - d);
        var ans = function (dom, vol) { return 'Domain ' + m(dom) + '; ' + K.comma(vol) + ' cubic inches'; };
        return QP({ q: 'An open box is made from a sheet of cardboard that measures ' + L + ' inches by ' + W + ' inches by cutting a square of side <i>x</i> inches from each corner and folding up the sides. Its volume is ' + m('<i>V</i>(<i>x</i>) = <i>x</i>(' + L + ' ' + M + ' 2<i>x</i>)(' + W + ' ' + M + ' 2<i>x</i>)') + '. What is the domain of <i>V</i> in this situation, and what is the volume when ' + m(IX + ' = ' + d) + '?',
          mc: mc(ans(iv(0, W / 2), vd), [ans(iv(0, L / 2), vd), ans(iv(0, W / 2), v2), 'Domain ' + m('[0, ' + n(W / 2) + ']') + '; ' + K.comma(vd) + ' cubic inches']),
          why: ['Every dimension must be positive: ' + m('<i>x</i> &gt; 0') + ', ' + m(L + ' ' + M + ' 2<i>x</i> &gt; 0') + ' (so ' + m('<i>x</i> &lt; ' + n(L / 2)) + '), and ' + m(W + ' ' + M + ' 2<i>x</i> &gt; 0') + ' (so ' + m('<i>x</i> &lt; ' + n(W / 2)) + ').', 'All three hold when ' + m('0 &lt; <i>x</i> &lt; ' + n(W / 2)) + ', so the domain is ' + m(iv(0, W / 2)) + '.', m('<i>V</i>(' + d + ') = ' + d + '(' + (L - 2 * d) + ')(' + (W - 2 * d) + ') = ' + K.comma(vd)) + ' cubic inches.'] }, { t: 'box', L: L, W: W, d: d });
      }
    ]
  ];
  K.lesson('3.4', { title: 'Polynomial Functions: Graphs, Applications, and Models', std: 'Lial 12e · Section 3.4', levels: c34 });

  /* ================= 3.5 Rational Functions: Graphs, Applications, and Models ================= */
  function sgnFrac(a, den) { return (a < 0 ? M : '') + fr(n(Math.abs(a)), den); }
  var c35 = [
    [
      function () {
        if (K.coin()) {
          var a, b, c; do { a = rnz(-4, 4); b = rnz(-9, 9); c = rnz(-6, 6); } while (a * c + b === 0 || R(-b, a).eq(-c));
          var f = fr(P([[a, IX], [b, '']]), dv(c));
          return QP({ q: 'What is the vertical asymptote of ' + fx(f) + '?', mc: mc(xe(c), [xe(-c), xe(R(-b, a)), ye(a)]),
            why: ['Nothing cancels: the numerator is 0 only at ' + m(IX + ' = ' + rh(R(-b, a))) + ', which is not ' + n(c) + '.', 'Set the denominator equal to 0: ' + m(dv(c) + ' = 0') + ' gives ' + xe(c) + '.', 'That is the vertical asymptote. (The numerator’s zero gives an <i>x</i>-intercept, not an asymptote.)'] }, { t: 'va', f: f });
        }
        var a2, b2, c1, c2; do { a2 = rnz(-4, 4); b2 = rnz(-9, 9); c1 = rnz(-6, 6); c2 = rnz(-6, 6); } while (c1 >= c2 || c1 === -c2 || R(-b2, a2).eq(c1) || R(-b2, a2).eq(c2));
        var f2 = fr(P([[a2, IX], [b2, '']]), pd(fromRoots([c1, c2])));
        var two = function (u, v) { return m(IX + ' = ' + n(u)) + ' and ' + m(IX + ' = ' + n(v)); };
        return QP({ q: 'What are the vertical asymptotes of ' + fx(f2) + '?', mc: mc(two(c1, c2), [two(-c2, -c1), xe(R(-b2, a2)), ye(0)]),
          why: ['Factor the denominator: ' + m(pd(fromRoots([c1, c2])) + ' = ' + fac(c1) + fac(c2)) + '.', 'Neither factor cancels with the numerator ' + m(P([[a2, IX], [b2, '']])) + '.', 'Each zero of the denominator is a vertical asymptote: ' + two(c1, c2) + '.'] }, { t: 'va', f: f2 });
      },
      function () {
        var cs = pick(['less', 'equal', 'more']), nD = pick([1, 2]), nN = cs === 'less' ? nD - 1 : cs === 'equal' ? nD : nD + 1;
        var num, den, aN, aD, cN, cD;
        do {
          aN = rnz(-6, 6); aD = rnz(-6, 6); cN = rnz(-9, 9); cD = rnz(-9, 9); if (nN === 0) aN = cN;
          num = [aN]; for (var i = 1; i < nN; i++) num.push(ri(-6, 6)); if (nN > 0) num.push(cN);
          den = [aD]; for (var j = 1; j < nD; j++) den.push(ri(-6, 6)); den.push(cD);
        } while (R(cN, cD).eq(R(aN, aD)) || gcdDeg(num, den) > 0); // no common factor, so no hole and no reduced form
        var rat = R(aN, aD), f = fr(pd(num), pd(den)), none = 'No horizontal asymptote';
        var opts = [ye(0), ye(rat), ye(R(cN, cD)), none];
        var cor = cs === 'less' ? ye(0) : cs === 'equal' ? ye(rat) : none;
        var why = cs === 'less' ? ['The numerator has degree ' + nN + ' and the denominator has degree ' + nD + '.', 'When the denominator’s degree is larger, the horizontal asymptote is ' + ye(0) + '.']
          : cs === 'equal' ? ['Both numerator and denominator have degree ' + nD + '.', 'Equal degrees: the horizontal asymptote is the ratio of leading coefficients, ' + m(IY + ' = ' + eqs(frq(aN, aD), rat.html())) + '.']
            : ['The numerator has degree ' + nN + ', one more than the denominator’s degree ' + nD + '.', 'So there is no horizontal asymptote; the graph has an oblique (slanted) asymptote instead.'];
        return QP({ q: 'What is the horizontal asymptote of ' + fx(f) + '?', mc: mc(cor, opts.filter(function (o) { return o !== cor; })), why: why }, { t: 'ha', f: f });
      },
      function () {
        var h, k, a = pick([1, 1, 2, 3, -1]); do { h = rnz(-6, 6); k = rnz(-6, 6); } while (Math.abs(h) === Math.abs(k));
        var f = sgnFrac(a, dv(h)) + K.plusK(k), two = function (u, v) { return m(IX + ' = ' + n(u)) + ' and ' + m(IY + ' = ' + n(v)); };
        return QP({ q: 'What are the vertical and horizontal asymptotes of ' + fx(f) + '?', mc: mc(two(h, k), [two(-h, k), two(h, -k), two(k, h)]),
          why: ['This is ' + m(IY + ' = ' + fr('1', IX)) + [Math.abs(a) > 1 ? ' stretched by a factor of ' + Math.abs(a) : '', a < 0 ? ' reflected across the <i>x</i>-axis' : ''].filter(Boolean).join(' and') + (a !== 1 ? ',' : '') + ' shifted ' + (h > 0 ? 'right ' + h : 'left ' + (-h)) + ' and ' + (k > 0 ? 'up ' + k : 'down ' + (-k)) + '.', 'The asymptotes move with the graph: ' + m(IX + ' = 0') + ' becomes ' + m(IX + ' = ' + n(h)) + ' (where ' + m(dv(h) + ' = 0') + '), and ' + m(IY + ' = 0') + ' becomes ' + m(IY + ' = ' + n(k)) + '.'] }, { t: 'asym', f: f });
      }
    ],
    [
      function () {
        var a, b, c; do { a = rnz(-5, 5); b = ri(-5, 5); c = rnz(-5, 5); } while (a === b || a === c || b === c);
        var hy = R(a - b, a - c), f = fr(pd(fromRoots([a, b])), pd(fromRoots([a, c])));
        var hv = function (hx, hyv, va) { return 'Hole at ' + K.pt(hx, hyv) + '; vertical asymptote ' + xe(va); };
        var lo = Math.min(a, c), hi = Math.max(a, c);
        return QP({ q: 'Find the hole and the vertical asymptote of ' + fx(f) + '.', mc: mc(hv(a, hy, c), ['No hole; vertical asymptotes ' + xe(lo) + ' and ' + xe(hi), hv(c, R(c - b, c - a), a), hv(a, hy, -c)]),
          why: ['Factor: ' + fx(fr(fac(a) + fac(b), fac(a) + fac(c))) + '.', 'The factor ' + m(fac(a)) + ' cancels, leaving ' + m(fr(dv(b), dv(c))) + ' with ' + m(IX + ' ≠ ' + n(a)) + '. Substitute ' + n(a) + ': ' + m(eqs(frq(a - b, a - c), hy.html())) + ', so the hole is at ' + K.pt(a, hy) + '.', 'The remaining denominator gives the vertical asymptote ' + xe(c) + '.'] }, { t: 'hole', f: f });
      },
      function () {
        var a, b, cc, d, rr; do { a = pick([1, 2, -1, 3]); b = ri(-6, 6); cc = ri(-9, 9); d = rnz(-4, 4); rr = a * d * d + b * d + cc; } while (rr === 0);
        var s = synth([a, b, cc], d), f = fr(pd([a, b, cc]), dv(d)), ln = function (mm, bb) { return m(K.lineEq(mm, bb)); };
        return QP({ q: 'What is the oblique asymptote of ' + fx(f) + '?', mc: mc(ln(a, b + a * d), [ln(a, b - a * d), ln(a, b), ye(a)]),
          why: ['The numerator’s degree is one more than the denominator’s, so divide. Synthetic division with ' + m('<i>k</i> = ' + n(d)) + ':' + synTable(d, [a, b, cc], s), fx(P([[a, IX], [b + a * d, '']]) + (rr > 0 ? ' + ' : ' ' + M + ' ') + fr(n(Math.abs(rr)), dv(d))) + '.', 'As ' + m('|<i>x</i>| → ∞') + ', the fraction goes to 0, so the oblique asymptote is ' + ln(a, b + a * d) + '.'] }, { t: 'oblique', f: f });
      },
      function () {
        var a = pick([1, -1, 2, -2]), h = rnz(-4, 4), k = rnz(-4, 4);
        var mk = function (aa, hh, kk) { return fx(sgnFrac(aa, dv(hh)) + K.plusK(kk)); };
        var fn = function (x) { return a / (x - h) + k; };
        return QP({ q: 'Which function is graphed below? The dashed lines are asymptotes.', graph: ratGraph(fn, [h], k, { x: [-7, 7], y: [-7, 7], h: 340, pts: [{ x: h + 1, y: k + a, label: '(' + (h + 1) + ', ' + (k + a) + ')' }, { x: h - 1, y: k - a, label: '(' + (h - 1) + ', ' + (k - a) + ')' }] }),
          mc: mc(mk(a, h, k), [mk(a, -h, k), mk(a, h, -k), mk(-a, h, k)]),
          why: ['The vertical asymptote is ' + m(IX + ' = ' + n(h)) + ', so the denominator is ' + m(dv(h)) + '.', 'The horizontal asymptote is ' + m(IY + ' = ' + n(k)) + ', so the graph is shifted ' + (k > 0 ? 'up ' : 'down ') + Math.abs(k) + '.', 'At ' + m(IX + ' = ' + n(h + 1)) + ' the graph is at ' + n(k + a) + ', which is ' + Math.abs(a) + (a > 0 ? ' above' : ' below') + ' the asymptote, so the numerator is ' + n(a) + ': ' + mk(a, h, k) + '.'] }, { t: 'graph', fn: fn, undef: [h] });
      },
      function () {
        var a, b, d; do { a = rnz(-4, 4); b = rnz(-9, 9); d = rnz(-6, 6); } while (a * d === b || R(b, d).eq(a) || R(b, a).eq(-d));
        var xi = R(-b, a), yi = R(b, d), f = fr(P([[a, IX], [b, '']]), P([[1, IX], [d, '']]));
        var ans = function (xv, yv) { return '<i>x</i>-intercept ' + K.pt(xv, 0) + '; <i>y</i>-intercept ' + K.pt(0, yv); };
        return QP({ q: 'Find the intercepts of ' + fx(f) + '.', mc: mc(ans(xi, yi), [ans(-d, yi), ans(xi.neg(), yi), ans(xi, a)]),
          why: ['<i>x</i>-intercept: set the numerator equal to 0. ' + m(P([[a, IX], [b, '']]) + ' = 0') + ' gives ' + m(IX + ' = ' + xi.html()) + '.', '<i>y</i>-intercept: ' + m('<i>f</i>(0) = ' + eqs(frq(b, d), yi.html())) + '.', 'Answer: ' + ans(xi, yi) + '. (' + m(IX + ' = ' + n(-d)) + ' is the vertical asymptote, not an intercept.)'] }, { t: 'intercepts', f: f });
      }
    ],
    [
      function () {
        var k, a, b, c, hy, tries = 0;
        do { k = pick([1, 2, -1, -2]); a = rnz(-5, 5); b = ri(-5, 5); c = rnz(-5, 5); hy = a === c ? R(99) : R(k * (a - b), a - c); } while ((a === b || a === c || b === c || a === -c || Math.abs(hy.val()) > 7 || Math.abs(hy.val()) < 0.5) && tries++ < 500);
        var mk = function (kk, bb, cc, aa) { return fx(fr(lead(kk) + fac(bb) + fac(aa), fac(cc) + fac(aa))); };
        var fn = function (x) { return k * (x - b) / (x - c); };
        return QP({ q: 'Which function has the graph shown? The dashed lines are asymptotes, and the open circle is a hole.', graph: ratGraph(fn, [c], k, { x: [-7, 7], y: [-8, 8], h: 360, pts: [{ x: a, y: hy.val(), open: true }, { x: b, y: 0 }] }),
          mc: mc(mk(k, b, c, a), [mk(k, c, b, a), mk(k, b, c, -a), mk(-k, b, c, a)]),
          why: ['The hole at ' + m(IX + ' = ' + n(a)) + ' means ' + m(fac(a)) + ' is a factor of both the numerator and the denominator.', 'The vertical asymptote ' + m(IX + ' = ' + n(c)) + ' puts ' + m(fac(c)) + ' in the denominator; the <i>x</i>-intercept ' + K.pt(b, 0) + ' puts ' + m(fac(b)) + ' in the numerator.', 'The horizontal asymptote ' + m(IY + ' = ' + n(k)) + ' is the ratio of leading coefficients, so ' + (k === 1 ? 'no extra constant factor is needed' : 'the numerator has a constant factor of ' + n(k)) + ': ' + mk(k, b, c, a) + '. Check the hole: ' + m(fr((k === 1 ? '' : k === -1 ? M : n(k)) + '(' + n(a) + ' ' + M + ' ' + sub(b) + ')', n(a) + ' ' + M + ' ' + sub(c)) + ' = ' + hy.html()) + '.'] }, { t: 'graph', fn: fn, undef: [a, c] });
      },
      function () {
        var c = pick([2, 3, 4, 5, 8, 12]), N = pick([50, 100, 200, 250, 500]), t = ri(2, 12), F = N * t, A2 = c + t;
        var ans = function (v, lim) { return '$' + K.comma(v) + ' per item; it approaches $' + K.comma(lim); };
        return QP({ q: 'A small business has fixed costs of $' + K.comma(F) + ' plus $' + c + ' per item, so its average cost per item is ' + m('<i>A</i>(<i>x</i>) = ' + fr(c + '<i>x</i> + ' + K.comma(F), IX)) + ' when it makes <i>x</i> items. What is the average cost when ' + K.comma(N) + ' items are made, and what value does the average cost approach as <i>x</i> grows?',
          mc: mc(ans(A2, c), [ans(A2, F), ans(c * N + F, c), '$' + K.comma(A2) + ' per item; it approaches $0']),
          why: [m('<i>A</i>(' + K.comma(N) + ') =') + ' ' + brk(fr(c + '(' + K.comma(N) + ') + ' + K.comma(F), K.comma(N)) + ' = ' + fr(K.comma(c * N + F), K.comma(N)) + ' = ' + A2) + ' dollars per item.', 'Numerator and denominator both have degree 1, so the horizontal asymptote is ' + m(IY + ' = ' + fr(String(c), '1') + ' = ' + c) + '.', 'As production grows, the fixed cost is spread thin and the average cost approaches $' + c + ' per item (it never goes below it).'] }, { t: 'avgcost', c: c, F: F, N: N });
      },
      function () {
        var c = pick([2, 3, 4, 5, 6]), d = pick([1, 2, 3, 4, 5]), T = c + d, x0 = pick([100, 150, 200, 250, 300, 400, 500, 600, 800, 1000]), F = x0 * d;
        var wr = []; [F / T, F / (T + c), F / c].forEach(function (v) { if (v % 1 === 0 && v !== x0) wr.push(K.comma(v) + ' loaves'); });
        return QP({ q: 'A bakery’s average cost per loaf is ' + m('<i>A</i>(<i>x</i>) = ' + fr(c + '<i>x</i> + ' + K.comma(F), IX)) + ' dollars when it bakes <i>x</i> loaves. How many loaves must it bake for the average cost to be $' + T + ' per loaf?',
          mc: mc(K.comma(x0) + ' loaves', wr, function (i) { return K.comma(x0 + 50 * (i % 2 ? (i + 1) / 2 : -i / 2)) + ' loaves'; }),
          why: ['Set ' + m(fr(c + '<i>x</i> + ' + K.comma(F), IX) + ' = ' + T) + ' and multiply both sides by <i>x</i>: ' + m(c + '<i>x</i> + ' + K.comma(F) + ' = ' + T + '<i>x</i>') + '.', m(K.comma(F) + ' = ' + (d === 1 ? '' : d) + '<i>x</i>') + ', so ' + m(IX + ' = ' + K.comma(x0)) + '.', 'Check: ' + m(fr(c + '(' + K.comma(x0) + ') + ' + K.comma(F), K.comma(x0)) + ' = ' + fr(K.comma(c * x0 + F), K.comma(x0)) + ' = ' + T) + '.'] }, { t: 'solveCost', c: c, F: F, T: T });
      }
    ]
  ];
  K.lesson('3.5', { title: 'Rational Functions: Graphs, Applications, and Models', std: 'Lial 12e · Section 3.5', levels: c35 });

  /* ================= 3.6 Variation ================= */
  function pw(e, v) { return e === 2 ? 'the square of ' + v : e === 3 ? 'the cube of ' + v : v; }
  function vv(s) { return '<i>' + s + '</i>'; }
  function vterm(s, e) { return vv(s) + (Math.abs(e) > 1 ? '<sup>' + Math.abs(e) + '</sup>' : ''); }
  function vformula(dep, sig) {
    var num = sig.filter(function (t) { return t[1] > 0; }).map(function (t) { return vterm(t[0], t[1]); }).join(''), den = sig.filter(function (t) { return t[1] < 0; }).map(function (t) { return vterm(t[0], t[1]); }).join('');
    return m(vv(dep) + ' = ' + (den ? fr('<i>k</i>' + num, den) : '<i>k</i>' + num));
  }
  function ohms(v) { return nice(v) + (nice(v) === '1' ? ' ohm' : ' ohms'); }
  function nice(v) { return K.comma(K.round(v, 2)); }
  function rc(v) { v = R(v); return v.isInt() ? K.comma(v.val()) : v.html(); }
  function cn(v) { return K.comma(v); }
  var c36 = [
    [
      function () {
        var k = pick([2, 3, 4, 5, 6, R(1, 2), R(3, 2), R(5, 2)]), x1, x2;
        do { x1 = ri(2, 12); x2 = ri(2, 20); } while (x1 === x2 || !R(k).mul(x1).isInt() || !R(k).mul(x2).isInt());
        var y1 = R(k).mul(x1).val(), y2 = R(k).mul(x2).val();
        return QP({ q: '<i>y</i> varies directly as <i>x</i>, and ' + m(IY + ' = ' + y1) + ' when ' + m(IX + ' = ' + x1) + '. Find <i>y</i> when ' + m(IX + ' = ' + x2) + '.',
          mc: mc(cn(y2), [rc(R(y1 * x1, x2)), cn(y1 + x2 - x1), cn(y1 * x2)], function (i) { return cn(y2 + i); }),
          why: ['Direct variation: ' + m(IY + ' = <i>kx</i>') + '.', m(y1 + ' = <i>k</i>(' + x1 + ')') + ', so ' + m('<i>k</i> = ' + eqs(frq(y1, x1), R(k).html())) + '.', m(IY + ' = ' + R(k).html() + '(' + x2 + ') = ' + n(y2)) + '.'] }, { t: 'vary', e: [[1, x1, x2]], y1: y1 });
      },
      function () {
        var x1, y1, x2, kk;
        do { x1 = ri(2, 12); y1 = ri(2, 15); kk = x1 * y1; x2 = pick(divisors(kk).filter(function (d) { return d >= 2 && d !== x1 && d <= 60; }).concat([0])); } while (!x2);
        var y2 = kk / x2;
        return QP({ q: '<i>y</i> varies inversely as <i>x</i>, and ' + m(IY + ' = ' + y1) + ' when ' + m(IX + ' = ' + x1) + '. Find <i>y</i> when ' + m(IX + ' = ' + x2) + '.',
          mc: mc(cn(y2), [rc(R(y1 * x2, x1)), rc(R(x2, kk)), cn(kk * x2)], function (i) { return cn(y2 + i); }),
          why: ['Inverse variation: ' + m(IY + ' = ' + fr('<i>k</i>', IX)) + '.', m('<i>k</i> = <i>xy</i> = ' + x1 + ' · ' + y1 + ' = ' + kk) + '.', m(IY + ' = ' + fr(String(kk), String(x2)) + ' = ' + n(y2)) + '. As <i>x</i> ' + (x2 > x1 ? 'grows' : 'shrinks') + ', <i>y</i> ' + (x2 > x1 ? 'shrinks' : 'grows') + '.'] }, { t: 'vary', e: [[-1, x1, x2]], y1: y1 });
      },
      function () {
        var e1 = pick([1, 2, 3]), e2 = pick([1, 2, 3]), tp = ri(0, 4), dep, sig, sent;
        if (tp === 0) { dep = 'y'; sig = [['x', e1 === 1 ? 2 : e1]]; sent = 'varies directly as ' + pw(sig[0][1], vv('x')); }
        else if (tp === 1) { dep = 'y'; sig = [['x', -e1]]; sent = 'varies inversely as ' + pw(e1, vv('x')); }
        else if (tp === 2) { dep = 'z'; sig = [['x', 1], ['y', e2]]; sent = 'varies jointly as ' + vv('x') + ' and ' + pw(e2, vv('y')); }
        else if (tp === 3) { dep = 'w'; sig = [['x', e1], ['y', -e2]]; sent = 'varies directly as ' + pw(e1, vv('x')) + ' and inversely as ' + pw(e2, vv('y')); }
        else { dep = 'V'; sig = [['x', 1], ['y', 1], ['z', -e2]]; sent = 'varies jointly as ' + vv('x') + ' and ' + vv('y') + ' and inversely as ' + pw(e2, vv('z')); }
        var key = function (s) { return s.map(function (t) { return t[0] + t[1]; }).join(','); };
        var cands = [sig.map(function (t) { return [t[0], -t[1]]; }), sig.map(function (t) { return [t[0], t[1] > 0 ? 1 : -1]; }), sig.map(function (t, i) { return i === sig.length - 1 ? [t[0], -t[1]] : t; }), sig.map(function (t, i) { return i === 0 ? [t[0], t[1] + (t[1] > 0 ? 1 : -1)] : t; })];
        var seen = {}, wr = []; seen[key(sig)] = 1;
        cands.forEach(function (s) { if (!seen[key(s)]) { seen[key(s)] = 1; wr.push(vformula(dep, s)); } });
        for (var g = 0; wr.length < 3 && g < 200; g++) { var s2 = sig.map(function (t) { return [t[0], pick([-3, -2, -1, 1, 2, 3])]; }); if (!seen[key(s2)]) { seen[key(s2)] = 1; wr.push(vformula(dep, s2)); } }
        return QP({ q: 'Which equation says “' + vv(dep) + ' ' + sent + '”? (<i>k</i> is the constant of variation.)', mc: mc(vformula(dep, sig), wr.slice(0, 3)),
          why: ['“Directly” or “jointly” puts a variable in the numerator; “inversely” puts it in the denominator.', '“The square of” and “the cube of” add exponents 2 and 3.', 'So ' + vformula(dep, sig) + '.'] }, { t: 'translate', dep: dep, sig: sig });
      }
    ],
    [
      function () {
        var k, x1, y1, x2, y2;
        do { k = pick([2, 3, 4, 5, R(1, 2), R(3, 2), R(1, 3), R(2, 3)]); x1 = ri(2, 9); y1 = ri(2, 9); x2 = ri(2, 12); y2 = ri(2, 12); } while (!R(k).mul(x1 * y1).isInt() || !R(k).mul(x2 * y2).isInt() || (x1 === x2 && y1 === y2));
        var z1 = R(k).mul(x1 * y1).val(), z2 = R(k).mul(x2 * y2).val();
        return QP({ q: '<i>z</i> varies jointly as <i>x</i> and <i>y</i>, and ' + m('<i>z</i> = ' + z1) + ' when ' + m(IX + ' = ' + x1) + ' and ' + m(IY + ' = ' + y1) + '. Find <i>z</i> when ' + m(IX + ' = ' + x2) + ' and ' + m(IY + ' = ' + y2) + '.',
          mc: mc(cn(z2), [cn(x2 * y2), rc(R(z1 * x2, x1)), rc(R(z1 * x1 * y1, x2 * y2))], function (i) { return cn(z2 + i); }),
          why: ['Joint variation: ' + m('<i>z</i> = <i>kxy</i>') + '.', m(z1 + ' = <i>k</i>(' + x1 + ')(' + y1 + ') = ' + (x1 * y1) + '<i>k</i>') + ', so ' + m('<i>k</i> = ' + R(k).html()) + '.', m('<i>z</i> = ' + R(k).html() + '(' + x2 + ')(' + y2 + ') = ' + n(z2)) + '.'] }, { t: 'vary', e: [[1, x1, x2], [1, y1, y2]], y1: z1 });
      },
      function () {
        var d1, d2, t, I1, kk, tries = 0;
        do { d1 = ri(1, 6); d2 = ri(1, 8); t = ri(1, 5); I1 = t * d2 * d2 / K.gcd(d1 * d1, d2 * d2); kk = I1 * d1 * d1; } while ((d1 === d2 || I1 > 2000 || kk % (d2 * d2)) && tries++ < 200);
        var I2 = kk / (d2 * d2);
        return QP({ q: 'The intensity of light from a lamp varies inversely as the square of the distance from the lamp. The intensity is ' + K.comma(I1) + ' lux at ' + d1 + (d1 === 1 ? ' meter' : ' meters') + '. What is the intensity at ' + d2 + (d2 === 1 ? ' meter' : ' meters') + '?',
          mc: mc(K.comma(I2) + ' lux', [nice(I1 * d1 / d2) + ' lux', nice(I1 * d2 * d2 / (d1 * d1)) + ' lux', nice(kk / d2) + ' lux'].filter(function (s) { return s !== K.comma(I2) + ' lux'; }), function (i) { return K.comma(I2 + i) + ' lux'; }),
          why: [m('<i>I</i> = ' + fr('<i>k</i>', '<i>d</i><sup>2</sup>')) + '.', m(K.comma(I1) + ' = ' + fr('<i>k</i>', d1 + '<sup>2</sup>')) + ', so ' + m('<i>k</i> = ' + K.comma(I1) + ' · ' + (d1 * d1) + ' = ' + K.comma(kk)) + '.', m('<i>I</i> = ' + fr(K.comma(kk), d2 + '<sup>2</sup>') + ' = ' + fr(K.comma(kk), String(d2 * d2)) + ' = ' + K.comma(I2)) + ' lux.'] }, { t: 'vary', e: [[-2, d1, d2]], y1: I1 });
      },
      function () {
        var k = ri(2, 12), P1 = pick([10, 20, 25, 40, 50]), u1 = ri(2, 8), P2, u2;
        do { P2 = pick([10, 20, 25, 40, 50, 80]); u2 = ri(2, 8); } while (P2 === P1 && u2 === u1);
        var T1 = P1 * u1, T2 = P2 * u2, V1 = k * u1, V2 = k * u2;
        return QP({ q: '<i>V</i> varies directly as <i>T</i> and inversely as <i>P</i>. If ' + m('<i>V</i> = ' + V1) + ' when ' + m('<i>T</i> = ' + T1) + ' and ' + m('<i>P</i> = ' + P1) + ', find <i>V</i> when ' + m('<i>T</i> = ' + T2) + ' and ' + m('<i>P</i> = ' + P2) + '.',
          mc: mc(cn(V2), [rc(R(V1 * T2 * P2, T1 * P1)), rc(R(V1 * T2, T1)), cn(k * T2 * P2)], function (i) { return cn(V2 + i); }),
          why: [m('<i>V</i> = ' + fr('<i>kT</i>', '<i>P</i>')) + ': <i>T</i> on top (direct), <i>P</i> on the bottom (inverse).', m(V1 + ' = ' + fr('<i>k</i>(' + T1 + ')', String(P1)) + ' = ' + u1 + '<i>k</i>') + ', so ' + m('<i>k</i> = ' + k) + '.', m('<i>V</i> = ' + fr(k + '(' + T2 + ')', String(P2)) + ' = ' + n(V2)) + '.'] }, { t: 'vary', e: [[1, T1, T2], [-1, P1, P2]], y1: V1 });
      },
      function () {
        var k, x1, x2;
        do { k = R(pick([1, 2, 3, 5, R(1, 2), R(1, 4), R(3, 4)])); x1 = ri(2, 10); x2 = ri(2, 12); } while (x1 === x2 || !k.mul(x1 * x1).isInt() || !k.mul(x2 * x2).isInt());
        var y1 = k.mul(x1 * x1).val(), y2 = k.mul(x2 * x2).val();
        return QP({ q: '<i>y</i> varies directly as the square of <i>x</i>, and ' + m(IY + ' = ' + y1) + ' when ' + m(IX + ' = ' + x1) + '. Find <i>y</i> when ' + m(IX + ' = ' + x2) + '.',
          mc: mc(cn(y2), [rc(R(y1 * x2, x1)), rc(R(y1 * x1 * x1, x2 * x2)), cn(y1 * x2 * x2)], function (i) { return cn(y2 + i); }),
          why: [m(IY + ' = <i>kx</i><sup>2</sup>') + '.', m(y1 + ' = <i>k</i>(' + x1 + ')<sup>2</sup> = ' + (x1 * x1) + '<i>k</i>') + ', so ' + m('<i>k</i> = ' + k.html()) + '.', m(IY + ' = ' + k.html() + '(' + x2 + ')<sup>2</sup> = ' + n(y2)) + '.'] }, { t: 'vary', e: [[2, x1, x2]], y1: y1 });
      }
    ],
    [
      function () {
        var k, v1, v2, sp = [20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70];
        do { k = R(pick([R(1, 20), R(1, 10), R(1, 25), R(3, 50), R(1, 18)])); v1 = pick(sp); v2 = pick(sp); } while (v1 === v2 || !k.mul(v1 * v1).isInt() || !k.mul(v2 * v2).isInt());
        var d1 = k.mul(v1 * v1).val(), d2 = k.mul(v2 * v2).val();
        return QP({ q: 'The braking distance of a car varies directly as the square of its speed. A car traveling ' + v1 + ' mph needs ' + d1 + ' feet to stop. How many feet does it need to stop at ' + v2 + ' mph? Round to the nearest tenth if necessary.',
          mc: mc(n(d2) + ' feet', [n(K.round(d1 * v2 / v1, 1)) + ' feet', n(K.round(d1 * v1 * v1 / (v2 * v2), 1)) + ' feet', n(d1 + v2 - v1) + ' feet'].filter(function (s) { return s !== n(d2) + ' feet'; }), function (i) { return n(d2 + 5 * i) + ' feet'; }),
          why: [m('<i>d</i> = <i>kv</i><sup>2</sup>') + '.', m('<i>k</i> = ' + fr(String(d1), v1 + '<sup>2</sup>') + ' = ' + fr(String(d1), String(v1 * v1)) + ' = ' + k.html()) + '.', m('<i>d</i> = ' + k.html() + '(' + v2 + ')<sup>2</sup> = ' + n(d2)) + ' feet.'] }, { t: 'vary', e: [[2, v1, v2]], y1: d1, round: 1 });
      },
      function () {
        var a = pick([1, 2, 3]), b = pick([1, 2]), mx = pick([2, 3]), my = pick([2, 3, 4]), word = { 2: 'doubled', 3: 'tripled', 4: 'quadrupled' };
        if (mx === my) my = mx === 2 ? 3 : 2;
        var fac2 = R(Math.pow(mx, a), Math.pow(my, b)), ans = function (r) { return '<i>z</i> is multiplied by ' + m(r.html()); };
        return QP({ q: '<i>z</i> varies directly as ' + pw(a, vv('x')) + ' and inversely as ' + pw(b, vv('y')) + '. If <i>x</i> is ' + word[mx] + ' and <i>y</i> is ' + word[my] + ', what happens to <i>z</i>?',
          mc: mc(ans(fac2), [ans(R(Math.pow(my, b), Math.pow(mx, a))), ans(R(mx, my)), ans(R(Math.pow(mx, a) * Math.pow(my, b)))], function (i) { return ans(fac2.mul(i + 1)); }),
          why: [m('<i>z</i> = ' + fr('<i>k</i>' + vterm('x', a), vterm('y', b))) + '.', 'Replace <i>x</i> with ' + m(mx + '<i>x</i>') + ' and <i>y</i> with ' + m(my + '<i>y</i>') + ': ' + m(fr('<i>k</i>(' + mx + '<i>x</i>)' + (a > 1 ? '<sup>' + a + '</sup>' : ''), '(' + my + '<i>y</i>)' + (b > 1 ? '<sup>' + b + '</sup>' : '')) + ' = ' + fr(String(Math.pow(mx, a)), String(Math.pow(my, b))) + ' · ' + fr('<i>k</i>' + vterm('x', a), vterm('y', b))) + '.', 'So <i>z</i> is multiplied by ' + m(fac2.html()) + '.'] }, { t: 'scale', a: a, b: b, mx: mx, my: my });
      },
      function () {
        var L1, d1, R1, L2, d2, kq, R2, tries = 0;
        do { L1 = pick([50, 100, 150, 200, 250, 300]); d1 = ri(1, 5); R1 = ri(2, 40); L2 = pick([50, 100, 150, 200, 300, 400, 500]); d2 = ri(1, 6); kq = R(R1 * d1 * d1, L1); R2 = kq.mul(L2).div(d2 * d2); } while ((d1 === d2 || !R(R2.n * 100, R2.d).isInt()) && tries++ < 300);
        var v2 = R2.val(), wrv = [R1 * (L2 / L1) * (d1 / d2), R1 * (L1 / L2) * (d1 * d1) / (d2 * d2), R1 * (L2 / L1) * (d2 * d2) / (d1 * d1)];
        var wr = wrv.filter(function (v) { return Math.abs(v - v2) >= 0.01; }).map(function (v) { return ohms(v); });
        return QP({ q: 'The resistance of a wire varies directly as its length and inversely as the square of its diameter. A wire ' + L1 + ' meters long with a diameter of ' + d1 + ' mm has a resistance of ' + R1 + ' ohms. Find the resistance of a wire of the same material that is ' + L2 + ' meters long with a diameter of ' + d2 + ' mm. Round to the nearest hundredth if necessary.',
          mc: mc(ohms(v2), wr, function (i) { return ohms(v2 + i); }),
          why: [m('<i>R</i> = ' + fr('<i>kL</i>', '<i>d</i><sup>2</sup>')) + '.', m(R1 + ' = ' + fr('<i>k</i>(' + L1 + ')', d1 + '<sup>2</sup>')) + ', so ' + m('<i>k</i> = ' + eqs(frq(R1 * d1 * d1, L1), kq.html())) + '.', m('<i>R</i> = ' + fr(kq.html() + '(' + L2 + ')', d2 + '<sup>2</sup>') + ' =') + ' ' + ohms(v2) + '.'] }, { t: 'vary', e: [[1, L1, L2], [-2, d1, d2]], y1: R1, round: 2 });
      }
    ]
  ];
  K.lesson('3.6', { title: 'Variation', std: 'Lial 12e · Section 3.6', levels: c36 });

  K.review('3', 'Chapter 3 Review: Polynomial and Rational Functions');
})(typeof window !== 'undefined' ? window.KCEP : globalThis.KCEP);
