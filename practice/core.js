/* KCE College Algebra Practice — core utilities, math formatting, SVG graphs, lesson registry.
   Runs in the browser and in Node (for automated accuracy tests). */
(function (root) {
  'use strict';
  var K = {};
  K.lessons = {};
  K.lesson = function (id, def) { def.id = id; K.lessons[id] = def; };

  /* ---------- random helpers ---------- */
  var rng = Math.random;
  K.setRng = function (f) { rng = f; };
  K.ri = function (a, b) { return a + Math.floor(rng() * (b - a + 1)); };          // int in [a,b]
  K.rnz = function (a, b) { var v; do { v = K.ri(a, b); } while (v === 0); return v; }; // nonzero
  K.pick = function (arr) { return arr[Math.floor(rng() * arr.length)]; };
  K.coin = function () { return rng() < 0.5; };
  K.shuffle = function (arr) { var a = arr.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(rng() * (i + 1)); var t = a[i]; a[i] = a[j]; a[j] = t; } return a; };
  K.sample = function (arr, n) { return K.shuffle(arr).slice(0, n); };
  K.gcd = function (a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = b; b = a % b; a = t; } return a || 1; };
  K.lcm = function (a, b) { return Math.abs(a * b) / K.gcd(a, b); };
  K.round = function (x, d) { var p = Math.pow(10, d || 0); return Math.round(x * p + (x >= 0 ? 1e-9 : -1e-9)) / p; };

  /* ---------- formatting ---------- */
  var MINUS = '−';
  K.MINUS = MINUS;
  // number → display string (unicode minus, trims decimals)
  K.n = function (x, dec) {
    if (typeof x !== 'number') return String(x);
    if (dec !== undefined) x = K.round(x, dec);
    var s;
    if (Math.abs(x - Math.round(x)) < 1e-9) s = String(Math.round(x));
    else s = String(K.round(x, 4)).replace(/(\.\d*?)0+$/, '$1').replace(/\.$/, '');
    if (s === '-0') s = '0';
    return s.replace(/^-/, MINUS);
  };
  // money
  K.money = function (x) {
    var neg = x < 0; x = Math.abs(x);
    var s = x.toFixed(2).replace(/\B(?=(\d{3})+(?!\d))/g, ',');
    return (neg ? MINUS : '') + '$' + s;
  };
  K.comma = function (x) { return K.n(x).replace(/\B(?=(\d{3})+(?!\d))/g, ','); };
  K.v = function (s) { return '<i>' + s + '</i>'; };       // italic variable
  K.sup = function (s) { return '<sup>' + s + '</sup>'; };
  // wraps math so it never breaks across lines
  K.m = function (s) { return '<span class="mth">' + s + '</span>'; };

  /* ---------- rationals ---------- */
  function R(n, d) {
    if (!(this instanceof R)) return new R(n, d);
    if (d === undefined) d = 1;
    if (d === 0) throw new Error('zero denominator');
    if (d < 0) { n = -n; d = -d; }
    var g = K.gcd(n, d); this.n = n / g; this.d = d / g;
  }
  R.prototype.add = function (o) { o = K.R(o); return new R(this.n * o.d + o.n * this.d, this.d * o.d); };
  R.prototype.sub = function (o) { o = K.R(o); return new R(this.n * o.d - o.n * this.d, this.d * o.d); };
  R.prototype.mul = function (o) { o = K.R(o); return new R(this.n * o.n, this.d * o.d); };
  R.prototype.div = function (o) { o = K.R(o); return new R(this.n * o.d, this.d * o.n); };
  R.prototype.neg = function () { return new R(-this.n, this.d); };
  R.prototype.eq = function (o) { o = K.R(o); return this.n === o.n && this.d === o.d; };
  R.prototype.val = function () { return this.n / this.d; };
  R.prototype.isInt = function () { return this.d === 1; };
  R.prototype.abs = function () { return new R(Math.abs(this.n), this.d); };
  R.prototype.toString = function () { return this.d === 1 ? String(this.n) : this.n + '/' + this.d; };
  // HTML: stacked fraction
  R.prototype.html = function () {
    if (this.d === 1) return K.n(this.n);
    var s = this.n < 0 ? MINUS : '';
    return s + '<span class="fr"><span class="nu">' + Math.abs(this.n) + '</span><span class="de">' + this.d + '</span></span>';
  };
  K.R = function (n, d) { return (n instanceof R) ? n : new R(n, d); };
  K.Rclass = R;
  K.f = function (n, d) { return K.R(n, d).html(); }; // quick fraction html

  // coefficient in front of a variable: 1→'', -1→'−', fractions ok. first=true omits leading +
  K.coef = function (c, first) {
    c = K.R(c);
    var neg = c.n < 0, a = c.abs();
    var body = (a.n === 1 && a.d === 1) ? '' : a.html();
    if (first) return (neg ? MINUS : '') + body;
    return (neg ? ' ' + MINUS + ' ' : ' + ') + body;
  };
  // polynomial from [[coef, varHTML], ...]; varHTML '' means constant. Skips zero terms.
  K.poly = function (terms) {
    var out = '', first = true;
    terms.forEach(function (t) {
      var c = K.R(t[0]), vp = t[1] || '';
      if (c.n === 0) return;
      if (vp === '') {
        var a = c.abs();
        out += first ? (c.n < 0 ? MINUS : '') + a.html() : (c.n < 0 ? ' ' + MINUS + ' ' : ' + ') + a.html();
      } else {
        out += K.coef(c, first) + vp;
      }
      first = false;
    });
    return out === '' ? '0' : out;
  };
  // common variable powers
  K.x = '<i>x</i>'; K.y = '<i>y</i>';
  K.xp = function (p, v) { v = v || 'x'; return p === 0 ? '' : p === 1 ? '<i>' + v + '</i>' : '<i>' + v + '</i><sup>' + p + '</sup>'; };
  // y = mx + b
  K.lineEq = function (m, b, lhs) {
    lhs = lhs === undefined ? '<i>y</i> = ' : lhs;
    return lhs + K.poly([[m, K.x], [b, '']]);
  };
  // signed constant inside parentheses: (x − 3) / (x + 3)
  K.minusH = function (v, h) { h = K.R(h); return h.n === 0 ? v : v + (h.n > 0 ? ' ' + MINUS + ' ' : ' + ') + h.abs().html(); };
  K.plusK = function (k) { k = K.R(k); return k.n === 0 ? '' : (k.n > 0 ? ' + ' : ' ' + MINUS + ' ') + k.abs().html(); };
  K.par = function (s) { return '(' + s + ')'; };
  // fraction with arbitrary HTML numerator/denominator
  K.frx = function (a, b) { return '<span class="fr"><span class="nu">' + a + '</span><span class="de">' + b + '</span></span>'; };
  // substitution display: terms [[coef, power]], value html → "3(−2)<sup>2</sup> − 4(−2) + 8"
  K.subst = function (terms, val) {
    var out = '', first = true;
    terms.forEach(function (t) {
      var c = K.R(t[0]), p = t[1]; if (c.n === 0) return;
      var a = c.abs(), body = (p > 0 && a.n === 1 && a.d === 1) ? '' : a.html();
      if (p > 0) body += '(' + val + ')' + (p > 1 ? '<sup>' + p + '</sup>' : '');
      out += first ? (c.n < 0 ? MINUS : '') + body : (c.n < 0 ? ' ' + MINUS + ' ' : ' + ') + body;
      first = false;
    });
    return out || '0';
  };
  // a(b)^x with a = 1 shown as b^x
  K.expo = function (a, b, v) { v = '<i>' + (v || 'x') + '</i>'; var bs = (typeof b === 'number') ? K.n(b) : b; return (a === 1 ? (/^[\d]+$/.test(bs) ? bs : '(' + bs + ')') : K.n(a) + '(' + bs + ')') + '<sup>' + v + '</sup>'; };
  // coefficient × (value) chain: [[3, '−2'], [−1, '4']] → "3(−2) − (4)"; cont=true starts with a sign
  K.lin = function (terms, cont) {
    var out = '', first = !cont;
    terms.forEach(function (t) {
      var c = K.R(t[0]); if (c.n === 0) return;
      var a = c.abs(), body = (a.n === 1 && a.d === 1 ? '' : a.html()) + '(' + t[1] + ')';
      out += first ? (c.n < 0 ? MINUS : '') + body : (c.n < 0 ? ' ' + MINUS + ' ' : ' + ') + body;
      first = false;
    });
    return out || '0';
  };
  K.sqrt = function (s) { return '<span class="rad">√<span class="rc">' + s + '</span></span>'; };
  K.cbrt = function (s) { return '<span class="rad"><sup class="ri">3</sup>√<span class="rc">' + s + '</span></span>'; };
  // matrix: rows = array of arrays of html/number; aug = column index where the augment bar goes; det = straight bars (determinant)
  K.mat = function (rows, aug, det) {
    var cell = function (v) { return (typeof v === 'number') ? K.n(v) : (v instanceof R ? v.html() : String(v)); };
    var h = '<span class="mx' + (det ? ' det' : '') + '"><table>';
    rows.forEach(function (r) { h += '<tr>' + r.map(function (v, j) { return '<td' + (aug !== undefined && aug !== null && j === aug ? ' class="ag"' : '') + '>' + cell(v) + '</td>'; }).join('') + '</tr>'; });
    return h + '</table></span>';
  };
  K.pt = function (x, y) { return '(' + K.R(x).html() + ', ' + K.R(y).html() + ')'; };
  K.ineqSym = { '<': '&lt;', '>': '&gt;', '<=': '≤', '>=': '≥' };
  K.flipSym = { '<': '>', '>': '<', '<=': '>=', '>=': '<=' };

  /* ---------- multiple-choice builder ---------- */
  K.strip = function (h) { return String(h).replace(/<span class="nu">(.*?)<\/span><span class="de">(.*?)<\/span>/g, '[$1]/[$2]').replace(/<sup[^>]*>(.*?)<\/sup>/g, '^$1').replace(/<[^>]+>/g, '').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/\s+/g, ' ').trim(); };
  // Plain-text version for reports: fractions as a/b, exponents as ^.
  K.plain = function (h) {
    var w0 = function (s) { s = s.replace(/<[^>]+>/g, '').trim(); return /[\s+\u2212-]/.test(s.replace(/^\u2212/, '')) ? '(' + s + ')' : s; };
    h = String(h).replace(/<span class="nu">(.*?)<\/span><span class="de">(.*?)<\/span>/g, function (m, a, b) { return w0(a) + '/' + w0(b); });
    return K.strip(String(h).replace(/<\/li>/g, ' ').replace(/<\/tr>/g, ' ; ').replace(/<br\s*\/?>/g, ' ; ').replace(/<div[^>]*>/g, ' ').replace(/<\/div>/g, ' ').replace(/<\/t[dh]>/g, ' ')).replace(/\[([^\]]+)\]\/\[([^\]]+)\]/g, function (m, a, b) { var w = function (t) { return /[\s+\u2212-]/.test(t.trim().replace(/^\u2212/, '')) ? '(' + t + ')' : t; }; return w(a) + '/' + w(b); });
  };
  function dropMath(h) {   // replace every <span class="mth">…</span> (nested spans allowed) with an ellipsis
    var out = '', i = 0, tag = '<span class="mth">';
    while (i < h.length) {
      var j = h.indexOf(tag, i); if (j < 0) { out += h.slice(i); break; }
      out += h.slice(i, j) + ' … '; var depth = 0, k = j;
      while (k < h.length) { var o = h.indexOf('<span', k), c = h.indexOf('</span>', k); if (c < 0) { k = h.length; break; } if (o >= 0 && o < c) { depth++; k = o + 5; } else { depth--; k = c + 7; if (depth === 0) break; } }
      i = k;
    }
    return out;
  }
  K.skillOf = function (q) {
    var t = K.strip(dropMath(String(q)).replace(/<table[\s\S]*?<\/table>/g, ' ').replace(/<div class="center">[\s\S]*?<\/div>/g, ' '));
    t = t.replace(/\$?\d[\d,.]*%?/g, '…').replace(/(… ?)+/g, '… ').replace(/\s+/g, ' ').trim();
    t = t.replace(/[\u2212-] ?…/g, '…').replace(/\([^()]*…[^()]*\)/g, '(…)').replace(/\[[^\]]*\]\/\[[^\]]*\]/g, '…').replace(/[a-z]\^…/g, '…').replace(/(… ?)+/g, '… ').replace(/ … ?([,.?:;])/g, ' …$1').replace(/\s+/g, ' ').trim();
    var m = t.match(/^[^?]*\?/); if (m && m[0].length < 140) t = m[0];
    return t.length > 140 ? t.slice(0, 137) + '…' : t;
  };
  // correct: html; wrong: array of html; extra(): returns more candidate wrong answers if needed
  K.mc = function (correct, wrong, extra) {
    var seen = {}, list = [];
    var key = function (h) { return K.strip(h); };
    seen[key(correct)] = 1;
    (wrong || []).forEach(function (w) { var k = key(w); if (w !== undefined && w !== null && !seen[k] && k !== '' && !/NaN|undefined|Infinity/.test(k)) { seen[k] = 1; list.push(w); } });
    var guard = 0;
    while (list.length < 3 && extra && guard++ < 200) {
      var w2 = extra(guard); var k2 = key(w2);
      if (!seen[k2] && k2 !== '' && !/NaN|undefined|Infinity/.test(k2)) { seen[k2] = 1; list.push(w2); }
    }
    list = list.slice(0, 3);
    var all = K.shuffle([correct].concat(list));
    return { ch: all, a: all.indexOf(correct) };
  };
  // numeric MC: correct number, wrong numbers, formatter; auto-fills with nearby values
  K.mcNum = function (c, wrong, fmt, spread) {
    fmt = fmt || K.n; spread = spread || Math.max(2, Math.round(Math.abs(c) * 0.25));
    return K.mc(fmt(c), (wrong || []).map(fmt), function (i) {
      var d = K.rnz(-spread, spread); return fmt(c + d * (1 + Math.floor(i / 20)));
    });
  };
  // Build a question object
  K.Q = function (o) {
    // o: {q, graph, table, mc:{ch,a}, why:[steps] | html, after}
    var why = Array.isArray(o.why) ? '<ol class="steps">' + o.why.map(function (s) { return '<li>' + s + '</li>'; }).join('') + '</ol>' : (o.why || '');
    return { q: o.q, graph: o.graph || '', ch: o.mc.ch, a: o.mc.a, why: why, ans: o.mc.ch[o.mc.a] };
  };

  /* ---------- tables ---------- */
  K.table = function (heads, rows, opts) {
    opts = opts || {};
    var h = '<table class="qt' + (opts.cls ? ' ' + opts.cls : '') + '">';
    if (heads) h += '<tr>' + heads.map(function (c) { return '<th>' + c + '</th>'; }).join('') + '</tr>';
    rows.forEach(function (r) { h += '<tr>' + r.map(function (c, i) { return (opts.rowHead && i === 0) ? '<th>' + c + '</th>' : '<td>' + c + '</td>'; }).join('') + '</tr>'; });
    return h + '</table>';
  };
  // horizontal x / y table
  K.xyTable = function (xs, ys, xl, yl) {
    xl = xl || K.x; yl = yl || K.y;
    var fmt = function (v) { return (typeof v === 'number') ? K.n(v) : (v instanceof R ? v.html() : v); };
    return '<table class="qt xy"><tr><th>' + xl + '</th>' + xs.map(function (v) { return '<td>' + fmt(v) + '</td>'; }).join('') + '</tr><tr><th>' + yl + '</th>' + ys.map(function (v) { return '<td>' + fmt(v) + '</td>'; }).join('') + '</tr></table>';
  };

  /* ---------- SVG graphs ---------- */
  var COL = { blue: '#0047BA', red: '#DB2F30', green: '#1a7a3c', gold: '#B8912F', navy: '#0A1F3D', purple: '#6B3FA0', gray: '#8a8f98' };
  K.COL = COL;
  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }
  function lbl(s) { return String(s).replace(/-/g, MINUS); }

  // Clip polygon (array of [x,y]) to half-plane a*x + b*y <= c  (Sutherland–Hodgman)
  function clipHalf(poly, a, b, c) {
    var out = [];
    for (var i = 0; i < poly.length; i++) {
      var P = poly[i], Q = poly[(i + 1) % poly.length];
      var pin = a * P[0] + b * P[1] <= c + 1e-9, qin = a * Q[0] + b * Q[1] <= c + 1e-9;
      if (pin) out.push(P);
      if (pin !== qin) {
        var t = (c - a * P[0] - b * P[1]) / (a * (Q[0] - P[0]) + b * (Q[1] - P[1]));
        out.push([P[0] + t * (Q[0] - P[0]), P[1] + t * (Q[1] - P[1])]);
      }
    }
    return out;
  }
  K.clipHalf = clipHalf;

  /* plane(o)
     o.x:[min,max], o.y:[min,max], o.step (grid), o.lab (label every), o.size px, o.xlab/o.ylab axis titles
     o.lines: [{m,b, color, dash, label}] or {vx: c} vertical
     o.fns: [{f: x=>y, color, dash, from, to}]
     o.pts: [{x,y,color,label,open}]
     o.shade: [{a,b,c, color}]   region a*x+b*y<=c (several = intersection when grouped via o.shadeAll)
     o.segs: [{x1,y1,x2,y2,color,dash}]
     o.firstQuadrant: true → only show axes from 0 */
  K._gd = [];
  function describePlane(o) {
    var v = function (x) { return K.n(K.round(K.R(x).val(), 2)); }, out = [];
    (o.lines || []).forEach(function (L) { out.push(L.vx !== undefined ? 'line x = ' + v(L.vx) : K.plain(K.lineEq(K.R(L.m), K.R(L.b))) + (L.dash ? ' (dashed)' : ' (solid)') + (L.color === COL.gray ? ' [gray guide]' : '')); });
    if ((o.fns || []).length) out.push((o.fns.length === 1 ? 'a curve' : o.fns.length + ' curves') + ((o.fns || []).some(function (F) { return F.dash; }) ? ' (dashed one is the parent graph)' : ''));
    var key = (o.pts || []).filter(function (P) { return !P.r && P.color !== COL.gray; }), data = (o.pts || []).filter(function (P) { return P.r || P.color === COL.gray; });
    if (key.length) out.push('marked point' + (key.length > 1 ? 's ' : ' ') + key.map(function (P) { return '(' + v(P.x) + ', ' + v(P.y) + ')'; }).join(', '));
    if (data.length) out.push(data.length + ' data points: ' + data.map(function (P) { return '(' + v(P.x) + ', ' + v(P.y) + ')'; }).join(' '));
    if ((o.shade || []).length) out.push('shaded region');
    return 'graph: ' + out.join('; ');
  }
  K.plane = function (o) {
    try { K._gd.push(describePlane(o)); } catch (e) { }
    var x0 = o.x[0], x1 = o.x[1], y0 = o.y[0], y1 = o.y[1];
    var W = o.w || 320, H = o.h || 320, pad = o.pad || 30, padB = o.xlab ? 40 : pad, padL = o.ylab ? 44 : pad;
    var gx = o.stepX || o.step || 1, gy = o.stepY || o.step || 1;
    var lx = o.labX || o.lab || (gx * ((x1 - x0) / gx > 12 ? 2 : 1)), ly = o.labY || o.lab || (gy * ((y1 - y0) / gy > 12 ? 2 : 1));
    var pw = W - padL - pad, ph = H - pad - padB;
    var X = function (x) { return padL + (x - x0) / (x1 - x0) * pw; };
    var Y = function (y) { return pad + (y1 - y) / (y1 - y0) * ph; };
    var s = '<svg class="graph" viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" xmlns="http://www.w3.org/2000/svg" font-family="Arial,Helvetica,sans-serif">';
    s += '<rect x="0" y="0" width="' + W + '" height="' + H + '" fill="#fff"/>';
    s += '<defs><clipPath id="cp' + (K._cp = (K._cp || 0) + 1) + '"><rect x="' + padL + '" y="' + pad + '" width="' + pw + '" height="' + ph + '"/></clipPath>' +
      '<marker id="ar' + K._cp + '" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="#333"/></marker></defs>';
    var cp = K._cp;
    // shading
    var box = [[x0, y0], [x1, y0], [x1, y1], [x0, y1]];
    (o.shade || []).forEach(function (sh) {
      var poly = box;
      (sh.parts || [sh]).forEach(function (p) { poly = clipHalf(poly, p.a, p.b, p.c); });
      if (poly.length > 2) s += '<polygon points="' + poly.map(function (p) { return X(p[0]).toFixed(1) + ',' + Y(p[1]).toFixed(1); }).join(' ') + '" fill="' + (sh.color || COL.blue) + '" fill-opacity="' + (sh.op || 0.22) + '" stroke="none"/>';
    });
    // grid
    var g = '';
    for (var gxv = Math.ceil(x0 / gx) * gx; gxv <= x1 + 1e-9; gxv += gx) g += '<line x1="' + X(gxv).toFixed(1) + '" y1="' + pad + '" x2="' + X(gxv).toFixed(1) + '" y2="' + (pad + ph) + '"/>';
    for (var gyv = Math.ceil(y0 / gy) * gy; gyv <= y1 + 1e-9; gyv += gy) g += '<line x1="' + padL + '" y1="' + Y(gyv).toFixed(1) + '" x2="' + (padL + pw) + '" y2="' + Y(gyv).toFixed(1) + '"/>';
    s += '<g stroke="#dfe3ea" stroke-width="1">' + g + '</g>';
    // axes
    var ax = (y0 <= 0 && y1 >= 0) ? Y(0) : (y0 > 0 ? pad + ph : pad);
    var ay = (x0 <= 0 && x1 >= 0) ? X(0) : (x0 > 0 ? padL : padL + pw);
    var neg = !o.firstQuadrant;
    s += '<line x1="' + (neg ? padL - 6 : padL) + '" y1="' + ax.toFixed(1) + '" x2="' + (padL + pw + 6) + '" y2="' + ax.toFixed(1) + '" stroke="#333" stroke-width="1.6" marker-end="url(#ar' + cp + ')"' + (neg ? ' marker-start="url(#ar' + cp + ')"' : '') + '/>';
    s += '<line x1="' + ay.toFixed(1) + '" y1="' + (neg ? pad + ph + 6 : pad + ph) + '" x2="' + ay.toFixed(1) + '" y2="' + (pad - 6) + '" stroke="#333" stroke-width="1.6" marker-end="url(#ar' + cp + ')"' + (neg ? ' marker-start="url(#ar' + cp + ')"' : '') + '/>';
    // tick labels
    var t = '';
    var fl = o.fmtX || K.n, fly = o.fmtY || K.n;
    for (var lxv = Math.ceil(x0 / lx) * lx; lxv <= x1 + 1e-9; lxv += lx) {
      if (Math.abs(lxv) < 1e-9 && (x0 < 0 || y0 >= 0)) continue;
      t += '<line x1="' + X(lxv).toFixed(1) + '" y1="' + (ax - 3) + '" x2="' + X(lxv).toFixed(1) + '" y2="' + (ax + 3) + '" stroke="#333"/>';
      t += '<text x="' + X(lxv).toFixed(1) + '" y="' + (ax + 15).toFixed(1) + '" text-anchor="middle" font-size="11" fill="#333">' + esc(fl(K.round(lxv, 6))) + '</text>';
    }
    for (var lyv = Math.ceil(y0 / ly) * ly; lyv <= y1 + 1e-9; lyv += ly) {
      if (Math.abs(lyv) < 1e-9) continue;
      t += '<line x1="' + (ay - 3) + '" y1="' + Y(lyv).toFixed(1) + '" x2="' + (ay + 3) + '" y2="' + Y(lyv).toFixed(1) + '" stroke="#333"/>';
      t += '<text x="' + (ay - 6).toFixed(1) + '" y="' + (Y(lyv) + 4).toFixed(1) + '" text-anchor="end" font-size="11" fill="#333">' + esc(fly(K.round(lyv, 6))) + '</text>';
    }
    if (x0 >= 0 && y0 >= 0) t += '<text x="' + (ay - 6) + '" y="' + (ax + 15) + '" text-anchor="end" font-size="11" fill="#333">0</text>';
    var tickLabels = t;
    if (o.xlab) s += '<text x="' + (padL + pw / 2) + '" y="' + (H - 6) + '" text-anchor="middle" font-size="12" font-weight="bold" fill="#0A1F3D">' + esc(o.xlab) + '</text>';
    if (o.ylab) s += '<text transform="translate(13,' + (pad + ph / 2) + ') rotate(-90)" text-anchor="middle" font-size="12" font-weight="bold" fill="#0A1F3D">' + esc(o.ylab) + '</text>';
    if (!o.noXY) {
      if (!o.xlab) s += '<text x="' + (padL + pw + 4) + '" y="' + (ax - 8) + '" font-size="13" font-style="italic" fill="#333" text-anchor="end">x</text>';
      if (!o.ylab) s += '<text x="' + (ay + 8) + '" y="' + (pad + 4) + '" font-size="13" font-style="italic" fill="#333">y</text>';
    }
    // drawable content (clipped)
    var c = '<g clip-path="url(#cp' + cp + ')">';
    var lineLabs = '';
    (o.lines || []).forEach(function (L) {
      var col = L.color || COL.blue, da = L.dash ? ' stroke-dasharray="7 5"' : '';
      if (L.vx !== undefined) c += '<line x1="' + X(L.vx) + '" y1="' + pad + '" x2="' + X(L.vx) + '" y2="' + (pad + ph) + '" stroke="' + col + '" stroke-width="2.4"' + da + '/>';
      else {
        var m = K.R(L.m).val(), b = K.R(L.b).val();
        var xa = L.from !== undefined ? L.from : x0 - 1, xb = L.to !== undefined ? L.to : x1 + 1;
        c += '<line x1="' + X(xa).toFixed(1) + '" y1="' + Y(m * xa + b).toFixed(1) + '" x2="' + X(xb).toFixed(1) + '" y2="' + Y(m * xb + b).toFixed(1) + '" stroke="' + col + '" stroke-width="2.4"' + da + ' stroke-linecap="round"/>';
      }
      if (L.label && L.vx === undefined) {
        var lm = K.R(L.m).val(), lb = K.R(L.b).val(), xe = x1;
        if (lm > 0) xe = Math.min(x1, (y1 - lb) / lm); else if (lm < 0) xe = Math.min(x1, (y0 - lb) / lm);
        xe -= (x1 - x0) * 0.05;
        lineLabs += '<text x="' + (X(xe) - 4).toFixed(1) + '" y="' + (Y(lm * xe + lb) - 8).toFixed(1) + '" font-size="12.5" font-weight="bold" fill="' + col + '" text-anchor="end" paint-order="stroke" stroke="#fff" stroke-width="3">' + esc(L.label) + '</text>';
      }
    });
    (o.fns || []).forEach(function (F) {
      var col = F.color || COL.blue, da = F.dash ? ' stroke-dasharray="7 5"' : '';
      var xa = F.from !== undefined ? F.from : x0, xb = F.to !== undefined ? F.to : x1, n = 240, d = '';
      var pen = false;
      for (var i = 0; i <= n; i++) {
        var xv = xa + (xb - xa) * i / n, yv = F.f(xv);
        if (!isFinite(yv) || yv > y1 + (y1 - y0) * 2 || yv < y0 - (y1 - y0) * 2) { pen = false; continue; }
        d += (pen ? 'L' : 'M') + X(xv).toFixed(1) + ',' + Y(yv).toFixed(1); pen = true;
      }
      c += '<path d="' + d + '" fill="none" stroke="' + col + '" stroke-width="2.4"' + da + ' stroke-linejoin="round"/>';
    });
    (o.segs || []).forEach(function (S) {
      c += '<line x1="' + X(S.x1).toFixed(1) + '" y1="' + Y(S.y1).toFixed(1) + '" x2="' + X(S.x2).toFixed(1) + '" y2="' + Y(S.y2).toFixed(1) + '" stroke="' + (S.color || COL.blue) + '" stroke-width="' + (S.w || 2.4) + '"' + (S.dash ? ' stroke-dasharray="6 4"' : '') + ' stroke-linecap="round"/>';
    });
    c += '</g>';
    s += c + tickLabels + lineLabs;
    (o.pts || []).forEach(function (P) {
      var col = P.color || COL.navy;
      s += '<circle cx="' + X(P.x).toFixed(1) + '" cy="' + Y(P.y).toFixed(1) + '" r="' + (P.r || 4.2) + '" fill="' + (P.open ? '#fff' : col) + '" stroke="' + col + '" stroke-width="2"/>';
      if (P.label) {
        var yr = o.y[1] - o.y[0], xr = o.x[1] - o.x[0];
        var nearTop = P.y > o.y[1] - yr * 0.1, nearRight = P.x > o.x[1] - xr * 0.22;
        var anc = P.anchor || (nearRight ? 'end' : 'start');
        var dx = P.dx !== undefined ? P.dx : (anc === 'end' ? -7 : 7), dy = P.dy !== undefined ? P.dy : (nearTop ? 17 : -7);
        s += '<text x="' + (X(P.x) + dx).toFixed(1) + '" y="' + (Y(P.y) + dy).toFixed(1) + '" font-size="11.5" font-weight="bold" fill="' + col + '" text-anchor="' + anc + '" paint-order="stroke" stroke="#fff" stroke-width="3">' + esc(lbl(P.label)) + '</text>';
      }
    });
    (o.texts || []).forEach(function (T) {
      s += '<text x="' + X(T.x).toFixed(1) + '" y="' + Y(T.y).toFixed(1) + '" font-size="' + (T.size || 12) + '" font-weight="bold" fill="' + (T.color || COL.navy) + '" text-anchor="' + (T.anchor || 'middle') + '" paint-order="stroke" stroke="#fff" stroke-width="3">' + esc(lbl(T.t)) + '</text>';
    });
    return s + '</svg>';
  };

  // number line: o.min,o.max,o.step; o.pts:[{x,open}]; o.rays:[{from,dir:+1/-1}], o.segs:[{a,b}]
  K.numberLine = function (o) {
    try { K._gd.push('number line: ' + (o.pts || []).map(function (P) { return (P.open ? 'open' : 'closed') + ' dot at ' + K.n(K.R(P.x).val()); }).join(', ') + (o.rays || []).map(function (r) { return ', arrow pointing ' + (r.dir > 0 ? 'right' : 'left'); }).join('') + (o.segs || []).map(function (g) { return ', segment from ' + K.n(K.R(g.a !== undefined ? g.a : g[0]).val()) + ' to ' + K.n(K.R(g.b !== undefined ? g.b : g[1]).val()); }).join('')); } catch (e) { }
    var W = o.w || 420, H = 70, pad = 26, min = o.min, max = o.max, st = o.step || 1;
    var X = function (x) { return pad + (x - min) / (max - min) * (W - 2 * pad); };
    var yb = 30, col = COL.blue;
    var s = '<svg class="graph nl" viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" xmlns="http://www.w3.org/2000/svg" font-family="Arial,Helvetica,sans-serif"><rect width="' + W + '" height="' + H + '" fill="#fff"/>';
    s += '<defs><marker id="nla" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="#333"/></marker><marker id="nlb" viewBox="0 0 10 10" refX="7" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="' + col + '"/></marker></defs>';
    s += '<line x1="' + (pad - 14) + '" y1="' + yb + '" x2="' + (W - pad + 14) + '" y2="' + yb + '" stroke="#333" stroke-width="1.6" marker-start="url(#nla)" marker-end="url(#nla)"/>';
    for (var v = min; v <= max + 1e-9; v += st) {
      s += '<line x1="' + X(v).toFixed(1) + '" y1="' + (yb - 6) + '" x2="' + X(v).toFixed(1) + '" y2="' + (yb + 6) + '" stroke="#333"/>';
      s += '<text x="' + X(v).toFixed(1) + '" y="' + (yb + 22) + '" font-size="12" text-anchor="middle" fill="#333">' + esc(K.n(K.round(v, 6))) + '</text>';
    }
    (o.segs || []).forEach(function (g) { s += '<line x1="' + X(g.a) + '" y1="' + yb + '" x2="' + X(g.b) + '" y2="' + yb + '" stroke="' + col + '" stroke-width="5"/>'; });
    (o.rays || []).forEach(function (r) { var xe = r.dir > 0 ? W - pad + 10 : pad - 10; s += '<line x1="' + X(r.from) + '" y1="' + yb + '" x2="' + xe + '" y2="' + yb + '" stroke="' + col + '" stroke-width="5" marker-end="url(#nlb)"/>'; });
    (o.pts || []).forEach(function (p) { s += '<circle cx="' + X(p.x).toFixed(1) + '" cy="' + yb + '" r="6.5" fill="' + (p.open ? '#fff' : col) + '" stroke="' + col + '" stroke-width="2.6"/>'; });
    return s + '</svg>';
  };

  // box plot: five = [min,q1,med,q3,max]; o.min,o.max,o.step, o.title
  K.boxPlot = function (o) {
    K._gd.push('box plot' + (o.title ? ' (' + o.title + ')' : '') + ': min ' + o.five[0] + ', Q1 ' + o.five[1] + ', median ' + o.five[2] + ', Q3 ' + o.five[3] + ', max ' + o.five[4]);
    var W = 420, H = o.title ? 120 : 104, pad = 26, f = o.five, top = o.title ? 28 : 12;
    var X = function (x) { return pad + (x - o.min) / (o.max - o.min) * (W - 2 * pad); };
    var yb = top + 56, mid = top + 22;
    var s = '<svg class="graph" viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" xmlns="http://www.w3.org/2000/svg" font-family="Arial,Helvetica,sans-serif"><rect width="' + W + '" height="' + H + '" fill="#fff"/>';
    if (o.title) s += '<text x="' + W / 2 + '" y="16" text-anchor="middle" font-size="12.5" font-weight="bold" fill="#0A1F3D">' + esc(o.title) + '</text>';
    s += '<line x1="' + X(f[0]) + '" y1="' + mid + '" x2="' + X(f[1]) + '" y2="' + mid + '" stroke="' + COL.navy + '" stroke-width="2"/>';
    s += '<line x1="' + X(f[3]) + '" y1="' + mid + '" x2="' + X(f[4]) + '" y2="' + mid + '" stroke="' + COL.navy + '" stroke-width="2"/>';
    s += '<rect x="' + X(f[1]) + '" y="' + (mid - 14) + '" width="' + (X(f[3]) - X(f[1])) + '" height="28" fill="#eef2fb" stroke="' + COL.navy + '" stroke-width="2"/>';
    s += '<line x1="' + X(f[2]) + '" y1="' + (mid - 14) + '" x2="' + X(f[2]) + '" y2="' + (mid + 14) + '" stroke="' + COL.red + '" stroke-width="3"/>';
    [0, 4].forEach(function (i) { s += '<line x1="' + X(f[i]) + '" y1="' + (mid - 9) + '" x2="' + X(f[i]) + '" y2="' + (mid + 9) + '" stroke="' + COL.navy + '" stroke-width="2"/>'; });
    s += '<line x1="' + (pad - 8) + '" y1="' + yb + '" x2="' + (W - pad + 8) + '" y2="' + yb + '" stroke="#333" stroke-width="1.4"/>';
    for (var v = o.min; v <= o.max + 1e-9; v += o.step) {
      s += '<line x1="' + X(v) + '" y1="' + (yb - 4) + '" x2="' + X(v) + '" y2="' + (yb + 4) + '" stroke="#333"/><text x="' + X(v) + '" y="' + (yb + 18) + '" font-size="11.5" text-anchor="middle" fill="#333">' + esc(K.n(v)) + '</text>';
    }
    return s + '</svg>';
  };

  // dot plot: values array; o.min,o.max (integers)
  K.dotPlot = function (o) {
    K._gd.push('dot plot' + (o.title ? ' (' + o.title + ')' : '') + ': ' + o.vals.slice().sort(function (a, b) { return a - b; }).join(', '));
    var counts = {}, maxc = 0;
    o.vals.forEach(function (v) { counts[v] = (counts[v] || 0) + 1; maxc = Math.max(maxc, counts[v]); });
    var W = 420, pad = 26, r = 7, H = 50 + maxc * 17 + (o.title ? 18 : 0), top = o.title ? 20 : 4;
    var X = function (x) { return pad + (x - o.min) / (o.max - o.min) * (W - 2 * pad); };
    var yb = H - 30;
    var s = '<svg class="graph" viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" xmlns="http://www.w3.org/2000/svg" font-family="Arial,Helvetica,sans-serif"><rect width="' + W + '" height="' + H + '" fill="#fff"/>';
    if (o.title) s += '<text x="' + W / 2 + '" y="14" text-anchor="middle" font-size="12.5" font-weight="bold" fill="#0A1F3D">' + esc(o.title) + '</text>';
    s += '<line x1="' + (pad - 8) + '" y1="' + yb + '" x2="' + (W - pad + 8) + '" y2="' + yb + '" stroke="#333" stroke-width="1.4"/>';
    for (var v = o.min; v <= o.max; v++) {
      s += '<line x1="' + X(v) + '" y1="' + (yb - 4) + '" x2="' + X(v) + '" y2="' + (yb + 4) + '" stroke="#333"/><text x="' + X(v) + '" y="' + (yb + 18) + '" font-size="11.5" text-anchor="middle" fill="#333">' + esc(K.n(v)) + '</text>';
      for (var i = 0; i < (counts[v] || 0); i++) s += '<circle cx="' + X(v) + '" cy="' + (yb - 12 - i * 17) + '" r="' + r + '" fill="' + COL.blue + '"/>';
    }
    return s + '</svg>';
  };

  // bar/histogram: o.labels, o.vals, o.hist (touching bars), o.ymax, o.ystep, o.xlab, o.ylab
  K.bars = function (o) {
    K._gd.push((o.hist ? 'histogram' : 'bar graph') + ': ' + o.labels.map(function (l, i) { return l + ' → ' + o.vals[i]; }).join(', '));
    var W = 420, H = 260, padL = 50, padR = 14, padT = 16, padB = o.xlab ? 50 : 34;
    var n = o.vals.length, pw = W - padL - padR, ph = H - padT - padB;
    var ymax = o.ymax, ys = o.ystep;
    var Y = function (v) { return padT + ph - v / ymax * ph; };
    var s = '<svg class="graph" viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" xmlns="http://www.w3.org/2000/svg" font-family="Arial,Helvetica,sans-serif"><rect width="' + W + '" height="' + H + '" fill="#fff"/>';
    for (var v = 0; v <= ymax + 1e-9; v += ys) s += '<line x1="' + padL + '" y1="' + Y(v) + '" x2="' + (W - padR) + '" y2="' + Y(v) + '" stroke="#e3e6ec"/><text x="' + (padL - 6) + '" y="' + (Y(v) + 4) + '" font-size="11" text-anchor="end" fill="#333">' + v + '</text>';
    var bw = pw / n, gap = o.hist ? 0 : bw * 0.25;
    o.vals.forEach(function (val, i) {
      s += '<rect x="' + (padL + i * bw + gap / 2).toFixed(1) + '" y="' + Y(val).toFixed(1) + '" width="' + (bw - gap).toFixed(1) + '" height="' + (padT + ph - Y(val)).toFixed(1) + '" fill="' + COL.blue + '" fill-opacity=".8" stroke="' + COL.navy + '" stroke-width="1"/>';
      s += '<text x="' + (padL + i * bw + bw / 2).toFixed(1) + '" y="' + (padT + ph + 16) + '" font-size="11" text-anchor="middle" fill="#333">' + esc(o.labels[i]) + '</text>';
    });
    s += '<line x1="' + padL + '" y1="' + (padT + ph) + '" x2="' + (W - padR) + '" y2="' + (padT + ph) + '" stroke="#333" stroke-width="1.4"/><line x1="' + padL + '" y1="' + padT + '" x2="' + padL + '" y2="' + (padT + ph) + '" stroke="#333" stroke-width="1.4"/>';
    if (o.xlab) s += '<text x="' + (padL + pw / 2) + '" y="' + (H - 8) + '" text-anchor="middle" font-size="12" font-weight="bold" fill="#0A1F3D">' + esc(o.xlab) + '</text>';
    if (o.ylab) s += '<text transform="translate(14,' + (padT + ph / 2) + ') rotate(-90)" text-anchor="middle" font-size="12" font-weight="bold" fill="#0A1F3D">' + esc(o.ylab) + '</text>';
    return s + '</svg>';
  };

  // Unit review = every lesson in the unit, level by level
  K.review = function (u, title) {
    var ids = Object.keys(K.lessons).filter(function (i) { return i.split('.')[0] === String(u); });
    K.lesson('R' + u, { title: title, std: 'Every lesson in Chapter ' + u + ', mixed together', levels: [0, 1, 2].map(function (lv) { var a = []; ids.forEach(function (id) { a = a.concat(K.lessons[id].levels[lv]); }); return a; }) });
  };

  /* ---------- question selection ---------- */
  // Generate a question for lesson id at level (1..3). Avoids repeating recent stems.
  K.make = function (id, level, recent) {
    var L = K.lessons[id]; if (!L) throw new Error('no lesson ' + id);
    var gens = L.levels[level - 1];
    recent = recent || [];
    var q, tries = 0;
    do {
      var gi = K.ri(0, gens.length - 1), g = gens[gi];
      K._gd = [];
      q = g();
      q.gi = gi; q.gdesc = q.graph ? K._gd.slice(-((q.graph.match(/<svg/g) || []).length || 1)).join(' | ') : '';
      q.key = K.strip(q.q).slice(0, 160) + '|' + K.strip(q.ans);
      tries++;
    } while (recent.indexOf(q.key) >= 0 && tries < 25);
    return q;
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = K;
  root.KCEP = K;
})(typeof window !== 'undefined' ? window : globalThis);
