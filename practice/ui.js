/* KCE College Algebra Practice — page UI. Requires core.js and the lesson's generator file. */
(function () {
  'use strict';
  var K = window.KCEP;
  var FORM = 'https://formspree.io/f/xrpbqdra';
  var NEED = 5; // first-try correct answers in a row to unlock the next level
  var LV = ['Level 1 · Warm-Up', 'Level 2 · Building', 'Level 3 · Exam Challenge'];
  var LVS = ['Warm-Up', 'Building', 'Exam Challenge'];
  var LETTERS = ['A', 'B', 'C', 'D'];

  function $(id) { return document.getElementById(id); }
  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;'); }
  function store(k, v) { try { if (v === undefined) return JSON.parse(localStorage.getItem(k) || 'null'); localStorage.setItem(k, JSON.stringify(v)); } catch (e) { return null; } }

  K.start = function (id) {
    var L = K.lessons[id];
    var S = {
      id: id, name: '', level: 1, unlocked: 1, cleared3: false, streak: 0, best: 0,
      n: 0, recent: [], log: [], picks: [], q: null, tries: 0, done: false, started: Date.now(),
      per: [{ a: 0, f: 0, s: 0, m: 0 }, { a: 0, f: 0, s: 0, m: 0 }, { a: 0, f: 0, s: 0, m: 0 }],
      dirty: false
    };
    K._S = S; // exposed for automated testing
    var root = $('app');
    var isReview = /review/i.test(L.title);
    var label = isReview ? 'Chapter ' + id.slice(1) + ' Review Practice' : 'Lesson ' + id + ' Practice';
    document.title = 'KCE College Algebra — ' + label;

    root.innerHTML =
      '<div class="masthead"><div class="mast-row"><div class="brand"><div class="kc"><span class="inner">KC</span></div><div><div class="wordmark">KingCretot Experience</div><div class="course-tag">College Algebra · Practice</div></div></div><div class="lesson-tag">' + esc(label) + '</div></div></div>' +
      '<div class="tricolor"><div class="tri-b"></div><div class="tri-g"></div><div class="tri-r"></div></div>' +
      '<div id="pbar" class="pbar" style="display:none"></div>' +
      '<div class="stage" id="stage"></div>' +
      '<div class="footer-brand">KINGCRETOT EXPERIENCE · COLLEGE ALGEBRA PRACTICE · <a href="../index.html">BACK TO THE COURSE</a></div>';

    /* ---------- gate ---------- */
    function gate() {
      $('stage').innerHTML =
        '<p class="eyebrow">' + (isReview ? 'Chapter Review Practice' : 'Lesson ' + esc(id) + ' · Practice Questions') + '</p>' +
        '<h1 class="title">' + esc(L.title) + '</h1>' +
        '<div class="std">' + esc(L.std) + '</div>' +
        '<div class="card warm"><p style="margin-bottom:8px"><b>How practice works</b></p><ul class="how">' +
        '<li>Questions start easy and get harder, up to college exam level.</li>' +
        '<li>Get <b>' + NEED + ' in a row right on your first try</b> to unlock the next level.</li>' +
        '<li>You get <b>2 tries</b> on every question. If you miss it twice, you’ll see the correct answer and the logic behind it.</li>' +
        '<li>Your results are sent to KingCretot Experience so your progress can be followed.</li></ul>' +
        '<div class="levels-preview">' + [0, 1, 2].map(function (i) { return '<div class="lvp"><b>Level ' + (i + 1) + '</b><span>' + LVS[i] + '</span></div>'; }).join('') + '</div></div>' +
        '<div class="card name-wrap"><label for="nm">Enter your first and last name to begin</label>' +
        '<input id="nm" type="text" autocomplete="name" placeholder="First and last name" maxlength="60">' +
        '<div class="err" id="nmerr"></div>' +
        '<div class="row"><button class="btn go" id="startb" disabled>Start practice →</button></div></div>';
      var nm = $('nm'), b = $('startb');
      var ok = function () { return nm.value.trim().length >= 2; };
      nm.addEventListener('input', function () { b.disabled = !ok(); if (ok()) $('nmerr').textContent = ''; });
      nm.addEventListener('keydown', function (e) { if (e.key === 'Enter') go(); });
      b.addEventListener('click', go);
      function go() {
        if (!ok()) { $('nmerr').textContent = 'Please type your name before you start.'; nm.focus(); return; }
        S.name = nm.value.trim().replace(/\s+/g, ' ');
        var saved = store('kcep:' + id + ':' + S.name.toLowerCase());
        if (saved) { S.unlocked = Math.max(1, Math.min(3, saved.u || 1)); S.cleared3 = !!saved.c; S.level = S.unlocked; }
        bar(); next();
      }
      setTimeout(function () { nm.focus(); }, 50);
    }

    /* ---------- header bar ---------- */
    function bar() {
      var p = $('pbar'); p.style.display = 'flex';
      var tabs = [1, 2, 3].map(function (l) {
        var locked = l > S.unlocked, done = l < S.unlocked || (l === 3 && S.cleared3);
        return '<button class="tab' + (l === S.level ? ' on' : '') + (locked ? ' locked' : '') + '" data-l="' + l + '"' + (locked ? ' disabled title="Locked: get ' + NEED + ' in a row on Level ' + (l - 1) + '"' : '') + '>' + (locked ? '<span class="lock">🔒</span> ' : '') + 'Level ' + l + (done ? ' <span class="ck">✓</span>' : '') + '</button>';
      }).join('');
      var dots = ''; for (var i = 0; i < NEED; i++) dots += '<span class="dot' + (i < Math.min(S.streak, NEED) ? ' f' : '') + '"></span>';
      var tot = S.per[0].a + S.per[1].a + S.per[2].a, ft = S.per[0].f + S.per[1].f + S.per[2].f;
      p.innerHTML = '<div class="who">Practicing: <b>' + esc(S.name) + '</b></div><div class="tabs">' + tabs + '</div>' +
        '<div class="streak">Streak <span class="dots">' + dots + '</span></div><div class="stats">' + ft + ' of ' + tot + ' right on 1st try</div>';
      Array.prototype.forEach.call(p.querySelectorAll('.tab'), function (t) {
        t.addEventListener('click', function () { var l = +t.getAttribute('data-l'); if (l <= S.unlocked && l !== S.level) { S.level = l; S.streak = 0; bar(); next(); } });
      });
    }

    /* ---------- question ---------- */
    function next() {
      var q;
      for (var t = 0; t < 6 && !q; t++) { try { q = K.make(id, S.level, S.recent); } catch (e) { if (window.console) console.error('KCEP generator error: ' + e.message + ' ' + (e.stack || '')); } }
      if (!q) { $('stage').innerHTML = '<p>Sorry, something went wrong loading a question. Please refresh the page.</p>'; return; }
      S.q = q; S.tries = 0; S.n++; S.picks = [];
      S.recent.push(q.key); if (S.recent.length > 20) S.recent.shift();
      var h = '<div class="qhead"><div class="qnum">Question ' + S.n + '</div><div class="lvname">' + LV[S.level - 1] + '</div></div>' +
        '<div class="card"><div class="qtext">' + q.q + '</div>' + (q.graph ? '<div class="gwrap">' + q.graph + '</div>' : '') +
        '<div class="choices">' + q.ch.map(function (c, i) { return '<button class="ch" data-i="' + i + '"><span class="lt">' + LETTERS[i] + '</span><span class="cv">' + c + '</span></button>'; }).join('') + '</div>' +
        '<div class="fb" id="fb"></div><div class="next-row" id="nr"><button class="btn go" id="nextb">Next question →</button></div></div>' +
        '<div class="finish"><span class="sendst" id="sendst"></span><button class="btn ghost" id="finb">I’m done — send my results</button></div>';
      $('stage').innerHTML = h;
      Array.prototype.forEach.call(document.querySelectorAll('.ch'), function (b) { b.addEventListener('click', function () { answer(+b.getAttribute('data-i'), b); }); });
      $('nextb').addEventListener('click', afterQ);
      $('finb').addEventListener('click', finish);
      window.scrollTo(0, 0);
    }

    function lockAll() { Array.prototype.forEach.call(document.querySelectorAll('.ch'), function (b) { b.disabled = true; }); }
    function answer(i, btn) {
      if (S.qdone) return;
      var q = S.q, per = S.per[S.level - 1], fb = $('fb');
      S.tries++; S.dirty = true; S.picks.push(i);
      if (i === q.a) {
        btn.classList.add('right'); lockAll();
        Array.prototype.forEach.call(document.querySelectorAll('.ch'), function (b) { if (!b.classList.contains('right') && !b.classList.contains('wrong')) b.classList.add('dim'); });
        per.a++;
        if (S.tries === 1) { per.f++; S.streak++; S.best = Math.max(S.best, S.streak); }
        else { per.s++; S.streak = 0; }
        fb.className = 'fb good show';
        fb.innerHTML = '<h4>' + (S.tries === 1 ? 'Correct! ✔' : 'Correct on your second try.') + '</h4>' + (S.tries === 1 ? '' : '<p style="margin:0 0 6px;font-size:15px">Second-try answers don’t count toward your streak, but you’re learning. Here’s the logic:</p>') + q.why;
        done();
      } else if (S.tries === 1) {
        btn.classList.add('wrong'); btn.disabled = true;
        fb.className = 'fb try show';
        fb.innerHTML = '<h4>Not quite. Try once more.</h4><p style="margin:0;font-size:15px">Look at the question again carefully. You have one try left.</p>';
      } else {
        btn.classList.add('wrong'); lockAll();
        var rb = document.querySelector('.ch[data-i="' + q.a + '"]'); rb.classList.add('right');
        per.a++; per.m++; S.streak = 0;
        fb.className = 'fb bad show';
        fb.innerHTML = '<h4>Here’s the answer and the logic</h4><div class="ansline">The correct answer is ' + LETTERS[q.a] + ': <span>' + q.ans + '</span></div>' + q.why;
        done();
      }
    }
    function logQ() {
      var q = S.q, res = S.tries === 1 && S.picks[0] === q.a ? 'right' : S.picks[S.picks.length - 1] === q.a ? 'second' : 'missed';
      S.log.push({ n: S.n, lv: S.level, gi: q.gi, res: res, skill: K.skillOf(q.q), q: K.plain(q.q), g: q.gdesc || '', picks: S.picks.map(function (i) { return LETTERS[i] + ') ' + K.plain(q.ch[i]); }), right: LETTERS[q.a] + ') ' + K.plain(q.ans), why: K.plain(q.why) });
    }
    function done() {
      logQ();
      S.qdone = true;
      bar();
      $('nr').classList.add('show');
      setTimeout(function () { var el = $('fb'); if (el && el.scrollIntoView) el.scrollIntoView({ behavior: 'smooth', block: 'nearest' }); }, 60);
    }
    function afterQ() {
      S.qdone = false;
      if (S.streak >= NEED) {
        S.streak = 0;
        if (S.level < 3 && S.level === S.unlocked) {
          S.unlocked++; save(); send('Level ' + S.unlocked + ' unlocked');
          return celebrate(S.unlocked);
        }
        if (S.level === 3 && !S.cleared3) {
          S.cleared3 = true; save(); send('Mastered (Level 3 cleared)');
          return mastered();
        }
      }
      next();
    }
    function save() { store('kcep:' + id + ':' + S.name.toLowerCase(), { u: S.unlocked, c: S.cleared3 }); }

    function celebrate(l) {
      bar();
      $('stage').innerHTML = '<div class="card banner"><div class="big">🔓</div><h2>Level ' + l + ' unlocked!</h2><p>You got ' + NEED + ' in a row right on the first try. Nice work, ' + esc(S.name.split(' ')[0]) + '.</p><p><b>' + LV[l - 1] + '</b> is next, and the questions get harder.</p><div class="row" style="justify-content:center;margin-top:10px"><button class="btn go" id="gol">Start Level ' + l + ' →</button><button class="btn ghost" id="stay">Keep practicing Level ' + (l - 1) + '</button></div></div>' + finishRow();
      $('gol').addEventListener('click', function () { S.level = l; bar(); next(); });
      $('stay').addEventListener('click', function () { next(); });
      $('finb').addEventListener('click', finish);
    }
    function mastered() {
      bar();
      $('stage').innerHTML = '<div class="card banner"><div class="big">🏆</div><h2>You mastered this practice set!</h2><p>' + NEED + ' Exam Challenge questions in a row on the first try. Outstanding, ' + esc(S.name.split(' ')[0]) + '.</p><p>Your result has been sent to KingCretot Experience. You can keep practicing any level.</p><div class="row" style="justify-content:center;margin-top:10px"><button class="btn go" id="more">Keep practicing →</button><a class="btn ghost" href="../index.html" style="text-decoration:none">Back to the course</a></div></div>' + finishRow();
      $('more').addEventListener('click', function () { next(); });
      $('finb').addEventListener('click', finish);
    }
    function finishRow() { return '<div class="finish"><span class="sendst" id="sendst"></span><button class="btn ghost" id="finb">I’m done — send my results</button></div>'; }

    function finish() {
      send('Finished practice', true);
    }

    /* ---------- Formspree ---------- */
    function payload(event) {
      var tot = 0, ft = 0;
      S.per.forEach(function (p) { tot += p.a; ft += p.f; });
      var perTxt = S.per.map(function (p, i) { return 'Level ' + (i + 1) + ': ' + p.a + ' answered, ' + p.f + ' right on 1st try, ' + p.s + ' on 2nd try, ' + p.m + ' missed'; }).join(' | ');
      var reached = S.cleared3 ? 'Level 3 cleared' : 'Level ' + S.unlocked;
      return {
        program: 'KCE College Algebra Practice',
        student: S.name,
        module: 'college-algebra-practice-' + (isReview ? 'chapter-' + id.slice(1).toLowerCase() + '-review' : id.replace('.', '-').toLowerCase()),
        lesson: isReview ? L.title + ' (Practice)' : label + ': ' + L.title,
        event: event,
        score: tot ? Math.round(ft / tot * 100) : 0,
        mastered: S.cleared3 ? 'yes' : 'no',
        rawScore: ft + ' right on 1st try / ' + tot + ' answered',
        levelReached: reached,
        byLevel: perTxt,
        bestStreak: S.best,
        minutes: Math.max(1, Math.round((Date.now() - S.started) / 60000)),
        needsReview: review(),
        missedQuestions: missedTxt(),
        questionLog: S.log.map(function (e) { return 'Q' + e.n + ' (L' + e.lv + ') ' + (e.res === 'right' ? '✓' : e.res === 'second' ? '2nd try' : '✗ missed'); }).join(', ') || 'none'
      };
    }
    // Skills the student struggled with, grouped by question type.
    function review() {
      var g = {}, order = [];
      S.log.forEach(function (e) { var k = e.lv + ':' + e.skill; if (!g[k]) { g[k] = { lv: e.lv, skill: e.skill, tot: 0, bad: 0, miss: 0 }; order.push(k); } g[k].tot++; if (e.res !== 'right') g[k].bad++; if (e.res === 'missed') g[k].miss++; });
      var out = order.map(function (k) { return g[k]; }).filter(function (x) { return x.bad; }).sort(function (a, b) { return b.bad / b.tot - a.bad / a.tot || b.bad - a.bad; });
      if (!out.length) return S.log.length ? 'Nothing to reteach — every question was right on the first try.' : 'No questions answered yet.';
      return out.map(function (x) { return '• Level ' + x.lv + ' — ' + x.skill + ' — not right on 1st try ' + x.bad + ' of ' + x.tot + (x.miss ? ' (' + x.miss + ' missed both tries)' : ''); }).join('\n');
    }
    // Every question that was not right on the first try, with what the student chose.
    function missedTxt() {
      var bad = S.log.filter(function (e) { return e.res !== 'right'; });
      if (!bad.length) return 'None.';
      var shown = bad.slice(-25), out = shown.map(function (e) {
        return 'Q' + e.n + ' (Level ' + e.lv + ', ' + (e.res === 'second' ? 'correct on 2nd try' : 'MISSED both tries') + ')\n' +
          'Question: ' + e.q + (e.g ? '\n' + e.g.charAt(0).toUpperCase() + e.g.slice(1) : '') + '\n' +
          'Student chose: ' + e.picks.join('  then  ') + '\n' +
          'Correct answer: ' + e.right + '\n' +
          'Logic shown: ' + e.why;
      });
      return (bad.length > shown.length ? '(Showing the last ' + shown.length + ' of ' + bad.length + ')\n\n' : '') + out.join('\n\n');
    }
    function send(event, user) {
      var st = $('sendst');
      var tot = S.per[0].a + S.per[1].a + S.per[2].a;
      if (user && tot === 0) { if (st) st.textContent = 'Answer at least one question first.'; return; }
      if (st) st.textContent = 'Sending your results…';
      S.dirty = false;
      fetch(FORM, { method: 'POST', headers: { 'Accept': 'application/json', 'Content-Type': 'application/json' }, body: JSON.stringify(payload(event)) })
        .then(function (r) { var s2 = $('sendst'); if (s2) s2.textContent = r.ok ? '✓ Results sent to KingCretot Experience.' : 'Could not send results. Please tell your tutor your score.'; })
        .catch(function () { var s2 = $('sendst'); if (s2) s2.textContent = 'Could not send results. Please tell your tutor your score.'; });
    }
    // If the student leaves with unsent work, send a final summary.
    window.addEventListener('pagehide', function () {
      if (!S.dirty || !S.name || !navigator.sendBeacon) return;
      S.dirty = false;
      var p = payload('Left the page'), fd = new FormData();
      Object.keys(p).forEach(function (k) { fd.append(k, p[k]); });
      try { navigator.sendBeacon(FORM, fd); } catch (e) { }
    });

    K._go = function (l) { S.unlocked = Math.max(S.unlocked, l); S.level = l; S.streak = 0; S.qdone = false; bar(); next(); }; // testing hook
    gate();
  };
})();
