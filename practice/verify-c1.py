#!/usr/bin/env python3
"""Independent math check for gen-c1.js (Chapter 1: Equations & Inequalities).

Node renders >= 200 questions per generator (fixed seeds) and dumps the HTML plus raw data (q.p).
This script re-reads the DISPLAYED math (question HTML -> sympy), solves it independently
(sympy solveset / substitution / brute force / own word-problem setup), and checks:
  * the marked answer is right,
  * no distractor is mathematically equal to the right answer,
  * the explanation has no hyphen-minus before a digit.
Usage: python3 verify-c1.py [runs_per_generator]
"""
import json, os, re, subprocess, sys, random, html as H
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr, standard_transformations, implicit_multiplication_application, convert_xor, rationalize

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = int(sys.argv[1]) if len(sys.argv) > 1 else 220

DUMP_JS = r"""
global.window = undefined;
const K = require(process.argv[1] + '/core.js');
require(process.argv[1] + '/gen-c1.js');
const RUNS = +process.argv[2];
const out = [];
for (const id of Object.keys(K.lessons)) {
  if (/^R/.test(id)) continue;
  K.lessons[id].levels.forEach((gens, lv) => gens.forEach((g, gi) => {
    let seed = 1000 + gi * 7919 + lv * 104729 + id.charCodeAt(2) * 31;
    K.setRng(() => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; });
    for (let r = 0; r < RUNS; r++) {
      K._gd = [];
      const q = g();
      out.push({ id, lv: lv + 1, gi, q: q.q, ch: q.ch, a: q.a, why: q.why, p: q.p || null, gd: K._gd.join(' | '), graph: q.graph || '' });
    }
  }));
}
process.stdout.write(JSON.stringify(out));
"""

x, k, t = sp.symbols('x k t')
TR = standard_transformations + (implicit_multiplication_application, convert_xor, rationalize)
LETTERS = 'abcdefghjklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
RP = sp.Function('rp')


def strip_tags(s):
    return re.sub(r'<[^>]+>', '', s)


def to_text(h, cx=False):
    """HTML math -> sympy-parsable text."""
    s = h
    s = re.sub(r'<i>x</i><sup>(\d+)/(\d+)</sup>', r' rp(x,\1,\2) ', s)
    s = s.replace('<i>', '').replace('</i>', '').replace('<b>', '').replace('</b>', '')
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r'<sup>([^<]*)</sup>', r'**(\1)', s)
        s = re.sub(r'<span class="fr"><span class="nu">([^<]*)</span><span class="de">([^<]*)</span></span>', r'((\1)/(\2))', s)
        s = re.sub(r'<span class="rad">√<span class="rc"[^>]*>([^<]*)</span></span>', r' sqrt(\1) ', s)
    s = strip_tags(s)
    s = H.unescape(s)
    s = (s.replace('−', '-').replace('·', '*').replace('×', '*').replace('π', ' pi ').replace('∞', 'oo')
         .replace('≤', '<=').replace('≥', '>=').replace(' ', ' '))
    s = re.sub(r'\|([^|]*)\|', r'Abs(\1)', s)
    if cx:
        s = re.sub(r'(?<![A-Za-z])i(?![A-Za-z])', ' I ', s)
    return s


def P(s, cx=False, extra=None):
    ld = {c: sp.Symbol(c) for c in LETTERS}
    ld.update({'pi': sp.pi, 'sqrt': sp.sqrt, 'Abs': sp.Abs, 'oo': sp.oo, 'rp': RP})
    if cx:
        ld['I'] = sp.I
    else:
        ld['I'] = sp.Symbol('I')
    ld['i'] = sp.I if cx else sp.Symbol('i')
    if extra:
        ld.update(extra)
    return parse_expr(s, local_dict=ld, transformations=TR)


def num(v):
    return complex(sp.N(v, 30))


def close(a, b, tol=1e-8):
    return abs(a - b) <= tol * max(1, abs(a), abs(b))


def split_top(s, sep=','):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur); cur = ''
        else:
            cur += ch
    out.append(cur)
    return [o.strip() for o in out]


def parse_set(h, cx=False):
    """'{a, b}' / '∅' / 'x = v' -> sorted list of complex numbers."""
    s = to_text(h, cx).strip()
    if s in ('∅',):
        return []
    s = re.sub(r'^\s*x\s*=\s*', '', s)
    if s.startswith('{') and s.endswith('}'):
        s = s[1:-1]
    vals = []
    for el in split_top(s):
        if '±' in el:
            vals += [num(P(el.replace('±', '+', 1), cx)), num(P(el.replace('±', '-', 1), cx))]
        else:
            vals.append(num(P(el, cx)))
    return sorted(vals, key=lambda z: (round(z.real, 7), round(z.imag, 7)))


def same_vals(A, B):
    if len(A) != len(B):
        return False
    A = sorted(A, key=lambda z: (round(z.real, 6), round(z.imag, 6)))
    B = sorted(B, key=lambda z: (round(z.real, 6), round(z.imag, 6)))
    return all(close(a, b) for a, b in zip(A, B))


def dedupe(vals):
    out = []
    for v in vals:
        if not any(close(v, w) for w in out):
            out.append(v)
    return out


def eq_sides(h, cx=False, extra=None):
    s = to_text(h, cx)
    l, r = s.split('=', 1)
    return P(l, cx, extra), P(r, cx, extra)


def solve_eq(h, dom):
    L, R = eq_sides(h, cx=(dom == 'C'))
    f = L - R
    S = sp.solveset(f, x, sp.S.Complexes if dom == 'C' else sp.S.Reals)
    if S == sp.S.EmptySet:
        S = []
    elif not isinstance(S, sp.FiniteSet):
        raise ValueError('solveset not finite: %s' % S)
    good = []
    for r in S:
        try:
            lv, rv = num(L.subs(x, r)), num(R.subs(x, r))
        except Exception:
            continue
        if any(map(lambda z: z != z or abs(z) == float('inf'), [lv, rv])):
            continue
        if dom != 'C' and abs(complex(sp.N(r)).imag) > 1e-12:
            continue
        if close(lv, rv, 1e-9):
            good.append(num(r))
    return dedupe(good), L, R


def classify(h, extra=None):
    L, R = eq_sides(h, extra=extra)
    d = sp.expand(sp.simplify(L - R))
    if d == 0:
        return ('id', None)
    if not d.has(x):
        return ('co', None)
    sol = sp.solve(d, x)
    return ('cd', [num(s) for s in sol])


def parse_classify(h):
    s = strip_tags(H.unescape(h))
    if s.startswith('Identity'):
        return ('id', None)
    if s.startswith('Contradiction'):
        return ('co', None)
    m = re.search(r'solution set (.*)$', h)
    return ('cd', parse_set(m.group(1)))


def same_class(a, b):
    return a[0] == b[0] and (a[0] != 'cd' or same_vals(a[1], b[1]))


# ---------- intervals ----------
def parse_iv(h):
    s = to_text(h).strip()
    if s == '∅':
        return sp.S.EmptySet
    if s.startswith('{'):
        return sp.FiniteSet(*[P(e) for e in split_top(s[1:-1])])
    out = sp.S.EmptySet
    for piece in s.split('∪'):
        piece = piece.strip()
        lb, rb = piece[0], piece[-1]
        a, b = split_top(piece[1:-1])
        A, B = P(a), P(b)
        out = sp.Union(out, sp.Interval(A, B, left_open=(lb == '('), right_open=(rb == ')')))
    return out


def rel(lhs, op, rhs):
    return {'<': sp.Lt, '<=': sp.Le, '>': sp.Gt, '>=': sp.Ge, '=': sp.Eq}[op](lhs, rhs)


OPRE = re.compile(r'(<=|>=|<|>|=)')


def ineq_set(h):
    s = to_text(h)
    parts = OPRE.split(s)
    terms = [P(p) for p in parts[0::2]]
    ops = parts[1::2]
    S = sp.S.Reals
    for i, op in enumerate(ops):
        S = sp.Intersection(S, sp.solveset(rel(terms[i], op, terms[i + 1]), x, sp.S.Reals))
    return sp.simplify(S)


def same_set(A, B):
    return sp.simplify(sp.Union(sp.Complement(A, B), sp.Complement(B, A))) == sp.S.EmptySet


# ---------- statements (compound inequalities) ----------
SAMPLES = [sp.Rational(i, 4) for i in range(-160, 161)]


def stmt_truth(h):
    s = to_text(h)
    if ' or ' in s:
        parts, mode = s.split(' or '), 'or'
    elif ' and ' in s:
        parts, mode = s.split(' and '), 'and'
    else:
        parts, mode = [s], 'and'
    chains = []
    for p in parts:
        pp = OPRE.split(p)
        chains.append(([sp.lambdify(x, P(e)) for e in pp[0::2]], pp[1::2]))
    res = []
    for v in SAMPLES:
        fv = float(v)
        vals = []
        for fs, ops in chains:
            ev = [f(fv) for f in fs]
            ok = all({'<': ev[i] < ev[i + 1] - 1e-12, '<=': ev[i] <= ev[i + 1] + 1e-12, '>': ev[i] > ev[i + 1] + 1e-12, '>=': ev[i] >= ev[i + 1] - 1e-12}[o] for i, o in enumerate(ops))
            vals.append(ok)
        res.append(any(vals) if mode == 'or' else all(vals))
    return res


# ---------- numbers from word answers ----------
def nums(h):
    s = H.unescape(strip_tags(h)).replace('−', '-')
    s = re.sub(r'(?<=\d),(?=\d{3})', '', s)
    return [float(z) for z in re.findall(r'-?\d+(?:\.\d+)?', s)]


def same_nums(a, b):
    return len(a) == len(b) and all(close(u, v, 1e-9) for u, v in zip(a, b))


def pos_roots(expr, var=t):
    return sorted(float(r) for r in sp.solve(expr, var) if r.is_real and r > 0)


def word_expected(p):
    w = p['w']
    R = sp.Rational
    def S(v):
        return R(str(v))
    if w == 'interestT':
        T = sp.Symbol('T'); return [float(sp.solve(S(p['P']) * (1 + S(p['r']) / 100 * T) - S(p['A']), T)[0])]
    if w == 'interest':
        return [float(S(p['P']) * S(p['r']) / 100 * S(p['t']))]
    if w == 'plan':
        return [float(sp.solve(S(p['F']) + S(p['c']) * x - S(p['B']), x)[0])]
    if w == 'rectP':
        return [float(sp.solve(2 * x + 2 * (x + p['d']) - p['P'], x)[0])]
    if w == 'opposite':
        return [float(sp.solve((p['r1'] + p['r2']) * t - p['D'], t)[0])]
    if w == 'rectKP':
        wv = sp.solve(2 * x + 2 * (p['kk'] * x + p['d']) - p['P'], x)[0]; return [float(wv), float(p['kk'] * wv + p['d'])]
    if w == 'split':
        return [float(sp.solve(p['r1'] * x + p['r2'] * (p['T'] - x) - 100 * S(p['I']), x)[0])]
    if w == 'mixAdd':
        return [float(sp.solve(p['p1'] * x + p['p2'] * p['V'] - p['p3'] * (x + p['V']), x)[0])]
    if w == 'twoLegs':
        return [float(sp.solve(p['t1'] * x + p['t2'] * (x + p['d']) - p['D'], x)[0])]
    if w == 'mixTotal':
        a = sp.solve(p['p1'] * x + p['p2'] * (p['V'] - x) - p['p3'] * p['V'], x)[0]; return [float(a), p['p1'], float(p['V'] - a), p['p2']]
    if w == 'catch':
        return [float(sp.solve(p['r2'] * t - p['r1'] * (t + p['h']), t)[0])]
    if w == 'plans':
        return [float(sp.solve(p['F1'] + p['c1'] * x - p['F2'] - p['c2'] * x, x)[0])]
    if w == 'overall':
        return [float(sp.solve(p['r1'] * p['A'] + p['r2'] * x - p['r3'] * (p['A'] + x), x)[0])]
    if w == 'ladder':
        return pos_roots(x ** 2 + p['b'] ** 2 - p['c'] ** 2, x)
    if w == 'ground':
        return pos_roots(-16 * t ** 2 + p['v'] * t)
    if w == 'area':
        r = pos_roots(x * (x + p['d']) - p['A'], x); return [r[0], r[0] + p['d']]
    if w == 'consec':
        r = pos_roots(x * (x + 1) - p['pr'], x); return [r[0], r[0] + 1]
    if w == 'height0':
        return pos_roots(-16 * t ** 2 + p['v'] * t + p['s0'])
    if w == 'heightTimes':
        return pos_roots(-16 * t ** 2 + p['v'] * t + p['s0'] - p['h'])
    if w == 'legs':
        r = pos_roots(x ** 2 + (x + p['d']) ** 2 - p['c'] ** 2, x); return [r[0], r[0] + p['d']]
    if w == 'border':
        return pos_roots((p['Lg'] + 2 * x) * (p['Wg'] + 2 * x) - p['T'], x)
    if w == 'cliff':
        r = pos_roots(-16 * t ** 2 + p['v'] * t + p['s0']); return [round(r[0] + 1e-12, 1)]
    if w == 'box':
        return [r for r in pos_roots(p['c'] * (x - 2 * p['c']) ** 2 - p['V'], x) if r > 2 * p['c']]
    if w == 'lot':
        r = pos_roots(x * (S(p['P']) / 2 - x) - p['A'], x); return [r[0], r[1]]
    if w == 'down':
        return [max(pos_roots(-16 * t ** 2 + p['v'] * t + p['s0'] - p['h']))]
    if w == 'work':
        return [float(sp.solve(t / p['a'] + t / p['b'] - 1, t)[0])]
    if w == 'workB':
        return [float(sp.solve(S(p['T']) / p['a'] + S(p['T']) / x - 1, x)[0])]
    if w == 'drain':
        return [float(sp.solve(t / p['f'] - t / p['dr'] - 1, t)[0])]
    raise KeyError(w)


def check_word(rec):
    p, ch, a = rec['p'], rec['ch'], rec['a']
    w = p['w']
    plain_q = H.unescape(strip_tags(rec['q'])).replace('−', '-').replace(',', '')
    for key, v in p.items():
        if key in ('k', 'w', 'kk', 's') or not isinstance(v, (int, float)):
            continue
        v = abs(v)
        if v == 0:
            continue
        sv = str(int(v)) if float(v).is_integer() else ('%g' % v)
        if sv not in plain_q:
            return 'param %s=%s not in question text' % (key, sv)
    if w == 'profit':
        N = sp.Rational(p['F'], p['p'] - p['c'])
        def key(h):
            s = strip_tags(h)
            return (s.split(' ')[0] + ' ' + s.split(' ')[1], nums(h)[0])
        exp = ('More than', float(N))
        if key(ch[a]) != exp:
            return 'profit answer %s vs %s' % (key(ch[a]), exp)
        if any(key(c) == exp for i, c in enumerate(ch) if i != a):
            return 'profit distractor equals answer'
        return None
    if w in ('avg', 'above', 'tol'):
        if w == 'avg':
            need = 4 * p['G'] - sum(p['s']); exp = sp.Interval(need, 100)
        elif w == 'above':
            exp = sp.solveset(-16 * x ** 2 + p['v'] * x + p['s0'] - p['h'] > 0, x, sp.S.Reals)
        else:
            T, tt = sp.Rational(str(p['T'])), sp.Rational(str(p['t'])); exp = sp.solveset(sp.Abs(x - T) <= tt, x, sp.S.Reals)
        got = parse_iv(ch[a])
        if not same_set(got, exp):
            return 'interval %s vs %s' % (got, exp)
        for i, c in enumerate(ch):
            if i != a and same_set(parse_iv(c), exp):
                return 'distractor equals answer: ' + c
        return None
    exp = word_expected(p)
    got = nums(ch[a])
    if not same_nums(got, exp):
        return 'word %s: answer %s vs expected %s' % (w, got, exp)
    for i, c in enumerate(ch):
        if i != a and same_nums(nums(c), exp):
            return 'distractor equals answer: ' + c
    return None


def check(rec):
    p, ch, a = rec['p'], rec['ch'], rec['a']
    if p is None:
        return 'no p'
    kind = p['k']
    if 'e' in p and p['e'] not in rec['q']:
        return 'p.e not shown in question'
    if kind == 'solve':
        dom = p.get('dom', 'R')
        exp, L, R = solve_eq(p['e'], dom)
        cx = dom == 'C'
        got = parse_set(ch[a], cx)
        if not same_vals(got, exp):
            return 'answer %s vs solveset %s' % (got, exp)
        for i, c in enumerate(ch):
            if i != a and same_vals(parse_set(c, cx), exp):
                return 'distractor equals answer: ' + c
        return None
    if kind == 'cx':
        v = num(P(to_text(p['e'], True), True))
        g = parse_set(ch[a], True)
        if len(g) != 1 or not close(g[0], v):
            return 'complex answer %s vs %s' % (g, v)
        for i, c in enumerate(ch):
            if i != a:
                gg = parse_set(c, True)
                if len(gg) == 1 and close(gg[0], v):
                    return 'distractor equals answer: ' + c
        return None
    if kind == 'classify':
        exp = classify(p['e'])
        if not same_class(parse_classify(ch[a]), exp):
            return 'classify %s vs %s' % (parse_classify(ch[a]), exp)
        for i, c in enumerate(ch):
            if i != a and same_class(parse_classify(c), exp):
                return 'distractor equals answer: ' + c
        return None
    if kind == 'kval':
        want = 'co' if p['want'] == 'none' else 'id'
        for i, c in enumerate(ch):
            kv = P(re.sub(r'^\s*k\s*=', '', to_text(c)))
            cl = classify(p['e'], extra={'k': kv})
            if (cl[0] == want) != (i == a):
                return 'kval choice %s gives %s' % (c, cl[0])
        return None
    if kind == 'formula':
        v = sp.Symbol(p['v'])
        L, R = eq_sides(p['e'])
        syms = sorted((L - R).free_symbols, key=str)
        rnd = random.Random(5)
        pts = [{s: sp.Rational(rnd.randint(13, 57), 10) for s in syms} for _ in range(6)]
        def ok(c):
            lhs, rhs = to_text(c).split('=', 1)
            assert lhs.strip() == p['v'], lhs
            ex = P(rhs)
            d = (L - R).subs(v, ex)
            return all(abs(num(d.subs(pt))) < 1e-9 for pt in pts)
        if not ok(ch[a]):
            return 'formula answer does not satisfy equation'
        for i, c in enumerate(ch):
            if i != a and ok(c):
                return 'distractor satisfies equation: ' + c
        return None
    if kind == 'disc':
        L, R = eq_sides(p['e'])
        poly = sp.Poly(sp.expand(L - R), x)
        A, B, C = [poly.coeff_monomial(x ** j) for j in (2, 1, 0)]
        D = B * B - 4 * A * C
        cat = 3 if D < 0 else 2 if D == 0 else (0 if sp.sqrt(D).is_rational else 1)
        names = ['Two distinct rational', 'Two distinct irrational', 'One rational', 'Two nonreal']
        if not ch[a].startswith(names[cat]):
            return 'disc category %s vs %s' % (ch[a], names[cat])
        if sum(c.startswith(names[cat]) for c in ch) != 1:
            return 'disc duplicate category'
        return None
    if kind == 'kdisc':
        L, R = eq_sides(p['e'])
        poly = sp.Poly(sp.expand(L - R), x)
        A, B, C = [poly.coeff_monomial(x ** j) for j in (2, 1, 0)]
        exp = [num(s) for s in sp.solve(B * B - 4 * A * C, k)]
        def kset(c):
            s = to_text(c).replace('only', '')
            return [num(P(re.sub(r'^\s*k\s*=', '', piece))) for piece in s.split(' or ')]
        if not same_vals(kset(ch[a]), exp):
            return 'kdisc %s vs %s' % (kset(ch[a]), exp)
        for i, c in enumerate(ch):
            if i != a and same_vals(kset(c), exp):
                return 'distractor equals answer: ' + c
        return None
    if kind == 'ineq':
        exp = ineq_set(p['e'])
        got = parse_iv(ch[a])
        if not same_set(got, exp):
            return 'ineq answer %s vs %s' % (got, exp)
        for i, c in enumerate(ch):
            if i != a and same_set(parse_iv(c), exp):
                return 'distractor equals answer: ' + c
        return None
    if kind == 'nl':
        d = rec['gd'].replace('−', '-')
        dots = re.findall(r'(open|closed) dot at (-?[\d.]+)', d)
        dots = [(o == 'closed', sp.Rational(v)) for o, v in dots]
        if 'arrow pointing right' in d:
            exp = sp.Interval(dots[0][1], sp.oo, left_open=not dots[0][0])
        elif 'arrow pointing left' in d:
            exp = sp.Interval(-sp.oo, dots[0][1], right_open=not dots[0][0])
        else:
            (c1, v1), (c2, v2) = sorted(dots, key=lambda z: z[1])
            if 'segment from' not in d:
                return 'no segment'
            exp = sp.Interval(v1, v2, left_open=not c1, right_open=not c2)
        if not same_set(parse_iv(ch[a]), exp):
            return 'number line %s vs %s' % (parse_iv(ch[a]), exp)
        for i, c in enumerate(ch):
            if i != a and same_set(parse_iv(c), exp):
                return 'distractor equals answer: ' + c
        return None
    if kind == 'stmt':
        if 'ref' in p:
            r = p['ref']
            ref = [{'<': abs(float(v) - r['h']) < r['c'], '<=': abs(float(v) - r['h']) <= r['c'], '>': abs(float(v) - r['h']) > r['c'], '>=': abs(float(v) - r['h']) >= r['c']}[r['rel']] for v in SAMPLES]
        else:
            ref = stmt_truth(p['e'])
        if stmt_truth(ch[a]) != ref:
            return 'statement not equivalent: ' + ch[a]
        for i, c in enumerate(ch):
            if i != a and stmt_truth(c) == ref:
                return 'distractor equivalent: ' + c
        return None
    if kind == 'excl':
        L, R = eq_sides(p['e'])
        dens = set()
        for side in (L, R):
            for term in sp.Add.make_args(side):
                dn = sp.fraction(sp.together(term))[1]
                dens |= set(sp.solve(dn, x))
        exp = sorted(float(v) for v in dens)
        got = sorted(nums(ch[a]))
        if not same_nums(got, exp):
            return 'excluded %s vs %s' % (got, exp)
        for i, c in enumerate(ch):
            if i != a and same_nums(sorted(nums(c)), exp):
                return 'distractor equals answer'
        return None
    if kind in ('ratexp', 'ratexp2'):
        L, R = eq_sides(p['e'])
        def rp_num(v, mm, nn):
            if v < 0 and nn % 2 == 0:
                return float('nan')
            r = abs(v) ** (1.0 / nn)
            if v < 0:
                r = -r
            return r ** mm
        f = sp.lambdify(x, L - R, modules=[{'rp': rp_num}, 'math'])
        def zero(v):
            try:
                y = f(v)
            except (ValueError, ZeroDivisionError):
                return False
            return y == y and abs(y) < 1e-7 * max(1, abs(v))
        exp = [v for v in range(-30000, 30001) if zero(v)]
        got = [z.real for z in parse_set(ch[a])]
        if not same_nums(sorted(got), exp):
            return 'ratexp %s vs brute %s' % (got, exp)
        for i, c in enumerate(ch):
            if i != a and same_nums(sorted(z.real for z in parse_set(c)), exp):
                return 'distractor equals answer: ' + c
        return None
    if kind == 'word':
        return check_word(rec)
    return 'unknown kind ' + kind


def main():
    raw = subprocess.run(['node', '-e', DUMP_JS, HERE, str(RUNS)], capture_output=True, text=True, check=True).stdout
    data = json.loads(raw)
    stats, fails = {}, 0
    shown = {}
    for rec in data:
        key = (rec['id'], rec['lv'], rec['gi'])
        stats[key] = stats.get(key, 0) + 1
        why = H.unescape(strip_tags(rec['why']))
        err = None
        if re.search(r'-\d', re.sub(r'\d-\d|[A-Za-z]-[A-Za-z]', '', why)):
            err = 'hyphen-minus in explanation: ' + why[:100]
        if not err:
            try:
                err = check(rec)
            except Exception as e:  # noqa
                err = 'EXCEPTION %s: %s' % (type(e).__name__, e)
        if err:
            fails += 1
            shown[key] = shown.get(key, 0) + 1
            if shown[key] <= 3:
                print('FAIL', key, err, '::', H.unescape(strip_tags(rec['q']))[:110], '| ANS', H.unescape(strip_tags(rec['ch'][rec['a']])))
    per_lesson = {}
    for (i, lv, gi), n in stats.items():
        per_lesson.setdefault(i, [0, 0]); per_lesson[i][0] += 1; per_lesson[i][1] += n
    for i in sorted(per_lesson):
        print('lesson %s: %d generators, %d questions checked' % (i, per_lesson[i][0], per_lesson[i][1]))
    print('TOTAL generators %d, questions %d, failures %d' % (len(stats), len(data), fails))
    sys.exit(1 if fails else 0)


if __name__ == '__main__':
    main()
