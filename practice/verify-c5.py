#!/usr/bin/env python3
"""Independent math check for gen-c5.js (Chapter 5: Systems & Matrices).

Runs every generator N times in Node (default 200), then re-solves each problem
here with sympy / numpy / fractions, from the raw problem data (q.p), and checks
that the marked answer is correct, that every distractor is wrong, and that no two
choices are mathematically equal.  Usage: python3 verify-c5.py [N]
"""
import json, subprocess, sys, os, random
from fractions import Fraction as Fr
from collections import Counter, defaultdict
import numpy as np
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
x, y, kk, X_ = sp.symbols('x y k X')

DUMP = r"""
global.window = undefined;
const K = require('./core.js'); require('./gen-c5.js');
const N = +process.argv[1]; const out = [];
for (const id of Object.keys(K.lessons)) { if (id[0] === 'R') continue;
  K.lessons[id].levels.forEach((gens, lv) => gens.forEach((g, gi) => {
    for (let r = 0; r < N; r++) { K._gd = []; const q = g();
      out.push({ id, lv: lv + 1, gi, p: q.p, raw: q.raw, a: q.a, ch: q.ch.map(K.strip), q: K.strip(q.q) }); } })); }
process.stdout.write(JSON.stringify(out));
"""

def cv(o):
    if isinstance(o, dict):
        if set(o.keys()) == {'n', 'd'}:
            return Fr(o['n'], o['d'])
        return {k: cv(v) for k, v in o.items()}
    if isinstance(o, list):
        return [cv(v) for v in o]
    if isinstance(o, bool) or o is None or isinstance(o, str):
        return o
    if isinstance(o, (int, float)):
        return Fr(o).limit_denominator(10**9) if isinstance(o, float) else Fr(o)
    return o

def S(v):  # to sympy rational
    if isinstance(v, Fr):
        return sp.Rational(v.numerator, v.denominator)
    return sp.sympify(v)

def mat(A):
    return sp.Matrix([[S(v) for v in r] for r in A])

# ---------- linear systems ----------
def lin_cat(eqs):
    A = mat([r[:-1] for r in eqs]); Ab = mat(eqs)
    nv = A.shape[1]
    ra, rab = A.rank(), Ab.rank()
    if rab > ra: return 'none', None
    if ra == nv:
        sol = sp.linsolve((A, mat([[r[-1]] for r in eqs])))
        return 'one', list(list(sol)[0])
    return 'inf', None

def sat_lin(eqs, pt):
    return all(sum(S(c) * S(v) for c, v in zip(r[:-1], pt)) == S(r[-1]) for r in eqs)

# ---------- polynomials ----------
def poly(c):
    return sum(S(v) * x ** (len(c) - 1 - i) for i, v in enumerate(c))

def deg(c):
    c = list(c)
    while len(c) > 1 and c[0] == 0: c.pop(0)
    return len(c) - 1

def dec_expr(d):
    e = poly(d['q']) if d.get('q') else 0
    for t in d['t']:
        e += poly(t[0]) / poly(t[1]) ** int(t[2])
    return e

# ---------- nonlinear ----------
def real_solutions(eqs):
    es = [sp.sympify(e, locals={'x': x, 'y': y}) for e in eqs]
    sols = sp.solve(es, [x, y], dict=True)
    out = set()
    for s in sols:
        xv, yv = sp.nsimplify(s[x]), sp.nsimplify(s[y])
        if xv.is_real and yv.is_real:
            out.add((xv, yv))
    return out

def ptset(raw):
    return set((S(p[0]), S(p[1])) for p in raw)

# ---------- inequalities / LP ----------
def holds(l, op, r):
    d = l - r
    return {'<': d < 0, '<=': d <= 0, '>': d > 0, '>=': d >= 0}[op]

def sat_ineq(I, px, py):
    return holds(Fr(I[0]) * px + Fr(I[1]) * py, I[2], Fr(I[3]))

def vertices(cons):
    vs = set()
    for i in range(len(cons)):
        for j in range(i + 1, len(cons)):
            a1, b1, _, c1 = cons[i]; a2, b2, _, c2 = cons[j]
            D = a1 * b2 - a2 * b1
            if D == 0: continue
            px = (c1 * b2 - c2 * b1) / D; py = (a1 * c2 - a2 * c1) / D
            if all(sat_ineq(I, px, py) for I in cons): vs.add((px, py))
    return vs

def lp_opt(cons, obj, goal):
    vs = vertices(cons)
    vals = {v: obj[0] * v[0] + obj[1] * v[1] for v in vs}
    best = max(vals.values()) if goal == 'max' else min(vals.values())
    at = [v for v in vs if vals[v] == best]
    return best, at

def in_half(h, px, py):  # a x + b y <= c
    return Fr(h[0]).limit_denominator(1000) * px + Fr(h[1]).limit_denominator(1000) * py <= Fr(h[2]).limit_denominator(1000)

def yineq(r, px, py):  # r = [m, b, op]: y op m x + b
    return holds(py, r[2], r[0] * px + r[1])

# ---------- matrices ----------
def npf(A):
    return np.array([[Fr(v) for v in r] for r in A], dtype=object)

def try_prod(shapes, expr):
    arrs = [np.zeros(shapes[ch]) for ch in expr]
    try:
        r = arrs[0]
        for a in arrs[1:]: r = r @ a
        return r.shape
    except ValueError:
        return None

# ---------- the checker ----------
def correct(p, raw, case):
    t = p['t']
    if t == 'sol':
        cat, sol = lin_cat(p['eqs']); assert cat == 'one', 'system not uniquely solvable'
        return [S(v) for v in raw] == sol
    if t == 'count':
        return raw == lin_cat(p['eqs'])[0]
    if t == 'linset':
        cat, sol = lin_cat(p['eqs'])
        if raw[0] == 'none': return cat == 'none'
        if raw[0] == 'pt': return cat == 'one' and [S(raw[1]), S(raw[2])] == sol
        if cat != 'inf': return False
        for v in (Fr(0), Fr(1), Fr(7), Fr(-3)):
            pt = (v, raw[1] * v + raw[2]) if raw[0] == 'infx' else (raw[1] * v + raw[2], v)
            if not sat_lin(p['eqs'], pt): return False
        return True
    if t == 'parab':
        a, b, c = sp.symbols('a b c')
        sol = sp.solve([a * S(px) ** 2 + b * S(px) + c - S(py) for px, py in p['pts']], [a, b, c], dict=True)[0]
        return [S(v) for v in raw] == [sol[a], sol[b], sol[c]]
    if t == 'aug':
        return mat(raw) == mat(p['eqs'])
    if t == 'msol':
        cat, sol = lin_cat(p['mat']); assert cat == 'one'
        return [S(v) for v in raw] == sol
    if t == 'rowop':
        tt, k, s = p['op']; tt, s = int(tt), int(s); M = p['mat']
        return [S(v) for v in raw] == [S(M[tt - 1][j]) + S(k) * S(M[s - 1][j]) for j in range(len(M[0]))]
    if t == 'cat3':
        cat, sol = lin_cat(p['eqs'])
        if raw[0] == 'one': return cat == 'one' and [S(v) for v in raw[1:]] == sol
        return raw[0] == cat
    if t == 'mcount':
        cat, sol = lin_cat(p['mat'])
        if raw == 'zero': return cat == 'one' and all(v == 0 for v in sol)
        return raw == cat
    if t == 'rowzero':
        tt, k, s = raw; tt, s = int(tt), int(s); r, c = int(p['pos'][0]), int(p['pos'][1])
        if tt == s or k == 0: return False
        M = [[Fr(v) for v in row] for row in p['mat']]
        M[tt - 1] = [M[tt - 1][j] + Fr(k) * M[s - 1][j] for j in range(len(M[0]))]
        return M[r - 1][c - 1] == 0
    if t == 'det':
        return S(raw) == mat(p['mat']).det()
    if t == 'cof':
        Mx = mat(p['mat'])
        v = Mx.minor(int(p['i']), int(p['j'])) if p['kind'] == 'minor' else Mx.cofactor(int(p['i']), int(p['j']))
        return S(raw) == v
    if t == 'dmat':
        e = p['eqs']; col = 0 if p['v'] == 'x' else 1
        D = [[r[0], r[1]] for r in e]
        for i in range(2): D[i][col] = e[i][2]
        return mat(raw) == mat(D)
    if t == 'solvar':
        cat, sol = lin_cat(p['eqs']); assert cat == 'one'
        return S(raw) == sol[int(p['v'])]
    if t == 'detx':
        Mx = sp.Matrix([[X_ if v is None else S(v) for v in r] for r in p['mat']])
        roots = sp.solve(sp.Eq(Mx.det(), S(p['k'])), X_)
        assert len(roots) == 1
        return S(raw) == roots[0]
    if t == 'area':
        (x1, y1), (x2, y2), (x3, y3) = p['pts']
        A = abs(x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2)) / 2   # shoelace
        return Fr(raw) == A
    if t == 'kD0':
        roots = sp.solve(sp.Eq(S(p['a']) * S(p['d']) - S(p['b']) * kk, 0), kk)
        return [S(raw)] == roots
    if t == 'kD0f':   # value of k with D = 0, then classify the system for that k
        roots = sp.solve(sp.Eq(mat([[p['a'], kk], [p['ta'], p['d']]]).det(), 0), kk)
        assert len(roots) == 1
        k0 = roots[0]
        cat, _ = lin_cat([[p['a'], k0, p['c1']], [p['ta'], p['d'], p['c2']]])
        return S(raw[0]) == k0 and raw[1] == cat
    if t == 'pform':
        facs = p['facs']
        prod = 1
        for f, pw in facs:
            fp = poly(f)
            if len(f) == 3: assert f[1] ** 2 - 4 * f[0] * f[2] < 0, 'quadratic factor not irreducible'
            prod *= fp ** int(pw)
        assert sp.expand(prod - poly(p['den'])) == 0, 'factors do not multiply to the denominator'
        assert deg(p['num']) < deg(p['den'])
        canon = sorted((i, k, len(facs[i][0]) - 2) for i, (f, pw) in enumerate(facs) for k in range(1, int(pw) + 1))
        return sorted(tuple(int(v) for v in r) for r in raw) == canon
    if t == 'pconst':
        f = poly(p['num']) / poly(p['den'])
        v = sp.cancel((x - S(p['root'])) * f).subs(x, S(p['root']))
        return S(raw) == v
    if t == 'improper':
        return deg(raw[0]) >= deg(raw[1])
    if t == 'pfd':
        orig = poly(p['num']) / poly(p['den'])
        ok = sp.cancel(sp.together(orig - dec_expr(raw))) == 0
        if ok:
            for tm in raw['t']:
                assert deg(tm[0]) < deg(tm[1]), 'improper term in a correct decomposition'
        return ok
    if t == 'nl':
        return ptset(raw) == real_solutions(p['eqs'])
    if t == 'nlcount':
        return int(raw) == len(real_solutions(p['eqs']))
    if t == 'rect':
        L, W = sp.symbols('L W', positive=True)
        e1 = L * W - S(p['A']) if p['kind'] == 'area' else L ** 2 + W ** 2 - S(p['D']) ** 2
        sols = [s for s in sp.solve([e1, 2 * L + 2 * W - S(p['P'])], [L, W], dict=True) if s[L] >= s[W]]
        assert len(sols) == 1
        return [S(raw[0]), S(raw[1])] == [sols[0][L], sols[0][W]]
    if t == 'ineqpt':
        return all(sat_ineq(I, Fr(raw[0]), Fr(raw[1])) for I in p['ineqs'])
    if t == 'ineqg':
        a, b, c = [Fr(v).limit_denominator(1000) for v in p['shade']]
        m_, b_, op = raw
        if b == 0 or -a / b != m_ or c / b != b_: return False
        px, py = -a, c / b - b                     # strictly inside the shaded half-plane
        assert a * px + b * py < c
        return yineq(raw, px, py) and ((op in ('<=', '>=')) == (not p['dash']))
    if t == 'ineqsys':
        rnd = random.Random(1)
        for _ in range(400):
            px, py = Fr(rnd.randint(-120, 120), 20), Fr(rnd.randint(-120, 120), 20)
            on = any(py == r[0] * px + r[1] for r in raw)
            if on: continue
            if all(in_half(h, px, py) for h in p['shade']) != all(yineq(r, px, py) for r in raw): return False
        return True
    if t == 'lpc':
        o = p['obj']; vals = [(o[0] * c[0] + o[1] * c[1], c) for c in p['corners']]
        best = max(v for v, _ in vals) if p['goal'] == 'max' else min(v for v, _ in vals)
        at = [c for v, c in vals if v == best]; assert len(at) == 1
        return Fr(raw[0]) == best and [Fr(raw[1]), Fr(raw[2])] == list(at[0])
    if t == 'lp':
        cons = [[Fr(c[0]), Fr(c[1]), c[2], Fr(c[3])] for c in p['cons']]
        best, at = lp_opt(cons, [Fr(v) for v in p['obj']], p['goal']); assert len(at) == 1, 'optimum not unique'
        return Fr(raw[0]) == best and (Fr(raw[1]), Fr(raw[2])) == at[0]
    if t == 'corner':
        cons = [[Fr(c[0]), Fr(c[1]), c[2], Fr(c[3])] for c in p['cons']]
        return (Fr(raw[0]), Fr(raw[1])) in vertices(cons)
    if t == 'dims':
        sh = try_prod({'A': tuple(int(v) for v in p['A']), 'B': tuple(int(v) for v in p['B'])}, 'AB')
        return (raw == 'undef') if sh is None else (raw != 'undef' and tuple(int(v) for v in raw) == sh)
    if t in ('matexpr', 'entry'):
        env = {k: npf(v) for k, v in p['mats'].items()}
        R = eval(p['expr'].replace('(', '(').strip(), {}, env)
        if t == 'entry': return Fr(raw) == R[int(p['i'])][int(p['j'])]
        return np.array_equal(npf(raw), R) if npf(raw).shape == R.shape else False
    if t == 'eqmat':
        eqs = []
        for i in range(2):
            for j in range(2):
                l = p['L'][i][j]; l = sp.sympify(l, locals={'x': x, 'y': y}) if isinstance(l, str) else S(l)
                eqs.append(sp.Eq(l, S(p['Rm'][i][j])))
        sol = sp.solve(eqs, [x, y], dict=True); assert len(sol) == 1
        return [S(raw[0]), S(raw[1])] == [sol[0][x], sol[0][y]]
    if t == 'undef':
        sh = {k: tuple(int(v) for v in s) for k, s in p['shapes'].items()}
        ok = try_prod(sh, raw) is not None
        return (not ok) if p['ask'] == 'not' else ok
    if t == 'inv':
        return mat(p['A']) * mat(raw) == sp.eye(len(p['A']))
    if t == 'sing':
        return mat(raw).det() == 0
    if t == 'mateq':
        return mat(raw[0]) == mat([r[:-1] for r in p['eqs']]) and mat(raw[1]) == mat([[r[-1]] for r in p['eqs']])
    if t == 'solinv':
        A = mat([r[:-1] for r in p['eqs']])
        assert A * mat(p['Ainv']) == sp.eye(A.shape[0]), 'given inverse is wrong'
        cat, sol = lin_cat(p['eqs'])
        return [S(v) for v in raw] == sol
    if t == 'ksing':
        Mx = sp.Matrix([[kk if v == 'k' else S(v) for v in r] for r in p['A']])
        roots = set(sp.solve(Mx.det(), kk))
        return set(S(v) for v in raw) == roots
    if t == 'decode':
        return mat(p['A']) * mat(raw) == mat([[v] for v in p['Y']])
    raise Exception('unknown type ' + t)

def canon(p, raw):
    """Normalized mathematical value of a choice, to catch equal-but-differently-written choices."""
    t = p['t']
    if t == 'pfd': return str(sp.cancel(sp.together(dec_expr(raw))))
    if t == 'nl': return tuple(sorted(ptset(raw)))
    if t == 'ksing': return tuple(sorted(set(S(v) for v in raw)))
    if t == 'pform': return tuple(sorted(tuple(int(v) for v in r) for r in raw))
    if t == 'improper': return str(sp.cancel(poly(raw[0]) / poly(raw[1])))
    return json.dumps(raw, default=str, sort_keys=True)

def fmtnum(v):
    v = Fr(v)
    sgn = '−' if v < 0 else ''
    v = abs(v)
    return sgn + (str(v.numerator) if v.denominator == 1 else '[%d]/[%d]' % (v.numerator, v.denominator))

def fmt_lin(row):
    """The equation as the page should show it, built independently of the JS formatter."""
    out, first = '', True
    for c, v in zip(row[:-1], 'xyz'):
        c = Fr(c)
        if c == 0: continue
        body = ('' if abs(c) == 1 else fmtnum(abs(c))) + v
        out += (('−' if c < 0 else '') + body) if first else ((' − ' if c < 0 else ' + ') + body)
        first = False
    return out + ' = ' + fmtnum(row[-1])

def main():
    res = subprocess.run(['node', '-e', DUMP, str(N)], cwd=HERE, capture_output=True, text=True)
    if res.returncode:
        print(res.stderr); sys.exit(1)
    data = json.loads(res.stdout)
    fails, per, shown, disp = [], Counter(), Counter(), Counter()
    for c in data:
        key = (c['id'], c['lv'], c['gi'])
        per[key] += 1
        p = cv(c['p']); raws = [cv(r) for r in c['raw']]
        try:
            flags = [bool(correct(p, r, c)) for r in raws]
            if not flags[c['a']]: fails.append((key, 'MARKED ANSWER WRONG', c['q'][:110], c['ch'][c['a']]))
            for i, f in enumerate(flags):
                if f and i != c['a']: fails.append((key, 'DISTRACTOR IS CORRECT', c['q'][:110], c['ch'][i]))
            cs = [canon(p, r) for r in raws]
            if len(set(cs)) != len(cs): fails.append((key, 'TWO CHOICES MATHEMATICALLY EQUAL', c['q'][:110], ' | '.join(c['ch'])))
            if any(r is None for r in raws): fails.append((key, 'MISSING RAW', c['q'][:110], ''))
            if 'eqs' in p and p['t'] in ('sol', 'count', 'linset', 'cat3', 'aug', 'solvar', 'mateq', 'solinv'):
                shown[key] += 1
                if all(fmt_lin(r) in c['q'] for r in p['eqs']): disp[key] += 1
        except Exception as e:
            fails.append((key, 'ERROR ' + repr(e), c['q'][:110], ' | '.join(c['ch'])))
    gens = sorted(per)
    by_lesson = defaultdict(int)
    for g in gens: by_lesson[g[0]] += 1
    print('generators checked:', len(gens), '| cases:', len(data), '| cases per generator:', min(per.values()))
    print('generators per lesson:', dict(by_lesson))
    print('display cross-check (system in p found verbatim in the question text):')
    for k in sorted(shown): print('   ', k, '%d/%d' % (disp[k], shown[k]))
    shown = Counter()
    for f in fails:
        shown[f[0]] += 1
        if shown[f[0]] <= 3: print('FAIL', f)
    print('failures:', len(fails))
    sys.exit(1 if fails else 0)

if __name__ == '__main__':
    main()
