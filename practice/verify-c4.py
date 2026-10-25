"""Independent math check for gen-c4.js (Chapter 4).
Runs dump-c4.js to generate questions, parses the DISPLAYED choices (HTML) back into numbers,
expressions, intervals and sets, and checks every marked answer against an independent computation
(numeric root finding, sympy, direct evaluation of the original equation). Also checks that no
distractor is mathematically equal to the correct answer.
Usage: python3 verify-c4.py [runs_per_generator]"""
import json, math, re, subprocess, sys, random, os
from collections import Counter, defaultdict
from html.parser import HTMLParser
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr, standard_transformations, implicit_multiplication_application, rationalize

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = int(sys.argv[1]) if len(sys.argv) > 1 else 250
data = json.loads(subprocess.run(['node', os.path.join(HERE, 'dump-c4.js'), str(RUNS)], capture_output=True, text=True, cwd=HERE, check=True).stdout)
X, Y, Z, A_, B_ = sp.symbols('x y z A B')

# ---------------- HTML -> text / sympy ----------------
class _T(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True); self.root = ['root', {}, []]; self.st = [self.root]
    def handle_starttag(self, tag, attrs):
        nd = [tag, dict(attrs), []]; self.st[-1][2].append(nd)
        if tag not in ('br', 'img'): self.st.append(nd)
    def handle_endtag(self, tag):
        if len(self.st) > 1: self.st.pop()
    def handle_data(self, d): self.st[-1][2].append(d)
def tree(h):
    t = _T(); t.feed(h); return t.root
def conv(nd):
    if isinstance(nd, str): return nd
    tag, at, ch = nd; cls = at.get('class', '') or ''
    if tag == 'span' and cls == 'fr':
        nu = [c for c in ch if not isinstance(c, str) and c[1].get('class') == 'nu'][0]
        de = [c for c in ch if not isinstance(c, str) and c[1].get('class') == 'de'][0]
        return '((' + conv(nu) + ')/(' + conv(de) + '))'
    if tag == 'span' and cls == 'rad':
        idx = '2'; rc = ''
        for c in ch:
            if isinstance(c, str): continue
            if c[0] == 'sup': idx = ''.join(conv(k) for k in c[2])
            elif c[1].get('class') == 'rc': rc = conv(c)
        return 'root((' + rc + '),' + idx + ')'
    inner = ''.join(conv(c) for c in ch)
    if tag == 'sup': return '**(' + inner + ')'
    if tag == 'sub': return '@(' + inner + ')'
    return inner
def text(h):  # plain readable text (fractions written a/b)
    h = re.sub(r'<span class="fr"><span class="nu">(.*?)</span><span class="de">(.*?)</span></span>', r'(\1)/(\2)', h)
    return re.sub(r'\s+', ' ', re.sub(r'<[^>]+>', '', h).replace('&gt;', '>').replace('&lt;', '<').replace('&amp;', '&')).strip()

def _logs(s):
    out = ''; i = 0
    while i < len(s):
        mm = re.match(r'(ln|log)(@\(([^()]*)\))?\s*', s[i:])
        if mm and (i == 0 or not s[i - 1].isalpha()):
            base = 'E' if mm.group(1) == 'ln' else (mm.group(3) if mm.group(2) else '10')
            j = i + mm.end()
            if j < len(s) and s[j] == '(':
                d = 0; k = j
                while k < len(s):
                    if s[k] == '(': d += 1
                    elif s[k] == ')':
                        d -= 1
                        if d == 0: break
                    k += 1
                arg = s[j + 1:k]; j = k + 1
            else:
                t = re.match(r'[A-Za-z0-9.]+', s[j:]); k = j + t.end()
                if k < len(s) and s[k] == '(':
                    d = 0
                    while k < len(s):
                        if s[k] == '(': d += 1
                        elif s[k] == ')':
                            d -= 1
                            if d == 0: k += 1; break
                        k += 1
                t2 = re.match(r'\*\*\([^()]*\)', s[k:])
                if t2: k += t2.end()
                arg = s[j:k]; j = k
            out += ' LG((' + _logs(base) + '),(' + _logs(arg) + ')) '; i = j
        else:
            out += s[i]; i += 1
    return out
def LG(b, a): return sp.log(a) / sp.log(b)
LOC = {'x': X, 'y': Y, 'z': Z, 'A': A_, 'B': B_, 'e': sp.E, 'E': sp.E, 'LG': LG, 'root': sp.root, 'Abs': sp.Abs, 'oo': sp.oo}
TR = standard_transformations + (implicit_multiplication_application, rationalize)
def pre(h):
    s = conv(tree(h))
    for a, b in [('−', '-'), ('·', '*'), ('×', '*'), ('½', '(1/2)'), ('⅓', '(1/3)'), ('¼', '(1/4)'), ('∞', 'oo'), (' ', ' ')]: s = s.replace(a, b)
    s = re.sub(r'\|([^|]*)\|', r'Abs(\1)', s)
    s = re.sub(r'(\d),(\d{3})', r'\1\2', s)
    return _logs(s)
def sx(h):  # sympy expression from html
    return parse_expr(pre(h).strip(), local_dict=LOC, transformations=TR, evaluate=True)
def rhs(h):  # expression after the last '='
    s = pre(h); s = s.split('=')[-1]
    return parse_expr(s.strip(), local_dict=LOC, transformations=TR)
def numval(h):  # first number in the displayed text
    t = text(h).replace('−', '-').replace(',', '').replace('$', '')
    m = re.search(r'-?\d+(?:\.\d+)?', t); return float(m.group(0))
def ratval(h):  # exact rational shown after '=' (or alone)
    e = rhs(h) if '=' in text(h) else sx(h); return sp.nsimplify(e)
def sameval(a, b, tol=1e-9): return abs(float(a) - float(b)) <= tol * max(1, abs(float(a)))

# interval parse -> membership function
def ivparse(h):
    t = text(h).replace('−', '-').replace('∞', 'inf')
    if 'All real' in t: return lambda v: True
    parts = []
    t = re.sub(r'\((-?\d+)\)/\((\d+)\)', r'\1/\2', t)
    for m in re.finditer(r'([\(\[])\s*([^,\]\)]+),\s*([^\]\)]+)([\)\]])', t):
        lo = -math.inf if m.group(2).strip() == '-inf' else float(sp.nsimplify(m.group(2).replace(' ', '')))
        hi = math.inf if m.group(3).strip() == 'inf' else float(sp.nsimplify(m.group(3).replace(' ', '')))
        parts.append((m.group(1), lo, hi, m.group(4)))
    def mem(v):
        for l, lo, hi, r in parts:
            okl = v > lo or (l == '[' and v == lo); okr = v < hi or (r == ']' and v == hi)
            if okl and okr: return True
        return False
    mem.parts = parts; return mem
def ivsame(mem, pred, pts):
    return all(mem(v) == pred(v) for v in pts)
def ivpts(ends):
    pts = [k / 4 for k in range(-80, 81)]
    for e in ends: pts += [e, e - 1e-6, e + 1e-6]
    return pts

def setparse(h):  # "x = 3 or x = -2" / "x = ±4" / "No solution"
    t = text(h).replace('−', '-')
    if 'No' in t: return set()
    vals = set()
    for m in re.finditer(r'x\s*[=≈]\s*(±)?\s*(-?\d+(?:\.\d+)?(?:/\d+)?)', t):
        v = sp.nsimplify(m.group(2)); vals.add(v)
        if m.group(1): vals.add(-v)
    return vals

def bisect(f, lo, hi, it=200):
    flo = f(lo)
    for _ in range(it):
        mid = (lo + hi) / 2; fm = f(mid)
        if (fm > 0) == (flo > 0): lo, flo = mid, fm
        else: hi = mid
    return (lo + hi) / 2
def roots_scan(f, lo, hi, N=4000, dom=lambda v: True):
    out = []; prev = None; pv = None
    for i in range(N + 1):
        v = lo + (hi - lo) * i / N
        if not dom(v): prev = None; continue
        fv = f(v)
        if fv == 0:
            if not out or abs(out[-1] - v) > 1e-9: out.append(v)
            prev, pv = None, None; continue
        elif prev is not None and (fv > 0) != (pv > 0): out.append(bisect(f, prev, v))
        prev, pv = v, fv
    return out
def fmt(v, d): s = f'{v:.{d}f}'; return '0' + s[2:] if s.startswith('-0') and float(s) == 0 else s
def disp_num(h, d):  # displayed number string normalized
    t = text(h).replace('−', '-').replace(',', '').replace('$', '')
    return re.search(r'-?\d+(?:\.\d+)?', t).group(0)

def check_rounded(o, true_v, d, getter=None):
    getter = getter or (lambda h: disp_num(h, d))
    ok = getter(o['ch'][o['a']]) == fmt(true_v, d)
    wr = all(getter(c) != fmt(true_v, d) for i, c in enumerate(o['ch']) if i != o['a'])
    return ok and wr, 'shown ' + getter(o['ch'][o['a']]) + ' true ' + fmt(true_v, d)

def correct_only(o, pred):
    res = [bool(pred(c)) for c in o['ch']]
    return res[o['a']] and sum(res) == 1, str(res)

R = random.Random(7)
def rpts(n=6, lo=0.3, hi=6): return [sp.Rational(R.randint(int(lo * 100), int(hi * 100)), 100) for _ in range(n)]

# ---------------- checkers ----------------
def c_oto(o):
    def inj(c):
        f = sp.lambdify(X, rhs(c), 'math'); vals = []
        for i in range(-400, 401):
            v = i / 40
            try:
                y = f(v)
                if isinstance(y, complex) or y != y: continue
                vals.append(y)
            except (ValueError, ZeroDivisionError): continue
        d = [vals[i + 1] - vals[i] for i in range(len(vals) - 1)]
        return all(t > 1e-12 for t in d) or all(t < -1e-12 for t in d)
    return correct_only(o, inj)
def c_tbl(o):
    p = o['p']; x = [p['xs'][i] for i in range(6) if p['ys'][i] == p['y']]
    return correct_only(o, lambda c: len(x) == 1 and sameval(ratval(c), x[0]))
def c_linv(o):
    p = o['p']; f = lambda t: p['a'] * t + p['b']
    def good(c):
        g = rhs(c)
        try: return all(abs(float(f(g.subs(X, v))) - float(v)) < 1e-9 for v in rpts())
        except TypeError: return False   # a distractor such as 1/(4x - 2) can have a pole at a test point: it is not the inverse
    return correct_only(o, good)
def c_gread(o):
    p = o['p']
    if p['type'] == 'line': f = lambda v: p['s'] * v + p['b']; xs = (p['y'] - p['b']) / p['s']
    else: f = lambda v: math.sqrt(v + p['a']) + p['c']; xs = (p['y'] - p['c']) ** 2 - p['a']
    if p['type'] == 'sqrt' and p['y'] < p['c']: return False, 'y below range'
    if any(abs(f(a) - b) > 1e-9 for a, b in p['shown']): return False, 'marked point off curve'
    return correct_only(o, lambda c: sameval(ratval(c), xs))
def c_comp(o):
    p = o['p']; f = lambda t: p['a'] * t + p['b']; g = lambda t: (t + p['c']) / sp.Integer(p['a'])
    fg = sp.expand(f(g(X))); gf = sp.expand(g(f(X))); inv = sp.simplify(fg - X) == 0 and sp.simplify(gf - X) == 0
    def good(c):
        t = text(c); e = parse_expr(pre(c.split(', so')[0]).split('=')[-1], local_dict=LOC, transformations=TR)
        concl_inv = 'not inverses' not in t
        return sp.simplify(e - fg) == 0 and concl_inv == inv
    return correct_only(o, good)
def c_ratinv(o):
    p = o['p']; f = lambda t: (p['a'] * t + p['b']) / (t - p['c'])
    def good(c):
        g = rhs(c)
        for v in rpts(6, 7, 20):
            gv = g.subs(X, v)
            if gv == sp.zoo or gv - p['c'] == 0: return False
            if abs(float(f(gv)) - float(v)) > 1e-9: return False
        return True
    return correct_only(o, good)
def c_sqinv(o):
    p = o['p']; h, k = p['h'], p['k']
    def good(c):
        parts = c.split(', <span class="mth"><i>x</i> ≥ ')
        g = rhs(parts[0]); dom = float(sp.nsimplify(text(parts[1]).replace('−', '-')))
        if dom != k: return False   # domain of f^-1 = range of f = [k, inf)
        for v in rpts(6, 0.1, 9):
            xv = k + v; gv = float(g.subs(X, xv))
            if gv < h - 1e-12 or abs((gv - h) ** 2 + k - float(xv)) > 1e-9: return False
        return True
    return correct_only(o, good)
def c_drinv(o):
    p = o['p']; h, k = p['h'], p['k']
    if any(abs(math.sqrt(a - h) + k - b) > 1e-9 for a, b in p['pts']): return False, 'pt off curve'
    def good(c):
        t = text(c).replace('−', '-'); m = re.findall(r'([\(\[])(-?\d+), inf', t.replace('∞', 'inf'))
        return m == [('[', str(k)), ('[', str(h))] and 'Domain [' in t
    return correct_only(o, good)
def c_taxi(o):
    p = o['p']; true = (p['F'] - p['b']) / p['r']
    def good(c):
        t = text(c).replace('−', '-'); v = float(re.search(r'\) = (-?[\d.]+)', t).group(1))
        return abs(v - true) < 1e-9 and 'pays for a ride of' in t
    return correct_only(o, good)
def c_ratdom(o):
    p = o['p']; a, b, d, e = p['a'], p['b'], p['d'], p['e']; yv = sp.symbols('yv')
    sol = sp.solve(sp.Eq(yv, (a * X + b) / (d * X + e)), X)[0]
    excl = sp.solve(sp.denom(sp.together(sol)), yv)
    if len(excl) != 1: return False, 'excl'
    ex = float(excl[0])
    def good(c):
        mem = ivparse(c); return ivsame(mem, lambda v: abs(v - ex) > 1e-12, ivpts([ex, -e / d, e / d]))
    return correct_only(o, good)
def c_evalexp(o):
    p = o['p']; val = sp.Rational(p['B'][0], p['B'][1]) ** sp.Rational(p['x'][0], p['x'][1])
    return correct_only(o, lambda c: sp.simplify(ratval(c) - val) == 0)
def c_asym(o):
    p = o['p']; b = p['b'][0] / p['b'][1]; f = lambda t: p['a'] * b ** (t - p['h']) + p['k']
    asy = f(-60) if b > 1 else f(60); asy = round(asy, 6); above = f(0) > asy
    def good(c):
        t = text(c).replace('−', '-').replace('∞', 'inf'); m = re.search(r'y = (-?\d+); range \((-?\w+), (-?\w+)\)', t)
        A = float(m.group(1)); up = m.group(3) == 'inf'
        return abs(A - asy) < 1e-6 and up == above and (float(m.group(2)) == A if up else float(m.group(3)) == A)
    return correct_only(o, good)
def eq_from_q(o):
    """Parse the equation shown in the question (left = right) and return a checker for a displayed x."""
    mth = first_math(o['q']); L, Rr = pre(mth).split('=')
    Le = parse_expr(L.strip(), local_dict=LOC, transformations=TR); Re = parse_expr(Rr.strip(), local_dict=LOC, transformations=TR)
    def good(c):
        xv = ratval(c); l = sp.N(Le.subs(X, xv), 60); r = sp.N(Re.subs(X, xv), 60)
        return abs(l - r) <= 1e-40 * max(abs(l), abs(r))   # relative: values can be tiny
    return good
def c_mb1(o): return correct_only(o, eq_from_q(o))
def c_mbase(o): return correct_only(o, eq_from_q(o))
def c_expgraph(o):
    p = o['p']; b = sp.Rational(p['b'][0], p['b'][1]); f = lambda t: float(b) ** (t - p['h']) + p['k']
    if any(abs(f(a) - bb) > 1e-9 for a, bb in p['pts']): return False, 'pt'
    def good(c):
        e = rhs(c); return all(abs(float(e.subs(X, v)) - f(float(v))) < 1e-9 for v in rpts(5, -3, 3))
    return correct_only(o, good)
def c_compound(o):
    p = o['p']; from decimal import Decimal, getcontext; getcontext().prec = 50
    A = Decimal(p['P']) * (Decimal(1) + Decimal(str(p['r'])) / Decimal(p['n'])) ** (p['n'] * p['yrs'])
    return check_rounded(o, float(A), 2)
def c_cont(o):
    p = o['p']; A = p['P'] * math.exp(p['r'] * p['yrs']); v = A if p['want'] == 'bal' else A - p['P']
    return check_rounded(o, v, 2)
def c_reflexp(o):
    p = o['p']; a, b, h, k = p['a'], p['b'], p['h'], p['k']
    f0 = -a * sp.Integer(b) ** (-h) + k  # f(0)
    def good(c):
        t = text(c).replace('−', '-').replace('∞', 'inf')
        m = re.search(r'Range \((-?\w+), (-?\w+)\)', t); down = m.group(1) == '-inf'; edge = float(m.group(2) if down else m.group(1))
        yint = sx(c.split('intercept')[1].split(',')[1].rsplit(')', 1)[0])
        return down and edge == k and sp.simplify(yint - f0) == 0   # graph is below y = k since -a*b^(...) < 0
    return correct_only(o, good)
def c_twopt(o):
    p = o['p']
    def good(c):
        e = rhs(c); return sp.simplify(e.subs(X, p['x1']) - p['y1']) == 0 and sp.simplify(e.subs(X, p['x1'] + 2) - p['y2']) == 0
    return correct_only(o, good)
def c_tolog(o):
    def good(c):
        t = pre(c); lhs, r = t.split('=')
        m = re.search(r'LG\(\((.*?)\),\((.*)\)\)', lhs); B = parse_expr(m.group(1), local_dict=LOC); Av = parse_expr(m.group(2), local_dict=LOC); Cv = parse_expr(r, local_dict=LOC)
        if not (B > 0 and B != 1 and Av > 0): return False
        return sp.simplify(B ** Cv - Av) == 0
    # the statement in the question must be b^e = v
    return correct_only(o, good)
def c_evallog(o):
    p = o['p']; v = sp.Rational(p['v'][0], p['v'][1]); true = sp.nsimplify(sp.log(v) / sp.log(p['b']))
    q = sx(o['q'].split('Evaluate ')[1].split('. Give')[0])
    if sp.simplify(q - true) != 0: return False, 'question mismatch'
    return correct_only(o, lambda c: sp.simplify(ratval(c) - true) == 0)
def c_logeq1(o):
    p = o['p']
    def good(c):
        xv = ratval(c); arg = xv + p['c']
        return arg > 0 and sp.simplify(sp.log(arg) / sp.log(p['b']) - p['e']) == 0
    return correct_only(o, good)
def c_logdom(o):
    p = o['p']; h = p['h']
    return correct_only(o, lambda c: ivsame(ivparse(c), lambda v: v - h > 0, ivpts([h, -h, p['k']])))
def c_loggraph(o):
    p = o['p']; f = lambda t: math.log(t - p['h']) / math.log(p['b']) + p['k']
    if any(abs(f(a) - bb) > 1e-9 for a, bb in p['pts']): return False, 'pt'
    def good2(c):
        e = rhs(c)
        for t in rpts(5, 0.2, 8):
            v = p['h'] + t; ev = complex(sp.N(e.subs(X, v)))
            if abs(ev.imag) > 1e-12 or abs(ev.real - f(float(v))) > 1e-9: return False
        return True
    return correct_only(o, good2)
def first_math(h):
    i = h.index('<span class="mth">'); d = 0; k = i
    while True:
        o_ = h.find('<span', k); c = h.find('</span>', k)
        if o_ != -1 and o_ < c: d += 1; k = o_ + 5
        else:
            d -= 1; k = c + 7
            if d == 0: return h[i:k]
def numeq(e1, e2, n=5):
    for _ in range(n):
        s = {X: rpts(1, 0.5, 4)[0], Y: rpts(1, 0.5, 4)[0], Z: rpts(1, 0.5, 4)[0]}
        if abs(sp.N(e1.subs(s) - e2.subs(s), 30)) > 1e-20: return False
    return True
def c_expand(o):
    qe = sx(first_math(o['q']))
    return correct_only(o, lambda c: numeq(sx(c), qe))
def c_condense(o):
    qe = sx(first_math(o['q']))
    return correct_only(o, lambda c: numeq(sx(c), qe))
def c_lognum(o):
    qe = sp.N(sx(first_math(o['q'])), 30)
    return correct_only(o, lambda c: abs(float(ratval(c)) - float(qe)) < 1e-12)
def c_logbase(o):
    p = o['p']; V = p['V']; e = sp.Rational(p['rhs'][0], p['rhs'][1])
    def good(c):
        s = setparse(c)
        return len(s) == 1 and all(v > 0 and v != 1 and sp.simplify(v ** e - V) == 0 for v in s)
    return correct_only(o, good)
def c_logAB(o):
    p = o['p']; N = sp.Rational(p['N'][0], p['N'][1]); b = 7
    sub = {A_: sp.log(2) / sp.log(b), B_: sp.log(3) / sp.log(b)}; true = sp.log(N) / sp.log(b)
    return correct_only(o, lambda c: abs(sp.N(sx(c).subs(sub) - true, 30)) < 1e-20)
def c_exactlog(o):
    qe = sx(first_math(o['q'].split('exactly: ')[1]))
    v = sp.N(qe, 30)
    return correct_only(o, lambda c: abs(sp.N(ratval(c) - v, 30)) < 1e-20)
def c_cob(o):
    p = o['p']; return check_rounded(o, math.log(p['x']) / math.log(p['a']), 2)
def c_lindom(o):
    p = o['p']; s, c0 = p['s'], p['c']; r0 = -c0 / s
    return correct_only(o, lambda c: ivsame(ivparse(c), lambda v: s * v + c0 > 0, ivpts([r0, -r0])))
def c_cobform(o):
    p = o['p']; true = math.log(p['x']) / math.log(p['a'])
    return correct_only(o, lambda c: abs(float(sp.N(sx(c))) - true) < 1e-12)
def c_ph(o):
    p = o['p']; ph = -math.log10(p['c'] * 10 ** (-p['k'])); cls = 'acidic' if ph < 7 else 'basic'
    def good(c):
        t = text(c).replace('−', '-'); v = re.search(r'≈ (-?[\d.]+)', t).group(1)
        return v == fmt(ph, 1) and t.endswith(cls)
    return correct_only(o, good)
def c_db(o):
    p = o['p']; D = 10 * math.log10(p['c'] * 10 ** p['k']); return check_rounded(o, D, 0)
def c_quaddom(o):
    p = o['p']; f = lambda v: p['lead'] * (v - p['p']) * (v - p['q'])
    return correct_only(o, lambda c: ivsame(ivparse(c), lambda v: f(v) > 0, ivpts([p['p'], p['q']])))
def sci_parse(h):
    t = text(h).replace('−', '-'); m = re.search(r'([\d.]+) × 10\s*(-?\d+)', t); return m.group(1), int(m.group(2))
def c_phinv(o):
    p = o['p']; v = 10 ** (-p['ph']); e = math.floor(math.log10(v)); mt = v / 10 ** e
    true = (fmt(mt, 1), e)
    return correct_only(o, lambda c: sci_parse(c) == true)
def c_dbratio(o):
    p = o['p']; ratio = 10 ** ((p['D1'] - p['D2']) / 10)
    def val(c):
        t = conv(tree(c)).replace(',', '')
        m = re.match(r'\s*10\*\*\((\d+)\)', t)
        return 10 ** int(m.group(1)) if m else float(re.search(r'[\d.]+', t).group(0))
    return correct_only(o, lambda c: abs(val(c) - ratio) < 1e-9)
def c_sumdom(o):
    qe = first_math(o['q'])
    # independent: evaluate the displayed function where both log arguments are positive
    e = rhs(qe)
    def defined(v):
        try:
            val = complex(sp.N(e.subs(X, v)))
            return abs(val.imag) < 1e-12 and math.isfinite(val.real)
        except Exception: return False
    pts = [k / 2 for k in range(-24, 25)]
    pred = {v: defined(v) for v in pts}
    return correct_only(o, lambda c: all(ivparse(c)(v) == pred[v] for v in pts))
def solve_round(o, F, lo, hi, d, dom=lambda v: True):
    r = roots_scan(F, lo, hi, 20000, dom)
    if len(r) != 1: return False, 'roots ' + str(r)
    return check_rounded(o, r[0], d)
def c_axc(o): p = o['p']; return solve_round(o, lambda v: p['a'] ** v - p['c'], -5, 20, 2)
def c_ekx(o): p = o['p']; return solve_round(o, lambda v: math.exp(p['k'] * v) - p['c'], -1, 5 / p['k'], 2)
def c_lnx(o):
    p = o['p']; F = (lambda v: math.log(v) - p['d']) if p['useLn'] else (lambda v: math.log10(v) - p['d'])
    r = roots_scan(F, 0.01, 40000, 400000);
    return check_rounded(o, r[0], 2) if len(r) == 1 else (False, 'roots')
def c_exact(o):
    p = o['p']; true = math.log(p['c']) / math.log(p['a'])
    return correct_only(o, lambda c: abs(float(sp.N(rhs(c))) - true) < 1e-12)
def c_axpq(o): p = o['p']; return solve_round(o, lambda v: p['a'] ** (p['p'] * v + p['q']) - p['c'], -10, 20, 2)
def logsol_set(F, dom, lo, hi):
    r = roots_scan(F, lo, hi, 60000, dom); return set(sp.nsimplify(round(v, 6)) for v in r)
def c_logext(o):
    p = o['p']; b = p['b']; d = p['d']
    dom = lambda v: v > 0 and v + d > 0
    F = lambda v: math.log(v * (v + d)) / math.log(b) - p['nn']
    sols = logsol_set(F, dom, -60, 120)
    return correct_only(o, lambda c: setparse(c) == sols)
def c_logext2(o):
    p = o['p']; a, c0, Kv = p['a'], p['c'], p['K']
    dom = lambda v: v + a > 0 and v - c0 > 0
    F = lambda v: math.log(v + a) + math.log(v - c0) - math.log(Kv)
    sols = logsol_set(F, dom, -60, 80)
    return correct_only(o, lambda c: setparse(c) == sols)
def c_qform(o):
    p = o['p']; F = lambda v: math.exp(2 * v) + (p['q'] - p['p']) * math.exp(v) - p['p'] * p['q']
    r = roots_scan(F, -10, 10, 20000)
    if len(r) != 1: return False, 'roots'
    true = fmt(r[0], 2)
    def good(c):
        t = text(c).replace('−', '-'); vals = re.findall(r'x\s*[≈=]\s*(-?[\d.]+)', t)
        return '≈' in t and vals == [true]
    return correct_only(o, good)
def c_qform2(o):
    p = o['p']; B = p['B']; F = lambda v: (B * B) ** v - p['S'] * B ** v + p['Pr']
    r = roots_scan(F, -6, 8, 28000)
    sols = set(sp.nsimplify(round(v, 6)) for v in r)
    return correct_only(o, lambda c: 'only' not in text(c) and setparse(c) == sols)
def c_ttime(o):
    p = o['p']
    F = (lambda t: p['P'] * math.exp(p['r'] * t) - p['A']) if p['n'] == 0 else (lambda t: p['P'] * (1 + p['r'] / p['n']) ** (p['n'] * t) - p['A'])
    return check_rounded(o, bisect(F, 0, 200), 2)
def c_axbx(o): p = o['p']; return solve_round(o, lambda v: v * math.log(p['a']) - (v + p['c']) * math.log(p['b']), -400, 400, 2)
def c_model(o): p = o['p']; return check_rounded(o, p['A0'] * math.exp(p['k'] * p['tt']), 1)
def c_halfk(o):
    p = o['p']; k = bisect(lambda k: math.exp(k * p['h']) - 0.5, -5, 0); return check_rounded(o, k, 4)
def c_dbl(o):
    p = o['p']; t = bisect(lambda t: math.exp(p['k'] * t) - 2, 0, 1000); return check_rounded(o, t, 2)
def hund(h): return disp_num(h, 0)
def k4(k): return round(k, 4)
def also_k4(o, res, v_true, v_k4, d):
    """The stem says to keep k unrounded; the marked answer must also survive a student rounding k to 4 places (as the lesson displays it)."""
    ok, info = res
    same = fmt(v_true, d) == fmt(v_k4, d)
    say = 'unrounded' in text(o['q'])
    return ok and same and say, info + ('' if same else ' | k rounded to 4 places gives ' + fmt(v_k4, d)) + ('' if say else ' | stem lacks keep-k-unrounded note')
def c_predict(o):
    p = o['p']; k = bisect(lambda k: p['P0'] * math.exp(k * p['t1']) - p['P1'], -1, 1)
    v = p['P0'] * math.exp(k * p['t2']); v4 = p['P0'] * math.exp(k4(k) * p['t2'])
    return also_k4(o, check_rounded(o, round(v / 100) * 100, 0), round(v / 100) * 100, round(v4 / 100) * 100, 0)
def c_carbon(o):
    p = o['p']; k = bisect(lambda k: math.exp(k * 5730) - 0.5, -1, 0); t = bisect(lambda t: math.exp(k * t) - p['f'], 0, 100000)
    ok, info = check_rounded(o, round(t / 100) * 100, 0)
    return ok and 'unrounded' in text(o['q']), info
def c_halfleft(o):
    p = o['p']; k = bisect(lambda k: math.exp(k * p['h']) - 0.5, -5, 0)
    return also_k4(o, check_rounded(o, p['A0'] * math.exp(k * p['tt']), 1), p['A0'] * math.exp(k * p['tt']), p['A0'] * math.exp(k4(k) * p['tt']), 1)
def c_reach(o):
    p = o['p']; k = bisect(lambda k: p['P0'] * math.exp(k * p['t1']) - p['P1'], 0, 5); t = bisect(lambda t: p['P0'] * math.exp(k * t) - p['T'], 0, 1000)
    t4 = math.log(p['T'] / p['P0']) / k4(k)
    return also_k4(o, check_rounded(o, t, 1), t, t4, 1)
def c_cool(o):
    p = o['p']; Ts, T0 = p['Ts'], p['T0']
    k = bisect(lambda k: Ts + (T0 - Ts) * math.exp(k * p['t1']) - p['T1'], -5, 0)
    v = Ts + (T0 - Ts) * math.exp(k * p['t2']); v4 = Ts + (T0 - Ts) * math.exp(k4(k) * p['t2'])
    return also_k4(o, check_rounded(o, v, 0), v, v4, 0)
def c_halfdata(o):
    p = o['p']; k = bisect(lambda k: p['A0'] * math.exp(k * p['t1']) - p['A1'], -5, 0); h = bisect(lambda t: math.exp(k * t) - 0.5, 0, 10000)
    return also_k4(o, check_rounded(o, h, 1), h, -math.log(2) / k4(k), 1)

def c_pv(o):
    """present value: independent Decimal computation of A / (1 + r/n)^(nt); also checks that the marked value grows back to A."""
    p = o['p']; from decimal import Decimal, getcontext; getcontext().prec = 50
    g = (Decimal(1) + Decimal(str(p['r'])) / Decimal(p['n'])) ** (p['n'] * p['yrs'])
    Pv = Decimal(p['A']) / g
    ok, info = check_rounded(o, float(Pv), 2)
    shown = Decimal(disp_num(o['ch'][o['a']], 2))
    return ok and abs(shown * g - Decimal(p['A'])) < Decimal('0.01') * g, info
def c_invprop(o):
    """evaluate the displayed expression itself with sympy (no use of the generator's answer)"""
    q = text(o['q']).split('calculator: ')[1].replace('−', '-')
    mm = re.match(r'(\d+)log_?(\d+) (\d+) ([+-]) log_?(\d+) (\S+)$', q.replace('^', '').replace('@', ''))
    p = o['p']; a, N, b = sp.Integer(p['a']), sp.Integer(p['N']), sp.Integer(p['b'])
    first = sp.simplify(a ** (sp.log(N) / sp.log(a)))
    arg = {'pow': b ** p['k'], 'one': sp.Integer(1), 'base': b}[p['kind']]
    second = sp.simplify(sp.log(arg) / sp.log(b))
    val = first + second if p['plus'] else first - second
    # the question text must show the same pieces the parameters describe
    shown_ok = ('%d' % p['a']) in q and ('%d' % p['N']) in q and (' + ' in q) == p['plus']
    return correct_only(o, lambda c: sp.Integer(int(disp_num(c, 0))) == val and re.fullmatch(r'-?\d+', text(c).replace('−', '-')) is not None) if shown_ok else (False, 'question text mismatch')
def c_givenlog(o):
    """factor N into 2, 3, 5 with sympy; log 5 = 1 - log 2; apply the given 4-place values; root halves everything"""
    p = o['p']; N = sp.Rational(p['N'][0], p['N'][1])
    fac = {}
    for part, sgn in ((sp.numer(N), 1), (sp.denom(N), -1)):
        for pr, e in sp.factorint(part).items(): fac[pr] = fac.get(pr, 0) + sgn * e
    assert set(fac) <= {2, 3, 5}
    L2, L3 = sp.Rational(3010, 10000), sp.Rational(4771, 10000)
    v = fac.get(2, 0) * L2 + fac.get(3, 0) * L3 + fac.get(5, 0) * (1 - L2)
    if p['root']: v = v / 2
    # the value shown in the question must be N (or its square root)
    qt = text(o['q'])
    if p['root']: assert ('√' + str(N)) in qt
    v4 = float(v)
    good = lambda c: disp_num(c, 4) == fmt(v4, 4)
    ok, info = correct_only(o, good)
    exact4 = (v * 10000).q == 1   # the given values make the answer exact to 4 places
    return ok and exact4, info

CHK = {k[2:]: v for k, v in globals().items() if k.startswith('c_')}

# ---------------- general checks + run ----------------
fails = defaultdict(list); counts = Counter()
for o in data:
    key = '%s L%d gen%d (%s)' % (o['id'], o['lv'], o['gi'], o['p']['t']); counts[key] += 1
    try:
        assert len(o['ch']) == 4 and len(set(text(c) for c in o['ch'])) == 4
        res = CHK[o['p']['t']](o)
        ok, info = res if isinstance(res, tuple) else (res, '')
    except Exception as e:
        ok, info = False, 'EXC ' + repr(e)[:200]
    if not ok: fails[key].append(text(o['q'])[:150] + ' || ' + ' | '.join(text(c) for c in o['ch']) + ' || ans ' + str(o['a']) + ' || ' + str(info)[:200])

print('generators checked:', len(counts), ' cases:', sum(counts.values()), ' min cases per generator:', min(counts.values()))
for k in sorted(fails):
    print('FAIL', k, len(fails[k]), 'of', counts[k]); [print('   ', f) for f in fails[k][:3]]
print('failures:', sum(len(v) for v in fails.values()))
