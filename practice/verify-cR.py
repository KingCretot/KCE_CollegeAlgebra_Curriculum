#!/usr/bin/env python3
"""Independent math check for gen-cR.js (Chapter R practice generators).

Runs every generator RUNS times (via Node), then re-derives each correct answer with
independent methods: the displayed HTML of the question and of every choice is parsed into
SymPy, set questions are recomputed with Python sets, counts by brute-force enumeration,
number classes by SymPy, and so on. Checks:
  * the marked answer is correct;
  * no distractor is mathematically equal to the correct answer;
  * extra form checks: complete factorization, lowest terms, simplified radicals,
    positive exponents.
Usage: python3 verify-cR.py [runs]
"""
import json, re, subprocess, sys, os, itertools, random
from html.parser import HTMLParser
from fractions import Fraction
import sympy as sp

RUNS = int(sys.argv[1]) if len(sys.argv) > 1 else 220
HERE = os.path.dirname(os.path.abspath(__file__))

DUMP = r"""
global.window = undefined;
const K = require('./core.js'); require('./gen-cR.js');
const RUNS = +process.argv[1]; const out = [];
for (const id of Object.keys(K.lessons)) { if (id === 'RR') continue;
  K.lessons[id].levels.forEach((gens, lv) => gens.forEach((g, gi) => {
    for (let r = 0; r < RUNS; r++) { K._gd = []; const q = g();
      out.push({ id, lv: lv + 1, gi, q: q.q, ch: q.ch, a: q.a, p: q.p || null, gd: K._gd.slice() }); } })); }
process.stdout.write(JSON.stringify(out));
"""

# ---------------------------------------------------------------- HTML → tree
class Node:
    def __init__(self, tag, attrs):
        self.tag, self.attrs, self.kids = tag, dict(attrs), []
    def cls(self):
        return self.attrs.get('class', '') or ''

class TreeP(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = Node('root', []); self.stack = [self.root]
    def handle_starttag(self, tag, attrs):
        n = Node(tag, attrs); self.stack[-1].kids.append(n)
        if tag not in ('br', 'img'): self.stack.append(n)
    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i].tag == tag:
                del self.stack[i:]; break
    def handle_data(self, d):
        self.stack[-1].kids.append(d)

def tree(h):
    p = TreeP(); p.feed(h); return p.root

def text(h):
    def t(n):
        if isinstance(n, str): return n
        return ''.join(t(k) for k in n.kids)
    return t(tree(h)).replace('−', '-')

# ---------------------------------------------------------------- tree → SymPy source
def emit(n):
    if isinstance(n, str):
        s = n.replace('−', '-').replace('·', '*').replace('÷', '/').replace('×', '*').replace('π', ' pi ')
        s = s.replace('[', '(').replace(']', ')').replace(' ft', '').replace('$', '').replace(',', '')
        return s
    c = n.cls()
    if n.tag == 'i':
        return ' ' + ''.join(emit(k) for k in n.kids).strip() + ' '
    if n.tag == 'sup' and 'ri' not in c:
        return '**(' + ''.join(emit(k) for k in n.kids) + ')'
    if n.tag == 'span' and 'fr' in c.split():
        nu = [k for k in n.kids if not isinstance(k, str) and k.cls() == 'nu'][0]
        de = [k for k in n.kids if not isinstance(k, str) and k.cls() == 'de'][0]
        return '((' + emit(nu) + ')/(' + emit(de) + '))'
    if n.tag == 'span' and 'rad' in c.split():
        idx = 2; rc = None
        for k in n.kids:
            if isinstance(k, str): continue
            if k.tag == 'sup' and 'ri' in k.cls(): idx = int(text_of(k))
            if k.cls() == 'rc': rc = k
        return ' root((' + emit(rc) + '),' + str(idx) + ') '
    if n.tag == 'span' and 'overline' in n.attrs.get('style', ''):
        return '~' + text_of(n) + '~'
    return ''.join(emit(k) for k in n.kids)

def text_of(n):
    if isinstance(n, str): return n
    return ''.join(text_of(k) for k in n.kids)

FUNCS = {'root', 'rpow', 'Abs', 'Rational'}
def implicit(s):
    toks = re.findall(r'\d+\.\d+|\d+|[A-Za-z_]+|\*\*|[-+*/(),]', s)
    out = []; prev = None
    for t in toks:
        kind = 'num' if re.match(r'\d', t) else ('name' if re.match(r'[A-Za-z_]', t) else t)
        if prev is not None:
            pk, pt = prev
            if (pk in ('num', 'name') and not (pk == 'name' and pt in FUNCS) or pk == ')') and (kind in ('num', 'name') or kind == '('):
                out.append('*')
        out.append(t); prev = (kind, t)
    return ' '.join(out)

def to_src(h):
    s = emit(tree(h))
    # repeating decimals  0.~3~  →  Rational
    def repl(mo):
        sign, ip, fp, rp = mo.group(1), mo.group(2), mo.group(3), mo.group(4)
        v = Fraction(int(ip)) + (Fraction(int(fp), 10 ** len(fp)) if fp else 0) + Fraction(int(rp), (10 ** len(rp) - 1) * 10 ** len(fp))
        if sign: v = -v
        return ' Rational(%d,%d) ' % (v.numerator, v.denominator)
    s = re.sub(r'(-?)(\d+)\.(\d*)~(\d+)~', repl, s)
    # absolute value bars, alternately opening and closing
    out, open_ = '', False
    for ch in s:
        if ch == '|':
            out += ' Abs(' if not open_ else ')'; open_ = not open_
        else: out += ch
    s = out
    s = implicit(s)
    # numeric negative base in parentheses raised to a power → real-valued rpow
    s = re.sub(r'\( - (\d+) \) \*\* \(([^()]*)\)', lambda mo: ' rpow(-' + mo.group(1) + ', (' + mo.group(2) + ')) ', s)
    return s

x, y, z, a, b, u = sp.symbols('x y z a b u', positive=True)
NAN = sp.nan
def root(e, nidx):
    e = sp.sympify(e)
    if e.is_number and e.is_negative:
        if nidx % 2 == 1: return -((-e) ** sp.Rational(1, nidx))
        return NAN
    return e ** sp.Rational(1, nidx)
def rpow(base, ex):
    ex = sp.Rational(ex); base = sp.sympify(base)
    if base.is_negative:
        if ex.q % 2 == 1: return (-1) ** ex.p * (-base) ** ex
        return NAN
    return base ** ex
NS = {'x': x, 'y': y, 'z': z, 'a': a, 'b': b, 'u': u, 'root': root, 'rpow': rpow, 'Abs': sp.Abs, 'pi': sp.pi, 'Rational': sp.Rational}

def P(h, ns=None):
    return sp.parse_expr(to_src(h), local_dict=dict(ns or NS))

PTS = [{x: sp.Rational(137, 100), y: sp.Rational(29, 10), a: sp.Rational(7, 5), b: sp.Rational(23, 10), z: sp.Rational(11, 7), u: sp.Rational(5, 3)},
       {x: sp.Rational(271, 100), y: sp.Rational(13, 10), a: sp.Rational(31, 10), b: sp.Rational(3, 7), z: sp.Rational(9, 4), u: sp.Rational(7, 2)},
       {x: sp.Rational(43, 7), y: sp.Rational(19, 5), a: sp.Rational(2, 9), b: sp.Rational(41, 6), z: sp.Rational(3, 11), u: sp.Rational(1, 3)}]

def val(e, pt):
    v = sp.sympify(e).subs(pt)
    return complex(sp.N(v, 30))

def eq(e1, e2):
    if e1 is NAN or e2 is NAN: return e1 is e2
    for pt in PTS:
        try:
            v1, v2 = val(e1, pt), val(e2, pt)
        except Exception:
            return False
        if abs(v1 - v2) > 1e-12 * (1 + abs(v1)): return False
    return True

# ---------------------------------------------------------------- form checks
def top_fraction(h):
    """If the choice is a single stacked fraction (optionally preceded by a minus), return (nu_html_tree, de_tree)."""
    r = tree(h)
    def strip_m(n):
        while not isinstance(n, str) and len([k for k in n.kids if not (isinstance(k, str) and not k.strip())]) == 1 and not ('fr' in n.cls().split()):
            n = [k for k in n.kids if not (isinstance(k, str) and not k.strip())][0]
        return n
    n = strip_m(r)
    if not isinstance(n, str) and 'fr' in n.cls().split():
        nu = [k for k in n.kids if not isinstance(k, str) and k.cls() == 'nu'][0]
        de = [k for k in n.kids if not isinstance(k, str) and k.cls() == 'de'][0]
        return nu, de
    return None

def src_of_node(nd):
    return to_src_tree(nd)
def to_src_tree(nd):
    s = emit(nd); s = implicit(s); return s
def Pn(nd):
    return sp.parse_expr(to_src_tree(nd), local_dict=dict(NS))

def check_factor(h, target):
    """Complete factorization over the integers: product equals target, every non-constant factor is
    irreducible and primitive."""
    src = to_src(h)
    e = sp.parse_expr(src, local_dict=dict(NS), evaluate=False)
    args = e.args if isinstance(e, sp.Mul) else (e,)
    for f in args:
        base = f
        if isinstance(f, sp.Pow) and f.exp.is_Integer: base = f.base
        if base.is_number: continue
        cont, fl = sp.factor_list(sp.expand(base))
        tot = sum(m for _, m in fl)
        if tot != 1: return 'factor %s not irreducible' % base
        if abs(cont) != 1: return 'factor %s not primitive' % base
    return None

def check_lowest(h):
    tf = top_fraction(h)
    if not tf: return None
    nu, de = Pn(tf[0]), Pn(tf[1])
    g = sp.gcd(sp.expand(nu), sp.expand(de))
    if not g.is_number: return 'not in lowest terms (common factor %s)' % g
    return None

def rad_nodes(nd, acc):
    if isinstance(nd, str): return acc
    if nd.tag == 'span' and 'rad' in nd.cls().split(): acc.append(nd)
    for k in nd.kids: rad_nodes(k, acc)
    return acc

def check_rad(h):
    r = tree(h)
    for rn in rad_nodes(r, []):
        idx = 2; rc = None
        for k in rn.kids:
            if isinstance(k, str): continue
            if k.tag == 'sup' and 'ri' in k.cls(): idx = int(text_of(k))
            if k.cls() == 'rc': rc = k
        e = sp.sympify(Pn(rc))
        cst, rest = e.as_coeff_Mul()
        if cst != int(cst): return 'fraction under radical'
        cst = int(cst)
        for pr, mlt in sp.factorint(abs(cst)).items():
            if mlt >= idx: return 'radicand %s has a perfect power factor' % cst
        for s in rest.free_symbols:
            d = sp.degree(rest, s)
            if d >= idx: return 'variable power %s under index %d' % (d, idx)
    tf = top_fraction(h)
    if tf:
        if rad_nodes(tf[1], []): return 'radical in the denominator'
        nu, de = sp.expand(Pn(tf[0])), Pn(tf[1])
        if de.is_Integer:
            coeffs = [c for c in nu.as_coefficients_dict().values()]
            g = 0
            for c in coeffs: g = sp.gcd(g, c)
            if sp.gcd(g, de) != 1: return 'fraction not reduced'
    return None

# ---------------------------------------------------------------- sets
def parse_set(t):
    t = t.strip()
    if t == '∅': return frozenset()
    assert t[0] == '{' and t[-1] == '}', t
    body = t[1:-1].strip()
    if not body: return frozenset()
    out = []
    for e in body.split(','):
        e = e.strip()
        out.append(int(e) if re.match(r'^-?\d+$', e) else e)
    return frozenset(out)

def sets_from_q(qt):
    S = {}
    for name in ['A', 'B', 'C', 'S']:
        mo = re.search(r'\b' + name + r' = (\{[^}]*\})', qt)
        if mo and '…' not in mo.group(1) and '|' not in mo.group(1): S[name] = parse_set(mo.group(1))
    mo = re.search(r'U = \{1, 2, 3, …, (\d+)\}', qt)
    if mo: S['U'] = frozenset(range(1, int(mo.group(1)) + 1))
    return S

def eval_op(op, S):
    toks = re.findall(r"[ABCU]|′|∪|∩|\(|\)", op)
    pos = [0]
    def peek(): return toks[pos[0]] if pos[0] < len(toks) else None
    def take(): pos[0] += 1; return toks[pos[0] - 1]
    def atom():
        t = take()
        if t == '(':
            v = expr(); assert take() == ')'; r = v
        else: r = S[t]
        while peek() == '′': take(); r = S['U'] - r
        return r
    def expr():
        v = atom()
        while peek() in ('∪', '∩'):
            o = take(); w = atom(); v = (v | w) if o == '∪' else (v & w)
        return v
    v = expr(); assert pos[0] == len(toks), op
    return v

def roster_from_text(qt):
    mo = re.search(r'x is a natural number between (\d+) and (\d+)', qt)
    if mo: lo, hi = int(mo.group(1)), int(mo.group(2)); return frozenset(k for k in range(1, 200) if lo < k < hi)
    mo = re.search(r'x is an integer and (-?\d+) ≤ x < (-?\d+)', qt)
    if mo: lo, hi = int(mo.group(1)), int(mo.group(2)); return frozenset(k for k in range(-200, 200) if lo <= k < hi)
    mo = re.search(r'x is an integer and (-?\d+) ≤ x ≤ (-?\d+)', qt)
    if mo: lo, hi = int(mo.group(1)), int(mo.group(2)); return frozenset(k for k in range(-200, 200) if lo <= k <= hi)
    mo = re.search(r'x is an (even|odd) natural number less than (\d+)', qt)
    if mo:
        par = 0 if mo.group(1) == 'even' else 1; N = int(mo.group(2))
        return frozenset(k for k in range(1, N) if k % 2 == par)
    raise ValueError('no set-builder pattern: ' + qt)

def n_subsets(Sx, pred=lambda s: True):
    L = list(Sx); c = 0
    for r in range(len(L) + 1):
        for comb in itertools.combinations(L, r):
            if pred(set(comb)): c += 1
    return c

# ---------------------------------------------------------------- statements (R.1 truth, R.2 properties)
def stmt_true(st, S):
    st = st.replace('−', '-')
    for op in ['∉', '∈', '⊆']:
        if op in st:
            L, Rr = [t.strip() for t in st.split(op)]
            break
    def obj(t):
        if t == 'S': return S
        if t == '∅': return frozenset()
        if t.startswith('{'): return parse_set(t)
        return int(t)
    Lo, Ro = obj(L), obj(Rr)
    if op == '∈': return isinstance(Ro, frozenset) and (Lo in Ro)
    if op == '∉': return isinstance(Ro, frozenset) and not isinstance(Lo, frozenset) and (Lo not in Ro)
    if op == '⊆': return isinstance(Lo, frozenset) and isinstance(Ro, frozenset) and Lo <= Ro

def prop_tokens(h):
    """tokenize a property statement: numbers, variables, fractions (as Fraction), + − · ( ) ="""
    r = tree(h); toks = []
    def walk(nd):
        if isinstance(nd, str):
            for t in re.findall(r'\d+|[a-z]|[+−·()=]', nd): toks.append(t)
            return
        if nd.tag == 'span' and 'fr' in nd.cls().split():
            nu = text_of([k for k in nd.kids if not isinstance(k, str) and k.cls() == 'nu'][0])
            de = text_of([k for k in nd.kids if not isinstance(k, str) and k.cls() == 'de'][0])
            toks.append(Fraction(int(nu), int(de))); return
        for k in nd.kids: walk(k)
    walk(r); return toks

def prop_parse(toks):
    pos = [0]
    def peek(): return toks[pos[0]] if pos[0] < len(toks) else None
    def take(): pos[0] += 1; return toks[pos[0] - 1]
    def factor():
        t = take()
        if t == '(':
            if peek() == '−':
                take(); inner = term(); assert take() == ')'; return ('neg', inner)
            e = expr(); assert take() == ')'; return ('grp', e)
        if isinstance(t, Fraction): return ('num', t)
        if re.match(r'\d', t):
            node = ('num', Fraction(int(t)))
            if peek() is not None and isinstance(peek(), str) and re.match(r'[a-z]', peek()):
                v = take(); return ('*', node, ('var', v), 'tight')
            return node
        if re.match(r'[a-z]', t): return ('var', t)
        raise ValueError(t)
    def term():
        f = factor()
        while True:
            pk = peek()
            if pk == '·': take(); f = ('*', f, factor())
            elif pk == '(' : f = ('*', f, factor())
            elif isinstance(pk, str) and re.match(r'[a-z]', pk): f = ('*', f, factor())
            else: break
        return f
    def expr():
        e = term()
        while peek() in ('+', '−'):
            o = take(); t2 = term(); e = ('+', e, t2) if o == '+' else ('-', e, t2)
        return e
    L = expr(); assert take() == '='; Rr = expr(); assert pos[0] == len(toks)
    return L, Rr

def un(e):  # remove grouping wrapper
    while e[0] == 'grp': e = e[1]
    return e
def ev(e):
    e = un(e)
    k = e[0]
    if k == 'num': return sp.Rational(e[1].numerator, e[1].denominator)
    if k == 'var': return sp.Symbol(e[1])
    if k == 'neg': return -ev(e[1])
    if k == '*': return ev(e[1]) * ev(e[2])
    if k == '+': return ev(e[1]) + ev(e[2])
    if k == '-': return ev(e[1]) - ev(e[2])
def same_tree(p, q):
    return sp.simplify(ev(p) - ev(q)) == 0 and strip_g(p) == strip_g(q)
def strip_g(e):
    if isinstance(e, tuple):
        if e[0] == 'grp': return strip_g(e[1])
        return tuple(strip_g(t) for t in e if t != 'tight')
    return e

def classify_prop(h):
    L, Rr = prop_parse(prop_tokens(h))
    if sp.simplify(ev(L) - ev(Rr)) != 0: return 'NOT AN IDENTITY'
    Ls, Rs = strip_g(L), strip_g(Rr)
    found = []
    for A, B in [(Ls, Rs), (Rs, Ls)]:
        # identity / inverse
        if B == ('num', 0) and A[0] == '+' and ((A[2] == ('neg', A[1])) or (A[1] == ('neg', A[2]))): found.append('Inverse property of addition')
        if B == ('num', 1) and A[0] == '*' and A[1] != ('num', 1) and A[2] != ('num', 1) and sp.simplify(ev(A[1]) * ev(A[2]) - 1) == 0: found.append('Inverse property of multiplication')
        if A[0] == '+' and (A[1] == ('num', 0) and A[2] == B or A[2] == ('num', 0) and A[1] == B): found.append('Identity property of addition')
        if A[0] == '*' and (A[1] == ('num', 1) and A[2] == B or A[2] == ('num', 1) and A[1] == B): found.append('Identity property of multiplication')
    if Ls[0] == Rs[0] and Ls[0] in '+*' and len(Ls) == 3 and Ls[1] == Rs[2] and Ls[2] == Rs[1] and Ls[1] != Ls[2]:
        found.append('Commutative property of ' + ('addition' if Ls[0] == '+' else 'multiplication'))
    for A, B in [(Ls, Rs), (Rs, Ls)]:
        if A[0] == B[0] and A[0] in '+*' and A[1][0] == A[0] and B[2][0] == B[0] and A[1][1] == B[1] and A[1][2] == B[2][1] and A[2] == B[2][2]:
            found.append('Associative property of ' + ('addition' if A[0] == '+' else 'multiplication'))
        if A[0] == '*' and (A[2][0] == '+' or A[1][0] == '+') and B[0] == '+':
            found.append('Distributive property')
    found = sorted(set(found))
    return found[0] if len(found) == 1 else 'AMBIGUOUS ' + str(found)

# ---------------------------------------------------------------- number classes
def ncls(v):
    v = sp.nsimplify(v) if not v.is_Rational else v
    if v.is_rational is False: return 'irr'
    if v.is_integer:
        return 'nat' if v > 0 else ('zero' if v == 0 else 'neg')
    if v.is_rational: return 'ratn'
    return '?'

# ---------------------------------------------------------------- main
def main():
    res = subprocess.run(['node', '-e', DUMP, str(RUNS)], cwd=HERE, capture_output=True, text=True, check=True)
    data = json.loads(res.stdout)
    fails, warns = [], []
    counts = {}
    def F(d, msg):
        fails.append('%s L%d gen%d: %s :: %s' % (d['id'], d['lv'], d['gi'], msg, text(d['q'])[:140]))
    for d in data:
        key = (d['id'], d['lv'], d['gi']); counts[key] = counts.get(key, 0) + 1
        p = d['p'] or {}; t = p.get('t'); q = d['q']; qt = text(q); ch = d['ch']; A = d['a']
        try:
            if t == 'roster':
                exp = roster_from_text(qt)
                got = [parse_set(text(c)) for c in ch]
                if got[A] != exp: F(d, 'wrong roster %s vs %s' % (sorted(got[A]), sorted(exp)))
                if sum(g == exp for g in got) != 1: F(d, 'distractor equals answer')
            elif t in ('set', 'mult'):
                if t == 'set': S = sets_from_q(qt)
                else:
                    S = sets_from_q(qt); mul = [int(z) for z in re.findall(r'multiple of (\d+)', qt)]
                    S['A'] = frozenset(k for k in S['U'] if k % mul[0] == 0); S['B'] = frozenset(k for k in S['U'] if k % mul[1] == 0)
                if 'U' not in S: S['U'] = frozenset().union(*[v for v in S.values()])
                op = text(p['op']).strip()
                if op not in qt: F(d, 'op not in question')
                exp = eval_op(op, S)
                got = [parse_set(text(c)) for c in ch]
                if got[A] != exp: F(d, 'wrong set %s vs %s' % (sorted(got[A], key=str), sorted(exp, key=str)))
                if sum(g == exp for g in got) != 1: F(d, 'distractor equals answer')
            elif t == 'count':
                mode = p['mode']
                if mode == 'union':
                    S = sets_from_q(qt); base = S['A'] | S['B']; exp = n_subsets(base)
                elif mode == 'contain':
                    S = parse_set(re.search(r'subsets of (\{[^}]*\})', qt).group(1)); e = int(re.search(r'contain the element (-?\d+)', qt).group(1))
                    exp = n_subsets(S, lambda s: e in s)
                else:
                    if '|' in qt: S = roster_from_text(qt)
                    else: S = parse_set(re.search(r'(\{[^}]*\})', qt).group(1))
                    exp = n_subsets(S) - (1 if mode == 'proper' else 0)
                got = [int(text(c)) for c in ch]
                if got[A] != exp: F(d, 'count %s vs %s' % (got[A], exp))
                if got.count(exp) != 1: F(d, 'dup')
            elif t == 'truth':
                S = sets_from_q(qt)['S']
                tv = [stmt_true(text(c).strip(), S) for c in ch]
                if not tv[A] or sum(tv) != 1: F(d, 'truth values %s' % tv)
            elif t == 'num':
                if p['eh'] not in q: F(d, 'eh not in q')
                e = P(p['eh'], dict(NS, x=sp.Symbol('x'), y=sp.Symbol('y')) if 'vars' in p else None)
                if 'vars' in p:
                    for k, v in p['vars'].items():
                        if not re.search(k + r' = ' + str(v).replace('-', '-') + r'\b', qt): F(d, 'var value not shown')
                    e = e.subs({sp.Symbol(k): v for k, v in p['vars'].items()})
                vals = []
                for c in ch:
                    tc = text(c)
                    vals.append(NAN if 'Not a real number' in tc else sp.nsimplify(P(c)))
                if e is NAN or (hasattr(e, 'has') and e.has(sp.nan)): e = NAN
                else: e = sp.nsimplify(e)
                if not (vals[A] is NAN and e is NAN) and (vals[A] is NAN or e is NAN or sp.simplify(vals[A] - e) != 0): F(d, 'num %s vs %s' % (vals[A], e))
                if sum(1 for v in vals if (v is NAN and e is NAN) or (v is not NAN and e is not NAN and sp.simplify(v - e) == 0)) != 1: F(d, 'distractor equal')
            elif t == 'dist':
                if p.get('nl'):
                    dots = [int(z.replace('−', '-')) for z in re.findall(r'closed dot at ([−-]?\d+)', ' '.join(d['gd']))]
                    assert len(dots) == 2
                    exp = abs(dots[0] - dots[1])
                else:
                    mo = re.search(r'between (-?\d+) and (-?\d+)', qt); exp = abs(int(mo.group(1)) - int(mo.group(2)))
                got = [int(text(c)) for c in ch]
                if got[A] != exp or got.count(exp) != 1: F(d, 'dist %s vs %s' % (got[A], exp))
            elif t == 'classify':
                cl = [ncls(P(c)) for c in ch]
                phrase = {'nat': 'a natural number', 'zero': 'a whole number but not a natural number', 'neg': 'an integer but not a whole number', 'ratn': 'a rational number but not an integer', 'irr': 'irrational' if 'irrational' in qt else 'a real number but not a rational number', 'rat': 'rational'}[p['cls']]
                if phrase not in qt: F(d, 'phrase mismatch')
                okf = {'nat': lambda c: c == 'nat', 'zero': lambda c: c == 'zero', 'neg': lambda c: c == 'neg', 'ratn': lambda c: c == 'ratn', 'irr': lambda c: c == 'irr', 'rat': lambda c: c in ('nat', 'zero', 'neg', 'ratn')}[p['cls']]
                good = [okf(c) for c in cl]
                if not good[A] or sum(good) != 1: F(d, 'classify %s' % cl)
            elif t == 'classset':
                items = p['items']
                for it in items:
                    if it not in q: F(d, 'item missing')
                cls = [ncls(P(it)) for it in items]
                test = {'natural': lambda c: c == 'nat', 'whole': lambda c: c in ('nat', 'zero'), 'integers': lambda c: c in ('nat', 'zero', 'neg'), 'rational': lambda c: c != 'irr', 'irrational': lambda c: c == 'irr'}[p['ask']]
                exp = [it for it, c in zip(items, cls) if test(c)]
                def parse_list(c):
                    inner = re.sub(r'^<span class="mth">', '', c); inner = re.sub(r'</span>$', '', inner)
                    if inner.strip() == '∅': return []
                    assert inner.startswith('{') and inner.endswith('}'), inner
                    return inner[1:-1].split(', ')
                got = [parse_list(c) for c in ch]
                if got[A] != exp: F(d, 'classset %s vs %s' % (got[A], exp))
                expv = sorted(str(sp.nsimplify(P(e))) for e in exp)
                if sum(1 for g in got if sorted(str(sp.nsimplify(P(e))) for e in g) == expv) != 1: F(d, 'distractor same set')
            elif t == 'prop':
                if p['s'] not in q: F(d, 's not in q')
                name = classify_prop(p['s'])
                if text(ch[A]) != name: F(d, 'property %s vs %s' % (text(ch[A]), name))
                if sum(1 for c in ch if text(c) == name) != 1: F(d, 'dup prop')
            elif t == 'temp':
                t1 = int(re.search(r'was (-?\d+)°F', qt).group(1)); r_ = int(re.search(r'risen (\d+) degrees', qt).group(1)); f_ = int(re.search(r'fallen (\d+) degrees', qt).group(1))
                rd = [t1, t1 + r_, t1 + r_ - f_]; exp = max(rd) - min(rd)
                got = [int(text(c)) for c in ch]
                if got[A] != exp or got.count(exp) != 1: F(d, 'temp')
            elif t == 'deg':
                if p['eh'] not in q: F(d, 'eh')
                exp = sp.Poly(P(p['eh']), x, y).total_degree()
                got = [int(text(c)) for c in ch]
                if got[A] != exp or got.count(exp) != 1: F(d, 'deg %s vs %s' % (got[A], exp))
            elif t == 'domain':
                if p['eh'] not in q: F(d, 'eh')
                tf = top_fraction(p['eh']); X = sp.Symbol('x')
                den = Pn(tf[1]).subs(x, X)
                exp = sorted(int(r) for r in sp.solve(den, X))
                got = [sorted(int(v.replace('−', '-')) for v in re.findall(r'x ≠ ([−-]?\d+)', text(c))) for c in ch]
                if got[A] != exp: F(d, 'domain %s vs %s' % (got[A], exp))
                if got.count(exp) != 1: F(d, 'dup domain')
            elif t in ('expr', 'expr2'):
                if t == 'expr':
                    if p['eh'] not in q: F(d, 'eh not in q')
                    tgt = P(p['eh'])
                else:
                    for part in p['parts']:
                        if part not in q: F(d, 'part not in q')
                    tgt = sp.sympify(p['tpl'].format(*['(' + to_src(pp) + ')' for pp in p['parts']]), locals=dict(NS))
                vals = [None if ('cannot' in text(c)) else P(c) for c in ch]
                if vals[A] is None or not eq(vals[A], tgt): F(d, 'answer not equal to target: %s' % text(ch[A]))
                for i, v in enumerate(vals):
                    if i != A and v is not None and eq(v, tgt): F(d, 'distractor equal to answer: %s' % text(ch[i]))
                for i in range(4):
                    for j in range(i + 1, 4):
                        if vals[i] is not None and vals[j] is not None and eq(vals[i], vals[j]): warns.append('%s L%d gen%d: two choices equal: %s | %s' % (d['id'], d['lv'], d['gi'], text(ch[i]), text(ch[j])))
                chk = p.get('chk')
                if chk == 'factor':
                    err = check_factor(ch[A], tgt)
                    if err: F(d, err)
                if chk == 'lowest':
                    err = check_lowest(ch[A])
                    if err: F(d, err)
                if chk == 'rad':
                    err = check_rad(ch[A])
                    if err: F(d, err + ' :: ' + text(ch[A]))
                if p.get('pos') and re.search(r'<sup>−', ch[A]): F(d, 'negative exponent in answer')
            elif t == 'path':
                w_, d_ = int(re.search(r'path (\d+) feet wide', qt).group(1)), (int(re.search(r'\(x \+ (\d+)\) feet long', qt).group(1)) if 'long' in qt else 0)
                tgt = sp.expand((x + 2 * w_) * (x + d_ + 2 * w_) - x * (x + d_))
                vals = [P(c) for c in ch]
                if not eq(vals[A], tgt): F(d, 'path')
                if sum(eq(v, tgt) for v in vals) != 1: F(d, 'path dup')
            elif t == 'cost':
                nums = [int(z.replace(',', '')) for z in re.findall(r'\$([\d,]+)\.00', qt)]
                F_, c_ = nums[0], nums[1]
                n1n2 = re.search(r'with (\d+) students than with (\d+) students', qt)
                n2_, n1_ = int(n1n2.group(1)), int(n1n2.group(2))
                exp = Fraction(F_ + c_ * n1_, n1_) - Fraction(F_ + c_ * n2_, n2_)
                got = [Fraction(text(c).replace('$', '').replace(',', '')) for c in ch]
                if got[A] != exp or got.count(exp) != 1: F(d, 'cost %s vs %s' % (got[A], exp))
            elif t == 'scale':
                k = int(re.search(r'is (\d+) times as heavy', qt).group(1)); e = sp.Rational(3, 4) if '3/4' in qt else sp.Rational(2, 3)
                exp = sp.nsimplify(sp.Integer(k) ** e)
                vals = [sp.nsimplify(P(c)) for c in ch]
                if vals[A] != exp or vals.count(exp) != 1: F(d, 'scale %s vs %s' % (vals[A], exp))
            elif t == 'diag':
                mo = re.search(r'measures (\d+) feet by (\d+) feet', qt); A_, B_ = int(mo.group(1)), int(mo.group(2))
                exp = sp.sqrt(A_ ** 2 + B_ ** 2)
                vals = [P(c) for c in ch]
                if not eq(vals[A], exp): F(d, 'diag')
                if sum(eq(v, exp) for v in vals) != 1: F(d, 'diag dup')
                err = check_rad(ch[A].replace(' ft', ''))
                if err: F(d, err)
            else:
                F(d, 'no verifier for type %s' % t)
        except Exception as ex:
            F(d, 'EXCEPTION %r' % ex)
    gens = sorted(counts)
    print('Chapter R verification: %d generators, %d questions checked (%d per generator)' % (len(gens), len(data), RUNS))
    for k in gens: pass
    from collections import Counter
    fc = Counter(f.split(':')[0] for f in fails)
    for f in fails[:40]: print('FAIL', f)
    for k, v in fc.items(): print('  failures in', k, v)
    wc = Counter(w.split(':')[0] for w in warns)
    for k, v in wc.items(): print('  note (two distractors equal) in', k, v)
    for w in warns[:12]: print('   ', w)
    print('failures:', len(fails))
    return 1 if fails else 0

if __name__ == '__main__':
    sys.exit(main())
