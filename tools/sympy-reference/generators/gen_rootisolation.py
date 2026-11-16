"""Regenerate the references of complex root isolation (SymPy 1.14.0
polys/rootisolation.py) and of the complex roots of CRootOf (rootoftools.py):
isolating rectangles, root counts in rectangles, Poly.intervals with bounds and
all=True, ComplexInterval refinement, eval_rational sequences, evalf values
and the order of all_roots.

Polynomials are given as strings in x and results are compared by str().
"""
import json
from pathlib import Path

import sympy
from sympy import CRootOf, I, Poly, Rational, S, Symbol, sympify
from sympy.polys.domains import ZZ
from sympy.polys.rootisolation import dup_count_complex_roots, dup_isolate_complex_roots_sqf

assert sympy.__version__ == '1.14.0'

x = Symbol('x')


def coeffs(f):
    return [int(c) for c in Poly(sympify(f), x).all_coeffs()]


def rect(r):
    (ax, ay), (bx, by) = r.as_tuple() if hasattr(r, 'as_tuple') else r
    return [str(ax), str(ay), str(bx), str(by)]


def attempt(fn):
    try:
        return fn()
    except Exception as e:  # noqa: BLE001 - recorded for the tests
        return 'ERR:' + type(e).__name__ + ':' + str(e)


ISOLATE = [
    ('x**2 + 1', {}), ('x**3 + 10*x + 1', {}), ('x**4 + 1', {}), ('x**5 - x - 7', {}), ('x**6 + x + 1', {}),
    ('x**4 + 3*x**2 + 1', {}), ('x**7 - 3*x + 1', {}), ('x**2 + x + 1', {}), ('4*x**4 + 1', {}), ('x**5 + 1', {}),
    ('x**4 - 1', {}), ('x**2 - 2*x + 2', {}), ('x**4 + 4', {}), ('x**8 + 1', {}), ('x**3 - x', {}), ('x', {}),
    ('x**6 + x**2 + 1', {}), ('x**3 - 2', {}), ('3*x**3 - 7*x**2 + 5*x + 11', {}), ('x**4 + 4*x**2 - x + 6', {}),
    ('x**3 + 10*x + 1', {'eps': '1/10'}), ('x**4 + 4', {'eps': '1/100'}), ('x**5 - x - 7', {'eps': '1/1000'}),
    ('x**4 + 1', {'inf': '0'}), ('x**4 + 1', {'sup': '0'}), ('x**4 + 1', {'inf': '-1/2', 'sup': '1/2'}),
    ('x**6 + x + 1', {'inf': '-1/2', 'sup': '2'}), ('x**4 + 1', {'inf': '1', 'sup': '1'}), ('x**4 + 1', {'inf': '1', 'sup': '0'}),
]
isolate = []
for f, kw in ISOLATE:
    args = {k: Rational(v) for k, v in kw.items()}
    res = attempt(lambda: [rect(r) for r in dup_isolate_complex_roots_sqf(coeffs(f), ZZ, blackbox=True, **args)])
    isolate.append({'f': f, 'opts': kw, 'rects': res})

# root counts in rectangles with corners on a grid (roots on edges and corners included)
COUNT_POLYS = ['x**2 + 1', 'x**2', '(x**2 + 1)**2', 'x**4 - 1', 'x**4 + 4', 'x**3', 'x', 'x**3 - x', 'x**2 - 2*x + 2', 'x**5 + x**3 + 2*x**2 + 2', 'x**6 + x + 1', '2*x**2 + 2']
GRID = [Rational(v) for v in (-2, -1, 0, 1, 2)]
counts = []
for f in COUNT_POLYS:
    p = Poly(sympify(f), x)
    for u in GRID:
        for s in GRID:
            if s <= u:
                continue
            for v in GRID:
                for t in GRID:
                    if t <= v or (v == 0 and t == 0):
                        continue
                    if (u * 7 + s * 3 + v * 5 + t) % 3:
                        continue
                    counts.append([f, str(u), str(v), str(s), str(t), attempt(lambda: int(p.count_roots(u + I * v, s + I * t)))])
# a single bound, the other one from the root bound; real bounds with a complex one
for f, a, b in [('x**4 - 4', '0', '1 + 3*I'), ('x**4 + 4', None, '1 + I'), ('x**4 + 4', '-1/2 - I/2', None), ('x**3 + 10*x + 1', '-1', 'I'),
                ('x**2 + 1', '-I', '1'), ('x**6 + x + 1', None, '0 + I'), ('x**2 + 1', '-1/2 + I', '1/2 + 2*I')]:
    p = Poly(sympify(f), x)
    counts.append([f, a, b, attempt(lambda: int(p.count_roots(None if a is None else sympify(a), None if b is None else sympify(b))))])

# Poly.intervals with bounds, fast refinement and all=True
INTERVALS = [
    ('x**2 - 3', {'inf': '0'}), ('x**2 - 3', {'sup': '0'}), ('x**2 - 3', {'inf': '-1', 'sup': '2'}), ('x**2 - 3', {'inf': '3', 'sup': '4'}),
    ('x**3 - x', {'inf': '0', 'sup': '1'}), ('(x - 1/4)*(x - 1/3)*(x - 1)', {}), ('x**3 - x', {'inf': '1/2'}), ('x*(x - 1)', {'inf': '1/2'}), ('(x - 100)*(x - 200)*(x**2 - 2)', {'fast': True}),
    ('(x - 1000)*(x - 2000)*(x**2 - 3)', {'fast': True, 'eps': '1/100'}), ('(x**2 - 2)*(x**2 - 3)', {'inf': '-3/2', 'sup': '3/2'}),
    ('(x**2 - 2)*(x - 7)**2', {'inf': '-1', 'sup': '7'}), ('x**5 - 5*x**3 + 4*x + 1', {'inf': '-1', 'sup': '1', 'eps': '1/10'}),
    ('x**3 + 10*x + 1', {'all': True}), ('x**4 + 1', {'all': True}), ('x**4 - 1', {'all': True, 'eps': '1/10'}),
    ('2*x**3 - 2*x + 2', {'all': True}), ('(x**2 + 1)**2', {'all': True}), ('x**5 - x - 7', {'all': True, 'inf': '0', 'sup': '2'}),
    ('(x**2 + 1)*(x - 1)**2', {'all': True}), ('x**2 - 3', {'eps': '-1'}),
]
intervals = []
for f, kw in INTERVALS:
    args = {k: (v if k in ('all', 'fast') else Rational(v)) for k, v in kw.items()}
    res = attempt(lambda: Poly(sympify(f), x).intervals(**args))
    intervals.append({'f': f, 'opts': kw, 'result': res if isinstance(res, str) else str(res)})

# ComplexInterval refinement
ci = []
for f in ['x**3 + 10*x + 1', 'x**6 + x + 1', 'x**4 + 4']:
    rs = dup_isolate_complex_roots_sqf(coeffs(f), ZZ, blackbox=True)
    r = rs[-1]
    u, v = rs[-1].refine_disjoint(rs[-3] if len(rs) > 2 else rs[0])
    ci.append({
        'f': f, 'all': [repr(z) for z in rs], 'step3': repr(r.refine_step(3)), 'step0': repr(r.refine_step(0)), 'refine': repr(r.refine()),
        'size': repr(r.refine_size(Rational(1, 10))), 'size2': repr(r.refine_size(Rational(1, 10), Rational(1, 1000))),
        'center': [str(c) for c in r.center], 'dx': str(r.dx), 'dy': str(r.dy), 'conj': [z.conj for z in rs],
        'disjoint': [rs[i].is_disjoint(rs[j]) for i in range(len(rs)) for j in range(len(rs))],
        'refine_disjoint': [repr(u), repr(v)], 'conjugate': repr(r.conjugate()),
    })

# eval_rational sequences from a cleared cache; the refined rectangle is kept between the calls
SEQ = [
    ('x**3 + 10*x + 1', 1, [['1/10'], ['1/10', '1/10000'], ['1/10000', '1/10000'], [None, None, 2]]),
    ('x**3 + 10*x + 1', 2, [[None, None, 5], ['1/10']]),
    ('x**2 + 1', 0, [[None, None, 15], ['1/1000']]),
    ('x**2 + 1', 1, [['1/1000', '1/100'], [None, None, 3]]),
    ('x**4 + 3*x**2 + 1', 2, [[None, None, 4]]),
    ('x**6 + x**2 + 1', 0, [[None, None, 6]]), ('x**6 + x**2 + 1', 3, [['1/100']]), ('x**6 + x**2 + 1', 5, [['1/100', '1/10']]),
    ('x**6 + x + 1', 3, [['1/1000'], [None, None, 10]]), ('x**7 - 3*x + 1', 5, [[None, None, 8]]),
    ('x**5 - x - 7', 4, [['0.001'], ['1e-8']]), ('3*x**3 - 7*x**2 + 5*x + 11', 2, [[None, None, 5]]),
]
evalrational = []
for f, i, calls in SEQ:
    CRootOf.clear_cache()
    r = CRootOf(sympify(f), i)
    out = []
    for c in calls:
        dx, dy = (c + [None, None])[:2]
        n = c[2] if len(c) > 2 else 15
        conv = lambda v: None if v is None else (float(v) if '.' in v or 'e' in v else Rational(v))
        out.append(str(r.eval_rational(conv(dx), conv(dy), n)))
    evalrational.append({'f': f, 'i': i, 'calls': calls, 'results': out})

# evalf of every root and the order of all_roots
EVALF = ['x**3 + 10*x + 1', 'x**5 - x - 7', 'x**6 + x + 1', 'x**4 + 3*x**2 + 1', 'x**7 - 3*x + 1', 'x**6 + x**2 + 1', '3*x**3 - 7*x**2 + 5*x + 11']
evalf = []
for f in EVALF:
    CRootOf.clear_cache()
    evalf.append({'f': f, 'values': [str(CRootOf(sympify(f), i).evalf(15)) for i in range(Poly(sympify(f), x).degree())],
                  'imaginary': [bool(CRootOf(sympify(f), i).is_imaginary) for i in range(Poly(sympify(f), x).degree())]})
ALLROOTS = ['(x**2 + 1)*(x**2 + x + 1)', '(x**2 + x + 1)*(x**2 + 4)*(x**2 - 2*x + 5)', '(x**4 + 1)*(x**2 + 2)', '(x**3 - 2)*(x**2 + 3)',
            '(x**3 + x + 1)*(x**3 + x + 3)', '(x**2 + 2)*(x**2 + 3)', '(x**3 + 2)**2*(x**2 + 1)', '(x**3 + 10*x + 1)*(x**2 + 1)**2',
            '(2*x**2 + 3)*(x**2 - x + 1)*(x - 2)', '(x**5 - x - 7)*(x**3 + 10*x + 1)']
allroots = []
for f in ALLROOTS:
    CRootOf.clear_cache()
    p = Poly(sympify(f), x)
    allroots.append({'f': f, 'radicals': [str(r) for r in p.all_roots()], 'crootof': [str(r) for r in p.all_roots(radicals=False)],
                     'real': [str(r) for r in p.real_roots(radicals=False)]})

out = {'isolate': isolate, 'counts': counts, 'intervals': intervals, 'complex_intervals': ci, 'eval_rational': evalrational, 'evalf': evalf, 'all_roots': allroots}
path = Path(__file__).resolve().parents[3] / 'packages/symjs/tests/polys/rootisolation.references.json'
path.write_text(json.dumps(out, indent=1) + '\n')
