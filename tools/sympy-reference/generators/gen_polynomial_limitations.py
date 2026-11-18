"""Generate polynomial limitation regression fixtures with SymPy 1.14.0."""
import json
from pathlib import Path

import sympy as s
from sympy.polys import appellseqs

assert s.__version__ == '1.14.0'
destination = Path(__file__).resolve().parents[3] / 'packages/symjs/tests/polys'

rows = []
for name, domain in [('bernoulli', s.QQ), ('bernoulli_c', s.QQ),
                     ('genocchi', s.ZZ), ('euler', s.QQ), ('andre', s.ZZ)]:
    for n in range(21):
        coefficients = getattr(appellseqs, 'dup_' + name)(n, domain)
        rows.append(dict(kind=name, n=n, domain=str(domain), coeffs=list(map(str, coefficients))))
(destination / 'appellseqs.dense.references.json').write_text(json.dumps(rows, indent=2) + '\n')

x, y = s.symbols('x y')
rows = []
for dividend, divisor, gens, modulus in [
    ('2*x**3+3*x+1', '2*x+4', [x], 5),
    ('x**4+1', '2*x**2+1', [x], 5),
    ('x**2+1', 'x**4+1', [x], 5),
    ('0', 'x+1', [x], 5),
    ('(y+1)*x**3+y*x+1', 'y*x**2+2', [x, y], 5),
    ('x**4+y', 'x**2+y', [x, y], 7),
    ('x**3+1', '2*x+1', [x], 4),
]:
    f, g = (s.Poly(expression, *gens, modulus=modulus) for expression in (dividend, divisor))
    q, r = f.pdiv(g)
    row = dict(f=dividend, g=divisor, gens=list(map(str, gens)), modulus=modulus,
               q=str(q.as_expr()), r=str(r.as_expr()))
    try:
        row['resultant'] = str(f.resultant(g).as_expr())
    except ZeroDivisionError as error:
        row['resultantError'] = type(error).__name__ + ': ' + str(error)
    rows.append(row)
(destination / 'finite-pseudo.references.json').write_text(json.dumps(rows, indent=2) + '\n')
