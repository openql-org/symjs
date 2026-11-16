"""Regenerate the references of sympy.polys.groebnertools (F5B, lcm/gcd by Groebner bases) with SymPy 1.14.0."""
import json
from pathlib import Path

import sympy
from sympy.polys import ring, QQ, ZZ, lex, grlex, grevlex
from sympy.polys.groebnertools import (_f5b, _buchberger, groebner_lcm, groebner_gcd, is_groebner, is_minimal, is_reduced,
                                       red_groebner, spoly, lbp, sig, f5_reduce, critical_pair, s_poly, cp_key, lbp_key)

assert sympy.__version__ == '1.14.0'
out = {'systems': [], 'lcm': []}
for order in ('lex', 'grlex', 'grevlex'):
    O = {'lex': lex, 'grlex': grlex, 'grevlex': grevlex}[order]
    R, x, y, z = ring('x,y,z', QQ, O)
    systems = [
        [x**2 + y - 1, x*y - 1],
        [x**2 + y**2 + z**2 - 1, x**2 - y + z**2, x - z],
        [x*y*z - 1, x**2 - y, y**2 - z],
        [x**3 - 2*x*y, x**2*y - 2*y**2 + x],
        [x + y + z, x*y + y*z + z*x, x*y*z - 1],
        [2*x, 3*x],
    ]
    for F in systems:
        G = _f5b(F, R)
        out['systems'].append({'order': order, 'F': [str(f) for f in F], 'f5b': [str(g) for g in G],
                               'buchberger': [str(g) for g in _buchberger(F, R)],
                               'is_groebner': [is_groebner(G, R), is_groebner(F, R)], 'is_minimal': [is_minimal(list(G), R), is_minimal(list(F), R)],
                               'is_reduced': [is_reduced(list(G), R), is_reduced(list(F), R)],
                               'red': [str(g) for g in red_groebner(list(G) + [g * 2 for g in G[:1]], R)] if G else [],
                               'spoly': str(spoly(F[0], F[1], R))})
    f = lbp(sig((1, 1, 1), 4), x, 3)
    g = lbp(sig((0, 0, 0), 2), x, 2)
    h = lbp(sig((0, 1, 0), 3), x*y + z, 5)
    k = lbp(sig((0, 0, 1), 3), y**2 - x, 6)
    cp = critical_pair(h, k, R)
    out.setdefault('labeled', []).append({'order': order, 'f5_reduce': str(f5_reduce(f, [g])),
                                          'f5_reduce2': str(f5_reduce(lbp(sig((2, 0, 0), 1), x**2*y + z, 7), [h, k])),
                                          'cp': str(cp), 's_poly': str(s_poly(cp)), 'cp_key': str(cp_key(cp, R)), 'lbp_key': str(lbp_key(h))})
R, x, y = ring('x,y', ZZ, lex)
for f, g in [(x**2 - y**2, x - y), (x**2*y**2, x*y**2), (4*x**2*y - 4*y, 6*x*y + 6*y), (x, ZZ(0) + R.zero), (2*x, 3*x), (x**3 - 1, x**2 - 1)]:
    out['lcm'].append({'domain': 'ZZ', 'f': str(f), 'g': str(g), 'lcm': str(groebner_lcm(f, g)), 'gcd': str(groebner_gcd(f, g)) if f and g else None})
R, x, y = ring('x,y', QQ, lex)
for f, g in [(x**2 - y**2, x - y), (x**2 + 2*x*y + y**2, x**2 - y**2), (QQ(1, 2)*x**2, QQ(1, 3)*x*y)]:
    out['lcm'].append({'domain': 'QQ', 'f': str(f), 'g': str(g), 'lcm': str(groebner_lcm(f, g)), 'gcd': str(groebner_gcd(f, g))})
path = Path(__file__).resolve().parents[3] / 'packages/symjs/tests/polys/groebnertools.references.json'
path.write_text(json.dumps(out, indent=1) + '\n')
