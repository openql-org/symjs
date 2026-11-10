# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
"""Regenerate sparse-series references with SymPy 1.14.0, never with symjs."""
import json
from pathlib import Path

import sympy as s
from sympy.polys import ring_series as rs
from sympy.polys.puiseux import puiseux_ring
from sympy.polys.rings import ring


def main():
    assert s.__version__ == '1.14.0'
    symbols = s.symbols('x y')

    def element(r, expr):
        e = s.sympify(expr, locals=dict(zip(('x', 'y'), symbols)))
        terms = {}
        for term in s.Add.make_args(s.expand(e)):
            powers = term.as_powers_dict()
            monom = tuple(s.Rational(powers.get(x, 0)) for x in symbols)
            coeff = term / s.prod(x**n for x, n in zip(symbols, monom))
            terms[monom] = r.domain.convert(coeff)
        return r.from_dict(terms)

    cases = []
    def record(kind, domain, operation, expr, precision, arg=None):
        r, x, _ = (ring if kind == 'polynomial' else puiseux_ring)('x y', getattr(s, domain))
        p = element(r, expr)
        f = getattr(rs, operation)
        result = f(p, x, precision) if arg is None else f(p, arg, x, precision)
        cases.append(dict(kind=kind, domain=domain, operation=operation, expr=expr,
                          precision=precision, arg=arg, expected=str(result)))

    for kind in ['polynomial', 'puiseux']:
        for name in ['exp', 'sin', 'cos', 'sinh', 'cosh', 'atan', 'atanh', 'asin', 'asinh', 'tan', 'tanh', 'LambertW']:
            record(kind, 'QQ', 'rs_' + name, 'x+x*y', 8)
        for precision in [1, 4]:
            record(kind, 'QQ', 'rs_exp', '0', precision)
        for expr in ['1+x', '1+x*y+x**2', '1+x**2']:
            record(kind, 'QQ', 'rs_log', expr, 8)
        for expr in ['1+x*y**2', 'x+x**2', 'x**2+x**3']:
            record(kind, 'QQ', 'rs_series_inversion', expr, 5)
        for n in [-3, 2, 3, 4]:
            record(kind, 'QQ', 'rs_nth_root', '1+x+x*y', 5, n)
        for n in [0, 1, 2, 3, 4, 7]:
            record(kind, 'QQ', 'rs_pow', 'x+x*y+x**2', 8, n)
        record(kind, 'QQ', 'rs_cot', 'x', 8)
        record(kind, 'RR', 'rs_nth_root', '3+x+x*y', 2, 3)
    for name in ['exp', 'sin', 'cos', 'atan', 'LambertW']:
        record('puiseux', 'QQ', 'rs_' + name, 'x**(2/5)+x**(2/3)+x*y**(7/5)', 3)
    record('puiseux', 'QQ', 'rs_log', '1+x**(3/2)', 5)
    record('puiseux', 'QQ', 'rs_series_inversion', 'x**(1/3)+x**(2/3)', 3)
    record('polynomial', 'EX', 'rs_exp', '1+x', 4)
    record('polynomial', 'EX', 'rs_sin', '1+x', 4)

    puiseux = []
    r, x, y = puiseux_ring('x y', s.QQ)
    for expr in ['0', '1', '5*x**(1/2)+7/y', '(x+y)**2', '(1+x)**3', 'x**(-2)', 'x**(-1/3)', 'x**(1/3)+x**(2/7)', '3*x**2-4*y**3']:
        p = element(r, expr)
        puiseux.append(dict(expr=expr, expected=str(p), asExpr=str(p.as_expr()), dx=str(p.diff(x)), dy=str(p.diff(y))))
    path = Path(__file__).resolve().parents[1] / 'packages/symjs/tests/polys/ringseries.references.json'
    x = symbols[0]
    fractional_root = str(s.series((8*x+x**2+x**3)**s.Rational(1,3), x, 0, 5).removeO())
    path.write_text(json.dumps(dict(sympy=s.__version__, series=cases, puiseux=puiseux, fractionalRoot=fractional_root), indent=2) + '\n')


if __name__ == '__main__':
    main()
