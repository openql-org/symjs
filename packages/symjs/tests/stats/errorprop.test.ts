// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/errorprop.ts (SymPy sympy/stats/error_prop.py and
// sympy/stats/tests/test_error_prop.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { SymFunction, Sym, add, exp, mul, pow, str } from '../../src';
import type { Expr } from '../../src';
import { Normal, RandomSymbol, varianceProp } from '../../src/stats';

const [x, y, z, phi, t] = ['x', 'y', 'z', 'phi', 't'].map((n) => new Sym(n)) as [Sym, Sym, Sym, Sym, Sym];
const consts = [phi, t];
const a = new RandomSymbol(x);
const f = SymFunction('f')(x);

const cases: [Expr, string, string][] = [
  [add(x, y), 'Variance(x) + Variance(y)', '2*Covariance(x, y) + Variance(x) + Variance(y)'],
  [add(a, y), 'Variance(x) + Variance(y)', '2*Covariance(x, y) + Variance(x) + Variance(y)'],
  [add(x, y, z), 'Variance(x) + Variance(y) + Variance(z)', '2*Covariance(x, y) + 2*Covariance(x, z) + 2*Covariance(y, z) + Variance(x) + Variance(y) + Variance(z)'],
  [mul(2, x), '4*Variance(x)', '4*Variance(x)'],
  [mul(x, y), 'x**2*Variance(y) + y**2*Variance(x)', 'x**2*Variance(y) + y**2*Variance(x) + 2*Covariance(x, y)/(x*y)'],
  [pow(x, -1), 'Variance(x)/x**4', 'Variance(x)/x**4'],
  [mul(x, pow(y, -1)), '(x**2*Variance(y) + y**2*Variance(x))/y**4', '(x**2*Variance(y) + y**2*Variance(x))/y**4'],
  [exp(x), 'exp(2*x)*Variance(x)', 'exp(2*x)*Variance(x)'],
  [exp(mul(2, x)), '4*exp(4*x)*Variance(x)', '4*exp(4*x)*Variance(x)'],
  [exp(mul(-1, x, t)), 't**2*exp(-2*t*x)*Variance(x)', 't**2*exp(-2*t*x)*Variance(x)'],
  [f, 'Variance(f(x))', 'Variance(f(x))'],
  [add(x, phi), 'Variance(x)', 'Variance(x)'],
];

describe('variance propagation (SymPy test_variance_prop, test_variance_prop_with_covar)', () => {
  it('without covariances', () => {
    for (const [e, out] of cases) expect(str(varianceProp(e, { consts }))).toBe(out);
  });
  it('with covariances', () => {
    for (const [e, , out] of cases) expect(str(varianceProp(e, { consts, includeCovar: true }))).toBe(out);
  });
  it('of random symbols with a space and of numbers', () => {
    const N = Normal('N', 0, 2);
    expect(str(varianceProp(mul(N, x)))).toBe('x**2*Variance(N) + N**2*Variance(x)');
    // SymPy: Variance(N).doit() stays Variance(N)
    expect(str(varianceProp(N))).toBe('Variance(N)');
    expect(str(varianceProp(add(x, 3)))).toBe('Variance(x)');
  });
});
