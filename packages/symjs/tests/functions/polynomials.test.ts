// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/polynomials.ts.
//
// The orthogonal polynomials: evaluation rules, derivatives, conjugates, rewrites, printing and
// numerics. Expected values are str() results of SymPy 1.14 (mpmath 1.3 values for the numerics).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const locals = {
  p: new sj.Sym('p', { positive: true }),
  k: new sj.Sym('k', { integer: true, negative: true }),
  q: new sj.Sym('q', { integer: true, positive: true }),
  ng: new sj.Sym('ng', { negative: true }),
  jacobi_normalized: sj.jacobiNormalized,
  chebyshevt_root: sj.chebyshevtRoot,
  chebyshevu_root: sj.chebyshevuRoot,
};
/** str() of the evaluated SymPy source, or ERR and the error class name. */
function run(src: string): string {
  try {
    return String(sj.parse(src, { locals }));
  } catch (e) {
    return `ERR ${e instanceof sj.NotImplementedError ? 'NotImplementedError' : e instanceof RangeError ? 'ValueError' : e instanceof TypeError ? 'TypeError' : String(e)}`;
  }
}

// [SymPy source, str() of the SymPy 1.14 result (ERR ValueError: SymPy raises ValueError, a RangeError here;
// ERR TypeError: SymPy raises TypeError, so does symjs)]
const CASES: [string, string][] = [
  ["jacobi(0, a, b, x)", "1"],
  ["jacobi(1, a, b, x)", "a/2 - b/2 + x*(a/2 + b/2 + 1)"],
  ["jacobi(3, 1, 2, x)", "21*x**3/2 - 7*x**2/2 - 7*x/2 + 1/2"],
  ["jacobi(2, 1/2, 3/2, x)", "15*x**2/4 - 5*x/4 - 5/8"],
  ["jacobi(n, a, a, x)", "RisingFactorial(a + 1, n)*gegenbauer(n, a + 1/2, x)/RisingFactorial(2*a + 1, n)"],
  ["jacobi(n, 0, 0, x)", "legendre(n, x)"],
  ["jacobi(n, 1/2, 1/2, x)", "RisingFactorial(3/2, n)*chebyshevu(n, x)/factorial(n + 1)"],
  ["jacobi(n, -1/2, -1/2, x)", "RisingFactorial(1/2, n)*chebyshevt(n, x)/factorial(n)"],
  ["jacobi(2, a, a, x)", "(a + 1)*(a + 2)*(-a + x**2*(2*a**2 + 4*a + 3/2) - 1/2)/((2*a + 1)*(2*a + 2))"],
  ["jacobi(n, a, -a, x)", "(-1)**a*(x + 1)**(a/2)*assoc_legendre(n, a, x)*factorial(-a + n)*gamma(a + n + 1)/((1 - x)**(a/2)*factorial(a + n)*gamma(n + 1))"],
  ["jacobi(n, a, b, -x)", "(-1)**n*jacobi(n, b, a, x)"],
  ["jacobi(n, a, b, 0)", "gamma(a + n + 1)*hyper((-n, -b - n), (a + 1,), -1)/(2**n*factorial(n)*gamma(a + 1))"],
  ["jacobi(n, a, b, 1)", "RisingFactorial(a + 1, n)/factorial(n)"],
  ["jacobi(p, a, b, oo)", "oo*RisingFactorial(a + b + p + 1, p)"],
  ["jacobi(n, a, b, oo)", "jacobi(n, a, b, oo)"],
  ["jacobi(p, 1/3, 1/5, oo)", "oo*RisingFactorial(p + 23/15, p)"],
  ["jacobi(p, 1, 2, oo)", "oo*RisingFactorial(p + 4, p)"],
  ["jacobi(q, 1, 2, oo)", "ERR ValueError"],
  ["jacobi(-1, a, b, x)", "ERR ValueError"],
  ["diff(jacobi(n, a, b, x), x)", "(a/2 + b/2 + n/2 + 1/2)*jacobi(n - 1, a + 1, b + 1, x)"],
  ["diff(jacobi(n, a, b, x), a)", "Sum((jacobi(n, a, b, x) + (2*_k + a + b + 1)*RisingFactorial(_k + b + 1, -_k + n)*jacobi(_k, a, b, x)/((-_k + n)*RisingFactorial(_k + a + b + 1, -_k + n)))/(_k + a + b + n + 1), (_k, 0, n - 1))"],
  ["diff(jacobi(n, a, b, x), b)", "Sum(((-1)**(-_k + n)*(2*_k + a + b + 1)*RisingFactorial(_k + a + 1, -_k + n)*jacobi(_k, a, b, x)/((-_k + n)*RisingFactorial(_k + a + b + 1, -_k + n)) + jacobi(n, a, b, x))/(_k + a + b + n + 1), (_k, 0, n - 1))"],
  ["diff(jacobi(n, a, b, x), n)", "Derivative(jacobi(n, a, b, x), n)"],
  ["conjugate(jacobi(n, a, b, x))", "jacobi(n, conjugate(a), conjugate(b), conjugate(x))"],
  ["jacobi_normalized(n, a, b, x)", "jacobi(n, a, b, x)/sqrt(2**(a + b + 1)*gamma(a + n + 1)*gamma(b + n + 1)/((a + b + 2*n + 1)*factorial(n)*gamma(a + b + n + 1)))"],
  ["jacobi_normalized(1, 0, 0, x)", "sqrt(6)*x/2"],
  ["gegenbauer(0, a, x)", "1"],
  ["gegenbauer(3, a, x)", "x**3*(4*a**3/3 + 4*a**2 + 8*a/3) + x*(-2*a**2 - 2*a)"],
  ["gegenbauer(2, 2, x)", "12*x**2 - 2"],
  ["gegenbauer(n, 1/2, x)", "legendre(n, x)"],
  ["gegenbauer(n, 1, x)", "chebyshevu(n, x)"],
  ["gegenbauer(n, -1, x)", "0"],
  ["gegenbauer(-2, a, x)", "0"],
  ["gegenbauer(k, a, x)", "0"],
  ["gegenbauer(n, a, -1)", "cos(pi*(a + n))*gamma(2*a + n)*sec(pi*a)/(gamma(2*a)*gamma(n + 1))"],
  ["gegenbauer(n, 2, -1)", "zoo"],
  ["gegenbauer(n, a, -x)", "(-1)**n*gegenbauer(n, a, x)"],
  ["gegenbauer(n, a, 0)", "2**n*sqrt(pi)*gamma(a + n/2)/(gamma(a)*gamma(1/2 - n/2)*gamma(n + 1))"],
  ["gegenbauer(n, a, 1)", "gamma(2*a + n)/(gamma(2*a)*gamma(n + 1))"],
  ["gegenbauer(p, a, oo)", "oo*RisingFactorial(a, p)"],
  ["gegenbauer(n, a, oo)", "gegenbauer(n, a, oo)"],
  ["gegenbauer(n, a, x)", "gegenbauer(n, a, x)"],
  ["diff(gegenbauer(n, a, x), x)", "2*a*gegenbauer(n - 1, a + 1, x)"],
  ["diff(gegenbauer(n, a, x), a)", "Sum((2*(-1)**(-_k + n) + 2)*(_k + a)*gegenbauer(_k, a, x)/((-_k + n)*(_k + 2*a + n)) + ((2*_k + 2)/((_k + 2*a)*(2*_k + 2*a + 1)) + 2/(_k + 2*a + n))*gegenbauer(n, a, x), (_k, 0, n - 1))"],
  ["diff(gegenbauer(n, a, x), n)", "Derivative(gegenbauer(n, a, x), n)"],
  ["conjugate(gegenbauer(n, a, x))", "gegenbauer(n, conjugate(a), conjugate(x))"],
  ["chebyshevt(0, x)", "1"],
  ["chebyshevt(5, x)", "16*x**5 - 20*x**3 + 5*x"],
  ["chebyshevt(-3, x)", "4*x**3 - 3*x"],
  ["chebyshevt(1/2, x)", "chebyshevt(1/2, x)"],
  ["chebyshevt(n, -x)", "(-1)**n*chebyshevt(n, x)"],
  ["chebyshevt(-n, x)", "chebyshevt(n, x)"],
  ["chebyshevt(n, 0)", "cos(pi*n/2)"],
  ["chebyshevt(n, 1)", "1"],
  ["chebyshevt(n, oo)", "oo"],
  ["chebyshevt(n, x)", "chebyshevt(n, x)"],
  ["diff(chebyshevt(n, x), x)", "n*chebyshevu(n - 1, x)"],
  ["diff(chebyshevt(n, x), n)", "Derivative(chebyshevt(n, x), n)"],
  ["conjugate(chebyshevt(n, x))", "chebyshevt(n, conjugate(x))"],
  ["chebyshevu(0, x)", "1"],
  ["chebyshevu(4, x)", "16*x**4 - 12*x**2 + 1"],
  ["chebyshevu(-1, x)", "0"],
  ["chebyshevu(-4, x)", "1 - 4*x**2"],
  ["chebyshevu(n, -x)", "(-1)**n*chebyshevu(n, x)"],
  ["chebyshevu(-n, x)", "-chebyshevu(n - 2, x)"],
  ["chebyshevu(-n + 1, x)", "-chebyshevu(n - 3, x)"],
  ["chebyshevu(-n - 1, x)", "-chebyshevu(n - 1, x)"],
  ["chebyshevu(-2*n + y, x)", "chebyshevu(-2*n + y, x)"],
  // SymPy raises TypeError (-None from _eval_at_order)
  ["chebyshevu(-1/2, x)", "ERR TypeError"],
  ["chebyshevu(n, 0)", "cos(pi*n/2)"],
  ["chebyshevu(n, 1)", "n + 1"],
  ["chebyshevu(n, oo)", "oo"],
  ["chebyshevu(n, x)", "chebyshevu(n, x)"],
  ["diff(chebyshevu(n, x), x)", "(-x*chebyshevu(n, x) + (n + 1)*chebyshevt(n + 1, x))/(x**2 - 1)"],
  ["legendre(0, x)", "1"],
  ["legendre(4, x)", "35*x**4/8 - 15*x**2/4 + 3/8"],
  ["legendre(-3, x)", "3*x**2/2 - 1/2"],
  ["legendre(n, -x)", "(-1)**n*legendre(n, x)"],
  ["legendre(-n, x)", "legendre(n - 1, x)"],
  ["legendre(-n - 1, x)", "legendre(n, x)"],
  ["legendre(n, 0)", "sqrt(pi)/(gamma(1/2 - n/2)*gamma(n/2 + 1))"],
  ["legendre(n, 1)", "1"],
  ["legendre(n, oo)", "oo"],
  ["legendre(n, x)", "legendre(n, x)"],
  ["diff(legendre(n, x), x)", "n*(x*legendre(n, x) - legendre(n - 1, x))/(x**2 - 1)"],
  ["assoc_legendre(0, 0, x)", "1"],
  ["assoc_legendre(2, 1, x)", "-3*x*sqrt(1 - x**2)"],
  ["assoc_legendre(3, 2, x)", "15*x*(1 - x**2)"],
  ["assoc_legendre(2, -1, x)", "x*sqrt(1 - x**2)/2"],
  ["assoc_legendre(n, -m, x)", "(-1)**m*assoc_legendre(n, m, x)*factorial(-m + n)/factorial(m + n)"],
  ["assoc_legendre(n, 0, x)", "legendre(n, x)"],
  ["assoc_legendre(n, m, 0)", "2**m*sqrt(pi)/(gamma(-m/2 - n/2 + 1/2)*gamma(-m/2 + n/2 + 1))"],
  ["assoc_legendre(n, m, x)", "assoc_legendre(n, m, x)"],
  ["assoc_legendre(-1, 0, x)", "1"],
  ["assoc_legendre(1, 2, x)", "ERR ValueError"],
  ["assoc_legendre(-1, 1, x)", "ERR ValueError"],
  ["assoc_legendre(1/2, 1, x)", "assoc_legendre(1/2, 1, x)"],
  ["diff(assoc_legendre(n, m, x), x)", "(n*x*assoc_legendre(n, m, x) - (m + n)*assoc_legendre(n - 1, m, x))/(x**2 - 1)"],
  ["diff(assoc_legendre(n, m, x), m)", "Derivative(assoc_legendre(n, m, x), m)"],
  ["conjugate(assoc_legendre(n, m, x))", "assoc_legendre(n, conjugate(m), conjugate(x))"],
  ["hermite(0, x)", "1"],
  ["hermite(4, x)", "16*x**4 - 48*x**2 + 12"],
  ["hermite(-1, x)", "ERR ValueError"],
  ["hermite(n, -x)", "(-1)**n*hermite(n, x)"],
  ["hermite(n, 0)", "2**n*sqrt(pi)/gamma(1/2 - n/2)"],
  ["hermite(n, oo)", "oo"],
  ["hermite(n, x)", "hermite(n, x)"],
  ["diff(hermite(n, x), x)", "2*n*hermite(n - 1, x)"],
  ["conjugate(hermite(n, x))", "hermite(n, conjugate(x))"],
  ["hermite_prob(0, x)", "1"],
  ["hermite_prob(4, x)", "x**4 - 6*x**2 + 3"],
  ["hermite_prob(-1, x)", "hermite_prob(-1, x)"],
  ["hermite_prob(n, -x)", "(-1)**n*hermite_prob(n, x)"],
  ["hermite_prob(n, 0)", "sqrt(pi)/gamma(1/2 - n/2)"],
  ["hermite_prob(n, oo)", "oo"],
  ["diff(hermite_prob(n, x), x)", "n*hermite_prob(n - 1, x)"],
  ["diff(hermite_prob(n, x), n)", "Derivative(hermite_prob(n, x), n)"],
  ["laguerre(0, x)", "1"],
  ["laguerre(3, x)", "-x**3/6 + 3*x**2/2 - 3*x + 1"],
  ["laguerre(-3, x)", "(x**2/2 + 2*x + 1)*exp(x)"],
  ["laguerre(-n, x)", "exp(x)*laguerre(n - 1, -x)"],
  ["laguerre(-n + 2, x)", "exp(x)*laguerre(n - 3, -x)"],
  ["laguerre(n, 0)", "1"],
  ["laguerre(n, -oo)", "oo"],
  ["laguerre(n, oo)", "oo*(-1)**n"],
  ["laguerre(n, x)", "laguerre(n, x)"],
  ["laguerre(1/2, x)", "ERR ValueError"],
  ["diff(laguerre(n, x), x)", "-assoc_laguerre(n - 1, 1, x)"],
  ["assoc_laguerre(0, a, x)", "1"],
  ["assoc_laguerre(2, a, x)", "a**2/2 + 3*a/2 + x**2/2 + x*(-a - 2) + 1"],
  ["assoc_laguerre(2, 1/2, x)", "x**2/2 - 5*x/2 + 15/8"],
  ["assoc_laguerre(n, 0, x)", "laguerre(n, x)"],
  ["assoc_laguerre(n, a, 0)", "binomial(a + n, a)"],
  ["assoc_laguerre(p, a, oo)", "oo*(-1)**p"],
  ["assoc_laguerre(p, a, -oo)", "oo"],
  // SymPy raises TypeError (the bool of n > 0; SymPy 1.14's cache reports it as an AttributeError)
  ["assoc_laguerre(n, a, oo)", "ERR TypeError"],
  ["assoc_laguerre(n, a, x)", "assoc_laguerre(n, a, x)"],
  ["assoc_laguerre(-1, a, x)", "ERR ValueError"],
  ["diff(assoc_laguerre(n, a, x), x)", "-assoc_laguerre(n - 1, a + 1, x)"],
  ["diff(assoc_laguerre(n, a, x), a)", "Sum(assoc_laguerre(_k, a, x)/(-a + n), (_k, 0, n - 1))"],
  ["diff(assoc_laguerre(n, a, x), n)", "Derivative(assoc_laguerre(n, a, x), n)"],
  ["conjugate(assoc_laguerre(n, a, x))", "assoc_laguerre(n, conjugate(a), conjugate(x))"],
  ["chebyshevt_root(3, 2)", "-sqrt(3)/2"],
  ["chebyshevt_root(4, 0)", "sqrt(sqrt(2)/4 + 1/2)"],
  ["chebyshevu_root(3, 2)", "-sqrt(2)/2"],
  ["chebyshevu_root(5, 1)", "1/2"],
  ["chebyshevt_root(3, 3)", "ERR ValueError"],
  ["chebyshevu_root(2, -1)", "ERR ValueError"],
  ["chebyshevt(3, chebyshevt_root(3, 2))", "0"],  // non-integer and Float degrees: jacobi, gegenbauer and assoc_laguerre truncate with int(n) like SymPy
  ["jacobi(5/2, a, b, x)", "a**2/8 - a*b/4 - a/8 + b**2/8 - b/8 + x**2*(a**2/8 + a*b/4 + 7*a/8 + b**2/8 + 7*b/8 + 3/2) + x*(a**2/4 + 3*a/4 - b**2/4 - 3*b/4) - 1/2"],
  ["jacobi(-1/2, a, b, x)", "ERR ValueError"],
  ["jacobi(-5/2, a, b, x)", "ERR ValueError"],
  ["jacobi(1/2, a, b, x)", "1"],
  ["jacobi(5/2, 1, 2, x)", "21*x**2/4 - 3*x/2 - 3/4"],
  ["jacobi(2.7, 1, 2, x)", "21*x**2/4 - 3*x/2 - 3/4"],
  ["jacobi(-2.5, a, b, x)", "ERR ValueError"],
  ["gegenbauer(5/2, a, x)", "-a + x**2*(2*a**2 + 2*a)"],
  ["gegenbauer(-1/2, a, x)", "0"],
  ["gegenbauer(-5/2, a, x)", "0"],
  ["gegenbauer(1/2, a, x)", "1"],
  ["gegenbauer(7/3, 2, x)", "12*x**2 - 2"],
  ["gegenbauer(2.5, a, x)", "-a + x**2*(2*a**2 + 2*a)"],
  ["gegenbauer(ng, a, x)", "0"],
  ["assoc_laguerre(5/2, a, x)", "a**2/2 + 3*a/2 + x**2/2 + x*(-a - 2) + 1"],
  ["assoc_laguerre(1/2, a, x)", "1"],
  ["assoc_laguerre(-1/2, a, x)", "ERR ValueError"],
  ["assoc_laguerre(-5/2, a, x)", "ERR ValueError"],
  ["assoc_laguerre(1.5, 2, x)", "3 - x"],
  ["assoc_laguerre(n, a, -oo)", "ERR TypeError"],
  ["assoc_laguerre(n + 1, a, oo)", "ERR TypeError"],
  ["assoc_laguerre(ng, a, oo)", "assoc_laguerre(ng, a, oo)"],
  ["assoc_laguerre(ng, a, -oo)", "assoc_laguerre(ng, a, -oo)"],
  ["chebyshevu(-5/2, x)", "ERR TypeError"],
  ["chebyshevu(-3/2, x)", "ERR TypeError"],
  ["chebyshevu(-1.0, x)", "ERR TypeError"],
  ["chebyshevu(-2.0, x)", "-1"],
  ["chebyshevu(5/2, x)", "chebyshevu(5/2, x)"],
  ["chebyshevt(-5/2, x)", "chebyshevt(-5/2, x)"],
  ["legendre(-5/2, x)", "legendre(-5/2, x)"],
  ["laguerre(2.0, x)", "laguerre(2.0, x)"],
  ["laguerre(-2.0, x)", "exp(x)*laguerre(1.0, -x)"],
  ["laguerre(2.5, x)", "ERR ValueError"],
  ["laguerre(0.0, x)", "1"],
  ["hermite(-2.0, x)", "ERR ValueError"],
  ["hermite(-5/2, x)", "ERR ValueError"],
  ["hermite_prob(-5/2, x)", "hermite_prob(-5/2, x)"],
  ["diff(legendre(x**2, x), x)", "x**2*(x*legendre(x**2, x) - legendre(x**2 - 1, x))/(x**2 - 1) + 2*x*Subs(Derivative(legendre(_xi_1, x), _xi_1), _xi_1, x**2)"],
  ["diff(legendre(x, x), x)", "x*(x*legendre(x, x) - legendre(x - 1, x))/(x**2 - 1) + Subs(Derivative(legendre(_xi_1, x), _xi_1), _xi_1, x)"],
  ["diff(jacobi(x**2, a, b, x), x)", "2*x*Subs(Derivative(jacobi(_xi_1, a, b, x), _xi_1), _xi_1, x**2) + (a/2 + b/2 + x**2/2 + 1/2)*jacobi(x**2 - 1, a + 1, b + 1, x)"],
  ["diff(assoc_legendre(n, x**2, x), x)", "2*x*Subs(Derivative(assoc_legendre(n, _xi_2, x), _xi_2), _xi_2, x**2) + (n*x*assoc_legendre(n, x**2, x) - (n + x**2)*assoc_legendre(n - 1, x**2, x))/(x**2 - 1)"],
  ["diff(chebyshevt(x**2, y), x)", "2*x*Subs(Derivative(chebyshevt(_xi_1, y), _xi_1), _xi_1, x**2)"],
  ["diff(assoc_laguerre(x**2, a, x), x)", "2*x*Subs(Derivative(assoc_laguerre(_xi_1, a, x), _xi_1), _xi_1, x**2) - assoc_laguerre(x**2 - 1, a + 1, x)"],
  ["diff(gegenbauer(x**2, a, y), x)", "2*x*Subs(Derivative(gegenbauer(_xi_1, a, y), _xi_1), _xi_1, x**2)"],

];

describe('orthogonal polynomials (SymPy table)', () => {
  for (const [src, expected] of CASES) it(src, () => expect(run(src)).toBe(expected));
});

const [n, a, b, x, m] = sj.symbols('n a b x m');
const P = (src: string): sj.Expr => sj.parse(src, { locals });

describe('rewrites as sums (SymPy _eval_rewrite_as_Sum)', () => {
  const R: [string, string][] = [
    ['jacobi(n, a, b, x)', 'Sum((1/2 - x/2)**_k*RisingFactorial(-n, _k)*RisingFactorial(_k + a + 1, -_k + n)*RisingFactorial(a + b + n + 1, _k)/factorial(_k), (_k, 0, n))/factorial(n)'],
    ['gegenbauer(n, a, x)', 'Sum((-1)**_k*(2*x)**(-2*_k + n)*RisingFactorial(a, -_k + n)/(factorial(_k)*factorial(-2*_k + n)), (_k, 0, floor(n/2)))'],
    ['chebyshevt(n, x)', 'Sum(x**(-2*_k + n)*(x**2 - 1)**_k*binomial(n, 2*_k), (_k, 0, floor(n/2)))'],
    ['chebyshevu(n, x)', 'Sum((-1)**_k*(2*x)**(-2*_k + n)*factorial(-_k + n)/(factorial(_k)*factorial(-2*_k + n)), (_k, 0, floor(n/2)))'],
    ['legendre(n, x)', 'Sum((-1)**_k*(1/2 - x/2)**_k*(x/2 + 1/2)**(-_k + n)*binomial(n, _k)**2, (_k, 0, n))'],
    ['assoc_legendre(n, m, x)', '(1 - x**2)**(m/2)*Sum((-1)**_k*x**(-2*_k - m + n)*factorial(-2*_k + 2*n)/(2**n*factorial(_k)*factorial(-_k + n)*factorial(-2*_k - m + n)), (_k, 0, floor(-m/2 + n/2)))'],
    ['hermite(n, x)', 'factorial(n)*Sum((-1)**_k*(2*x)**(-2*_k + n)/(factorial(_k)*factorial(-2*_k + n)), (_k, 0, floor(n/2)))'],
    ['hermite_prob(n, x)', 'factorial(n)*Sum((-1/2)**_k*x**(-2*_k + n)/(factorial(_k)*factorial(-2*_k + n)), (_k, 0, floor(n/2)))'],
    ['laguerre(n, x)', 'Sum(x**_k*RisingFactorial(-n, _k)/factorial(_k)**2, (_k, 0, n))'],
    ['assoc_laguerre(n, a, x)', 'gamma(a + n + 1)*Sum(x**_k*RisingFactorial(-n, _k)/(factorial(_k)*gamma(_k + a + 1)), (_k, 0, n))/factorial(n)'],
  ];
  for (const [src, expected] of R) it(src, () => expect(String(sj.rewrite(P(src), 'Sum'))).toBe(expected));
  it('polynomial is the same rewrite', () => {
    expect(String(sj.rewrite(sj.legendre(n, x), 'polynomial'))).toBe('Sum((-1)**_k*(1/2 - x/2)**_k*(x/2 + 1/2)**(-_k + n)*binomial(n, _k)**2, (_k, 0, n))');
  });
  it('laguerre of a negative degree, and the degrees the sums reject', () => {
    const q = new sj.Sym('q', { negative: true });
    expect(String(sj.rewrite(sj.laguerre(q, x), 'Sum'))).toBe('exp(x)*Sum((-x)**_k*RisingFactorial(q + 1, _k)/factorial(_k)**2, (_k, 0, -q - 1))');
    expect(() => sj.rewrite(sj.jacobi(q, a, b, x), 'Sum')).toThrow(RangeError);
    expect(() => sj.rewrite(sj.assocLaguerre(q, a, x), 'Sum')).toThrow(RangeError);
    // laguerre(1/2, x) itself raises; the unevaluated calls of a non-integer degree are rejected too
    const h = sj.Rational.of(1, 2);
    expect(() => sj.rewrite(sj.fn('laguerre', [h, x], { evaluate: false }), 'Sum')).toThrow(RangeError);
    expect(() => sj.rewrite(sj.fn('jacobi', [h, a, b, x], { evaluate: false }), 'Sum')).toThrow(RangeError);
  });
  it('hermite and hermite_prob in terms of each other', () => {
    expect(String(sj.rewrite(sj.hermite(n, x), 'hermite_prob'))).toBe('2**(n/2)*hermite_prob(n, sqrt(2)*x)');
    expect(String(sj.rewrite(sj.hermiteProb(n, x), 'hermite'))).toBe('hermite(n, sqrt(2)*x/2)/2**(n/2)');
  });
});

describe('printing', () => {
  it('LaTeX (SymPy _print_jacobi, ...)', () => {
    expect(sj.latex(sj.pow(sj.gegenbauer(n, a, x), 3))).toBe('\\left(C_{n}^{\\left(a\\right)}\\left(x\\right)\\right)^{3}');
    expect(sj.latex(sj.chebyshevt(n, x))).toBe('T_{n}\\left(x\\right)');
    expect(sj.latex(sj.assocLegendre(n, m, x))).toBe('P_{n}^{\\left(m\\right)}\\left(x\\right)');
    expect(sj.latex(sj.jacobi(n, a, b, x))).toBe('P_{n}^{\\left(a,b\\right)}\\left(x\\right)');
    expect(sj.latex(sj.hermiteProb(n, x))).toBe('\\operatorname{hermite}_{prob}{\\left(n,x \\right)}');
  });
});

describe('numerics (mpmath)', () => {
  const h = sj.Rational.of(1, 2);
  const t = sj.Rational.of(3, 10);
  const N = (e: sj.Expr): string => String(sj.evalf(e));
  it('legendre, assoc_legendre, chebyshevt, chebyshevu at a non-integer degree', () => {
    expect(N(sj.legendre(2.5, 0.3))).toBe('-0.463661013457223');
    expect(N(sj.assocLegendre(sj.Rational.of(5, 2), h, t))).toBe('-0.647000915205833');
    expect(N(sj.chebyshevt(sj.Rational.of(5, 2), t))).toBe('-0.999719960789020');
    expect(N(sj.chebyshevu(sj.Rational.of(5, 2), t))).toBe('-1.00716204486437');
  });
  it('jacobi, gegenbauer and assoc_laguerre at a non-integer degree', () => {
    // SymPy truncates the degree 5/2 to 2 when it evaluates the call
    expect(N(sj.jacobi(sj.Rational.of(5, 2), sj.Rational.of(1, 3), h, t))).toBe('-0.440173611111111');
    expect(N(sj.gegenbauer(sj.Rational.of(5, 2), sj.Rational.of(1, 3), t))).toBe('-0.253333333333333');
    expect(N(sj.assocLaguerre(2.5, 1.5, 0.3))).toBe('3.37000000000000');
    // the unevaluated calls have mpmath's values of the functions of degree 5/2
    const lazy = (name: 'jacobi' | 'gegenbauer' | 'assoc_laguerre', ...args: sj.ExprLike[]) => sj.fn(name, args, { evaluate: false });
    expect(N(lazy('jacobi', sj.Rational.of(5, 2), sj.Rational.of(1, 3), h, t))).toBe('-0.565673809268390');
    expect(N(lazy('gegenbauer', sj.Rational.of(5, 2), sj.Rational.of(1, 3), t))).toBe('-0.297094627875875');
    expect(N(lazy('assoc_laguerre', 2.5, 1.5, 0.3))).toBe('3.90633937877087');
    expect(String(sj.evalf(lazy('assoc_laguerre', 2.5, -3, 0.3), 30))).toBe('-0.00467667243452184378605625971611');
  });
  it('hermite at a non-integer degree and a complex argument', () => {
    expect(N(sj.hermite(sj.Rational.of(5, 2), sj.add(t, sj.I)))).toBe('-10.6262151108772 - 3.42201666927314*I');
    expect(N(sj.hermite(2.5, 0.3))).toBe('-3.07575876298222');
  });
  it('laguerre at a non-integer degree', () => {
    // SymPy raises ValueError for laguerre(7/3, x); the unevaluated call has the mpmath value laguerre(7/3, 0, 0.3)
    expect(() => sj.laguerre(sj.Rational.of(7, 3), x)).toThrow(RangeError);
    expect(N(sj.fn('laguerre', [sj.Rational.of(7, 3), t], { evaluate: false }))).toBe('0.369212301135399');
  });
  it('double precision (lambdify, numeric checks)', () => {
    const v = sj.toComplex(sj.fn('jacobi', [2.5, 0.5, 0.25, 0.3], { evaluate: false }));
    expect(v.re).toBeCloseTo(Number(String(sj.evalf(sj.fn('jacobi', [sj.Rational.of(5, 2), h, sj.Rational.of(1, 4), t], { evaluate: false })))), 12);
    expect(v.im).toBe(0);
  });
});


describe("SymPy's error messages", () => {
  it('TypeError and ValueError as SymPy 1.14 raises them', () => {
    expect(() => P('chebyshevu(-1/2, x)')).toThrow(new TypeError("bad operand type for unary -: 'NoneType'"));
    expect(() => P('assoc_laguerre(n, a, oo)')).toThrow(new TypeError('cannot determine truth value of Relational: n > 0'));
    expect(() => P('assoc_laguerre(n + 1, a, -oo)')).toThrow(new TypeError('cannot determine truth value of Relational: n + 1 > 0'));
    expect(() => P('jacobi(-5/2, a, b, x)')).toThrow('Cannot generate Jacobi polynomial of index -5/2');
    expect(() => P('jacobi(-2.5, a, b, x)')).toThrow('Cannot generate Jacobi polynomial of index -2.50000000000000');
    expect(() => P('assoc_laguerre(-1/2, a, x)')).toThrow('The index n must be nonnegative integer (got -1/2)');
    expect(() => P('hermite(-2.0, x)')).toThrow('The index n must be nonnegative integer (got -2.00000000000000)');
  });
});

describe('degrees above 100000', () => {
  it('stay unevaluated (SymPy expands the polynomial, which takes hours)', () => {
    const big = 10n ** 6n;
    expect(String(sj.jacobi(big, 1, 2, x))).toBe('jacobi(1000000, 1, 2, x)');
    expect(String(sj.gegenbauer(big, 2, x))).toBe('gegenbauer(1000000, 2, x)');
    expect(String(sj.assocLaguerre(big, 2, x))).toBe('assoc_laguerre(1000000, 2, x)');
  });
});
