// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { firstMotzkins, isMotzkin, motzkinNumbersInRange, parse, rewrite, series, symbols } from '../src';

const [x] = symbols('x');

describe('Motzkin numbers', () => {
  it('lists, ranges and membership', () => {
    expect(firstMotzkins(10).map(String)).toEqual(['1', '1', '2', '4', '9', '21', '51', '127', '323', '835']);
    expect(motzkinNumbersInRange(2n, 300n).map(String)).toEqual(['2', '4', '9', '21', '51', '127']);
    expect(isMotzkin(5n)).toBe(false);
    expect(isMotzkin(127n)).toBe(true);
  });
});

describe('rewrites and series of special functions', () => {
  it('frac in terms of floor', () => {
    expect(String(rewrite(parse('frac(x)'), 'floor'))).toBe('x - floor(x)');
  });
  it('series of sinc', () => {
    expect(String(series(parse('sinc(x)'), x))).toBe('1 - x**2/6 + x**4/120 + O(x**6)');
  });
});

import { add, factor, harmonic, neg, oo, pow, rationalInterpolate, Rational, Sym } from '../src';

describe('factor of powers and deep factoring', () => {
  it('factors bases of large powers without expanding', () => {
    expect(String(factor(parse('(x**2 + 4*x + 4)**10000000*(x**2 + 1)')))).toBe('(x + 2)**20000000*(x**2 + 1)');
  });
  it('factors inside exponents with deep', () => {
    expect(String(factor(parse('2**(x**2 + 2*x + 1)'), { deep: true }))).toBe('2**((x + 1)**2)');
  });
});

describe('rational_interpolate and harmonic at infinity', () => {
  it('interpolates rational functions', () => {
    const data = [[1, 2], [2, 3], [3, 4], [4, 5], [5, 6]].map(([a, b]) => [Rational.of(a!), Rational.of(b!)] as const);
    expect(String(rationalInterpolate(data, 1))).toBe('x + 1');
  });
  it('harmonic(oo, m) for symbolic m', () => {
    const m = new Sym('m', { positive: true });
    expect(String(harmonic(oo, add(m, 1)))).toBe('zeta(m + 1)');
    expect(String(harmonic(oo, neg(m)))).toBe('nan');
  });
});

import { Function as Fn, diff, doit, derivative } from '../src';

describe('derivatives of undefined functions', () => {
  const f = Fn('f');
  const g = Fn('g');
  const y = symbols('y')[0];
  it('chain rule through a nested undefined function', () => {
    expect(String(diff(f(g(x)), x))).toBe('Derivative(f(g(x)), g(x))*Derivative(g(x), x)');
  });
  it('sorts symbol variables of evaluated derivatives only', () => {
    expect(String(diff(diff(f(x, y), y), x))).toBe('Derivative(f(x, y), x, y)');
    expect(String(derivative(f(x, y), [[y, 1], [x, 1]]))).toBe('Derivative(f(x, y), y, x)');
  });
  it('doit evaluates Derivative objects', () => {
    expect(String(doit(derivative(f(f(x)), [[x, 1]])))).toBe('Derivative(f(x), x)*Derivative(f(f(x)), f(x))');
  });
});

import { integrate } from '../src';

describe('antiderivatives of special and inverse functions', () => {
  it('matches SymPy', () => {
    const cases: [string, string][] = [
      ['li(x)', 'x*li(x) - Ei(2*log(x))'],
      ['Ei(x)', 'x*Ei(x) - exp(x)'],
      ['Si(x)', 'x*Si(x) + cos(x)'],
      ['erf(x)', 'x*erf(x) + exp(-x**2)/sqrt(pi)'],
      ['asinh(x)', 'x*asinh(x) - sqrt(x**2 + 1)'],
      ['acot(x)', 'x*acot(x) + log(x**2 + 1)/2'],
    ];
    for (const [f, F] of cases) expect(String(integrate(parse(f), x))).toBe(F);
  });
});

import { Max, Min } from '../src';

describe('nested Min/Max collapse (SymPy)', () => {
  const [a, b, c, d, e] = symbols('a b c d e');
  it('drops repeated arguments inside nested Min/Max', () => {
    expect(String(Min(a, Max(b, Min(a, c, d))))).toBe('Min(a, Max(b, Min(c, d)))');
    expect(String(Min(a, Max(b, Min(c, d, Max(a, e)))))).toBe('Min(a, Max(b, Min(a, c, d)))');
  });
});

import { arg, atan2 } from '../src';

describe('series of multi-argument functions and nested arg', () => {
  const [y] = symbols('y');
  it('atan2 series in either argument', () => {
    expect(String(series(atan2(x, y), x, 0, 2))).toBe('atan2(0, y) + x/y + O(x**2)');
    expect(String(series(atan2(x, y), y, 0, 2))).toBe('-y/x + atan2(x, 0) + O(y**2)');
  });
  it('arg of nested arg', () => {
    expect(String(arg(arg(arg(arg(x)))))).toBe('nan');
  });
});

import { expandSymbolNames } from '../src';

describe('symbols name parsing (SymPy)', () => {
  it('ranges, parentheses and escaped commas', () => {
    expect(expandSymbolNames(':3:2')).toEqual(['00', '01', '10', '11', '20', '21']);
    expect(expandSymbolNames('x((a:b))')).toEqual(['x(a)', 'x(b)']);
    expect(expandSymbolNames('x(:1\\,:2)')).toEqual(['x(0,0)', 'x(0,1)']);
    expect(expandSymbolNames('x:3, y')).toEqual(['x0', 'x1', 'x2', 'y']);
    expect(expandSymbolNames('a:d')).toEqual(['a', 'b', 'c', 'd']);
  });
});

import { loggamma, mul, multigamma } from '../src';

describe('symbolic gamma-family evaluation (SymPy)', () => {
  const n = new Sym('n', { positive: true, integer: true });
  const p = new Sym('p', { positive: true, integer: true });
  it('loggamma of a half integer symbol', () => {
    expect(String(loggamma(mul(Rational.of(1, 2), n)))).toBe('log(2**(1 - n)*sqrt(pi)*gamma(n)/gamma(n/2 + 1/2))');
  });
  it('multigamma with a symbolic order', () => {
    expect(String(multigamma(x, p))).toBe('pi**(p*(p - 1)/4)*Product(gamma(-_k/2 + x + 1/2), (_k, 1, p))');
  });
  it('Si as an integral of sinc', () => {
    expect(String(rewrite(parse('Si(z)'), 'sinc'))).toBe('Integral(sinc(_t), (_t, 0, z))');
  });
});

import { I, sqrt } from '../src';

describe('factor over an algebraic extension', () => {
  it('gaussian and sqrt(2)', () => {
    expect(String(factor(parse('x**2 + 1'), { gaussian: true }))).toBe('(x - I)*(x + I)');
    expect(String(factor(parse('x**2 - 2'), { extension: [sqrt(2)] }))).toBe('(x - sqrt(2))*(x + sqrt(2))');
    expect(String(factor(parse('x**3 + x'), { extension: [I] }))).toBe('x*(x - I)*(x + I)');
  });
});

import { acos, cos, dsolve, sin } from '../src';

describe('first-order exact ODEs and acos of negated arguments', () => {
  it('acos(-u) stays unevaluated', () => {
    expect(String(acos(neg(x)))).toBe('acos(-x)');
  });
  it('1st_exact gives both branches', () => {
    const f = Fn('f');
    const eq = add(mul(cos(f(x)), sin(x)), mul(diff(f(x), x), cos(x), sin(f(x))));
    const r = dsolve(eq, f(x));
    expect(Array.isArray(r) ? r.map(String) : String(r)).toEqual(['Eq(f(x), -acos(C1/cos(x)) + 2*pi)', 'Eq(f(x), acos(C1/cos(x)))']);
  });
});

import { abs, subs as subsE } from '../src';

describe('abs series and derivative substitution', () => {
  it('one-sided series of abs at 0', () => {
    expect(String(series(abs(x), x, 0, 6, '+'))).toBe('x');
    expect(String(series(abs(x), x, 0, 6, '-'))).toBe('-x');
  });
  it('substituting a lower derivative inside a higher one', () => {
    const f = Fn('f');
    const [yy] = symbols('y');
    expect(String(subsE(derivative(f(x), [[x, 2]]), [[derivative(f(x), [[x, 1]]), yy]]))).toBe('Derivative(y, x)');
  });
});

import { nsolve } from '../src';

describe('nsolve with a precision', () => {
  it('refines in arbitrary precision', () => {
    expect(String(nsolve(parse('cos(x) - x'), x, 1, { prec: 50 }))).toBe('0.73908513321516064165531208767387340401341175890076');
  });
});

describe('gamma-type definite integrals', () => {
  it('conditional result like SymPy', () => {
    const [a] = symbols('a');
    const n = new Sym('n', { positive: true });
    const f = parse('x**a*exp(-x)', { symbols: { a } });
    expect(String(integrate(f, x, [0, oo]))).toBe('Piecewise((gamma(a + 1), re(a) > -1), (Integral(x**a*exp(-x), (x, 0, oo)), True))');
    expect(String(integrate(f, x, [0, oo], { conds: 'none' }))).toBe('gamma(a + 1)');
    expect(String(integrate(mul(pow(x, n), parse('exp(-x)')), x, [0, oo]))).toBe('gamma(n + 1)');
  });
});

import { Product, sumIsConvergent, Concrete } from '../src';

describe('convergence of infinite products', () => {
  it('uses the comparison with p-series of log(term)', () => {
    const n = new Sym('n');
    expect(sumIsConvergent(Product(parse('n/(n + 1)'), [n, 1, oo]) as Concrete)).toBe(false);
    expect(sumIsConvergent(Product(parse('cos(pi/n)'), [n, 1, oo]) as Concrete)).toBe(true);
  });
});

import { Poly } from '../src';

describe('greatest factorial factorization and nseries logx', () => {
  it('gff_list', () => {
    const p = Poly.from(parse('x**5 + 2*x**4 - x**3 - 2*x**2'), [x]);
    expect(p.gffList().map(([h, k]) => `${h.asExpr()}:${k}`)).toEqual(['x:1', 'x + 2:4']);
  });
  it('series with logx', () => {
    const logx = new Sym('logx');
    expect(String(series(parse('x**y'), x, 0, 2, '+', { logx }))).toBe('exp(logx*y)');
    expect(String(series(parse('x**y'), x, 0, 2))).toBe('x**y');
  });
});

import { gamma, maximum, minimum } from '../src';

describe('series at poles of gamma and extrema of periodic functions', () => {
  it('Laurent series of gamma at 0', () => {
    expect(String(series(gamma(x), x, 0, 3))).toBe(
      '1/x - EulerGamma + x*(EulerGamma**2/2 + pi**2/12) + x**2*(-EulerGamma*pi**2/12 - zeta(3)/3 - EulerGamma**3/6) + O(x**3)',
    );
  });
  it('maximum and minimum of sin(x)*cos(x)', () => {
    expect(String(maximum(parse('sin(x)*cos(x)'), x))).toBe('1/2');
    expect(String(minimum(parse('sin(x)*cos(x)'), x))).toBe('-1/2');
  });
});
