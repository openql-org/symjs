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

import { add, factor, harmonic, neg, oo, rationalInterpolate, Rational, Sym } from '../src';

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
