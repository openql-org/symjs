// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transform.ts.
// IntegralTransform and the unevaluated transform classes. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  Integral,
  S,
  add,
  parse,
  pow,
  principalValue,
  symbols,
  transformIntegral,
  Curve,
  Sym,
  mul,
  simplify,
  Rational,
  asSum,
  lineIntegrate,
  sstr,
} from '../../src';

const [x, u, a] = symbols('x u a');

describe('Integral.transform', () => {
  it('renames and shifts the integration variable', () => {
    const i = new Integral([x, x, S.Zero, S.One]);
    expect(String(transformIntegral(i, x, add(u, a), u))).toBe('Integral(a + u, (u, -a, 1 - a))');
    expect(String(transformIntegral(i, x, add(u, a), a))).toBe('Integral(a + u, (a, -u, 1 - u))');
    expect(String(transformIntegral(new Integral([parse('x*cos(x**2 - 1)'), x, S.Zero, S.One]), x, u))).toBe(
      'Integral(u*cos(u**2 - 1), (u, 0, 1))',
    );
  });
});

describe('Integral.principal_value', () => {
  it('handles singularities inside the interval and infinite limits', () => {
    expect(String(principalValue(new Integral([pow(x, -3), x, parse('-10'), parse('10')])))).toBe('0');
    expect(String(principalValue(new Integral([pow(x, -3), x, S.NegativeInfinity, S.Infinity])))).toBe('0');
    expect(String(principalValue(new Integral([add(x, 1), x, S.NegativeInfinity, S.Infinity])))).toBe('oo');
  });
});


const [y, t, n] = symbols('y t n');
const I01 = (lo: number, hi: number) => new Integral([x, x, Rational.of(lo), Rational.of(hi)]);

describe('Integral.transform (SymPy 1.14)', () => {
  it('maps the limits through the positive inverse', () => {
    // Integral(x, (x, 0, 1)).transform(x, u**2) -> Integral(2*u**3, (u, 0, 1))
    expect(sstr(transformIntegral(I01(0, 1), x, parse('u**2')))).toBe('Integral(2*u**3, (u, 0, 1))');
    expect(sstr(transformIntegral(I01(1, 4), x, parse('u**2')))).toBe('Integral(2*u**3, (u, 1, 2))');
    expect(sstr(transformIntegral(I01(1, 4), x, parse('2*u')))).toBe('Integral(4*u, (u, 1/2, 2))');
    // the limit 0 maps to log(0): SymPy takes the limit, -oo
    expect(sstr(transformIntegral(I01(0, 1), x, parse('exp(u)')))).toBe('Integral(exp(2*u), (u, -oo, 0))');
    expect(sstr(transformIntegral(I01(1, 4), x, parse('exp(u)')))).toBe('Integral(exp(2*u), (u, 0, log(4)))');
    // a variable already positive is solved for directly
    const v = new Sym('v', { positive: true });
    expect(sstr(transformIntegral(I01(1, 4), x, pow(v, 2)))).toBe('Integral(2*v**3, (v, 1, 2))');
    // indefinite: Integral(x**2, x).transform(x, 2*u) -> Integral(8*u**2, u)
    expect(sstr(transformIntegral(new Integral([parse('x**2'), x]), x, parse('2*u')))).toBe('Integral(8*u**2, u)');
  });

  it('swaps reversed limits; x = -u is solved without the positivity assumption', () => {
    // SymPy raises "no solution for solve(F(x) - f(u), u)" for x = -u (its posify leaves no root);
    // the substitution is valid: Integral(-u, (u, -1, 0)) = 1/2 = Integral(x, (x, 0, 1))
    expect(sstr(transformIntegral(I01(0, 1), x, parse('-u')))).toBe('Integral(-u, (u, -1, 0))');
    expect(sstr(transformIntegral(I01(1, 4), x, parse('-u')))).toBe('Integral(-u, (u, -4, -1))');
  });

  it('errors like SymPy (ValueError there)', () => {
    // "The mapping between F(x) and f(u) did not give a unique limit."
    expect(() => transformIntegral(I01(0, 1), x, parse('u**2 - u'))).toThrow(RangeError);
    // "When f(u) has more than one free symbol, the one replacing x must be identified"
    expect(() => transformIntegral(I01(0, 1), x, parse('u + a'))).toThrow(TypeError);
    // u does not occur in f(u)
    expect(() => transformIntegral(I01(0, 1), x, a, u)).toThrow(RangeError);
    expect(() => transformIntegral(I01(0, 1), u, u)).toThrow(TypeError);
  });
});

describe('Integral.principal_value (SymPy 1.14)', () => {
  it('equal limits, singular end point, no antiderivative, indefinite', () => {
    expect(sstr(principalValue(new Integral([parse('1/x'), x, S.One, S.One])))).toBe('0');
    // ValueError: The principal value is not defined in the given interval due to singularity at 0.
    expect(() => principalValue(new Integral([parse('1/x'), x, S.Zero, S.One]))).toThrow(RangeError);
    const i = new Integral([parse('sin(sin(x))/x'), x, Rational.of(-1), S.One]);
    expect(sstr(principalValue(i))).toBe('Integral(sin(sin(x))/x, (x, -1, 1))');
    expect(() => principalValue(new Integral([parse('1/x'), x]))).toThrow(TypeError);
  });
});

describe('Integral.as_sum (SymPy 1.14)', () => {
  const I = new Integral([parse('x**2'), x, S.Zero, Rational.of(2)]);
  it('left, right and trapezoid rules', () => {
    expect(sstr(asSum(I, 4, 'left'))).toBe('7/4');
    expect(sstr(asSum(I, 4, 'right'))).toBe('15/4');
    expect(sstr(asSum(I, 4, 'trapezoid'))).toBe('11/4');
    expect(sstr(asSum(I, 4))).toBe('21/8');
    // I.as_sum(n, 'left', evaluate=False) -> 2*Sum(4*(_k - 1)**2/n**2, (_k, 1, n))/n
    expect(sstr(asSum(I, n, 'left', { evaluate: false }))).toBe('2*Sum(4*(_k - 1)**2/n**2, (_k, 1, n))/n');
    // I.as_sum(4, 'trapezoid', evaluate=False) -> 1 + Sum(_k**2/4, (_k, 1, 3))/2
    // (the printer orders this Add as Sum(...)/2 + 1, so the terms are checked apart)
    expect(sstr(add(asSum(I, 4, 'trapezoid', { evaluate: false }), -1))).toBe('Sum(_k**2/4, (_k, 1, 3))/2');
    // I.as_sum(n, 'right') -> 8*(n**3/3 + n**2/2 + n/6)/n**3
    // (symjs evaluates the Sum to an equal expression in another form)
    expect(sstr(simplify(add(asSum(I, n, 'right'), mul(-1, parse('8*(n**3/3 + n**2/2 + n/6)/n**3')))))).toBe('0');
    expect(() => asSum(new Integral([x, x]), 4)).toThrow(TypeError);
  });
});

describe('Curve and line_integrate (SymPy 1.14)', () => {
  it('prints and checks the dimension', () => {
    const C = new Curve([parse('exp(t) + 1'), parse('exp(t) - 1')], [t, S.Zero, parse('log(2)')]);
    expect(String(C)).toBe('Curve((exp(t) + 1, exp(t) - 1), (t, 0, log(2)))');
    // ValueError: Field variable size does not match curve dimension.
    expect(() => lineIntegrate(parse('x + y'), new Curve([t, t], [t, S.Zero, S.One]), [x])).toThrow(RangeError);
    expect(y).toBeDefined();
  });
});


describe('as_sum, euler_maclaurin and nsolve bisection', () => {
  it('match SymPy', async () => {
    const { asSum, eulerMaclaurin, Integral, Sum, nsolve, Rational } = await import('../../src');
    const [x, n, k, b] = symbols('x n k b');
    const I2 = new Integral([parse('x**2'), x, Rational.of(0), Rational.of(2)]);
    expect(sstr(asSum(I2, n, 'midpoint', { evaluate: false }))).toBe('2*Sum((2*_k/n - 1/n)**2, (_k, 1, n))/n');
    expect(sstr(asSum(I2, 4, 'midpoint'))).toBe('21/8');
    expect(eulerMaclaurin(Sum(k, [k, 2, b]) as never).map((e) => sstr(e))).toEqual(['b**2/2 + b/2 - 1', '0']);
    expect(sstr(nsolve(parse('cos(x)*cosh(x) - 1'), x, [313, 317]))).toBe('315.730061685774');
  });
});
