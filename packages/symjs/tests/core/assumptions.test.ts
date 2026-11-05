// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/assumptions.ts.
// Assumption queries on symbols and expressions. Expected values are SymPy 1.14's
// (sympy.core.tests.test_assumptions).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { isIntegerQ, isNegative, isNonNegative, isNonZero, isPolar, isPositive, isReal, isZero } from '../../src/core/assumptions';
import { at } from '../../src/core/guard';
import { Pow, S } from '../../src/core/nodes';
import { add, mul } from '../../src/core/ops';

const [x] = sj.symbols('x');

const { I } = sj;

describe('assumption queries (SymPy test_assumptions)', () => {
  it('knows that 0 to a negative power is not a real number', () => {
    // 0**-1 is zoo; the raw power is not known to be real
    expect(isReal(new Pow(S.Zero, S.NegOne))).toBe(undefined);
  });
  it('knows that a positive power of a nonnegative number is real', () => {
    // SymPy: sqrt(y).is_real is True for nonnegative y
    const yn = new sj.Sym('y', { nonnegative: true });
    expect(isReal(sj.sqrt(yn))).toBe(true);
  });
  it('does not know the sign of Abs(x)', () => {
    // SymPy: Abs(x).is_positive is None
    expect(isPositive(sj.Abs(x))).toBe(undefined);
    expect(isNegative(sj.Abs(x))).toBe(undefined);
    // SymPy gives None for Abs(x).is_positive with zero=False, but the modulus of a nonzero number is positive
    expect(isPositive(sj.Abs(new sj.Sym('x', { zero: false })))).toBe(true);
  });
  it('knows a product with one imaginary factor is not real', () => {
    const p = new sj.Sym('p', { positive: true });
    expect(isReal(mul(I, p))).toBe(false);
    expect(isReal(mul(I, x))).toBe(undefined);
  });
});

describe('signs of numbers and powers (SymPy Expr._eval_is_extended_positive_negative, Pow)', () => {
  const q = new sj.Sym('q', { negative: true });
  const p = new sj.Sym('p', { positive: true });
  const r = new sj.Sym('r', { real: true });
  const P = (t: string): sj.Expr => sj.parse(t, { symbols: { q, p, r, x } } as never);
  it.each([
    // [expr, isPositive, isNegative]; SymPy decides a sum without symbols numerically
    ['pi - 3', true, false],
    ['3 - pi', false, true],
    ['1 + I', false, false],
    ['sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6))', undefined, undefined],
    ['-1 + sin(pi/7)**2 + cos(pi/7)**2', undefined, undefined],
    ['x + 1', undefined, undefined],
    ['1/q', false, true],
    ['q**3', false, true],
    ['q**2', true, false],
    ['q**(-2)', true, false],
    ['sqrt(q)', undefined, false],
    ['p**x', undefined, undefined],
    ['p**r', true, false],
    ['r**2', undefined, false],
    ['sqrt(x)', undefined, false],
  ])('%s', (t, pos, negv) => {
    const e = P(t);
    expect(isPositive(e)).toBe(pos);
    expect(isNegative(e)).toBe(negv);
  });
  it('gives up on sums whose value cannot be computed', () => {
    // a term without a numeric value (an undefined function of a number)
    const f = sj.SymFunction('f');
    expect(isPositive(add(f(1), 1))).toBeUndefined();
  });
});

describe('signs of a signed symbol plus a rational (SymPy Add._eval_is_extended_positive, _monotonic_sign)', () => {
  const syms = [
    new sj.Sym('ip', { positive: true, integer: true }),
    new sj.Sym('p', { positive: true }),
    new sj.Sym('ni', { negative: true, integer: true }),
    new sj.Sym('n', { negative: true }),
    new sj.Sym('nn', { nonnegative: true }),
    new sj.Sym('np', { nonpositive: true }),
    new sj.Sym('r', { real: true }),
    new sj.Sym('z', { zero: true }),
    new sj.Sym('zi', { integer: false }),
  ];
  const P = (t: string): sj.Expr => sj.parse(t, { symbols: syms } as never);
  // [expr, is_positive, is_negative, is_nonnegative, is_zero, is_integer] of SymPy 1.14
  const u = undefined;
  it.each<[string, boolean | undefined, boolean | undefined, boolean | undefined, boolean | undefined, boolean | undefined]>([
    ['ip - 1', u, false, true, u, true],
    ['ip - 2', u, u, u, u, true],
    ['ip + 1/2', true, false, true, false, false],
    ['ip - 1/2', true, false, true, false, false],
    ['p - 1', u, u, u, u, u],
    ['p + 1', true, false, true, false, u],
    ['1 - ip', false, u, u, u, true],
    ['2 - ip', u, u, u, u, true],
    // SymPy is_positive is None, while is_nonpositive is True: ni + 1 <= 0
    ['ni + 1', false, u, u, u, true],
    ['ni + 2', u, u, u, u, true],
    ['ni - 1', false, true, false, false, true],
    ['nn - 1', u, u, u, u, u],
    ['nn + 1', true, false, true, false, u],
    ['np + 1', u, u, u, u, u],
    ['np - 1', false, true, false, false, u],
    ['n + 1', u, u, u, u, u],
    ['n - 1', false, true, false, false, u],
    ['1 - p', u, u, u, u, u],
    ['-ip - 1', false, true, false, false, true],
    ['-nn + 1', u, u, u, u, u],
    ['-nn - 1', false, true, false, false, u],
    ['r + 1', u, u, u, u, u],
    ['z + 1', true, false, true, false, true],
    ['z - 1', false, true, false, false, true],
    ['zi + 1', u, u, u, false, false],
    ['ip + zi', u, u, u, false, false],
  ])('%s', (t, pos, negv, nonneg, zero, integer) => {
    const e = P(t);
    expect([isPositive(e), isNegative(e), isNonNegative(e), isZero(e), isIntegerQ(e)]).toEqual([pos, negv, nonneg, zero, integer]);
  });
  it('knows that a non-real number is neither positive nor negative', () => {
    // SymPy: (1 + I).is_positive and (1 + I).is_negative are False
    expect([isPositive(add(1, I)), isNegative(add(1, I))]).toEqual([false, false]);
  });
  it('honours zero=True and integer=False on a symbol', () => {
    const [z, zi] = [at(syms, 7), at(syms, 8)];
    expect([isZero(z), isIntegerQ(z), isPositive(z), isNegative(z), isNonNegative(z), isReal(z)]).toEqual([true, true, false, false, true, true]);
    expect([isZero(zi), isIntegerQ(zi), isReal(zi)]).toEqual([false, false, undefined]);
    expect([sj.isZero(z), sj.isIntegerValued(zi)]).toEqual([true, false]);
  });
});

describe('LambertW and log (SymPy LambertW._eval_is_extended_real, log._eval_is_extended_positive)', () => {
  const P = sj.parse;
  const xp = new sj.Sym('x', { positive: true });
  const r = new sj.Sym('r', { real: true });
  const n = new sj.Sym('n', { negative: true });
  const k = new sj.Sym('k', { integer: true });
  const q = (e: sj.Expr) => [isReal(e), isPositive(e), isNegative(e), isZero(e)];
  it('LambertW', () => {
    // SymPy (is_real, is_positive, is_negative, is_zero); None is undefined
    expect(q(sj.LambertW(xp))).toEqual([true, undefined, undefined, false]);
    expect(q(P('LambertW(1)'))).toEqual([true, true, false, false]);
    expect(q(P('LambertW(-1/4)'))).toEqual([true, false, true, false]);
    expect(q(P('LambertW(-1)'))).toEqual([false, false, false, false]);
    expect(q(P('LambertW(-1/4, -1)'))).toEqual([true, false, true, false]);
    expect(q(P('LambertW(2, 1)'))).toEqual([false, false, false, false]);
    expect(q(sj.LambertW(xp, -1))).toEqual([false, false, false, false]);
    expect(q(sj.LambertW(mul(-1, xp), -1))).toEqual([false, false, false, false]);
    expect(q(sj.LambertW(r))).toEqual([undefined, undefined, undefined, undefined]);
    expect(q(sj.LambertW(add(xp, mul(-1, sj.exp(-1)))))).toEqual([true, undefined, undefined, undefined]);
    // SymPy None, None, None, False
    expect(q(sj.LambertW(n))).toEqual([undefined, undefined, undefined, false]);
    expect(q(sj.LambertW(r, -1))).toEqual([undefined, undefined, undefined, false]);
    expect(q(sj.LambertW(xp, k))).toEqual([undefined, undefined, undefined, false]);
    // SymPy fuzzy_and([x.is_zero, k.is_zero]): False and None
    expect([isZero(sj.LambertW(r, 1)), isZero(sj.LambertW(r, k))]).toEqual([false, undefined]);
    // SymPy False: -x is not zero for a positive x (Mul._eval_is_zero)
    expect(isZero(sj.LambertW(mul(-1, xp)))).toBe(false);
  });
  it('log', () => {
    // SymPy (is_real, is_positive, is_negative)
    const l = (e: sj.Expr) => [isReal(e), isPositive(e), isNegative(e)];
    expect(l(P('-log(2)'))).toEqual([true, false, true]);
    expect(l(P('log(2)'))).toEqual([true, true, false]);
    expect(l(sj.log(xp))).toEqual([true, undefined, undefined]);
    expect(l(sj.log(add(xp, 1)))).toEqual([true, true, false]);
    // log(x) for a real x: SymPy None
    expect(l(sj.log(r))).toEqual([undefined, undefined, undefined]);
    expect(isNegative(sj.log(add(r, 2)))).toBeUndefined();
    // SymPy log(Abs(y) + 1).is_negative = False
    expect(isNegative(sj.log(add(sj.abs(x), 1)))).toBe(false);
    // an extension node that does not say whether it is real
    expect(isReal(sj.defineFunction('g', {})(1))).toBeUndefined();
  });
});

describe('signs of functions of numbers (SymPy Expr._eval_is_extended_positive_negative)', () => {
  const P = sj.parse;
  // [expr, is_positive, is_negative] of SymPy 1.14; None is undefined
  it.each<[string, boolean | undefined, boolean | undefined]>([
    ['sin(1)', true, false],
    ['cos(2)', false, true],
    ['sin(4)', false, true],
    ['sin(10**30)', false, true],
    ['zeta(1/2)', false, true],
    ['asin(-1/3)', false, true],
    // a value that is not real gives None (no _prec on a complex evalf result)
    ['sin(1 + I)', undefined, undefined],
    // the extended sign without finiteness: besselj(1, 5) < 0 is not is_negative in SymPy
    ['besselj(1, 5)', false, undefined],
    ['Ei(-1)', false, undefined],
    ['stieltjes(1)', false, undefined],
    // no value: a function without a numeric implementation
    ['riemann_xi(3)', undefined, undefined],
    // evalf raises (mpmath's ValueError): SymPy None
    ['erfinv(2)', undefined, undefined],
  ])('%s', (t, pos, negv) => {
    const e = P(t);
    expect([isPositive(e), isNegative(e)]).toEqual([pos, negv]);
    // the sign is computed once per expression
    expect([isPositive(e), isNegative(e)]).toEqual([pos, negv]);
  });
  it('decides is_zero of products and powers of nonzero factors (SymPy Mul/Pow._eval_is_zero)', () => {
    const p = new sj.Sym('p', { positive: true });
    const z = new sj.Sym('z', { zero: true });
    expect([isZero(mul(-1, p)), isZero(mul(p, x)), isZero(new Pow(p, sj.Rational.of(1n, 3n))), isZero(new Pow(x, S.Half))]).toEqual([false, undefined, false, undefined]);
    expect([String(mul(z, x)), isNonZero(mul(z, x))]).toEqual(['x*z', false]);
  });
  it('isPolar (SymPy is_polar)', () => {
    const x = sj.symbol('x');
    const y = sj.symbol('y');
    expect(isPolar(sj.polarLift(x))).toBe(true);
    expect(isPolar(new sj.Sym('w', { polar: true }))).toBe(true);
    expect(isPolar(sj.mul(2, sj.polarLift(x)))).toBe(true);
    expect(isPolar(sj.pow(sj.polarLift(x), 2))).toBe(true);
    // SymPy (polar_lift(x)**y).is_polar is True (Pow.is_polar = base.is_polar), and a product is
    // polar when its other factors are positive: (q*polar_lift(x)).is_polar, but not x*polar_lift(x)
    expect(isPolar(sj.pow(sj.polarLift(x), y))).toBe(true);
    expect(isPolar(sj.mul(new sj.Sym('q', { positive: true }), sj.polarLift(x)))).toBe(true);
    expect(isPolar(sj.mul(x, sj.polarLift(x)))).toBe(false);
    expect(isPolar(x)).toBe(false);
  });
});
