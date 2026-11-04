// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/assumptions.ts.
// Assumption queries on symbols and expressions. Expected values are SymPy 1.14's
// (sympy.core.tests.test_assumptions).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { isIntegerQ, isNegative, isNonNegative, isPositive, isReal, isZero } from '../../src/core/assumptions';
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
