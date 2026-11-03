// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/assumptions.ts.
// Assumption queries on symbols and expressions. Expected values are SymPy 1.14's
// (sympy.core.tests.test_assumptions).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { isNegative, isPositive, isReal } from '../../src/core/assumptions';
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
