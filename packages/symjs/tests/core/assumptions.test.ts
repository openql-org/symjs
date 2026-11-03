// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/assumptions.ts.
// Assumption queries on symbols and expressions. Expected values are SymPy 1.14's
// (sympy.core.tests.test_assumptions).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { isNegative, isPositive, isReal } from '../../src/core/assumptions';
import { Pow, S } from '../../src/core/nodes';
import { mul } from '../../src/core/ops';

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
