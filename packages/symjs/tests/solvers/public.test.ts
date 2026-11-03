// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/public.ts: the monotonicity wrappers; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { isDecreasing, isStrictlyDecreasing, isStrictlyIncreasing, oo, parse, symbols } from '../../src';
import { interval } from '../../src/sets/sets';

const [x] = symbols('x');

describe('monotonicity wrappers', () => {
  it('follow SymPy (None is unknown)', () => {
    const pos = interval(0, oo);
    const neg = interval(oo.neg(), 0);
    const unit = interval(0, 1);
    expect([parse('-x**3'), parse('x**2')].map((e) => isStrictlyIncreasing(e))).toEqual([false, false]);
    expect([isStrictlyIncreasing(parse('-x'), unit, x), isStrictlyIncreasing(parse('x**2'), neg)]).toEqual([false, false]);
    expect([parse('-x**3'), parse('x**2')].map((e) => isDecreasing(e))).toEqual([true, false]);
    expect([isDecreasing(parse('-x'), unit), isDecreasing(parse('x**2'), pos, x)]).toEqual([true, false]);
    expect([parse('x**3'), parse('x**2')].map((e) => isStrictlyDecreasing(e))).toEqual([false, false]);
    expect([isStrictlyDecreasing(parse('-x'), unit), isStrictlyDecreasing(parse('x**2'), pos, x)]).toEqual([true, false]);
  });
});
