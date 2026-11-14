// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/conventions.ts. Expected values are SymPy 1.14's split_super_sub.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

describe('splitSuperSub (SymPy split_super_sub)', () => {
  const cases: [string, [string, string[], string[]]][] = [
    ['a_x^1', ['a', ['1'], ['x']]],
    ['var_sub1__sup_sub2', ['var', ['sup'], ['sub1', 'sub2']]],
    ['', ['', [], []]],
    ['x', ['x', [], []]],
    ['x12', ['x', [], ['12']]],
    ['x_1^2__3', ['x', ['2', '3'], ['1']]],
    ['alpha_beta', ['alpha', [], ['beta']]],
    ['x__a__b', ['x', ['a', 'b'], []]],
    // Python's \w is Unicode-aware: a Greek name ending with digits
    ['α1', ['α', [], ['1']]],
    ['x2_3', ['x', [], ['2', '3']]],
    ['a^b_c', ['a', ['b'], ['c']]],
  ];
  for (const [text, want] of cases) it(JSON.stringify(text), () => expect(sj.splitSuperSub(text)).toEqual(want));
});

describe('requiresPartial (SymPy requires_partial)', () => {
  it('counts the free symbols that may not be integers', () => {
    const [x, y] = sj.symbols('x y');
    const n = sj.symbol('n', { integer: true });
    const f = sj.SymFunction('f');
    // SymPy test_requires_partial
    expect(sj.requiresPartial(sj.Derivative(sj.mul(x, y), x))).toBe(true);
    expect(sj.requiresPartial(sj.Derivative(f(x), x))).toBe(false);
    expect(sj.requiresPartial(sj.Derivative(f(x, y), x))).toBe(true);
    expect(sj.requiresPartial(sj.Derivative(sj.pow(x, n), x))).toBe(false);
  });
});
