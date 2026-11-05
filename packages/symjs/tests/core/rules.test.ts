// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/rules.ts; the cases of SymPy 1.14's Transform docstring.
import { describe, expect, it } from 'vitest';
import { Transform, add, symbols, type Expr } from '../../src';

const [x] = symbols('x') as [Expr];

describe('Transform', () => {
  it('maps every key without a filter', () => {
    const add1 = new Transform((k: Expr | number) => add(k, 1));
    expect(String(add1.at(1))).toBe('2');
    expect(String(add1.at(x))).toBe('x + 1');
    expect(add1.has(x)).toBe(true);
  });

  it('maps only the keys the filter accepts', () => {
    const add1Odd = new Transform(
      (k: number) => add(k, 1),
      (k: number) => k % 2 === 1,
    );
    expect(add1Odd.has(2)).toBe(false);
    expect(add1Odd.get(2, 0)).toBe(0);
    expect(add1Odd.has(3)).toBe(true);
    expect(String(add1Odd.at(3))).toBe('4');
    expect(String(add1Odd.get(3, 0))).toBe('4');
    expect(() => add1Odd.at(2)).toThrow(RangeError);
  });
});
