// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/parameters.ts; expected values from SymPy 1.14 (with evaluate(False): ...).
import { describe, expect, it } from 'vitest';
import { Add, Mul, Pow, add, evaluate, globalParameters, mul, pow, symbols } from '../../src';

const [x] = symbols('x') as [ReturnType<typeof symbols>[0]];

describe('evaluate', () => {
  it('keeps sums, products and powers as given', () => {
    expect(String(add(x, x))).toBe('2*x');
    expect(globalParameters.evaluate).toBe(true);
    const r = evaluate(false, () => {
      expect(globalParameters.evaluate).toBe(false);
      return [add(x, x), mul(2, add(x, 1)), pow(2, 2), add(x), add(), mul(x), mul()];
    });
    expect(r.map(String)).toEqual(['x + x', '2*(x + 1)', '2**2', 'x', '0', 'x', '1']);
    expect(r[0]).toBeInstanceOf(Add);
    expect(r[1]).toBeInstanceOf(Mul);
    expect(r[2]).toBeInstanceOf(Pow);
    expect(String(add(x, x))).toBe('2*x');
  });

  it('nests and restores the setting when the callback throws', () => {
    expect(evaluate(false, () => evaluate(true, () => String(add(x, x))))).toBe('2*x');
    expect(() =>
      evaluate(false, () => {
        throw new RangeError('boom');
      }),
    ).toThrow(RangeError);
    expect(globalParameters.evaluate).toBe(true);
  });
});
