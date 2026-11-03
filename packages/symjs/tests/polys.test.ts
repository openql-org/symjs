// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys.ts.
// The polys entry: deprecated functions. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { NoMatch, parse, sstr, symbol } from '../src';
import { divExact, polyCoefficients } from '../src/polys';

describe('divExact (deprecated)', () => {
  it('divides exactly or gives NoMatch', () => {
    const x = symbol('x');
    // SymPy exquo(x**2 - 1, x - 1) = x + 1; exquo(x**2 + 1, x - 1) raises ExactQuotientFailed
    expect(String(divExact(parse('x**2 - 1'), parse('x - 1'), [x]))).toBe('x + 1');
    expect(divExact(parse('x**2 + 1'), parse('x - 1'), [x])).toBe(NoMatch);
  });
});

describe('polyCoefficients (deprecated)', () => {
  it('maps degrees to coefficients or gives NoMatch', () => {
    const x = symbol('x');
    // SymPy Poly(x**2 + 2*x, x).as_dict() = {(2,): 1, (1,): 2}
    const c = polyCoefficients(parse('x**2 + 2*x'), x);
    expect(c instanceof Map ? [...c].map(([k, v]) => [k, sstr(v)]).sort((a, b) => Number(a[0]) - Number(b[0])) : c).toEqual([
      [1, '2'],
      [2, '1'],
    ]);
    expect(polyCoefficients(parse('sin(x)'), x)).toBe(NoMatch);
  });
});
