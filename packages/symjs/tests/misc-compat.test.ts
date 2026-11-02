// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { firstMotzkins, isMotzkin, motzkinNumbersInRange, parse, rewrite, series, symbols } from '../src';

const [x] = symbols('x');

describe('Motzkin numbers', () => {
  it('lists, ranges and membership', () => {
    expect(firstMotzkins(10).map(String)).toEqual(['1', '1', '2', '4', '9', '21', '51', '127', '323', '835']);
    expect(motzkinNumbersInRange(2n, 300n).map(String)).toEqual(['2', '4', '9', '21', '51', '127']);
    expect(isMotzkin(5n)).toBe(false);
    expect(isMotzkin(127n)).toBe(true);
  });
});

describe('rewrites and series of special functions', () => {
  it('frac in terms of floor', () => {
    expect(String(rewrite(parse('frac(x)'), 'floor'))).toBe('x - floor(x)');
  });
  it('series of sinc', () => {
    expect(String(series(parse('sinc(x)'), x))).toBe('1 - x**2/6 + x**4/120 + O(x**6)');
  });
});
