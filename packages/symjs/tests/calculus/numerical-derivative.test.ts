// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { exp, meijerg, parse, symbol, testDerivativeNumerically } from '../../src';

it('checks derivatives independently at complex sample points', () => {
  const z = symbol('z');
  expect(testDerivativeNumerically(parse('z**3 + sin(z)'), z)).toBe(true);
  expect(testDerivativeNumerically(exp(z), z, 1e-6, -2, 1, -1, 2)).toBe(true);
  expect(testDerivativeNumerically(parse('z**2'), z, 1e-6, 0, 0, 0, 0)).toBe(true);
  expect(testDerivativeNumerically(exp(z), z, Number.MIN_VALUE)).toBe(false);
  expect(testDerivativeNumerically(meijerg([], [], [0], [], z), z)).toBe(true);
});

it('validates tolerance and the sampling rectangle', () => {
  const z = symbol('z');
  for (const tol of [0, -1, Infinity, NaN]) expect(() => testDerivativeNumerically(z, z, tol)).toThrow(RangeError);
  for (const bounds of [[Infinity, 0, 1, 1], [0, NaN, 1, 1], [0, 0, -Infinity, 1], [0, 0, 1, NaN]]) {
    expect(() => testDerivativeNumerically(z, z, 1e-6, ...bounds)).toThrow(RangeError);
  }
});
