// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { kernS } from '../../src';

it('kernS simplifies arithmetic without distributing numeric coefficients into sums', () => {
  expect(String(kernS('2*(x + y)'))).toBe('2*(x + y)');
  expect(String(kernS('-(x + 1)'))).toBe('-(x + 1)');
  expect(String(kernS('x + x'))).toBe('2*x');
  expect(String(kernS('0.5*(x + y)'))).toBe('0.5*(x + y)');
  expect(String(kernS('x*(x+y)'))).toBe('x*(x + y)');
  expect(String(kernS('2*x'))).toBe('2*x');
  expect(String(kernS('2*x*y'))).toBe('2*x*y');
  expect(() => kernS('x + (')).toThrow(SyntaxError);
});
