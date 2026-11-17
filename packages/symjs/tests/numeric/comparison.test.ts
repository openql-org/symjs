// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { epsilonEq, float, symbol } from '../../src';

it('compares absolute errors strictly without discarding float precision', () => {
  expect(epsilonEq(float('0.5'), float('0.5000000000000001'))).toBe(true);
  expect(epsilonEq(1000000, 1000001, 0.001)).toBe(false);
  expect(epsilonEq(1, 1.5, 0.5)).toBe(false);
  expect(epsilonEq(1, 1.5, 0.6)).toBe(true);
  expect(epsilonEq(1, 1, 0)).toBe(false);
  expect(epsilonEq(float('0.123456789012345678901', 25), float('0.123456789012345678902', 25), float('1e-22', 25))).toBe(false);
  expect(epsilonEq(symbol('x'), 1)).toBe('unknown');
});
