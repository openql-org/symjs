// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { Integral, S, expand, symbol } from '../../src/core';

it('distributes finite numeric integrals in the standalone core entry', () => {
  const x = symbol('x');
  const integrand = x.add(1);
  const definite = new Integral([integrand, x, S.Zero, S.One]);
  expect(String(expand(definite))).toBe('Integral(1, (x, 0, 1)) + Integral(x, (x, 0, 1))');
  const improper = new Integral([integrand, x, S.Zero, S.Infinity]);
  expect(expand(improper).equals(improper)).toBe(true);
});
