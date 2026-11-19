// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { Concrete } from '../../src/core/concrete';
import { Integral, S, expand, sin, symbol } from '../../src/core';

it('distributes finite numeric integrals in the standalone core entry', () => {
  const x = symbol('x');
  const integrand = x.add(1);
  const definite = new Integral([integrand, x, S.Zero, S.One]);
  expect(String(expand(definite))).toBe('Integral(1, (x, 0, 1)) + Integral(x, (x, 0, 1))');
  expect(String(expand(sin(definite)))).toBe('sin(Integral(1, (x, 0, 1)) + Integral(x, (x, 0, 1)))');
  const improper = new Integral([integrand, x, S.Zero, S.Infinity]);
  expect(expand(improper).equals(improper)).toBe(true);
  expect(expand(sin(improper))).toEqual(sin(improper));
  expect(String(expand(sin(improper), { force: true }))).toBe('sin(Integral(1, (x, 0, oo)) + Integral(x, (x, 0, oo)))');
});

it('keeps noncommuting integrands and handles symbolic and indefinite bounds', () => {
  const x = symbol('x');
  const a = symbol('a', { commutative: false });
  const b = symbol('b', { finite: false });
  const noncommutative = sin(new Integral([a.add(x), x, S.Zero, S.One]));
  expect(expand(noncommutative)).toEqual(noncommutative);
  const symbolic = new Integral([x.add(1), x, b, S.One]);
  expect(expand(symbolic)).toEqual(symbolic);
  expect(String(expand(new Integral([x.add(1), x])))).toBe('Integral(1, x) + Integral(x, x)');
});

it('distributes a sum with explicit finite bounds in the standalone core entry', () => {
  const k = symbol('k');
  const s = new Concrete('Sum', [k.add(1), k, S.Zero, S.One]);
  expect(String(expand(s))).toBe('Sum(1, (k, 0, 1)) + Sum(k, (k, 0, 1))');
});
