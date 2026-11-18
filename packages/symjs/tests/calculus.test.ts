// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Concrete, O, S, Sum, Sym, dominant, getn, isAbsolutelyConvergent, isConvergent, parse } from '../src';
it('exposes calculus result wrappers', () => {
  const n = new Sym('n', { positive: true, integer: true });
  expect(String(dominant(parse('n**2 + n', { symbols: [n] }), n))).toBe('n**2');
  expect(String(getn(O(n)))).toBe('1');
  const sum = Sum(parse('1/n**2', { symbols: [n] }), [n, 1, S.Infinity]);
  if (!(sum instanceof Concrete)) throw new TypeError('unevaluated sum expected');
  expect(isConvergent(sum)).toBe(true);
  expect(isAbsolutelyConvergent(sum)).toBe(true);
});
