// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Concrete, dominant, getn, isAbsolutelyConvergent, isConvergent, NoMatch, O, oo, parse, S, Sum, Sym, symbols } from '../src';
it('exposes calculus result wrappers', () => {
  const n = new Sym('n', { positive: true, integer: true });
  expect(String(dominant(parse('n**2 + n', { symbols: [n] }), n))).toBe('n**2');
  expect(String(getn(O(n)))).toBe('1');
  const sum = Sum(parse('1/n**2', { symbols: [n] }), [n, 1, S.Infinity]);
  if (!(sum instanceof Concrete)) throw new TypeError('unevaluated sum expected');
  expect(isConvergent(sum)).toBe(true);
  expect(isAbsolutelyConvergent(sum)).toBe(true);
});

it('exposes calculus queries with public result types', () => {
  const [n] = symbols('n');
  expect(String(dominant(parse('n**2 + n'), n))).toBe('n**2');
  expect(dominant(parse('n + (-1)**n*n'), n)).toBe(NoMatch);
  expect(String(getn(O(n)))).toBe('1');
  expect(getn(n)).toBe(NoMatch);
  const sum = Sum(parse('1/n**2'), [n, 1, oo]);
  if (!(sum instanceof Concrete)) throw new TypeError('Sum');
  expect(isConvergent(sum)).toBe(true);
  expect(isAbsolutelyConvergent(sum)).toBe(true);
});
