// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Poly, rootFactors, symbol, parseExpr, expand, mul } from '../../src';
const x = symbol('x');
it('returns root factors and preserves unresolved residual factors', () => {
  const f = parseExpr('x**2-y');
  const factors = rootFactors(f,x);
  expect(new Set(factors.map(String))).toEqual(new Set(['x - sqrt(y)','x + sqrt(y)']));
  expect(expand(mul(...factors)).equals(f)).toBe(true);
  expect(rootFactors(Poly.from(parseExpr('x**2-1'),[x])).every(p => p instanceof Poly)).toBe(true);
  expect(rootFactors(parseExpr('x**2-1'))).toHaveLength(2);
  expect(rootFactors(parseExpr('x**5-x+1'),x).map(String)).toEqual(['x**5 - x + 1']);
  const g = parseExpr('x*(x-1)*(x**5-x+1)');
  expect(expand(mul(...rootFactors(g,x))).equals(expand(g))).toBe(true);
  expect(() => rootFactors(parseExpr('x+y'))).toThrow(RangeError);
});
