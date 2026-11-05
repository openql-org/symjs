// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference results from SymPy 1.14 (sympy.solvers.bivariate.bivariate_type).
import { expect, it } from 'vitest';
import { PolynomialError, isNoMatch, parseExpr, symbols } from '../../src';
import { bivariateType } from '../../src/solvers/bivariate';

const [x, y] = symbols('x y');
const bt = (src: string): string => {
  const r = bivariateType(parseExpr(src), x, y);
  return isNoMatch(r) ? 'None' : `(${r.map(String).join(', ')})`;
};

it('recognizes the composites x*y, a*x + b*y and a*x*y + b*y', () => {
  expect(bt('(x + y)**2 - 3')).toBe('(x + y, _u**2 - 3, _u)');
  expect(bt('x**2*y**2 + 2*x*y + 1')).toBe('(x*y, _u**2 + 2*_u + 1, _u)');
  expect(bt('(2*x + 3*y)**2 - 1')).toBe('(2*x + 3*y, _u**2 - 1, _u)');
  expect(bt('(x*y + y)**2 - 4')).toBe('(x*y + y, _u**2 - 4, _u)');
  expect(bt('(x*y + x)**2 - 4')).toBe('(x*y + x, _u**2 - 4, _u)');
  expect(bt('x + y')).toBe('(x + y, _u, _u)');
  expect(bt('x**3*y**3')).toBe('(x*y, _u**3, _u)');
  expect(bt('-2*x*y - 3*y + (2*x*y + 3*y)**2 + 1')).toBe('(2*x*y + 3*y, _u**2 - _u + 1, _u)');
});

it('returns NoMatch for other polynomials', () => {
  expect(bt('x**2 + y')).toBe('None');
  expect(bt('x**2 + y**2')).toBe('None');
  expect(bt('x**2')).toBe('None');
});

it('requires a polynomial in x and y', () => {
  expect(() => bivariateType(parseExpr('exp(x) + y'), x, y)).toThrow(PolynomialError);
});
