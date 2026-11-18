// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import * as sj from '../../src';

const x = new sj.Sym('x');
const expr = sj.parse;
it('handles degenerate Sylvester and Bezout matrices in either order', () => {
  for (const [f, g] of [[0, 0], [2, 3], [0, 3], [3, 0]] as const) {
    expect(sj.sylvester(f, g, x).rows).toBe(0);
    expect(sj.bezout(f, g, x).rows).toBe(0);
  }
  for (const [f, g] of [[x, 0], [0, x]] as const) {
    expect(String(sj.sylvester(f, g, x))).toBe('Matrix([[0]])');
    expect(String(sj.bezout(f, g, x))).toBe('Matrix([[0]])');
  }
  expect(sj.bezout(expr('x**2+1'), x, x).equals(sj.Matrix.of([[-1, 0], [0, 1]]))).toBe(true);
  expect(sj.sylvester(2, expr('x**2+1'), x, 2).det().equals(sj.sympify(-4))).toBe(true);
  expect(sj.sylvester(expr('x**2+1'), 2, x, 2).det().equals(sj.sympify(-4))).toBe(true);
});
it('preserves initial zero or constant pairs and swaps by degree', () => {
  for (const [f, g] of [[0, x], [x, 0], [1, 2], [x, 2], [2, x]] as const) {
    expect(sj.subresultantsSylv(f, g, x)).toHaveLength(2);
    expect(sj.modifiedSubresultantsSylv(f, g, x)).toHaveLength(2);
    expect(sj.euclidQ(f, g, x)).toHaveLength(2);
    expect(sj.sturmQ(f, g, x)).toHaveLength(2);
    expect(sj.sturmAmv(f, g, x)).toHaveLength(2);
  }
  expect(sj.euclidQ(expr('x+1'), expr('x**2-1'), x).map(String)).toEqual(['x**2 - 1', 'x + 1']);
  expect(sj.sturmQ(expr('x**2-1'), expr('x+1'), x).map(String)).toEqual(['x**2 - 1', 'x + 1']);
  expect(sj.remZ(expr('x**2+y'), expr('y*x+1'), x).equals(sj.Poly.from(expr('x**2+y'), [x]).prem(sj.Poly.from(expr('y*x+1'), [x])).asExpr())).toBe(true);
  expect(sj.backwardEye(3).mul(sj.backwardEye(3)).equals(sj.Matrix.eye(3))).toBe(true);
});
it('computes rational PRS without changing the signs of negative input', () => {
  expect(sj.euclidQ(expr('-x**2-1'), expr('-x'), x).map(String)).toEqual(['-x**2 - 1', '-x', '-1']);
  expect(sj.sturmQ(expr('-x**2-1'), expr('-x'), x).map(String)).toEqual(['-x**2 - 1', '-x', '1']);
});
it('reverses the Bezout coefficient order for PRS and exposes polynomial helpers', () => {
  const p = expr('x**3+2*x+1'), q = expr('3*x**2+1');
  const reverse = sj.backwardEye(3);
  expect(sj.bezout(p, q, x, 'prs').equals(reverse.mul(sj.bezout(p, q, x)).mul(reverse))).toBe(true);
  expect(sj.polyCoefficients(expr('x**2+1'), x)).toBeInstanceOf(Map);
  expect(sj.divExact(expr('x**2-1'), expr('x-1'), [x]).toString()).toBe('x + 1');
});
