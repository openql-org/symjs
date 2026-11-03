// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/nroots.ts: numerical roots of polynomials; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const { parse } = sj;
const [x] = sj.symbols('x') as [sj.Sym];
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('nroots', () => {
  it.each([
    ['x**3 - x', '[-1.00000000000000, 0, 1.00000000000000]'],
    ['x**2 + 1', '[-1.0*I, 1.0*I]'],
    ['I*x - 1', '[-1.0*I]'],
    ['x**2 - sqrt(2)', '[-1.18920711500272, 1.18920711500272]'],
    ['sqrt(2)*x**2 - 1', '[-0.840896415253715, 0.840896415253715]'],
    ['x**2', '[0, 0]'],
    ['(x - 1)**2*(x + 2)', '[-2.00000000000000, 1.00000000000000, 1.00000000000000]'],
    [
      'x**4 + 1',
      '[-0.707106781186548 - 0.707106781186548*I, -0.707106781186548 + 0.707106781186548*I, 0.707106781186548 - 0.707106781186548*I, 0.707106781186548 + 0.707106781186548*I]',
    ],
  ])('nroots(%s)', (f, expected) => {
    expect(show(sj.nroots(parse(f)))).toBe(expected);
  });
  it('a Poly, a generator and symbolic coefficients', () => {
    expect(show(sj.nroots(sj.Poly.from(parse('x**2 - 2'), [x]), 10))).toBe('[-1.414213562, 1.414213562]');
    expect(show(sj.nroots(parse('x**2 - 2'), 10, x))).toBe('[-1.414213562, 1.414213562]');
    // SymPy: MultivariatePolynomialError Cannot compute numerical roots of Poly(x**2 - a, x, a, domain='ZZ')
    expect(() => sj.nroots(parse('x**2 - a'), 15, x)).toThrow(sj.DomainError);
  });
});
