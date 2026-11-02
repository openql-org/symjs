// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Poly, evalf, factor, parse, rootOf, solve, symbols } from '../src';

const [x] = symbols('x');
const P = (s: string) => Poly.from(parse(s), [x]);

// expected values from SymPy 1.14
describe('factorization over ZZ (Zassenhaus)', () => {
  it('splits polynomials without rational roots', () => {
    expect(String(factor(parse('x**5 + x + 1')))).toBe('(x**2 + x + 1)*(x**3 - x**2 + 1)');
    expect(String(factor(parse('x**4 + 4')))).toBe('(x**2 - 2*x + 2)*(x**2 + 2*x + 2)');
    expect(String(factor(parse('x**8 - 1')))).toBe('(x - 1)*(x + 1)*(x**2 + 1)*(x**4 + 1)');
    expect(String(factor(parse('6*x**4 - 5*x**3 + 7*x**2 - 5*x + 1')))).toBe('(2*x - 1)*(3*x - 1)*(x**2 + 1)');
    expect(String(factor(parse('x**4 - 10*x**2 + 1')))).toBe('x**4 - 10*x**2 + 1');
  });
});

describe('CRootOf', () => {
  it('all_roots and real_roots order', () => {
    expect(P('x**5 + x + 1').allRoots().map(String)).toEqual([
      'CRootOf(x**3 - x**2 + 1, 0)',
      '-1/2 - sqrt(3)*I/2',
      '-1/2 + sqrt(3)*I/2',
      'CRootOf(x**3 - x**2 + 1, 1)',
      'CRootOf(x**3 - x**2 + 1, 2)',
    ]);
    expect(P('(x**2 - 2)*(x**3 + x + 1)').realRoots().map(String)).toEqual(['-sqrt(2)', 'CRootOf(x**3 + x + 1, 0)', 'sqrt(2)']);
  });
  it('numeric values', () => {
    expect(String(evalf(rootOf(parse('x**3 + x + 1'), 0), 30))).toBe('-0.682327803828019327369483739711');
    expect(String(evalf(rootOf(parse('x**3 + x + 1'), 1)))).toBe('0.34116390191401 - 1.16154139999725*I');
  });
  it('solve falls back to CRootOf', () => {
    expect(solve(parse('x**5 - x - 1'), x).map(String)).toEqual([0, 1, 2, 3, 4].map((i) => `CRootOf(x**5 - x - 1, ${i})`));
    expect(solve(parse('x**3 - x + 1'), x, { cubics: false }).map(String)).toEqual([0, 1, 2].map((i) => `CRootOf(x**3 - x + 1, ${i})`));
  });
});
