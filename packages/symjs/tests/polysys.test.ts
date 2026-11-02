// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { factorSystem, parse, solvePolySystem, symbols } from '../src';

const [x, y] = symbols('x y');
const show = (sols: unknown[][]) => sols.map((s) => `(${s.map(String).join(', ')})`).join(', ');

describe('factorSystem (SymPy factor_system)', () => {
  it('splits a system into irreducible factor systems', () => {
    expect(factorSystem([parse('x**2 - 1'), parse('y - 1')]).map((s) => s.map(String))).toEqual([
      ['x + 1', 'y - 1'],
      ['x - 1', 'y - 1'],
    ]);
  });
  it('detects inconsistent and trivial systems', () => {
    expect(factorSystem([x, parse('1')])).toEqual([]);
    expect(factorSystem([parse('0')])).toEqual([[]]);
  });
});

describe('solvePolySystem (SymPy solve_poly_system)', () => {
  it('solves a zero-dimensional system with algebraic solutions', () => {
    expect(show(solvePolySystem([parse('x*y - 2*y'), parse('2*y**2 - x**2')], [x, y]))).toBe('(0, 0), (2, -sqrt(2)), (2, sqrt(2))');
  });
  it('keeps only rational solutions on request', () => {
    const [a, b, c] = symbols('a b c');
    const F = [parse('a**2 + b + c - 1'), parse('a + b**2 + c - 1'), parse('a + b + c**2 - 1')];
    expect(show(solvePolySystem(F, [a, b, c], { rationalOnly: true }))).toBe('(0, 0, 1), (0, 1, 0), (1, 0, 0)');
  });
});
