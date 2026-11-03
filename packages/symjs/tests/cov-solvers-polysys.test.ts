// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { NotImplementedError, factorSystem, factorSystemCond, parse, solvePolySystem, symbols } from '../src';

const [x, y, z] = symbols('x y z');
const P = (ss: string[]) => ss.map((s) => parse(s));
const show = (r: unknown[][]) => `[${r.map((s) => `[${s.map(String).join(', ')}]`).join(', ')}]`;

// expected values from SymPy 1.14 sympy.solvers.polysys (None is [])
describe('factor_system', () => {
  it('factor_system_cond', () => {
    expect(show(factorSystemCond(P(['x*a - a', 'x**2 - 1'])))).toBe('[[x + 1, a], [x - 1]]');
    expect(show(factorSystemCond(P(['x*(x - 1)', '(x - 1)*y'])))).toBe('[[x, y], [x - 1]]');
    expect(show(factorSystemCond(P(['0', 'x - 1'])))).toBe('[[x - 1]]');
    expect(show(factorSystemCond(P(['0'])))).toBe('[[]]');
    expect(show(factorSystemCond(P(['1'])))).toBe('[]');
    expect(show(factorSystemCond(P(['a'])))).toBe('[[a]]');
    expect(show(factorSystemCond(P(['x*y', 'x']), [x]))).toBe('[[x]]');
    expect(show(factorSystemCond(P(['0']), [x]))).toBe('[[]]');
  });
  it('factor_system', () => {
    expect(show(factorSystem(P(['a*(x - 1)', 'x*(y - 2)']), [x, y]))).toBe('[[x - 1, x], [x - 1, y - 2]]');
    expect(show(factorSystem(P(['x**2 - 1', '(x - 1)*(y - 1)*(y + 1)'])))).toBe('[[x + 1, y + 1], [x + 1, y - 1], [x - 1]]');
    expect(show(factorSystem(P(['x - 1', '3'])))).toBe('[]');
  });
});

describe('solve_poly_system', () => {
  it('solutions', () => {
    expect(show(solvePolySystem(P(['x**2 - 2', 'x**3 - 2*x']), [x]))).toBe('[[-sqrt(2)], [sqrt(2)]]');
    expect(show(solvePolySystem(P(['x**2 - 1', 'x - 1', 'x + 1']), [x]))).toBe('[]');
    expect(show(solvePolySystem(P(['x*y - 1', 'x - y']), [x, y]))).toBe('[[-1, -1], [1, 1]]');
    expect(show(solvePolySystem(P(['x**2 + y**2 - 1', 'x - y']), [x, y]))).toBe('[[-sqrt(2)/2, -sqrt(2)/2], [sqrt(2)/2, sqrt(2)/2]]');
    expect(show(solvePolySystem(P(['x - 1', 'x - 2', 'y']), [x, y]))).toBe('[]');
    expect(show(solvePolySystem(P(['x**2 - 2', 'y**2 - x']), [x, y]))).toBe('[[-sqrt(2), -2**(1/4)*I], [-sqrt(2), 2**(1/4)*I], [sqrt(2), -2**(1/4)], [sqrt(2), 2**(1/4)]]');
    expect(show(solvePolySystem(P(['x - sqrt(2)', 'y**2 - x']), [x, y]))).toBe('[[sqrt(2), -2**(1/4)], [sqrt(2), 2**(1/4)]]');
    expect(show(solvePolySystem(P(['x + sqrt(2)*y - 1', 'y**2 - 2']), [x, y]))).toBe('[[-1, sqrt(2)], [3, -sqrt(2)]]');
    expect(show(solvePolySystem(P(['y**2 - sqrt(3)*y', 'x - y']), [x, y]))).toBe('[[0, 0], [sqrt(3), sqrt(3)]]');
  });
  it('algebraic coefficients', () => {
    expect(show(solvePolySystem(P(['x**2 - 2', 'y - sqrt(2)']), [x, y]))).toBe('[[-sqrt(2), sqrt(2)], [sqrt(2), sqrt(2)]]');
    expect(show(solvePolySystem(P(['x - sqrt(2)', 'y**2 - 2', 'x*y - 2']), [x, y]))).toBe('[[sqrt(2), sqrt(2)]]');
    expect(show(solvePolySystem(P(['y - sqrt(2)*x', 'x**2 - 1', 'z - 1']), [x, y, z]))).toBe('[[-1, -sqrt(2), 1], [1, sqrt(2), 1]]');
    expect(show(solvePolySystem(P(['x - y', 'y - z', 'z**2 - sqrt(3)']), [x, y, z]))).toBe('[[-3**(1/4), -3**(1/4), -3**(1/4)], [3**(1/4), 3**(1/4), 3**(1/4)]]');
  });
  it('not zero-dimensional', () => {
    expect(() => solvePolySystem(P(['x**2 - 1']), [x, y])).toThrow(NotImplementedError);
    expect(() => solvePolySystem(P(['x*y', 'x*z']), [x, y, z])).toThrow(NotImplementedError);
  });
});
