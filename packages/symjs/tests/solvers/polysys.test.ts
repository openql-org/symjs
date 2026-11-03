// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/polysys.ts: polynomial systems (solve_poly_system, factor_system); expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { factorSystem, factorSystemCond, NotImplementedError, parse, solvePolySystem, symbols } from '../../src';

const [x, y, z] = symbols('x y z');
const P = (ss: string[]) => ss.map((s) => parse(s));
const show = (r: unknown[][]) => `[${r.map((s) => `[${s.map(String).join(', ')}]`).join(', ')}]`;
const show2 = (sols: unknown[][]) => sols.map((s) => `(${s.map(String).join(', ')})`).join(', ');

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

// expected values from SymPy 1.14 sympy.solvers.polysys
describe('factor_system ordering (SymPy _sort_systems on the dense representation)', () => {
  it('orders systems by degree lists, then by the nested dense coefficient lists', () => {
    expect(show(factorSystem(P(['x*(x-1)', 'y*(y-1)'])))).toBe('[[x - 1, y], [x - 1, y - 1], [x, y], [x, y - 1]]');
    expect(show(factorSystem(P(['(x-3)*(x-2)'])))).toBe('[[x - 2], [x - 3]]');
    expect(show(factorSystem(P(['(x-2)*(x-3)*(x+5)'])))).toBe('[[x + 5], [x - 2], [x - 3]]');
    expect(show(factorSystem(P(['(x-y)*(x+y)'])))).toBe('[[x + y], [x - y]]');
  });
  it('three generators (zero coefficients at an inner level) and systems of different lengths', () => {
    expect(show(factorSystem(P(['x*(x-1)*(x**2+z)', 'y*(y-1)*(y**2+x*z+z)'])))).toBe(
      '[[x**2 + z, x*z + y**2 + z], [x**2 + z, y - 1], [x**2 + z, y], [x*z + y**2 + z, x - 1], [x*z + y**2 + z, x], [x - 1, y - 1], [x - 1, y], [x, y - 1], [x, y]]',
    );
    expect(show(factorSystem(P(['(x**2+z)*(x**2+2*z)', '(y**2 + y + 1)*(y**2 + 2)*(x-1)'])))).toBe(
      '[[x**2 + 2*z, x - 1], [x**2 + z, x - 1], [x**2 + 2*z, y**2 + y + 1], [x**2 + 2*z, y**2 + 2], [x**2 + z, y**2 + y + 1], [x**2 + z, y**2 + 2]]',
    );
    expect(show(factorSystem(P(['(x-1)*(x-2)', '(x-1)*(y-2)', 'x*y*z'])))).toBe(
      '[[x - 2, x, y - 2], [x - 1, x], [x - 2, y - 2, y], [x - 2, y - 2, z], [x - 1, y], [x - 1, z]]',
    );
  });
  it('coefficients: numbers, and polynomials in the parameters (SymPy PolyElement order)', () => {
    expect(show(factorSystem(P(['x*y - sqrt(2)', 'x*y - sqrt(3)'])))).toBe('[[x*y - sqrt(2), x*y - sqrt(3)]]');
    expect(show(factorSystem(P(['x*y - sqrt(3)', 'x*y - 2'])))).toBe('[[x*y - sqrt(3), x*y - 2]]');
    expect(show(factorSystem(P(['x*y - I', 'x*y - 2*I'])))).toBe('[[x*y - I, x*y - 2*I]]');
    expect(show(factorSystem(P(['(x-a)*(x-b)']), [x]))).toBe('[[-a + x], [-b + x]]');
    expect(show(factorSystem(P(['(x-b)*(x-a)']), [x]))).toBe('[[-a + x], [-b + x]]');
    expect(show(factorSystem(P(['(x-a)*(x-2*a)']), [x]))).toBe('[[-a + x], [-2*a + x]]');
    expect(show(factorSystem(P(['(x-a)*(x-a**2)']), [x]))).toBe('[[-a**2 + x], [-a + x]]');
    expect(show(factorSystem(P(['(x-a)*(x+a)']), [x]))).toBe('[[a + x], [-a + x]]');
    expect(show(factorSystem(P(['(x-2)*(x+a)']), [x]))).toBe('[[a + x], [x - 2]]');
    expect(show(factorSystem(P(['(x-a*b)*(x-a-b)*(x-1)*(x-b**2)*x']), [x]))).toBe('[[-a - b + x], [-a*b + x], [-b**2 + x], [x - 1], [x]]');
    expect(show(factorSystem(P(['(x - a)*(y-1)', '(x-1)*(y-b)']), [x, y]))).toBe('[[-a + x, x - 1], [-a + x, -b + y], [x - 1, y - 1], [-b + y, y - 1]]');
    expect(show(factorSystemCond(P(['(x - a)*(y-1)', '(x-1)*(y-b)*a']), [x, y]))).toBe(
      '[[-a + x, x - 1], [-a + x, -b + y], [x - 1, y - 1], [-a + x, a], [-b + y, y - 1], [y - 1, a]]',
    );
  });
});

describe('solve_poly_system', () => {
  it('a substituted root that makes an equation a nonzero constant is dropped', () => {
    expect(show(solvePolySystem(P(['x*y-1', 'y**2-y']), [x, y]))).toBe('[[1, 1]]');
  });
  it('positive-dimensional systems raise NotImplementedError', () => {
    // a single polynomial in the last generator
    expect(() => solvePolySystem(P(['y**2-1']), [x, y])).toThrow(NotImplementedError);
    // y = 1 leaves x free
    expect(() => solvePolySystem(P(['x*(y-1)', 'y*(y-1)']), [x, y])).toThrow(NotImplementedError);
    expect(() => solvePolySystem(P(['y-1', 'z**2-1']), [x, y, z])).toThrow(NotImplementedError);
    expect(() => solvePolySystem(P(['y-sqrt(2)']), [x, y])).toThrow(NotImplementedError);
    // SymPy returns [] for solve_poly_system([0], x), but every x solves 0 = 0
    expect(() => solvePolySystem(P(['0']), [x])).toThrow(NotImplementedError);
  });
  it('algebraic coefficients', () => {
    expect(show(solvePolySystem(P(['x-sqrt(2)*y', 'y**2-2']), [x, y]))).toBe('[[-2, -sqrt(2)], [2, sqrt(2)]]');
    expect(show(solvePolySystem(P(['x**2+y-1', 'y+sqrt(2)']), [x, y]))).toBe('[[-sqrt(1 + sqrt(2)), -sqrt(2)], [sqrt(1 + sqrt(2)), -sqrt(2)]]');
    expect(show(solvePolySystem(P(['x-sqrt(2)', 'y-sqrt(2)']), [x, y]))).toBe('[[sqrt(2), sqrt(2)]]');
    // inconsistent: y = sqrt(3) turns the last equation into 1 = 0 (SymPy: None, no solution)
    expect(show(solvePolySystem(P(['y - sqrt(3)', 'x - sqrt(2)', '(y-sqrt(3))*x + 1']), [x, y]))).toBe('[]');
    // SymPy: [(0, 0)] from a Groebner basis over QQ<sqrt(2)>; the back substitution here needs an
    // equation in one generator alone
    expect(() => solvePolySystem(P(['x-sqrt(2)*y', 'x*y']), [x, y])).toThrow(NotImplementedError);
    // SymPy: None (no solution, sqrt(2)*x*y = sqrt(3)*x*y = 1 is inconsistent); not decided here
    expect(() => solvePolySystem(P(['sqrt(2)*x*y-1', 'sqrt(3)*x*y-1']), [x, y])).toThrow(NotImplementedError);
  });
  it('rationalOnly keeps rational roots only', () => {
    expect(show(solvePolySystem(P(['x**2-2', 'y**2-3']), [x, y], { rationalOnly: true }))).toBe('[]');
    expect(show(solvePolySystem(P(['x**2-2', 'y-1']), [x, y], { rationalOnly: true }))).toBe('[]');
    expect(show(solvePolySystem(P(['x**2-1', 'y-sqrt(2)']), [x, y], { rationalOnly: true }))).toBe('[]');
    expect(show(solvePolySystem(P(['x**2-1', 'y-1']), [x, y], { rationalOnly: true }))).toBe('[[-1, 1], [1, 1]]');
  });
});

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
    expect(show2(solvePolySystem([parse('x*y - 2*y'), parse('2*y**2 - x**2')], [x, y]))).toBe('(0, 0), (2, -sqrt(2)), (2, sqrt(2))');
  });
  it('keeps only rational solutions on request', () => {
    const [a, b, c] = symbols('a b c');
    const F = [parse('a**2 + b + c - 1'), parse('a + b**2 + c - 1'), parse('a + b + c**2 - 1')];
    expect(show2(solvePolySystem(F, [a, b, c], { rationalOnly: true }))).toBe('(0, 0, 1), (0, 1, 0), (1, 0, 0)');
  });
});
