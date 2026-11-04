// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/solvehelp.ts: the equation systems of the geometry
// module (SymPy solve(eqs, syms, dict=True) as sympy/geometry calls it).

import { describe, expect, it } from 'vitest';
import { NotImplementedError, Sym, parse } from '../../src';
import { isNonRealNumber, solveEquations } from '../../src/geometry/solvehelp';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : String(e));

describe('solveEquations', () => {
  const [x, y] = [new Sym('x', { real: true }), new Sym('y', { real: true })];
  const p = (t: string) => parse(t).subs(new Sym('x'), x).subs(new Sym('y'), y);

  it('one unknown', () => {
    expect(s(solveEquations([], [x]))).toBe('[[x]]');
    expect(s(solveEquations([parse('0')], [x]))).toBe('[[x]]');
    expect(s(solveEquations([p('x - 1'), p('2*x - 2')], [x]))).toBe('[[1]]');
    expect(s(solveEquations([p('x - 1'), p('x - 2')], [x]))).toBe('[]');
    expect(s(solveEquations([p('x - 1'), parse('3')], [x]))).toBe('[]');
    // the first equation that solve can handle gives the candidates
    expect(s(solveEquations([p('x + exp(x) + cos(x)'), p('x**2 - 1')], [x]))).toBe('[]');
    expect(() => solveEquations([p('x + exp(x) + cos(x)')], [x])).toThrow(NotImplementedError);
    // a root that makes a denominator vanish is not a solution
    expect(s(solveEquations([p('(x**2 - x)/x')], [x]))).toBe('[[1]]');
    // a real unknown takes no complex value
    expect(s(solveEquations([p('x**2 + 1')], [x]))).toBe('[]');
  });

  it('two unknowns', () => {
    expect(s(solveEquations([p('x + y - 2'), p('x - y')], [x, y]))).toBe('[[1, 1]]');
    expect(s(solveEquations([p('x**2 + y**2 - 2'), p('x - y')], [x, y]))).toBe('[[-1, -1], [1, 1]]');
    expect(s(solveEquations([p('x*exp(y) - 1'), p('y')], [x, y]))).toBe('[[1, 0]]');
    // infinitely many solutions
    expect(s(solveEquations([p('x - y'), p('2*x - 2*y')], [x, y]))).toBe('[[y, y]]');
    expect(s(solveEquations([p('x - y'), p('2*x - 2*y'), p('3*x - 3*y')], [x, y]))).toBe('[[y, y]]');
    // an irreducible quartic eliminant without a real solution (two ellipses that do not meet)
    expect(s(solveEquations([p('x**2/25 + y**2/289 - 1'), p('(x - 4)**2*1000000/998001 + 25*y**2 - 1')], [x, y]))).toBe('[]');
    // an irreducible quartic eliminant with real roots: SymPy gives the four points in radicals, symjs's
    // roots does not solve the quartic
    expect(() => solveEquations([p('x**2/4 + y**2 - 1'), p('(x - 1/2)**2 + y**2/4 - 1')], [x, y])).toThrow(NotImplementedError);
  });

  it('non-real numbers', () => {
    expect(isNonRealNumber(parse('1 + I'))).toBe(true);
    expect(isNonRealNumber(parse('2'))).toBe(false);
    expect(isNonRealNumber(parse('sqrt(1 - pi)'))).toBe(true);
    expect(isNonRealNumber(parse('f(1)'))).toBe(false);
  });
});
