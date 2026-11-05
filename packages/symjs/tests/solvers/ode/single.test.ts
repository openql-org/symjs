// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference results from SymPy 1.14 (sympy/solvers/ode/single.py doctests and the objects run in SymPy).
import { describe, expect, it } from 'vitest';
import type { UndefFn } from '../../../src';
import { SymFunction, dsolve, isNoMatch, parseExpr, Sym, Eq, S } from '../../../src';
import { NthAlgebraic, ODEMatchError, SingleODEProblem, nthAlgebraicSolutions } from '../../../src/solvers/ode/single';

const x = new Sym('x');
const fx = SymFunction('f')(x) as UndefFn;
const e = (src: string) => parseExpr(src);

describe('SingleODEProblem', () => {
  it('gives the properties of the equation', () => {
    const p = new SingleODEProblem(e('x*Derivative(f(x), (x, 2)) + f(x)*sin(x)'), fx, x);
    expect(p.order).toBe(2);
    expect(String(p.eqExpanded)).toBe('x*Derivative(f(x), (x, 2)) + f(x)*sin(x)');
    expect(p.isAutonomous).toBe(false);
    expect(new SingleODEProblem(e('Derivative(f(x), x) + f(x)'), fx, x).isAutonomous).toBe(true);
    expect(p.getNumberedConstants(2).map(String)).toEqual(['C1', 'C2']);
    expect(new SingleODEProblem(e('C1*Derivative(f(x), x)'), fx, x).getNumberedConstants(2).map(String)).toEqual(['C2', 'C3']);
  });

  it('gives the linear coefficients (get_linear_coefficients)', () => {
    const eq = e('Derivative(f(x), (x, 3)) + 2*Derivative(f(x), x) + x*Derivative(f(x), (x, 2)) + cos(x)*Derivative(f(x), x) + x - f(x) - sin(x)');
    const r = new SingleODEProblem(eq, fx, x).getLinearCoefficients(eq, fx, 3);
    expect(isNoMatch(r) ? 'None' : [...r].map(([k, v]) => `${k}: ${String(v)}`).join(', ')).toBe('0: -1, 1: cos(x) + 2, 2: x, 3: 1, -1: x - sin(x)');
    const eq2 = e('Derivative(f(x), (x, 3)) + x - sin(f(x))');
    expect(isNoMatch(new SingleODEProblem(eq2, fx, x).getLinearCoefficients(eq2, fx, 3))).toBe(true);
  });
});

describe('NthAlgebraic', () => {
  const general = (src: string): string => String(new NthAlgebraic(new SingleODEProblem(e(src), fx, x)).getGeneralSolution());
  it('solves with differentiation as an invertible function', () => {
    expect(general('Derivative(f(x), (x, 2))')).toBe('Eq(f(x), _C*x + _C)');
    expect(general('f(x)**2*(Derivative(f(x), x) - 1)')).toBe('Eq(f(x), 0),Eq(f(x), _C + x)');
    const s = new NthAlgebraic(new SingleODEProblem(e('2*Derivative(f(x), (x, 2))'), fx, x));
    expect(s.hint).toBe('nth_algebraic');
    expect(s.hasIntegral).toBe(true);
    expect(String(s.getGeneralSolution({ simplify: false }))).toBe('Eq(f(x), _C*x + _C)');
  });
  it('does not match other equations', () => {
    expect(() => new NthAlgebraic(new SingleODEProblem(e('Derivative(f(x), x) + f(x)'), fx, x)).getGeneralSolution()).toThrow(ODEMatchError);
    expect(nthAlgebraicSolutions(e('Derivative(f(x), x) + f(x)'), fx, x)).toBeUndefined();
    // solve fails on this factor
    expect(nthAlgebraicSolutions(e('Derivative(f(x), x) + exp(Derivative(f(x), x))*Derivative(f(x), x)**x'), fx, x)).toBeUndefined();
  });
  it('is the nth_algebraic hint of dsolve', () => {
    expect(String(dsolve(Eq(e('f(x)*(Derivative(f(x), x)**2 - 1)'), S.Zero), fx, { hint: 'nth_algebraic' }))).toBe('Eq(f(x), 0),Eq(f(x), C1 - x),Eq(f(x), C1 + x)');
    expect(String(dsolve(e('f(x)**2*(Derivative(f(x), x) - 1)'), fx, { hint: 'nth_algebraic' }))).toBe('Eq(f(x), 0),Eq(f(x), C1 + x)');
  });
});
