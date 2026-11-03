// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/odesimp.ts: odesimp and constantsimp; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { parse, symbols, SymFunction as Fn } from '../../src';
import { InvariantError } from '../../src/core/errors';
import { Integral, Rational, type UndefFn } from '../../src/core/nodes';
import { add } from '../../src/core/ops';
import { constantsimp, odesimp } from '../../src/solvers/odesimp';

const [x, y, C1, C2, C3] = symbols('x y C1 C2 C3');
const s = (e: unknown): string => String(e);
const cs = (e: string, ...c: typeof C1[]) => String(constantsimp(parse(e), c));
const f = Fn('f');
const fx = f(x) as UndefFn;
const ode = parse('Eq(Derivative(f(x), x), f(x)/x)');
const simp = (e: string, hint = 'separable') => odesimp(ode, parse(e), fx, hint).map(String).join(', ');

describe('Mul substitution (SymPy Mul._eval_subs)', () => {
  it('simplifies constants of ODE solutions', () => {
    expect(s(constantsimp(sj.Eq(sj.mul(C1, C2, x), sj.mul(2, y)), [C1, C2]))).toBe('Eq(x, C1*y)');
  });
});

// expected values from SymPy 1.14 sympy.solvers.ode.ode.constantsimp
describe('constantsimp', () => {
  it('absorbs constant subexpressions', () => {
    expect(cs('C1*x', C1)).toBe('C1*x');
    expect(cs('C1 + x + 2', C1)).toBe('C1 + x');
    expect(cs('C1*C2 + C2 + C3*x + 2', C1, C2, C3)).toBe('C1 + C3*x');
    expect(cs('exp(C1 + x)', C1)).toBe('C1*exp(x)');
    expect(String(constantsimp(add(x, new Integral([C1, y, Rational.of(0), Rational.of(1)])), [C1]))).toBe('C1 + x');
    expect(cs('x + Integral(C1, y)', C1)).toBe('x + Integral(C1, y)');
    expect(cs('x + 2', C1)).toBe('x + 2');
  });
  it('removes linear redundancies', () => {
    expect(cs('C1*sin(x) + C2*sin(x) + C3*cos(x)', C1, C2, C3)).toBe('C1*sin(x) + C3*cos(x)');
  });
  it('factors terms unless exp would be both outside and inside a sum', () => {
    expect(cs('(C1 + exp(x))*exp(x)', C1)).toBe('(C1 + exp(x))*exp(x)');
    expect(cs('(C1*exp(x) + x)*exp(x)', C1)).toBe('(C1*exp(x) + x)*exp(x)');
    expect(cs('C1*(exp(x) + 1)*exp(x)', C1)).toBe('C1*(exp(x) + 1)*exp(x)');
    expect(cs('(C1 + C2*exp(x))*exp(2*x)', C1, C2)).toBe('(C1 + C2*exp(x))*exp(2*x)');
    expect(cs('(C1 + x)*exp(x) + exp(x)*sin(x)', C1)).toBe('(C1 + x + sin(x))*exp(x)');
  });
  it('normalizes equations', () => {
    expect(cs('Eq(C1, x)', C1)).toBe('Eq(x, C1)');
    expect(cs('Eq(C1*x, x**2)', C1)).toBe('Eq(C1*x, x**2)');
    expect(cs('Eq(C1 + x, C2 + x**2)', C1, C2)).toBe('Eq(x*(1 - x), C1)');
    expect(cs('Eq(C1*x*y, 2)', C1)).toBe('Eq(C1*x*y, 2)');
  });
});

// expected values from SymPy 1.14 sympy.solvers.ode.ode (constantsimp, odesimp)
describe('constantsimp', () => {
  it('a definite integral without free symbols is a constant subexpression without constants', () => {
    expect(String(constantsimp(add(x, new Integral([y, y, Rational.of(0), Rational.of(1)])), [C1]))).toBe('x + Integral(y, (y, 0, 1))');
  });
  it('constants in any order', () => {
    expect(cs('C3*sin(x) + C2*sin(x) + C1*cos(x) + exp(x)', C1, C2, C3)).toBe('C1*cos(x) + C2*sin(x) + exp(x)');
    expect(cs('Eq(f(x), C3*C2 + C1*C2 + x)', C1, C2, C3)).toBe('Eq(f(x), C1 + x)');
    expect(cs('Eq(f(x), exp(C3 + C1)*x + C2)', C1, C2, C3)).toBe('Eq(f(x), C1*x + C2)');
  });
});

describe('odesimp', () => {
  it('f(x) on the right-hand side', () => {
    // SymPy 1.14 raises AttributeError here (it wraps the swapped equation in a list
    // before testing eq.lhs); the solution is f(x) = C1 + x
    expect(simp('Eq(x + C1, f(x))')).toBe('Eq(f(x), C1 + x)');
  });
  it('solutions with powers of a negated sum', () => {
    expect(simp('Eq(1/f(x), (-x-C1)**2)')).toBe('Eq(f(x), 1/(C1**2 - 2*C1*x + x**2))');
    expect(simp('Eq(1/f(x), -(-x-C1)**3)')).toBe('Eq(f(x), -1/(C1**3 - 3*C1**2*x + 3*C1*x**2 - x**3))');
    expect(simp('Eq(sqrt(f(x)), 1/(-x-C1))')).toBe('Eq(f(x), 1/(C1**2 - 2*C1*x + x**2))');
    // an even power of a negated sum without constants
    const odeY = parse('Eq(Derivative(f(x), x), y*f(x)/x)');
    expect(odesimp(odeY, parse('Eq(1/f(x), (-x-y)**2)'), fx, 'separable').map(String)).toEqual(['Eq(f(x), 1/(x**2 + 2*x*y + y**2))']);
  });
  it('1st_homogeneous_coeff hints: log(u) = 0 becomes u/C1 = C1', () => {
    // SymPy: Eq(x*(f(x) + sin(f(x)))/C1, C1*C2), whose C1/C2 combination is one constant
    // (its C1 is a fresh constant beside the one in the equation)
    expect(simp('Eq(log(C1*x*(f(x)+sin(f(x)))), 0)', '1st_homogeneous_coeff_subs_dep_div_indep')).toBe('Eq(x*(f(x) + sin(f(x))), C1)');
    expect(simp('Eq(log(C1*x*(f(x)+sin(f(x)))), 0)')).toBe('Eq(log(C1*x*(f(x) + sin(f(x)))), 0)');
    // no constant: a new C1 (SymPy: Eq(x*(f(x) + sin(f(x)))/C1, C1))
    expect(simp('Eq(log(x*(f(x)+sin(f(x)))), 0)', '1st_homogeneous_coeff_best')).toBe('Eq(x*(f(x) + sin(f(x)))/C1, C1)');
  });
  it('a solution that is not an equation', () => {
    // SymPy: TypeError, eq should be an instance of Equality
    expect(() => odesimp(ode, parse('x + C1'), fx, 'separable')).toThrow(InvariantError);
  });
});
