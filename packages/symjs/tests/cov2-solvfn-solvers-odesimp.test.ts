// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { SymFunction as Fn, parse, symbols } from '../src';
import { InvariantError } from '../src/core/errors';
import type { UndefFn } from '../src/core/nodes';
import { Integral, Rational } from '../src/core/nodes';
import { add } from '../src/core/ops';
import { constantsimp, odesimp } from '../src/solvers/odesimp';

const [C1, C2, C3, x, y] = symbols('C1 C2 C3 x y');
const f = Fn('f');
const fx = f(x) as UndefFn;
const ode = parse('Eq(Derivative(f(x), x), f(x)/x)');
const cs = (e: string, ...c: (typeof C1)[]) => String(constantsimp(parse(e), c));
const simp = (e: string, hint = 'separable') => odesimp(ode, parse(e), fx, hint).map(String).join(', ');

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
