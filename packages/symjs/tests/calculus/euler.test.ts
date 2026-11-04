// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/calculus/euler.ts.
// Euler-Lagrange equations. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [t, x] = [new sj.Sym('t'), new sj.Sym('x')];
const [X, Y, u] = [sj.SymFunction('x'), sj.SymFunction('y'), sj.SymFunction('u')];
const half = sj.Rational.of(1n, 2n);
const show = (eqs: readonly sj.Expr[]): string => `[${eqs.map(String).join(', ')}]`;

describe('euler_equations', () => {
  it('gives the equations of the SymPy doctests', () => {
    const L1 = sj.sub(sj.mul(half, sj.pow(sj.diff(X(t), t), 2)), sj.mul(half, sj.pow(X(t), 2)));
    expect(show(sj.eulerEquations(L1, X(t), t))).toBe('[Eq(-x(t) - Derivative(x(t), (t, 2)), 0)]');
    const L2 = sj.sub(sj.mul(half, sj.pow(sj.diff(u(t, x), t), 2)), sj.mul(half, sj.pow(sj.diff(u(t, x), x), 2)));
    expect(show(sj.eulerEquations(L2, u(t, x), [t, x]))).toBe('[Eq(-Derivative(u(t, x), (t, 2)) + Derivative(u(t, x), (x, 2)), 0)]');
  });

  it('finds the functions and variables', () => {
    expect(show(sj.eulerEquations(sj.add(sj.pow(sj.diff(X(t), t, 2), 2), sj.mul(X(t), sj.diff(X(t), t)))))).toBe('[Eq(2*Derivative(x(t), (t, 4)), 0)]');
    expect(show(sj.eulerEquations(sj.mul(sj.diff(u(t, x), t), sj.diff(u(t, x), x))))).toBe('[Eq(-2*Derivative(u(t, x), t, x), 0)]');
    const L = sj.add(sj.mul(sj.diff(X(t), t), sj.diff(Y(t), t)), sj.mul(X(t), Y(t)));
    expect(show(sj.eulerEquations(L, [X(t), Y(t)], [t]))).toBe('[Eq(y(t) - Derivative(y(t), (t, 2)), 0), Eq(x(t) - Derivative(x(t), (t, 2)), 0)]');
    // no equation where the derivative of L is a number
    expect(show(sj.eulerEquations(sj.pow(t, 2), X(t), t))).toBe('[]');
    expect(show(sj.eulerEquations(X(t), X(t), [t]))).toBe('[]');
  });

  it('rejects other arguments', () => {
    expect(() => sj.eulerEquations(X(t), t, t)).toThrow('Function expected, got: t');
    expect(() => sj.eulerEquations(X(t), X(t), sj.mul(x, t))).toThrow('Variables are not symbols, got t*x');
    expect(() => sj.eulerEquations(X(t), X(t), x)).toThrow('Variables (x,) do not match args: x(t)');
    expect(() => sj.eulerEquations(X(t), X(t), [t, x])).toThrow('Variables (t, x) do not match args: x(t)');
    expect(() => sj.eulerEquations(sj.add(sj.sin(X(t)), sj.pow(sj.diff(X(t), t), 2)))).toThrow('Variables (t,) do not match args: sin(x(t))');
  });
});
