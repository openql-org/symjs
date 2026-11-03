// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { parse, symbols } from '../src';
import { Integral, Rational } from '../src/core/nodes';
import { add } from '../src/core/ops';
import { constantsimp } from '../src/solvers/odesimp';

const [C1, C2, C3, x, y] = symbols('C1 C2 C3 x y');
const cs = (e: string, ...c: typeof C1[]) => String(constantsimp(parse(e), c));

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
