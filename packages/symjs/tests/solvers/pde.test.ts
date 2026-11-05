// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference results from SymPy 1.14 solvers.pde; verify solutions independently by differentiation.
import { expect, it } from 'vitest';
import type { Expr } from '../../src';
import { classifyPde, pdsolve, checkpdesol, pdeSeparate, pdeSeparateAdd, pdeSeparateMul, symbols, SymFunction, diff, add, mul, pow, sin, exp, Eq, S, isNoMatch } from '../../src';
const [x, y, z] = symbols('x y z'); const u = SymFunction('u')(x, y), X = SymFunction('X')(x), Y = SymFunction('Y')(y);
const ux = diff(u, x), uy = diff(u, y);
it('solves and checks constant coefficient homogeneous PDEs', () => {
  const a = add(ux, uy);
  expect(String(pdsolve(a))).toBe('Eq(u(x, y), F(x - y))');
  expect(classifyPde(a)).toEqual(['1st_linear_constant_coeff_homogeneous']);
  const b = add(mul(2, ux), mul(3, uy), mul(5, u));
  expect(String(pdsolve(b, u))).toBe('Eq(u(x, y), F(3*x - 2*y)*exp(-10*x/13 - 15*y/13))');
  expect(checkpdesol(b, pdsolve(b), u)[0]).toBe(true);
});
it('includes a particular solution for inhomogeneous equations', () => {
  for (const eq of [add(ux, uy, mul(-1, x), mul(-1, y)), add(uy, mul(-1, y)), add(ux, u, mul(-1, exp(x)))]) {
    expect(classifyPde(eq)[0]).toBe('1st_linear_constant_coeff');
    const solution = pdsolve(eq, u, '1st_linear_constant_coeff');
    expect(checkpdesol(eq, solution)[0]).toBe(true);
  }
  expect(String(pdsolve(add(uy, mul(-1, y))))).toBe('Eq(u(x, y), y**2/2 + F(x))');
});
it('uses a nondegenerate characteristic chart for complex coefficients', () => {
  // SymPy 1.14 returns False for this equation because a^2+b^2=0.
  // F(I*x-y) is a solution for any differentiable F; its residual is exactly zero.
  const eq = add(ux, mul(S.I, uy));
  expect(String(pdsolve(eq))).toBe('Eq(u(x, y), F(I*x - y))');
  expect(checkpdesol(eq, pdsolve(eq), u)[0]).toBe(true);
});
it('rejects an unsupported class or hint explicitly', () => {
  for (const eq of [diff(u, x, 2), mul(u, ux), add(mul(pow(u, 2), ux), mul(pow(u, 3), uy)), add(mul(exp(u), ux), uy), add(mul(pow(u, z), ux), uy), u]) {
    expect(classifyPde(eq, u)).toEqual([]);
    expect(() => pdsolve(eq, u)).toThrow('only first-order');
  }
  expect(classifyPde(diff(SymFunction('v')(x), x), SymFunction('v')(x))).toEqual([]);
  expect(() => pdsolve(add(ux, uy), u, 'unsupported')).toThrow('hint');
  expect(() => pdsolve(x)).toThrow('Specify');
  expect(() => classifyPde(add(u, SymFunction('v')(x, y)))).toThrow('Specify');
});
it('checks both equation orientations and rejects invalid candidates', () => {
  const eq = add(ux, uy), solution = SymFunction('F')(add(x, mul(-1, y)));
  expect(checkpdesol(eq, solution, u)).toEqual([true, S.Zero]);
  expect(checkpdesol(eq, Eq(solution, u), u)[0]).toBe(true);
  const [valid, residual] = checkpdesol(eq, x, u);
  expect(valid).toBe(false); expect(residual.equals(S.One)).toBe(true);
  expect(() => checkpdesol(eq, Eq(x, y), u)).toThrow('explicit');
  expect(() => checkpdesol(eq, add(u, 1), u)).toThrow('explicit');
});
it('separates a heat equation multiplicatively and a transport equation additively', () => {
  expect(pdeSeparateMul(add(diff(u, x, 2), mul(-1, uy)), u, [X, Y]).toString()).toBe('Derivative(X(x), (x, 2))/X(x),Derivative(Y(y), y)/Y(y)');
  expect(pdeSeparateAdd(add(ux, mul(-1, uy)), u, [X, Y]).toString()).toBe('Derivative(X(x), x),Derivative(Y(y), y)');
  const result = pdeSeparate(add(ux, mul(x, y, u)), u, [X, Y]);
  expect(result.toString()).toBe('Derivative(X(x), x)/(x*X(x)),-y');
});
it('validates separation variables and reports an unavailable separation', () => {
  expect(() => pdeSeparate(ux, u, [X])).toThrow('counts');
  expect(() => pdeSeparate(ux, u, [X, X])).toThrow('Duplicate');
  expect(() => pdeSeparate(ux, u, [X, SymFunction('Z')(z)])).toThrow('Arguments');
  expect(() => pdeSeparate(ux, u, [u])).toThrow('At least');
  expect(isNoMatch(pdeSeparate(add(mul(sin(mul(x, y)), ux), uy), u, [X, Y], 'add'))).toBe(true);
  expect(isNoMatch(pdeSeparate(ux, u, [X, Y], 'add'))).toBe(true);
});

it('keeps the integration unevaluated for the Integral hint', () => {
  expect(String(pdsolve(add(ux, uy, mul(-1, x)), u, '1st_linear_constant_coeff_Integral'))).toContain('Integral(');
  expect(() => Reflect.apply(pdeSeparate, undefined, [ux, u, [X, Y], 'invalid'])).toThrow('strategy');
});

it('separates algebraic terms and rejects inseparable remainders', () => {
  // SymPy 1.14: [1/x, -y], None, None respectively.
  expect(String(pdeSeparateAdd(add(mul(x, y), 1), u, [X, Y]))).toBe('1/x,-y');
  expect(isNoMatch(pdeSeparateAdd(add(sin(mul(x, y)), uy), u, [X, Y]))).toBe(true);
  expect(isNoMatch(pdeSeparateAdd(add(ux, mul(x, y), mul(x, x, y, y)), u, [X, Y]))).toBe(true);
});

it('divides out the smallest power of the function from the derivative coefficients', () => {
  // SymPy 1.14 classify_pde / pdsolve doctest
  const eq = Eq(add(1, mul(2, ux, pow(u, -1)), mul(3, uy, pow(u, -1))), 0);
  expect(classifyPde(eq)).toEqual(['1st_linear_constant_coeff_homogeneous']);
  expect(String(pdsolve(eq))).toBe('Eq(u(x, y), F(3*x - 2*y)*exp(-2*x/13 - 3*y/13))');
  expect(String(pdsolve(add(mul(pow(u, 2), ux), mul(pow(u, 2), uy))))).toBe('Eq(u(x, y), F(x - y))');
});
it('solves first-order linear PDEs with variable coefficients', () => {
  // SymPy 1.14 pdsolve results (1st_linear_variable_coeff)
  const cases: [Expr, string][] = [
    [add(mul(x, ux), uy), 'F(y - log(x))'],
    [add(mul(x, u, ux), mul(u, uy)), 'F(y - log(x))'],
    // SymPy: F(-2*x + y**2); symjs dsolve writes the characteristic as sqrt(2)*sqrt(C1 + x)
    // instead of sqrt(C1 + 2*x), which gives the same family of solutions
    [add(mul(y, ux), uy), 'F(-x + y**2/2)'],
    [add(mul(x, ux), mul(-1, y, uy), mul(y, y, u), mul(-1, y, y)), 'F(x*y)*exp(y**2/2) + 1'],
    [add(mul(x, ux), mul(y, y, uy), u), 'F(-log(x) - 1/y)/x'],
    [add(ux, mul(x, y, uy)), 'F(y*exp(-x**2/2))'],
    [add(mul(x, ux), u), 'F(y)/x'],
    [add(mul(-1, x), mul(y, uy), u), 'x + F(x)/y'],
    [add(mul(x, ux), mul(x, u)), 'F(y)*exp(-x)'],
    [add(mul(x, ux), -1), 'F(y) + log(x)'],
    [add(mul(y, uy), mul(-1, x)), 'x*log(y) + F(x)'],
  ];
  for (const [eq, solution] of cases) {
    expect(classifyPde(eq, u)).toEqual(['1st_linear_variable_coeff']);
    const sol = pdsolve(eq, u, '1st_linear_variable_coeff');
    expect(String(sol)).toBe(`Eq(u(x, y), ${solution})`);
    expect(checkpdesol(eq, sol, u)[0]).toBe(true);
  }
});
