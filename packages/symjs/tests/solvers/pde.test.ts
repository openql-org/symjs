// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference results from SymPy 1.14 solvers.pde; verify solutions independently by differentiation.
import { expect, it } from 'vitest';
import { classifyPde, pdsolve, checkpdesol, pdeSeparate, pdeSeparateAdd, pdeSeparateMul, symbols, SymFunction, diff, add, mul, sin, exp, Eq, S, isNoMatch } from '../../src';
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
  for (const eq of [diff(u, x, 2), mul(u, ux), add(mul(x, ux), uy), u]) {
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
