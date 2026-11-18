// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected solution families: SymPy 1.14 solvers.solveset.
import { expect, it } from 'vitest';
import { nonlinsolve, substitution, symbols, add, mul, pow, exp, sin, log, ImageSet, subs, S } from '../../src';
const [x, y, z] = symbols('x y z');
it('returns all complex exponential branches through the public API', () => {
  const eqs = [add(exp(x), mul(-1, sin(y))), add(pow(y, 2), -4)];
  const result = nonlinsolve(eqs, [x, y]);
  expect(result.length).toBe(2);
  expect(result.map((t) => String(t[1])).sort()).toEqual(['-2', '2']);
  for (const tuple of result) {
    expect(tuple[0]).toBeInstanceOf(ImageSet);
    const family = tuple[0] as ImageSet;
    for (const n of [-2, -1, 0, 1, 2]) {
      const value = subs(family.expr, [[family.variable, n]]);
      const residual = subs(eqs[0]!, [[x, value], [y, tuple[1]!]]).evalf().toComplex();
      expect(Math.hypot(residual.re, residual.im)).toBeLessThan(1e-10);
    }
  }
  expect(substitution(eqs, [x, y]).map(String)).toEqual(result.map(String));
});
it('preserves the same parameter in dependent infinite components', () => {
  const eqs = [add(exp(y), S.One.div(3).neg()), add(pow(z, 2), exp(mul(2, x)), mul(-1, sin(y)))];
  const result = substitution(eqs, [y, z]);
  expect(result.length).toBe(4);
  for (const tuple of result.slice(2)) {
    expect(tuple[0]).toBeInstanceOf(ImageSet); expect(tuple[1]).toBeInstanceOf(ImageSet);
    expect((tuple[0] as ImageSet).variable.equals((tuple[1] as ImageSet).variable)).toBe(true);
  }
  expect(result[0]![0]!.equals(log(S.One.div(3)))).toBe(true);
});
it('solves finite, parametric and inconsistent algebraic systems', () => {
  expect(nonlinsolve([add(x, y), add(pow(y, 2), -1)], [x, y]).map(String).sort()).toEqual(['-1,1', '1,-1']);
  expect(nonlinsolve([add(x, y), add(y, -2)], [x, y]).map(String)).toEqual(['-2,2']);
  expect(nonlinsolve([add(x, y), add(x, y, -1)], [x, y])).toEqual([]);
  expect(nonlinsolve([add(x, y, -1)], [x, y]).length).toBe(1);
});
it('extends assignments, excludes poles and preserves requested column order', () => {
  const known = [new Map([[y, S.One]])];
  expect(substitution([add(x, y)], [x], known, [y], [], [x, y]).map(String)).toEqual(['-1,1']);
  expect(substitution([add(x, y)], [x], known, [y], [add(x, 1)], [y, x])).toEqual([]);
  expect(substitution([add(x, y)], [x], known, [y], [add(x, -1)], [y, x]).map(String)).toEqual(['1,-1']);
  expect(substitution([add(y, -1)], [], known, [y], [], [y, z]).map(String)).toEqual(['1,z']);
  expect(substitution([add(y, -2)], [], known)).toEqual([]);
});

it('refuses to silently drop an independent infinite branch', () => {
  expect(() => nonlinsolve([add(exp(y), -1), add(exp(x), -1)], [x, y])).toThrow('another parameter');
  expect(() => nonlinsolve([add(pow(y, 2), -1), mul(add(y, -1), add(exp(x), -1))], [x, y])).toThrow('unresolved');
});

it('handles complex-only exponential families and inconsistent equations', () => {
  const complex = nonlinsolve([add(exp(y), 1), add(x, mul(-1, y))], [x, y]);
  expect(complex.length).toBe(1); expect(complex[0]!.every((e) => e instanceof ImageSet)).toBe(true);
  expect(nonlinsolve([add(exp(y), -2), add(exp(y), -3)], [x, y])).toEqual([]);
  expect(nonlinsolve([exp(y), x], [x, y])).toEqual([]);
});

it('reports an unresolved transcendental equation explicitly', () => {
  expect(() => nonlinsolve([add(y, sin(y)), x], [x, y])).toThrow();
});

import * as sj from '../../src';
it('checks the domain of every original subexpression', () => {
  expect(sj.domainCheck(sj.parseExpr('1/(1 + 1/(x + 1)**2)'), x, -1)).toBe(false);
  expect(sj.domainCheck(pow(x, 2), x, 0)).toBe(true);
  expect(sj.domainCheck(pow(x, -1), x, S.Infinity)).toBe(false);
  expect(sj.domainCheck(mul(x, pow(x, -1)), x, 0)).toBe(true);
  expect(sj.domainCheck(new sj.Mul([x, pow(x, -1)]), x, 0)).toBe(false);
});
it('collects unexpanded linear coefficients and rejects hidden nonlinearities', () => {
  expect(sj.linearCoeffs(sj.parseExpr('3*x + 2*y - 1'), x, y).map(String)).toEqual(['3', '2', '-1']);
  expect(sj.linearCoeffs(sj.parseExpr('x + y*(z*(3*x + 2) + 3)'), x).map(String)).toEqual(['3*y*z + 1', 'y*(2*z + 3)']);
  expect(sj.linearCoeffs(1, x).map(String)).toEqual(['0', '1']);
  expect(sj.linearCoeffs(x).map(String)).toEqual(['x']);
  expect(() => sj.linearCoeffs(x, x, x)).toThrow(RangeError);
  expect(() => sj.linearCoeffs(mul(x, add(y, 1)), x, y)).toThrow(sj.NonlinearError);
  expect(() => sj.linearCoeffs(pow(x, 2), x)).toThrow(sj.NonlinearError);
  expect(() => sj.linearCoeffs(sj.parseExpr('(x - 1)/x + 1/x'), x)).toThrow(sj.NonlinearError);
});
it('returns real and periodic solution representatives', () => {
  expect(String(sj.solvesetReal(add(exp(x), -1), x))).toBe('{0}');
  expect(sj.solvify(add(pow(x, 2), -9), x, sj.Reals)).toEqual([sj.Rational.of(-3), sj.Rational.of(3)]);
  expect(sj.solvify(1, x, sj.Reals)).toEqual([]);
  expect(sj.solvify(add(exp(x), -1), x, sj.Complexes)).toBe(sj.NoMatch);
  expect(sj.solvify(add(sin(x), -1), x, sj.Reals).toString()).toBe('pi/2');
  expect(sj.solvify(sj.tan(x), x, sj.Reals).toString()).toBe('0');
  expect(() => sj.solvify(add(sin(x), x), x, sj.Reals)).toThrow(sj.NotImplementedError);
});

it('inverts functions over real and complex domains', () => {
  expect(sj.invertReal(exp(x), 1, x).map(String)).toEqual(['x', '{0}']);
  expect(sj.invertReal(exp(x), y, x).map(String)).toEqual(['x', 'Intersection({log(y)}, Reals)']);
  expect(sj.invertComplex(exp(x), 1, x)[1]).toBeInstanceOf(ImageSet);
  expect(sj.invertComplex(add(sin(x), x), y, x).map(String)).toEqual(['x + sin(x)', '{y}']);
  expect(() => sj.invertReal(y, 1, x)).toThrow(RangeError);
  expect(() => sj.invertReal(x, x, x)).toThrow(RangeError);
});

it('handles unions and non-real periodic representatives', () => {
  expect(sj.solvify(sin(x),x,sj.Reals).toString()).toBe('0,pi');
  expect(sj.solvify(sin(x),x,sj.Integers)).toEqual([S.Zero]);
  expect(sj.solvify(add(exp(mul(S.I,x)),-2),x,sj.Complexes)).toBe(sj.NoMatch);
});

it('solves polynomial equations over the complex domain explicitly', () => {
  expect(sj.solvesetComplex(add(pow(x, 2), 1), x)).toEqual(sj.FiniteSet.of(mul(-1, S.I), S.I));
});

it('handles empty nonlinear systems and rejects missing unknowns', () => {
  expect(nonlinsolve([], [])).toEqual([]);
  expect(nonlinsolve([], [x, y])).toEqual([]);
  expect(() => nonlinsolve([add(pow(x, 2), -1)], [])).toThrow(RangeError);
});
