// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected solution families: SymPy 1.14 solvers.solveset.
import { expect, it, vi } from 'vitest';
import { nonlinsolve, substitution, solvify, Reals, NoMatch, symbols, parse, add, mul, pow, exp, sin, log, ImageSet, subs, S } from '../../src';
import { at } from '../../src/core/guard';
import { passingModuleCases, runTestCase } from '../../../../tools/sympy-corpus/unittest-harness';
import * as elimination from '../../src/solvers/solve';
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
it('includes the complex solutions of a polynomial system with real unknowns', () => {
  const [a, b] = symbols('a b', { real: true });
  const eqs = [add(pow(a, 2), mul(-2, pow(b, 2)), -2), add(mul(a, b), -2)];
  expect(nonlinsolve(eqs, [a, b]).map(String).sort()).toEqual(['-2,-1', '-sqrt(2)*I,sqrt(2)*I', '2,1', 'sqrt(2)*I,-sqrt(2)*I']);
  expect(nonlinsolve([add(a, mul(-1, S.I))], [a]).map(String)).toEqual(['I']);
});
it('rejects the extraneous solution from squaring a radical equation', () => {
  expect(nonlinsolve([parse('sqrt(y)-x-z'), parse('y-1')], [x, y, z]).map(String)).toEqual(['1 - z,1,z']);
});
it('represents a dependent coordinate in a positive-dimensional system', () => {
  const equations = [parse('x**4-3*x**2+y*x'), parse('x*z**2'), parse('y*z-1')];
  expect(nonlinsolve(equations, [x, y, z]).map(String)).toEqual(['0,1/z,z']);
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
  expect((sj.solvify(sin(x),x,sj.Integers) as sj.Expr[]).map(String)).toEqual(['0']);
  expect(sj.solvify(add(exp(mul(S.I,x)),-2),x,sj.Complexes)).toBe(sj.NoMatch);
});

it('solves polynomial equations over the complex domain explicitly', () => {
  expect(sj.solvesetComplex(add(pow(x, 2), 1), x).key).toBe(sj.FiniteSet.of(mul(-1, S.I), S.I).key);
});

it('handles empty nonlinear systems and rejects missing unknowns', () => {
  expect(nonlinsolve([], [])).toEqual([]);
  expect(nonlinsolve([], [x, y])).toEqual([]);
  expect(() => nonlinsolve([add(pow(x, 2), -1)], [])).toThrow(RangeError);
});

it('inverts real hyperbolic functions and preserves partially inverted expressions', () => {
  const r = new sj.Sym('r', { real: true }), p = new sj.Sym('p', { positive: true });
  expect(sj.invertReal(sj.Abs(add(pow(x, 31), x, 1)), p, x).map(String)).toEqual(['x**31 + x', '{-p - 1, p - 1}']);
  expect(sj.invertReal(sj.sinh(x), r, x).map(String)).toEqual(['x', '{asinh(r)}']);
  expect(sj.invertReal(sj.sinh(log(x)), p, x).map(String)).toEqual(['x', '{exp(asinh(p))}']);
  expect(sj.invertReal(sj.cosh(x), r, x).map(String)).toEqual(['x', 'Intersection({-acosh(r), acosh(r)}, Reals)']);
  expect(sj.invertReal(sj.cosh(x), add(p, 1), x).map(String)).toEqual(['x', '{-acosh(p + 1), acosh(p + 1)}']);
  expect(sj.invertReal(sj.tanh(x), r, x).map(String)).toEqual(['x', 'Intersection({atanh(r)}, Reals)']);
  expect(sj.invertReal(sj.coth(x), add(p, 1), x).map(String)).toEqual(['x', '{acoth(p + 1)}']);
  expect(sj.invertReal(sj.sech(x), r, x).map(String)).toEqual(['x', 'Intersection({-asech(r), asech(r)}, Reals)']);
  expect(sj.invertReal(sj.csch(x), p, x).map(String)).toEqual(['x', '{acsch(p)}']);
  expect(sj.invertReal(pow(x, sj.pi), sj.E.neg(), x).map(String)).toEqual(['x', 'EmptySet']);
  expect(sj.invertReal(sj.Abs(x), -1, x).map(String)).toEqual(['x', 'EmptySet']);
  expect(() => sj.invertReal(y, 0, x)).toThrow(RangeError);
  expect(() => sj.invertReal(x, x, x)).toThrow(RangeError);
  expect(sj.invertReal(add(mul(3, x), 1), p, x).map(String)).toEqual(['x', '{p/3 - 1/3}']);
  expect(sj.invertReal(pow(2, exp(x)), p, x).map(String)).toEqual(['x', 'Intersection({log(log(p)/log(2))}, Reals)']);
});

it('solves functional decompositions through ranges and successive preimages', () => {
  for (const [expression, expected] of [
    ['exp(3*x)-6*exp(2*x)+11*exp(x)-6', '{0, log(2), log(3)}'],
    ['exp(x+2)-1', '{-2}'], ['1/log(x)', 'EmptySet'], ['1/x', 'EmptySet'],
  ] as const) expect(String(sj.solveDecomposition(sj.parseExpr(expression), x, sj.Reals))).toBe(expected);
  expect(sj.solveDecomposition(x, x, sj.interval(1, 2))).toBe(sj.EmptySet);
});

it('preserves periodic families while solving decompositions', () => {
  for (const f of [sj.sin(add(x, 1)), add(pow(sin(x), 2), mul(-1, sin(x))), sin(pow(x, 2)), sin(exp(x))]) {
    const result = sj.solveDecomposition(f, x, sj.Reals);
    const families = result instanceof sj.SetOp ? result.args : [result];
    expect(families.every((family) => family instanceof ImageSet)).toBe(true);
    for (const family of families) if (family instanceof ImageSet) {
      const value = subs(family.expr, [[family.variable, 2]]);
      const residual = subs(f, [[x, value]]).evalf().toComplex();
      expect(Math.hypot(residual.re, residual.im)).toBeLessThan(1e-8);
    }
  }
});

it('handles zero right hand sides and nonzero real inverse hyperbolic values', () => {
  const n = new sj.Sym('n', { negative: true });
  expect(sj.invertReal(exp(x), 0, x)).toEqual([x, sj.EmptySet]);
  expect(sj.invertReal(sj.csch(x), n, x).map(String)).toEqual(['x', '{acsch(n)}']);
  expect(sj.invertReal(sj.csch(x), y, x)[1]).toBeInstanceOf(sj.SetOp);
  expect(nonlinsolve([1, 2], [])).toEqual([]);
  expect(nonlinsolve([0], [])).toEqual([[]]);
});

it('retains unresolved decompositions and inversion problems', () => {
  const a = new sj.Sym('a', { real: true });
  expect(sj.solveDecomposition(sin(add(pow(x, 5), x)), x, sj.Reals)).toBeInstanceOf(sj.ConditionSet);
  expect(sj.solveDecomposition(sin(add(exp(x), a)), x, sj.Reals)).toBeInstanceOf(sj.ConditionSet);
  expect(sj.solveDecomposition(sj.cos(add(x, 1)), x, sj.Reals)).toBeInstanceOf(sj.SetOp);
  expect(() => sj.invertComplex(y, 0, x)).toThrow(RangeError);
  expect(() => sj.invertComplex(x, x, x)).toThrow(RangeError);
  expect(sj.invertReal(pow(x, sj.E), -1, x)).toEqual([x, sj.EmptySet]);
  expect(sj.invertReal(pow(x, sj.pi), 1, x)[0]).toEqual(x);
  expect(sj.invertReal(pow(x, S.I), 1, x).length).toBe(2);
  expect(nonlinsolve([add(pow(y, 2), -1), add(y, -2)], [x, y])).toEqual([]);
  expect(() => nonlinsolve([add(pow(y, 2), -1), add(x, sin(x))], [x, y])).toThrow(sj.NotImplementedError);
});

it('eliminates a variable in an underdetermined exponential system', () => {
  expect(nonlinsolve([parse('2**x + 2**y - 3')], [x, y]).map(String)).toEqual(['log(3 - 2**y)/log(2),y']);
});

it('keeps free variables when known assignments resolve every equation', () => {
  expect(substitution([add(x, -1)], [x, y], [new Map([[x, 1]])]).map(String)).toEqual(['1,y']);
  expect(substitution([], [x, y], [new Map([[x, 1]])])).toEqual([]);
});

it('excludes poles from free parameters introduced by finite substitution', () => {
  const solutions = nonlinsolve([parse('x**3*y**3 - 1/2')], [x, y]);
  expect(solutions).toHaveLength(3);
  expect(solutions.map((solution) => String(solution[1]))).toEqual([
    'Complement({y}, {0})', 'Complement({y}, {0})', 'Complement({y}, {0})',
  ]);
});

it('rejects infinite algebraic candidates in an exponential system', () => {
  const equations = [parse('(x**2+2*x-y**2)*exp(x)'), parse('-2*y*exp(x)')];
  expect(nonlinsolve(equations, [x, y]).map(String)).toEqual(['-2,0', '0,0']);
  expect(nonlinsolve([exp(add(x, y))], [x, y])).toEqual([]);
});

it('finds isolated solutions in a union with intervals of zeros', () => {
  expect(String(solvify(parse('Piecewise((0,x<-1),(x**2,x<=1),(log(x),True))'), x, Reals))).toBe('0');
  expect(String(solvify(parse('Piecewise((0,x<-10),(x**2+5*x-6,x>=-9))'), x, Reals))).toBe('-6,1');
});

it('discards a branch when finite substitution leaves a nonzero constant', () => {
  expect(nonlinsolve([parse('x**2-y**2'), parse('sin(x**2-y**2+1)')], [x, y])).toEqual([]);
});

it('has no finite representatives for an identity on the reals', () => {
  expect(solvify(0, x, Reals)).toBe(NoMatch);
});

it('propagates errors from elimination that are unrelated to solver support', () => {
  const failure = new RangeError('invalid elimination input');
  const spy = vi.spyOn(elimination, 'nonlinsolve').mockImplementationOnce(() => { throw failure; });
  try {
    expect(() => nonlinsolve([x], [x, y])).toThrow(failure);
  } finally {
    spy.mockRestore();
  }
});

it('evaluates the SymPy nonlinear-system assertions that require symbolic set results', () => {
  const cases = passingModuleCases('solvers', 'sympy.solvers.tests.test_solveset')
    .filter((c) => c.fn === 'nonlinsolve' || c.fn === 'substitution');
  for (const c of cases) expect(['pass', 'equivalent'], c.src).toContain(runTestCase(c).status);
});

it('preserves the joint integer parameters of a binomial exponential system', () => {
  const equations = [parse('32*2**x*2**y-4**y'), parse('27*3**x-3**(-y)')];
  const system = nonlinsolve(equations, [x, y], { asSet: true });
  expect(system).toBeInstanceOf(ImageSet);
  if (!(system instanceof ImageSet)) throw new TypeError('expected an integer image');
  for (const [i, j] of [[0, 0], [-2, 1], [1, 3]] as const) {
    const point = system.lamda.call(i, j);
    for (const e of equations) {
      const residual = subs(e, [[x, at(point.args, 0)], [y, at(point.args, 1)]]).toComplex();
      expect(Math.hypot(residual.re, residual.im)).toBeLessThan(1e-10);
    }
  }
  expect(nonlinsolve(equations, [x, y])[0]?.every((coord) => coord instanceof ImageSet)).toBe(true);
});

it('retains relations for unsolved coordinates and supports compound unknowns', () => {
  const f = sin(x);
  expect(nonlinsolve([add(f, y, -1), add(f, y.neg())], [f, y]).map(String)).toEqual(['1/2,1/2']);
  expect(nonlinsolve([add(x, -1)], [x]).map(String)).toEqual(['1']);
  expect(nonlinsolve([sj.Eq(add(x, pow(x, -1)), pow(x, -1))], [x]).map(String)).toEqual(['EmptySet']);
  expect(() => substitution([x], [])).toThrow(RangeError);
});

it('retains constraints that survive attempted bivariate elimination', () => {
  for (const equations of [
    ['(x**2+y**2+1)*(exp(x)+exp(y)+1)', 'sin(x+y)+x+y'],
    ['2**(x+y)+5**x+2**x', '3**x+x+sin(y)'],
    ['2**x+y+1', '3**x+sin(y)+x'],
    ['sin(x+y)/y+x', 'sin(x+y)/x+y'],
  ]) {
    expect(nonlinsolve(equations.map((e) => parse(e)), [x, y], { asSet: true })).toBeInstanceOf(sj.ConditionSet);
  }
  const rankDeficient = nonlinsolve([parse('2**x-3**y'), parse('4**x-9**y')], [x, y], { asSet: true });
  expect(rankDeficient).toBeInstanceOf(ImageSet);
  const oddPeriods = nonlinsolve([parse('2**x+3**y'), parse('2**x*3**y-3**(-y)')], [x, y], { asSet: true });
  expect(oddPeriods).toBeInstanceOf(ImageSet);
  expect(nonlinsolve([parse('z-1'), parse('x**2-y**2')], [x, z])).toHaveLength(4);
});

it('separates periodic coordinates only when their periods and zero factors allow it', () => {
  for (const equations of [
    ['sin(x)*cos(y)', 'sin(x)+sin(y)'],
    ['sin(x)*cos(y)', 'y-x'],
    ['sin(x)*cos(y)', 'cos(x/3)*cos(y)-1'],
    ['sin(x)*cos(y)', 'cos(x)*y-1'],
    ['sin(x+y)*cos(y)', 'x-y'],
    ['sin(z)*cos(x)', 'x-y'],
    ['sin(x**2)*sin(y)', 'cos(x)*cos(y)'],
    ['sin(x)*sin(y)', 'cos(x)*sin(y)'],
  ]) {
    const result = nonlinsolve(equations.map((e) => parse(e)), [x, y], { asSet: true });
    expect(result).toBeInstanceOf(sj.FiniteSet);
  }
});

it('solves quadratic factors with numeric and parametric content', () => {
  expect(nonlinsolve([parse('2*(x**2-y**2)')], [x, y]).length).toBeGreaterThanOrEqual(2);
  expect(nonlinsolve([parse('z*(x**2-y**2)')], [x, y]).length).toBeGreaterThanOrEqual(2);
  expect(nonlinsolve([parse('sin(x)*(y**2-x**2)')], [x, y], { asSet: true })).toBeInstanceOf(sj.SetExpr);
});

it('keeps residual equations over all coordinates of a positive-dimensional domain', () => {
  const equations = [parse('sin(x+y)+x'), parse('sin(x+y)+y')];
  const result = nonlinsolve(equations, [x, y, z], { asSet: true });
  expect(result).toBeInstanceOf(sj.ConditionSet);
  expect(String(result)).toContain('ProductSet(Complexes, Complexes, Complexes)');
  const coupled = nonlinsolve([parse('sin(x+y)*cos(y)'), parse('sin(y)+sin(x)')], [x, y], { asSet: true });
  expect(coupled).toBeInstanceOf(sj.ConditionSet);
  const shorterPeriod = nonlinsolve([parse('sin(2*x)*sin(2*y)'), parse('sin(x)+sin(y)')], [x, y]);
  expect(shorterPeriod.map(String)).toContain('0,0');
});

it('combines the two substitution passes for a cubic with conjugate Cardano radicals', () => {
  const equation = parse('y**3-3*y**2+1');
  const rows = substitution([x.sub(y), equation], [x, y]);
  const ordinates = new Set<string>();
  for (const row of rows) {
    const a = at(row, 0).toNumber(), b = at(row, 1).toNumber();
    expect(a).toBeCloseTo(b, 12);
    expect(b ** 3 - 3 * b ** 2 + 1).toBeCloseTo(0, 12);
    ordinates.add(at(row, 1).key);
  }
  expect(rows).toHaveLength(5);
  expect(ordinates.size).toBe(3);
  const rationalEquation = equation.div(y.add(2));
  expect(substitution([x.sub(y), rationalEquation], [x, y])).toHaveLength(3);
});
