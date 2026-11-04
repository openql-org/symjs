// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/symbolicprobability.ts (SymPy
// sympy/stats/symbolic_probability.py and
// sympy/stats/tests/test_symbolic_probability.py). Expected values are
// those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { And, Eq, Gt, Not, S, Sym, add, doit, expand, mul, pow, rewrite, simplify, sin, str, sub } from '../../src';
import type { Expr } from '../../src';
import {
  CentralMoment,
  CentralMomentNode,
  Covariance,
  CovarianceNode,
  Die,
  Expectation,
  ExpectationNode,
  Moment,
  MomentNode,
  Normal,
  P,
  Poisson,
  Probability,
  ProbabilityNode,
  RandomSymbol,
  Variance,
  VarianceNode,
  expectation,
  variance,
} from '../../src/stats';
import { makeExpectation } from '../../src/stats/symbolicprobability';
import { statsClasses } from '../../src/stats/rv';
import { defined } from '../../src/core/guard';

const eq = (a: Expr, b: Expr): boolean => a.key === b.key;
const [xr] = [new Sym('x', { real: true })];
const [y, w, z] = [new Sym('y'), new Sym('w'), new Sym('z')];
const X = Normal('X', 2, 3);
const Y = Normal('Y', 3, 4);
const Z = Poisson('Z', 4);
const W = Poisson('W', 3);

describe('Probability and Expectation (SymPy test_literal_probability)', () => {
  it('evaluate the integrals', () => {
    expect(eq(Probability(Gt(X, 0)).evaluateIntegral(), P(Gt(X, 0)))).toBe(true);
    expect(str(Probability(Gt(X, 0)).evaluateIntegral())).toBe(str(P(Gt(X, 0))));
    expect(str(doit(rewrite(Probability(Gt(X, xr)), 'Integral')))).toBe(str(P(Gt(X, xr))));
    expect(eq((Expectation(X) as ExpectationNode).evaluateIntegral(), expectation(X))).toBe(true);
    expect(str(doit(rewrite(Expectation(X), 'Integral')))).toBe('2');
    expect(str((Expectation(pow(X, 2)) as ExpectationNode).evaluateIntegral())).toBe(str(expectation(pow(X, 2))));
    expect(str((Expectation(X) as ExpectationNode).evaluateSum())).toBe('2');
  });

  it('expand by linearity', () => {
    const e = (v: Expr): Expr => expand(Expectation(v));
    expect(Expectation(mul(xr, X)).args.map(str)).toEqual(['x*X']);
    expect(str(e(mul(xr, X)))).toBe('x*Expectation(X)');
    expect(str(e(add(mul(2, X), mul(3, Y), mul(z, X, Y))))).toBe('z*Expectation(X*Y) + 2*Expectation(X) + 3*Expectation(Y)');
    expect(eq(e(sin(X)), Expectation(sin(X)))).toBe(true);
    expect(str(e(add(mul(2, xr, sin(X), Y), mul(y, pow(X, 2)), mul(z, X, Y))))).toBe('2*x*Expectation(sin(X)*Y) + y*Expectation(X**2) + z*Expectation(X*Y)');
    expect(str(e(add(X, Y)))).toBe('Expectation(X) + Expectation(Y)');
    expect(str(e(mul(add(X, Y), sub(X, Y))))).toBe('Expectation(X**2) - Expectation(Y**2)');
    expect(str(doit(e(mul(add(X, Y), sub(X, Y)))))).toBe('-12');
    expect(str(e(pow(add(X, Y), 3)))).toBe('3*Expectation(X*Y**2) + 3*Expectation(X**2*Y) + Expectation(X**3) + Expectation(Y**3)');
    expect(str(e(pow(sub(X, Y), 3)))).toBe('3*Expectation(X*Y**2) - 3*Expectation(X**2*Y) + Expectation(X**3) - Expectation(Y**3)');
    expect(str(e(pow(sub(X, Y), 2)))).toBe('-2*Expectation(X*Y) + Expectation(X**2) + Expectation(Y**2)');
    // a value that is not random, and a condition
    expect(str((new ExpectationNode([y]) as ExpectationNode).expand())).toBe('y');
    expect(str(expand(Expectation(add(X, Y), Gt(X, 0))))).toBe('Expectation(X, X > 0) + Expectation(Y, X > 0)');
  });

  it('doit with and without deep', () => {
    expect(str(doit(Expectation(add(X, Y))))).toBe('5');
    expect(str(doit(Expectation(add(X, Expectation(Y)))))).toBe('5');
    const ex = (v: Expr, deep: boolean): string => str((Expectation(v) as ExpectationNode).doit({ deep }));
    expect(ex(add(X, Expectation(Y)), false)).toBe('Expectation(Expectation(Y)) + 2');
    expect(ex(add(X, Expectation(add(Y, Expectation(mul(2, X))))), false)).toBe('Expectation(Expectation(Expectation(2*X) + Y)) + 2');
    expect(ex(add(X, Expectation(add(Y, Expectation(mul(2, X))))), true)).toBe('9');
    expect(ex(Expectation(mul(2, X)), true)).toBe('4');
    expect(ex(Expectation(mul(2, X)), false)).toBe('Expectation(2*X)');
    expect(ex(mul(4, Expectation(mul(2, X))), false)).toBe('4*Expectation(2*X)');
    // a condition, and evaluate=False
    expect(str(doit(Expectation(X, Gt(X, 2))))).toBe('2 + 3*sqrt(2)/sqrt(pi)');
    expect(str((Expectation(X) as ExpectationNode).doit({ evaluate: false }))).toBe('Integral(sqrt(2)*X*exp(-(X - 2)**2/18)/(6*sqrt(pi)), (X, -oo, oo))');
    // a random symbol without a space
    const R = new RandomSymbol('R');
    expect(str(doit(Expectation(R)))).toBe('Expectation(R)');
  });

  it('constructors, printing and rebuilding', () => {
    expect(str(Expectation(5))).toBe('5');
    expect(str(Expectation(y, Gt(X, 0)))).toBe('Expectation(y, X > 0)');
    expect(str((makeExpectation(X) as ExpectationNode).withArgs([Y]))).toBe('Expectation(Y)');
    expect((Expectation(X) as ExpectationNode).condition).toBeUndefined();
    expect(Expectation(X).isCommutative).toBe(true);
    expect(str(Probability(Gt(X, 0), Gt(Y, 0)))).toBe('Probability(X > 0, Y > 0)');
    expect(str(Probability(true))).toBe('Probability(True)');
    expect(String(Probability(Gt(X, 0), false).condition)).toBe('False');
    expect(str(Probability(Gt(X, 0)).withArgs([Gt(Y, 0)]))).toBe('Probability(Y > 0)');
    expect(Probability(Gt(X, 0))).toBeInstanceOf(ProbabilityNode);
  });

  it('Not, constant terms, conditions giving a constant and the registered constructors', () => {
    expect(str(P(Not(And(Gt(X, 2), Gt(Y, 3)))))).toBe('3/4');
    // SymPy raises an AttributeError for a negated And with a condition on the same space
    expect(str(expand(Expectation(add(X, 3))))).toBe('Expectation(X) + 3');
    expect(str(expand(Expectation(mul(add(X, 1), add(X, 1)))))).toBe('2*Expectation(X) + Expectation(X**2) + 1');
    expect(str(doit(Expectation(X, Eq(X, 2))))).toBe('2');
    expect(str(defined(statsClasses.probabilityNode)(Gt(X, 0)))).toBe('Probability(X > 0)');
    expect(str(defined(statsClasses.expectation)(X, undefined, false))).toBe('Expectation(X)');
    expect(str(defined(statsClasses.probability)(Gt(X, 0), undefined, false))).toBe('Probability(X > 0)');
  });

  it('Probability.doit', () => {
    expect(str(doit(Probability(Not(Gt(X, 2)))))).toBe('1/2');
    expect(str(doit(Probability(Not(Gt(X, 2)), Gt(X, 2))))).toBe('0');
    expect(str(doit(Probability(Gt(X, 0), false)))).toBe('0');
    expect(str(doit(Probability(false)))).toBe('0');
    expect(str(doit(Probability(true)))).toBe('1');
    expect(() => doit(Probability(X))).toThrow('X is not a relational or combination of relationals');
    expect(() => doit(Probability(Gt(X, 0), X.add(1)))).toThrow('X + 1 is not a relational or combination of relationals');
    expect(str(doit(Probability(Gt(X, 2), Gt(X, 2))))).toBe('1');
    expect(str((Probability(Gt(X, 2)) as ProbabilityNode).doit({ evaluate: false }))).toBe('Integral(sqrt(2)*exp(-(_z - 2)**2/18)/(6*sqrt(pi)), (_z, 2, oo))');
    expect(str(doit(Probability(Gt(new RandomSymbol('R'), 0))))).toBe('Probability(R > 0)');
    // given a random symbol: a Bernoulli distribution, a dependent condition kept, an independent one evaluated
    expect(str(doit(Probability(Gt(X, 2), X)))).toBe('BernoulliDistribution(1/2, 0, 1)');
    expect(str(doit(Probability(Gt(Y, 3), X)))).toBe('1/2');
    expect(str(doit(Probability(Gt(add(X, Y), 0), X)))).toBe('Probability(X + Y > 0, X)');
    expect(rewrite(Probability(Gt(X, 2)), 'Expectation').key).toBe(Probability(Gt(X, 2)).key);
  });
});

describe('Variance and Covariance (SymPy test_literal_probability)', () => {
  it('Variance', () => {
    expect(Variance(w).args.map(str)).toEqual(['w']);
    expect(str(expand(Variance(w)))).toBe('0');
    expect(str(Variance(X).evaluateIntegral())).toBe('9');
    expect(str(doit(rewrite(Variance(X), 'Integral')))).toBe(str(variance(X)));
    expect(str(Variance(add(X, z)))).toBe('Variance(z + X)');
    expect(str(expand(Variance(add(X, z))))).toBe('Variance(X)');
    expect(str(Variance(mul(X, Y)))).toBe('Variance(X*Y)');
    expect(Variance(mul(X, Y))).toBeInstanceOf(VarianceNode);
    expect(str(expand(Variance(mul(z, X))))).toBe('z**2*Variance(X)');
    expect(str(expand(Variance(add(X, Y))))).toBe('2*Covariance(X, Y) + Variance(X) + Variance(Y)');
    expect(str(expand(Variance(add(X, Y, Z, W))))).toBe(
      '2*Covariance(W, X) + 2*Covariance(W, Y) + 2*Covariance(W, Z) + 2*Covariance(X, Y) + 2*Covariance(X, Z) + 2*Covariance(Y, Z) + Variance(W) + Variance(X) + Variance(Y) + Variance(Z)',
    );
    expect(str(expand(Variance(mul(xr, pow(X, 2)))))).toBe('x**2*Variance(X**2)');
    expect(str(expand(Variance(sin(X))))).toBe('Variance(sin(X))');
    expect(str(expand(Variance(mul(xr, sin(X)))))).toBe('x**2*Variance(sin(X))');
    expect(str(doit(Variance(X, Gt(X, 0))))).toBe('Variance(X, X > 0)');
    expect((Variance(X) as VarianceNode).condition).toBeUndefined();
    expect(str(Variance(X).withArgs([Y]))).toBe('Variance(Y)');
    expect(Variance(X).isCommutative).toBe(true);
    expect(str(expand(new VarianceNode([mul(y, z, X).subs(X, y)])))).toBe('0');
  });

  it('Covariance', () => {
    expect(Covariance(w, z).args.map(str)).toEqual(['w', 'z']);
    expect(str(expand(Covariance(w, z)))).toBe('0');
    expect(str(expand(Covariance(X, w)))).toBe('0');
    expect(str(expand(Covariance(w, X)))).toBe('0');
    expect(Covariance(X, Y).args.map(str)).toEqual(['X', 'Y']);
    expect(str(expand(Covariance(add(mul(z, X), 3), Y)))).toBe('z*Covariance(X, Y)');
    expect(Covariance(X, X).args.map(str)).toEqual(['X', 'X']);
    expect(str(expand(Covariance(X, X)))).toBe('Variance(X)');
    expect(str(expand(Covariance(add(mul(z, X), 3), add(mul(w, Y), 4))))).toBe('w*z*Covariance(X, Y)');
    expect(eq(Covariance(X, Y), Covariance(Y, X))).toBe(true);
    expect(str(expand(Covariance(add(X, Y), add(Z, W))))).toBe('Covariance(W, X) + Covariance(W, Y) + Covariance(X, Z) + Covariance(Y, Z)');
    const x = new Sym('x');
    expect(str(expand(Covariance(add(mul(x, X), mul(y, Y)), add(mul(z, Z), mul(w, W)))))).toBe('w*x*Covariance(W, X) + w*y*Covariance(W, Y) + x*z*Covariance(X, Z) + y*z*Covariance(Y, Z)');
    expect(str(expand(Covariance(add(mul(x, pow(X, 2)), mul(y, sin(Y))), add(mul(z, Y, pow(Z, 2)), mul(w, W)))))).toBe(
      'w*x*Covariance(W, X**2) + w*y*Covariance(sin(Y), W) + x*z*Covariance(Y*Z**2, X**2) + y*z*Covariance(Y*Z**2, sin(Y))',
    );
    expect(str(expand(Covariance(X, pow(X, 2))))).toBe('Covariance(X, X**2)');
    expect(str(expand(Covariance(X, sin(X))))).toBe('Covariance(sin(X), X)');
    expect(str(expand(Covariance(pow(X, 2), mul(sin(X), Y))))).toBe('Covariance(sin(X)*Y, X**2)');
    expect(str(Covariance(w, X).evaluateIntegral())).toBe('0');
    // evaluate=False keeps the order of the arguments
    expect(str(Covariance(Y, X, undefined, { evaluate: false }))).toBe('Covariance(Y, X)');
    expect(str(Covariance(X, Y, Gt(X, 0)))).toBe('Covariance(X, Y, X > 0)');
    expect(String((Covariance(X, Y, Gt(X, 0)) as CovarianceNode).condition)).toBe('X > 0');
    expect(str(doit(Covariance(X, Y)))).toBe('Covariance(X, Y)');
    expect(str(Covariance(X, Y).withArgs([X, Z]))).toBe('Covariance(X, Z)');
    expect(Covariance(X, Y).isCommutative).toBe(true);
    // a constant term of a sum is dropped
    expect(str(expand(Covariance(add(X, Y, 1), Z)))).toBe('Covariance(X, Z) + Covariance(Y, Z)');
  });
});

describe('rewriting (SymPy test_probability_rewrite)', () => {
  const W2 = new Sym('W');
  it('in terms of Expectation', () => {
    expect(str(rewrite(Variance(w), 'Expectation'))).toBe('0');
    expect(str(rewrite(Variance(X), 'Expectation'))).toBe('-Expectation(X)**2 + Expectation(X**2)');
    expect(str(rewrite(Variance(X, Y), 'Expectation'))).toBe('-Expectation(X, Y)**2 + Expectation(X**2, Y)');
    expect(str(rewrite(Variance(add(X, z)), 'Expectation'))).toBe('-Expectation(z + X)**2 + Expectation((z + X)**2)');
    expect(str(rewrite(Variance(mul(X, Y)), 'Expectation'))).toBe('-Expectation(X*Y)**2 + Expectation(X**2*Y**2)');
    expect(str(rewrite(Covariance(w, X), 'Expectation'))).toBe('-w*Expectation(X) + Expectation(w*X)');
    expect(str(rewrite(Covariance(X, Y), 'Expectation'))).toBe('Expectation(X*Y) - Expectation(X)*Expectation(Y)');
    expect(str(rewrite(Covariance(X, Y, W), 'Expectation'))).toBe('Expectation(X*Y, W) - Expectation(X, W)*Expectation(Y, W)');
    expect(rewrite(Variance(X), 'cos').key).toBe(Variance(X).key);
    expect(rewrite(Covariance(X, Y), 'cos').key).toBe(Covariance(X, Y).key);
  });

  it('in terms of Probability', () => {
    expect(str(rewrite(Expectation(X), 'Probability'))).toBe('Integral(x*Probability(Eq(X, x)), (x, -oo, oo))');
    expect(str(rewrite(Expectation(Z), 'Probability'))).toBe('Sum(z*Probability(Eq(Z, z)), (z, 0, oo))');
    expect(str(rewrite(Variance(X), 'Probability'))).toBe('-Integral(x*Probability(Eq(X, x)), (x, -oo, oo))**2 + Integral(x**2*Probability(Eq(X, x)), (x, -oo, oo))');
    expect(str(rewrite(Variance(Z), 'Probability'))).toBe('-Sum(z*Probability(Eq(Z, z)), (z, 0, oo))**2 + Sum(z**2*Probability(Eq(Z, z)), (z, 0, oo))');
    expect(str(rewrite(Covariance(W2, X), 'Probability'))).toBe('-W*Integral(x*Probability(Eq(X, x)), (x, -oo, oo)) + Integral(W*x*Probability(Eq(X, x)), (x, -oo, oo))');
    expect(str(rewrite(Variance(X, Y), 'Probability'))).toBe(
      '-Integral(x*Probability(Eq(X, x), Y), (x, -oo, oo))**2 + Integral(x**2*Probability(Eq(X, x), Y), (x, -oo, oo))',
    );
    // a lowercase name gets a suffix; a value that is not random is itself
    const x = Normal('x', 0, 1);
    expect(str(rewrite(Expectation(x), 'Probability'))).toBe('Integral(x_1*Probability(Eq(x, x_1)), (x_1, -oo, oo))');
    expect(str(rewrite(new ExpectationNode([y]), 'Probability'))).toBe('y');
    // SymPy: NotImplementedError for several random symbols and for finite ones
    expect(() => rewrite(Expectation(add(X, Y)), 'Probability')).toThrow('several random symbols');
    expect(() => rewrite(Expectation(Die('D')), 'Probability')).toThrow('finite random symbol');
  });

  it('as integrals and sums', () => {
    expect(str(rewrite(Variance(X), 'Sum'))).toBe(str(rewrite(Variance(X), 'Integral')));
    expect(str(rewrite(Expectation(X), 'Sum'))).toBe(str(rewrite(Expectation(X), 'Integral')));
    expect(str(rewrite(Covariance(W2, X), 'Sum'))).toBe('0');
    expect(str(rewrite(Covariance(W2, X), 'Integral'))).toBe('0');
    expect(str(rewrite(Expectation(Z), 'Sum'))).toBe('Sum(4**Z*Z*exp(-4)/factorial(Z), (Z, 0, oo))');
    expect(str(rewrite(Probability(Gt(X, 2)), 'Sum'))).toBe('Integral(sqrt(2)*exp(-(_z - 2)**2/18)/(6*sqrt(pi)), (_z, 2, oo))');
  });
});

describe('Moment and CentralMoment (SymPy test_symbolic_Moment, test_symbolic_CentralMoment)', () => {
  const mu = new Sym('mu', { real: true });
  const sigma = new Sym('sigma', { positive: true });
  const N = Normal('X', mu, sigma);

  it('Moment', () => {
    const M = Moment(N, 4, 2);
    expect(str(rewrite(M, 'Expectation'))).toBe('Expectation((X - 2)**4)');
    expect(str(rewrite(M, 'Probability'))).toBe('Integral((x - 2)**4*Probability(Eq(X, x)), (x, -oo, oo))');
    expect(str(rewrite(M, 'Integral'))).toBe('Integral(sqrt(2)*(X - 2)**4*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo))');
    expect(str(M.doit())).toBe('mu**4 - 8*mu**3 + 6*mu**2*sigma**2 + 24*mu**2 - 24*mu*sigma**2 - 32*mu + 3*sigma**4 + 24*sigma**2 + 16');
    expect(str(Moment(2, 5).doit())).toBe('32');
    expect(str(Moment(N, 2, 0, Gt(N, 0)))).toBe('Moment(X, 2, 0, X > 0)');
    expect(str(Moment(N, 2).withArgs([N, S.One, S.Zero]))).toBe('Moment(X, 1, 0)');
    expect(rewrite(Moment(N, 2), 'cos').key).toBe(Moment(N, 2).key);
    expect(Moment(N, 2)).toBeInstanceOf(MomentNode);
  });

  it('CentralMoment', () => {
    const CM = CentralMoment(N, 6);
    expect(str(rewrite(CM, 'Expectation'))).toBe('Expectation((-Expectation(X) + X)**6)');
    expect(str(rewrite(CM, 'Probability'))).toBe('Integral((x - Integral(x*Probability(True), (x, -oo, oo)))**6*Probability(Eq(X, x)), (x, -oo, oo))');
    expect(str(rewrite(CM, 'Integral'))).toBe(
      'Integral(sqrt(2)*(X - Integral(sqrt(2)*X*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo)))**6*exp(-(X - mu)**2/(2*sigma**2))/(2*sqrt(pi)*sigma), (X, -oo, oo))',
    );
    expect(str(simplify(CM.doit()))).toBe('15*sigma**6');
    expect(str(Moment(5, 5).doit())).toBe('3125');
    expect(str(CentralMoment(N, 2, Gt(N, 0)))).toBe('CentralMoment(X, 2, X > 0)');
    expect(str(CentralMoment(N, 2).withArgs([N, S.One]))).toBe('CentralMoment(X, 1)');
    expect(rewrite(CentralMoment(N, 2), 'cos').key).toBe(CentralMoment(N, 2).key);
    expect(CentralMoment(N, 2)).toBeInstanceOf(CentralMomentNode);
    expect(str(rewrite(CentralMoment(N, 2, Gt(N, 0)), 'Expectation'))).toBe('Expectation((-Expectation(X, X > 0) + X)**2, X > 0)');
  });
});
