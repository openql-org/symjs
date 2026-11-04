// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/rvinterface.ts (SymPy sympy/stats/rv_interface.py and the
// cases of sympy/stats/tests/test_rv.py, test_continuous_rv.py and
// test_finite_rv.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Gt, Rational, Sym, add, mul, rewrite, str } from '../../src';
import {
  Covariance,
  Die,
  RandomSymbol,
  Variance,
  Exponential,
  Geometric,
  H,
  Normal,
  Poisson,
  Uniform,
  cmoment,
  correlation,
  coskewness,
  covariance,
  entropy,
  factorialMoment,
  kurtosis,
  median,
  moment,
  skewness,
  smoment,
  std,
  variance,
} from '../../src/stats';

const D = Die('D', 6);
const X = Normal('X', 0, 1);
const Y = Normal('Y', 0, 1);

describe('moments', () => {
  it('of a die', () => {
    expect(str(variance(D))).toBe('35/12');
    expect(str(std(D))).toBe('sqrt(105)/6');
    expect(str(moment(D, 2))).toBe('91/6');
    expect(str(moment(D, 1, 6))).toBe('-5/2');
    expect(str(cmoment(D, 2))).toBe('35/12');
    expect(str(smoment(D, 2))).toBe('1');
    expect(str(skewness(D))).toBe('0');
    expect(str(kurtosis(D))).toBe('303/175');
  });

  it('given a condition', () => {
    expect(str(variance(D, Gt(D, 3)))).toBe('2/3');
    expect(str(moment(D, 2, 0, Gt(D, 3)))).toBe('77/3');
    expect(str(cmoment(D, 2, Gt(D, 3)))).toBe('2/3');
    expect(str(std(X, Gt(X, 0)))).toBe('sqrt(1 - 2/pi)');
    expect(str(factorialMoment(Poisson('P', 2), 2))).toBe('4');
  });

  it('unevaluated (evaluate=False)', () => {
    expect(str(moment(X, 2, 0, undefined, { evaluate: false }))).toBe('Integral(sqrt(2)*X**2*exp(-X**2/2)/(2*sqrt(pi)), (X, -oo, oo))');
    expect(str(cmoment(X, 2, undefined, { evaluate: false }))).toBe(
      'Integral(sqrt(2)*(X - Integral(sqrt(2)*X*exp(-X**2/2)/(2*sqrt(pi)), (X, -oo, oo)))**2*exp(-X**2/2)/(2*sqrt(pi)), (X, -oo, oo))',
    );
  });

  it('covariance, correlation and coskewness', () => {
    expect(str(variance(add(X, 3)))).toBe('1');
    expect(str(covariance(X, add(X, Y)))).toBe('1');
    expect(str(correlation(X, add(X, Y)))).toBe('sqrt(2)/2');
    expect(str(coskewness(D, D, D))).toBe('0');
    expect(str(coskewness(X, X, Y))).toBe('0');
  });
});

describe('entropy', () => {
  it('of finite and continuous random symbols, in a base', () => {
    expect(str(entropy(D))).toBe('log(6)');
    expect(str(entropy(D, undefined, { b: 2 }))).toBe('log(6)/log(2)');
    expect(str(entropy(X))).toBe('log(2)/2 + 1/2 + log(pi)/2');
    expect(str(H(Uniform('U', 0, 2)))).toBe('log(2)');
    expect(str(entropy(D, Gt(D, 3)))).toBe('log(3)');
    // the density of a function of a random symbol is a Lambda
    expect(str(entropy(mul(2, X)))).toBe('1/2 + log(pi)/2 + 3*log(2)/2');
  });
});

describe('median', () => {
  it('of finite, continuous and discrete random symbols', () => {
    expect(str(median(D))).toBe('{3, 4}');
    expect(str(median(Die('D4', 4)))).toBe('{2, 3}');
    expect(str(median(X))).toBe('{0}');
    expect(str(median(Normal('N', 3, 1)))).toBe('{3}');
    expect(str(median(Exponential('E', 2)))).toBe('{log(2)/2}');
    // SymPy: ConditionSet(_x, Eq(floor(_x) - 1, 0), Range(1, oo, 1)), the same solutions [1, 2)
    expect(str(median(Geometric('G', Rational.of(1, 2))))).toContain('ConditionSet(_x, ');
  });

  it('of products of spaces', () => {
    // SymPy: ValueError (a product of finite spaces has no cdf) and NotImplementedError
    expect(() => median(add(D, Die('F', 6)))).toThrow('CDF not well defined on multivariate expressions');
    expect(() => median(add(X, Y))).toThrow('The median of IndependentProductPSpace');
  });
});

describe('random symbols without a space and constants', () => {
  it('give the unevaluated nodes or the constant itself', () => {
    const R = new RandomSymbol('R');
    const x = new Sym('x');
    expect(str(variance(R, Gt(R, 0)))).toBe('Variance(R, R > 0)');
    expect(str(covariance(X, R))).toBe('Covariance(R, X)');
    expect(str(median(x))).toBe('x');
    expect(str(rewrite(Variance(X), 'Integral'))).toBe(str(variance(X, undefined, { evaluate: false })));
    expect(str(rewrite(Covariance(X, Y), 'Integral'))).toBe('Expectation((-Expectation(X) + X)*(-Expectation(Y) + Y))');
  });
});
