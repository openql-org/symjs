// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/frv.ts (SymPy sympy/stats/frv.py and
// sympy/stats/tests/test_finite_rv.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, FiniteSet, Gt, Lt, NotImplementedError, Rational, S, Sym, Tuple, add, and, cos, doit, mul, pi, pow, str, sub, symbols } from '../../src';
import type { Expr } from '../../src';
import {
  ConditionalFiniteDomain,
  Coin,
  Die,
  DieDistribution,
  FiniteDensity,
  FinitePSpace,
  ProductFiniteDomain,
  ProductFinitePSpace,
  SingleFiniteDomain,
  SingleFinitePSpace,
  Bernoulli,
  Normal,
  Poisson,
  RademacherDistribution,
  cdf,
  characteristicFunction,
  cmoment,
  correlation,
  covariance,
  density,
  expectation,
  given,
  kurtosis,
  median,
  moment,
  momentGeneratingFunction,
  pspace,
  quantile,
  skewness,
  smoment,
  variance,
  where,
  P,
} from '../../src/stats';
import { finiteElements } from '../../src/stats/frv';

const R = (p: number, q = 1): Expr => Rational.of(p, q);
const t = new Sym('t');
const call = (d: unknown, v: Expr): Expr => (d as { call: (v: Expr) => Expr }).call(v);
const dictStr = (d: unknown): string => {
  const m = d as Map<Expr, Expr>;
  return `{${[...m].map(([k, v]) => `${str(k)}: ${str(v)}`).join(', ')}}`;
};

describe('dice (SymPy test_dice)', () => {
  const [X, Y, Z] = [Die('X', 6), Die('Y', 6), Die('Z', 6)];
  const [a, b, p] = symbols('a b p') as Sym[] as [Sym, Sym, Sym];
  it('expectations, variances and moments', () => {
    expect(str(expectation(X))).toBe('7/2');
    expect(str(variance(X))).toBe('35/12');
    expect(str(expectation(add(X, Y)))).toBe('7');
    expect(str(expectation(add(X, X)))).toBe('7');
    expect(str(expectation(add(mul(a, X), b)))).toBe('7*a/2 + b');
    expect(str(variance(add(X, Y)))).toBe('35/6');
    expect(str(cmoment(add(X, Y), 2))).toBe('35/6');
    expect(str(variance(add(X, X)))).toBe('35/3');
    expect(str(cmoment(X, 0))).toBe('1');
    expect(str(cmoment(mul(4, X), 3))).toBe('0');
    expect(str(covariance(X, Y))).toBe('0');
    expect(str(covariance(X, add(X, Y)))).toBe('35/12');
    expect(str(correlation(X, Y))).toBe('0');
    expect(str(sub(smoment(add(X, Y), 3), skewness(add(X, Y))))).toBe('0');
    expect(str(sub(smoment(add(X, Y), 4), kurtosis(add(X, Y))))).toBe('0');
    expect(str(smoment(X, 0))).toBe('1');
    expect(str(moment(X, 0))).toBe('1');
    expect(str(sub(moment(mul(5, X), 2), mul(25, moment(X, 2))))).toBe('0');
  });
  it('densities', () => {
    expect(str((density(Eq(cos(mul(X, pi)), 1)) as FiniteDensity).get(S.true) as Expr)).toBe('1/2');
    expect(dictStr(density(add(X, Y)))).toBe(dictStr(density(add(Y, Z))));
    expect(dictStr(density(add(X, Y)))).not.toBe(dictStr(density(add(X, X))));
    const d = density(add(mul(2, X), pow(Y, Z))) as FiniteDensity;
    expect(str(d.get(R(22)) as Expr)).toBe('1/108');
    expect(str(d.get(R(4100)) as Expr)).toBe('1/216');
    expect(d.has(R(3130))).toBe(false);
    expect(str(d.call(3130))).toBe('0');
    expect(dictStr(d.dict)).toBe(dictStr(d));
  });
  it('probabilities', () => {
    expect(str(P(Gt(X, 3)))).toBe('1/2');
    expect(str(P(Gt(mul(2, X), 6)))).toBe('1/2');
    expect(str(P(Gt(X, Y)))).toBe('5/12');
    expect(str(P(Eq(X, Y)))).toBe('1/6');
    expect(str(P(Gt(X, 3), Gt(X, 3)))).toBe('1');
    expect(str(P(Gt(X, Y), Eq(Y, 6)))).toBe('0');
    expect(str(P(Eq(add(X, Y), 12)))).toBe('1/36');
    expect(str(P(Eq(add(X, Y), 12), Eq(X, 6)))).toBe('1/6');
    // Bayes
    const A = Gt(X, 3);
    const B = Lt(add(X, Y), 5);
    expect(str(sub(P(A, B), mul(P(and(A, B)), pow(P(B), -1))))).toBe('0');
    expect(str(sub(P(A, B), mul(P(B, A), P(A), pow(P(B), -1))))).toBe('0');
    expect(str(P(Eq(sub(X, Y), Z), Gt(Z, Y)))).toBe('1/15');
  });
  it('conditional expectations', () => {
    expect(str(expectation(X, Gt(X, 3)))).toBe('5');
    expect(str(moment(X, 1, 0, Gt(X, 3)))).toBe('5');
    expect(str(expectation(X, Gt(Y, 3)))).toBe('7/2');
    expect(str(expectation(add(X, Y), Eq(X, Y)))).toBe('7');
  });
  it('quantiles, medians, cdf and transforms', () => {
    expect(str(call(quantile(X), p))).toBe('Piecewise((nan, (p > 1) | (p < 0)), (1, p <= 1/6), (2, p <= 1/3), (3, p <= 1/2), (4, p <= 2/3), (5, p <= 5/6), (6, p <= 1))');
    expect(str(median(X))).toBe('{3, 4}');
    expect(str(median(Die('D', 7)))).toBe('{4}');
    expect(dictStr(cdf(X))).toBe('{1: 1/6, 2: 1/3, 3: 1/2, 4: 2/3, 5: 5/6, 6: 1}');
    expect(str(call(characteristicFunction(X), t))).toBe('exp(6*I*t)/6 + exp(5*I*t)/6 + exp(4*I*t)/6 + exp(3*I*t)/6 + exp(2*I*t)/6 + exp(I*t)/6');
    expect(str(call(momentGeneratingFunction(X), t))).toBe('exp(6*t)/6 + exp(5*t)/6 + exp(4*t)/6 + exp(3*t)/6 + exp(2*t)/6 + exp(t)/6');
    expect((X.pspace as SingleFinitePSpace).sortedCdf(X).map(([k, v]) => `${str(k)}:${str(v)}`).join(',')).toBe('1:1/6,2:1/3,3:1/2,4:2/3,5:5/6,6:1');
  });
  it('domains', () => {
    expect(str(pspace(X).domain.asBoolean())).toBe('Eq(X, 1) | Eq(X, 2) | Eq(X, 3) | Eq(X, 4) | Eq(X, 5) | Eq(X, 6)');
    expect(str(where(Gt(X, 3)).set)).toBe('{4, 5, 6}');
    expect(pspace(X).density).toEqual(new DieDistribution([R(6)]));
  });
});

describe('a symbolic number of sides (SymPy test_dice)', () => {
  const n = new Sym('n', { positive: true });
  const D = Die('D', n);
  const k = new Sym('k');
  it('cdf, characteristic and moment generating functions are sums', () => {
    const c = call(cdf(D), k);
    // SymPy: Sum(Piecewise((1/n, (ki >= 1) & (ki <= n)), (0, True)), (ki, 1, k))
    expect(str(c)).toBe('Sum(Piecewise((Piecewise((1/n, Contains(_ki, Integers) & (_ki >= 1) & (_ki <= n)), (0, True)), (_ki >= 1) & (_ki <= n)), (0, True)), (_ki, 1, k))');
    expect(str(doit(c.subs([[n, 6], [k, 2]])))).toBe('1/3');
    const cf = call(characteristicFunction(D), t);
    expect(str(doit(cf.subs(n, 3)))).toBe('exp(3*I*t)/3 + exp(2*I*t)/3 + exp(I*t)/3');
    const mgf = call(momentGeneratingFunction(D), t);
    expect(str(doit(mgf.subs(n, 3)))).toBe('exp(3*t)/3 + exp(2*t)/3 + exp(t)/3');
  });
  it('the density of a condition, quantile and probability', () => {
    // SymPy: Piecewise((Piecewise((1/n, (m >= 1) & (m <= n)), (0, True)), (m >= 1) & (m <= n) & (m > 2)), (0, True)), where the
    // Dummy k is an integer, so Contains(k, Integers) is True
    expect(str(call(density(Gt(D, 2)), new Sym('m')))).toBe('Piecewise((Piecewise((1/n, Contains(m, Integers) & (m >= 1) & (m <= n)), (0, True)), (m >= 1) & (m <= n) & (m > 2)), (0, True))');
    expect(() => quantile(D)).toThrow('Computing quantile for random variables with symbolic dimension');
    expect(() => P(Gt(D, 2))).toThrow('Currently, probability queries are not supported');
    // SymPy: Sum(Piecewise((_k/n, (_k <= n) & (_k > 2)), (0, True)), (_k, 1, n)) (its Sum folds the Piecewise)
    expect(str(expectation(Gt(D, 2)))).toBe('Sum(Piecewise((_k*Piecewise((1/n, Contains(_k, Integers) & (_k >= 1) & (_k <= n)), (0, True)), _k > 2), (0, True)), (_k, 1, n))');
  });
});

describe('given and domains (SymPy test_given, test_domains)', () => {
  it('given', () => {
    const X = Die('X', 6);
    expect(dictStr(density(X, Gt(X, 5)))).toBe('{6: 1}');
    expect(str(where(Gt(X, 2), Gt(X, 5)).asBoolean())).toBe('Eq(X, 6)');
    const Y = given(X, Gt(X, 3));
    expect(dictStr(density(Y))).toBe('{4: 1/3, 5: 1/3, 6: 1/3}');
    expect((Y as Sym & { pspace: FinitePSpace }).pspace).toBeInstanceOf(FinitePSpace);
  });
  it('domains', () => {
    const [X, Y] = [Die('x', 6), Die('y', 6)];
    const [x, y] = [X.symbol, Y.symbol];
    const d = where(Gt(X, Y)) as ConditionalFiniteDomain;
    expect(d).toBeInstanceOf(ConditionalFiniteDomain);
    expect(d.condition.key).toBe(Gt(x, y).key);
    const d2 = where(and(Gt(X, Y), Gt(Y, 3))) as ConditionalFiniteDomain;
    expect(str(d2.asBoolean())).toBe('(Eq(x, 5) & Eq(y, 4)) | (Eq(x, 6) & Eq(y, 4)) | (Eq(x, 6) & Eq(y, 5))');
    expect(d2.elements().length).toBe(3);
    const pd = pspace(add(X, Y)).domain as ProductFiniteDomain;
    expect(pd).toBeInstanceOf(ProductFiniteDomain);
    expect(pd.elements().length).toBe(36);
    expect(str(pd.set)).toBe('ProductSet({1, 2, 3, 4, 5, 6}, {1, 2, 3, 4, 5, 6})');
    expect(str(pd.asBoolean()).startsWith('(Eq(x, 1) & Eq(y, 1)) |')).toBe(true);
    expect(pd.dict.args.length).toBe(36);
    // two domains with the same internal symbol
    expect(() => P(Gt(X, Die('x', 4)))).toThrow('Overlapping Random Variables');
    expect(str((X.pspace.domain as SingleFiniteDomain).dict)).toBe('{{x: 1}, {x: 2}, {x: 3}, {x: 4}, {x: 5}, {x: 6}}');
    expect((where(Gt(X, Y)) as ConditionalFiniteDomain).dict.args.length).toBe(15);
    expect(() => (where(Gt(X, Y)) as ConditionalFiniteDomain).set).toThrow('Not implemented on multi-dimensional conditional domain');
    const sd = X.pspace.domain as SingleFiniteDomain;
    expect(sd.containsElement([[x, R(3)]])).toBe(true);
    expect(sd.containsElement([[x, R(7)]])).toBe(false);
    // an undecidable condition
    expect(() => (where(Gt(X, new Sym('c'))) as ConditionalFiniteDomain).elements()).toThrow('Undecidable if');
  });
});

describe('coins and symbolic conditions (SymPy test_coins, test_symbolic_conditions)', () => {
  it('coins', () => {
    const [C, D] = [Coin('C'), Coin('D')];
    expect(dictStr(density(Tuple(C, D)))).toBe('{(H, H): 1/4, (H, T): 1/4, (T, H): 1/4, (T, T): 1/4}');
    // SymPy raises a TypeError (it sorts the values H and T); symjs orders them by their sort keys
    expect(dictStr(cdf(C))).toBe('{H: 1/2, T: 1}');
  });
  it('symbolic conditions', () => {
    const B = Bernoulli('B', R(1, 4));
    const D = Die('D', 4);
    const [bs, n] = symbols('b n') as Sym[] as [Sym, Sym];
    expect(str(P(Eq(B, bs)))).toBe('Piecewise((1/4, Eq(b, 1)), (0, True)) + Piecewise((3/4, Eq(b, 0)), (0, True))');
    expect(str(expectation(Gt(D, n)))).toBe('Piecewise((1/4, n < 1), (0, True)) + Piecewise((1/2, n < 2), (0, True)) + Piecewise((3/4, n < 3), (0, True)) + Piecewise((1, n < 4), (0, True))');
  });
});

describe('product spaces', () => {
  const [X, Y] = [Die('X', 2), Die('Y', 2)];
  const ps = pspace(add(X, Y)) as ProductFinitePSpace;
  it('members', () => {
    expect(ps).toBeInstanceOf(ProductFinitePSpace);
    expect(ps.isFinite).toBe(true);
    expect(str(ps.density)).toBe('{{(X, 1), (Y, 1)}: 1/4, {(X, 1), (Y, 2)}: 1/4, {(X, 2), (Y, 1)}: 1/4, {(X, 2), (Y, 2)}: 1/4}');
    expect(str(call(characteristicFunction(add(X, Y)), t))).toBe('exp(4*I*t)/4 + exp(3*I*t)/2 + exp(2*I*t)/4');
    expect(str(call(momentGeneratingFunction(add(X, Y)), t))).toBe('exp(4*t)/4 + exp(3*t)/2 + exp(2*t)/4');
    // SymPy: the cdf (and so the quantile) of a product space is not defined
    expect(() => quantile(add(X, Y))).toThrow('CDF not well defined on multivariate expressions');
    expect(str(expectation(mul(X, Y)))).toBe('9/4');
  });
  it('conditional spaces', () => {
    const Z = given(add(X, Y), Gt(X, Y));
    expect(dictStr(density(Z))).toBe('{3: 1}');
  });
  it('a FinitePSpace of a density keyed by values', () => {
    const fp = new FinitePSpace([X.pspace.domain, new DieDistribution([R(2)])]);
    expect(str(fp.probOf([[X.symbol, R(2)]]))).toBe('1/2');
    expect(str(fp.probOf([[X.symbol, R(3)]]))).toBe('0');
    const fp2 = new FinitePSpace([X.pspace.domain, ps.density]);
    expect(str(fp2.probOf([[X.symbol, R(3)]]))).toBe('0');
    expect(() => fp.probability(Gt(Y, 1))).toThrow('Cannot compare foreign random symbols, Y');
    expect(() => new FinitePSpace([X.pspace.domain, FiniteSet.of(1)]).densityItems).toThrow();
  });
});

describe('the remaining branches of frv', () => {
  it('members of the domains and spaces', () => {
    const [X, Y] = [Die('X', 2), Die('Y', 2)];
    expect((pspace(add(X, Y)).domain as ProductFiniteDomain).isFinite).toBe(true);
    expect((where(Gt(X, Y)) as ConditionalFiniteDomain).isFinite).toBe(true);
    expect(str(X.pspace.pdf)).toBe('Piecewise((1/2, Contains(X, Integers) & (X >= 1) & (X <= 2)), (0, True))');
    expect(X.pspace.where(S.true).key).toBe(X.pspace.domain.key);
    expect(() => finiteElements(Poisson('P', 1).pspace.domain)).toThrow('SingleDiscreteDomain is not a finite domain');
    expect(() => new RademacherDistribution().low).toThrow('RademacherDistribution has no low value');
    expect(() => new RademacherDistribution().high).toThrow('RademacherDistribution has no high value');
  });
  it('a condition with a symbol on the left (SymPy substitutes for the wrong side)', () => {
    const B = Bernoulli('B', R(1, 4));
    const b = new Sym('b');
    // SymPy: Piecewise((1/4, Eq(B, 1)), (0, True)) + Piecewise((3/4, Eq(B, 0)), (0, True)), which leaves the random symbol
    expect(str(P(Eq(B, add(b, 1))))).toBe('Piecewise((1/4, Eq(b, 0)), (0, True)) + Piecewise((3/4, Eq(b, -1)), (0, True))');
    // SymPy: Piecewise((1/4, Eq(B, 1)), (0, True)) + Piecewise((3/4, Eq(B, 0)), (0, True)) (b replaced, B left)
    expect(str(P(Eq(b, B)))).toBe('Piecewise((1/4, Eq(b, 1)), (0, True)) + Piecewise((3/4, Eq(b, 0)), (0, True))');
  });
  it('the conditional space of a product with a continuous space (SymPy: NotImplementedError)', () => {
    expect(() => given(add(Normal('N', 0, 1), Die('D', 6)), Gt(Die('D', 6), 3))).toThrow(NotImplementedError);
  });
});
