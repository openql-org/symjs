// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/drvtypes.ts (SymPy sympy/stats/drv_types.py and
// sympy/stats/tests/test_discrete_rv.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Dummy, Float, Integers, Lambda, Naturals, Rational, S, Sym, add, diff, doit, exp, expand, ff, hyperexpand, mul, parse, pow, simplify, str, sub } from '../../src';
import type { Expr } from '../../src';
import {
  DiscreteRV,
  DiscreteDistributionHandmade,
  ExpectationNode,
  FlorySchulz,
  Geometric,
  GeometricDistribution,
  Hermite,
  Logarithmic,
  NegativeBinomial,
  Poisson,
  PoissonDistribution,
  Skellam,
  YuleSimon,
  Zeta,
  ZetaDistribution,
  cdf,
  characteristicFunction,
  density,
  expectation,
  kurtosis,
  momentGeneratingFunction,
  quantile,
  skewness,
  variance,
  P,
} from '../../src/stats';
import type { Distribution } from '../../src/stats';
import { FiniteSet, Gt, Lt } from '../../src';

const R = (p: number, q = 1): Expr => Rational.of(p, q);
const t = new Sym('t');
const z = new Sym('z');
const x = new Sym('x');
const call = (d: unknown, v: Expr): Expr => (d as { call: (v: Expr) => Expr }).call(v);
const dist = (X: Expr): Distribution => density(X) as Distribution;

describe('the distributions (SymPy drv_types)', () => {
  const a = new Sym('a', { positive: true });
  const p = new Sym('p', { positive: true });
  const r = new Sym('r', { positive: true });
  const l = new Sym('lamda', { positive: true });
  const rho = new Sym('rho', { positive: true });
  const s = new Sym('s', { positive: true });
  const a1 = new Sym('a1', { positive: true });
  const a2 = new Sym('a2', { positive: true });
  const mu1 = new Sym('mu1', { positive: true });
  const mu2 = new Sym('mu2', { positive: true });
  // [distribution, pdf at z, characteristic function at t, moment generating function at t, set]
  const cases: [Expr, string, string, string, string][] = [
    [FlorySchulz('X', a), 'a**2*z*(1 - a)**(z - 1)', 'a**2*exp(I*t)/((a - 1)*exp(I*t) + 1)**2', 'a**2*exp(t)/((a - 1)*exp(t) + 1)**2', 'Naturals'],
    [Geometric('X', p), 'p*(1 - p)**(z - 1)', 'p*exp(I*t)/(-(1 - p)*exp(I*t) + 1)', 'p*exp(t)/(-(1 - p)*exp(t) + 1)', 'Naturals'],
    [Logarithmic('X', p), '-p**z/(z*log(1 - p))', 'log(-p*exp(I*t) + 1)/log(1 - p)', 'log(-p*exp(t) + 1)/log(1 - p)', 'Naturals'],
    [NegativeBinomial('X', r, p), 'p**r*(1 - p)**z*binomial(r + z - 1, z)', '(p/(-(1 - p)*exp(I*t) + 1))**r', '(p/(-(1 - p)*exp(t) + 1))**r', 'Naturals0'],
    [Poisson('X', l), 'lamda**z*exp(-lamda)/factorial(z)', 'exp(lamda*(exp(I*t) - 1))', 'exp(lamda*(exp(t) - 1))', 'Naturals0'],
    [Hermite('X', a1, a2), 'exp(-a1 - a2)*Sum(a1**(-2*_j + z)*a2**_j/(factorial(_j)*factorial(-2*_j + z)), (_j, 0, floor(z/2)))', 'exp(a1*(exp(I*t) - 1) + a2*(exp(2*I*t) - 1))', 'exp(a1*(exp(t) - 1) + a2*(exp(2*t) - 1))', 'Naturals0'],
    [Skellam('X', mu1, mu2), '(mu1/mu2)**(z/2)*exp(-mu1 - mu2)*besseli(z, 2*sqrt(mu1)*sqrt(mu2))', 'exp(mu1*exp(I*t) - mu1 - mu2 + mu2*exp(-I*t))', 'exp(mu1*exp(t) - mu1 - mu2 + mu2*exp(-t))', 'Integers'],
    [YuleSimon('X', rho), 'rho*beta(z, rho + 1)', 'rho*exp(I*t)*hyper((1, 1), (rho + 2,), exp(I*t))/(rho + 1)', 'rho*exp(t)*hyper((1, 1), (rho + 2,), exp(t))/(rho + 1)', 'Naturals'],
    [Zeta('X', s), '1/(z**s*zeta(s))', 'polylog(s, exp(I*t))/zeta(s)', 'polylog(s, exp(t))/zeta(s)', 'Naturals'],
  ];
  for (const [X, pdf, cf, mgf, set] of cases) {
    it(dist(X).name, () => {
      expect(str(dist(X).pdf(z))).toBe(pdf);
      expect(str(call(characteristicFunction(X), t))).toBe(cf);
      expect(str(call(momentGeneratingFunction(X), t))).toBe(mgf);
      expect(str(dist(X).set)).toBe(set);
    });
  }

  it('reject invalid parameters (SymPy ValueError)', () => {
    expect(() => FlorySchulz('X', 2)).toThrow('a must be between 0 and 1');
    expect(() => Geometric('X', 2)).toThrow('p must be between 0 and 1');
    expect(() => Hermite('H', new Sym('a1', { positive: true }), new Sym('a2', { negative: true }))).toThrow('Parameter a2 must be >= 0.');
    expect(() => Hermite('H', new Sym('a1', { negative: true }), new Sym('a2', { positive: true }))).toThrow('Parameter a1 must be >= 0.');
    expect(() => Logarithmic('X', 2)).toThrow('p should be between 0 and 1');
    expect(() => NegativeBinomial('X', -1, R(1, 2))).toThrow('r should be positive');
    expect(() => NegativeBinomial('X', 1, 2)).toThrow('p should be between 0 and 1');
    expect(() => Poisson('X', -1)).toThrow('Lambda must be positive');
    expect(() => Skellam('X', -1, 1)).toThrow('Parameter mu1 must be >= 0');
    expect(() => Skellam('X', 1, -1)).toThrow('Parameter mu2 must be >= 0');
    expect(() => YuleSimon('X', -1)).toThrow('rho should be positive');
    expect(() => Zeta('X', 1)).toThrow('s should be greater than 1');
  });
});

describe('Poisson (SymPy test_PoissonDistribution, test_Poisson)', () => {
  it('the distribution', () => {
    const p = new PoissonDistribution([R(3)]);
    expect(Math.abs(doit(p.cdf(10)).evalf().toNumber() - 1)).toBeLessThan(0.001);
    expect(Math.abs(doit(p.cdf(new Float(10.4))).evalf().toNumber() - 1)).toBeLessThan(0.001);
    expect(str(p.expectation(x, x))).toBe('3');
    expect(str(sub(p.expectation(pow(x, 2), x), pow(p.expectation(x, x), 2)))).toBe('3');
  });
  it('the random symbol', () => {
    const X = Poisson('x', 3);
    expect(str(expectation(X))).toBe('3');
    expect(str(expectation(mul(2, X)))).toBe('6');
    expect(str(variance(X))).toBe('3');
    expect(density(X)).toEqual(new PoissonDistribution([R(3)]));
    expect(expectation(X, undefined, { evaluate: false })).toBeInstanceOf(ExpectationNode);
    expect(expectation(mul(2, X), undefined, { evaluate: false })).toBeInstanceOf(ExpectationNode);
    // issue 8248
    expect(str(X.pspace.computeExpectation(S.One))).toBe('1');
    const Z = Poisson('z', 5);
    expect(str(expectation(ff(Z, 3)))).toBe('125');
    expect(str(expectation(pow(Z, 2)))).toBe('30');
    const n = new Sym('n', { integer: true, positive: true });
    expect(str(expectation(ff(Z, n)))).toBe('5**n');
    expect(str(new PoissonDistribution([R(5)]).expectation(x, x, { evaluate: false }))).toBe('Sum(5**x*x*exp(-5)/factorial(x), (x, 0, oo))');
    // the falling factorial shortcut needs a positive integer order
    expect(str(expectation(ff(Z, R(1, 2))))).toBe('Sum(5**z*exp(-5)*FallingFactorial(z, 1/2)/factorial(z), (z, 0, oo))');
    // an expression that is not a polynomial is summed (SymPy: exp(-lamda)*exp(E*lamda))
    const l = new Sym('lamda', { positive: true });
    expect(str(expectation(exp(Poisson('X', l))))).toBe('exp(-lamda)*exp(E*lamda)');
  });
  it('the summation fallbacks', () => {
    const l = new Sym('lamda', { positive: true });
    const d = new PoissonDistribution([l]);
    // SymPy leaves the sum unevaluated (its summation variable is a real Dummy)
    expect(str(call(d.computeCharacteristicFunction(), t))).toBe('exp(-lamda)*exp(lamda*exp(I*t))');
    expect(str(call(d.computeMomentGeneratingFunction(), t))).toBe('exp(-lamda)*exp(lamda*exp(t))');
    // SymPy: Piecewise(((-lamda**(-floor(z) - 1)*lamda**(floor(z) + 1)*(floor(z) + 1)*exp(lamda)*lowergamma(floor(z) + 1, lamda)/factorial(floor(z) + 1) + exp(lamda))*exp(-lamda), z >= 0), (0, True))
    expect(str(cdf(Poisson('X', l)) as Expr)).toBe(
      'Lambda(_x, Piecewise((-lamda**(-floor(_x) - 1)*lamda**(floor(_x) + 1)*(floor(_x) + 1)*lowergamma(floor(_x) + 1, lamda)/gamma(floor(_x) + 2) + 1, _x >= 0), (0, True)))',
    );
    // SymPy sums the mass function up to its own summation variable: Piecewise((_x, z <= (exp(lamda) - sinh(lamda))*exp(-lamda)))
    expect(str(call(quantile(Poisson('X', l)), z))).toBe('Piecewise((_x, z <= 1 - exp(-lamda)*sinh(lamda)))');
  });
});

describe('the other distributions (SymPy test_discrete_rv)', () => {
  it('FlorySchulz', () => {
    const a = new Sym('a');
    const X = FlorySchulz('x', a);
    expect(str(expectation(X))).toBe('-1 + 2/a');
    expect(str(simplify(sub(variance(X), parse('2*(1 - a)/a**2'))))).toBe('0');
    expect(str(call(density(X), z))).toBe('a**2*z*(1 - a)**(z - 1)');
  });
  it('Geometric', () => {
    const p = R(1, 5);
    const d = new GeometricDistribution([p]);
    expect(str(d.expectation(x, x))).toBe('5');
    expect(str(sub(d.expectation(pow(x, 2), x), pow(d.expectation(x, x), 2)))).toBe('20');
    expect(str(d.cdf(5))).toBe('2101/3125');
    const G = Geometric('G', R(1, 4));
    expect(str(call(cdf(G), R(7, 2)))).toBe('37/64');
    expect(str(P(Gt(G, R(7, 2))))).toBe('27/64');
    expect(str(call(new GeometricDistribution([R(1, 3)]).computeCdf(), z))).toBe('Piecewise((1 - 3*(2/3)**(floor(z) + 1)/2, z >= 1), (0, True))');
  });
  it('Hermite', () => {
    const a1 = new Sym('a1', { positive: true });
    const a2 = new Sym('a2', { positive: true });
    expect(str(expectation(Hermite('H', a1, a2)))).toBe('a1 + 2*a2');
    const H = Hermite('H', 5, 4);
    expect(str(call(density(H), R(2)))).toBe('33*exp(-9)/2');
    expect(str(expectation(H))).toBe('13');
    expect(str(variance(H))).toBe('21');
    expect(str(kurtosis(H))).toBe('464/147');
    expect(str(skewness(H))).toBe('37*sqrt(21)/441');
  });
  it('Logarithmic', () => {
    const X = Logarithmic('x', S.Half);
    expect(str(expectation(X))).toBe('1/log(2)');
    expect(str(variance(X))).toBe('-1/log(2)**2 + 2/log(2)');
    expect(str(expectation(add(mul(2, pow(X, 2)), mul(3, X), 4)))).toBe('4 + 7/log(2)');
  });
  it('NegativeBinomial', () => {
    const X = NegativeBinomial('x', 5, R(1, 3));
    expect(str(expectation(X))).toBe('10');
    expect(str(variance(X))).toBe('30');
    expect(str(expectation(add(pow(X, 5), mul(2, X), 3)))).toBe('796473');
  });
  it('Skellam', () => {
    const mu1 = new Sym('mu1');
    const mu2 = new Sym('mu2');
    const X = Skellam('x', mu1, mu2);
    expect(str(call(density(X), z))).toBe('(mu1/mu2)**(z/2)*exp(-mu1 - mu2)*besseli(z, 2*sqrt(mu1*mu2))');
    // SymPy 1.14
    expect(str(expand(skewness(X)))).toBe('mu1/(mu1*sqrt(mu1 + mu2) + mu2*sqrt(mu1 + mu2)) - mu2/(mu1*sqrt(mu1 + mu2) + mu2*sqrt(mu1 + mu2))');
    expect(str(expand(variance(X)))).toBe('mu1 + mu2');
    expect(str(expectation(X))).toBe('mu1 - mu2');
    // SymPy: Skellam has no closed form of the cdf
    expect(() => cdf(X)).toThrow("Skellam doesn't have closed form for the CDF.");
  });
  it('YuleSimon', () => {
    const X = YuleSimon('x', 3);
    expect(str(simplify(expectation(X)))).toBe('3/2');
    expect(str(simplify(variance(X)))).toBe('9/4');
    expect(str(call(cdf(X), x))).toBe('Piecewise((-beta(floor(x), 4)*floor(x) + 1, x >= 1), (0, True))');
  });
  it('Zeta', () => {
    const X = Zeta('x', 5);
    expect(str(expectation(X))).toBe('pi**4/(90*zeta(5))');
    expect(str(simplify(variance(X)))).toBe('(-pi**8/8100 + zeta(3)*zeta(5))/zeta(5)**2');
    expect(str(new ZetaDistribution([R(5)]).pdf(2))).toBe('1/(32*zeta(5))');
  });
  it('the derivatives of the moment generating functions at 0 (SymPy test_moment_generating_functions)', () => {
    const d1 = (X: Expr): string => str(diff(call(momentGeneratingFunction(X), t), t).subs(t, 0));
    expect(d1(Geometric('g', S.Half))).toBe('2');
    expect(d1(Logarithmic('l', S.Half))).toBe('1/log(2)');
    expect(d1(NegativeBinomial('n', 5, R(1, 3)))).toBe('10');
    expect(d1(Poisson('p', 5))).toBe('5');
    expect(d1(Zeta('z', 5))).toBe('pi**4/(90*zeta(5))');
    expect(str(diff(call(momentGeneratingFunction(Skellam('s', 1, 1)), t), t).subs(t, 2))).toBe('(-exp(-2) + exp(2))*exp(-2 + exp(-2) + exp(2))');
    // SymPy simplify expands the hypergeometric functions at 1 (hyperexpand)
    expect(str(hyperexpand(diff(call(momentGeneratingFunction(YuleSimon('y', 3)), t), t).subs(t, 0)))).toBe('3/2');
  });
});

describe('DiscreteRV (SymPy test_DiscreteRV)', () => {
  it('a mass function on a set', () => {
    const xp = new Sym('x', { integer: true, positive: true });
    const pdf = mul(S.Half, pow(S.Half, sub(xp, 1)));
    const D = DiscreteRV(xp, pdf, Naturals, { check: true });
    expect(str(expectation(D))).toBe('2');
    expect(str(P(Gt(D, 3)))).toBe('1/8');
    expect(str(D.pspace.domain.set)).toBe('Naturals');
    expect(() => DiscreteRV(xp, xp, FiniteSet.of(0, 1, 2, 3), { check: true })).toThrow('The pdf is incorrect on the given set.');
    // an invalid mass function is not checked by default
    const X = DiscreteRV(xp, pow(xp, -1), Naturals);
    expect(str(P(Lt(X, 2)))).toBe('1');
    expect(str(expectation(X))).toBe('oo');
  });
  it('the handmade distribution', () => {
    const k = new Dummy('k');
    const d = new DiscreteDistributionHandmade([Lambda(k, pow(S.Half, k))]);
    expect(d.set).toBe(Integers);
    expect(str(d.pdf(2))).toBe('1/4');
    expect(() => d.check()).not.toThrow();
  });
  it('random parameters give a compound distribution; the name may be a symbol', () => {
    expect(Poisson('X', Poisson('Y', 1)).pspace.name).toBe('CompoundPSpace');
    expect(Poisson(new Sym('X'), 1).pspace.name).toBe('SingleDiscretePSpace');
  });
  it('the default set of a DiscreteRV', () => {
    const xi = new Sym('x', { integer: true });
    expect(str(DiscreteRV(xi, S.Zero).pspace.domain.set)).toBe('Integers');
  });
});

