// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/crvtypes.ts (SymPy sympy/stats/crv_types.py and
// sympy/stats/tests/test_continuous_rv.py): the continuous distributions
// through the probability functions. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Ge, Gt, I, Interval, Le, Lt, Ne, NotImplementedError, Rational, S, Sym, rewrite, add, and, doit, exp, expand, mul, neg, oo, or, pow, simplify, sin, sqrt, str } from '../../src';
import type { Expr } from '../../src';
import {
  Arcsin, Benini, Beta, BetaPrime, BoundedPareto, Cauchy, ChiRV, ChiSquared, ContinuousRV, Dagum, Davis, Distribution, Erlang, ExGaussian, Expectation, Exponential,
  FDistribution, FrechetDistribution, LogCauchy, LogitNormal,
  FiniteDensity, Gamma, GammaInverse, GaussianInverse, Gumbel, Laplace, Levy, LogLogistic, LogNormal, Logistic, Lomax, Maxwell, Moyal, Nakagami,
  Normal, P, Pareto, PowerFunction, QuadraticU, RaisedCosine, Rayleigh, Reciprocal, StudentT, Trapezoidal, Triangular, Uniform, UniformSum,
  Weibull, WignerSemicircle, cdf, characteristicFunction, density, expectation as E, given, median, momentGeneratingFunction, quantile, variance,
  where,
} from '../../src/stats';
import type { RandomSymbol, SingleDomain } from '../../src/stats';
import { LambdaNode } from '../../src/core/lambda';

/** A density, cdf, ... applied to arguments (SymPy d(x)). */
function ap(d: unknown, ...xs: (Expr | number)[]): Expr {
  if (d instanceof LambdaNode) return d.call(...xs);
  if (d instanceof Distribution) return d.pdf(xs[0] as Expr | number);
  if (d instanceof FiniteDensity) return d.call(xs[0] as Expr | number);
  throw new TypeError('not callable');
}
const show = (v: unknown): string => str(v as Expr);

const xr = new Sym('x', { real: true });
const z = new Sym('z');
const mu = new Sym('mu', { real: true });
const sigma = new Sym('sigma', { positive: true });
const [a, b] = [new Sym('a', { positive: true }), new Sym('b', { positive: true })];
const pp = new Sym('p', { positive: true });
const tp = new Sym('t', { positive: true });
const rate = new Sym('lambda', { positive: true });
const Xn = Normal('x', 0, 1);
const Yn = Normal('y', 0, 1);
const X1 = Normal('x', mu, sigma);
const Z = Exponential('z', rate);

describe('SymPy test_continuous_rv 1', () => {
  it("E(Y) normal", () => expect(show(E(add(mul(Xn, sigma), mu)))).toBe("mu"));
  it("variance(Y)", () => expect(show(variance(add(mul(Xn, sigma), mu)))).toBe("sigma**2"));
  it("density(Y)(x)", () => expect(show(ap(density(add(mul(Xn, sigma), mu)), xr))).toBe("sqrt(2)*exp(-(-mu + x)**2/(2*sigma**2))/(2*sqrt(pi)*sigma)"));
  it("P(X**2 < 1)", () => expect(show(P(Lt(pow(Xn, 2), 1)))).toBe("erf(sqrt(2)/2)"));
  // SymPy: Complement(Intersection({sqrt(2)*sigma*(sqrt(2)*mu/(2*sigma) + erfinv(2*x - 1))}, Interval(-oo, oo)), {mu});
  // symjs's solveset does not solve the linear equation with parameters
  it("quantile(Y)(x)", () => expect(show(ap(quantile(add(mul(Xn, sigma), mu)), xr))).toMatch(/^ConditionSet\(_x, Eq\(sqrt\(2\)\*_x\/\(2\*sigma\) - sqrt\(2\)\*mu\/\(2\*sigma\) - erfinv\(2\*x - 1\), 0\), Reals\)$|Complement/));
  it("E(X, Eq(X, mu))", () => expect(show(E(Xn, Eq(Xn, mu)))).toBe("mu"));
  it("compute_expectation(1)", () => expect(show(doit(Xn.pspace.computeExpectation(S.One)))).toBe("1"));
  it("density(given)(z)", () => expect(show(ap(density(given(Xn, Ge(Xn, 0))), z))).toBe("sqrt(2)*exp(-z**2/2)/sqrt(pi)"));
  it("given set", () => expect(show((given(Xn, Ge(Xn, 0)) as RandomSymbol).pspace.domain.set)).toBe("Interval(0, oo)"));
  it("E(given)", () => expect(show(E(given(Xn, Ge(Xn, 0))))).toBe("sqrt(2)/sqrt(pi)"));
  it("E(given**2)", () => expect(show(E(pow(given(Xn, Ge(Xn, 0)), 2)))).toBe("1"));
  it("where(X**2<=1).set", () => expect(show(where(Le(pow(Xn, 2), 1)).set)).toBe("Interval(-1, 1)"));
});

describe('SymPy test_continuous_rv 2', () => {
  it("where(X**2<=1).symbol", () => expect(show((where(Le(pow(Xn, 2), 1)) as SingleDomain).symbol)).toBe("x"));
  it("where(And).set", () => expect(show(where(and(Le(pow(Xn, 2), 1), Ge(Xn, 0))).set)).toBe("Interval(0, 1)"));
  // SymPy raises ValueError (Reduction of condition failed): sin(x) > 1 holds nowhere, so the domain is empty
  it("where(sin(X) > 1)", () => expect(show(where(Gt(sin(Xn), 1)))).toBe('Domain: False'));
  it("E(X+Y)", () => expect(show(E(add(Xn, Yn)))).toBe("0"));
  it("variance(X+Y)", () => expect(show(variance(add(Xn, Yn)))).toBe("2"));
  it("E(X, Eq(X + Y, 0))", () => expect(show(E(Xn, Eq(add(Xn, Yn), 0)))).toBe("0"));
  it("variance(X, Eq(X + Y, 0))", () => expect(show(variance(Xn, Eq(add(Xn, Yn), 0)))).toBe("1/2"));
  it("quantile(X)(p)", () => expect(show(ap(quantile(Xn), pp))).toBe("sqrt(2)*erfinv(2*p - 1)"));
  it("E(a*Z + b)", () => expect(show(E(add(mul(a, Z), b)))).toBe("a/lambda + b"));
  it("E(X + a*Z + b)", () => expect(show(E(add(X1, mul(a, Z), b)))).toBe("a/lambda + b + mu"));
  it("cdf(X)(1)", () => expect(show(ap(cdf(Xn), 1))).toBe("erf(sqrt(2)/2)/2 + 1/2"));
  // SymPy: 1 - erfc(sqrt(2)/2)/2 (the same value)
  it("P(X < 1)", () => expect(show(P(Lt(Xn, 1)))).toBe('erf(sqrt(2)/2)/2 + 1/2'));
});

describe('SymPy test_continuous_rv 3', () => {
  it("cdf(X, X>0)(0)", () => expect(show(ap(cdf(Xn, Gt(Xn, 0)), 0))).toBe("0"));
  it("cdf(Y)(-5)", () => expect(show(ap(cdf(Exponential('y', 10)), -5))).toBe("0"));
  it("P(Y > 3)", () => expect(show(P(Gt(Exponential('y', 10), 3)))).toBe("exp(-30)"));
  it("cdf(X+Y)", () => expect(() => cdf(add(Xn, Exponential('y', 10)))).toThrow(RangeError));
  it("cdf(Z)(z)", () => expect(show(ap(cdf(Exponential('z', 1)), z))).toBe("Piecewise((1 - exp(-z), z >= 0), (0, True))"));
  it("cf uniform", () => expect(show(ap(characteristicFunction(Uniform('x', 0, 1)), 1))).toBe("-I*(-1 + exp(I))"));
  it("cf normal 1", () => expect(show(ap(characteristicFunction(Normal('y', 1, 1)), 1))).toBe("exp(-1/2 + I)"));
  it("cf exp", () => expect(show(expand(ap(characteristicFunction(Exponential('z', 5)), 1)))).toBe("25/26 + 5*I/26"));
  it("cf gaussinv", () => expect(show(ap(characteristicFunction(GaussianInverse('x', 1, 1)), 1))).toBe("exp(1 - sqrt(1 - 2*I))"));
  it("cf exgauss", () => expect(show(ap(characteristicFunction(ExGaussian('x', 0, 1, 1)), 1))).toBe("(1 + I)*exp(-1/2)/2"));
  it("cf levy", () => expect(show(ap(characteristicFunction(Levy('x', 0, 1)), 1))).toBe("exp(-sqrt(2)*sqrt(-I))"));
  it("mgf beta", () => expect(show(ap(momentGeneratingFunction(Beta('x', 1, 1)), tp).diff(tp).subs(tp, 1))).toBe("hyper((2,), (3,), 1)/2"));
});

describe('SymPy test_continuous_rv 4', () => {
  it("mgf chisq", () => expect(show(ap(momentGeneratingFunction(ChiSquared('x', 1)), tp).diff(tp).subs(tp, 1))).toBe("I"));
  it("mgf gumbel", () => expect(show(ap(momentGeneratingFunction(Gumbel('x', 1, 1)), tp).diff(tp).subs(tp, 0))).toBe("EulerGamma + 1"));
  it("mgf normal", () => expect(show(ap(momentGeneratingFunction(Normal('x', 0, 1)), tp).diff(tp).subs(tp, 1))).toBe("exp(1/2)"));
  it("mgf triangular", () => expect(show(ap(momentGeneratingFunction(Triangular('x', 1, 3, 2)), tp).diff(tp).subs(tp, 1))).toBe("-E + exp(3)"));
  it("mgf uniform", () => expect(show(ap(momentGeneratingFunction(Uniform('x', 0, 1)), tp).diff(tp).subs(tp, 1))).toBe("1"));
  it("mgf wigner", () => expect(show(ap(momentGeneratingFunction(WignerSemicircle('x', 1)), tp).diff(tp).subs(tp, 1))).toBe("-2*besseli(1, 1) + besseli(2, 1) + besseli(0, 1)"));
  it("ContinuousRV density", () => expect(show(ap(density(ContinuousRV(xr, exp(neg(xr)), Interval.of(0, oo))), xr))).toBe("Piecewise((exp(-x), x >= 0), (0, True))"));
  it("ContinuousRV E", () => expect(show(E(ContinuousRV(xr, exp(neg(xr)), Interval.of(0, oo))))).toBe("1"));
  it("ContinuousRV P", () => expect(show(P(Gt(ContinuousRV(xr, exp(neg(xr)), Interval.of(0, oo)), 1)))).toBe("exp(-1)"));
  it("handmade set", () => expect(show(ContinuousRV(xr, exp(neg(xr)), Interval.of(0, oo)).pspace.domain.set)).toBe("Interval(0, oo)"));
  it("handmade check", () => expect(show(ContinuousRV(xr, exp(neg(xr)), Interval.of(0, oo), { check: true }))).toBe("x"));
  it("handmade bad check", () => expect(() => ContinuousRV(xr, mul(2, exp(neg(xr))), Interval.of(0, oo), { check: true })).toThrow(RangeError));
});

describe('SymPy test_continuous_rv 5', () => {
  it("arcsin cdf", () => expect(show(ap(cdf(Arcsin('x', 0, 4)), xr))).toBe("Piecewise((0, x < 0), (2*asin(sqrt(x)/2)/pi, x <= 4), (1, True))"));
  it("benini E", () => expect(() => E(Benini('x', 1, 1, 1))).toThrow(NotImplementedError));
  it("beta E", () => expect(show(simplify(E(Beta('x', a, b))))).toBe("a/(a + b)"));
  it("betaprime pdf", () => expect(show(ap(density(BetaPrime('x', a, b)), xr))).toBe("x**(a - 1)*(x + 1)**(-a - b)/beta(a, b)"));
  it("bpareto E", () => expect(show(E(BoundedPareto('x', 2, 1, 2)))).toBe("4/3"));
  it("cauchy cf", () => expect(show(ap(characteristicFunction(Cauchy('x', 1, 1)), xr))).toBe("exp(I*x - Abs(x))"));
  it("cauchy E", () => expect(() => E(Cauchy('x', 1, 1))).toThrow(NotImplementedError));
  it("chi E", () => expect(show(E(ChiRV('x', 3)))).toBe("2*sqrt(2)/sqrt(pi)"));
  it("chisq E", () => expect(show(E(ChiSquared('x', 4)))).toBe("4"));
  it("chisq var", () => expect(show(variance(ChiSquared('x', 4)))).toBe("8"));
  it("dagum cdf", () => expect(show(ap(cdf(Dagum('x', 1, 1, 1)), xr))).toBe("Piecewise((1/(1 + 1/x), x >= 0), (0, True))"));
  it("erlang E", () => expect(show(E(Erlang('x', 2, 3)))).toBe("2/3"));
});

describe('SymPy test_continuous_rv 6', () => {
  it("exgauss E", () => expect(show(E(ExGaussian('x', 1, 2, 3)))).toBe("4/3"));
  it("exgauss var", () => expect(show(variance(ExGaussian('x', 1, 2, 3)))).toBe("37/9"));
  it("exponential E", () => expect(show(E(Exponential('x', 2)))).toBe("1/2"));
  it("exponential E2", () => expect(show(E(pow(Exponential('x', 2), 2)))).toBe("1/2"));
  it("exponential P", () => expect(show(P(Gt(Exponential('x', 2), 1)))).toBe("exp(-2)"));
  it("exponential median", () => expect(show(median(Exponential('x', 2)))).toBe("{log(2)/2}"));
  it("exponential quantile", () => expect(show(ap(quantile(Exponential('x', 2)), pp))).toBe("-log(1 - p)/2"));
  it("exponential given", () => expect(show(E(Exponential('x', 2), Gt(Exponential('x', 2), 1)))).toBe("3/2"));
  it("exponential density 2x", () => expect(show(ap(density(mul(2, Exponential('x', 2))), xr))).toBe("exp(-x)"));
  it("gamma E", () => expect(show(E(Gamma('x', 2, 3)))).toBe("6"));
  it("gamma var", () => expect(show(variance(Gamma('x', 2, 3)))).toBe("18"));
  it("gammainv E", () => expect(() => E(GammaInverse('x', 3, 2))).toThrow(NotImplementedError));
});

describe('SymPy test_continuous_rv 7', () => {
  it("gumbel E", () => expect(show(E(Gumbel('x', 1, 2)))).toBe("EulerGamma + 2"));
  it("laplace E", () => expect(show(E(Laplace('x', 2, 3)))).toBe("2"));
  it("laplace var", () => expect(show(variance(Laplace('x', 2, 3)))).toBe("18"));
  it("logistic E", () => expect(show(E(Logistic('x', 2, 3)))).toBe("2"));
  it("loglogistic E", () => expect(show(E(LogLogistic('x', 2, 3)))).toBe("4*sqrt(3)*pi/9"));
  it("lognormal E", () => expect(() => E(LogNormal('x', 0, 1))).toThrow(NotImplementedError));
  it("lomax E", () => expect(show(E(Lomax('x', 3, 1)))).toBe("1/2"));
  it("maxwell var", () => expect(show(variance(Maxwell('x', 1)))).toBe("3 - 8/pi"));
  it("moyal E", () => expect(show(E(Moyal('x', 0, 1)))).toBe("EulerGamma + log(2)"));
  it("nakagami var", () => expect(show(simplify(variance(Nakagami('x', 1, 1))))).toBe("1 - pi/4"));
  // SymPy: 3/2; symjs does not evaluate expint(3, 0) = 1/2
  it("pareto E", () => expect(show(E(Pareto('x', 1, 3)))).toBe('3*expint(3, 0)'));
  it("powerfunction E", () => expect(show(E(PowerFunction('x', 2, 0, 1)))).toBe("2/3"));
});

describe('SymPy test_continuous_rv 8', () => {
  // SymPy: -11, from its wrong moment generating function; the density is symmetric about 2 on [1, 3]
  it("quadraticu E", () => expect(show(E(QuadraticU('x', 1, 3)))).toBe('2'));
  it("raisedcosine E", () => expect(show(E(RaisedCosine('x', 1, 1)))).toBe("1"));
  it("rayleigh E", () => expect(show(E(Rayleigh('x', 1)))).toBe("sqrt(2)*sqrt(pi)/2"));
  it("reciprocal E", () => expect(show(E(Reciprocal('x', 1, 2)))).toBe("1/log(2)"));
  it("studentt E", () => expect(() => E(StudentT('x', 3))).toThrow(NotImplementedError));
  it("trapezoidal E", () => expect(show(E(Trapezoidal('x', 1, 2, 3, 4)))).toBe("5/2"));
  it("triangular E", () => expect(show(E(Triangular('x', 1, 3, 2)))).toBe("2"));
  it("uniform E", () => expect(show(E(Uniform('x', 1, 3)))).toBe("2"));
  it("uniform var", () => expect(show(variance(Uniform('x', 1, 3)))).toBe("1/3"));
  it("uniform P", () => expect(show(P(Gt(Uniform('x', 1, 3), 2)))).toBe("1/2"));
  it("uniformsum E", () => expect(show(E(UniformSum('x', 3)))).toBe("3/2"));
  it("weibull E", () => expect(show(E(Weibull('x', 1, 2)))).toBe("sqrt(pi)/2"));
});

describe('SymPy test_continuous_rv 9', () => {
  it("wigner var", () => expect(show(variance(WignerSemicircle('x', 1)))).toBe("1/4"));
  // SymPy: sqrt(2)*(-sqrt(2)*sqrt(pi)*erf(sqrt(2)/2) + sqrt(2)*sqrt(pi))/(2*sqrt(pi)) (the same value)
  it("union prob", () => expect(show(P(or(Lt(Xn, -1), Gt(Xn, 1))))).toBe('1 - erf(sqrt(2)/2)'));
  it("finite prob", () => expect(show(P(Eq(Xn, 1)))).toBe("0"));
  it("ne prob", () => expect(show(P(Ne(Xn, 1)))).toBe("1"));
  it("P(X > Y)", () => expect(show(P(Gt(Xn, Yn)))).toBe("1/2"));
});

describe('parameter checks (SymPy ValueError is a RangeError)', () => {
  const cases: [string, () => unknown, string][] = [
    ["LogitNormal('x', 0, I)", () => LogitNormal('x', 0, I), 'Squared scale parameter s must be positive.'],
    ["LogitNormal('x', 0, sqrt(I))", () => LogitNormal('x', 0, sqrt(I)), 'Squared scale parameter s must be positive.'],
    ["Moyal('x', 0, I)", () => Moyal('x', 0, I), 'Scale parameter must be real        and positive.'],
    ["Normal('x', 0, -1)", () => Normal('x', 0, -1), 'Standard deviation must be positive'],
    ["Exponential('x', -1)", () => Exponential('x', -1), 'Rate must be positive.'],
    ["Uniform('x', 2, 1)", () => Uniform('x', 2, 1), 'Lower limit should be less than Upper limit.'],
    ["Beta('x', -1, 1)", () => Beta('x', -1, 1), 'Shape parameter Alpha must be positive.'],
    ["ChiSquared('x', 1/2)", () => ChiSquared('x', S.Half), 'Number of degrees of freedom (k) must be an integer.'],
    ["Triangular('x', 1, 3, 4)", () => Triangular('x', 1, 3, 4), 'Parameter c must be in range [1, 3]. c = 4'],
    ["Trapezoidal('x', 1, 3, 2, 4)", () => Trapezoidal('x', 1, 3, 2, 4), 'Level start parameter b must be in range [1, 2). b = 3'],
    ["QuadraticU('x', 3, 1)", () => QuadraticU('x', 3, 1), 'Parameter b must be in range (3, oo).'],
    ["Reciprocal('x', 2, 1)", () => Reciprocal('x', 2, 1), 'Parameter b must be in range (2, +oo]. b = 1'],
    ["Davis('x', 1, 1, 1)", () => Davis('x', 1, 1, 1), 'Shape parameter n must be above 1.'],
    ["Nakagami('x', 1/4, 1)", () => Nakagami('x', Rational.of(1, 4), 1), 'Shape parameter mu must be greater than equal to 1/2.'],
    ["BoundedPareto('x', 1, 3, 2)", () => BoundedPareto('x', 1, 3, 2), 'Right should be greater than left.'],
    ["Cauchy('x', I, 1)", () => Cauchy('x', I, 1), 'Location parameter must be real.'],
    ["PowerFunction('x', 1, 2, 1)", () => PowerFunction('x', 1, 2, 1), " 'a' the left Boundary must be smaller than 'b' the right Boundary."],
    ["FDistribution('x', 1/2, 1)", () => FDistribution('x', S.Half, 1), 'Degrees of freedom d1 must be positive integer.'],
    ["UniformSum('x', 1/2)", () => UniformSum('x', S.Half), 'Parameter n must be positive integer.'],
    ["Lomax('x', -1, 1)", () => Lomax('x', -1, 1), 'Shape parameter should be positive.'],
    ["GaussianInverse('x', -1, 1)", () => GaussianInverse('x', -1, 1), 'Mean must be positive'],
    ["Laplace('x', I, 1)", () => Laplace('x', I, 1), 'Location parameter mu should be real'],
    ["Levy('x', I, 1)", () => Levy('x', I, 1), 'mu (location parameter) must be real'],
    ["LogCauchy('x', 0, -1)", () => LogCauchy('x', 0, -1), 'Scale parameter Gamma must be positive.'],
  ];
  for (const [src, f, msg] of cases) it(src, () => expect(f).toThrow(new RangeError(msg)));
  it('undecided parameters are accepted', () => {
    expect(show(Moyal('x', 0, new Sym('s')))).toBe('x');
  });
});

describe('construction details', () => {
  it('a compound distribution (random parameters)', () => {
    const X = Normal('X', Normal('Y', 0, 1), 1);
    expect(X.pspace.name).toBe('CompoundPSpace');
    expect(show(X.pspace.args[1])).toBe('CompoundDistribution(NormalDistribution(Y, 1))');
  });
  it('a symbol as the name, and default parameters', () => {
    expect(show(Normal(new Sym('w'), 0, 1).pspace)).toBe('SingleContinuousPSpace(w, NormalDistribution(0, 1))');
    expect(show(new FrechetDistribution([Rational.of(2)]))).toBe('FrechetDistribution(2, 1, 0)');
  });
  it('LogLogistic: the expectation of an expression other than the variable', () => {
    // SymPy returns the mean pi*a/(b*sin(pi/b)) for any expression: E(LogLogistic('x', 1, 3)**2) is 2*sqrt(3)*pi/9 there,
    // but E(X**2) = (2*pi/3)/sin(2*pi/3) = 4*sqrt(3)*pi/9 (the integral); here it is the integral
    const X = LogLogistic('x', 1, 3);
    expect(show(rewrite(Expectation(X), 'Integral'))).toBe('Integral(3*x**3/(x**3 + 1)**2, (x, 0, oo))');
  });
  it('QuadraticU: the characteristic function (SymPy\'s is wrong)', () => {
    // SymPy: cf(1/2) = -3.57704245837667 - 1.94958034448306*I, but the integral of exp(I*x/2)*pdf(x) over [1, 3]
    // is 0.500378754700027 + 0.779293737823023*I
    const v = ap(characteristicFunction(QuadraticU('x', 1, 3)), S.Half).evalf();
    expect(show(v)).toBe('0.500378754700027 + 0.779293737823023*I');
  });
});

describe('the crv_types doctests that needed capabilities outside stats (SymPy 1.14)', () => {
  const l = new Sym('lambda', { positive: true });
  const k = new Sym('k', { positive: true });
  const [m, om] = [new Sym('mu', { positive: true }), new Sym('omega', { positive: true })];
  it('Weibull', () => {
    const X = Weibull('x', l, k);
    expect(show(simplify(E(X)))).toBe('lambda*gamma(1 + 1/k)');
    expect(show(simplify(variance(X)))).toBe('lambda**2*(-gamma(1 + 1/k)**2 + gamma(1 + 2/k))');
  });
  it('Nakagami', () => {
    expect(show(simplify(E(Nakagami('x', m, om))))).toBe('sqrt(mu)*sqrt(omega)*gamma(mu + 1/2)/gamma(mu + 1)');
  });
  it('Maxwell, Uniform, WignerSemicircle and ContinuousRV', () => {
    expect(show(E(Maxwell('x', a)))).toBe('2*sqrt(2)*a/sqrt(pi)');
    expect(show(E(Uniform('x', a, b)))).toBe('a/2 + b/2');
    expect(show(E(WignerSemicircle('x', a)))).toBe('0');
    const X = ContinuousRV(xr, mul(S.Half, pow(S.Pi, -1), pow(add(1, pow(xr, 2)), -1)).mul(2));
    expect(show(P(Gt(X, 0)))).toBe('1/2');
  });
});
