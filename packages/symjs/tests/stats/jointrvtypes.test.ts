// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/jointrvtypes.ts (SymPy sympy/stats/joint_rv_types.py
// and sympy/stats/tests/test_joint_rv.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Indexed, IndexedBase, Matrix, MatrixSymbol, NotImplementedError, Rational, S, Sym, add, doit, evalf, exp, mul, pow, simplify, str, sub, sympify } from '../../src';
import type { Expr } from '../../src';
import {
  Dirichlet,
  GeneralizedMultivariateLogGamma,
  GeneralizedMultivariateLogGammaOmega,
  JointDistributionHandmade,
  JointRV,
  JointRandomSymbol,
  Laplace,
  Multinomial,
  MultivariateBeta,
  MultivariateEwens,
  MultivariateLaplace,
  MultivariateNormal,
  MultivariateNormalDistribution,
  MultivariateT,
  NegativeMultinomial,
  Normal,
  NormalGamma,
  density,
  expectation,
  marginalDistribution,
  median,
} from '../../src/stats';
import type { JointDistribution, JointPSpace } from '../../src/stats';

const [x, y] = [new Sym('x'), new Sym('y')];
const s = (e: unknown): string => str(e as Expr);
const dens = (X: Expr, ...v: (Expr | number | IndexedBase)[]): Expr => (density(X) as JointDistribution).call(...(v as Expr[]));
const marg = (X: Expr, ...idx: (Expr | number | number[])[]): ((...v: (Expr | number)[]) => Expr) => {
  const l = marginalDistribution(X as JointRandomSymbol, ...idx) as Expr & { call(...v: (Expr | number)[]): Expr };
  return (...v) => l.call(...v);
};
const distOf = (X: Expr): JointDistribution => (X as JointRandomSymbol).pspace.valueDensity as JointDistribution;
const half = S.Half;

describe('MultivariateNormal (SymPy test_Normal)', () => {
  it('numeric parameters', () => {
    const m = Normal('A', [1, 2], [[1, 0], [0, 1]]);
    const A = MultivariateNormal('A', [1, 2], [[1, 0], [0, 1]]);
    expect(m.key).toBe(A.key);
    expect(s(dens(m, 1, 2))).toBe('1/(2*pi)');
    expect(s(distOf(m).set)).toBe('ProductSet(Reals, Reals)');
    expect(() => (m as JointRandomSymbol).at(2)).toThrow(RangeError);
    const n = Normal('B', [1, 2, 3], [[1, 0, 0], [0, 1, 0], [0, 0, 1]]);
    const p = Normal('C', Matrix.col(1, 2), Matrix.of([[1, 0], [0, 1]]));
    expect(dens(m, x, y).key).toBe(dens(p, x, y).key);
    expect(s(marg(n, 0, 1)(1, 2))).toBe('1/(2*pi)');
    expect(() => marginalDistribution(m)).toThrow(RangeError);
    const N = Normal('N', [1, 2], [[x, 0], [0, y]]);
    // SymPy: exp(-(4*x + y)/(2*x*y))/(2*pi*sqrt(x*y)), the same value
    expect(s(simplify(sub(dens(N, 0, 0), mul(exp(mul(-1, add(mul(4, x), y), pow(mul(2, x, y), -1))), pow(mul(2, S.Pi, pow(mul(x, y), half)), -1)))))).toBe('0');
    expect(() => Normal('M', [1, 2], [[1, 1], [1, -1]])).toThrow('The covariance matrix must be positive semi definite. ');
    expect(() => MultivariateNormal('M', [1, 2], [[1, 0, 0], [0, 1, 0], [0, 0, 1]])).toThrow('Size of the mean vector and covariance matrix are incorrect.');
    expect(() => median(m)).toThrow(NotImplementedError);
    // issue 21057: a zero covariance matrix
    expect(Normal('x', [0, 0], [[0, 0], [0, 0]]).key).toBe(MultivariateNormal('x', [0, 0], [[0, 0], [0, 0]]).key);
  });
  it('symbolic parameters', () => {
    const n = new Sym('n', { integer: true, positive: true });
    const mu = MatrixSymbol('mu', n, 1);
    const sigma = MatrixSymbol('sigma', n, n);
    const X = Normal('X', mu, sigma);
    expect((density(X) as Expr).key).toBe(new MultivariateNormalDistribution([mu, sigma]).key);
    const Sg = MatrixSymbol('Sg', n, n);
    const obs = MatrixSymbol('obs', n, 1);
    const X2 = MultivariateNormal('X', mu, Sg);
    // SymPy: (exp(((1/2)*mu.T - (1/2)*obs.T)*Sg**(-1)*(-mu + obs))/sqrt((2*pi)**n*Determinant(Sg)))[0, 0]
    // (symjs takes the positive factor (2*pi)**n out of the square root)
    expect(s(dens(X2, obs))).toBe('(exp(((1/2)*mu.T - (1/2)*obs.T)*Sg**(-1)*(-mu + obs))/((2*pi)**(n/2)*sqrt(Determinant(Sg))))[0, 0]');
    const Sg3 = MatrixSymbol('Sg', 3, 3);
    const mu3 = MatrixSymbol('mu', 3, 1);
    const X3 = MultivariateNormal('X', mu3, Sg3);
    expect(s(dens(X3, MatrixSymbol('obs', 3, 1)))).toBe('(sqrt(2)*exp(((1/2)*mu.T - (1/2)*obs.T)*Sg**(-1)*(-mu + obs))/(4*pi**(3/2)*sqrt(Determinant(Sg))))[0, 0]');
    // SymPy: density_X(obs).subs({Sg: eye(3), mu: Matrix([0, 0, 0]), obs: Matrix([0, 0, 0])}).doit() == sqrt(2)/(4*pi**(3/2));
    // here the density at an explicit point of a symbolic distribution
    const X4 = MultivariateNormal('X', Matrix.col(0, 0, 0), Matrix.eye(3));
    expect(s(dens(X4, 0, 0, 0))).toBe('sqrt(2)/(4*pi**(3/2))');
  });
  it('expectation (SymPy test_expectation)', () => {
    const m = Normal('A', [x, y], [[1, 0], [0, 1]]) as JointRandomSymbol;
    expect(s(simplify(expectation(m.at(1))))).toBe('y');
    expect(s(expectation(m.at(0), undefined, { evaluate: false }))).toBe('Expectation(A[0])');
  });
});

describe('MultivariateT (SymPy test_MultivariateTDist)', () => {
  it('densities', () => {
    const t1 = MultivariateT('T', [0, 0], [[1, 0], [0, 1]], 2);
    expect(s(dens(t1, 1, 1))).toBe('1/(8*pi)');
    expect(s(distOf(t1).set)).toBe('ProductSet(Reals, Reals)');
    expect(() => MultivariateT('T', [1, 2], [[1, 1], [1, -1]], 1)).toThrow('The shape matrix must be positive definite. ');
    expect(() => MultivariateT('T', [1, 2], [[1]], 1)).toThrow('Size of the location vector and shape matrix are incorrect.');
    const t2 = MultivariateT('t2', [1, 2], [[x, 0], [0, y]], 1);
    expect(s(dens(t2, 1, 2))).toBe('1/(2*pi*sqrt(x*y))');
    expect(s((distOf(t1) as unknown as { dof: Expr }).dof)).toBe('2');
  });
  it('marginal distribution (SymPy test_JointPSpace_marginal_distribution)', () => {
    const T = MultivariateT('T', [0, 0], [[1, 0], [0, 1]], 2) as JointRandomSymbol;
    // SymPy: sqrt(2)*(x**2/2 + 1)/(4*polar_lift(x**2/2 + 1)**(5/2)), and at x = 0 sqrt(2)*exp_polar(0)/4
    expect(s(doit(marg(T, T.at(1))(0)))).toBe('sqrt(2)*exp_polar(0)/4');
  });
});

describe('MultivariateLaplace (SymPy test_multivariate_laplace)', () => {
  it('densities', () => {
    expect(() => Laplace('T', [1, 2], [[1, 2], [2, 1]])).toThrow('The covariance matrix must be positive definite. ');
    expect(() => MultivariateLaplace('T', [1, 2], [[1]])).toThrow('Size of the mean vector and covariance matrix are incorrect.');
    const L = Laplace('L', [1, 0], [[1, 0], [0, 1]]);
    const L2 = MultivariateLaplace('L2', [1, 0], [[1, 0], [0, 1]]);
    expect(s(dens(L, 2, 3))).toBe('exp(2)*besselk(0, sqrt(39))/pi');
    const L1 = Laplace('L1', [1, 2], [[x, 0], [0, y]]);
    expect(s(dens(L1, 0, 1))).toBe('exp(2/y)*besselk(0, sqrt((2 + 4/y + 1/x)/y))/(pi*sqrt(x*y))');
    expect(s(distOf(L).set)).toBe('ProductSet(Reals, Reals)');
    expect(distOf(L).key).toBe(distOf(L2).key);
    // scalar parameters give the univariate distributions
    expect(s(Laplace('S', 0, 1).pspace)).toBe('SingleContinuousPSpace(S, LaplaceDistribution(0, 1))');
    expect(() => Laplace('S', 0, [1])).toThrow(TypeError);
    expect(() => Normal('S', [0], 1)).toThrow(TypeError);
  });
});

describe('NormalGamma (SymPy test_NormalGamma)', () => {
  it('densities and marginals', () => {
    const ng = NormalGamma('G', 1, 2, 3, 4);
    expect(s(dens(ng, 1, 1))).toBe('32*exp(-4)/sqrt(pi)');
    expect(s(distOf(ng).set)).toBe('ProductSet(Reals, Interval(0, oo))');
    expect(() => NormalGamma('G', 1, 2, 3, -1)).toThrow('beta must be positive');
    expect(s(marg(ng, 0)(1))).toBe('3*sqrt(10)*gamma(7/4)/(10*sqrt(pi)*gamma(5/4))');
    expect(s(marg(ng, y)(1))).toBe('exp(-1/4)/128');
    expect(s(marg(ng, [0, 1])(x))).toBe('x**2*exp(-x/4)/128');
    expect(s(marginalDistribution(ng as JointRandomSymbol, 1))).toBe('Lambda(G, G**2*exp(-G/4)/128)');
    // SymPy self.pdf(*sym) with one symbol: TypeError
    expect(() => marginalDistribution(ng as JointRandomSymbol, 0, 1)).toThrow(TypeError);
  });
});

describe('GeneralizedMultivariateLogGamma (SymPy test_GeneralizedMultivariateLogGammaDistribution)', () => {
  const omega = Matrix.of([
    [1, half, half, half],
    [half, 1, half, half],
    [half, half, 1, half],
    [half, half, half, 1],
  ]);
  const [v, l, mu] = [4, [1, 2, 3, 4], [1, 2, 3, 4]];
  const ys = [1, 2, 3, 4].map((i) => new Sym(`y_${i}`, { real: true }));
  const delta = new Sym('d', { positive: true });
  it('densities', () => {
    const G = GeneralizedMultivariateLogGammaOmega('G', omega, v, l, mu);
    const Gd = GeneralizedMultivariateLogGamma('Gd', delta, v, l, mu);
    expect(s(dens(Gd, ...ys))).toBe(
      'd**4*Sum(4*24**(-n - 4)*(1 - d)**n*exp((n + 4)*(y_1 + 2*y_2 + 3*y_3 + 4*y_4) - exp(y_1) - exp(2*y_2)/2 - exp(3*y_3)/3 - exp(4*y_4)/4)/(gamma(n + 1)*gamma(n + 4)**3), (n, 0, oo))',
    );
    expect(s(dens(G, ...ys))).toBe(
      '5*2**(2/3)*5**(1/3)*Sum(4*24**(-n - 4)*(-2**(2/3)*5**(1/3)/4 + 1)**n*exp((n + 4)*(y_1 + 2*y_2 + 3*y_3 + 4*y_4) - exp(y_1) - exp(2*y_2)/2 - exp(3*y_3)/3 - exp(4*y_4)/4)/(gamma(n + 1)*gamma(n + 4)**3), (n, 0, oo))/64',
    );
    expect(s(distOf(G))).toBe('GeneralizedMultivariateLogGammaDistribution(2**(2/3)*5**(1/3)/4, 4, Matrix([[1], [2], [3], [4]]), Matrix([[1], [2], [3], [4]]))');
    expect(s(distOf(G).set)).toBe('ProductSet(Reals, Reals, Reals, Reals)');
    const g = distOf(G) as unknown as { delta: Expr; v: Expr; lamda: Expr; mu: Expr };
    expect([g.delta, g.v, g.lamda, g.mu].map(s)).toEqual(['2**(2/3)*5**(1/3)/4', '4', 'Matrix([[1], [2], [3], [4]])', 'Matrix([[1], [2], [3], [4]])']);
  });
  it('invalid parameters', () => {
    const omegaF1 = [[1, half, half]];
    const omegaF2 = Matrix.of([[1, half, half, half], [half, 1, 2, half], [half, half, 1, half], [half, half, half, 1]]);
    const omegaF3 = Matrix.of([[6, half, half, half], [half, 1, 2, half], [half, half, 1, half], [half, half, half, 1]]);
    // SymPy symbols('v_f', positive=False, real=True): nonpositive
    const vF = new Sym('v_f', { nonpositive: true });
    const lF = [1, 2, vF, 4];
    const mF = [vF, 2, 3, 4];
    const omegaF4 = Matrix.fromFunction(5, 5, (i, j) => (i === j ? 1 : half));
    const GO = GeneralizedMultivariateLogGammaOmega;
    expect(() => GO('G', omegaF1, v, l, mu)).toThrow(RangeError);
    expect(() => GO('G', omegaF2, v, l, mu)).toThrow(RangeError);
    expect(() => GO('G', omegaF3, v, l, mu)).toThrow(RangeError);
    expect(() => GO('G', omega, vF, l, mu)).toThrow(RangeError);
    expect(() => GO('G', omega, v, lF, mu)).toThrow(RangeError);
    expect(() => GO('G', omega, v, l, mF)).toThrow(RangeError);
    expect(() => GO('G', omegaF4, v, l, mu)).toThrow(RangeError);
    expect(() => GO('G', omega, v, [1, 2, 3, 4, 5], mu)).toThrow(RangeError);
    expect(() => GO('G', Matrix.of([[1]]), v, [1], [1])).toThrow(RangeError);
    expect(() => GeneralizedMultivariateLogGamma('G', Rational.of(3n, 2n), v, l, mu)).toThrow(RangeError);
    expect(() => GeneralizedMultivariateLogGamma('G', half, v, [1], [1])).toThrow('the distribution should have at least two random variables.');
  });
});

describe('MultivariateBeta (SymPy test_MultivariateBeta)', () => {
  it('densities', () => {
    const [a1, a2] = [new Sym('a1', { positive: true }), new Sym('a2', { positive: true })];
    // SymPy symbols('a1, a2', positive=False, real=True): nonpositive
    const [a1f, a2f] = [new Sym('a1', { nonpositive: true }), new Sym('a2', { nonpositive: true })];
    const mb = MultivariateBeta('B', [a1, a2]);
    const mbc = MultivariateBeta('C', a1, a2);
    expect(s(dens(mb, 1, 2))).toBe('2**(a2 - 1)*gamma(a1 + a2)/(gamma(a1)*gamma(a2))');
    expect(s(marg(mbc, 0)(3))).toBe('3**(a1 - 1)*gamma(a1 + a2)/(a2*gamma(a1)*gamma(a2))');
    expect(() => MultivariateBeta('b1', [a1f, a2])).toThrow(RangeError);
    expect(() => MultivariateBeta('b2', [a1, a2f])).toThrow(RangeError);
    expect(() => MultivariateBeta('b3', [0, 0])).toThrow(RangeError);
    expect(() => MultivariateBeta('b4', [a1f, a2f])).toThrow(RangeError);
    expect(() => MultivariateBeta('b5', [a1])).toThrow('At least two categories should be passed.');
    expect(s(distOf(mb).set)).toBe('ProductSet(Interval(0, 1), Interval(0, 1))');
    expect(s(distOf(mb))).toBe('MultivariateBetaDistribution(Matrix([[a1], [a2]]))');
    expect(Dirichlet).toBe(MultivariateBeta);
  });
});

describe('MultivariateEwens (SymPy test_MultivariateEwens)', () => {
  const n = new Sym('n', { positive: true });
  const theta = new Sym('theta', { positive: true });
  it('integer dimension', () => {
    const thetaF = new Sym('t_f', { negative: true });
    const a = [1, 2, 3].map((i) => new Sym(`a_${i}`, { positive: true, integer: true })) as [Sym, Sym, Sym];
    const ed = MultivariateEwens('E', 3, theta) as JointRandomSymbol;
    expect(s(dens(ed, ...a))).toBe(
      'Piecewise((6*theta**a_1*theta**a_2*theta**a_3/(2**a_2*3**a_3*theta*(theta + 1)*(theta + 2)*factorial(a_1)*factorial(a_2)*factorial(a_3)), Eq(a_1 + 2*a_2 + 3*a_3, 3)), (0, True))',
    );
    expect(s(marg(ed, ed.at(1))(a[1]))).toBe('Piecewise((6*theta**a_2/(2**a_2*(theta + 1)*(theta + 2)*factorial(a_2)), Eq(a_2, 1)), (0, True))');
    expect(() => MultivariateEwens('e1', 5, thetaF)).toThrow('mutation rate should be positive.');
    expect(() => MultivariateEwens('e1', -1, theta)).toThrow('sample size should be positive integer.');
    expect(s(distOf(ed).set)).toBe('ProductSet(Range(0, 4, 1), Range(0, 2, 1), Range(0, 2, 1))');
    expect(s((distOf(ed) as unknown as { theta: Expr }).theta)).toBe('theta');
  });
  it('symbolic dimension', () => {
    const eds = MultivariateEwens('E', n, theta);
    expect(s(dens(eds, new IndexedBase('a')))).toBe(
      'Piecewise((factorial(n)*Product(theta**a[j]/((j + 1)**a[j]*factorial(a[j])), (j, 0, n - 1))/RisingFactorial(theta, n), Eq(n, Sum((k + 1)*a[k], (k, 0, n - 1)))), (0, True))',
    );
    expect(() => dens(eds, x)).toThrow('Please use IndexedBase object for syms as the dimension is symbolic');
    // SymPy: Product(Intersection(Interval(0, floor(n/i)), Naturals0), (i, 1, n)), a product of sets
    expect(() => distOf(eds).set).toThrow(NotImplementedError);
  });
});

describe('Multinomial (SymPy test_Multinomial)', () => {
  const n = new Sym('n', { nonnegative: true, integer: true });
  const xs = [1, 2, 3, 4].map((i) => new Sym(`x${i}`, { nonnegative: true, integer: true })) as [Sym, Sym, Sym, Sym];
  const ps = [1, 2, 3, 4].map((i) => new Sym(`p${i}`, { positive: true })) as [Sym, Sym, Sym, Sym];
  it('densities and marginals', () => {
    const [p1f, nf] = [new Sym('p1_f', { negative: true }), new Sym('n_f', { negative: true })];
    const M = Multinomial('M', n, ps);
    const C = Multinomial('C', 3, ps[0], ps[1], ps[2]) as JointRandomSymbol;
    expect(s(dens(M, ...xs))).toBe('Piecewise((p1**x1*p2**x2*p3**x3*p4**x4*factorial(n)/(factorial(x1)*factorial(x2)*factorial(x3)*factorial(x4)), Eq(n, x1 + x2 + x3 + x4)), (0, True))');
    expect(s(marg(C, C.at(0))(xs[0]).subs(xs[0], 1))).toBe('3*p1*p2**2 + 6*p1*p2*p3 + 3*p1*p3**2');
    expect(() => Multinomial('b1', 5, [ps[0], ps[1], ps[2], p1f])).toThrow(RangeError);
    expect(() => Multinomial('b2', nf, ps)).toThrow(RangeError);
    expect(() => Multinomial('b3', n, 0.5, 0.4, 0.3, 0.1)).toThrow(RangeError);
    expect(s(distOf(M).set)).toBe(
      'ProductSet(Intersection(Interval(0, n), Naturals0), Intersection(Interval(0, n), Naturals0), Intersection(Interval(0, n), Naturals0), Intersection(Interval(0, n), Naturals0))',
    );
    expect(s(distOf(C).set)).toBe('ProductSet(Range(0, 4, 1), Range(0, 4, 1), Range(0, 4, 1))');
    // a symbolic number of trials: the sum over Intersection(Interval(0, n), Naturals0) is not implemented (as in SymPy)
    expect(() => marginalDistribution(M as JointRandomSymbol, 0)).toThrow(NotImplementedError);
    expect(s((distOf(M) as unknown as { p: Expr }).p)).toBe('Matrix([[p1], [p2], [p3], [p4]])');
  });
  it('doctests (sympy.stats.joint_rv_types)', () => {
    const M = Multinomial('M', 3, ps[0], ps[1], ps[2]) as JointRandomSymbol;
    expect(s(marg(M, M.at(0))(xs[0]).subs(xs[0], 1))).toBe('3*p1*p2**2 + 6*p1*p2*p3 + 3*p1*p3**2');
  });
  it('expectations are sums (SymPy: TypeError, it integrates over Range limits)', () => {
    const Q = Multinomial('Q', 2, [half, half]) as JointRandomSymbol;
    expect(s(expectation(Q.at(0)))).toBe('1');
  });
});

describe('NegativeMultinomial (SymPy test_NegativeMultinomial)', () => {
  it('densities and marginals', () => {
    const xs = [1, 2, 3, 4].map((i) => new Sym(`x${i}`, { nonnegative: true, integer: true })) as [Sym, Sym, Sym, Sym];
    const ps = [1, 2, 3, 4].map((i) => new Sym(`p${i}`, { positive: true })) as [Sym, Sym, Sym, Sym];
    const p1f = new Sym('p1_f', { negative: true });
    const N = NegativeMultinomial('N', 4, ps);
    const C = NegativeMultinomial('C', 4, 0.1, 0.2, 0.3) as JointRandomSymbol;
    expect(s(dens(N, ...xs))).toBe('p1**x1*p2**x2*p3**x3*p4**x4*(-p1 - p2 - p3 - p4 + 1)**4*gamma(x1 + x2 + x3 + x4 + 4)/(6*factorial(x1)*factorial(x2)*factorial(x3)*factorial(x4))');
    expect(s(evalf(marg(C, C.at(0))(1)))).toBe('0.327680000000000');
    expect(() => NegativeMultinomial('b1', 5, [ps[0], ps[1], ps[2], p1f])).toThrow(RangeError);
    expect(() => NegativeMultinomial('b2', new Sym('k0', { nonnegative: true, integer: true }), 0.5, 0.4, 0.3, 0.4)).toThrow(RangeError);
    expect(() => NegativeMultinomial('b3', -1, 0.5)).toThrow('number of failures must be a positive integer');
    expect(s(distOf(N).set)).toBe('ProductSet(Range(0, oo, 1), Range(0, oo, 1), Range(0, oo, 1), Range(0, oo, 1))');
    expect(s((distOf(N) as unknown as { k0: Expr }).k0)).toBe('4');
  });
  it('doctests (sympy.stats.joint_rv_types)', () => {
    const Nc = NegativeMultinomial('N', 3, 0.1, 0.1, 0.1) as JointRandomSymbol;
    expect(s(evalf(marg(Nc, Nc.at(0))(1), 2))).toBe('0.25');
  });
});

describe('JointRV (SymPy test_JointRV)', () => {
  it('handmade joint densities', () => {
    const [x1, x2] = [1, 2].map((i) => new Indexed([x, sympify(i)])) as [Indexed, Indexed];
    const pdf = mul(exp(add(mul(-1, half, pow(x1, 2)), x1, mul(-1, half, pow(x2, 2)), mul(-1, half))), pow(mul(2, S.Pi), -1));
    const X = JointRV('x', pdf);
    expect(s(dens(X, 1, 2))).toBe('exp(-2)/(2*pi)');
    expect(distOf(X)).toBeInstanceOf(JointDistributionHandmade);
    expect(s(distOf(X))).toBe('JointDistributionHandmade(Lambda((x[1], x[2]), exp(-x[1]**2/2 + x[1] - x[2]**2/2 - 1/2)/(2*pi)), ProductSet(Reals, Reals))');
    expect(s(marg(X, 0)(2))).toBe('sqrt(2)*exp(-1/2)/(2*sqrt(pi))');
    expect(s((distOf(X) as JointDistributionHandmade).pdfLambda)).toBe('Lambda((x[1], x[2]), exp(-x[1]**2/2 + x[1] - x[2]**2/2 - 1/2)/(2*pi))');
    expect(JointRV(new Sym('y'), mul(new Indexed([y, sympify(0)]), 2)).pspace).toBeDefined();
  });
});

describe('the pspace of a joint random symbol', () => {
  it('is a JointPSpace', () => {
    const X = MultivariateNormal('X', [0], [[1]]);
    expect((X.pspace as JointPSpace).componentCount.key).toBe(sympify(1).key);
  });
});

describe('the kinds of the joint distributions (SymPy is_Continuous, is_Discrete)', () => {
  it('continuous and discrete', () => {
    const cont = [MultivariateNormal('a', [0], [[1]]), MultivariateLaplace('b', [0, 0], [[1, 0], [0, 1]]), MultivariateT('c', [0], [[1]], 2), MultivariateBeta('d', 1, 2), GeneralizedMultivariateLogGamma('e', half, 1, [1, 2], [1, 2]), NormalGamma('n', 0, 1, 1, 1)];
    expect(cont.map((X) => distOf(X).isContinuous)).toEqual([true, true, true, true, true, true]);
    const disc = [MultivariateEwens('f', 2, 1), Multinomial('g', 2, half, half), NegativeMultinomial('h', 2, Rational.of(1n, 3n))];
    expect(disc.map((X) => distOf(X).isDiscrete)).toEqual([true, true, true]);
    expect(disc.map((X) => distOf(X).isContinuous)).toEqual([false, false, false]);
  });
  it('an explicit vector, an IndexedBase among integer dimensions', () => {
    const X = MultivariateNormal('X', [0, 0], [[1, 0], [0, 1]]);
    expect(s(dens(X, Matrix.col(0, 0) as unknown as Expr))).toBe('1/(2*pi)');
    expect(s(dens(MultivariateNormal('a', [0], [[1]]), 0))).toBe('sqrt(2)/(2*sqrt(pi))');
    const theta = new Sym('theta', { positive: true });
    expect(s(dens(MultivariateEwens('E', 1, theta), new IndexedBase('a')))).toBe('Piecewise((theta**a/(theta*factorial(a)), Eq(a, 1)), (0, True))');
    // a scalar parameter in place of a vector
    expect(s(dens(MultivariateBeta('B', [1, 2]), half, half))).toBe('1');
  });
});
