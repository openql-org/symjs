// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/drv.ts (SymPy sympy/stats/drv.py and
// sympy/stats/tests/test_discrete_rv.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, FiniteSet, Ge, Gt, Interval, Lambda, Naturals, Le, Lt, Ne, NotImplementedError, Rational, S, Sym, add, and, cos, mul, oo, or, pow, rewrite, simplify, str, sub, Xor } from '../../src';
import { defined } from '../../src/core/guard';
import { statsClasses } from '../../src/stats/rv';
import type { DensityResult } from '../../src/stats';
import type { Expr } from '../../src';
import {
  ConditionalDiscreteDomain,
  DiscreteRV,
  SingleDiscreteDistribution,
  DiscretePSpace,
  Geometric,
  GeometricDistribution,
  Poisson,
  PoissonDistribution,
  ProbabilityNode,
  ProductDiscreteDomain,
  SingleDiscreteDomain,
  SingleDiscretePSpace,
  Skellam,
  cdf,
  characteristicFunction,
  coskewness,
  density,
  expectation,
  given,
  momentGeneratingFunction,
  pspace,
  quantile,
  where,
  P,
} from '../../src/stats';

const R = (p: number, q = 1): Expr => Rational.of(p, q);
const z = new Sym('z');
const x = new Sym('x');
const t = new Sym('t');
const call = (d: unknown, v: Expr): Expr => (d as { call: (v: Expr) => Expr }).call(v);

describe('probabilities (SymPy test_discrete_probability)', () => {
  const X = Geometric('X', R(1, 5));
  const Y = Poisson('Y', 4);
  it('of a geometric random variable', () => {
    expect(str(P(Eq(X, 3)))).toBe('16/125');
    expect(str(P(Lt(X, 3)))).toBe('9/25');
    expect(str(P(Gt(X, 3)))).toBe('64/125');
    expect(str(P(Ge(X, 3)))).toBe('16/25');
    expect(str(P(Le(X, 3)))).toBe('61/125');
    expect(str(P(Ne(X, 3)))).toBe('109/125');
    expect(str(P(Gt(X, oo)))).toBe('0');
    const G = Geometric('e', x);
    // SymPy: x*(2 - x)
    expect(str(P(Lt(G, 3)))).toBe('x*(1 - x) + x');
    expect(str(P(Eq(G, 3)))).toBe('x*(1 - x)**2');
  });
  it('of a Poisson random variable', () => {
    expect(str(P(Eq(Y, 3)))).toBe('32*exp(-4)/3');
    expect(str(P(Lt(Y, 3)))).toBe('13*exp(-4)');
    expect(str(P(Gt(Y, 3)))).toBe('32*(-71/32 + 3*exp(4)/32)*exp(-4)/3');
    expect(str(P(Ge(Y, 3)))).toBe('32*(-39/32 + 3*exp(4)/32)*exp(-4)/3');
    expect(str(P(Le(Y, 3)))).toBe('71*exp(-4)/3');
    // SymPy: 13*exp(-4) + 32*(-71/32 + 3*exp(4)/32)*exp(-4)/3
    expect(str(P(Ne(Y, 3)))).toBe('1 - 32*exp(-4)/3');
  });
  it('X < oo', () => {
    expect(str(P(Lt(X, oo)))).toBe('1');
  });
  it('coskewness (SymPy test_GeometricDistribution)', () => {
    const Y2 = Geometric('Y', R(3, 10));
    expect(str(simplify(coskewness(X, add(X, Y2), add(X, mul(2, Y2)))))).toBe('81*sqrt(230)/1150');
    const G = Geometric('G', R(1, 4));
    expect(str(sub(call(cdf(G), R(7, 2)), P(Le(G, R(7, 2)))))).toBe('0');
  });
  it('of disjunctions (SymPy test_Or)', () => {
    const Xh = Geometric('X', S.Half);
    expect(str(P(or(Lt(Xh, 3), Gt(Xh, 4))))).toBe('13/16');
    expect(str(P(or(Gt(Xh, 2), Gt(Xh, 1))))).toBe('1/2');
    expect(str(P(or(Ge(Xh, 3), Lt(Xh, 3))))).toBe('1');
  });
  it('given conditions (SymPy test_conditional)', () => {
    const Xc = Geometric('X', R(2, 3));
    const Yc = Poisson('Y', 3);
    expect(str(P(Gt(Xc, 2), Gt(Xc, 3)))).toBe('1');
    expect(str(P(Gt(Xc, 3), Gt(Xc, 2)))).toBe('1/3');
    expect(str(P(Gt(Yc, 2), Lt(Yc, 2)))).toBe('0');
    expect(str(P(Eq(Yc, 3), Ge(Yc, 0)))).toBe('9*exp(-3)/2');
    expect(str(P(Eq(Yc, 3), Eq(Yc, 2)))).toBe('0');
    expect(str(P(Lt(Xc, 2), Eq(Xc, 2)))).toBe('0');
    expect(str(P(Gt(Xc, 2), Eq(Xc, 3)))).toBe('1');
  });
  it('of a sum of independent random variables (SymPy test_product_spaces)', () => {
    const X1 = Geometric('X1', S.Half);
    const X2 = Geometric('X2', R(1, 3));
    // SymPy: Sum(Piecewise((1/(4*2**n), n >= -1), (0, True)), (n, -oo, -1))/3 (a Piecewise whose condition
    // bounds X2 by a parameter is not summed here)
    expect(str(rewrite(P(Lt(add(X1, X2), 3)), 'Sum'))).toBe('Sum(Sum((2/3)**(X2 - 1)*Piecewise(((1/2)**(-X2 + n + 2)/2, X2 - n <= 2), (0, True))/3, (X2, 1, oo)), (n, -oo, -1))');
    // SymPy's 1/12 is wrong: X1 + X2 = 3 for (1, 2) and (2, 1), with probability (1/2)*(2/9) + (1/4)*(1/3) = 7/36
    expect(str(P(Eq(add(X1, X2), 3)))).toBe('7/36');
  });
});

describe('domains (SymPy test_where)', () => {
  const X = Geometric('X', R(1, 5));
  const Y = Poisson('Y', 4);
  it('where', () => {
    expect(str(where(Gt(pow(X, 2), 4)).set)).toBe('Range(3, oo, 1)');
    expect(str(where(Ge(pow(X, 2), 4)).set)).toBe('Range(2, oo, 1)');
    expect(str(where(Lt(pow(Y, 2), 9)).set)).toBe('Range(0, 3, 1)');
    expect(str(where(Le(pow(Y, 2), 9)).set)).toBe('Range(0, 4, 1)');
    expect(str(where(Gt(X, 3)))).toBe('Domain: Contains(X, Range(4, oo, 1))');
    expect(where(Gt(X, 3))).toBeInstanceOf(SingleDiscreteDomain);
  });
  it('the domain of several random variables', () => {
    // SymPy: NotImplementedError of the product space
    expect(() => where(Gt(X, Y))).toThrow(NotImplementedError);
    const d = pspace(add(X, Y)).domain;
    expect(d).toBeInstanceOf(ProductDiscreteDomain);
    expect(d.isDiscrete).toBe(true);
  });
  it('a conditional domain', () => {
    const Yg = given(Y, Gt(Y, 2));
    const ps = (Yg as Sym & { pspace: DiscretePSpace }).pspace;
    expect(ps).toBeInstanceOf(DiscretePSpace);
    const dom = ps.domain as ConditionalDiscreteDomain;
    expect(dom).toBeInstanceOf(ConditionalDiscreteDomain);
    expect(dom.isDiscrete).toBe(true);
    expect(str(dom.set)).toBe('Range(3, oo, 1)');
    expect(str(dom.condition)).toBe('Y > 2');
    // SymPy: 4**Y/((-13 + exp(4))*factorial(Y))
    expect(str(ps.pdf)).toBe('3*4**Y/(32*(-39/32 + 3*exp(4)/32)*factorial(Y))');
    expect(() => new ConditionalDiscreteDomain([pspace(add(X, Y)).domain, Gt(X, 2)]).set).toThrow('Multivariate conditional domains are not yet implemented.');
  });
});

describe('the summation fallbacks of SingleDiscreteDistribution', () => {
  it('compute_quantile, compute_cdf and the characteristic and moment generating functions', () => {
    const d = new GeometricDistribution([R(1, 3)]);
    expect(str(call(d.computeQuantile(), z))).toBe('Piecewise((_x, z <= 1 - 3*(2/3)**(_x + 1)/2))');
    // SymPy leaves both sums unevaluated (its summation variable is a real Dummy)
    expect(str(call(d.computeMomentGeneratingFunction(), z))).toBe('Piecewise((exp(z)/(3*(1 - 2*exp(z)/3)), exp(z) < 3/2), (Sum((2/3)**(_x - 1)*exp(_x*z)/3, (_x, 1, oo)), True))');
    expect(str(call(d.computeCharacteristicFunction(), z))).toBe('exp(I*z)/(3*(1 - 2*exp(I*z)/3))');
    expect(str(call(quantile(Geometric('X', R(1, 3))), z))).toBe('Piecewise((_x, z <= 1 - 3*(2/3)**(_x + 1)/2))');
    expect(str(d.quantile(S.Half))).toBe('Piecewise((_x, (2/3)**(_x + 1) <= 1/3))');
    expect(str(d.characteristicFunction(0))).toBe('1');
  });
  it('expectations that are not polynomials', () => {
    const X = Geometric('X', S.Half);
    // SymPy: oo ((1/2)**(X - 1)*2**X is not combined to 2 here)
    expect(str(expectation(pow(2, X)))).toBe('Sum((1/2)**(X - 1)*2**X/2, (X, 1, oo))');
    // SymPy: Sum(2**(1 - X)*cos(X)/2, (X, 1, oo))
    expect(str(expectation(cos(X)))).toBe('Sum((1/2)**(X - 1)*cos(X)/2, (X, 1, oo))');
  });
  it('unevaluated expectation', () => {
    const d = new PoissonDistribution([R(3)]);
    expect(str(d.expectation(pow(x, 2), x, { evaluate: false }))).toBe('Sum(3**x*x**2*exp(-3)/factorial(x), (x, 0, oo))');
  });
});

describe('SingleDiscretePSpace', () => {
  const X = Poisson('X', 2);
  const ps = X.pspace as SingleDiscretePSpace;
  it('members', () => {
    expect(ps.isReal).toBe(true);
    expect(ps.isDiscrete).toBe(true);
    expect(ps.isSingle).toBe(true);
    expect(str(ps.symbol)).toBe('X');
    expect(str(ps.pdf)).toBe('2**X*exp(-2)/factorial(X)');
    expect(str(ps.set)).toBe('Naturals0');
    expect(str(ps.domain.asBoolean())).toBe('Contains(X, Naturals0)');
    expect(ps.density).toBe(ps.distribution);
  });
  it('the expectation over other random symbols is the expression', () => {
    const Y = Poisson('Y', 3);
    expect(ps.computeExpectation(Y, [Y])).toBe(Y);
  });
  it('functions of the random symbol are not implemented', () => {
    const e = mul(2, X);
    expect(() => cdf(e)).toThrow(/not implemented|NotImplemented|cdf/);
    expect(() => density(e)).toThrow();
    expect(() => characteristicFunction(e)).toThrow();
    expect(() => momentGeneratingFunction(e)).toThrow();
    expect(() => quantile(e)).toThrow();
  });
  it('an expectation whose mass function has no closed form of the moment generating function', () => {
    const S1 = Skellam('S', 1, 1);
    expect(str(expectation(pow(S1, 2)))).toBe('2');
  });
});

describe('DiscretePSpace.probability', () => {
  it('a condition on two random symbols uses the density of their difference', () => {
    const X = Poisson('X', 1);
    const Y = Poisson('Y', 2);
    // SymPy: Sum((sqrt(2)/2)**n*exp(-3)*besseli(n, 2*sqrt(2)), (n, 1, oo)) (its inner sums see n > 0)
    expect(str(P(Gt(X, Y)))).toBe('Sum(Sum(2**Y*exp(-2)*Piecewise((exp(-1)/factorial(Y + n), Y + n >= 0), (0, True))/factorial(Y), (Y, 0, oo)), (n, 1, oo))');
  });
  it('a set it cannot sum over gives an unevaluated Probability', () => {
    // where() gives sets of integers that eval_prob sums over; another set (here an interval) is not summed
    class OtherSet extends DiscretePSpace {
      override where(): SingleDiscreteDomain {
        return new SingleDiscreteDomain([x, Interval.of(0, 1)]);
      }
    }
    const X = Geometric('X', R(1, 5));
    const ps = new OtherSet([X.pspace.domain, Lambda(x, pow(S.Half, x))]);
    const r = ps.probability(Lt(x, 1));
    expect(r).toBeInstanceOf(ProbabilityNode);
    expect(str(r)).toBe('Probability(x < 1)');
  });
  it('a finite set and a union of sets of values', () => {
    const X = Geometric('X', R(1, 5));
    expect(str(P(Eq(pow(sub(X, 3), 2), 1)))).toBe('164/625');
    expect(str(P(Gt(pow(sub(X, 3), 2), 1)))).toBe('381/625');
    expect(str(P(and(Gt(X, 2), Lt(X, 2))))).toBe('0');
  });
});

describe('the remaining branches of drv', () => {
  it('the registered constructors of the conditional discrete spaces', () => {
    const Y = Poisson('Y', 2);
    const dom = defined(statsClasses.discreteConditional)(Y.pspace.domain, Gt(Y.symbol, 1));
    expect(dom).toBeInstanceOf(ConditionalDiscreteDomain);
    const ps = defined(statsClasses.discretePSpace)(dom, Lambda(Y.symbol, pow(S.Half, Y.symbol)));
    expect(ps).toBeInstanceOf(DiscretePSpace);
    // a condition on a product of discrete spaces (SymPy: NotImplementedError, the conditional domain has no expectation)
    expect(() => given(Y, Gt(Y, Poisson('Z', 1)))).toThrow(NotImplementedError);
  });
  it('the defaults of SingleDiscreteDistribution', () => {
    class Plain extends SingleDiscreteDistribution {
      constructor(args: readonly Expr[] = []) {
        super('Plain', args);
      }
      pdf(k: Expr): Expr {
        return pow(S.Half, k);
      }
    }
    const d = new Plain();
    expect(() => d.check()).not.toThrow();
    expect(str(d.set)).toBe('Integers');
    // the characteristic function of a handmade distribution by summation
    const k = new Sym('k', { integer: true, positive: true });
    expect(str((DiscreteRV(k, pow(S.Half, k), Naturals).pspace as SingleDiscretePSpace).distribution.characteristicFunction(t))).toBe('exp(I*t)/(2*(1 - exp(I*t)/2))');
    expect(str(new PoissonDistribution([R(3)]).expectation(S.Zero, x))).toBe('0');
  });
  it('where of a space with one random symbol and a condition on two', () => {
    const X = Poisson('X', 1);
    expect(() => X.pspace.where(Gt(X, Poisson('Y', 1)))).toThrow('Multivariate discrete random variables are not yet supported.');
    expect(() => (X.pspace as SingleDiscretePSpace).probability(Xor(Gt(X, 1), Lt(X, 3)))).toThrow(TypeError);
  });
  it('complements of the empty set and of the whole set', () => {
    const X = Poisson('X', 1);
    expect(str(P(Ne(X, -1)))).toBe('1');
    const k = new Sym('k', { integer: true });
    const D = DiscreteRV(k, S.One, FiniteSet.of(1));
    expect(str(P(Ne(D, 1)))).toBe('0');
    expect(str(P(Eq(D, 1)))).toBe('1');
  });
  it('a condition on two random symbols of one space', () => {
    // where() cannot handle it, so the probability is that of the density of their difference
    class Joint extends DiscretePSpace {
      readonly dens: DensityResult;
      constructor(args: readonly Expr[], dens: DensityResult) {
        super(args);
        this.dens = dens;
      }
      override computeDensity(): DensityResult {
        return this.dens;
      }
    }
    const [a, b] = [new Sym('a', { integer: true }), new Sym('b', { integer: true })];
    const dom = pspace(add(Poisson('a', 1), Poisson('b', 1))).domain;
    const zz = new Sym('zz', { integer: true });
    const mk = (d: DensityResult) => new Joint([dom, Lambda([a, b], S.One)], d);
    const ps1 = mk(new PoissonDistribution([R(1)]));
    const [A1, B1] = ps1.values as unknown as [Expr, Expr];
    expect(str(ps1.probability(Gt(A1, B1)))).toBe('(-1 + E)*exp(-1)');
    const ps2 = mk(Lambda(zz, pow(S.Half, zz)));
    const [A2, B2] = ps2.values as unknown as [Expr, Expr];
    expect(str(ps2.probability(Gt(A2, B2)))).toBe('1');
  });
  it('an expectation that raises an error other than NotImplementedError', () => {
    class Failing extends PoissonDistribution {
      override expectation(): Expr {
        throw new RangeError('failing');
      }
    }
    const ps = new SingleDiscretePSpace([new Sym('F'), new Failing([R(1)])]);
    expect(() => ps.computeExpectation(ps.value)).toThrow('failing');
    expect(ps.computeDensity(ps.value)).toBe(ps.distribution);
  });
});
