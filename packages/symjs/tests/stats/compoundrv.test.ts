// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/compoundrv.ts (SymPy sympy/stats/compound_rv.py and
// sympy/stats/tests/test_compound_rv.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Gt, Rational, S, Sym, doit, str } from '../../src';
import type { Expr } from '../../src';
import {
  Bernoulli,
  BernoulliDistribution,
  Beta,
  Binomial,
  CompoundDistribution,
  CompoundPSpace,
  Die,
  Distribution,
  Gamma,
  Normal,
  NormalDistribution,
  P,
  Poisson,
  PoissonDistribution,
  RandomSymbol,
  SingleContinuousPSpace,
  SingleDiscretePSpace,
  SingleFinitePSpace,
  Uniform,
  cdf,
  density,
  expectation,
  given,
  variance,
  where,
} from '../../src/stats';
import { compoundDistribution, compoundPSpace } from '../../src/stats/compoundrv';
import { FiniteDensity } from '../../src/stats/rv';

const half = Rational.of(1, 2);
const s = (v: unknown): string => (v instanceof Map ? `{${[...v].map(([k, x]) => `${str(k as Expr)}: ${str(x as Expr)}`).join(', ')}}` : str(v as Expr));

describe('compound distributions of finite random symbols (SymPy test_bernoulli_CompoundDist)', () => {
  it('a Bernoulli with a random p', () => {
    const X = Beta('X', 1, 2);
    const Y = Bernoulli('Y', X);
    // SymPy: {0: 2/3, 1: 1/3}, E(Y) = P(Eq(Y, 1)) = 1/3, variance 2/9, cdf {0: 2/3, 1: 1} (beta(1, 2) is 1/2 there)
    const d = density(Y) as FiniteDensity;
    expect([...d.values()].map((v) => str(v.evalf()))).toEqual(['0.666666666666667', '0.333333333333333']);
    expect(str(expectation(Y).evalf())).toBe('0.333333333333333');
    expect(str(P(Eq(Y, 1)).evalf())).toBe('0.333333333333333');
    expect(str(variance(Y).evalf())).toBe('0.222222222222222');
    expect([...(cdf(Y) as FiniteDensity).values()].map((v) => str(v.evalf()))).toEqual(['0.666666666666667', '1.00000000000000']);
  });

  it('a Bernoulli with a Bernoulli p (SymPy issue 8128)', () => {
    const a = Bernoulli('a', half);
    const b = Bernoulli('b', a);
    expect(str(b.pspace)).toBe('CompoundPSpace(b, CompoundDistribution(BernoulliDistribution(a, 1, 0)))');
    expect(s(density(b))).toBe('{0: 1/2, 1: 1/2}');
    expect(str(P(Gt(b, half)))).toBe('1/2');
    expect(s(cdf(b))).toBe('{0: 1/2, 1: 1}');
    expect(str(expectation(b))).toBe('1/2');
    expect(s(density(b, Gt(b, half)))).toBe('{1: 1}');
    expect(str(b.pspace.domain)).toBe('Domain: Eq(b, 0) | Eq(b, 1)');
    expect(str(expectation(b, undefined, { evaluate: false }))).toBe('Expectation(b)');
    expect(str(doit(expectation(b, undefined, { evaluate: false })))).toBe('1/2');
    // SymPy: NotImplementedError (a compound space has no where)
    expect(() => where(Gt(b, half))).toThrow('where is not implemented for CompoundPSpace');
  });

  it('a Bernoulli and a Binomial with a uniform p', () => {
    const X = Uniform('X', 0, 1);
    const Y = Bernoulli('Y', X);
    expect(str(expectation(Y))).toBe('1/2');
    expect(str(P(Eq(Y, 1)))).toBe('1/2');
    expect(s(density(Y))).toBe('{0: 1/2, 1: 1/2}');
    // SymPy: {0: hyper((-2, 1), (2,), 1), 1: hyper((-1, 2), (3,), 1), 2: hyper((0, 3), (4,), 1)/3}, which are 1/3 each
    const B = Binomial('Bn', 2, Uniform('V', 0, 1));
    expect(s(density(B))).toBe('{0: 1/3, 1: 1/3, 2: 1/3}');
    expect(str(expectation(B))).toBe('1');
  });
});

describe('compound distributions of continuous and discrete random symbols', () => {
  it('a Normal with a uniform mean (unevaluated densities, SymPy test_unevaluated_CompoundDist)', () => {
    const N = Normal('N', Uniform('W', 0, 1), 1);
    expect(N.pspace.isContinuous).toBe(true);
    expect(str(N.pspace.pdf)).toBe('Integral(Piecewise((sqrt(2)*exp(-(N - W)**2/2)/(2*sqrt(pi)), (W >= 0) & (W <= 1)), (0, True)), (W, 0, 1))');
    expect(s(density(N, undefined, { evaluate: false }))).toBe(
      'ContinuousDistributionHandmade(Lambda(N, Integral(Piecewise((sqrt(2)*exp(-(N - W)**2/2)/(2*sqrt(pi)), (W >= 0) & (W <= 1)), (0, True)), (W, 0, 1))), Interval(-oo, oo))',
    );
    expect(str((N.pspace as CompoundPSpace).set)).toBe('Interval(-oo, oo)');
    expect(given(N, Gt(N, 0))).toBeInstanceOf(RandomSymbol);
    expect(s(cdf(Normal('M', Uniform('V', 0, 1), 1)))).toContain('Lambda(_z, ');
  });

  it('a Poisson with a Gamma rate is a negative binomial (SymPy test_poisson_CompoundDist)', () => {
    const k = new Sym('k', { positive: true });
    const t = new Sym('t', { positive: true });
    const y = new Sym('y', { positive: true });
    const D = Poisson('P', Gamma('G', k, t));
    expect(D.pspace.isDiscrete).toBe(true);
    // SymPy (simplified): t**y*(t + 1)**(-k - y)*gamma(k + y)/(gamma(k)*gamma(y + 1))
    expect(str((density(D) as Distribution).pdf(y).subs([[k, 2], [t, 1], [y, 3]]).evalf())).toBe('0.125000000000000');
    expect(str(Poisson('Z', Uniform('U', 1, 2)).pspace.domain)).toBe('Domain: Contains(Z, Naturals0)');
  });
});

describe('CompoundDistribution and CompoundPSpace (SymPy test_Compound_Distribution, test_compound_pspace)', () => {
  it('the distribution', () => {
    const X = Normal('X', 2, 4);
    const C = compoundDistribution(new NormalDistribution([X, Rational.of(4)])) as CompoundDistribution;
    expect(C).toBeInstanceOf(CompoundDistribution);
    expect(C.isContinuous).toBe(true);
    expect(C.isFinite).toBe(false);
    expect(C.isDiscrete).toBe(false);
    expect(str(C.set)).toBe('Interval(-oo, oo)');
    expect(str(C)).toBe('CompoundDistribution(NormalDistribution(X, 4))');
    expect(str(C.pdf(new Sym('x')))).toBe('Integral(exp(-(x - X)**2/32)*exp(-(X - 2)**2/32)/(32*pi), (X, -oo, oo))');
    expect(str(C.withArgs(C.args))).toBe(str(C));
    // without random parameters the distribution itself
    expect(compoundDistribution(new NormalDistribution([Rational.of(2), Rational.of(3)]))).toBeInstanceOf(NormalDistribution);
    const B = compoundDistribution(new BernoulliDistribution([Beta('X', 2, 4), S.One, S.Zero])) as CompoundDistribution;
    expect(B.isFinite).toBe(true);
    expect(str(B.set)).toBe('{0, 1}');
    // SymPy: Piecewise((1/(30*beta(2, 4)), Eq(y, 0)), (1/(60*beta(2, 4)), Eq(y, 1)), (0, True)) (the integral of the Piecewise)
    expect(str(B.pdf(0, true))).toBe('1/(30*beta(2, 4))');
    const G = Gamma('G', new Sym('k', { positive: true }), new Sym('t', { positive: true }));
    const P2 = compoundDistribution(new PoissonDistribution([G])) as CompoundDistribution;
    expect(P2.isDiscrete).toBe(true);
    expect(str(P2.set)).toBe('Naturals0');
    // a distribution that is not continuous, discrete or finite (SymPy: NotImplementedError for a joint one)
    expect(() => compoundDistribution(C)).toThrow('Compound Distribution for CompoundDistribution(NormalDistribution(X, 4)) is not implemented yet');
  });

  it('the space', () => {
    const X = Normal('X', 2, 4);
    const Y = Normal('Y', 3, 6);
    expect(Y.pspace).not.toBeInstanceOf(CompoundPSpace);
    expect(compoundPSpace('N', new NormalDistribution([S.One, Rational.of(2)]))).toBeInstanceOf(SingleContinuousPSpace);
    expect(compoundPSpace('D', new PoissonDistribution([Rational.of(3)]))).toBeInstanceOf(SingleDiscretePSpace);
    expect(compoundPSpace('B', new BernoulliDistribution([Rational.of(1, 5), S.One, S.Zero]))).toBeInstanceOf(SingleFinitePSpace);
    expect(() => compoundPSpace('M', new FiniteDensityDistribution([]))).toThrow('should be an isinstance of CompoundDistribution');
    const Z = Normal('Y', X, 6);
    expect(Z.pspace).toBeInstanceOf(CompoundPSpace);
    const ps = Z.pspace as CompoundPSpace;
    expect(ps.distribution.key).toBe(new CompoundDistribution([new NormalDistribution([X, Rational.of(6)])]).key);
    expect(str(ps.domain.set)).toBe('Interval(-oo, oo)');
    expect(str(ps.pdf)).toBe('Integral(exp(-(Y - X)**2/72)*exp(-(X - 2)**2/32)/(48*pi), (X, -oo, oo))');
    expect([ps.isCompound, ps.isSingle, ps.isFinite, ps.isContinuous, ps.isDiscrete]).toEqual([true, true, false, true, false]);
    expect(str(ps.symbol)).toBe('Y');
    expect(str(ps.value)).toBe('Y');
    // substitution in the parameters of the random symbol of a compound space
    expect(str((Z.subs(X.symbol, 1) as RandomSymbol).pspace)).toBe(str(Z.pspace));
  });

  it('the expectation over given random symbols', () => {
    const b = Bernoulli('b', Bernoulli('a', half));
    expect(str(doit(b.pspace.computeExpectation(b, [b])))).toBe('1/2');
    expect(str(doit(b.pspace.computeExpectation(b)))).toBe('1/2');
    expect(s(b.pspace.computeDensity(b))).toBe('{0: 1/2, 1: 1/2}');
    expect(str(doit(b.pspace.computeExpectation(b, [b, Bernoulli('c', half)])))).toBe('1/2');
    // a random parameter that is not a random symbol (SymPy: AttributeError)
    expect(() => density(Bernoulli('B', Rational.of(1, 2).mul(Die('D', 2)).sub(Rational.of(1, 2))))).toThrow('random parameter is not a RandomSymbol');
  });
});

/** A finite distribution that is neither continuous, discrete nor compound: a hand-made one built by hand. */
class FiniteDensityDistribution extends Distribution {
  constructor(args: readonly Expr[]) {
    super('FiniteDensityDistribution', args);
  }
  get set(): never {
    throw new TypeError('no set');
  }
  pdf(): Expr {
    return S.Zero;
  }
}
