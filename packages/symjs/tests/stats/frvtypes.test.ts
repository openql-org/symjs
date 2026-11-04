// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/frvtypes.ts (SymPy sympy/stats/frv_types.py and
// sympy/stats/tests/test_finite_rv.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, Float, Ge, Gt, Le, Rational, S, Sym, SymFunction, add, cancel, doit, expand, harmonic, mul, nan, parse, pow, simplify, sqrt, str, sub, symbols } from '../../src';
import type { Expr } from '../../src';
import {
  Bernoulli,
  BernoulliDistribution,
  BetaBinomial,
  Binomial,
  BinomialDistribution,
  Coin,
  Density,
  Die,
  DieDistribution,
  DiscreteUniform,
  FiniteDensity,
  FiniteDistributionHandmade,
  FiniteRV,
  Hypergeometric,
  HypergeometricDistribution,
  IdealSoliton,
  IdealSolitonDistribution,
  Rademacher,
  RademacherDistribution,
  RobustSoliton,
  RobustSolitonDistribution,
  characteristicFunction,
  cmoment,
  coskewness,
  density,
  expectation,
  kurtosis,
  median,
  moment,
  momentGeneratingFunction,
  pspace,
  quantile,
  skewness,
  smoment,
  variance,
  P,
} from '../../src/stats';
import type { SingleFiniteDistribution } from '../../src/stats';
import { pyRound } from '../../src/stats/frvtypes';

const R = (p: number, q = 1): Expr => Rational.of(p, q);
const t = new Sym('t');
const call = (d: unknown, v: Expr): Expr => (d as { call: (v: Expr) => Expr }).call(v);
const dist = (X: Expr): SingleFiniteDistribution => density(X) as SingleFiniteDistribution;
const dictStr = (d: unknown): string => {
  const m = d as Map<Expr, Expr>;
  return `{${[...m].map(([k, v]) => `${str(k)}: ${str(v)}`).join(', ')}}`;
};

describe('DiscreteUniform (SymPy test_discreteuniform)', () => {
  const [a, b, c] = symbols('a b c') as Sym[] as [Sym, Sym, Sym];
  it('symbolic values', () => {
    const X = DiscreteUniform('X', [a, b, c]);
    expect(str(expectation(X))).toBe('a/3 + b/3 + c/3');
    expect(str(simplify(sub(variance(X), parse('(a**2 + b**2 + c**2)/3 - (a/3 + b/3 + c/3)**2'))))).toBe('0');
    expect(str(P(Eq(X, a)))).toBe('1/3');
    expect(str(call(characteristicFunction(X), t))).toBe('exp(I*a*t)/3 + exp(I*b*t)/3 + exp(I*c*t)/3');
    expect(str(call(momentGeneratingFunction(X), t))).toBe('exp(a*t)/3 + exp(b*t)/3 + exp(c*t)/3');
    // issue 18611
    expect(() => DiscreteUniform('Z', [a, a, a, b, b, c])).toThrow('Repeated args detected but set expected.');
    expect(str(dist(X).pmf(a))).toBe('1/3');
    expect(str(dist(X).pmf(1))).toBe('0');
  });
  it('numeric values', () => {
    const Y = DiscreteUniform('Y', [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4]);
    expect(str(expectation(Y))).toBe('-1/2');
    expect(str(variance(Y))).toBe('33/4');
    expect(str(median(Y))).toBe('{-1, 0}');
    for (const v of [-5, 0, 4]) {
      expect(str(P(Eq(Y, v)))).toBe('1/10');
      expect(str(P(Le(Y, v)))).toBe(str(R(v + 6, 10)));
      expect(str(P(Ge(Y, v)))).toBe(str(R(5 - v, 10)));
    }
    expect(dictStr(dist(Die('D', 6)).dict)).toBe(dictStr(dist(DiscreteUniform('U', [1, 2, 3, 4, 5, 6])).dict));
  });
});

describe('Die (SymPy test_dice)', () => {
  it('rejects a number of sides that is not a positive integer', () => {
    // issues 8105 and 8103
    expect(() => Die('X', -1)).toThrow('number of sides must be a positive integer.');
    expect(() => Die('X', 0)).toThrow('number of sides must be a positive integer.');
    expect(() => Die('X', new Float(1.5))).toThrow('number of sides must be a positive integer.');
  });
  it('a symbolic number of sides', () => {
    const n = new Sym('n', { positive: true });
    const D = Die('D', n);
    const dens = dist(D).dict;
    expect(dens).toBeInstanceOf(Density);
    expect(str(dens as Expr)).toBe('Density(DieDistribution(n))');
    expect(dictStr((dens as Density).subs(n, 4) instanceof Density ? ((dens as Density).subs(n, 4) as Density).compute() : undefined)).toBe('{1: 1/4, 2: 1/4, 3: 1/4, 4: 1/4}');
    expect(str(dist(D).set)).toBe('Intersection(Interval(0, n), Naturals0)');
    expect(str(dist(D).low)).toBe('1');
    expect(str(dist(D).high)).toBe('n');
    // SymPy: Sum(Piecewise((k/n, k <= n), (0, True)), (k, 1, n)) (its Sum folds the Piecewise and its
    // summation variable is a positive integer)
    expect(str(expectation(D))).toBe('Sum(_k*Piecewise((1/n, Contains(_k, Integers) & (_k >= 1) & (_k <= n)), (0, True)), (_k, 1, n))');
    expect(str(doit(variance(D).subs(n, 6)))).toBe('35/12');
  });
  it('the mass function (SymPy test_DieDistribution)', () => {
    const X = new DieDistribution([R(6)]);
    const x = new Sym('x');
    expect(X.pmf(S.Half)).toBe(S.Zero);
    expect(str(doit(X.pmf(x).subs(x, 1)))).toBe('1/6');
    expect(str(doit(X.pmf(x).subs(x, 7)))).toBe('0');
    expect(str(doit(X.pmf(x).subs(x, -1)))).toBe('0');
    expect(str(doit(X.pmf(x).subs(x, R(1, 3))))).toBe('0');
    expect(() => X.pmf(sub(pow(x, 2), 1))).toThrow("'x' expected as an argument of type 'number', 'Symbol', or 'RandomSymbol' not Add");
    // SymPy prints the conjunction as (Y >= 1) & (Y <= 6) & Contains(Y, Integers)
    expect(str(X.pmf(Die('Y', 6)))).toBe('Piecewise((1/6, Contains(Y, Integers) & (Y >= 1) & (Y <= 6)), (0, True))');
    expect(X.containsValue(3)).toBe(true);
    expect(X.containsValue(7)).toBe(false);
  });
});

describe('Bernoulli and Coin (SymPy test_bernoulli, test_coins, test_density_call)', () => {
  const [p, a, b] = symbols('p a b') as Sym[] as [Sym, Sym, Sym];
  it('symbolic outcomes', () => {
    const X = Bernoulli('B', p, a, b);
    expect(str(expectation(X))).toBe('a*p + b*(1 - p)');
    expect(str((dist(X).dict as FiniteDensity).get(a) as Expr)).toBe('p');
    expect(str((dist(X).dict as FiniteDensity).get(b) as Expr)).toBe('1 - p');
    expect(str(call(characteristicFunction(X), t))).toBe('p*exp(I*a*t) + (1 - p)*exp(I*b*t)');
    expect(str(call(momentGeneratingFunction(X), t))).toBe('p*exp(a*t) + (1 - p)*exp(b*t)');
    expect(str(dist(X).pmf(a))).toBe('p');
    expect(str(dist(X).pmf(new Sym('c')))).toBe('0');
    const Bs = Bernoulli('B', p, 'win', 'lose');
    expect(str(dist(Bs).set)).toBe('{lose, win}');
  });
  it('the outcomes 1 and 0', () => {
    const X = Bernoulli('B', p, 1, 0);
    const z = new Sym('z');
    expect(str(expectation(X))).toBe('p');
    expect(str(simplify(variance(X)))).toBe('-p**2 + p');
    expect(str(simplify(variance(add(mul(a, X), b))))).toBe('a**2*p*(1 - p)');
    expect(str(call(quantile(X), z))).toBe('Piecewise((nan, (z > 1) | (z < 0)), (0, z <= 1 - p), (1, z <= 1))');
    expect(str(median(Bernoulli('Y', S.Half)))).toBe('{0, 1}');
    expect(str(median(Bernoulli('Z', R(2, 3))))).toBe('{1}');
    expect(() => Bernoulli('B', new Float(1.5))).toThrow('p should be in range [0, 1].');
    expect(() => Bernoulli('B', new Float(-0.5))).toThrow('p should be in range [0, 1].');
    // issue 8248
    expect(str(X.pspace.computeExpectation(S.One))).toBe('1');
    const d = density(X) as BernoulliDistribution;
    expect(str(d.call(0))).toBe('1 - p');
    expect(str(d.call(5))).toBe('0');
    expect(d.containsValue(0)).toBe(true);
    expect(d.containsValue(5)).toBe(false);
  });
  it('coins', () => {
    const C = Coin('C');
    const D = Coin('D');
    const [H, T] = [new Sym('H'), new Sym('T')];
    expect(str(P(Eq(C, D)))).toBe('1/2');
    expect(dictStr(dist(C).dict)).toBe('{H: 1/2, T: 1/2}');
    expect(str(P(Eq(Coin('F', R(1, 10)), H)))).toBe('1/10');
    expect(str(pspace(C).domain.asBoolean())).toBe('Eq(C, H) | Eq(C, T)');
    // SymPy: ValueError, H and T cannot be compared
    expect(() => P(Gt(C, D))).toThrow('Undecidable if');
    expect(str(dist(C).pmf(H))).toBe('1/2');
    expect(str(dist(C).pmf(T))).toBe('1/2');
  });
});

describe('Binomial (SymPy test_binomial_*)', () => {
  it('rejects invalid parameters', () => {
    expect(() => Binomial('b', new Float(0.2), new Float(0.5))).toThrow("'n' must be nonnegative integer.");
    expect(() => Binomial('b', 3, new Float(1.5))).toThrow('p should be in range [0, 1].');
  });
  it('numeric parameters', () => {
    for (const n of [0, 1, 4]) {
      for (const p of [S.Zero, R(1, 4), S.Half, S.One]) {
        const X = Binomial('X', n, p);
        expect(str(sub(expectation(X), mul(n, p)))).toBe('0');
        expect(str(sub(variance(X), mul(n, p, sub(1, p))))).toBe('0');
      }
    }
    const X = Binomial('X', 5, R(1, 4));
    expect(str(skewness(X))).toBe(str(mul(S.Half, pow(sqrt(mul(5, R(3, 16))), -1))));
    expect(str(kurtosis(X))).toBe('43/15');
    expect(str(P(Eq(X, 2)))).toBe('135/512');
  });
  it('quantiles and medians', () => {
    const X = Binomial('X', 50, S.Half);
    expect(str(call(quantile(X), new Float(0.95)))).toBe('31');
    expect(str(median(X))).toBe('{25}');
    const X5 = Binomial('X', 5, S.Half);
    const p = new Sym('p', { positive: true });
    expect(str(call(quantile(X5), p))).toBe('Piecewise((nan, p > 1), (0, p <= 1/32), (1, p <= 3/16), (2, p <= 1/2), (3, p <= 13/16), (4, p <= 31/32), (5, True))');
    expect(str(median(X5))).toBe('{2, 3}');
  });
  it('a symbolic probability', () => {
    const p = new Sym('p', { positive: true });
    const X = Binomial('X', 2, p);
    expect(str(simplify(expectation(X)))).toBe('2*p');
    expect(str(simplify(moment(X, 1)))).toBe('2*p');
    // SymPy: 2*p*(1 - p)
    expect(str(simplify(variance(X)))).toBe('-2*p**2 + 2*p');
    // SymPy: cancel(skewness(X) - (1 - 2*p)/sqrt(n*p*(1 - p))) == 0
    expect(sub(skewness(X), mul(sub(1, mul(2, p)), pow(sqrt(mul(2, p, sub(1, p))), -1))).subs(p, R(1, 3)).evalf().toNumber()).toBeCloseTo(0, 12);
    expect(str(call(characteristicFunction(X), t))).toBe('p**2*exp(2*I*t) + 2*p*(1 - p)*exp(I*t) + (1 - p)**2');
    expect(str(call(momentGeneratingFunction(X), t))).toBe('p**2*exp(2*t) + 2*p*(1 - p)*exp(t) + (1 - p)**2');
    const [H, T] = [new Sym('H'), new Sym('T')];
    const Y = Binomial('Y', 2, p, H, T);
    expect(str(simplify(sub(expectation(Y), mul(2, add(mul(H, p), mul(T, sub(1, p)))))))).toBe('0');
  });
  it('a symbolic number of trials', () => {
    const p = new Sym('p', { positive: true });
    const n = new Sym('n');
    const B = Binomial('B', n, p);
    expect(() => P(Gt(B, 2))).toThrow('Currently, probability queries are not supported for random variables with symbolic sized distributions.');
    const d = dist(B).dict as Density;
    expect(d.key).toBe(new Density([new BinomialDistribution([n, p, S.One, S.Zero])]).key);
    expect(dictStr((d.subs(n, 4) as Density).compute())).toBe('{0: (1 - p)**4, 1: 4*p*(1 - p)**3, 2: 6*p**2*(1 - p)**2, 3: 4*p**3*(1 - p), 4: p**4}');
    expect(str(dist(B).set)).toBe('Intersection(Interval(0, n), Naturals0)');
    expect(str(dist(B).low)).toBe('0');
    expect(str(dist(B).high)).toBe('n');
    // SymPy: Sum(Piecewise((k*p**k*(1 - p)**(-k + n)*binomial(n, k), (k >= 0) & (k <= n) & (k > 2)), (0, True)), (k, 0, n))
    expect(str(expectation(Gt(B, 2)))).toBe(
      'Sum(Piecewise((_k*Piecewise((p**_k*(1 - p)**(-_k + n)*binomial(n, _k), Contains(_k, Integers) & (_k >= 0) & (_k <= n)), (0, True)), _k > 2), (0, True)), (_k, 0, n))',
    );
  });
  it('coskewness (SymPy test_bernoulli)', () => {
    const p = R(1, 5);
    const X = Binomial('X', 5, p);
    const Y = Binomial('Y', 7, mul(2, p));
    const Z = Binomial('Z', 9, mul(3, p));
    expect(str(simplify(coskewness(add(Y, Z), add(X, Y), add(X, Z))))).toBe('0');
    expect(str(simplify(coskewness(add(Y, mul(2, X), Z), add(X, mul(2, Y), Z), add(X, mul(2, Z), Y))))).toBe('12*sqrt(1529)/16819');
  });
});

describe('BetaBinomial (SymPy test_beta_binomial)', () => {
  it('rejects invalid parameters', () => {
    expect(() => BetaBinomial('b', new Float(0.2), 1, 2)).toThrow("'n' must be nonnegative integer. n = 0.200000000000000.");
    expect(() => BetaBinomial('b', 2, -1, 2)).toThrow("'alpha' must be: alpha > 0 . alpha = -1");
    expect(() => BetaBinomial('b', 2, 1, -2)).toThrow("'beta' must be: beta > 0 . beta = -2");
    expect(str(BetaBinomial('b', 2, 1, 1))).toBe('b');
  });
  it('numeric and symbolic parameters', () => {
    for (const n of [1, 3]) {
      for (const [a, b] of [[R(1, 4), R(10)], [S.Half, R(3, 4)]] as const) {
        const X = BetaBinomial('X', n, a, b);
        expect(str(sub(expectation(X), moment(X, 1)))).toBe('0');
        expect(str(sub(variance(X), cmoment(X, 2)))).toBe('0');
      }
    }
    const [n, a0, b0] = symbols('a b n') as Sym[] as [Sym, Sym, Sym];
    expect(str(BetaBinomial('x', n, a0, b0))).toBe('x');
    expect(str(dist(BetaBinomial('x', n, a0, b0)).set)).toBe('Intersection(Interval(0, a), Naturals0)');
    expect(str(dist(BetaBinomial('x', n, a0, b0)).low)).toBe('0');
    expect(str(dist(BetaBinomial('x', n, a0, b0)).high)).toBe('a');
    const a = new Sym('a', { positive: true });
    const b = new Sym('b', { positive: true });
    const X = BetaBinomial('X', 2, a, b);
    expect(str(sub(expand(expectation(X)), expand(moment(X, 1))))).toBe('0');
    expect(str(sub(skewness(X), smoment(X, 3)))).toBe('0');
    expect(str(call(characteristicFunction(X), t))).toBe('exp(2*I*t)*beta(a + 2, b)/beta(a, b) + 2*exp(I*t)*beta(a + 1, b + 1)/beta(a, b) + beta(a, b + 2)/beta(a, b)');
    expect(str(call(momentGeneratingFunction(X), t))).toBe('exp(2*t)*beta(a + 2, b)/beta(a, b) + 2*exp(t)*beta(a + 1, b + 1)/beta(a, b) + beta(a, b + 2)/beta(a, b)');
  });
});

describe('Hypergeometric (SymPy test_hypergeometric_*)', () => {
  it('numeric parameters', () => {
    for (const [N, m, n] of [[4, 2, 3], [3, 0, 2], [2, 1, 1]] as const) {
      const X = Hypergeometric('X', N, m, n);
      expect(str(add(...(dist(X).dict as FiniteDensity).values()))).toBe('1');
      expect(str(sub(expectation(X), R(n * m, N)))).toBe('0');
      expect(str(sub(variance(X), mul(n, R(m, N), R(N - m, N), N - n, pow(N - 1, -1))))).toBe('0');
    }
    expect(str(skewness(Hypergeometric('X', 4, 1, 2)))).toBe('0');
    // SymPy's check(n, N, m) receives (N, m, n): the messages name the shifted parameters
    expect(() => Hypergeometric('X', -1, 0, 0)).toThrow("'n' must be nonnegative integer. n = -1.");
    expect(() => Hypergeometric('X', 2, -1, 0)).toThrow("'N' must be nonnegative integer. N = -1.");
    expect(() => Hypergeometric('X', 2, 0, -1)).toThrow("'m' must be nonnegative integer. m = -1.");
  });
  it('symbolic parameters', () => {
    const [N, m, n] = symbols('N m n') as Sym[] as [Sym, Sym, Sym];
    const H = Hypergeometric('H', N, m, n);
    const dens = dist(H).dict as Density;
    expect(dens.key).toBe(new Density([new HypergeometricDistribution([N, m, n])]).key);
    expect(str((dens.subs(N, 5) as Density).compute() as Expr)).toBe('Density(HypergeometricDistribution(5, m, n))');
    expect(dictStr((dens.subs([[N, 3], [m, 2], [n, 1]]) as Density).compute())).toBe('{0: 1/3, 1: 2/3}');
    expect(str(dist(H).set)).toBe('Intersection(Interval(0, n), Naturals0)');
    // SymPy: Sum(Piecewise((k*binomial(m, k)*binomial(N - m, -k + n)/binomial(N, n), k > 2), (0, True)), (k, 0, n))
    expect(str(expectation(Gt(H, 2)))).toBe('Sum(Piecewise((_k*binomial(m, _k)*binomial(N - m, -_k + n)/binomial(N, n), _k > 2), (0, True)), (_k, 0, n))');
  });
});

describe('Rademacher (SymPy test_rademacher)', () => {
  it('values', () => {
    const X = Rademacher('X');
    expect(str(expectation(X))).toBe('0');
    expect(str(variance(X))).toBe('1');
    expect(str((dist(X).dict as FiniteDensity).get(R(-1)) as Expr)).toBe('1/2');
    expect(str(call(characteristicFunction(X), t))).toBe('exp(I*t)/2 + exp(-I*t)/2');
    expect(str(call(momentGeneratingFunction(X), t))).toBe('exp(t)/2 + exp(-t)/2');
    expect(str(new RademacherDistribution().pmf(2))).toBe('0');
  });
});

describe('IdealSoliton and RobustSoliton (SymPy test_ideal_soliton, test_robust_soliton)', () => {
  const f = SymFunction('f');
  it('IdealSoliton', () => {
    expect(() => IdealSoliton('sol', -12)).toThrow("'k' must be a positive integer.");
    expect(() => IdealSoliton('sol', new Float(13.2))).toThrow("'k' must be a positive integer.");
    expect(() => IdealSoliton('sol', 0)).toThrow("'k' must be a positive integer.");
    expect(() => dist(IdealSoliton('sol', 10)).pmf(f(new Sym('x')))).toThrow("'x' expected as an argument of type 'number', 'Symbol', or 'RandomSymbol'");
    const k = new Sym('k', { integer: true, positive: true });
    const x = new Sym('x', { integer: true, positive: true });
    const sol = IdealSoliton('sol', k);
    expect(str(dist(sol).low)).toBe('1');
    expect(str(dist(sol).high)).toBe('k');
    expect(str(dist(sol).dict as Expr)).toBe('Density(IdealSolitonDistribution(k))');
    expect(str(dist(sol).pmf(x))).toBe('Piecewise((1/k, Eq(x, 1)), (1/(x*(x - 1)), k >= x), (0, True))');
    // SymPy raises a TypeError for a symbol that is not known to be an integer (Eq(x, 1) & None)
    expect(() => dist(sol).pmf(new Sym('y'))).toThrow(TypeError);
    expect(str(dist(sol).pmf(R(1, 2)))).toBe('0');
    for (const i of [5, 20]) {
      const s = sol.subs(k, i);
      expect(str(expectation(s))).toBe(str(harmonic(i)));
      expect(str(sub(variance(s), add(i - 1, harmonic(i), mul(-1, pow(harmonic(i), 2)))))).toBe('0');
    }
    expect(str(call(characteristicFunction(sol.subs(k, 4)), t))).toBe('exp(4*I*t)/12 + exp(3*I*t)/6 + exp(2*I*t)/2 + exp(I*t)/4');
    expect(str(new IdealSolitonDistribution([R(3)]).set)).toBe('{1, 2, 3}');
  });
  it('RobustSoliton', () => {
    expect(() => RobustSoliton('robSol', -12, new Float(0.1), new Float(0.02))).toThrow("'k' must be a positive integer");
    expect(() => RobustSoliton('robSol', 13, new Float(1.89), new Float(0.1))).toThrow("'delta' must be a real number in the interval (0,1)");
    expect(() => RobustSoliton('robSol', 15, new Float(0.6), new Float(-2.31))).toThrow("'c' must be a positive real number.");
    expect(() => dist(RobustSoliton('robSol', 15, new Float(0.6), new Float(0.1))).pmf(f(new Sym('x')))).toThrow("'x' expected as an argument");
    const k = new Sym('k', { integer: true, positive: true });
    const delta = new Sym('delta', { positive: true });
    const c = new Sym('c', { positive: true });
    const rob = RobustSoliton('robSol', k, delta, c);
    expect(str(dist(rob).low)).toBe('1');
    expect(str(dist(rob).high)).toBe('k');
    expect(dist(rob).isSymbolic).toBe(true);
    const r1 = rob.subs([
      [k, 10],
      [delta, new Float(0.2)],
      [c, new Float(0.01)],
    ]);
    expect(str(expectation(r1))).toBe('2.89220429724842');
    expect(str(sub(expectation(r1), moment(r1, 1)))).toBe('0');
    const d = new RobustSolitonDistribution([R(10), new Float(0.2), new Float(0.01)]);
    expect(str(d.set)).toBe('{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}');
    expect(str(d.pmf(1))).toBe('0.106463794967424');
  });
});

describe('FiniteRV (SymPy test_FiniteRV)', () => {
  it('a valid and invalid densities', () => {
    const F = FiniteRV('F', new Map([[1, S.Half], [2, R(1, 4)], [3, R(1, 4)]]), { check: true });
    const p = new Sym('p', { positive: true });
    expect(dictStr(dist(F).dict)).toBe('{1: 1/2, 2: 1/4, 3: 1/4}');
    expect(str(P(Ge(F, 2)))).toBe('1/2');
    expect(str(call(quantile(F), p))).toBe('Piecewise((nan, p > 1), (1, p <= 1/2), (2, p <= 3/4), (3, True))');
    expect(str(pspace(F).domain.asBoolean())).toBe('Eq(F, 1) | Eq(F, 2) | Eq(F, 3)');
    expect(str(F.pspace.domain.set)).toBe('{1, 2, 3}');
    expect(str(dist(F).pmf(2))).toBe('1/4');
    expect(() => FiniteRV('F', new Map([[1, S.Half], [2, S.Half], [3, S.Half]]), { check: true })).toThrow('Total Probability must be 1.');
    expect(() => FiniteRV('F', new Map([[1, S.Half], [2, R(-1, 2)], [3, S.One]]), { check: true })).toThrow('Probability at a point must be between 0 and 1.');
    // an invalid density is not checked by default
    const X = FiniteRV('X', [
      [1, 1],
      [2, 2],
    ]);
    expect(str(expectation(X))).toBe('5');
    expect(str(add(P(Le(X, 2)), P(Gt(X, 2))))).toBe('3');
    expect(new FiniteDistributionHandmade([dist(X).args[0] as Expr]).name).toBe('FiniteDistributionHandmade');
  });
});

void nan;
void cancel;

describe('the remaining branches of frvtypes', () => {
  it('random parameters and symbol names', () => {
    expect(Binomial('X', 2, Bernoulli('Y', S.Half)).pspace.name).toBe('CompoundPSpace');
    expect(Die(new Sym('X'), 6).pspace.name).toBe('SingleFinitePSpace');
  });
  it('Python round (ties to even)', () => {
    expect([2.5, 3.5, -2.5, -1.5, 2.4].map((v) => pyRound(new Float(v)))).toEqual([2, 4, -2, -2, 2]);
  });
});
