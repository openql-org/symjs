// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/rv.ts (SymPy sympy/stats/rv.py and
// sympy/stats/tests/test_rv.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  And,
  Dummy,
  Eq,
  Ge,
  Gt,
  Interval,
  Le,
  Lt,
  Ne,
  Not,
  Or,
  Rational,
  S,
  sin,
  Sym,
  add,
  diff,
  doit,
  integrate,
  isReal,
  mul,
  oo,
  pow,
  str,
  sub,
  subs,
} from '../../src';
import type { Expr } from '../../src';
import {
  Bernoulli,
  BernoulliDistribution,
  Binomial,
  Density,
  Distribution,
  Die,
  DiscreteUniform,
  Exponential,
  FiniteDensity,
  FiniteRV,
  Geometric,
  H,
  Hypergeometric,
  IndependentProductPSpace,
  NormalDistribution,
  Normal,
  P,
  PSpace,
  Poisson,
  RandomSymbol,
  SingleContinuousPSpace,
  SinglePSpace,
  SingleDomain,
  cdf,
  characteristicFunction,
  cmoment,
  covariance,
  density,
  dependent,
  expectation,
  factorialMoment,
  given,
  independent,
  isRandom,
  median,
  moment,
  momentGeneratingFunction,
  pspace,
  quantile,
  randomSymbols,
  variance,
  where,
} from '../../src/stats';
import {
  ProductDomain,
  makeDensity,
  makeProductDomain,
  pspaceIndependent,
  rsSwap,
  rvSubs,
  sortedSymbols,
  statsClasses,
  symbolConverter,
  valueCheck,
} from '../../src/stats/rv';
import { ConditionalContinuousDomain, SingleContinuousDomain } from '../../src/stats/crv';
import { SingleDiscreteDomain } from '../../src/stats/drv';
import { SingleFiniteDomain } from '../../src/stats/frv';
import { Tuple } from '../../src/core/containers';
import { LambdaNode } from '../../src/core/lambda';
import { finiteSet } from '../../src/sets/sets';

const s = (v: unknown): string => (v instanceof Map ? `{${[...v].map(([k, x]) => `${str(k as Expr)}: ${str(x as Expr)}`).join(', ')}}` : str(v as Expr));
const half = Rational.of(1, 2);

describe('random symbols (SymPy RandomSymbol)', () => {
  it('print as their name, compare with their space and carry its assumptions', () => {
    const X = Normal('x', 0, 1);
    const Y = Normal('x', 0, 2);
    expect(X.symbol.key).toBe(Y.symbol.key);
    expect(X.equals(Y)).toBe(false);
    expect(X.name).toBe(X.symbol.name);
    expect(str(X)).toBe('x');
    expect(isReal(X)).toBe(true);
    expect(isReal(Die('D'))).toBe('unknown');
    expect(str(diff(mul(2, X), X))).toBe('2');
    // SymPy: RandomSymbol is a Basic, sorted after the symbols (class key (5, 0, 'RandomSymbol'))
    expect(str(add(X, new Sym('a'), new Sym('z')))).toBe('a + z + x');
    expect(X.sortPriority).toBe(5);
    expect(X.sortClass).toBe('RandomSymbol');
    expect(str(new RandomSymbol(new Sym('x')).pspace)).toBe('PSpace()');
    expect(str(new RandomSymbol('Y'))).toBe('Y');
    expect(() => new RandomSymbol('Y', S.One as unknown as PSpace)).toThrow(TypeError);
    expect(() => symbolConverter(S.One)).toThrow(TypeError);
  });

  it('substitution reaches the probability space (SymPy subs of the arguments)', () => {
    const mu = new Sym('mu');
    const X = Normal('X', mu, 1);
    expect(str((X.subs(mu, 2) as RandomSymbol).pspace)).toBe('SingleContinuousPSpace(X, NormalDistribution(2, 1))');
    expect(X.subs(new Sym('nu'), 2)).toBe(X);
    expect(X.has(mu)).toBe(true);
    expect(X.has(new Sym('nu'))).toBe(false);
    expect(str(add(X, mu).subs(mu, 3))).toBe('X + 3');
    expect(rvSubs(add(X, 1)).key).toBe(add(X.symbol, 1).key);
    expect(rvSubs(mu)).toBe(mu);
    // a random symbol of a conditional space; its symbol is bound (SymPy also substitutes it, and fails for an expression)
    const XX = given(X, Gt(X, 0)) as RandomSymbol;
    expect(str((XX.subs(mu, 2) as RandomSymbol).pspace.domain)).toBe('Domain: (-oo < X) & (X > 0) & (X < oo)');
    expect((XX.subs(mu, 2) as RandomSymbol).pspace.has(mu)).toBe(false);
    expect(XX.subs(new Sym('nu'), 2)).toBe(XX);
    expect(str((X.subs(X.symbol, add(new Sym('y'), 1)) as RandomSymbol).pspace)).toBe('SingleContinuousPSpace(X, NormalDistribution(mu, 1))');
  });

  it('isRandom and randomSymbols', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    const [a, b] = [new Sym('a'), new Sym('b')];
    expect(isRandom(a)).toBe(false);
    expect(isRandom(add(a, b))).toBe(false);
    expect(isRandom(X)).toBe(true);
    expect(isRandom(add(pow(X, 2), Y))).toBe(true);
    expect(isRandom(Gt(Y, 5))).toBe(true);
    expect(isRandom(Eq(X, 4))).toBe(true);
    expect(isRandom(3)).toBe(false);
    expect(randomSymbols(add(mul(2, X), 1)).map(str)).toEqual(['X']);
    expect(randomSymbols(add(mul(2, X), Y)).map(str)).toEqual(['X', 'Y']);
    expect(randomSymbols(add(mul(2, Y), X)).map(str)).toEqual(['X', 'Y']);
    expect(randomSymbols(add(mul(2, X), Y.symbol)).map(str)).toEqual(['X']);
    expect(randomSymbols(2)).toEqual([]);
    expect(randomSymbols(add(Normal('A', 0, 1), Normal('A', 0, 2))).length).toBe(2);
  });
});

describe('probability spaces', () => {
  it('pspace (SymPy test_pspace, test_IndependentProductPSpace)', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    expect(() => pspace(5 + 3)).toThrow(RangeError);
    expect(() => pspace(Lt(new Sym('x'), 1))).toThrow(RangeError);
    expect(pspace(X)).toBe(X.pspace);
    expect(pspace(add(mul(2, X), 1)).key).toBe(X.pspace.key);
    const ps = pspace(add(mul(2, X), Y));
    expect(str(ps)).toBe('IndependentProductPSpace(SingleContinuousPSpace(X, NormalDistribution(0, 1)), SingleContinuousPSpace(Y, NormalDistribution(0, 1)))');
    expect(pspace(add(Y, X)).key).toBe(ps.key);
    expect(pspace([X, Y]).key).toBe(ps.key);
    expect(ps).toBeInstanceOf(IndependentProductPSpace);
    const ip = ps as IndependentProductPSpace;
    expect(ip.symbols.map(str)).toEqual(['X', 'Y']);
    expect(ip.values.map(str)).toEqual(['X', 'Y']);
    expect(str(ip.pdf)).toBe('exp(-X**2/2)*exp(-Y**2/2)/(2*pi)');
    expect(str(ip.domain)).toBe('Domain: (-oo < X) & (-oo < Y) & (X < oo) & (Y < oo)');
    expect(() => ip.density).toThrow('Density not available for ProductSpaces');
    expect(() => ip.computeCdf(add(X, Y))).toThrow(RangeError);
    expect(str(ip.computeExpectation(mul(X, Y), undefined, { evaluate: true }))).toBe('0');
    expect(str(ip.withArgs(ip.args))).toBe(str(ip));
  });

  it('overlapping random symbols (SymPy test_overlap)', () => {
    const X = Normal('x', 0, 1);
    const Y = Normal('x', 0, 2);
    expect(() => P(Gt(X, Y))).toThrow('Overlapping Random Variables');
  });

  it('the generic space and domain raise NotImplementedError', () => {
    const ps = new PSpace();
    const x = new Sym('x');
    for (const f of [
      () => ps.pdf,
      () => ps.where(x),
      () => ps.computeDensity(x),
      () => ps.probability(x),
      () => ps.computeExpectation(x),
      () => ps.computeCdf(x),
      () => ps.computeCharacteristicFunction(x),
      () => ps.computeMomentGeneratingFunction(x),
      () => ps.computeQuantile(x),
      () => ps.conditionalSpace(x),
      () => ps.domain,
    ]) {
      expect(f).toThrow();
    }
    expect([ps.isFinite, ps.isContinuous, ps.isDiscrete, ps.isReal, ps.isSingle, ps.isCompound]).toEqual([false, false, false, false, false, false]);
    const d = new SinglePSpace([x, new NormalDistribution([S.Zero, S.One])]);
    expect(str(d.value)).toBe('x');
    expect(str(d.pdf)).toBe('sqrt(2)*exp(-x**2/2)/(2*sqrt(pi))');
    expect(str(d.distribution)).toBe('NormalDistribution(0, 1)');
    const dom = new SingleContinuousDomain([x, Interval.of(0, 1)]);
    expect(dom.isProductDomain).toBe(false);
    expect(dom.isConditional).toBe(false);
    expect(new SingleFiniteDomain([x, finiteSet(1, 2)]).isContinuous).toBe(false);
  });

  it('product domains', () => {
    const [x, y] = [new Sym('x'), new Sym('y')];
    const a = new SingleContinuousDomain([x, Interval.of(0, 1)]);
    const b = new SingleDiscreteDomain([y, finiteSet(1, 2)]);
    const p = makeProductDomain([a, b]);
    expect(p).toBeInstanceOf(ProductDomain);
    expect(p.name).toBe('ProductDomain');
    const pd = p as ProductDomain;
    expect(pd.symbols.map(str)).toEqual(['x', 'y']);
    expect(str(pd.set)).toBe('ProductSet({1, 2}, Interval(0, 1))');
    expect([...pd.symDomainDict.keys()].sort()).toEqual([x.key, y.key].sort());
    // SymPy: (0 <= x) & (x <= 1) & Contains(y, {1, 2}) (SymPy's Contains of a symbol in a finite set stays unevaluated)
    expect(str(pd.asBoolean())).toBe('(0 <= x) & (x <= 1) & (Eq(1, y) | Eq(2, y))');
    expect(() => pd.computeExpectation(x)).toThrow('compute_expectation is not implemented for ProductDomain');
    // products of products are flattened
    const z = new Sym('z');
    const c = new SingleContinuousDomain([z, Interval.of(0, 1)]);
    expect(str(makeProductDomain([makeProductDomain([a, c]), c]))).toBe('Domain: (0 <= x) & (0 <= z) & (x <= 1) & (z <= 1)');
    expect(sortedSymbols([y, x, y]).map(str)).toEqual(['x', 'y']);
    expect(() => new SingleContinuousDomain([x, Interval.of(0, 1)]).computeExpectation(x, [y])).toThrow('Values should be equal');
  });

  it('rs_swap (SymPy test_rs_swap)', () => {
    const X = Normal('x', 0, 1);
    const Y = Exponential('y', 1);
    const XX = Normal('x', 0, 2);
    const YY = Normal('y', 0, 3);
    const expr = add(mul(2, X), Y);
    expect(subs(expr, rsSwap([X, Y], [YY, XX])).key).toBe(add(mul(2, XX), YY).key);
  });
});

describe('where and given', () => {
  it('SymPy test_where', () => {
    let X = Die('X');
    let Y = Die('Y');
    const Z = Normal('Z', 0, 1);
    expect(str(where(Le(pow(Z, 2), 1)).set)).toBe('Interval(-1, 1)');
    expect(str(where(Le(pow(Z, 2), 1)))).toBe('Domain: (-1 <= Z) & (Z <= 1)');
    expect(str(where(And(Gt(X, Y), Gt(Y, 4))).asBoolean())).toBe('Eq(X, 6) & Eq(Y, 5)');
    expect(str(where(Lt(X, 3)).set)).toBe('{1, 2}');
    X = Normal('X', 0, 1);
    Y = Normal('Y', 0, 1);
    expect(str(where(And(Le(pow(X, 2), 1), Ge(X, 0))).set)).toBe('Interval(0, 1)');
    const XX = given(X, And(Le(pow(X, 2), 1), Ge(X, 0))) as RandomSymbol;
    expect(str(XX.pspace.domain.set)).toBe('Interval(0, 1)');
    expect(str(XX.pspace.domain.asBoolean())).toBe('(-oo < X) & (X >= 0) & (X < oo) & (X**2 <= 1)');
    expect(str(XX.pspace)).toBe(
      'ContinuousPSpace(Domain: (-oo < X) & (X >= 0) & (X < oo) & (X**2 <= 1), Lambda(X, sqrt(2)*exp(-X**2/2)/(2*sqrt(pi)*Integral(sqrt(2)*exp(-_X**2/2)/(2*sqrt(pi)), (_X, 0, 1)))))',
    );
    // SymPy raises a TypeError for a condition that is not a relational
    expect(() => given(X, add(X, 3))).toThrow(TypeError);
    // a condition given a second condition
    expect(str(where(Gt(X, 0), Lt(X, 1)).set)).toBe('Interval.open(0, 1)');
  });

  it('SymPy test_given', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    expect(given(X, S.true)).toBe(X);
    expect(given(X, Gt(Y, 2))).toBe(X);
    expect(given(X)).toBe(X);
  });

  it('an equation given by solving for the random symbol', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    const z = new Sym('z', { real: true });
    expect(str(given(add(mul(2, X), Y), Eq(mul(-1, Y), z)))).toBe('-z + 2*X');
    // the expression is a condition: a relation at the solution
    expect(str(given(Gt(X, Y), Eq(Y, z)))).toBe('X > z');
    expect(str(given(Gt(X, mul(2, Y)), Eq(Y, z)))).toBe('X > 2*z');
    // a random symbol as the condition is fixed: Eq(X, x)
    expect(str(given(add(X, Y), Y))).toBe('Y + X');
    // the solutions of the condition are not a finite set: SymPy cannot iterate over them (TypeError)
    expect(() => given(X, Eq(add(X, sin(X)), z))).toThrow(TypeError);
  });
});

describe('expectation, probability and density', () => {
  it('SymPy test_E, test_issue_10052, test_issue_8129, test_issue_6810', () => {
    expect(expectation(5)).toEqual(S.Zero.add(5));
    const X = Exponential('X', 3);
    expect(str(P(Lt(X, oo)))).toBe('1');
    expect(str(P(Gt(X, oo)))).toBe('0');
    // X == 2 of Python is False
    expect(str(P(Lt(X, oo), Gt(X, 2)))).toBe('1');
    expect(str(P(Lt(X, 2), Gt(X, oo)))).toBe('0');
    expect(str(P(Lt(X, 3), false))).toBe('0');
    expect(str(P(Lt(X, 3), Eq(X, 2)))).toBe('1');
    expect(str(P(true))).toBe('1');
    expect(() => P(1)).toThrow(RangeError);
    expect(() => P(Lt(X, 1), 2)).toThrow(RangeError);
    expect(str(P(Ge(X, X)))).toBe('1');
    expect(str(P(Gt(X, X)))).toBe('0');
    expect(str(P(Gt(X, add(X, 1))))).toBe('0');
    const D = Die('X', 6);
    const Y = Normal('Y', 0, 1);
    expect(str(P(Eq(D, 2)))).toBe('1/6');
    expect(str(P(Eq(Y, 0)))).toBe('0');
    expect(str(P(Or(Gt(D, 2), Lt(D, 3))))).toBe('1');
    expect(str(P(And(Gt(D, 3), Gt(D, 2))))).toBe('1/2');
    expect(str(P(Not(Gt(D, 4))))).toBe('2/3');
  });

  it('evaluate=False keeps the unevaluated nodes', () => {
    const X = Normal('X', 0, 1);
    expect(str(P(Gt(X, 1), undefined, { evaluate: false }))).toBe('Probability(X > 1)');
    expect(str(expectation(X, undefined, { evaluate: false }))).toBe('Expectation(X)');
    expect(str(expectation(X, Gt(X, 0), { evaluate: false }))).toBe('Expectation(X, X > 0)');
    expect(s(cdf(X, undefined, { evaluate: false }))).toBe('Lambda(_z, erf(sqrt(2)*_z/2)/2 + 1/2)');
  });

  it('SymPy test_issue_12237: a random symbol as the given condition', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    expect(P(Gt(X, 0), X).key).toBe(new BernoulliDistribution([half, S.Zero, S.One]).key);
    expect(str(P(Lt(Y, 0), X))).toBe('1/2');
    expect(str(P(Gt(add(X, Y), 0), X))).toBe('Probability(X + Y > 0, X)');
  });

  it('SymPy test_issue_12283: random symbols without a space', () => {
    const x = new Sym('x');
    const X = new RandomSymbol(x);
    const Y = new RandomSymbol('Y');
    expect(pspace(X).key).toBe(new PSpace().key);
    expect(str(expectation(X))).toBe('Expectation(x)');
    expect(str(P(Gt(Y, 3)))).toBe('Probability(Y > 3)');
    expect(str(variance(X))).toBe('Variance(x)');
    expect(str(covariance(X, Y))).toBe('Covariance(Y, x)');
  });

  it('SymPy test_issue_11934', () => {
    const X = FiniteRV('X', [
      [0, 0.5],
      [1, 0.5],
    ]);
    expect(str(expectation(X))).toBe('0.500000000000000');
    expect(str(P(Ge(X, 2)))).toBe('0');
  });

  it('density of a constant and of random expressions (SymPy test_density_constant, test_Density)', () => {
    const d = density(3) as LambdaNode;
    expect(str(d)).toBe('Lambda(x, DiracDelta(x - 3))');
    expect(str(d.call(2))).toBe('0');
    expect(str(d.call(3))).toBe('DiracDelta(0)');
    const X = Die('X', 6);
    expect(s(makeDensity(X).compute())).toBe('DieDistribution(6)');
    expect(str(new Density([X]).withArgs([X]))).toBe('Density(X)');
    expect(new Density([X]).condition).toBeUndefined();
    expect(String(makeDensity(X, Gt(X, 3)).condition)).toBe('X > 3');
    expect(s(density(mul(2, X)))).toBe('{2: 1/6, 4: 1/6, 6: 1/6, 8: 1/6, 10: 1/6, 12: 1/6}');
    // doit of a Density of an expression; a dict (finite space) is not an expression
    const N = Normal('N', 0, 1);
    expect(str(doit(makeDensity(add(N, 1))))).toBe('Lambda(_y, sqrt(2)*exp(-(_y - 1)**2/2)/(2*sqrt(pi)))');
    expect(str(doit(makeDensity(mul(2, X))))).toBe('Density(2*X)');
    expect(s(density(X, Gt(X, 3)))).toBe('{4: 1/3, 5: 1/3, 6: 1/3}');
    // a finite distribution as the expression: its dict
    expect(s(density(new BernoulliDistribution([half, S.One, S.Zero]) as unknown as Expr))).toBe('{0: 1/2, 1: 1/2}');
    expect(s(density(add(N, 1), undefined, { evaluate: false }))).toBe('Lambda(_y, sqrt(2)*exp(-(_y - 1)**2/2)/(2*sqrt(pi)))');
  });

  it('FiniteDensity', () => {
    const d = new FiniteDensity([[S.One, half]]);
    d.set(S.One, Rational.of(1, 3));
    expect(str(d.call(1))).toBe('1/3');
    expect(str(d.call(2))).toBe('0');
    expect(d.has(S.One)).toBe(true);
    expect(d.dict).not.toBe(d);
    expect(s(d.dict)).toBe('{1: 1/3}');
  });

  it('cdf, characteristic and moment generating functions and quantile (SymPy test_characteristic_function, test_moment_generating_function)', () => {
    const X = Normal('X', 0, 1);
    const Y = DiscreteUniform('Y', [1, 2, 7]);
    const Z = Poisson('Z', 2);
    expect(str(characteristicFunction(X))).toBe('Lambda(_t, exp(-_t**2/2))');
    expect(str(characteristicFunction(Y))).toBe('Lambda(_t, exp(7*_t*I)/3 + exp(2*_t*I)/3 + exp(_t*I)/3)');
    expect(str(characteristicFunction(Z))).toBe('Lambda(_t, exp(2*exp(_t*I) - 2))');
    expect(str(momentGeneratingFunction(X))).toBe('Lambda(_t, exp(_t**2/2))');
    expect(str(momentGeneratingFunction(Y))).toBe('Lambda(_t, exp(7*_t)/3 + exp(2*_t)/3 + exp(_t)/3)');
    expect(str(momentGeneratingFunction(Z))).toBe('Lambda(_t, exp(2*exp(_t) - 2))');
    const D = Die('D', 6);
    expect(s(cdf(mul(3, D), Gt(D, 2)))).toBe('{9: 1/4, 12: 1/2, 15: 3/4, 18: 1}');
    expect(str(characteristicFunction(D, Gt(D, 4)))).toBe('Lambda(_t, exp(6*_t*I)/2 + exp(5*_t*I)/2)');
    expect(str(momentGeneratingFunction(D, Gt(D, 4)))).toBe('Lambda(_t, exp(6*_t)/2 + exp(5*_t)/2)');
    expect(str(characteristicFunction(X, undefined, { evaluate: false }))).toBe('Lambda(_t, exp(-_t**2/2))');
    expect(str(momentGeneratingFunction(X, undefined, { evaluate: false }))).toBe('Lambda(_t, exp(_t**2/2))');
    expect(str(quantile(X))).toBe('Lambda(_p, sqrt(2)*erfinv(2*_p - 1))');
    expect(str(quantile(X, { evaluate: false }))).toBe('Lambda(_p, sqrt(2)*erfinv(2*_p - 1))');
    expect(str(quantile(D))).toBe(
      'Lambda(_p, Piecewise((nan, (_p > 1) | (_p < 0)), (1, _p <= 1/6), (2, _p <= 1/3), (3, _p <= 1/2), (4, _p <= 2/3), (5, _p <= 5/6), (6, _p <= 1)))',
    );
  });
});

describe('products of independent spaces', () => {
  it('probability of And, Or and Ne of independent conditions, continuous and discrete', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    const ps = pspace(add(X, Y));
    expect(str(doit(ps.probability(And(Gt(X, 0), Gt(Y, 0)))))).toBe('1/4');
    expect(str(doit(ps.probability(Or(Gt(X, 0), Gt(Y, 0)))))).toBe('1');
    expect(str(doit(ps.probability(Ne(add(X, Y), 0))))).toBe('1');
    expect(str(P(Gt(X, Y)))).toBe('1/2');
    const A = Poisson('A', 1);
    const B = Poisson('B', 2);
    // SymPy leaves the same sum unevaluated (the value is exp(-3))
    expect(str(pspace(add(A, B)).probability(Eq(add(A, B), 0)))).toBe('Sum(2**B*exp(-2)*Sum(exp(-1)*KroneckerDelta(0, A + B)/factorial(A), (A, 0, oo))/factorial(B), (B, 0, oo))');
    expect(str(pspace(add(A, X)).probability(Gt(add(A, X), 0)))).not.toBe('');
  });

  it('a condition on one random symbol of a product is a condition on its own space', () => {
    // SymPy marginalizes with ProductContinuousDomain.integrate, which does not exist (AttributeError)
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    const ps = pspace(add(X, Y));
    expect(str(doit(ps.probability(Gt(X, 0))))).toBe('1/2');
    expect(str(doit(ps.probability(Ne(X, 0))))).toBe('1');
  });

  it('conditional spaces of products (SymPy test_dependence)', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    expect(independent(X, Y)).toBe(true);
    expect(dependent(X, mul(2, X))).toBe(true);
    const D1 = Die('X');
    const D2 = Die('Y');
    expect(independent(D1, mul(2, D2))).toBe(true);
    expect(dependent(D1, mul(2, D2))).toBe(false);
    expect(dependent(D1, add(D2, D1))).toBe(true);
    const XY = given(new Tuple([D1, D2]), Gt(add(D1, D2), 5)) as Expr;
    const [XX, YY] = XY.args;
    expect(dependent(XX as Expr, YY as Expr)).toBe(true);
    expect(pspaceIndependent(D1, D1)).toBe(false);
    // a discrete product
    const A = Poisson('A', 1);
    const B = Poisson('B', 2);
    // SymPy: NotImplementedError too (a conditional discrete domain has no compute_expectation)
    expect(() => given(new Tuple([A, B]), Gt(add(A, B), 1))).toThrow('compute_expectation is not implemented for ConditionalDiscreteDomain');
    // a continuous product
    const C = given(new Tuple([X, Y]), Gt(X, 0)) as Expr;
    expect((C.args[0] as RandomSymbol).pspace.name).toBe('ContinuousPSpace');
  });

  it('SymPy test_dependence: a continuous dependency', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    expect(dependent(add(mul(2, X), Y), mul(-1, Y))).toBe(true);
    expect(independent(add(mul(2, X), Y), mul(-1, Y))).toBe(false);
  });
});

describe('statistics', () => {
  it('SymPy test_H', () => {
    const X = Normal('X', 0, 1);
    const D = Die('D', 4);
    expect(str(H(X, Gt(X, 0)))).toBe('-log(2)/2 + 1/2 + log(pi)/2');
    expect(str(H(D, Gt(D, 2)))).toBe('log(2)');
    // SymPy: H(Geometric('G', 0.5)).evalf() = 1.38629436111989
    expect(str(H(Geometric('G', half)))).toBe('2*log(2)');
  });

  it('SymPy test_factorial_moment', () => {
    expect(str(factorialMoment(Poisson('X', 2), 2))).toBe('4');
    expect(str(factorialMoment(Binomial('Y', 2, half), 2))).toBe('1/2');
    expect(str(factorialMoment(Hypergeometric('Z', 4, 2, 2), 2))).toBe('1/3');
  });

  it('SymPy test_cmoment_constant, test_moment_constant, test_median_constant', () => {
    const x = new Sym('x');
    expect(str(variance(3))).toBe('0');
    expect(str(cmoment(3, 3))).toBe('0');
    expect(str(cmoment(3, 4))).toBe('0');
    expect(str(variance(x))).toBe('0');
    expect(str(cmoment(x, 15))).toBe('0');
    expect(str(cmoment(x, 0))).toBe('1');
    expect(str(moment(3, 0))).toBe('1');
    expect(str(moment(3, 1))).toBe('3');
    expect(str(moment(3, 2))).toBe('9');
    expect(str(moment(x, 2))).toBe('x**2');
    expect(str(median(3))).toBe('3');
    expect(str(median(x))).toBe('x');
  });

  it('SymPy test_normality', () => {
    const X = Normal('X', 0, 1);
    const Y = Normal('Y', 0, 1);
    const x = new Sym('x', { real: true });
    const z = new Sym('z', { real: true });
    const dens = density(sub(X, Y), Eq(add(X, Y), z)) as LambdaNode;
    // SymPy: integrate(dens(x), (x, -oo, oo)) == 1 (here 3/2 - erf(z/2)/2 - erfc(z/2)/2 before simplification)
    expect(str(integrate(dens.call(x), x, [mul(-1, oo), oo]).subs(z, 1).evalf())).toBe('1.00000000000000');
  });
});

describe('the base classes', () => {
  it('domains, spaces and distributions', () => {
    const x = new Sym('x');
    const X = Normal('X', 0, 1);
    expect(() => new SingleDomain([x, Interval.of(0, 1)]).asBoolean()).toThrow('as_boolean is not implemented for SingleDomain');
    const dom = where(Gt(X, 0));
    expect(str(dom.subs(X.symbol, x))).toBe('Domain: (0 < x) & (x < oo)');
    const cd = new ConditionalContinuousDomain([X.pspace.domain, Gt(X, 0)]);
    expect(str(cd.condition)).toBe('X > 0');
    expect(makeProductDomain([dom, cd]).isProductDomain).toBe(true);
    expect(new SinglePSpace([x, new NormalDistribution([S.Zero, S.One])]).isSingle).toBe(true);
    const nd = new NormalDistribution([S.Zero, S.One]);
    expect(nd.isFinite).toBe(false);
    expect(() => nd.dict).toThrow('NormalDistribution is not a finite distribution');
    expect(str(nd.call(0))).toBe('sqrt(2)/(2*sqrt(pi))');
    // a distribution is not random: its density is that of a constant
    expect(s(density(nd))).toBe('Lambda(x, DiracDelta(x - NormalDistribution(0, 1)))');
  });

  it('given: a condition that never holds at the solutions is False', () => {
    const N = Normal('N', 0, 1);
    const w = new Sym('w');
    expect(given(Gt(N, 1), Eq(N, 0))).toBe(S.false);
    expect(str(given(pow(N, 2), Eq(N, w)))).toBe('w**2');
  });

  it('boolean conditions, the cdf and compound densities', () => {
    const N = Normal('N', 0, 1);
    expect(str(P(false))).toBe('0');
    expect(str(P(Gt(N, 0), true))).toBe('1/2');
    expect(s(cdf(N))).toBe('Lambda(_z, erf(sqrt(2)*_z/2)/2 + 1/2)');
    const X = Normal('X', Normal('M', 0, 1), 1);
    // SymPy: ContinuousDistributionHandmade(Lambda(X, (2 - erfc(X/2))*exp(-X**2/4)/(4*sqrt(pi)) + exp(-X**2/4)*erfc(X/2)/(4*sqrt(pi))), Interval(-oo, oo)),
    // which is exp(-X**2/4)/(2*sqrt(pi)) like the form here
    expect(str((density(X) as Distribution).pdf(1).evalf())).toBe('0.219695644733861');
    expect(density(add(X, 1), undefined, { evaluate: false })).toBeInstanceOf(LambdaNode);
    expect(makeDensity(X).compute()).toBeInstanceOf(Distribution);
  });

  it('dependence of finite expressions on spaces that share a symbol', () => {
    expect(dependent(mul(2, Die('X', 6)), Die('X', 4))).toBe(false);
  });

  it('the space of a compound random symbol in an expression', () => {
    const X = Normal('X', Normal('M', 0, 1), 1);
    const Z = Normal('Z', 0, 1);
    expect(pspace(add(X, Z)).isCompound).toBe(true);
  });
});

describe('the registry and checks', () => {
  it('valueCheck (SymPy _value_check)', () => {
    expect(valueCheck(true, 'm')).toBe(true);
    expect(valueCheck(undefined, 'm')).toBe(false);
    expect(valueCheck(Gt(new Sym('a'), 0), 'm')).toBe(false);
    expect(valueCheck([S.true, true], 'm')).toBe(true);
    expect(() => valueCheck([true, S.false], 'msg')).toThrow('msg');
    expect(() => valueCheck(false, 'msg')).toThrow(RangeError);
  });

  it('every module registers its classes', () => {
    for (const k of Object.keys(statsClasses)) expect(typeof (statsClasses as Record<string, unknown>)[k]).toBe('function');
    expect(Object.keys(statsClasses).length).toBeGreaterThan(15);
  });

  it('a random symbol of a hand-made space', () => {
    const z = new Dummy('z', { real: true });
    const d = new SingleContinuousPSpace([z, new NormalDistribution([S.Zero, S.One])]);
    expect(str(d.value.pspace)).toBe('SingleContinuousPSpace(_z, NormalDistribution(0, 1))');
    expect(str(Bernoulli('B', half))).toBe('B');
  });
});

describe('random indexed and random matrix symbols, matrix domains (SymPy sympy/stats/rv.py, part 2)', async () => {
  const sj = await import('../../src');
  const t = new sj.Sym('t');
  it('RandomIndexedSymbol', () => {
    const r = new sj.RandomIndexedSymbol(sj.SymFunction('X')(t));
    expect(sj.str(r)).toBe('X(t)');
    expect(sj.str(r.indexKey)).toBe('t');
    expect([...sj.freeSymbols(r)].map(sj.str).sort()).toEqual(['X(t)', 't']);
    expect(r.has(t)).toBe(true);
    expect(r.has(new sj.Sym('u'))).toBe(false);
    expect(sj.str(sj.subs(r, [[t, 2]]))).toBe('X(2)');
    expect(sj.subs(r, [[new sj.Sym('u'), 2]]).key).toBe(r.key);
    expect(r.sortClass).toBe('RandomIndexedSymbol');
    // SymPy: TypeError An Function or Indexed object is expected not t
    expect(() => new sj.RandomIndexedSymbol(t)).toThrow('An Function or Indexed object is expected not t');
  });
  it('RandomMatrixSymbol', () => {
    const X = new sj.RandomMatrixSymbol('X', 2, 1);
    expect(X.has(new sj.Sym('z'))).toBe(false);
    expect(sj.isRandom(X)).toBe(true);
    expect(sj.pspace(X).key).toBe(new sj.PSpace().key);
    expect(sj.str(new sj.MatrixDomain([new sj.Sym('M'), sj.Reals]).symbols[0] as Expr)).toBe('M');
  });
  it('the hooks of the spaces of part 2 are not implemented by the generic space', () => {
    const ps = new sj.PSpace();
    expect(ps.hasValueDensity).toBe(false);
    expect(() => ps.valueDensity).toThrow(sj.NotImplementedError);
    expect(() => ps.probabilityGiven(S.true, undefined)).toThrow(sj.NotImplementedError);
    expect(() => ps.expectationGiven(S.One, undefined)).toThrow(sj.NotImplementedError);
  });
  it('the matrix forms of Expectation and Covariance with a condition', () => {
    const X = new sj.RandomMatrixSymbol('X', 2, 1);
    const Y = new sj.RandomMatrixSymbol('Y', 2, 1);
    const c = Gt(new sj.Sym('x'), 0);
    expect(sj.str(sj.Expectation(X, c))).toBe('ExpectationMatrix(X, x > 0)');
    expect(sj.str(sj.Covariance(X, Y, c))).toBe('CrossCovarianceMatrix(X, Y, x > 0)');
  });
});
