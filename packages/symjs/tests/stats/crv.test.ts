// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/crv.ts (SymPy sympy/stats/crv.py and
// sympy/stats/tests/test_continuous_rv.py): continuous domains,
// distributions and probability spaces. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, FiniteSet, Gt, Interval, Lt, Ne, NotImplementedError, Order, Rational, Reals, S, Sym, Union, add, and, exp, mul, neg, or, pow, rewrite, sin, sqrt, str } from '../../src';
import { Xor as xor } from '../../src/core';
import type { Expr } from '../../src';
import {
  Distribution, Expectation, Exponential, FiniteDensity, Normal, P, PowerFunction, Reciprocal, cdf, characteristicFunction, density, expectation as E,
  given, momentGeneratingFunction, quantile,
} from '../../src/stats';
import type { RandomSymbol } from '../../src/stats';
import { Lambda, LambdaNode } from '../../src/core/lambda';
import { ConditionalContinuousDomain, ContinuousPSpace, ProductContinuousDomain, SingleContinuousDomain } from '../../src/stats';
import { limitOver, reduceRationalInequalitiesWrap, removeO } from '../../src/stats/crv';

/** A density, cdf, ... applied to arguments (SymPy d(x)). */
function ap(d: unknown, ...xs: (Expr | number)[]): Expr {
  if (d instanceof LambdaNode) return d.call(...xs);
  if (d instanceof Distribution) return d.pdf(xs[0] as Expr | number);
  if (d instanceof FiniteDensity) return d.call(xs[0] as Expr | number);
  throw new TypeError('not callable');
}
const show = (v: unknown): string => str(v as Expr);

const [x, z, p, t] = ['x', 'z', 'p', 't'].map((n) => new Sym(n)) as [Sym, Sym, Sym, Sym];
/** The symbol of the space of Xn. */
const xs = x;
const Xn = Normal('x', 0, 1);
const Yn = Normal('y', 0, 1);

describe('continuous probability spaces (SymPy crv) 1', () => {
  it("E(X + Y, X > 0)", () => expect(show(E(add(Xn, Yn), Gt(Xn, 0)))).toBe("sqrt(2)/sqrt(pi)"));
  it("E(X, Or)", () => expect(() => E(Xn, or(Lt(Xn, -1), Gt(Xn, 1)))).toThrow(NotImplementedError));
  it("E(X, X > Y)", () => expect(() => E(Xn, Gt(Xn, Yn))).toThrow(NotImplementedError));
  it("P(X > Y, Y > 0)", () => expect(() => P(Gt(Xn, Yn), Gt(Yn, 0))).toThrow(NotImplementedError));
  it("probability no rv", () => expect(show(Xn.pspace.probability(Gt(x, 1)))).toBe("Integral(sqrt(2)*exp(-_z**2/2)/(2*sqrt(pi)), (_z, 1, oo))"));
  it("probability no rv given", () => expect(show((given(Xn, Gt(Xn, 0)) as RandomSymbol).pspace.probability(Gt(x, 1)))).toBe("Integral(sqrt(2)*exp(-_z**2/2)/(2*sqrt(pi)*Integral(sqrt(2)*exp(-_x**2/2)/(2*sqrt(pi)), (_x, 0, oo))), (_z, 1, oo))"));
  it("where two rvs", () => expect(() => Xn.pspace.where(Gt(Xn, Yn))).toThrow(NotImplementedError));
  it("E evaluate False", () => expect(show(E(Xn, undefined, { evaluate: false }))).toBe("Expectation(x)"));
  it("E evaluate False doit", () => expect(show(rewrite(Expectation(Xn), 'Integral'))).toBe("Integral(sqrt(2)*x*exp(-x**2/2)/(2*sqrt(pi)), (x, -oo, oo))"));
  it("E exp", () => expect(show(E(exp(neg(Exponential('e', 1)))))).toBe("1/2"));
  it("cdf computed", () => expect(show(ap(cdf(Reciprocal('r', 1, 2)), z))).toBe("Piecewise((log(z)/log(2), z >= 1), (0, True))"));
  // SymPy: Piecewise((Intersection({-sqrt(p), sqrt(p)}, Interval(0, 1)), (p >= 0) & (p <= 1)), (nan, True));
  // symjs's solveset does not solve x**2 = p with a parameter
  it("quantile computed", () => expect(show(ap(quantile(PowerFunction('w', 2, 0, 1)), p))).toBe('Piecewise((ConditionSet(_x, Eq(_x**2 - p, 0), Interval(0, 1)), (p >= 0) & (p <= 1)), (nan, True))'));
});

describe('continuous probability spaces (SymPy crv) 2', () => {
  // SymPy: Piecewise(((-2*I*t + 2)*exp(I*t)/t**2 - 2/t**2, Ne(t, 0)), (1, True)) (the same function)
  it("cf computed", () => expect(show(ap(characteristicFunction(PowerFunction('w', 2, 0, 1)), t))).toBe('-2*Piecewise((t**(-2), Ne(t, 0)), (0, True)) + 2*Piecewise(((-I/t + t**(-2))*exp(I*t), Ne(t, 0)), (1/2, True))'));
  // SymPy: Piecewise(((2*t - 2)*exp(t)/t**2 + 2/t**2, Ne(t, 0)), (1, True)) (the same function)
  it("mgf computed", () => expect(show(ap(momentGeneratingFunction(PowerFunction('w', 2, 0, 1)), t))).toBe('-2*Piecewise((-1/t**2, Ne(t, 0)), (0, True)) + 2*Piecewise(((1/t - 1/t**2)*exp(t), Ne(t, 0)), (1/2, True))'));
  it("conditional pdf", () => expect(show((given(Xn, Gt(Xn, 0)) as RandomSymbol).pspace.pdf)).toBe("sqrt(2)*exp(-x**2/2)/(2*sqrt(pi)*Integral(sqrt(2)*exp(-_x**2/2)/(2*sqrt(pi)), (_x, 0, oo)))"));
  it("conditional density 2x", () => expect(show(ap(density(mul(2, given(Xn, Gt(Xn, 0)))), z))).toBe("-sqrt(2)*exp(-z**2/8)*Heaviside(-z/2)/(2*sqrt(pi)) + sqrt(2)*exp(-z**2/8)/(2*sqrt(pi))"));
  it("conditional cdf", () => expect(show(ap(cdf(given(Xn, Gt(Xn, 0))), z))).toBe("Piecewise((erf(sqrt(2)*z/2), z >= 0), (0, True))"));
  // SymPy: E*Integral(exp(-_x)*exp(_x*I*t), (_x, -oo, oo)); symjs integrates it with the convergence conditions of the Meijer G-function method
  it("conditional cf", () => expect(show(ap(characteristicFunction(given(Exponential('e', 1), Gt(Exponential('e', 1), 1))), t))).toMatch(/^Piecewise\(\(-E\/\(-I\*t \+ 1\) \+ E\*I\/\(t\*\(1 \+ I\/t\)\), /));
  // SymPy: Piecewise((0, (Abs(t) > 1) & (Abs(arg(t)) < pi/2) & (Abs(arg(t) + pi) <= pi/2)), (Piecewise(...), True)): the conditions of the
  // Meijer G-function method in another form
  it("conditional mgf", () => expect(show(ap(momentGeneratingFunction(given(Exponential('e', 1), Gt(Exponential('e', 1), 1))), t))).toMatch(/^Piecewise\(\(0, Ne\(t, 1\) & /));
  // SymPy raises AttributeError ('ContinuousPSpace' object has no attribute 'set'); symjs solves in the set of the domain
  // (it does not solve the Piecewise equation: SymPy's solveset would give {1 - log(1 - p)})
  it("conditional quantile", () => expect(show(ap(quantile(given(Exponential('e', 1), Gt(Exponential('e', 1), 1))), p))).toBe('ConditionSet(_x, Eq(-p + Piecewise((1 - E*exp(-_x), _x >= 1), (0, True)), 0), Interval.open(1, oo))'));
  it("domain no variables", () => expect(show(Xn.pspace.domain.computeExpectation(xs, []))).toBe("x"));
  it("domain wrong variable", () => expect(() => Xn.pspace.domain.computeExpectation(xs, [new Sym('y')])).toThrow(RangeError));
  it("domain as_boolean", () => expect(show(Xn.pspace.domain.asBoolean())).toBe("(-oo < x) & (x < oo)"));
  it("exponential domain as_boolean", () => expect(show(Exponential('e', 1).pspace.domain.asBoolean())).toBe("(0 <= e) & (e < oo)"));
});

describe('continuous probability spaces (SymPy crv) 3', () => {
  it("given domain set", () => expect(show((given(Exponential('e', 1), Lt(Exponential('e', 1), 2)) as RandomSymbol).pspace.domain.set)).toBe("Interval.Ropen(0, 2)"));
  // SymPy: Piecewise((Integral(exp(-sqrt(_x))/Abs(sqrt(_x)), (_x, 0, z))/2 + Integral(exp(sqrt(_x))/Abs(sqrt(_x)), (_x, 0, z))/2, z >= 0), (0, True));
  // symjs leaves the same integral, behind the conditions of a Meijer G-function result that cannot hold
  it("cdf X**2", () => expect(show(ap(cdf(pow(Exponential('e', 1), 2)), z))).toMatch(/\(Integral\(exp\(sqrt\(_x\)\)\/\(2\*sqrt\(Abs\(_x\)\)\) \+ exp\(-sqrt\(_x\)\)\/\(2\*sqrt\(Abs\(_x\)\)\), \(_x, 0, z\)\), True\)\), z >= 0\), \(0, True\)\)$/));
  // SymPy raises ValueError (Can not solve sqrt(e) for e): solveset gives an ImageSet with the condition y >= 0
  it("density sqrt", () => expect(() => density(sqrt(Exponential('e', 1)))).toThrow('Can not solve sqrt(e) for e'));
  // SymPy: sqrt(2)*exp(-z/2)/(2*sqrt(pi)*Abs(sqrt(z))) (the same for a real z)
  it("density X**2", () => expect(show(ap(density(pow(Xn, 2)), z))).toBe('sqrt(2)*exp(-z/2)/(2*sqrt(pi)*sqrt(Abs(z)))'));
  it("density sin", () => expect(() => density(sin(Xn))).toThrow(RangeError));
  // SymPy: (2 - erfc(sqrt(2)*I*t))*exp(-2*t**2)/2 + exp(-2*t**2)*erfc(sqrt(2)*I*t)/2 (both are exp(-2*t**2))
  it("cf of 2X", () => expect(show(ap(characteristicFunction(mul(2, Xn)), t))).toBe('sqrt(2)*I*(-sqrt(2)*I*pi*t*exp(-2*t**2)*erf(sqrt(2)*I*t) - sqrt(2)*I*pi*t*exp(-2*t**2))/(4*pi*t) - sqrt(2)*I*(-sqrt(2)*I*pi*t*exp(-2*t**2)*erf(sqrt(2)*I*t) + sqrt(2)*I*pi*t*exp(-2*t**2))/(4*pi*t)'));
  // SymPy: (2 - erfc(sqrt(2)*t))*exp(2*t**2)/2 + exp(2*t**2)*erfc(sqrt(2)*t)/2 (both are exp(2*t**2))
  it("mgf of 2X", () => expect(show(ap(momentGeneratingFunction(mul(2, Xn)), t))).toBe('-sqrt(2)*(-sqrt(2)*pi*t*exp(2*t**2)*erf(sqrt(2)*t) - sqrt(2)*pi*t*exp(2*t**2))/(4*pi*t) + sqrt(2)*(-sqrt(2)*pi*t*exp(2*t**2)*erf(sqrt(2)*t) + sqrt(2)*pi*t*exp(2*t**2))/(4*pi*t)'));
  // SymPy: Intersection({-2*log(1 - p)}, Interval(0, oo)); symjs's solveset does not solve the Piecewise equation
  it("quantile of 2X", () => expect(show(ap(quantile(mul(2, Exponential('e', 1))), p))).toBe('ConditionSet(_x, Eq(-p + Piecewise((1 - exp(-_x/2), _x >= 0), (0, True)), 0), Interval(0, oo))'));
  it("P Eq", () => expect(show(P(Eq(Xn, 0)))).toBe("0"));
  it("P empty", () => expect(show(P(Lt(Exponential('e', 1), -1)))).toBe("0"));
  it("P Ne empty", () => expect(show(P(Ne(Exponential('e', 1), -1)))).toBe("1"));
  it("E 0 polynomial", () => expect(show(Xn.pspace.computeExpectation(S.Zero, undefined, { evaluate: true }))).toBe("0"));
});

describe('continuous probability spaces (SymPy crv) 4', () => {
  it("E poly no mgf", () => expect(show(E(Reciprocal('r', 1, 2)))).toBe("1/log(2)"));
  it("E other space", () => expect(show(Xn.pspace.computeExpectation(Yn, [Yn]))).toBe("y"));
});

describe('the continuous domains (SymPy crv)', () => {
  const [u, v] = [new Sym('x'), new Sym('y')];
  const dX = new SingleContinuousDomain([u, Interval.of(0, 1)]);
  const dY = new SingleContinuousDomain([v, Interval.of(0, 2)]);
  const half = S.Half;

  it('integrals over sets', () => {
    expect(limitOver(u, Reals).map(show)).toEqual(['x', '-oo', 'oo']);
    expect(() => limitOver(u, FiniteSet.of(1, 2))).toThrow(NotImplementedError);
    expect(show(removeO(new Order([u])))).toBe('0');
    expect(show(removeO(u))).toBe('x');
    expect(() => reduceRationalInequalitiesWrap(u, u)).toThrow(TypeError);
    expect(show(reduceRationalInequalitiesWrap(or(Lt(u, 0), Gt(u, 1)), u))).toBe('Union(Interval.open(-oo, 0), Interval.open(1, oo))');
  });

  it('SingleContinuousDomain', () => {
    expect(show(dX.computeExpectation(u))).toBe('Integral(x, (x, 0, 1))');
    expect(dX.isContinuous).toBe(true);
  });

  it('ProductContinuousDomain', () => {
    const pd = new ProductContinuousDomain([dX, dY]);
    expect(pd.isContinuous).toBe(true);
    expect(show(pd.computeExpectation(mul(u, v)))).toBe('Integral(x*y, (x, 0, 1), (y, 0, 2))');
    expect(show(pd.computeExpectation(mul(u, v), [u]))).toBe('Integral(x*y, (x, 0, 1))');
    expect(show(pd.asBoolean())).toBe('(0 <= x) & (0 <= y) & (x <= 1) & (y <= 2)');
    // SymPy: NotImplementedError (Set of Conditional Domain not Implemented)
    expect(() => new ConditionalContinuousDomain([pd, Gt(u, half)]).set).toThrow(NotImplementedError);
    expect(show(new ConditionalContinuousDomain([pd, Gt(u, half)]).computeExpectation(mul(u, v)))).toBe('Integral(x*y, (x, 1/2, 1), (y, 0, 2))');
    expect(() => new ConditionalContinuousDomain([pd, Gt(u, v)]).computeExpectation(u)).toThrow('Multivariate Inequalities not yet implemented');
  });

  it('ConditionalContinuousDomain', () => {
    const cd = new ConditionalContinuousDomain([dX, and(Gt(u, half), Lt(u, Rational.of(3, 4)))]);
    expect(cd.isContinuous).toBe(true);
    expect(show(cd.computeExpectation(u))).toBe('Integral(x, (x, 1/2, 3/4))');
    expect(show(cd.set)).toBe('Interval.open(1/2, 3/4)');
    expect(show(cd.asBoolean())).toBe('(0 <= x) & (x <= 1) & (x > 1/2) & (x < 3/4)');
    expect(show(cd.computeExpectation(u, []))).toBe('x');
    expect(show(new ConditionalContinuousDomain([dX, S.true]).computeExpectation(u))).toBe('Integral(x, (x, 0, 1))');
    // a boolean other than And and Or adds nothing (SymPy)
    expect(show(new ConditionalContinuousDomain([dX, xor(Gt(u, half), Lt(u, Rational.of(1, 4)))]).computeExpectation(u))).toBe('Integral(x, (x, 0, 1))');
    expect(() => new ConditionalContinuousDomain([dX, or(Lt(u, Rational.of(1, 4)), Gt(u, Rational.of(3, 4)))]).computeExpectation(u)).toThrow('Or not implemented here');
    expect(() => new ConditionalContinuousDomain([dX, u]).computeExpectation(u)).toThrow(TypeError);
  });
});

describe('the continuous probability spaces (SymPy crv)', () => {
  const [u, v] = [new Sym('x'), new Sym('y')];
  const dX = new SingleContinuousDomain([u, Interval.of(0, 1)]);
  const dY = new SingleContinuousDomain([v, Interval.of(0, 2)]);

  it('a space of two variables', () => {
    const ps = new ContinuousPSpace([new ProductContinuousDomain([dX, dY]), Lambda([u, v], S.Half)]);
    const X = ps.values.find((r) => r.symbol.key === u.key) as RandomSymbol;
    expect(show(ps.computeDensity(X))).toBe('Lambda(x, Integral(1/2, (y, 0, 2)))');
    expect(show(ps.pdf)).toBe('1/2');
  });

  it('a domain that is not an interval', () => {
    const ps = new ContinuousPSpace([new SingleContinuousDomain([u, Union(Interval.of(0, 1), Interval.of(2, 3))]), Lambda(u, S.Half)]);
    const X = ps.values[0] as RandomSymbol;
    expect(() => ps.computeCdf(X)).toThrow('CDF not well defined on multivariate expressions');
    expect(() => ps.computeCharacteristicFunction(X)).toThrow('Characteristic function of multivariate expressions not implemented');
    expect(() => ps.computeMomentGeneratingFunction(X)).toThrow('Moment generating function of multivariate expressions not implemented');
    expect(() => ps.computeQuantile(X)).toThrow('Quantile not well defined on multivariate expressions');
  });

  it('probability without random symbols', () => {
    expect(show(Xn.pspace.probability(Ne(x, 1)))).toBe('1');
    expect(() => Xn.pspace.probability(Xn)).toThrow(TypeError);
  });

  it('densities of functions', () => {
    const c = new Sym('c');
    expect(show(ap(density(mul(c, Xn)), z))).toBe('sqrt(2)*exp(-z**2/(2*c**2))/(2*sqrt(pi)*Abs(c))');
    expect(show(ap(density(add(Xn, c)), z))).toBe('sqrt(2)*exp(-(-c + z)**2/2)/(2*sqrt(pi))');
    expect(show(ap(density(exp(Xn)), z))).toBe('sqrt(2)*exp(-log(z)**2/2)/(2*sqrt(pi)*Abs(z))');
  });
});
