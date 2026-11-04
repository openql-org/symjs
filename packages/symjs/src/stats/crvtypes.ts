// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/crv_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.crv_types: the continuous distributions and the
 * functions that create random symbols with them (`Normal('X', mu,
 * sigma)`, `Exponential('T', rate)`, ...).
 *
 * The parameters are checked as in SymPy (a parameter that is known to be
 * invalid raises a RangeError, SymPy's ValueError). Where SymPy's closed
 * form is mathematically wrong (the characteristic and moment generating
 * functions of QuadraticU), the correct one is used; the tests give
 * SymPy's value.
 */

import { BoolAtom, Dummy, Rational, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, exp, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, Lt, Ne, piecewise } from '../core/logic';
import { and } from '../core/boolalg';
import { Lambda, LambdaNode } from '../core/lambda';
import { Sum } from '../core/concrete';
import { isIntegerQ as isIntegerValued, isPositive, isReal } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined } from '../core/guard';
import { Interval, SetExpr, asRelational, interval } from '../sets/sets';
import { abs, asin, atan, cos, log, sin, sinh, tan } from '../functions/elementary/elementary';
import { Max, Min, beta as betaFn, binomial, erf, erfc, erfi, erfinv, expint, factorial, floor, gamma, lowergamma, sign, uppergamma, zeta } from '../functions/special/special';
import { besseli, besselj, besselk } from '../functions/special/bessel';
import { hyper } from '../functions/special/hyper';
import { integrate } from '../integrals/integrate';
import { isMatrixParam, isRandom, statsClasses, valueCheck } from './rv';
import { SingleContinuousDistribution, SingleContinuousPSpace, limitOver, realLine } from './crv';
import type { ClosedForm } from './crv';
import type { ComputeOptions, MatrixParam, RandomSymbol } from './rv';
import { cdf } from './rv';

const half = S.Half;

/** A scalar parameter (SymPy sympifies a parameter that is not a list or a matrix). */
const scalarParam = (v: ExprLike | MatrixParam): ExprLike => {
  if (isMatrixParam(v)) throw new TypeError('a scalar parameter is expected, not a vector or matrix');
  return v;
};
const neg = (e: ExprLike): Expr => mul(-1, e);
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));

/** Options of the functions that create random symbols. */
export interface RVOptions {
  /** false: the parameters are not checked (SymPy check=False). */
  readonly check?: boolean;
}

/** A continuous distribution class (constructed from its parameters). */
type DistributionClass = new (args: readonly Expr[]) => SingleContinuousDistribution;

/**
 * A random symbol with the distribution of the parameters (SymPy rv):
 * the parameters are checked, and random parameters give a compound
 * distribution.
 */
export function rv(symbol: string | Sym, cls: DistributionClass, params: readonly ExprLike[], opts: RVOptions = {}): RandomSymbol {
  const args = params.map(sympify);
  const dist = new cls(args);
  if (opts.check ?? true) dist.check();
  if (args.some((a) => isRandom(a))) return compoundValue(symbol, dist);
  return new SingleContinuousPSpace([typeof symbol === 'string' ? new Sym(symbol) : symbol, dist]).value;
}

/** The random symbol of a compound distribution (SymPy CompoundPSpace(symbol, CompoundDistribution(dist)).value). */
function compoundValue(symbol: string | Sym, dist: SingleContinuousDistribution): RandomSymbol {
  return defined(statsClasses.compound, 'compound_rv')(symbol, dist);
}

// ---------------------------------------------------------------------------
// Handmade distributions
// ---------------------------------------------------------------------------

/** SymPy ContinuousDistributionHandmade(pdf, set): a distribution given by a Lambda density on a set. */
export class ContinuousDistributionHandmade extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ContinuousDistributionHandmade', args.length === 1 ? [at(args, 0), realLine] : args);
  }
  get pdfLambda(): Expr {
    return this.arg(0);
  }
  override get set(): SetExpr {
    return cast(this.arg(1), SetExpr);
  }
  pdf(x: ExprLike): Expr {
    return cast(this.pdfLambda, LambdaNode, 'pdf').call(x);
  }
  override check(): void {
    const x = new Dummy('x');
    const [, a, b] = limitOver(x, this.set);
    const val = integrate(this.pdf(x), x, [a, b]);
    valueCheck(Eq(val, 1) !== S.false, 'The pdf on the given set is incorrect.');
  }
}

/**
 * A continuous random variable with the given density on a set (SymPy
 * ContinuousRV(symbol, density, set)). The density is not checked unless
 * `check` is true.
 */
export function ContinuousRV(symbol: Sym, densityIn: ExprLike, set: SetExpr = realLine, opts: RVOptions = {}): RandomSymbol {
  const pdf = Lambda(symbol, piecewise([densityIn, asRelational(set, symbol)], [0, true]));
  return rv(symbol.name, ContinuousDistributionHandmade, [pdf, set], { check: opts.check ?? false });
}

// ---------------------------------------------------------------------------
// The distributions (alphabetically, as in SymPy)
// ---------------------------------------------------------------------------

/** SymPy ArcsinDistribution(a, b). */
export class ArcsinDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ArcsinDistribution', args);
  }
  get a(): Expr {
    return this.arg(0);
  }
  get b(): Expr {
    return this.arg(1);
  }
  override get set(): SetExpr {
    return interval(this.a, this.b);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return pow(mul(S.Pi, sqrt(mul(sub(x, this.a), sub(this.b, x)))), -1);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const { a, b } = this;
    return piecewise([S.Zero, Lt(x, a)], [div(mul(2, asin(sqrt(div(sub(x, a), sub(b, a))))), S.Pi), Le(x, b)], [S.One, true]);
  }
}

/** Arcsin distribution on [a, b] (SymPy Arcsin(name, a=0, b=1)). */
export function Arcsin(name: string | Sym, a: ExprLike = 0, b: ExprLike = 1): RandomSymbol {
  return rv(name, ArcsinDistribution, [a, b]);
}

/** SymPy BeniniDistribution(alpha, beta, sigma). */
export class BeniniDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('BeniniDistribution', args);
  }
  override check(): void {
    const [alpha, beta, sigma] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(Gt(alpha, 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(beta, 0), 'Shape parameter Beta must be positive.');
    valueCheck(Gt(sigma, 0), 'Scale parameter Sigma must be positive.');
  }
  override get set(): SetExpr {
    return interval(this.arg(2), S.Infinity);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta, sigma] = [this.arg(0), this.arg(1), this.arg(2)];
    const l = log(div(x, sigma));
    return mul(exp(sub(mul(-1, alpha, l), mul(beta, pow(l, 2)))), add(div(alpha, x), div(mul(2, beta, l), x)));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function of the Benini distribution does not exist.');
  }
}

/** Benini distribution (SymPy Benini(name, alpha, beta, sigma)). */
export function Benini(name: string | Sym, alpha: ExprLike, beta: ExprLike, sigma: ExprLike): RandomSymbol {
  return rv(name, BeniniDistribution, [alpha, beta, sigma]);
}

/** SymPy BetaDistribution(alpha, beta). */
export class BetaDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('BetaDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, 1);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta] = [this.arg(0), this.arg(1)];
    return div(mul(pow(x, sub(alpha, 1)), pow(sub(1, x), sub(beta, 1))), betaFn(alpha, beta));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return hyper([this.arg(0)], [add(this.arg(0), this.arg(1))], mul(S.I, t));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return hyper([this.arg(0)], [add(this.arg(0), this.arg(1))], t);
  }
}

/** Beta distribution (SymPy Beta(name, alpha, beta)). */
export function Beta(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, BetaDistribution, [alpha, beta]);
}

/** SymPy BetaNoncentralDistribution(alpha, beta, lamda). */
export class BetaNoncentralDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('BetaNoncentralDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, 1);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
    valueCheck(Ge(this.arg(2), 0), 'Noncentrality parameter Lambda must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta, lamda] = [this.arg(0), this.arg(1), this.arg(2)];
    const k = new Dummy('k');
    const term = div(
      mul(exp(div(neg(lamda), 2)), pow(div(lamda, 2), k), pow(x, add(alpha, k, -1)), pow(sub(1, x), sub(beta, 1))),
      mul(factorial(k), betaFn(add(alpha, k), beta)),
    );
    return Sum(term, [k, 0, S.Infinity]);
  }
}

/** Noncentral Beta distribution (SymPy BetaNoncentral(name, alpha, beta, lamda)). */
export function BetaNoncentral(name: string | Sym, alpha: ExprLike, beta: ExprLike, lamda: ExprLike): RandomSymbol {
  return rv(name, BetaNoncentralDistribution, [alpha, beta, lamda]);
}

/** SymPy BetaPrimeDistribution(alpha, beta). */
export class BetaPrimeDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('BetaPrimeDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta] = [this.arg(0), this.arg(1)];
    return div(mul(pow(x, sub(alpha, 1)), pow(add(1, x), sub(neg(alpha), beta))), betaFn(alpha, beta));
  }
}

/** Beta prime distribution (SymPy BetaPrime(name, alpha, beta)). */
export function BetaPrime(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, BetaPrimeDistribution, [alpha, beta]);
}

/** SymPy BoundedParetoDistribution(alpha, left, right). */
export class BoundedParetoDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('BoundedParetoDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(1), this.arg(2));
  }
  override check(): void {
    const [alpha, left, right] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(isPositive(alpha), 'Shape must be positive.');
    valueCheck(isPositive(left), 'Left value should be positive.');
    valueCheck(Gt(right, left), 'Right should be greater than left.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, left, right] = [this.arg(0), this.arg(1), this.arg(2)];
    const num = mul(alpha, pow(left, alpha), pow(x, sub(neg(alpha), 1)));
    const den = sub(1, pow(div(left, right), alpha));
    return div(num, den);
  }
}

/** Bounded Pareto distribution (SymPy BoundedPareto(name, alpha, left, right)). */
export function BoundedPareto(name: string | Sym, alpha: ExprLike, left: ExprLike, right: ExprLike): RandomSymbol {
  return rv(name, BoundedParetoDistribution, [alpha, left, right]);
}

/** SymPy CauchyDistribution(x0, gamma). */
export class CauchyDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('CauchyDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter Gamma must be positive.');
    valueCheck(isReal(this.arg(0)), 'Location parameter must be real.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [x0, g] = [this.arg(0), this.arg(1)];
    return pow(mul(S.Pi, g, add(1, pow(div(sub(x, x0), g), 2))), -1);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [x0, g] = [this.arg(0), this.arg(1)];
    return add(mul(pow(S.Pi, -1), atan(div(sub(x, x0), g))), half);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return exp(sub(mul(this.arg(0), S.I, t), mul(this.arg(1), abs(t))));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function for the Cauchy distribution does not exist.');
  }
  protected override quantileClosed(p: Expr): ClosedForm {
    return add(this.arg(0), mul(this.arg(1), tan(mul(S.Pi, sub(p, half)))));
  }
}

/** Cauchy distribution (SymPy Cauchy(name, x0, gamma)). */
export function Cauchy(name: string | Sym, x0: ExprLike, gamma: ExprLike): RandomSymbol {
  return rv(name, CauchyDistribution, [x0, gamma]);
}

/** Positive and integer degrees of freedom (the checks of Chi and ChiSquared). */
function checkDegrees(k: Expr): void {
  valueCheck(Gt(k, 0), 'Number of degrees of freedom (k) must be positive.');
  valueCheck(isIntegerValued(k), 'Number of degrees of freedom (k) must be an integer.');
}

/** SymPy ChiDistribution(k). */
export class ChiDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ChiDistribution', args);
  }
  override check(): void {
    checkDegrees(this.arg(0));
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const k = this.arg(0);
    return div(mul(pow(2, sub(1, div(k, 2))), pow(x, sub(k, 1)), exp(div(neg(pow(x, 2)), 2))), gamma(div(k, 2)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const k = this.arg(0);
    const part1 = hyper([div(k, 2)], [half], div(neg(pow(t, 2)), 2));
    const part2 = div(mul(S.I, t, sqrt(2), gamma(div(add(k, 1), 2))), gamma(div(k, 2)));
    const part3 = hyper([div(add(k, 1), 2)], [Rational.of(3, 2)], div(neg(pow(t, 2)), 2));
    return add(part1, mul(part2, part3));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const k = this.arg(0);
    const part1 = hyper([div(k, 2)], [half], div(pow(t, 2), 2));
    const part2 = div(mul(t, sqrt(2), gamma(div(add(k, 1), 2))), gamma(div(k, 2)));
    const part3 = hyper([div(add(k, 1), 2)], [Rational.of(3, 2)], div(pow(t, 2), 2));
    return add(part1, mul(part2, part3));
  }
}

/** Chi distribution (SymPy Chi(name, k)); exported as `ChiRV` (`Chi` is the hyperbolic cosine integral). */
export function ChiRV(name: string | Sym, k: ExprLike): RandomSymbol {
  return rv(name, ChiDistribution, [k]);
}

/** SymPy ChiNoncentralDistribution(k, l). */
export class ChiNoncentralDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ChiNoncentralDistribution', args);
  }
  override check(): void {
    checkDegrees(this.arg(0));
    valueCheck(Gt(this.arg(1), 0), 'Shift parameter Lambda must be positive.');
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [k, l] = [this.arg(0), this.arg(1)];
    return mul(
      exp(div(neg(add(pow(x, 2), pow(l, 2))), 2)),
      pow(x, k),
      l,
      pow(pow(mul(l, x), div(k, 2)), -1),
      besseli(sub(div(k, 2), 1), mul(l, x)),
    );
  }
}

/** Noncentral Chi distribution (SymPy ChiNoncentral(name, k, l)). */
export function ChiNoncentral(name: string | Sym, k: ExprLike, l: ExprLike): RandomSymbol {
  return rv(name, ChiNoncentralDistribution, [k, l]);
}

/** SymPy ChiSquaredDistribution(k). */
export class ChiSquaredDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ChiSquaredDistribution', args);
  }
  override check(): void {
    checkDegrees(this.arg(0));
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const k = this.arg(0);
    return mul(pow(mul(pow(2, div(k, 2)), gamma(div(k, 2))), -1), pow(x, sub(div(k, 2), 1)), exp(div(neg(x), 2)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const k = this.arg(0);
    return piecewise([mul(pow(gamma(div(k, 2)), -1), lowergamma(div(k, 2), div(x, 2))), Ge(x, 0)], [0, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return pow(sub(1, mul(2, S.I, t)), div(neg(this.arg(0)), 2));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return pow(sub(1, mul(2, t)), div(neg(this.arg(0)), 2));
  }
}

/** Chi-squared distribution (SymPy ChiSquared(name, k)). */
export function ChiSquared(name: string | Sym, k: ExprLike): RandomSymbol {
  return rv(name, ChiSquaredDistribution, [k]);
}

/** SymPy DagumDistribution(p, a, b). */
export class DagumDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('DagumDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter p must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter a must be positive.');
    valueCheck(Gt(this.arg(2), 0), 'Scale parameter b must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [p, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(div(mul(a, p), x), div(pow(div(x, b), mul(a, p)), pow(add(pow(div(x, b), a), 1), add(p, 1))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [p, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise([pow(add(1, pow(div(x, b), neg(a))), neg(p)), Ge(x, 0)], [S.Zero, true]);
  }
}

/** Dagum distribution (SymPy Dagum(name, p, a, b)). */
export function Dagum(name: string | Sym, p: ExprLike, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, DagumDistribution, [p, a, b]);
}

/** SymPy DavisDistribution(b, n, mu). */
export class DavisDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('DavisDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter b must be positive.');
    valueCheck(Gt(this.arg(1), 1), 'Shape parameter n must be above 1.');
    valueCheck(Gt(this.arg(2), 0), 'Location parameter mu must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [b, n, mu] = [this.arg(0), this.arg(1), this.arg(2)];
    const dividend = mul(pow(b, n), pow(sub(x, mu), sub(-1, n)));
    const divisor = mul(sub(exp(div(b, sub(x, mu))), 1), mul(gamma(n), zeta(n)));
    return div(dividend, divisor);
  }
}

/** Davis distribution (SymPy Davis(name, b, n, mu)). */
export function Davis(name: string | Sym, b: ExprLike, n: ExprLike, mu: ExprLike): RandomSymbol {
  return rv(name, DavisDistribution, [b, n, mu]);
}

/** Erlang distribution: a Gamma distribution with shape k and scale 1/l (SymPy Erlang(name, k, l)). */
export function Erlang(name: string | Sym, k: ExprLike, l: ExprLike): RandomSymbol {
  return rv(name, GammaDistribution, [k, pow(l, -1)]);
}

/** SymPy ExGaussianDistribution(mean, std, rate). */
export class ExGaussianDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ExGaussianDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Standard deviation of ExGaussian must be positive.');
    valueCheck(Gt(this.arg(2), 0), 'Rate of ExGaussian must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mean, std, rate] = [this.arg(0), this.arg(1), this.arg(2)];
    const term1 = div(rate, 2);
    const term2 = exp(div(mul(rate, add(mul(2, mean), mul(rate, pow(std, 2)), mul(-2, x))), 2));
    const term3 = erfc(div(sub(add(mean, mul(rate, pow(std, 2))), x), mul(sqrt(2), std)));
    return mul(term1, term2, term3);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mean, std, rate] = [this.arg(0), this.arg(1), this.arg(2)];
    const u = mul(rate, sub(x, mean));
    const v = mul(rate, std);
    const gaussianCdf1 = cast(cdf(Normal('x', 0, v)), LambdaNode).call(u);
    const gaussianCdf2 = cast(cdf(Normal('x', pow(v, 2), v)), LambdaNode).call(u);
    return sub(gaussianCdf1, exp(add(neg(u), div(pow(v, 2), 2), log(gaussianCdf2))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mean, std, rate] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(pow(sub(1, div(mul(S.I, t), rate)), -1), exp(sub(mul(S.I, mean, t), div(mul(pow(std, 2), pow(t, 2)), 2))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mean, std, rate] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(pow(sub(1, div(t, rate)), -1), exp(add(mul(mean, t), div(mul(pow(std, 2), pow(t, 2)), 2))));
  }
}

/** Exponentially modified Gaussian distribution (SymPy ExGaussian(name, mean, std, rate)). */
export function ExGaussian(name: string | Sym, mean: ExprLike, std: ExprLike, rate: ExprLike): RandomSymbol {
  return rv(name, ExGaussianDistribution, [mean, std, rate]);
}

/** SymPy ExponentialDistribution(rate). */
export class ExponentialDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ExponentialDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Rate must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const rate = this.arg(0);
    return mul(rate, exp(mul(-1, rate, xIn)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    return piecewise([sub(1, exp(mul(-1, this.arg(0), x))), Ge(x, 0)], [0, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const rate = this.arg(0);
    return div(rate, sub(rate, mul(S.I, t)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const rate = this.arg(0);
    return div(rate, sub(rate, t));
  }
  protected override quantileClosed(p: Expr): ClosedForm {
    return div(neg(log(sub(1, p))), this.arg(0));
  }
}

/** Exponential distribution (SymPy Exponential(name, rate)). */
export function Exponential(name: string | Sym, rate: ExprLike): RandomSymbol {
  return rv(name, ExponentialDistribution, [rate]);
}

/** SymPy ExponentialPowerDistribution(mu, alpha, beta). */
export class ExponentialPowerDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ExponentialPowerDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter alpha must be positive.');
    valueCheck(Gt(this.arg(2), 0), 'Shape parameter beta must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, alpha, beta] = [this.arg(0), this.arg(1), this.arg(2)];
    const num = mul(beta, exp(neg(pow(div(abs(sub(x, mu)), alpha), beta))));
    const den = mul(2, alpha, gamma(pow(beta, -1)));
    return div(num, den);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, alpha, beta] = [this.arg(0), this.arg(1), this.arg(2)];
    const num = lowergamma(pow(beta, -1), pow(div(abs(sub(x, mu)), alpha), beta));
    const den = mul(2, gamma(pow(beta, -1)));
    return add(div(mul(sign(sub(x, mu)), num), den), half);
  }
}

/** Exponential power distribution (SymPy ExponentialPower(name, mu, alpha, beta)). */
export function ExponentialPower(name: string | Sym, mu: ExprLike, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, ExponentialPowerDistribution, [mu, alpha, beta]);
}

/** SymPy FDistributionDistribution(d1, d2). */
export class FDistributionDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('FDistributionDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    const [d1, d2] = [this.arg(0), this.arg(1)];
    valueCheck([Gt(d1, 0), isIntegerValued(d1)], 'Degrees of freedom d1 must be positive integer.');
    valueCheck([Gt(d2, 0), isIntegerValued(d2)], 'Degrees of freedom d2 must be positive integer.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [d1, d2] = [this.arg(0), this.arg(1)];
    return div(sqrt(div(mul(pow(mul(d1, x), d1), pow(d2, d2)), pow(add(mul(d1, x), d2), add(d1, d2)))), mul(x, betaFn(div(d1, 2), div(d2, 2))));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function for the F-distribution does not exist.');
  }
}

/** F distribution (SymPy FDistribution(name, d1, d2)). */
export function FDistribution(name: string | Sym, d1: ExprLike, d2: ExprLike): RandomSymbol {
  return rv(name, FDistributionDistribution, [d1, d2]);
}

/** SymPy FisherZDistribution(d1, d2). */
export class FisherZDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('FisherZDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Degree of freedom d1 must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Degree of freedom d2 must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [d1, d2] = [this.arg(0), this.arg(1)];
    return mul(
      div(mul(2, pow(d1, div(d1, 2)), pow(d2, div(d2, 2))), betaFn(div(d1, 2), div(d2, 2))),
      div(exp(mul(d1, x)), pow(add(mul(d1, exp(mul(2, x))), d2), div(add(d1, d2), 2))),
    );
  }
}

/** Fisher's z distribution (SymPy FisherZ(name, d1, d2)). */
export function FisherZ(name: string | Sym, d1: ExprLike, d2: ExprLike): RandomSymbol {
  return rv(name, FisherZDistribution, [d1, d2]);
}

/** SymPy FrechetDistribution(a, s=1, m=0). */
export class FrechetDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('FrechetDistribution', [at(args, 0), args[1] ?? S.One, args[2] ?? S.Zero]);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter s must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, s, m] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(div(a, s), pow(div(sub(x, m), s), sub(-1, a)), exp(neg(pow(div(sub(x, m), s), neg(a)))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [a, s, m] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise([exp(neg(pow(div(sub(x, m), s), neg(a)))), Ge(x, m)], [S.Zero, true]);
  }
}

/** Frechet distribution (SymPy Frechet(name, a, s=1, m=0)). */
export function Frechet(name: string | Sym, a: ExprLike, s: ExprLike = 1, m: ExprLike = 0): RandomSymbol {
  return rv(name, FrechetDistribution, [a, s, m]);
}

/** SymPy GammaDistribution(k, theta). */
export class GammaDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('GammaDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'k must be positive');
    valueCheck(Gt(this.arg(1), 0), 'Theta must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [k, theta] = [this.arg(0), this.arg(1)];
    return div(mul(pow(x, sub(k, 1)), exp(div(neg(x), theta))), mul(gamma(k), pow(theta, k)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [k, theta] = [this.arg(0), this.arg(1)];
    return piecewise([div(lowergamma(k, div(x, theta)), gamma(k)), Gt(x, 0)], [S.Zero, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return pow(sub(1, mul(this.arg(1), S.I, t)), neg(this.arg(0)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return pow(sub(1, mul(this.arg(1), t)), neg(this.arg(0)));
  }
}

/** Gamma distribution with shape k and scale theta (SymPy Gamma(name, k, theta)). */
export function Gamma(name: string | Sym, k: ExprLike, theta: ExprLike): RandomSymbol {
  return rv(name, GammaDistribution, [k, theta]);
}

/** SymPy GammaInverseDistribution(a, b). */
export class GammaInverseDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('GammaInverseDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'alpha must be positive');
    valueCheck(Gt(this.arg(1), 0), 'beta must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b] = [this.arg(0), this.arg(1)];
    return mul(div(pow(b, a), gamma(a)), pow(x, sub(neg(a), 1)), exp(div(neg(b), x)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [a, b] = [this.arg(0), this.arg(1)];
    return piecewise([div(uppergamma(a, div(b, x)), gamma(a)), Gt(x, 0)], [S.Zero, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [a, b] = [this.arg(0), this.arg(1)];
    return div(mul(2, pow(mul(-1, S.I, b, t), div(a, 2)), besselk(a, sqrt(mul(-4, S.I, b, t)))), gamma(a));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function for the gamma inverse distribution does not exist.');
  }
}

/** Inverse gamma distribution (SymPy GammaInverse(name, a, b)). */
export function GammaInverse(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, GammaInverseDistribution, [a, b]);
}

/** SymPy GumbelDistribution(beta, mu, minimum). */
export class GumbelDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('GumbelDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter beta must be positive.');
  }
  /** SymPy Piecewise((min_form, minimum), (max_form, not minimum)). */
  #select(minForm: Expr, maxForm: Expr): Expr {
    const minimum = this.arg(2);
    return piecewise([minForm, minimum], [maxForm, !(minimum instanceof BoolAtom && minimum.value)]);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [beta, mu] = [this.arg(0), this.arg(1)];
    const z = div(sub(x, mu), beta);
    const fMax = mul(pow(beta, -1), exp(sub(neg(z), exp(neg(z)))));
    const fMin = mul(pow(beta, -1), exp(sub(z, exp(z))));
    return this.#select(fMin, fMax);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [beta, mu] = [this.arg(0), this.arg(1)];
    const z = div(sub(x, mu), beta);
    return this.#select(sub(1, exp(neg(exp(z)))), exp(neg(exp(neg(z)))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [beta, mu] = [this.arg(0), this.arg(1)];
    const cfMax = mul(gamma(sub(1, mul(S.I, beta, t))), exp(mul(S.I, mu, t)));
    const cfMin = mul(gamma(add(1, mul(S.I, beta, t))), exp(mul(S.I, mu, t)));
    return this.#select(cfMin, cfMax);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [beta, mu] = [this.arg(0), this.arg(1)];
    const mgfMax = mul(gamma(sub(1, mul(beta, t))), exp(mul(mu, t)));
    const mgfMin = mul(gamma(add(1, mul(beta, t))), exp(mul(mu, t)));
    return this.#select(mgfMin, mgfMax);
  }
}

/** Gumbel distribution of the maximum, or of the minimum when `minimum` is true (SymPy Gumbel(name, beta, mu, minimum=False)). */
export function Gumbel(name: string | Sym, beta: ExprLike, mu: ExprLike, minimum: boolean = false): RandomSymbol {
  return rv(name, GumbelDistribution, [beta, mu, minimum ? S.true : S.false]);
}

/** SymPy GompertzDistribution(b, eta). */
export class GompertzDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('GompertzDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'b must be positive');
    valueCheck(Gt(this.arg(1), 0), 'eta must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [b, eta] = [this.arg(0), this.arg(1)];
    return mul(b, eta, exp(mul(b, x)), exp(eta), exp(mul(neg(eta), exp(mul(b, x)))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [b, eta] = [this.arg(0), this.arg(1)];
    return sub(1, mul(exp(eta), exp(mul(neg(eta), exp(mul(b, x))))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [b, eta] = [this.arg(0), this.arg(1)];
    return mul(eta, exp(eta), expint(div(t, b), eta));
  }
}

/** Gompertz distribution (SymPy Gompertz(name, b, eta)). */
export function Gompertz(name: string | Sym, b: ExprLike, eta: ExprLike): RandomSymbol {
  return rv(name, GompertzDistribution, [b, eta]);
}

/** SymPy KumaraswamyDistribution(a, b). */
export class KumaraswamyDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('KumaraswamyDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'a must be positive');
    valueCheck(Gt(this.arg(1), 0), 'b must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b] = [this.arg(0), this.arg(1)];
    return mul(a, b, pow(x, sub(a, 1)), pow(sub(1, pow(x, a)), sub(b, 1)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [a, b] = [this.arg(0), this.arg(1)];
    return piecewise([S.Zero, Lt(x, 0)], [sub(1, pow(sub(1, pow(x, a)), b)), Le(x, 1)], [S.One, true]);
  }
}

/** Kumaraswamy distribution (SymPy Kumaraswamy(name, a, b)). */
export function Kumaraswamy(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, KumaraswamyDistribution, [a, b]);
}

/** SymPy LaplaceDistribution(mu, b). */
export class LaplaceDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LaplaceDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter b must be positive.');
    valueCheck(isReal(this.arg(0)), 'Location parameter mu should be real');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, b] = [this.arg(0), this.arg(1)];
    return mul(pow(mul(2, b), -1), exp(div(neg(abs(sub(x, mu))), b)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, b] = [this.arg(0), this.arg(1)];
    return piecewise([mul(half, exp(div(sub(x, mu), b))), Lt(x, mu)], [sub(1, mul(half, exp(div(neg(sub(x, mu)), b)))), Ge(x, mu)]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return div(exp(mul(this.arg(0), S.I, t)), add(1, mul(pow(this.arg(1), 2), pow(t, 2))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return div(exp(mul(this.arg(0), t)), sub(1, mul(pow(this.arg(1), 2), pow(t, 2))));
  }
}

/** Laplace distribution (SymPy Laplace(name, mu, b)). */
export function Laplace(name: string | Sym, mu: ExprLike | MatrixParam, b: ExprLike | MatrixParam): RandomSymbol {
  // vector and matrix parameters give the multivariate distribution
  if (isMatrixParam(mu) && isMatrixParam(b)) return defined(statsClasses.multivariateLaplace, 'joint_rv_types')(name, mu, b);
  return rv(name, LaplaceDistribution, [scalarParam(mu), scalarParam(b)]);
}

/** SymPy LevyDistribution(mu, c). */
export class LevyDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LevyDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(0), S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'c (scale parameter) must be positive');
    valueCheck(isReal(this.arg(0)), 'mu (location parameter) must be real');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, c] = [this.arg(0), this.arg(1)];
    return div(mul(sqrt(div(c, mul(2, S.Pi))), exp(div(neg(c), mul(2, sub(x, mu))))), pow(sub(x, mu), div(3, 2)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, c] = [this.arg(0), this.arg(1)];
    return erfc(sqrt(div(c, mul(2, sub(x, mu)))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu, c] = [this.arg(0), this.arg(1)];
    return exp(sub(mul(S.I, mu, t), sqrt(mul(-2, S.I, c, t))));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function of Levy distribution does not exist.');
  }
}

/** Levy distribution (SymPy Levy(name, mu, c)). */
export function Levy(name: string | Sym, mu: ExprLike, c: ExprLike): RandomSymbol {
  return rv(name, LevyDistribution, [mu, c]);
}

/** SymPy LogCauchyDistribution(mu, sigma). */
export class LogCauchyDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LogCauchyDistribution', args);
  }
  override get set(): SetExpr {
    return Interval.open(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0) !== S.false, 'Scale parameter Gamma must be positive.');
    valueCheck(isReal(this.arg(0)) !== false, 'Location parameter must be real.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    return mul(pow(mul(x, S.Pi), -1), div(sigma, add(pow(sub(log(x), mu), 2), pow(sigma, 2))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    return add(mul(pow(S.Pi, -1), atan(div(sub(log(x), mu), sigma))), half);
  }
  protected override characteristicFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The characteristic function for the Log-Cauchy distribution does not exist.');
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function for the Log-Cauchy distribution does not exist.');
  }
}

/** Log-Cauchy distribution (SymPy LogCauchy(name, mu, sigma)). */
export function LogCauchy(name: string | Sym, mu: ExprLike, sigma: ExprLike): RandomSymbol {
  return rv(name, LogCauchyDistribution, [mu, sigma]);
}

/** SymPy LogisticDistribution(mu, s). */
export class LogisticDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LogisticDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter s must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, s] = [this.arg(0), this.arg(1)];
    return div(exp(div(neg(sub(x, mu)), s)), mul(s, pow(add(1, exp(div(neg(sub(x, mu)), s))), 2)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return pow(add(1, exp(div(neg(sub(x, mu)), s))), -1);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return piecewise([div(mul(exp(mul(S.I, t, mu)), S.Pi, s, t), sinh(mul(S.Pi, s, t))), Ne(t, 0)], [S.One, true]);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return mul(exp(mul(mu, t)), betaFn(sub(1, mul(s, t)), add(1, mul(s, t))));
  }
  protected override quantileClosed(p: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return sub(mu, mul(s, log(add(-1, pow(p, -1)))));
  }
}

/** Logistic distribution (SymPy Logistic(name, mu, s)). */
export function Logistic(name: string | Sym, mu: ExprLike, s: ExprLike): RandomSymbol {
  return rv(name, LogisticDistribution, [mu, s]);
}

/** SymPy LogLogisticDistribution(alpha, beta). */
export class LogLogisticDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LogLogisticDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b] = [this.arg(0), this.arg(1)];
    return div(mul(div(b, a), pow(div(x, a), sub(b, 1))), pow(add(1, pow(div(x, a), b)), 2));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [a, b] = [this.arg(0), this.arg(1)];
    return pow(add(1, pow(div(x, a), neg(b))), -1);
  }
  protected override quantileClosed(p: Expr): ClosedForm {
    const [a, b] = [this.arg(0), this.arg(1)];
    return mul(a, pow(div(p, sub(1, p)), pow(b, -1)));
  }
  /**
   * The mean in closed form (SymPy LogLogisticDistribution.expectation).
   * SymPy returns it for any expression (E(X**2) is the mean there); here
   * only the expectation of the variable itself is the mean.
   */
  override expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    if (expr.key !== v.key || opts.evaluate === false) return super.expectation(expr, v, opts);
    const [a, b] = [this.arg(0), this.arg(1)];
    return piecewise([S.NaN, Le(b, 1)], [div(mul(S.Pi, a), mul(b, sin(div(S.Pi, b)))), true]);
  }
}

/** Log-logistic distribution (SymPy LogLogistic(name, alpha, beta)). */
export function LogLogistic(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, LogLogisticDistribution, [alpha, beta]);
}

/** SymPy LogitNormalDistribution(mu, s). */
export class LogitNormalDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LogitNormalDistribution', args);
  }
  override get set(): SetExpr {
    return Interval.open(0, 1);
  }
  override check(): void {
    const [mu, s] = [this.arg(0), this.arg(1)];
    // SymPy: (s**2).is_real is not False and s**2 > 0
    const s2 = pow(s, 2);
    valueCheck(isReal(s2) === false ? false : Gt(s2, 0), 'Squared scale parameter s must be positive.');
    valueCheck(isReal(mu) !== false, 'Location parameter must be real');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, s] = [this.arg(0), this.arg(1)];
    const logit = log(div(x, sub(1, x)));
    return mul(exp(div(neg(pow(sub(logit, mu), 2)), mul(2, pow(s, 2)))), pow(sqrt(mul(2, S.Pi, pow(s, 2))), -1), pow(mul(x, sub(1, x)), -1));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return mul(half, add(1, erf(div(sub(log(div(x, sub(1, x))), mu), sqrt(mul(2, pow(s, 2)))))));
  }
}

/** Logit-normal distribution (SymPy LogitNormal(name, mu, s)). */
export function LogitNormal(name: string | Sym, mu: ExprLike, s: ExprLike): RandomSymbol {
  return rv(name, LogitNormalDistribution, [mu, s]);
}

/** SymPy LogNormalDistribution(mean, std). */
export class LogNormalDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LogNormalDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Parameter std must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mean, std] = [this.arg(0), this.arg(1)];
    return div(exp(div(neg(pow(sub(log(x), mean), 2)), mul(2, pow(std, 2)))), mul(x, sqrt(mul(2, S.Pi)), std));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mean, std] = [this.arg(0), this.arg(1)];
    return piecewise([add(half, mul(half, erf(div(div(sub(log(x), mean), sqrt(2)), std)))), Gt(x, 0)], [S.Zero, true]);
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('Moment generating function of the log-normal distribution is not defined.');
  }
}

/** Log-normal distribution (SymPy LogNormal(name, mean, std)). */
export function LogNormal(name: string | Sym, mean: ExprLike, std: ExprLike): RandomSymbol {
  return rv(name, LogNormalDistribution, [mean, std]);
}

/** SymPy LomaxDistribution(alpha, lamda). */
export class LomaxDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('LomaxDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    const [alpha, lamda] = [this.arg(0), this.arg(1)];
    valueCheck(isReal(alpha), 'Shape parameter should be real.');
    valueCheck(isReal(lamda), 'Scale parameter should be real.');
    valueCheck(isPositive(alpha), 'Shape parameter should be positive.');
    valueCheck(isPositive(lamda), 'Scale parameter should be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, lamda] = [this.arg(0), this.arg(1)];
    return mul(div(alpha, lamda), pow(add(1, div(x, lamda)), sub(neg(alpha), 1)));
  }
}

/** Lomax distribution (SymPy Lomax(name, alpha, lamda)). */
export function Lomax(name: string | Sym, alpha: ExprLike, lamda: ExprLike): RandomSymbol {
  return rv(name, LomaxDistribution, [alpha, lamda]);
}

/** SymPy MaxwellDistribution(a). */
export class MaxwellDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('MaxwellDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Parameter a must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const a = this.arg(0);
    return div(mul(sqrt(div(2, S.Pi)), pow(x, 2), exp(div(neg(pow(x, 2)), mul(2, pow(a, 2))))), pow(a, 3));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const a = this.arg(0);
    return sub(erf(div(mul(sqrt(2), x), mul(2, a))), div(mul(sqrt(2), x, exp(div(neg(pow(x, 2)), mul(2, pow(a, 2))))), mul(sqrt(S.Pi), a)));
  }
}

/** Maxwell distribution (SymPy Maxwell(name, a)). */
export function Maxwell(name: string | Sym, a: ExprLike): RandomSymbol {
  return rv(name, MaxwellDistribution, [a]);
}

/** SymPy MoyalDistribution(mu, sigma). */
export class MoyalDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('MoyalDistribution', args);
  }
  override check(): void {
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    valueCheck(isReal(mu), 'Location parameter must be real.');
    // SymPy: sigma.is_real and sigma > 0
    const r = isReal(sigma);
    valueCheck(r === true ? Gt(sigma, 0) : r, 'Scale parameter must be real        and positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    // SymPy: exp(-(exp(-(x - mu)/sigma) + (x - mu)/sigma)/2), whose -(x - mu) is mu - x
    const num = exp(div(neg(add(exp(div(neg(sub(x, mu)), sigma)), div(sub(x, mu), sigma))), 2));
    const den = mul(sqrt(mul(2, S.Pi)), sigma);
    return div(num, den);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    const term1 = exp(mul(S.I, t, mu));
    const term2 = mul(pow(2, mul(-1, S.I, sigma, t)), gamma(sub(half, mul(S.I, t, sigma))));
    return div(mul(term1, term2), sqrt(S.Pi));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    const term1 = exp(mul(t, mu));
    const term2 = mul(pow(2, mul(-1, sigma, t)), gamma(sub(half, mul(t, sigma))));
    return div(mul(term1, term2), sqrt(S.Pi));
  }
}

/** Moyal distribution (SymPy Moyal(name, mu, sigma)). */
export function Moyal(name: string | Sym, mu: ExprLike, sigma: ExprLike): RandomSymbol {
  return rv(name, MoyalDistribution, [mu, sigma]);
}

/** SymPy NakagamiDistribution(mu, omega). */
export class NakagamiDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('NakagamiDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Ge(this.arg(0), half), 'Shape parameter mu must be greater than equal to 1/2.');
    valueCheck(Gt(this.arg(1), 0), 'Spread parameter omega must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, omega] = [this.arg(0), this.arg(1)];
    return mul(div(mul(2, pow(mu, mu)), mul(gamma(mu), pow(omega, mu))), pow(x, sub(mul(2, mu), 1)), exp(mul(div(neg(mu), omega), pow(x, 2))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, omega] = [this.arg(0), this.arg(1)];
    return piecewise([div(lowergamma(mu, mul(div(mu, omega), pow(x, 2))), gamma(mu)), Gt(x, 0)], [S.Zero, true]);
  }
}

/** Nakagami distribution (SymPy Nakagami(name, mu, omega)). */
export function Nakagami(name: string | Sym, mu: ExprLike, omega: ExprLike): RandomSymbol {
  return rv(name, NakagamiDistribution, [mu, omega]);
}

/** SymPy NormalDistribution(mean, std). */
export class NormalDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('NormalDistribution', args);
  }
  get mean(): Expr {
    return this.arg(0);
  }
  get std(): Expr {
    return this.arg(1);
  }
  override check(): void {
    valueCheck(Gt(this.std, 0), 'Standard deviation must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return div(exp(div(neg(pow(sub(x, this.mean), 2)), mul(2, pow(this.std, 2)))), mul(sqrt(mul(2, S.Pi)), this.std));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    return add(div(erf(div(mul(sqrt(2), add(neg(this.mean), x)), mul(2, this.std))), 2), half);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return exp(sub(mul(S.I, this.mean, t), div(mul(pow(this.std, 2), pow(t, 2)), 2)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return exp(add(mul(this.mean, t), div(mul(pow(this.std, 2), pow(t, 2)), 2)));
  }
  protected override quantileClosed(p: Expr): ClosedForm {
    return add(this.mean, mul(this.std, sqrt(2), erfinv(sub(mul(2, p), 1))));
  }
}

/** Normal (Gaussian) distribution (SymPy Normal(name, mean, std)). */
export function Normal(name: string | Sym, mean: ExprLike | MatrixParam, std: ExprLike | MatrixParam): RandomSymbol {
  // vector and matrix parameters give the multivariate distribution (SymPy: a list mean, or a matrix mean and a list std, or a matrix std)
  if ((Array.isArray(mean) || (isMatrixParam(mean) && Array.isArray(std)) || isMatrixParam(std)) && isMatrixParam(mean) && isMatrixParam(std)) {
    return defined(statsClasses.multivariateNormal, 'joint_rv_types')(name, mean, std);
  }
  return rv(name, NormalDistribution, [scalarParam(mean), scalarParam(std)]);
}

/** SymPy GaussianInverseDistribution(mean, shape). */
export class GaussianInverseDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('GaussianInverseDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter must be positive');
    valueCheck(Gt(this.arg(0), 0), 'Mean must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, s] = [this.arg(0), this.arg(1)];
    return mul(exp(div(mul(neg(s), pow(sub(x, mu), 2)), mul(2, x, pow(mu, 2)))), sqrt(div(s, mul(2, S.Pi, pow(x, 3)))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    const stdNormalCdf = cast(cdf(Normal('x', 0, 1)), LambdaNode);
    const firstTerm = stdNormalCdf.call(mul(sqrt(div(s, x)), sub(div(x, mu), 1)));
    const secondTerm = mul(exp(div(mul(2, s), mu)), stdNormalCdf.call(mul(neg(sqrt(div(s, x))), add(div(x, mu), 1))));
    return add(firstTerm, secondTerm);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return exp(mul(div(s, mu), sub(1, sqrt(sub(1, div(mul(2, pow(mu, 2), S.I, t), s))))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return exp(mul(div(s, mu), sub(1, sqrt(sub(1, div(mul(2, pow(mu, 2), t), s))))));
  }
}

/** Inverse Gaussian distribution (SymPy GaussianInverse(name, mean, shape)). */
export function GaussianInverse(name: string | Sym, mean: ExprLike, shape: ExprLike): RandomSymbol {
  return rv(name, GaussianInverseDistribution, [mean, shape]);
}

/** Wald distribution: SymPy's alias of GaussianInverse. */
export const Wald = GaussianInverse;

/** SymPy ParetoDistribution(xm, alpha). */
export class ParetoDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ParetoDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(0), S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Xm must be positive');
    valueCheck(Gt(this.arg(1), 0), 'Alpha must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [xm, alpha] = [this.arg(0), this.arg(1)];
    return div(mul(alpha, pow(xm, alpha)), pow(x, add(alpha, 1)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const [xm, alpha] = [this.arg(0), this.arg(1)];
    return piecewise([sub(1, div(pow(xm, alpha), pow(x, alpha))), Ge(x, xm)], [0, true]);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [xm, alpha] = [this.arg(0), this.arg(1)];
    return mul(alpha, pow(mul(neg(xm), t), alpha), uppergamma(neg(alpha), mul(neg(xm), t)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [xm, alpha] = [this.arg(0), this.arg(1)];
    return mul(alpha, pow(mul(-1, S.I, xm, t), alpha), uppergamma(neg(alpha), mul(-1, S.I, xm, t)));
  }
}

/** Pareto distribution (SymPy Pareto(name, xm, alpha)). */
export function Pareto(name: string | Sym, xm: ExprLike, alpha: ExprLike): RandomSymbol {
  return rv(name, ParetoDistribution, [xm, alpha]);
}

/** SymPy PowerFunctionDistribution(alpha, a, b). */
export class PowerFunctionDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('PowerFunctionDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(1), this.arg(2));
  }
  override check(): void {
    const [alpha, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(isReal(a), 'Continuous Boundary parameter should be real.');
    valueCheck(isReal(b), 'Continuous Boundary parameter should be real.');
    valueCheck(Lt(a, b), " 'a' the left Boundary must be smaller than 'b' the right Boundary.");
    valueCheck(isPositive(alpha), 'Continuous Shape parameter should be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    return div(mul(alpha, pow(sub(x, a), sub(alpha, 1))), pow(sub(b, a), alpha));
  }
}

/** Power function distribution (SymPy PowerFunction(name, alpha, a, b)). */
export function PowerFunction(name: string | Sym, alpha: ExprLike, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, PowerFunctionDistribution, [alpha, a, b]);
}

/** SymPy QuadraticUDistribution(a, b). */
export class QuadraticUDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('QuadraticUDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(1));
  }
  override check(): void {
    const [a, b] = [this.arg(0), this.arg(1)];
    valueCheck(Gt(b, a), `Parameter b must be in range (${a.toString()}, oo).`);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b] = [this.arg(0), this.arg(1)];
    const alpha = div(12, pow(sub(b, a), 3));
    const beta = div(add(a, b), 2);
    return piecewise([mul(alpha, pow(sub(x, beta), 2)), and(Le(a, x), Le(x, b))], [S.Zero, true]);
  }
  /**
   * The integral of 12/(b - a)**3*(x - (a + b)/2)**2*exp(u*x) over [a, b]
   * with h = (b - a)/2. SymPy's closed forms of the moment generating and
   * characteristic functions are wrong (the mean they give for
   * QuadraticU(1, 3) is -11 instead of 2).
   */
  #transform(u: Expr): Expr {
    const [a, b] = [this.arg(0), this.arg(1)];
    const h = div(sub(b, a), 2);
    const tail = (sgn: number): Expr => add(div(pow(h, 2), u), mul(sgn * -2, div(h, pow(u, 2))), div(2, pow(u, 3)));
    return mul(div(12, pow(sub(b, a), 3)), sub(mul(exp(mul(b, u)), tail(1)), mul(exp(mul(a, u)), tail(-1))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return this.#transform(t);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return this.#transform(mul(S.I, t));
  }
}

/** U-quadratic distribution on [a, b] (SymPy QuadraticU(name, a, b)). */
export function QuadraticU(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, QuadraticUDistribution, [a, b]);
}

/** SymPy RaisedCosineDistribution(mu, s). */
export class RaisedCosineDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('RaisedCosineDistribution', args);
  }
  override get set(): SetExpr {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return interval(sub(mu, s), add(mu, s));
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 's must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, s] = [this.arg(0), this.arg(1)];
    return piecewise([div(add(1, cos(div(mul(S.Pi, sub(x, mu)), s))), mul(2, s)), and(Le(sub(mu, s), x), Le(x, add(mu, s)))], [S.Zero, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return piecewise(
      [div(exp(div(mul(-1, S.I, S.Pi, mu), s)), 2), Eq(t, div(neg(S.Pi), s))],
      [div(exp(div(mul(S.I, S.Pi, mu), s)), 2), Eq(t, div(S.Pi, s))],
      [div(mul(pow(S.Pi, 2), sin(mul(s, t)), exp(mul(S.I, mu, t))), mul(s, t, sub(pow(S.Pi, 2), mul(pow(s, 2), pow(t, 2))))), true],
    );
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return div(mul(pow(S.Pi, 2), sinh(mul(s, t)), exp(mul(mu, t))), mul(s, t, add(pow(S.Pi, 2), mul(pow(s, 2), pow(t, 2)))));
  }
}

/** Raised cosine distribution (SymPy RaisedCosine(name, mu, s)). */
export function RaisedCosine(name: string | Sym, mu: ExprLike, s: ExprLike): RandomSymbol {
  return rv(name, RaisedCosineDistribution, [mu, s]);
}

/** SymPy RayleighDistribution(sigma). */
export class RayleighDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('RayleighDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter sigma must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const sigma = this.arg(0);
    return mul(div(x, pow(sigma, 2)), exp(div(neg(pow(x, 2)), mul(2, pow(sigma, 2)))));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const sigma = this.arg(0);
    return sub(1, exp(neg(div(pow(x, 2), mul(2, pow(sigma, 2))))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const sigma = this.arg(0);
    return sub(1, mul(sigma, t, exp(div(mul(-1, pow(sigma, 2), pow(t, 2)), 2)), sqrt(div(S.Pi, 2)), sub(erfi(div(mul(sigma, t), sqrt(2))), S.I)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const sigma = this.arg(0);
    return add(1, mul(sigma, t, exp(div(mul(pow(sigma, 2), pow(t, 2)), 2)), sqrt(div(S.Pi, 2)), add(erf(div(mul(sigma, t), sqrt(2))), 1)));
  }
}

/** Rayleigh distribution (SymPy Rayleigh(name, sigma)). */
export function Rayleigh(name: string | Sym, sigma: ExprLike): RandomSymbol {
  return rv(name, RayleighDistribution, [sigma]);
}

/** SymPy ReciprocalDistribution(a, b). */
export class ReciprocalDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ReciprocalDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(1));
  }
  override check(): void {
    const [a, b] = [this.arg(0), this.arg(1)];
    valueCheck(Gt(a, 0), `Parameter > 0. a = ${a.toString()}`);
    valueCheck(Lt(a, b), `Parameter b must be in range (${a.toString()}, +oo]. b = ${b.toString()}`);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b] = [this.arg(0), this.arg(1)];
    return pow(mul(x, sub(log(b), log(a))), -1);
  }
}

/** Reciprocal distribution (SymPy Reciprocal(name, a, b)). */
export function Reciprocal(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, ReciprocalDistribution, [a, b]);
}

/** SymPy ShiftedGompertzDistribution(b, eta). */
export class ShiftedGompertzDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('ShiftedGompertzDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'b must be positive');
    valueCheck(Gt(this.arg(1), 0), 'eta must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [b, eta] = [this.arg(0), this.arg(1)];
    const e = exp(mul(neg(b), x));
    return mul(b, e, exp(mul(neg(eta), e)), add(1, mul(eta, sub(1, e))));
  }
}

/** Shifted Gompertz distribution (SymPy ShiftedGompertz(name, b, eta)). */
export function ShiftedGompertz(name: string | Sym, b: ExprLike, eta: ExprLike): RandomSymbol {
  return rv(name, ShiftedGompertzDistribution, [b, eta]);
}

/** SymPy StudentTDistribution(nu). */
export class StudentTDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('StudentTDistribution', args);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Degrees of freedom nu must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const nu = this.arg(0);
    return mul(pow(mul(sqrt(nu), betaFn(half, div(nu, 2))), -1), pow(add(1, div(pow(x, 2), nu)), div(neg(add(nu, 1)), 2)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const nu = this.arg(0);
    return add(half, div(mul(x, gamma(div(add(nu, 1), 2)), hyper([half, div(add(nu, 1), 2)], [div(3, 2)], div(neg(pow(x, 2)), nu))), mul(sqrt(mul(S.Pi, nu)), gamma(div(nu, 2)))));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function for the Student-T distribution is undefined.');
  }
}

/** Student's t distribution (SymPy StudentT(name, nu)). */
export function StudentT(name: string | Sym, nu: ExprLike): RandomSymbol {
  return rv(name, StudentTDistribution, [nu]);
}

/** SymPy TrapezoidalDistribution(a, b, c, d). */
export class TrapezoidalDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('TrapezoidalDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(3));
  }
  override check(): void {
    const [a, b, c, d] = [this.arg(0), this.arg(1), this.arg(2), this.arg(3)];
    const s = (e: Expr): string => e.toString();
    valueCheck(Lt(a, d), `Lower bound parameter a < ${s(d)}. a = ${s(a)}`);
    valueCheck([Le(a, b), Lt(b, c)], `Level start parameter b must be in range [${s(a)}, ${s(c)}). b = ${s(b)}`);
    valueCheck([Lt(b, c), Le(c, d)], `Level end parameter c must be in range (${s(b)}, ${s(d)}]. c = ${s(c)}`);
    valueCheck(Ge(d, c), `Upper bound parameter d > ${s(c)}. d = ${s(d)}`);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b, c, d] = [this.arg(0), this.arg(1), this.arg(2), this.arg(3)];
    const w = sub(add(d, c), add(a, b));
    return piecewise(
      [div(mul(2, sub(x, a)), mul(sub(b, a), w)), and(Le(a, x), Lt(x, b))],
      [div(2, w), and(Le(b, x), Lt(x, c))],
      [div(mul(2, sub(d, x)), mul(sub(d, c), w)), and(Le(c, x), Le(x, d))],
      [S.Zero, true],
    );
  }
}

/** Trapezoidal distribution (SymPy Trapezoidal(name, a, b, c, d)). */
export function Trapezoidal(name: string | Sym, a: ExprLike, b: ExprLike, c: ExprLike, d: ExprLike): RandomSymbol {
  return rv(name, TrapezoidalDistribution, [a, b, c, d]);
}

/** SymPy TriangularDistribution(a, b, c). */
export class TriangularDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('TriangularDistribution', args);
  }
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(1));
  }
  override check(): void {
    const [a, b, c] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(Gt(b, a), `Parameter b > ${a.toString()}. b = ${b.toString()}`);
    valueCheck([Le(a, c), Le(c, b)], `Parameter c must be in range [${a.toString()}, ${b.toString()}]. c = ${c.toString()}`);
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b, c] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise(
      [div(mul(2, sub(x, a)), mul(sub(b, a), sub(c, a))), and(Le(a, x), Lt(x, c))],
      [div(2, sub(b, a)), Eq(x, c)],
      [div(mul(2, sub(b, x)), mul(sub(b, a), sub(b, c))), and(Lt(c, x), Le(x, b))],
      [S.Zero, true],
    );
  }
  /** The characteristic (u = I*t) or moment generating (u = t) function. */
  #transform(u: Expr, t: Expr, sgn: number): Expr {
    const [a, b, c] = [this.arg(0), this.arg(1), this.arg(2)];
    const num = add(mul(sub(b, c), exp(mul(a, u))), mul(-1, sub(b, a), exp(mul(c, u))), mul(sub(c, a), exp(mul(b, u))));
    return div(mul(2 * sgn, num), mul(sub(b, a), sub(c, a), sub(b, c), pow(t, 2)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return this.#transform(mul(S.I, t), t, -1);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return this.#transform(t, t, 1);
  }
}

/** Triangular distribution (SymPy Triangular(name, a, b, c)). */
export function Triangular(name: string | Sym, a: ExprLike, b: ExprLike, c: ExprLike): RandomSymbol {
  return rv(name, TriangularDistribution, [a, b, c]);
}

/** SymPy UniformDistribution(left, right). */
export class UniformDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('UniformDistribution', args);
  }
  get left(): Expr {
    return this.arg(0);
  }
  get right(): Expr {
    return this.arg(1);
  }
  override get set(): SetExpr {
    return interval(this.left, this.right);
  }
  override check(): void {
    valueCheck(Lt(this.left, this.right), 'Lower limit should be less than Upper limit.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const { left, right } = this;
    return piecewise([pow(sub(right, left), -1), and(Le(left, x), Le(x, right))], [S.Zero, true]);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const { left, right } = this;
    return piecewise([S.Zero, Lt(x, left)], [div(sub(x, left), sub(right, left)), Le(x, right)], [S.One, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const { left, right } = this;
    return piecewise([div(sub(exp(mul(S.I, t, right)), exp(mul(S.I, t, left))), mul(S.I, t, sub(right, left))), Ne(t, 0)], [S.One, true]);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const { left, right } = this;
    return piecewise([div(sub(exp(mul(t, right)), exp(mul(t, left))), mul(t, sub(right, left))), Ne(t, 0)], [S.One, true]);
  }
  /** SymPy UniformDistribution.expectation: evaluated, with Max(left, right) = right and Min(left, right) = left. */
  override expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    const r = super.expectation(expr, v, { ...opts, evaluate: true });
    return r.subs([
      [Max(this.left, this.right), this.right],
      [Min(this.left, this.right), this.left],
    ]);
  }
}

/** Uniform distribution on [left, right] (SymPy Uniform(name, left, right)). */
export function Uniform(name: string | Sym, left: ExprLike, right: ExprLike): RandomSymbol {
  return rv(name, UniformDistribution, [left, right]);
}

/** SymPy UniformSumDistribution(n): the Irwin-Hall distribution. */
export class UniformSumDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('UniformSumDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, this.arg(0));
  }
  override check(): void {
    const n = this.arg(0);
    valueCheck([Gt(n, 0), isIntegerValued(n)], 'Parameter n must be positive integer.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const n = this.arg(0);
    const k = new Dummy('k');
    return mul(pow(factorial(sub(n, 1)), -1), Sum(mul(pow(-1, k), binomial(n, k), pow(sub(x, k), sub(n, 1))), [k, 0, floor(x)]));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const n = this.arg(0);
    const k = new Dummy('k');
    return piecewise(
      [S.Zero, Lt(x, 0)],
      [mul(pow(factorial(n), -1), Sum(mul(pow(-1, k), binomial(n, k), pow(sub(x, k), n)), [k, 0, floor(x)])), Le(x, n)],
      [S.One, true],
    );
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return pow(div(sub(exp(mul(S.I, t)), 1), mul(S.I, t)), this.arg(0));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return pow(div(sub(exp(t), 1), t), this.arg(0));
  }
}

/** Uniform sum (Irwin-Hall) distribution (SymPy UniformSum(name, n)). */
export function UniformSum(name: string | Sym, n: ExprLike): RandomSymbol {
  return rv(name, UniformSumDistribution, [n]);
}

/** SymPy VonMisesDistribution(mu, k). */
export class VonMisesDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('VonMisesDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, mul(2, S.Pi));
  }
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'k must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, k] = [this.arg(0), this.arg(1)];
    return div(exp(mul(k, cos(sub(x, mu)))), mul(2, S.Pi, besseli(0, k)));
  }
}

/** Von Mises distribution (SymPy VonMises(name, mu, k)). */
export function VonMises(name: string | Sym, mu: ExprLike, k: ExprLike): RandomSymbol {
  return rv(name, VonMisesDistribution, [mu, k]);
}

/** SymPy WeibullDistribution(alpha, beta). */
export class WeibullDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('WeibullDistribution', args);
  }
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Alpha must be positive');
    valueCheck(Gt(this.arg(1), 0), 'Beta must be positive');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta] = [this.arg(0), this.arg(1)];
    return div(mul(beta, pow(div(x, alpha), sub(beta, 1)), exp(neg(pow(div(x, alpha), beta)))), alpha);
  }
}

/** Weibull distribution (SymPy Weibull(name, alpha, beta)). */
export function Weibull(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, WeibullDistribution, [alpha, beta]);
}

/** SymPy WignerSemicircleDistribution(R). */
export class WignerSemicircleDistribution extends SingleContinuousDistribution {
  constructor(args: readonly Expr[]) {
    super('WignerSemicircleDistribution', args);
  }
  override get set(): SetExpr {
    return interval(neg(this.arg(0)), this.arg(0));
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Radius R must be positive.');
  }
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const R = this.arg(0);
    return mul(div(2, mul(S.Pi, pow(R, 2))), sqrt(sub(pow(R, 2), pow(x, 2))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const R = this.arg(0);
    return piecewise([div(mul(2, besselj(1, mul(R, t))), mul(R, t)), Ne(t, 0)], [S.One, true]);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const R = this.arg(0);
    return piecewise([div(mul(2, besseli(1, mul(R, t))), mul(R, t)), Ne(t, 0)], [S.One, true]);
  }
}

/** Wigner semicircle distribution (SymPy WignerSemicircle(name, R)). */
export function WignerSemicircle(name: string | Sym, R: ExprLike): RandomSymbol {
  return rv(name, WignerSemicircleDistribution, [R]);
}

statsClasses.continuousHandmade = (pdf, set) => new ContinuousDistributionHandmade(set === undefined ? [pdf] : [pdf, set]);
