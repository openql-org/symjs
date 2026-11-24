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
  /** False: the parameters are not checked (SymPy check=False). */
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

/**
 * A distribution given by a Lambda density on a set.
 *
 * @see SymPy `sympy.stats.crv_types.ContinuousDistributionHandmade`
 */
export class ContinuousDistributionHandmade extends SingleContinuousDistribution {
  /**
   * Constructs a new `ContinuousDistributionHandmade`.
   *
   * @param args - Operands in the order `pdf`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super('ContinuousDistributionHandmade', args.length === 1 ? [at(args, 0), realLine] : args);
  }
  /**
   * The lambda expression defining the density.
   *
   * @returns The lambda expression defining the density.
   * @see SymPy `sympy.stats.crv_types.ContinuousDistributionHandmade.pdf`
   */
  get pdfLambda(): Expr {
    return this.arg(0);
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.crv_types.ContinuousDistributionHandmade.set`
   */
  override get set(): SetExpr {
    return cast(this.arg(1), SetExpr);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ContinuousDistributionHandmade.pdf`
   */
  pdf(x: ExprLike): Expr {
    return cast(this.pdfLambda, LambdaNode, 'pdf').call(x);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when a parameter is known to violate the distribution constraints.
   * @see SymPy `sympy.stats.crv_types.ContinuousDistributionHandmade.check`
   */
  override check(): void {
    const x = new Dummy('x');
    const [, a, b] = limitOver(x, this.set);
    const val = integrate(this.pdf(x), x, [a, b]);
    valueCheck(Eq(val, 1) !== S.false, 'The pdf on the given set is incorrect.');
  }
}

/**
 * Defines a continuous random variable by its density on a support set. Set `check` to verify normalization.
 *
 * @param symbol - Symbol used as the variable in the density and as the name of the random variable.
 * @param densityIn - Density on the support.
 * @param set - Support of the distribution.
 * @param opts - Set `check` to true to verify normalization.
 * @returns The random symbol with the specified law.
 * @throws RangeError when checking is enabled and the density is known not to integrate to one.
 * @see SymPy `sympy.stats.crv_types.ContinuousRV`
 * @example
 * ```ts
 * import { ContinuousRV, ex, expectation, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * expectation(ContinuousRV(x, ex`sqrt(2)*exp(-x**2/2)/(2*sqrt(pi))`)); // => 0
 * ```
 */
export function ContinuousRV(symbol: Sym, densityIn: ExprLike, set: SetExpr = realLine, opts: RVOptions = {}): RandomSymbol {
  const pdf = Lambda(symbol, piecewise([densityIn, asRelational(set, symbol)], [0, true]));
  return rv(symbol.name, ContinuousDistributionHandmade, [pdf, set], { check: opts.check ?? false });
}

// ---------------------------------------------------------------------------
// The distributions (alphabetically, as in SymPy)
// ---------------------------------------------------------------------------

/**
 * The arcsine law on the interval from `a` to `b`.
 *
 * @see SymPy `sympy.stats.crv_types.ArcsinDistribution`
 */
export class ArcsinDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ArcsinDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('ArcsinDistribution', args);
  }
  /**
   * Lower endpoint.
   *
   * @returns Lower endpoint.
   * @see SymPy `sympy.stats.crv_types.ArcsinDistribution.a`
   */
  get a(): Expr {
    return this.arg(0);
  }
  /**
   * Upper endpoint.
   *
   * @returns Upper endpoint.
   * @see SymPy `sympy.stats.crv_types.ArcsinDistribution.b`
   */
  get b(): Expr {
    return this.arg(1);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[a, b]`.
   * @see SymPy `sympy.stats.crv_types.ArcsinDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.a, this.b);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ArcsinDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return pow(mul(S.Pi, sqrt(mul(sub(x, this.a), sub(this.b, x)))), -1);
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const { a, b } = this;
    return piecewise([S.Zero, Lt(x, a)], [div(mul(2, asin(sqrt(div(sub(x, a), sub(b, a))))), S.Pi), Le(x, b)], [S.One, true]);
  }
}

/**
 * Arcsin distribution on [a, b].
 *
 * @param name - Name of the symbol.
 * @param a - Lower endpoint.
 * @param b - Upper endpoint.
 * @returns The random symbol with this distribution.
 * @see SymPy `sympy.stats.crv_types.Arcsin`
 * @example
 * ```ts
 * import { Arcsin, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a, b] = symbols('a b', { real: true });
 * const X = Arcsin('x', a, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 1/(pi*sqrt((-a + z)*(b - z)))
 * ```
 */
export function Arcsin(name: string | Sym, a: ExprLike = 0, b: ExprLike = 1): RandomSymbol {
  return rv(name, ArcsinDistribution, [a, b]);
}

/**
 * The Benini law with lower bound `sigma` and shape parameters `alpha` and `beta`.
 *
 * @see SymPy `sympy.stats.crv_types.BeniniDistribution`
 */
export class BeniniDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `BeniniDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`, `sigma`.
   */
  constructor(args: readonly Expr[]) {
    super('BeniniDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`, `sigma > 0`.
   * @see SymPy `sympy.stats.crv_types.BeniniDistribution.check`
   */
  override check(): void {
    const [alpha, beta, sigma] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(Gt(alpha, 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(beta, 0), 'Shape parameter Beta must be positive.');
    valueCheck(Gt(sigma, 0), 'Scale parameter Sigma must be positive.');
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[sigma, oo)`.
   * @see SymPy `sympy.stats.crv_types.BeniniDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(2), S.Infinity);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.BeniniDistribution.pdf`
   */
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

/**
 * Benini distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive first shape parameter.
 * @param beta - Positive second shape parameter.
 * @param sigma - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`, `sigma > 0`.
 * @see SymPy `sympy.stats.crv_types.Benini`
 * @example
 * ```ts
 * import { Benini, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [alpha, beta, sigma] = symbols('alpha beta sigma', { positive: true });
 * const X = Benini('x', alpha, beta, sigma); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => (alpha/z + 2*beta*log(z/sigma)/z)*exp(-alpha*log(z/sigma) - beta*log(z/sigma)**2)
 * ```
 */
export function Benini(name: string | Sym, alpha: ExprLike, beta: ExprLike, sigma: ExprLike): RandomSymbol {
  return rv(name, BeniniDistribution, [alpha, beta, sigma]);
}

/**
 * A distribution on the unit interval with density proportional to `x**(alpha - 1)*(1 - x)**(beta - 1)`.
 *
 * @see SymPy `sympy.stats.crv_types.BetaDistribution`
 */
export class BetaDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `BetaDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('BetaDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, 1]`.
   * @see SymPy `sympy.stats.crv_types.BetaDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, 1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
   * @see SymPy `sympy.stats.crv_types.BetaDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.BetaDistribution.pdf`
   */
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

/**
 * Beta distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive first shape parameter.
 * @param beta - Positive second shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
 * @see SymPy `sympy.stats.crv_types.Beta`
 * @example
 * ```ts
 * import { Beta, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [alpha, beta] = symbols('alpha beta', { positive: true });
 * const X = Beta('x', alpha, beta); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => z**(alpha - 1)*(1 - z)**(beta - 1)/beta(alpha, beta)
 * ```
 */
export function Beta(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, BetaDistribution, [alpha, beta]);
}

/**
 * The noncentral beta law with two shape parameters and noncentrality `lamda`.
 *
 * @see SymPy `sympy.stats.crv_types.BetaNoncentralDistribution`
 */
export class BetaNoncentralDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `BetaNoncentralDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`, `lamda`.
   */
  constructor(args: readonly Expr[]) {
    super('BetaNoncentralDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, 1]`.
   * @see SymPy `sympy.stats.crv_types.BetaNoncentralDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, 1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`, `lamda >= 0`.
   * @see SymPy `sympy.stats.crv_types.BetaNoncentralDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
    valueCheck(Ge(this.arg(2), 0), 'Noncentrality parameter Lambda must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.BetaNoncentralDistribution.pdf`
   */
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

/**
 * Noncentral Beta distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive first shape parameter.
 * @param beta - Positive second shape parameter.
 * @param lamda - Noncentrality parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`, `lamda >= 0`.
 * @see SymPy `sympy.stats.crv_types.BetaNoncentral`
 * @example
 * ```ts
 * import { BetaNoncentral, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [alpha, beta] = symbols('alpha beta', { positive: true });
 * const [lamda] = symbols('lamda', { nonnegative: true });
 * const X = BetaNoncentral('x', alpha, beta, lamda); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Sum(z**(_k + alpha - 1)*(lamda/2)**_k*(1 - z)**(beta - 1)*exp(-lamda/2)/(beta(_k + alpha, beta)*factorial(_k)), (_k, 0, oo))
 * ```
 */
export function BetaNoncentral(name: string | Sym, alpha: ExprLike, beta: ExprLike, lamda: ExprLike): RandomSymbol {
  return rv(name, BetaNoncentralDistribution, [alpha, beta, lamda]);
}

/**
 * The distribution of the odds `X/(1 - X)` of a beta-distributed variable.
 *
 * @see SymPy `sympy.stats.crv_types.BetaPrimeDistribution`
 */
export class BetaPrimeDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `BetaPrimeDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('BetaPrimeDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
   * @see SymPy `sympy.stats.crv_types.BetaPrimeDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.BetaPrimeDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.BetaPrimeDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta] = [this.arg(0), this.arg(1)];
    return div(mul(pow(x, sub(alpha, 1)), pow(add(1, x), sub(neg(alpha), beta))), betaFn(alpha, beta));
  }
}

/**
 * Beta prime distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive first shape parameter.
 * @param beta - Positive second shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
 * @see SymPy `sympy.stats.crv_types.BetaPrime`
 * @example
 * ```ts
 * import { BetaPrime, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [alpha, beta] = symbols('alpha beta', { positive: true });
 * const X = BetaPrime('x', alpha, beta); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => z**(alpha - 1)*(z + 1)**(-alpha - beta)/beta(alpha, beta)
 * ```
 */
export function BetaPrime(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, BetaPrimeDistribution, [alpha, beta]);
}

/**
 * A Pareto law restricted to the interval between its lower and upper bounds.
 *
 * @see SymPy `sympy.stats.crv_types.BoundedParetoDistribution`
 */
export class BoundedParetoDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `BoundedParetoDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `left`, `right`.
   */
  constructor(args: readonly Expr[]) {
    super('BoundedParetoDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[left, right]`.
   * @see SymPy `sympy.stats.crv_types.BoundedParetoDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(1), this.arg(2));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `0 < left < right`.
   * @see SymPy `sympy.stats.crv_types.BoundedParetoDistribution.check`
   */
  override check(): void {
    const [alpha, left, right] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(isPositive(alpha), 'Shape must be positive.');
    valueCheck(isPositive(left), 'Left value should be positive.');
    valueCheck(Gt(right, left), 'Right should be greater than left.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.BoundedParetoDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, left, right] = [this.arg(0), this.arg(1), this.arg(2)];
    const num = mul(alpha, pow(left, alpha), pow(x, sub(neg(alpha), 1)));
    const den = sub(1, pow(div(left, right), alpha));
    return div(num, den);
  }
}

/**
 * Bounded Pareto distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive shape parameter.
 * @param left - Positive lower bound.
 * @param right - Upper bound greater than the lower bound.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `0 < left < right`.
 * @see SymPy `sympy.stats.crv_types.BoundedPareto`
 * @example
 * ```ts
 * import { BoundedPareto, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [L, H] = symbols('L H', { positive: true });
 * const X = BoundedPareto('X', 2, L, H); // => X
 * (density(X) as Distribution).pdf(ex`x`); // => 2*L**2/(x**3*(1 - L**2/H**2))
 * ```
 */
export function BoundedPareto(name: string | Sym, alpha: ExprLike, left: ExprLike, right: ExprLike): RandomSymbol {
  return rv(name, BoundedParetoDistribution, [alpha, left, right]);
}

/**
 * The Cauchy law centered at `x0`, with half-width `gamma` at half the peak density.
 *
 * @see SymPy `sympy.stats.crv_types.CauchyDistribution`
 */
export class CauchyDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `CauchyDistribution`.
   *
   * @param args - Distribution parameters in the order `x0`, `gamma`.
   */
  constructor(args: readonly Expr[]) {
    super('CauchyDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location and positive scale.
   * @see SymPy `sympy.stats.crv_types.CauchyDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter Gamma must be positive.');
    valueCheck(isReal(this.arg(0)), 'Location parameter must be real.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.CauchyDistribution.pdf`
   */
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

/**
 * Cauchy distribution.
 *
 * @param name - Name of the symbol.
 * @param x0 - Real location parameter.
 * @param gamma - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location and positive scale.
 * @see SymPy `sympy.stats.crv_types.Cauchy`
 * @example
 * ```ts
 * import { Cauchy, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [gamma] = symbols('gamma', { positive: true });
 * const X = Cauchy('x', ex`x0`, gamma); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 1/(pi*gamma*(1 + (-x0 + z)**2/gamma**2))
 * ```
 */
export function Cauchy(name: string | Sym, x0: ExprLike, gamma: ExprLike): RandomSymbol {
  return rv(name, CauchyDistribution, [x0, gamma]);
}

/** Positive and integer degrees of freedom (the checks of Chi and ChiSquared). */
function checkDegrees(k: Expr): void {
  valueCheck(Gt(k, 0), 'Number of degrees of freedom (k) must be positive.');
  valueCheck(isIntegerValued(k), 'Number of degrees of freedom (k) must be an integer.');
}

/**
 * The law of the Euclidean norm of `k` independent standard normal variables.
 *
 * @see SymPy `sympy.stats.crv_types.ChiDistribution`
 */
export class ChiDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ChiDistribution`.
   *
   * @param args - Distribution parameters in the order `k`.
   */
  constructor(args: readonly Expr[]) {
    super('ChiDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom.
   * @see SymPy `sympy.stats.crv_types.ChiDistribution.check`
   */
  override check(): void {
    checkDegrees(this.arg(0));
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.ChiDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ChiDistribution.pdf`
   */
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

/**
 * Chi distribution (SymPy Chi(name, k)); exported as `ChiRV` (`Chi` is the hyperbolic cosine integral).
 *
 * @param name - Name of the symbol.
 * @param k - Degrees of freedom.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom.
 * @see SymPy `sympy.stats.crv_types.Chi`
 * @example
 * ```ts
 * import { ChiRV, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [k] = symbols('k', { integer: true });
 * const X = ChiRV('x', k); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 2**(1 - k/2)*z**(k - 1)*exp(-z**2/2)/gamma(k/2)
 * ```
 */
export function ChiRV(name: string | Sym, k: ExprLike): RandomSymbol {
  return rv(name, ChiDistribution, [k]);
}

/**
 * The law of the norm of a shifted standard normal vector with `k` components.
 *
 * @see SymPy `sympy.stats.crv_types.ChiNoncentralDistribution`
 */
export class ChiNoncentralDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ChiNoncentralDistribution`.
   *
   * @param args - Distribution parameters in the order `k`, `l`.
   */
  constructor(args: readonly Expr[]) {
    super('ChiNoncentralDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom and positive noncentrality.
   * @see SymPy `sympy.stats.crv_types.ChiNoncentralDistribution.check`
   */
  override check(): void {
    checkDegrees(this.arg(0));
    valueCheck(Gt(this.arg(1), 0), 'Shift parameter Lambda must be positive.');
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.ChiNoncentralDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ChiNoncentralDistribution.pdf`
   */
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

/**
 * Noncentral Chi distribution.
 *
 * @param name - Name of the symbol.
 * @param k - Degrees of freedom.
 * @param l - Noncentrality parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom and positive noncentrality.
 * @see SymPy `sympy.stats.crv_types.ChiNoncentral`
 * @example
 * ```ts
 * import { ChiNoncentral, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [k] = symbols('k', { integer: true });
 * const X = ChiNoncentral('x', k, ex`l`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => l*z**k*exp(-l**2/2 - z**2/2)*besseli(k/2 - 1, l*z)/(l*z)**(k/2)
 * ```
 */
export function ChiNoncentral(name: string | Sym, k: ExprLike, l: ExprLike): RandomSymbol {
  return rv(name, ChiNoncentralDistribution, [k, l]);
}

/**
 * The distribution of the sum of squares of `k` independent standard normal variables.
 *
 * @see SymPy `sympy.stats.crv_types.ChiSquaredDistribution`
 */
export class ChiSquaredDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ChiSquaredDistribution`.
   *
   * @param args - Distribution parameters in the order `k`.
   */
  constructor(args: readonly Expr[]) {
    super('ChiSquaredDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom.
   * @see SymPy `sympy.stats.crv_types.ChiSquaredDistribution.check`
   */
  override check(): void {
    checkDegrees(this.arg(0));
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.ChiSquaredDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ChiSquaredDistribution.pdf`
   */
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

/**
 * Chi-squared distribution.
 *
 * @param name - Name of the symbol.
 * @param k - Degrees of freedom.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom.
 * @see SymPy `sympy.stats.crv_types.ChiSquared`
 * @example
 * ```ts
 * import { ChiSquared, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [k] = symbols('k', { integer: true, positive: true });
 * const X = ChiSquared('x', k); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => z**(k/2 - 1)*exp(-z/2)/(2**(k/2)*gamma(k/2))
 * ```
 */
export function ChiSquared(name: string | Sym, k: ExprLike): RandomSymbol {
  return rv(name, ChiSquaredDistribution, [k]);
}

/**
 * A positive-valued Dagum law with shapes `p` and `a` and scale `b`.
 *
 * @see SymPy `sympy.stats.crv_types.DagumDistribution`
 */
export class DagumDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `DagumDistribution`.
   *
   * @param args - Distribution parameters in the order `p`, `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('DagumDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.DagumDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `p > 0`, `a > 0`, `b > 0`.
   * @see SymPy `sympy.stats.crv_types.DagumDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter p must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter a must be positive.');
    valueCheck(Gt(this.arg(2), 0), 'Scale parameter b must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.DagumDistribution.pdf`
   */
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

/**
 * Dagum distribution.
 *
 * @param name - Name of the symbol.
 * @param p - Positive first shape parameter.
 * @param a - Positive second shape parameter.
 * @param b - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `p > 0`, `a > 0`, `b > 0`.
 * @see SymPy `sympy.stats.crv_types.Dagum`
 * @example
 * ```ts
 * import { Dagum, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [p, a, b] = symbols('p a b', { positive: true });
 * const X = Dagum('x', p, a, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => a*p*(z/b)**(a*p)*((z/b)**a + 1)**(-p - 1)/z
 * ```
 */
export function Dagum(name: string | Sym, p: ExprLike, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, DagumDistribution, [p, a, b]);
}

/**
 * The Davis law with scale `b`, shape `n`, and location `mu`.
 *
 * @see SymPy `sympy.stats.crv_types.DavisDistribution`
 */
export class DavisDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `DavisDistribution`.
   *
   * @param args - Distribution parameters in the order `b`, `n`, `mu`.
   */
  constructor(args: readonly Expr[]) {
    super('DavisDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.DavisDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `b > 0`, `n > 1`, `mu > 0`.
   * @see SymPy `sympy.stats.crv_types.DavisDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter b must be positive.');
    valueCheck(Gt(this.arg(1), 1), 'Shape parameter n must be above 1.');
    valueCheck(Gt(this.arg(2), 0), 'Location parameter mu must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.DavisDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [b, n, mu] = [this.arg(0), this.arg(1), this.arg(2)];
    const dividend = mul(pow(b, n), pow(sub(x, mu), sub(-1, n)));
    const divisor = mul(sub(exp(div(b, sub(x, mu))), 1), mul(gamma(n), zeta(n)));
    return div(dividend, divisor);
  }
}

/**
 * Davis distribution.
 *
 * @param name - Name of the symbol.
 * @param b - Positive scale parameter.
 * @param n - Shape parameter greater than one.
 * @param mu - Location parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `b > 0`, `n > 1`, `mu > 0`.
 * @see SymPy `sympy.stats.crv_types.Davis`
 * @example
 * ```ts
 * import { Davis, Distribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [b, n, mu] = symbols('b n mu', { positive: true });
 * const X = Davis('x', b, n, mu); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => b**n*(-mu + z)**(-n - 1)/((exp(b/(-mu + z)) - 1)*gamma(n)*zeta(n))
 * ```
 */
export function Davis(name: string | Sym, b: ExprLike, n: ExprLike, mu: ExprLike): RandomSymbol {
  return rv(name, DavisDistribution, [b, n, mu]);
}

/**
 * Erlang distribution: a Gamma distribution with shape k and scale 1/l.
 *
 * @param name - Name of the symbol.
 * @param k - Positive integer shape.
 * @param l - Positive rate.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive shape and rate.
 * @see SymPy `sympy.stats.crv_types.Erlang`
 * @example
 * ```ts
 * import { Distribution, Erlang, density, ex, symbols } from '@symjs/symjs';
 *
 * const [k] = symbols('k', { integer: true, positive: true });
 * const [l] = symbols('l', { positive: true });
 * const X = Erlang('x', k, l); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => l**k*z**(k - 1)*exp(-l*z)/gamma(k)
 * ```
 */
export function Erlang(name: string | Sym, k: ExprLike, l: ExprLike): RandomSymbol {
  return rv(name, GammaDistribution, [k, pow(l, -1)]);
}

/**
 * The distribution of the sum of independent normal and exponential variables.
 *
 * @see SymPy `sympy.stats.crv_types.ExGaussianDistribution`
 */
export class ExGaussianDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ExGaussianDistribution`.
   *
   * @param args - Distribution parameters in the order `mean`, `std`, `rate`.
   */
  constructor(args: readonly Expr[]) {
    super('ExGaussianDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `std > 0`, `rate > 0`.
   * @see SymPy `sympy.stats.crv_types.ExGaussianDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Standard deviation of ExGaussian must be positive.');
    valueCheck(Gt(this.arg(2), 0), 'Rate of ExGaussian must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ExGaussianDistribution.pdf`
   */
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

/**
 * Exponentially modified Gaussian distribution.
 *
 * @param name - Name of the symbol.
 * @param mean - Mean of the normal component.
 * @param std - Positive standard deviation of the normal component.
 * @param rate - Positive rate of the exponential component.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `std > 0`, `rate > 0`.
 * @see SymPy `sympy.stats.crv_types.ExGaussian`
 * @example
 * ```ts
 * import { Distribution, ExGaussian, density, ex, symbols } from '@symjs/symjs';
 *
 * const [std, rate] = symbols('sigma lamda', { positive: true });
 * const X = ExGaussian('x', ex`mu`, std, rate); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => lamda*exp(lamda*(lamda*sigma**2 + 2*mu - 2*z)/2)*erfc(sqrt(2)*(lamda*sigma**2 + mu - z)/(2*sigma))/2
 * ```
 */
export function ExGaussian(name: string | Sym, mean: ExprLike, std: ExprLike, rate: ExprLike): RandomSymbol {
  return rv(name, ExGaussianDistribution, [mean, std, rate]);
}

/**
 * The waiting-time law with constant event rate `rate`.
 *
 * @see SymPy `sympy.stats.crv_types.ExponentialDistribution`
 */
export class ExponentialDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ExponentialDistribution`.
   *
   * @param args - Distribution parameters in the order `rate`.
   */
  constructor(args: readonly Expr[]) {
    super('ExponentialDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.ExponentialDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `rate > 0`.
   * @see SymPy `sympy.stats.crv_types.ExponentialDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Rate must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ExponentialDistribution.pdf`
   */
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

/**
 * Exponential distribution.
 *
 * @param name - Name of the symbol.
 * @param rate - Positive rate.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `rate > 0`.
 * @see SymPy `sympy.stats.crv_types.Exponential`
 * @example
 * ```ts
 * import { Distribution, Exponential, density, ex, expectation, symbols } from '@symjs/symjs';
 *
 * const [l] = symbols('lambda', { positive: true });
 * const X = Exponential('x', l); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => lambda*exp(-lambda*z)
 * expectation(X); // => 1/lambda
 * ```
 */
export function Exponential(name: string | Sym, rate: ExprLike): RandomSymbol {
  return rv(name, ExponentialDistribution, [rate]);
}

/**
 * The symmetric exponential power law centered at `mu`, with scale `alpha` and shape `beta`.
 *
 * @see SymPy `sympy.stats.crv_types.ExponentialPowerDistribution`
 */
export class ExponentialPowerDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ExponentialPowerDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('ExponentialPowerDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
   * @see SymPy `sympy.stats.crv_types.ExponentialPowerDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter alpha must be positive.');
    valueCheck(Gt(this.arg(2), 0), 'Shape parameter beta must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ExponentialPowerDistribution.pdf`
   */
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

/**
 * Exponential power distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Location parameter.
 * @param alpha - Positive scale parameter.
 * @param beta - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
 * @see SymPy `sympy.stats.crv_types.ExponentialPower`
 * @example
 * ```ts
 * import { Distribution, ExponentialPower, density, ex, symbols } from '@symjs/symjs';
 *
 * const [alpha, beta] = symbols('alpha beta', { positive: true });
 * const X = ExponentialPower('x', ex`mu`, alpha, beta); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => beta*exp(-(Abs(mu - z)/alpha)**beta)/(2*alpha*gamma(1/beta))
 * ```
 */
export function ExponentialPower(name: string | Sym, mu: ExprLike, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, ExponentialPowerDistribution, [mu, alpha, beta]);
}

/**
 * The ratio of independent chi-squared variables, each divided by its degrees of freedom.
 *
 * @see SymPy `sympy.stats.crv_types.FDistributionDistribution`
 */
export class FDistributionDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `FDistributionDistribution`.
   *
   * @param args - Distribution parameters in the order `d1`, `d2`.
   */
  constructor(args: readonly Expr[]) {
    super('FDistributionDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.FDistributionDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom.
   * @see SymPy `sympy.stats.crv_types.FDistributionDistribution.check`
   */
  override check(): void {
    const [d1, d2] = [this.arg(0), this.arg(1)];
    valueCheck([Gt(d1, 0), isIntegerValued(d1)], 'Degrees of freedom d1 must be positive integer.');
    valueCheck([Gt(d2, 0), isIntegerValued(d2)], 'Degrees of freedom d2 must be positive integer.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.FDistributionDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [d1, d2] = [this.arg(0), this.arg(1)];
    return div(sqrt(div(mul(pow(mul(d1, x), d1), pow(d2, d2)), pow(add(mul(d1, x), d2), add(d1, d2)))), mul(x, betaFn(div(d1, 2), div(d2, 2))));
  }
  protected override momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    throw new NotImplementedError('The moment generating function for the F-distribution does not exist.');
  }
}

/**
 * Creates an F-distributed variable from the numerator and denominator degrees of freedom.
 *
 * @param name - Name of the symbol.
 * @param d1 - Degrees of freedom of the numerator.
 * @param d2 - Degrees of freedom of the denominator.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive integer degrees of freedom.
 * @see SymPy `sympy.stats.crv_types.FDistribution`
 * @example
 * ```ts
 * import { Distribution, FDistribution, density, ex, symbols } from '@symjs/symjs';
 *
 * const [d1, d2] = symbols('d1 d2', { positive: true });
 * const X = FDistribution('x', d1, d2); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => d2**(d2/2)*sqrt((d1*z)**d1*(d1*z + d2)**(-d1 - d2))/(z*beta(d1/2, d2/2))
 * ```
 */
export function FDistribution(name: string | Sym, d1: ExprLike, d2: ExprLike): RandomSymbol {
  return rv(name, FDistributionDistribution, [d1, d2]);
}

/**
 * The distribution of half the logarithm of an F-distributed variable.
 *
 * @see SymPy `sympy.stats.crv_types.FisherZDistribution`
 */
export class FisherZDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `FisherZDistribution`.
   *
   * @param args - Distribution parameters in the order `d1`, `d2`.
   */
  constructor(args: readonly Expr[]) {
    super('FisherZDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `d1 > 0`, `d2 > 0`.
   * @see SymPy `sympy.stats.crv_types.FisherZDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Degree of freedom d1 must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Degree of freedom d2 must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.FisherZDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [d1, d2] = [this.arg(0), this.arg(1)];
    return mul(
      div(mul(2, pow(d1, div(d1, 2)), pow(d2, div(d2, 2))), betaFn(div(d1, 2), div(d2, 2))),
      div(exp(mul(d1, x)), pow(add(mul(d1, exp(mul(2, x))), d2), div(add(d1, d2), 2))),
    );
  }
}

/**
 * Fisher's z distribution.
 *
 * @param name - Name of the symbol.
 * @param d1 - Degrees of freedom of the numerator.
 * @param d2 - Degrees of freedom of the denominator.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `d1 > 0`, `d2 > 0`.
 * @see SymPy `sympy.stats.crv_types.FisherZ`
 * @example
 * ```ts
 * import { Distribution, FisherZ, density, ex, symbols } from '@symjs/symjs';
 *
 * const [d1, d2] = symbols('d1 d2', { positive: true });
 * const X = FisherZ('x', d1, d2); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 2*d1**(d1/2)*d2**(d2/2)*(d1*exp(2*z) + d2)**(-d1/2 - d2/2)*exp(d1*z)/beta(d1/2, d2/2)
 * ```
 */
export function FisherZ(name: string | Sym, d1: ExprLike, d2: ExprLike): RandomSymbol {
  return rv(name, FisherZDistribution, [d1, d2]);
}

/**
 * A Fréchet extreme-value law with shape `a`, scale `s`, and location `m`.
 *
 * @see SymPy `sympy.stats.crv_types.FrechetDistribution`
 */
export class FrechetDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `FrechetDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `s`, `m`.
   */
  constructor(args: readonly Expr[]) {
    super('FrechetDistribution', [at(args, 0), args[1] ?? S.One, args[2] ?? S.Zero]);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.FrechetDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a > 0`, `s > 0`.
   * @see SymPy `sympy.stats.crv_types.FrechetDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Shape parameter alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter s must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.FrechetDistribution.pdf`
   */
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

/**
 * Frechet distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Positive shape parameter.
 * @param s - Positive scale parameter.
 * @param m - Location parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a > 0`, `s > 0`.
 * @see SymPy `sympy.stats.crv_types.Frechet`
 * @example
 * ```ts
 * import { Distribution, Frechet, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a, s] = symbols('a s', { positive: true });
 * const [m] = symbols('m', { real: true });
 * const X = Frechet('x', a, s, m); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => a*((-m + z)/s)**(-a - 1)*exp(-1/((-m + z)/s)**a)/s
 * ```
 */
export function Frechet(name: string | Sym, a: ExprLike, s: ExprLike = 1, m: ExprLike = 0): RandomSymbol {
  return rv(name, FrechetDistribution, [a, s, m]);
}

/**
 * The gamma law parameterized by shape `k` and scale `theta`.
 *
 * @see SymPy `sympy.stats.crv_types.GammaDistribution`
 */
export class GammaDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `GammaDistribution`.
   *
   * @param args - Distribution parameters in the order `k`, `theta`.
   */
  constructor(args: readonly Expr[]) {
    super('GammaDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.GammaDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `k > 0`, `theta > 0`.
   * @see SymPy `sympy.stats.crv_types.GammaDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'k must be positive');
    valueCheck(Gt(this.arg(1), 0), 'Theta must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.GammaDistribution.pdf`
   */
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

/**
 * Gamma distribution with shape k and scale theta.
 *
 * @param name - Name of the symbol.
 * @param k - Positive shape parameter.
 * @param theta - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `k > 0`, `theta > 0`.
 * @see SymPy `sympy.stats.crv_types.Gamma`
 * @example
 * ```ts
 * import { Distribution, Gamma, density, ex, expectation, symbols } from '@symjs/symjs';
 *
 * const [k, theta] = symbols('k theta', { positive: true });
 * const X = Gamma('x', k, theta); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => z**(k - 1)*exp(-z/theta)/(theta**k*gamma(k))
 * expectation(X); // => k*theta
 * ```
 */
export function Gamma(name: string | Sym, k: ExprLike, theta: ExprLike): RandomSymbol {
  return rv(name, GammaDistribution, [k, theta]);
}

/**
 * The inverse gamma law with shape `a` and scale `b`.
 *
 * @see SymPy `sympy.stats.crv_types.GammaInverseDistribution`
 */
export class GammaInverseDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `GammaInverseDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('GammaInverseDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.GammaInverseDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a > 0`, `b > 0`.
   * @see SymPy `sympy.stats.crv_types.GammaInverseDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'alpha must be positive');
    valueCheck(Gt(this.arg(1), 0), 'beta must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.GammaInverseDistribution.pdf`
   */
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

/**
 * Inverse gamma distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Positive shape parameter.
 * @param b - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a > 0`, `b > 0`.
 * @see SymPy `sympy.stats.crv_types.GammaInverse`
 * @example
 * ```ts
 * import { Distribution, GammaInverse, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a, b] = symbols('a b', { positive: true });
 * const X = GammaInverse('x', a, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => b**a*z**(-a - 1)*exp(-b/z)/gamma(a)
 * ```
 */
export function GammaInverse(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, GammaInverseDistribution, [a, b]);
}

/**
 * A Gumbel extreme-value law for maxima or, with `minimum`, minima.
 *
 * @see SymPy `sympy.stats.crv_types.GumbelDistribution`
 */
export class GumbelDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `GumbelDistribution`.
   *
   * @param args - Distribution parameters in the order `beta`, `mu`, `minimum`.
   */
  constructor(args: readonly Expr[]) {
    super('GumbelDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `beta > 0`.
   * @see SymPy `sympy.stats.crv_types.GumbelDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter beta must be positive.');
  }
  /** SymPy Piecewise((min_form, minimum), (max_form, not minimum)). */
  #select(minForm: Expr, maxForm: Expr): Expr {
    const minimum = this.arg(2);
    return piecewise([minForm, minimum], [maxForm, !(minimum instanceof BoolAtom && minimum.value)]);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.GumbelDistribution.pdf`
   */
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

/**
 * Gumbel distribution of the maximum, or of the minimum when `minimum` is true.
 *
 * @param name - Name of the symbol.
 * @param beta - Positive scale parameter.
 * @param mu - Location parameter.
 * @param minimum - Use the distribution of a minimum when true.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `beta > 0`.
 * @see SymPy `sympy.stats.crv_types.Gumbel`
 * @example
 * ```ts
 * import { Distribution, Gumbel, density, ex, symbols } from '@symjs/symjs';
 *
 * const [beta] = symbols('beta', { positive: true });
 * const X = Gumbel('x', beta, ex`mu`); // => x
 * (density(X) as Distribution).pdf(ex`x`); // => exp(-exp(-(-mu + x)/beta) - (-mu + x)/beta)/beta
 * ```
 */
export function Gumbel(name: string | Sym, beta: ExprLike, mu: ExprLike, minimum: boolean = false): RandomSymbol {
  return rv(name, GumbelDistribution, [beta, mu, minimum ? S.true : S.false]);
}

/**
 * A positive waiting-time law whose hazard grows exponentially with time.
 *
 * @see SymPy `sympy.stats.crv_types.GompertzDistribution`
 */
export class GompertzDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `GompertzDistribution`.
   *
   * @param args - Distribution parameters in the order `b`, `eta`.
   */
  constructor(args: readonly Expr[]) {
    super('GompertzDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.GompertzDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `b > 0`, `eta > 0`.
   * @see SymPy `sympy.stats.crv_types.GompertzDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'b must be positive');
    valueCheck(Gt(this.arg(1), 0), 'eta must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.GompertzDistribution.pdf`
   */
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

/**
 * Gompertz distribution.
 *
 * @param name - Name of the symbol.
 * @param b - Positive scale parameter.
 * @param eta - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `b > 0`, `eta > 0`.
 * @see SymPy `sympy.stats.crv_types.Gompertz`
 * @example
 * ```ts
 * import { Distribution, Gompertz, density, ex, symbols } from '@symjs/symjs';
 *
 * const [b, eta] = symbols('b eta', { positive: true });
 * const X = Gompertz('x', b, eta); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => b*eta*exp(eta)*exp(b*z)*exp(-eta*exp(b*z))
 * ```
 */
export function Gompertz(name: string | Sym, b: ExprLike, eta: ExprLike): RandomSymbol {
  return rv(name, GompertzDistribution, [b, eta]);
}

/**
 * The Kumaraswamy law for proportions, with two shape parameters.
 *
 * @see SymPy `sympy.stats.crv_types.KumaraswamyDistribution`
 */
export class KumaraswamyDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `KumaraswamyDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('KumaraswamyDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.KumaraswamyDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a > 0`, `b > 0`.
   * @see SymPy `sympy.stats.crv_types.KumaraswamyDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'a must be positive');
    valueCheck(Gt(this.arg(1), 0), 'b must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.KumaraswamyDistribution.pdf`
   */
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

/**
 * Kumaraswamy distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Positive first shape parameter.
 * @param b - Positive second shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a > 0`, `b > 0`.
 * @see SymPy `sympy.stats.crv_types.Kumaraswamy`
 * @example
 * ```ts
 * import { Distribution, Kumaraswamy, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a, b] = symbols('a b', { positive: true });
 * const X = Kumaraswamy('x', a, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => a*b*z**(a - 1)*(1 - z**a)**(b - 1)
 * ```
 */
export function Kumaraswamy(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, KumaraswamyDistribution, [a, b]);
}

/**
 * The symmetric double-exponential law centered at `mu` with scale `b`.
 *
 * @see SymPy `sympy.stats.crv_types.LaplaceDistribution`
 */
export class LaplaceDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LaplaceDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('LaplaceDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location and positive scale (for a vector, compatible dimensions and a positive definite scale matrix).
   * @see SymPy `sympy.stats.crv_types.LaplaceDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter b must be positive.');
    valueCheck(isReal(this.arg(0)), 'Location parameter mu should be real');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LaplaceDistribution.pdf`
   */
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

/**
 * Laplace distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Location or location vector.
 * @param b - Positive scale or multivariate scale matrix.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location and positive scale (for a vector, compatible dimensions and a positive definite scale matrix).
 * @throws TypeError when scalar and matrix parameters are mixed.
 * @see SymPy `sympy.stats.crv_types.Laplace`
 * @example
 * ```ts
 * import { Distribution, Laplace, density, ex, symbols } from '@symjs/symjs';
 *
 * const [b] = symbols('b', { positive: true });
 * const X = Laplace('x', ex`mu`, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => exp(-Abs(mu - z)/b)/(2*b)
 * ```
 */
export function Laplace(name: string | Sym, mu: ExprLike | MatrixParam, b: ExprLike | MatrixParam): RandomSymbol {
  // vector and matrix parameters give the multivariate distribution
  if (isMatrixParam(mu) && isMatrixParam(b)) return defined(statsClasses.multivariateLaplace, 'joint_rv_types')(name, mu, b);
  return rv(name, LaplaceDistribution, [scalarParam(mu), scalarParam(b)]);
}

/**
 * The one-sided Lévy stable law with location `mu` and scale `c`.
 *
 * @see SymPy `sympy.stats.crv_types.LevyDistribution`
 */
export class LevyDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LevyDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `c`.
   */
  constructor(args: readonly Expr[]) {
    super('LevyDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[mu, oo)`.
   * @see SymPy `sympy.stats.crv_types.LevyDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(0), S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location and positive scale.
   * @see SymPy `sympy.stats.crv_types.LevyDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'c (scale parameter) must be positive');
    valueCheck(isReal(this.arg(0)), 'mu (location parameter) must be real');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LevyDistribution.pdf`
   */
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

/**
 * Levy distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Real location parameter.
 * @param c - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location and positive scale.
 * @see SymPy `sympy.stats.crv_types.Levy`
 * @example
 * ```ts
 * import { Distribution, Levy, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu] = symbols('mu', { real: true });
 * const [c] = symbols('c', { positive: true });
 * const X = Levy('x', mu, c); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => sqrt(2)*sqrt(c)*exp(-c/(-2*mu + 2*z))/(2*sqrt(pi)*(-mu + z)**(3/2))
 * ```
 */
export function Levy(name: string | Sym, mu: ExprLike, c: ExprLike): RandomSymbol {
  return rv(name, LevyDistribution, [mu, c]);
}

/**
 * The distribution of the exponential of a Cauchy random variable.
 *
 * @see SymPy `sympy.stats.crv_types.LogCauchyDistribution`
 */
export class LogCauchyDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LogCauchyDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `sigma`.
   */
  constructor(args: readonly Expr[]) {
    super('LogCauchyDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.crv_types.LogCauchyDistribution.set`
   */
  override get set(): SetExpr {
    return Interval.open(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location and positive scale.
   * @see SymPy `sympy.stats.crv_types.LogCauchyDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0) !== S.false, 'Scale parameter Gamma must be positive.');
    valueCheck(isReal(this.arg(0)) !== false, 'Location parameter must be real.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LogCauchyDistribution.pdf`
   */
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

/**
 * Log-Cauchy distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Location of the underlying Cauchy variable.
 * @param sigma - Positive scale of the underlying Cauchy variable.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location and positive scale.
 * @see SymPy `sympy.stats.crv_types.LogCauchy`
 * @example
 * ```ts
 * import { Distribution, LogCauchy, density, ex } from '@symjs/symjs';
 *
 * const X = LogCauchy('x', 2, ex`1/5`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 1/(5*pi*z*((log(z) - 2)**2 + 1/25))
 * ```
 */
export function LogCauchy(name: string | Sym, mu: ExprLike, sigma: ExprLike): RandomSymbol {
  return rv(name, LogCauchyDistribution, [mu, sigma]);
}

/**
 * A logistic law with location `mu` and scale `s`.
 *
 * @see SymPy `sympy.stats.crv_types.LogisticDistribution`
 */
export class LogisticDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LogisticDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `s`.
   */
  constructor(args: readonly Expr[]) {
    super('LogisticDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `s > 0`.
   * @see SymPy `sympy.stats.crv_types.LogisticDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Scale parameter s must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LogisticDistribution.pdf`
   */
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

/**
 * Logistic distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Location parameter.
 * @param s - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `s > 0`.
 * @see SymPy `sympy.stats.crv_types.Logistic`
 * @example
 * ```ts
 * import { Distribution, Logistic, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu] = symbols('mu', { real: true });
 * const [s] = symbols('s', { positive: true });
 * const X = Logistic('x', mu, s); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => exp((mu - z)/s)/(s*(exp((mu - z)/s) + 1)**2)
 * ```
 */
export function Logistic(name: string | Sym, mu: ExprLike, s: ExprLike): RandomSymbol {
  return rv(name, LogisticDistribution, [mu, s]);
}

/**
 * The distribution of a positive variable whose logarithm is logistic.
 *
 * @see SymPy `sympy.stats.crv_types.LogLogisticDistribution`
 */
export class LogLogisticDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LogLogisticDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('LogLogisticDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.LogLogisticDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
   * @see SymPy `sympy.stats.crv_types.LogLogisticDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter Alpha must be positive.');
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter Beta must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LogLogisticDistribution.pdf`
   */
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
   * Computes the expectation of a function of a log-logistic variable, using the closed-form mean for the variable itself.
   *
   * @param expr - Expression to evaluate.
   * @param v - Symbol distributed according to this law.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value of the supplied expression.
   * @see SymPy `sympy.stats.crv_types.LogLogisticDistribution.expectation`
   * @remarks For scale 1 and shape 4, SymPy gives the first moment, `sqrt(2)*pi/4`, when asked for the second. The integral of the squared variable gives `pi/2`.
   * @example
   * ```ts
   * import { LogLogisticDistribution, ex, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x', { real: true });
   * const law = new LogLogisticDistribution([ex`1`, ex`4`]);
   * law.expectation(x.pow(2), x); // => pi/2
   * ```
   */
  override expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    if (expr.key !== v.key || opts.evaluate === false) return super.expectation(expr, v, opts);
    const [a, b] = [this.arg(0), this.arg(1)];
    return piecewise([S.NaN, Le(b, 1)], [div(mul(S.Pi, a), mul(b, sin(div(S.Pi, b)))), true]);
  }
}

/**
 * Log-logistic distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive scale parameter.
 * @param beta - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
 * @see SymPy `sympy.stats.crv_types.LogLogistic`
 * @example
 * ```ts
 * import { Distribution, LogLogistic, density, symbols } from '@symjs/symjs';
 *
 * const [alpha, beta, z] = symbols('alpha beta z', { positive: true });
 * const X = LogLogistic('x', alpha, beta); // => x
 * (density(X) as Distribution).pdf(z); // => beta*(z/alpha)**(beta - 1)/(alpha*((z/alpha)**beta + 1)**2)
 * ```
 */
export function LogLogistic(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, LogLogisticDistribution, [alpha, beta]);
}

/**
 * The distribution of a proportion whose log odds are normal.
 *
 * @see SymPy `sympy.stats.crv_types.LogitNormalDistribution`
 */
export class LogitNormalDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LogitNormalDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `s`.
   */
  constructor(args: readonly Expr[]) {
    super('LogitNormalDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.crv_types.LogitNormalDistribution.set`
   */
  override get set(): SetExpr {
    return Interval.open(0, 1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location and positive squared scale.
   * @see SymPy `sympy.stats.crv_types.LogitNormalDistribution.check`
   */
  override check(): void {
    const [mu, s] = [this.arg(0), this.arg(1)];
    // SymPy: (s**2).is_real is not False and s**2 > 0
    const s2 = pow(s, 2);
    valueCheck(isReal(s2) === false ? false : Gt(s2, 0), 'Squared scale parameter s must be positive.');
    valueCheck(isReal(mu) !== false, 'Location parameter must be real');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LogitNormalDistribution.pdf`
   */
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

/**
 * Logit-normal distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Mean on the logit scale.
 * @param s - Standard deviation on the logit scale.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location and positive squared scale.
 * @see SymPy `sympy.stats.crv_types.LogitNormal`
 * @example
 * ```ts
 * import { Distribution, LogitNormal, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu] = symbols('mu', { real: true });
 * const [s] = symbols('s', { positive: true });
 * const X = LogitNormal('x', mu, s); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => sqrt(2)*exp(-(-mu + log(z/(1 - z)))**2/(2*s**2))/(2*sqrt(pi)*s*z*(1 - z))
 * ```
 */
export function LogitNormal(name: string | Sym, mu: ExprLike, s: ExprLike): RandomSymbol {
  return rv(name, LogitNormalDistribution, [mu, s]);
}

/**
 * The distribution of a positive variable whose logarithm is normal.
 *
 * @see SymPy `sympy.stats.crv_types.LogNormalDistribution`
 */
export class LogNormalDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LogNormalDistribution`.
   *
   * @param args - Distribution parameters in the order `mean`, `std`.
   */
  constructor(args: readonly Expr[]) {
    super('LogNormalDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.LogNormalDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `std > 0`.
   * @see SymPy `sympy.stats.crv_types.LogNormalDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Parameter std must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LogNormalDistribution.pdf`
   */
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

/**
 * Log-normal distribution.
 *
 * @param name - Name of the symbol.
 * @param mean - Mean of the logarithm.
 * @param std - Positive standard deviation of the logarithm.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `std > 0`.
 * @see SymPy `sympy.stats.crv_types.LogNormal`
 * @example
 * ```ts
 * import { Distribution, LogNormal, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu] = symbols('mu', { real: true });
 * const [sigma] = symbols('sigma', { positive: true });
 * const X = LogNormal('x', mu, sigma); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => sqrt(2)*exp(-(-mu + log(z))**2/(2*sigma**2))/(2*sqrt(pi)*sigma*z)
 * ```
 */
export function LogNormal(name: string | Sym, mean: ExprLike, std: ExprLike): RandomSymbol {
  return rv(name, LogNormalDistribution, [mean, std]);
}

/**
 * The Pareto type II law with lower endpoint zero, shape `alpha`, and scale `lamda`.
 *
 * @see SymPy `sympy.stats.crv_types.LomaxDistribution`
 */
export class LomaxDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `LomaxDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `lamda`.
   */
  constructor(args: readonly Expr[]) {
    super('LomaxDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.LomaxDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real, positive shape and scale.
   * @see SymPy `sympy.stats.crv_types.LomaxDistribution.check`
   */
  override check(): void {
    const [alpha, lamda] = [this.arg(0), this.arg(1)];
    valueCheck(isReal(alpha), 'Shape parameter should be real.');
    valueCheck(isReal(lamda), 'Scale parameter should be real.');
    valueCheck(isPositive(alpha), 'Shape parameter should be positive.');
    valueCheck(isPositive(lamda), 'Scale parameter should be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.LomaxDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, lamda] = [this.arg(0), this.arg(1)];
    return mul(div(alpha, lamda), pow(add(1, div(x, lamda)), sub(neg(alpha), 1)));
  }
}

/**
 * Lomax distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive shape parameter.
 * @param lamda - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real, positive shape and scale.
 * @see SymPy `sympy.stats.crv_types.Lomax`
 * @example
 * ```ts
 * import { Distribution, Lomax, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a, l] = symbols('a l', { positive: true });
 * const X = Lomax('X', a, l); // => X
 * (density(X) as Distribution).pdf(ex`x`); // => a*(1 + x/l)**(-a - 1)/l
 * ```
 */
export function Lomax(name: string | Sym, alpha: ExprLike, lamda: ExprLike): RandomSymbol {
  return rv(name, LomaxDistribution, [alpha, lamda]);
}

/**
 * The speed distribution for three independent centered normal velocity components with common scale `a`.
 *
 * @see SymPy `sympy.stats.crv_types.MaxwellDistribution`
 */
export class MaxwellDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `MaxwellDistribution`.
   *
   * @param args - Distribution parameters in the order `a`.
   */
  constructor(args: readonly Expr[]) {
    super('MaxwellDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.MaxwellDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a > 0`.
   * @see SymPy `sympy.stats.crv_types.MaxwellDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Parameter a must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.MaxwellDistribution.pdf`
   */
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

/**
 * Maxwell distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a > 0`.
 * @see SymPy `sympy.stats.crv_types.Maxwell`
 * @example
 * ```ts
 * import { Distribution, Maxwell, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a] = symbols('a', { positive: true });
 * const X = Maxwell('x', a); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => sqrt(2)*z**2*exp(-z**2/(2*a**2))/(sqrt(pi)*a**3)
 * ```
 */
export function Maxwell(name: string | Sym, a: ExprLike): RandomSymbol {
  return rv(name, MaxwellDistribution, [a]);
}

/**
 * The Moyal law with location `mu` and scale `sigma`.
 *
 * @see SymPy `sympy.stats.crv_types.MoyalDistribution`
 */
export class MoyalDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `MoyalDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `sigma`.
   */
  constructor(args: readonly Expr[]) {
    super('MoyalDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location and positive real scale.
   * @see SymPy `sympy.stats.crv_types.MoyalDistribution.check`
   */
  override check(): void {
    const [mu, sigma] = [this.arg(0), this.arg(1)];
    valueCheck(isReal(mu), 'Location parameter must be real.');
    // SymPy: sigma.is_real and sigma > 0
    const r = isReal(sigma);
    valueCheck(r === true ? Gt(sigma, 0) : r, 'Scale parameter must be real        and positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.MoyalDistribution.pdf`
   */
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

/**
 * Moyal distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Real location parameter.
 * @param sigma - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location and positive real scale.
 * @see SymPy `sympy.stats.crv_types.Moyal`
 * @example
 * ```ts
 * import { Distribution, Moyal, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu] = symbols('mu', { real: true });
 * const [sigma] = symbols('sigma', { positive: true, real: true });
 * const X = Moyal('x', mu, sigma); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => sqrt(2)*exp(-exp((mu - z)/sigma)/2 - (-mu + z)/(2*sigma))/(2*sqrt(pi)*sigma)
 * ```
 */
export function Moyal(name: string | Sym, mu: ExprLike, sigma: ExprLike): RandomSymbol {
  return rv(name, MoyalDistribution, [mu, sigma]);
}

/**
 * A Nakagami amplitude law with shape `mu` and mean-square amplitude `omega`.
 *
 * @see SymPy `sympy.stats.crv_types.NakagamiDistribution`
 */
export class NakagamiDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `NakagamiDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `omega`.
   */
  constructor(args: readonly Expr[]) {
    super('NakagamiDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.NakagamiDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `mu >= 1/2`, `omega > 0`.
   * @see SymPy `sympy.stats.crv_types.NakagamiDistribution.check`
   */
  override check(): void {
    valueCheck(Ge(this.arg(0), half), 'Shape parameter mu must be greater than equal to 1/2.');
    valueCheck(Gt(this.arg(1), 0), 'Spread parameter omega must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.NakagamiDistribution.pdf`
   */
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

/**
 * Nakagami distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Shape parameter of at least one half.
 * @param omega - Positive spread parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `mu >= 1/2`, `omega > 0`.
 * @see SymPy `sympy.stats.crv_types.Nakagami`
 * @example
 * ```ts
 * import { Distribution, Nakagami, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu, omega] = symbols('mu omega', { positive: true });
 * const X = Nakagami('x', mu, omega); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 2*mu**mu*z**(2*mu - 1)*exp(-mu*z**2/omega)/(omega**mu*gamma(mu))
 * ```
 */
export function Nakagami(name: string | Sym, mu: ExprLike, omega: ExprLike): RandomSymbol {
  return rv(name, NakagamiDistribution, [mu, omega]);
}

/**
 * The Gaussian law with the specified mean and standard deviation.
 *
 * @see SymPy `sympy.stats.crv_types.NormalDistribution`
 */
export class NormalDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `NormalDistribution`.
   *
   * @param args - Distribution parameters in the order `mean`, `std`.
   */
  constructor(args: readonly Expr[]) {
    super('NormalDistribution', args);
  }
  /**
   * Mean or mean vector.
   *
   * @returns Mean or mean vector.
   * @see SymPy `sympy.stats.crv_types.NormalDistribution.mean`
   */
  get mean(): Expr {
    return this.arg(0);
  }
  /**
   * Positive standard deviation or covariance matrix for a random vector.
   *
   * @returns Positive standard deviation or covariance matrix for a random vector.
   * @see SymPy `sympy.stats.crv_types.NormalDistribution.std`
   */
  get std(): Expr {
    return this.arg(1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive standard deviation (for a vector, compatible dimensions and a positive semidefinite covariance matrix).
   * @see SymPy `sympy.stats.crv_types.NormalDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.std, 0), 'Standard deviation must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.NormalDistribution.pdf`
   */
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

/**
 * Normal (Gaussian) distribution.
 *
 * @param name - Name of the symbol.
 * @param mean - Mean or mean vector.
 * @param std - Positive standard deviation or covariance matrix for a random vector.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive standard deviation (for a vector, compatible dimensions and a positive semidefinite covariance matrix).
 * @throws TypeError when scalar and matrix parameters are mixed.
 * @see SymPy `sympy.stats.crv_types.Normal`
 * @example
 * ```ts
 * import { Distribution, Normal, density, ex, expectation, symbols } from '@symjs/symjs';
 *
 * const [sigma] = symbols('sigma', { positive: true });
 * const X = Normal('x', ex`mu`, sigma); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => sqrt(2)*exp(-(-mu + z)**2/(2*sigma**2))/(2*sqrt(pi)*sigma)
 * expectation(X); // => mu
 * ```
 */
export function Normal(name: string | Sym, mean: ExprLike | MatrixParam, std: ExprLike | MatrixParam): RandomSymbol {
  // vector and matrix parameters give the multivariate distribution (SymPy: a list mean, or a matrix mean and a list std, or a matrix std)
  if ((Array.isArray(mean) || (isMatrixParam(mean) && Array.isArray(std)) || isMatrixParam(std)) && isMatrixParam(mean) && isMatrixParam(std)) {
    return defined(statsClasses.multivariateNormal, 'joint_rv_types')(name, mean, std);
  }
  return rv(name, NormalDistribution, [scalarParam(mean), scalarParam(std)]);
}

/**
 * The inverse Gaussian waiting-time law with the specified mean and shape.
 *
 * @see SymPy `sympy.stats.crv_types.GaussianInverseDistribution`
 */
export class GaussianInverseDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `GaussianInverseDistribution`.
   *
   * @param args - Distribution parameters in the order `mean`, `shape`.
   */
  constructor(args: readonly Expr[]) {
    super('GaussianInverseDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.GaussianInverseDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `mean > 0`, `shape > 0`.
   * @see SymPy `sympy.stats.crv_types.GaussianInverseDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'Shape parameter must be positive');
    valueCheck(Gt(this.arg(0), 0), 'Mean must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.GaussianInverseDistribution.pdf`
   */
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

/**
 * Inverse Gaussian distribution.
 *
 * @param name - Name of the symbol.
 * @param mean - Positive mean.
 * @param shape - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `mean > 0`, `shape > 0`.
 * @see SymPy `sympy.stats.crv_types.GaussianInverse`
 * @example
 * ```ts
 * import { Distribution, GaussianInverse, density, symbols } from '@symjs/symjs';
 *
 * const [mu, lamda, z] = symbols('mu lambda z', { positive: true });
 * const X = GaussianInverse('x', mu, lamda); // => x
 * (density(X) as Distribution).pdf(z); // => sqrt(2)*sqrt(lambda)*exp(-lambda*(-mu + z)**2/(2*mu**2*z))/(2*sqrt(pi)*z**(3/2))
 * ```
 */
export function GaussianInverse(name: string | Sym, mean: ExprLike, shape: ExprLike): RandomSymbol {
  return rv(name, GaussianInverseDistribution, [mean, shape]);
}

/**
 * Creates an inverse Gaussian random variable.
 *
 * @param name - Name of the symbol.
 * @param mean - Positive mean.
 * @param shape - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `mean > 0`, `shape > 0`.
 * @see SymPy `sympy.stats.crv_types.GaussianInverse`
 * @example
 * ```ts
 * import { Distribution, Wald, density, symbols } from '@symjs/symjs';
 *
 * const [mu, lamda, z] = symbols('mu lambda z', { positive: true });
 * const X = Wald('x', mu, lamda); // => x
 * (density(X) as Distribution).pdf(z); // => sqrt(2)*sqrt(lambda)*exp(-lambda*(-mu + z)**2/(2*mu**2*z))/(2*sqrt(pi)*z**(3/2))
 * ```
 */
export const Wald = GaussianInverse;

/**
 * A power-law distribution above the threshold `xm`, with tail index `alpha`.
 *
 * @see SymPy `sympy.stats.crv_types.ParetoDistribution`
 */
export class ParetoDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ParetoDistribution`.
   *
   * @param args - Distribution parameters in the order `xm`, `alpha`.
   */
  constructor(args: readonly Expr[]) {
    super('ParetoDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[xm, oo)`.
   * @see SymPy `sympy.stats.crv_types.ParetoDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(0), S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `xm > 0`, `alpha > 0`.
   * @see SymPy `sympy.stats.crv_types.ParetoDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Xm must be positive');
    valueCheck(Gt(this.arg(1), 0), 'Alpha must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ParetoDistribution.pdf`
   */
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

/**
 * Pareto distribution.
 *
 * @param name - Name of the symbol.
 * @param xm - Positive minimum value.
 * @param alpha - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `xm > 0`, `alpha > 0`.
 * @see SymPy `sympy.stats.crv_types.Pareto`
 * @example
 * ```ts
 * import { Distribution, Pareto, density, ex, symbols } from '@symjs/symjs';
 *
 * const [xm, beta] = symbols('xm beta', { positive: true });
 * const X = Pareto('x', xm, beta); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => beta*xm**beta*z**(-beta - 1)
 * ```
 */
export function Pareto(name: string | Sym, xm: ExprLike, alpha: ExprLike): RandomSymbol {
  return rv(name, ParetoDistribution, [xm, alpha]);
}

/**
 * A power-function distribution scaled to the interval from `a` to `b`.
 *
 * @see SymPy `sympy.stats.crv_types.PowerFunctionDistribution`
 */
export class PowerFunctionDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `PowerFunctionDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('PowerFunctionDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[a, b]`.
   * @see SymPy `sympy.stats.crv_types.PowerFunctionDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(1), this.arg(2));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive shape and increasing real endpoints.
   * @see SymPy `sympy.stats.crv_types.PowerFunctionDistribution.check`
   */
  override check(): void {
    const [alpha, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(isReal(a), 'Continuous Boundary parameter should be real.');
    valueCheck(isReal(b), 'Continuous Boundary parameter should be real.');
    valueCheck(Lt(a, b), " 'a' the left Boundary must be smaller than 'b' the right Boundary.");
    valueCheck(isPositive(alpha), 'Continuous Shape parameter should be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.PowerFunctionDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    return div(mul(alpha, pow(sub(x, a), sub(alpha, 1))), pow(sub(b, a), alpha));
  }
}

/**
 * Power function distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive shape parameter.
 * @param a - Lower endpoint.
 * @param b - Upper endpoint.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive shape and increasing real endpoints.
 * @see SymPy `sympy.stats.crv_types.PowerFunction`
 * @example
 * ```ts
 * import { Distribution, PowerFunction, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a, b] = symbols('a b', { real: true });
 * const X = PowerFunction('X', 2, a, b); // => X
 * (density(X) as Distribution).pdf(ex`z`); // => (-2*a + 2*z)/(-a + b)**2
 * ```
 */
export function PowerFunction(name: string | Sym, alpha: ExprLike, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, PowerFunctionDistribution, [alpha, a, b]);
}

/**
 * A bounded distribution whose density is proportional to the squared distance from the midpoint.
 *
 * @see SymPy `sympy.stats.crv_types.QuadraticUDistribution`
 */
export class QuadraticUDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `QuadraticUDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('QuadraticUDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[a, b]`.
   * @see SymPy `sympy.stats.crv_types.QuadraticUDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(1));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a < b`.
   * @see SymPy `sympy.stats.crv_types.QuadraticUDistribution.check`
   */
  override check(): void {
    const [a, b] = [this.arg(0), this.arg(1)];
    valueCheck(Gt(b, a), `Parameter b must be in range (${a.toString()}, oo).`);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.QuadraticUDistribution.pdf`
   */
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

/**
 * U-quadratic distribution on [a, b].
 *
 * @param name - Name of the symbol.
 * @param a - Lower endpoint.
 * @param b - Upper endpoint.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a < b`.
 * @see SymPy `sympy.stats.crv_types.QuadraticU`
 * @remarks For bounds 1 and 3 the law is symmetric about 2. SymPy gives `-11` for this mean.
 * @example
 * ```ts
 * import { Distribution, QuadraticU, density, ex, expectation, symbols } from '@symjs/symjs';
 *
 * const [a, b] = symbols('a b', { real: true });
 * const X = QuadraticU('x', a, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Piecewise((12*(-a/2 - b/2 + z)**2/(-a + b)**3, (b >= z) & (a <= z)), (0, True))
 * expectation(QuadraticU('X', 1, 3)); // => 2
 * ```
 */
export function QuadraticU(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, QuadraticUDistribution, [a, b]);
}

/**
 * A symmetric cosine-shaped density centered at `mu` with support of width `2*s`.
 *
 * @see SymPy `sympy.stats.crv_types.RaisedCosineDistribution`
 */
export class RaisedCosineDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `RaisedCosineDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `s`.
   */
  constructor(args: readonly Expr[]) {
    super('RaisedCosineDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[mu - s, mu + s]`.
   * @see SymPy `sympy.stats.crv_types.RaisedCosineDistribution.set`
   */
  override get set(): SetExpr {
    const [mu, s] = [this.arg(0), this.arg(1)];
    return interval(sub(mu, s), add(mu, s));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `s > 0`.
   * @see SymPy `sympy.stats.crv_types.RaisedCosineDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 's must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.RaisedCosineDistribution.pdf`
   */
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

/**
 * Raised cosine distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Center of the support.
 * @param s - Positive half-width of the support.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `s > 0`.
 * @see SymPy `sympy.stats.crv_types.RaisedCosine`
 * @example
 * ```ts
 * import { Distribution, RaisedCosine, density, ex, symbols } from '@symjs/symjs';
 *
 * const [mu] = symbols('mu', { real: true });
 * const [s] = symbols('s', { positive: true });
 * const X = RaisedCosine('x', mu, s); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Piecewise(((cos(pi*(-mu + z)/s) + 1)/(2*s), (z <= mu + s) & (z >= mu - s)), (0, True))
 * ```
 */
export function RaisedCosine(name: string | Sym, mu: ExprLike, s: ExprLike): RandomSymbol {
  return rv(name, RaisedCosineDistribution, [mu, s]);
}

/**
 * The distribution of the magnitude of two independent centered normal components with standard deviation `sigma`.
 *
 * @see SymPy `sympy.stats.crv_types.RayleighDistribution`
 */
export class RayleighDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `RayleighDistribution`.
   *
   * @param args - Distribution parameters in the order `sigma`.
   */
  constructor(args: readonly Expr[]) {
    super('RayleighDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.RayleighDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `sigma > 0`.
   * @see SymPy `sympy.stats.crv_types.RayleighDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Scale parameter sigma must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.RayleighDistribution.pdf`
   */
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

/**
 * Rayleigh distribution.
 *
 * @param name - Name of the symbol.
 * @param sigma - Positive scale parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `sigma > 0`.
 * @see SymPy `sympy.stats.crv_types.Rayleigh`
 * @example
 * ```ts
 * import { Distribution, Rayleigh, density, ex, symbols } from '@symjs/symjs';
 *
 * const [sigma] = symbols('sigma', { positive: true });
 * const X = Rayleigh('x', sigma); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => z*exp(-z**2/(2*sigma**2))/sigma**2
 * ```
 */
export function Rayleigh(name: string | Sym, sigma: ExprLike): RandomSymbol {
  return rv(name, RayleighDistribution, [sigma]);
}

/**
 * A log-uniform law whose density is proportional to `1/x` between two positive endpoints.
 *
 * @see SymPy `sympy.stats.crv_types.ReciprocalDistribution`
 */
export class ReciprocalDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ReciprocalDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`.
   */
  constructor(args: readonly Expr[]) {
    super('ReciprocalDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[a, b]`.
   * @see SymPy `sympy.stats.crv_types.ReciprocalDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(1));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `0 < a < b`.
   * @see SymPy `sympy.stats.crv_types.ReciprocalDistribution.check`
   */
  override check(): void {
    const [a, b] = [this.arg(0), this.arg(1)];
    valueCheck(Gt(a, 0), `Parameter > 0. a = ${a.toString()}`);
    valueCheck(Lt(a, b), `Parameter b must be in range (${a.toString()}, +oo]. b = ${b.toString()}`);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ReciprocalDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [a, b] = [this.arg(0), this.arg(1)];
    return pow(mul(x, sub(log(b), log(a))), -1);
  }
}

/**
 * Reciprocal distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Positive lower endpoint.
 * @param b - Upper endpoint greater than the lower endpoint.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `0 < a < b`.
 * @see SymPy `sympy.stats.crv_types.Reciprocal`
 * @example
 * ```ts
 * import { Distribution, Reciprocal, density, symbols } from '@symjs/symjs';
 *
 * const [a, b, x] = symbols('a b x', { positive: true });
 * const X = Reciprocal('R', a, b); // => R
 * (density(X) as Distribution).pdf(x); // => 1/(x*(-log(a) + log(b)))
 * ```
 */
export function Reciprocal(name: string | Sym, a: ExprLike, b: ExprLike): RandomSymbol {
  return rv(name, ReciprocalDistribution, [a, b]);
}

/**
 * The shifted Gompertz law with positive scale and shape parameters.
 *
 * @see SymPy `sympy.stats.crv_types.ShiftedGompertzDistribution`
 */
export class ShiftedGompertzDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `ShiftedGompertzDistribution`.
   *
   * @param args - Distribution parameters in the order `b`, `eta`.
   */
  constructor(args: readonly Expr[]) {
    super('ShiftedGompertzDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.ShiftedGompertzDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `b > 0`, `eta > 0`.
   * @see SymPy `sympy.stats.crv_types.ShiftedGompertzDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'b must be positive');
    valueCheck(Gt(this.arg(1), 0), 'eta must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.ShiftedGompertzDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [b, eta] = [this.arg(0), this.arg(1)];
    const e = exp(mul(neg(b), x));
    return mul(b, e, exp(mul(neg(eta), e)), add(1, mul(eta, sub(1, e))));
  }
}

/**
 * Shifted Gompertz distribution.
 *
 * @param name - Name of the symbol.
 * @param b - Positive scale parameter.
 * @param eta - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `b > 0`, `eta > 0`.
 * @see SymPy `sympy.stats.crv_types.ShiftedGompertz`
 * @example
 * ```ts
 * import { Distribution, ShiftedGompertz, density, ex, symbols } from '@symjs/symjs';
 *
 * const [b, eta] = symbols('b eta', { positive: true });
 * const X = ShiftedGompertz('x', b, eta); // => x
 * (density(X) as Distribution).pdf(ex`x`); // => b*(eta*(1 - exp(-b*x)) + 1)*exp(-b*x)*exp(-eta*exp(-b*x))
 * ```
 */
export function ShiftedGompertz(name: string | Sym, b: ExprLike, eta: ExprLike): RandomSymbol {
  return rv(name, ShiftedGompertzDistribution, [b, eta]);
}

/**
 * The Student t law with `nu` degrees of freedom.
 *
 * @see SymPy `sympy.stats.crv_types.StudentTDistribution`
 */
export class StudentTDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `StudentTDistribution`.
   *
   * @param args - Distribution parameters in the order `nu`.
   */
  constructor(args: readonly Expr[]) {
    super('StudentTDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `nu > 0`.
   * @see SymPy `sympy.stats.crv_types.StudentTDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Degrees of freedom nu must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.StudentTDistribution.pdf`
   */
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

/**
 * Student's t distribution.
 *
 * @param name - Name of the symbol.
 * @param nu - Positive degrees of freedom.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `nu > 0`.
 * @see SymPy `sympy.stats.crv_types.StudentT`
 * @example
 * ```ts
 * import { Distribution, StudentT, density, ex, symbols } from '@symjs/symjs';
 *
 * const [nu] = symbols('nu', { positive: true });
 * const X = StudentT('x', nu); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => (1 + z**2/nu)**(-nu/2 - 1/2)/(sqrt(nu)*beta(1/2, nu/2))
 * ```
 */
export function StudentT(name: string | Sym, nu: ExprLike): RandomSymbol {
  return rv(name, StudentTDistribution, [nu]);
}

/**
 * A bounded density that rises linearly, stays constant on a plateau, and falls linearly.
 *
 * @see SymPy `sympy.stats.crv_types.TrapezoidalDistribution`
 */
export class TrapezoidalDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `TrapezoidalDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`, `c`, `d`.
   */
  constructor(args: readonly Expr[]) {
    super('TrapezoidalDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[a, d]`.
   * @see SymPy `sympy.stats.crv_types.TrapezoidalDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(3));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a <= b < c <= d`.
   * @see SymPy `sympy.stats.crv_types.TrapezoidalDistribution.check`
   */
  override check(): void {
    const [a, b, c, d] = [this.arg(0), this.arg(1), this.arg(2), this.arg(3)];
    const s = (e: Expr): string => e.toString();
    valueCheck(Lt(a, d), `Lower bound parameter a < ${s(d)}. a = ${s(a)}`);
    valueCheck([Le(a, b), Lt(b, c)], `Level start parameter b must be in range [${s(a)}, ${s(c)}). b = ${s(b)}`);
    valueCheck([Lt(b, c), Le(c, d)], `Level end parameter c must be in range (${s(b)}, ${s(d)}]. c = ${s(c)}`);
    valueCheck(Ge(d, c), `Upper bound parameter d > ${s(c)}. d = ${s(d)}`);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.TrapezoidalDistribution.pdf`
   */
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

/**
 * Trapezoidal distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Lower endpoint.
 * @param b - Left edge of the plateau.
 * @param c - Right edge of the plateau.
 * @param d - Upper endpoint.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a <= b < c <= d`.
 * @see SymPy `sympy.stats.crv_types.Trapezoidal`
 * @example
 * ```ts
 * import { Distribution, Trapezoidal, density, ex } from '@symjs/symjs';
 *
 * const X = Trapezoidal('x', ex`a`, ex`b`, ex`c`, ex`d`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Piecewise(((-2*a + 2*z)/((-a + b)*(-a - b + c + d)), (a <= z) & (b > z)), (2/(-a - b + c + d), (b <= z) & (c > z)), ((2*d - 2*z)/((-c + d)*(-a - b + c + d)), (d >= z) & (c <= z)), (0, True))
 * ```
 */
export function Trapezoidal(name: string | Sym, a: ExprLike, b: ExprLike, c: ExprLike, d: ExprLike): RandomSymbol {
  return rv(name, TrapezoidalDistribution, [a, b, c, d]);
}

/**
 * A piecewise linear density with endpoints `a` and `b` and mode `c`.
 *
 * @see SymPy `sympy.stats.crv_types.TriangularDistribution`
 */
export class TriangularDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `TriangularDistribution`.
   *
   * @param args - Distribution parameters in the order `a`, `b`, `c`.
   */
  constructor(args: readonly Expr[]) {
    super('TriangularDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[a, b]`.
   * @see SymPy `sympy.stats.crv_types.TriangularDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.arg(0), this.arg(1));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a < b`, `a <= c <= b`.
   * @see SymPy `sympy.stats.crv_types.TriangularDistribution.check`
   */
  override check(): void {
    const [a, b, c] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck(Gt(b, a), `Parameter b > ${a.toString()}. b = ${b.toString()}`);
    valueCheck([Le(a, c), Le(c, b)], `Parameter c must be in range [${a.toString()}, ${b.toString()}]. c = ${c.toString()}`);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.TriangularDistribution.pdf`
   */
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

/**
 * Triangular distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Lower endpoint.
 * @param b - Upper endpoint.
 * @param c - Mode.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a < b`, `a <= c <= b`.
 * @see SymPy `sympy.stats.crv_types.Triangular`
 * @example
 * ```ts
 * import { Distribution, Triangular, density, ex } from '@symjs/symjs';
 *
 * const X = Triangular('x', ex`a`, ex`b`, ex`c`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Piecewise(((-2*a + 2*z)/((-a + b)*(-a + c)), (a <= z) & (c > z)), (2/(-a + b), Eq(c, z)), ((2*b - 2*z)/((-a + b)*(b - c)), (b >= z) & (c < z)), (0, True))
 * ```
 */
export function Triangular(name: string | Sym, a: ExprLike, b: ExprLike, c: ExprLike): RandomSymbol {
  return rv(name, TriangularDistribution, [a, b, c]);
}

/**
 * A constant density between two finite endpoints.
 *
 * @see SymPy `sympy.stats.crv_types.UniformDistribution`
 */
export class UniformDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `UniformDistribution`.
   *
   * @param args - Distribution parameters in the order `left`, `right`.
   */
  constructor(args: readonly Expr[]) {
    super('UniformDistribution', args);
  }
  /**
   * Lower endpoint.
   *
   * @returns Lower endpoint.
   * @see SymPy `sympy.stats.crv_types.UniformDistribution.left`
   */
  get left(): Expr {
    return this.arg(0);
  }
  /**
   * Upper endpoint.
   *
   * @returns Upper endpoint.
   * @see SymPy `sympy.stats.crv_types.UniformDistribution.right`
   */
  get right(): Expr {
    return this.arg(1);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[left, right]`.
   * @see SymPy `sympy.stats.crv_types.UniformDistribution.set`
   */
  override get set(): SetExpr {
    return interval(this.left, this.right);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `left < right`.
   * @see SymPy `sympy.stats.crv_types.UniformDistribution.check`
   */
  override check(): void {
    valueCheck(Lt(this.left, this.right), 'Lower limit should be less than Upper limit.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.UniformDistribution.pdf`
   */
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
  /**
   * Evaluated, with Max(left, right) = right and Min(left, right) = left.
   *
   * @param expr - Expression to evaluate.
   * @param v - Symbol distributed according to this law.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value of the expression in this process.
   * @see SymPy `sympy.stats.crv_types.UniformDistribution.expectation`
   */
  override expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    const r = super.expectation(expr, v, { ...opts, evaluate: true });
    return r.subs([
      [Max(this.left, this.right), this.right],
      [Min(this.left, this.right), this.left],
    ]);
  }
}

/**
 * Uniform distribution on [left, right].
 *
 * @param name - Name of the symbol.
 * @param left - Lower endpoint.
 * @param right - Upper endpoint.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `left < right`.
 * @see SymPy `sympy.stats.crv_types.Uniform`
 * @example
 * ```ts
 * import { Distribution, Uniform, density, ex, symbols } from '@symjs/symjs';
 *
 * const [a] = symbols('a', { negative: true });
 * const [b] = symbols('b', { positive: true });
 * const X = Uniform('x', a, b); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Piecewise((1/(-a + b), (b >= z) & (a <= z)), (0, True))
 * ```
 */
export function Uniform(name: string | Sym, left: ExprLike, right: ExprLike): RandomSymbol {
  return rv(name, UniformDistribution, [left, right]);
}

/**
 * The distribution of the sum of `n` independent uniform variables on the unit interval.
 *
 * @see SymPy `sympy.stats.crv_types.UniformSumDistribution`
 */
export class UniformSumDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `UniformSumDistribution`.
   *
   * @param args - Distribution parameters in the order `n`.
   */
  constructor(args: readonly Expr[]) {
    super('UniformSumDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, n]`.
   * @see SymPy `sympy.stats.crv_types.UniformSumDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, this.arg(0));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer number of summands.
   * @see SymPy `sympy.stats.crv_types.UniformSumDistribution.check`
   */
  override check(): void {
    const n = this.arg(0);
    valueCheck([Gt(n, 0), isIntegerValued(n)], 'Parameter n must be positive integer.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.UniformSumDistribution.pdf`
   */
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

/**
 * Uniform sum (Irwin-Hall) distribution.
 *
 * @param name - Name of the symbol.
 * @param n - Number of independent standard uniform variables to sum.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for a positive integer number of summands.
 * @see SymPy `sympy.stats.crv_types.UniformSum`
 * @example
 * ```ts
 * import { Distribution, UniformSum, density, ex, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n', { integer: true });
 * const X = UniformSum('x', n); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => Sum((-1)**_k*(-_k + z)**(n - 1)*binomial(n, _k), (_k, 0, floor(z)))/factorial(n - 1)
 * ```
 */
export function UniformSum(name: string | Sym, n: ExprLike): RandomSymbol {
  return rv(name, UniformSumDistribution, [n]);
}

/**
 * A circular distribution with mean direction `mu` and concentration `k`.
 *
 * @see SymPy `sympy.stats.crv_types.VonMisesDistribution`
 */
export class VonMisesDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `VonMisesDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `k`.
   */
  constructor(args: readonly Expr[]) {
    super('VonMisesDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, 2*pi]`.
   * @see SymPy `sympy.stats.crv_types.VonMisesDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, mul(2, S.Pi));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `k > 0`.
   * @see SymPy `sympy.stats.crv_types.VonMisesDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(1), 0), 'k must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.VonMisesDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [mu, k] = [this.arg(0), this.arg(1)];
    return div(exp(mul(k, cos(sub(x, mu)))), mul(2, S.Pi, besseli(0, k)));
  }
}

/**
 * Von Mises distribution.
 *
 * @param name - Name of the symbol.
 * @param mu - Mean direction in radians.
 * @param k - Concentration parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `k > 0`.
 * @see SymPy `sympy.stats.crv_types.VonMises`
 * @example
 * ```ts
 * import { Distribution, VonMises, density, ex, symbols } from '@symjs/symjs';
 *
 * const [k] = symbols('k', { positive: true });
 * const X = VonMises('x', ex`mu`, k); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => exp(k*cos(mu - z))/(2*pi*besseli(0, k))
 * ```
 */
export function VonMises(name: string | Sym, mu: ExprLike, k: ExprLike): RandomSymbol {
  return rv(name, VonMisesDistribution, [mu, k]);
}

/**
 * The Weibull lifetime law parameterized by scale `alpha` and shape `beta`.
 *
 * @see SymPy `sympy.stats.crv_types.WeibullDistribution`
 */
export class WeibullDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `WeibullDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('WeibullDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[0, oo)`.
   * @see SymPy `sympy.stats.crv_types.WeibullDistribution.set`
   */
  override get set(): SetExpr {
    return interval(0, S.Infinity);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
   * @see SymPy `sympy.stats.crv_types.WeibullDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Alpha must be positive');
    valueCheck(Gt(this.arg(1), 0), 'Beta must be positive');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.WeibullDistribution.pdf`
   */
  pdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    const [alpha, beta] = [this.arg(0), this.arg(1)];
    return div(mul(beta, pow(div(x, alpha), sub(beta, 1)), exp(neg(pow(div(x, alpha), beta)))), alpha);
  }
}

/**
 * Weibull distribution.
 *
 * @param name - Name of the symbol.
 * @param alpha - Positive scale parameter.
 * @param beta - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `alpha > 0`, `beta > 0`.
 * @see SymPy `sympy.stats.crv_types.Weibull`
 * @example
 * ```ts
 * import { Distribution, Weibull, density, ex, symbols } from '@symjs/symjs';
 *
 * const [l, k] = symbols('lambda k', { positive: true });
 * const X = Weibull('x', l, k); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => k*(z/lambda)**(k - 1)*exp(-(z/lambda)**k)/lambda
 * ```
 */
export function Weibull(name: string | Sym, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, WeibullDistribution, [alpha, beta]);
}

/**
 * A density proportional to the height of a semicircle of radius `R`, centered at zero.
 *
 * @see SymPy `sympy.stats.crv_types.WignerSemicircleDistribution`
 */
export class WignerSemicircleDistribution extends SingleContinuousDistribution {
  /**
   * Constructs a new `WignerSemicircleDistribution`.
   *
   * @param args - Distribution parameters in the order `R`.
   */
  constructor(args: readonly Expr[]) {
    super('WignerSemicircleDistribution', args);
  }
  /**
   * The support of the distribution.
   *
   * @returns The interval `[-R, R]`.
   * @see SymPy `sympy.stats.crv_types.WignerSemicircleDistribution.set`
   */
  override get set(): SetExpr {
    return interval(neg(this.arg(0)), this.arg(0));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `R > 0`.
   * @see SymPy `sympy.stats.crv_types.WignerSemicircleDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'Radius R must be positive.');
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.crv_types.WignerSemicircleDistribution.pdf`
   */
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

/**
 * Wigner semicircle distribution.
 *
 * @param name - Name of the symbol.
 * @param R - Positive radius of the support.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `R > 0`.
 * @see SymPy `sympy.stats.crv_types.WignerSemicircle`
 * @example
 * ```ts
 * import { Distribution, WignerSemicircle, density, ex, symbols } from '@symjs/symjs';
 *
 * const [R] = symbols('R', { positive: true });
 * const X = WignerSemicircle('x', R); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 2*sqrt(R**2 - z**2)/(pi*R**2)
 * ```
 */
export function WignerSemicircle(name: string | Sym, R: ExprLike): RandomSymbol {
  return rv(name, WignerSemicircleDistribution, [R]);
}

statsClasses.continuousHandmade = (pdf, set) => new ContinuousDistributionHandmade(set === undefined ? [pdf] : [pdf, set]);
