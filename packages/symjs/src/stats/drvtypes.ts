// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/drv_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.drv_types: the discrete distributions on the
 * integers and the functions that create random symbols with them
 * (`Poisson('X', lamda)`, `Geometric('X', p)`, ...).
 */

import { Dummy, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, exp, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Lt, piecewise } from '../core/logic';
import { Lambda, LambdaNode } from '../core/lambda';
import { Sum } from '../core/concrete';
import { isNonNegative } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined } from '../core/guard';
import { Integers, Naturals, Naturals0, SetExpr, asRelational, inf, sup } from '../sets/sets';
import { log } from '../functions/elementary/elementary';
import { beta, binomial, factorial, floor, zeta } from '../functions/special/special';
import { besseli } from '../functions/special/bessel';
import { hyper } from '../functions/special/hyper';
import { polylog } from '../functions/special/zetafunctions';
import { doit } from '../calculus/doit';
import { Fn } from '../core/nodes';
import { isPositive, isIntegerQ as isIntegerValued } from '../core/assumptions';
import { isRandom, statsClasses, valueCheck } from './rv';
import type { ComputeOptions , RandomSymbol} from './rv';
import { SingleDiscreteDistribution, SingleDiscretePSpace } from './drv';
import type { ClosedForm } from './crv';
import type { RVOptions } from './crvtypes';

const neg = (e: ExprLike): Expr => mul(-1, e);
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));

/** A discrete distribution class (constructed from its parameters). */
type DistributionClass = new (args: readonly Expr[]) => SingleDiscreteDistribution;

/** A random symbol with the distribution of the parameters (SymPy rv of drv_types). */
export function rv(symbol: string | Sym, cls: DistributionClass, params: readonly ExprLike[], opts: RVOptions = {}): RandomSymbol {
  const args = params.map(sympify);
  const dist = new cls(args);
  if (opts.check ?? true) dist.check();
  if (args.some((a) => isRandom(a))) return defined(statsClasses.compound, 'compound_rv')(symbol, dist);
  return new SingleDiscretePSpace([typeof symbol === 'string' ? new Sym(symbol) : symbol, dist]).value;
}

/**
 * A distribution given by a Lambda mass function on a set.
 *
 * @see SymPy `sympy.stats.drv_types.DiscreteDistributionHandmade`
 */
export class DiscreteDistributionHandmade extends SingleDiscreteDistribution {
  /**
   * Constructs a new `DiscreteDistributionHandmade`.
   *
   * @param args - Operands in the order `pdf`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super('DiscreteDistributionHandmade', args.length === 1 ? [at(args, 0), Integers] : args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.DiscreteDistributionHandmade.set`
   */
  override get set(): SetExpr {
    return cast(this.arg(1), SetExpr);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param x - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.DiscreteDistributionHandmade.pdf`
   */
  pdf(x: ExprLike): Expr {
    return cast(this.arg(0), LambdaNode, 'pdf').call(x);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when a parameter is known to violate the distribution constraints.
   * @see SymPy `sympy.stats.drv_types.DiscreteDistributionHandmade.check`
   */
  override check(): void {
    const x = new Dummy('x');
    const val = doit(Sum(this.pdf(x), [x, inf(this.set), sup(this.set)]));
    valueCheck(Eq(val, 1) !== S.false, 'The pdf is incorrect on the given set.');
  }
}

/**
 * Defines a discrete random variable by its mass function on a support set.
 *
 * @param symbol - Symbol used as the variable in the density and as the name of the random variable.
 * @param densityIn - Density on the support.
 * @param set - Support of the distribution.
 * @param opts - Set `check` to true to verify normalization.
 * @returns The random symbol with the specified law.
 * @throws RangeError when checking is enabled and the masses are known not to sum to one.
 * @see SymPy `sympy.stats.drv_types.DiscreteRV`
 * @example
 * ```ts
 * import { DiscreteRV, FiniteSet, ex, expectation, length, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * expectation(DiscreteRV(x, ex`1/10`, FiniteSet.of(0, 1, 2, 3, 4, 5, 6, 7, 8, 9))); // => 9/2
 * ```
 */
export function DiscreteRV(symbol: Sym, densityIn: ExprLike, set: SetExpr = Integers, opts: RVOptions = {}): RandomSymbol {
  const pdf = Lambda(symbol, piecewise([densityIn, asRelational(set, symbol)], [0, true]));
  return rv(symbol.name, DiscreteDistributionHandmade, [pdf, set], { check: opts.check ?? false });
}

/**
 * The Flory–Schulz distribution of positive integer chain lengths.
 *
 * @see SymPy `sympy.stats.drv_types.FlorySchulzDistribution`
 */
export class FlorySchulzDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `FlorySchulzDistribution`.
   *
   * @param args - Distribution parameters in the order `a`.
   */
  constructor(args: readonly Expr[]) {
    super('FlorySchulzDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.FlorySchulzDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `0 < a < 1`.
   * @see SymPy `sympy.stats.drv_types.FlorySchulzDistribution.check`
   */
  override check(): void {
    const a = this.arg(0);
    valueCheck([Lt(0, a), Lt(a, 1)], 'a must be between 0 and 1');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.FlorySchulzDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const a = this.arg(0);
    return mul(pow(a, 2), k, pow(sub(1, a), sub(k, 1)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const a = this.arg(0);
    return div(mul(pow(a, 2), exp(mul(S.I, t))), pow(add(1, mul(sub(a, 1), exp(mul(S.I, t)))), 2));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const a = this.arg(0);
    return div(mul(pow(a, 2), exp(t)), pow(add(1, mul(sub(a, 1), exp(t))), 2));
  }
}

/**
 * Constructs a random variable with the Flory-Schulz distribution.
 *
 * @param name - Name of the symbol.
 * @param a - Shape parameter between zero and one.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `0 < a < 1`.
 * @see SymPy `sympy.stats.drv_types.FlorySchulz`
 * @example
 * ```ts
 * import { Distribution, FlorySchulz, density, ex } from '@symjs/symjs';
 *
 * const X = FlorySchulz('x', ex`1/5`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => (4/5)**(z - 1)*z/25
 * ```
 */
export function FlorySchulz(name: string | Sym, a: ExprLike): RandomSymbol {
  return rv(name, FlorySchulzDistribution, [a]);
}

/**
 * The distribution of the number of trials up to and including the first success.
 *
 * @see SymPy `sympy.stats.drv_types.GeometricDistribution`
 */
export class GeometricDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `GeometricDistribution`.
   *
   * @param args - Distribution parameters in the order `p`.
   */
  constructor(args: readonly Expr[]) {
    super('GeometricDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.GeometricDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `0 < p <= 1`.
   * @see SymPy `sympy.stats.drv_types.GeometricDistribution.check`
   */
  override check(): void {
    const p = this.arg(0);
    valueCheck([Lt(0, p), Ge(1, p)], 'p must be between 0 and 1');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.GeometricDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const p = this.arg(0);
    return mul(pow(sub(1, p), sub(k, 1)), p);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(mul(p, exp(mul(S.I, t))), sub(1, mul(sub(1, p), exp(mul(S.I, t)))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(mul(p, exp(t)), sub(1, mul(sub(1, p), exp(t))));
  }
}

/**
 * Constructs a random variable with the geometric distribution.
 *
 * @param name - Name of the symbol.
 * @param p - Probability of success on each trial.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `0 < p <= 1`.
 * @see SymPy `sympy.stats.drv_types.Geometric`
 * @example
 * ```ts
 * import { Distribution, Geometric, density, ex, expectation } from '@symjs/symjs';
 *
 * const X = Geometric('x', ex`1/5`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => (4/5)**(z - 1)/5
 * expectation(X); // => 5
 * ```
 */
export function Geometric(name: string | Sym, p: ExprLike): RandomSymbol {
  return rv(name, GeometricDistribution, [p]);
}

/**
 * The discrete law of the sum of a Poisson count and twice an independent Poisson count.
 *
 * @see SymPy `sympy.stats.drv_types.HermiteDistribution`
 */
export class HermiteDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `HermiteDistribution`.
   *
   * @param args - Distribution parameters in the order `a1`, `a2`.
   */
  constructor(args: readonly Expr[]) {
    super('HermiteDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.HermiteDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals0;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `a1 >= 0`, `a2 >= 0`.
   * @see SymPy `sympy.stats.drv_types.HermiteDistribution.check`
   */
  override check(): void {
    valueCheck(isNonNegative(this.arg(0)), 'Parameter a1 must be >= 0.');
    valueCheck(isNonNegative(this.arg(1)), 'Parameter a2 must be >= 0.');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.HermiteDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [a1, a2] = [this.arg(0), this.arg(1)];
    const term1 = exp(neg(add(a1, a2)));
    const j = new Dummy('j', { integer: true });
    const num = mul(pow(a1, sub(k, mul(2, j))), pow(a2, j));
    const den = mul(factorial(sub(k, mul(2, j))), factorial(j));
    return mul(term1, doit(Sum(div(num, den), [j, 0, floor(div(k, 2))])));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [a1, a2] = [this.arg(0), this.arg(1)];
    return exp(add(mul(a1, sub(exp(t), 1)), mul(a2, sub(exp(mul(2, t)), 1))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [a1, a2] = [this.arg(0), this.arg(1)];
    return exp(add(mul(a1, sub(exp(mul(S.I, t)), 1)), mul(a2, sub(exp(mul(2, S.I, t)), 1))));
  }
}

/**
 * Constructs a random variable with the Hermite distribution.
 *
 * @param name - Name of the symbol.
 * @param a1 - Mean of the first Poisson component.
 * @param a2 - Mean of the Poisson component counted twice.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `a1 >= 0`, `a2 >= 0`.
 * @see SymPy `sympy.stats.drv_types.Hermite`
 * @example
 * ```ts
 * import { Distribution, Hermite, density } from '@symjs/symjs';
 *
 * const X = Hermite('H', 5, 4); // => H
 * (density(X) as Distribution).pdf(2); // => 33*exp(-9)/2
 * ```
 */
export function Hermite(name: string | Sym, a1: ExprLike, a2: ExprLike): RandomSymbol {
  return rv(name, HermiteDistribution, [a1, a2]);
}

/**
 * A positive integer law with mass proportional to `p**k/k`.
 *
 * @see SymPy `sympy.stats.drv_types.LogarithmicDistribution`
 */
export class LogarithmicDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `LogarithmicDistribution`.
   *
   * @param args - Distribution parameters in the order `p`.
   */
  constructor(args: readonly Expr[]) {
    super('LogarithmicDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.LogarithmicDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `0 < p < 1`.
   * @see SymPy `sympy.stats.drv_types.LogarithmicDistribution.check`
   */
  override check(): void {
    const p = this.arg(0);
    valueCheck([Gt(p, 0), Lt(p, 1)], 'p should be between 0 and 1');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.LogarithmicDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const p = this.arg(0);
    return div(mul(-1, pow(p, k)), mul(k, log(sub(1, p))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(log(sub(1, mul(p, exp(mul(S.I, t))))), log(sub(1, p)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(log(sub(1, mul(p, exp(t)))), log(sub(1, p)));
  }
}

/**
 * Constructs a random variable with the logarithmic distribution.
 *
 * @param name - Name of the symbol.
 * @param p - Distribution parameter between zero and one.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `0 < p < 1`.
 * @see SymPy `sympy.stats.drv_types.Logarithmic`
 * @remarks SymPy writes the same mass as `-1/(5**z*z*log(4/5))`.
 * @example
 * ```ts
 * import { Distribution, Logarithmic, density, ex } from '@symjs/symjs';
 *
 * const X = Logarithmic('x', ex`1/5`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => -(1/5)**z/(z*log(4/5))
 * ```
 */
export function Logarithmic(name: string | Sym, p: ExprLike): RandomSymbol {
  return rv(name, LogarithmicDistribution, [p]);
}

/**
 * The count distribution for failures before `r` successes, extended to positive real `r`.
 *
 * @see SymPy `sympy.stats.drv_types.NegativeBinomialDistribution`
 */
export class NegativeBinomialDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `NegativeBinomialDistribution`.
   *
   * @param args - Distribution parameters in the order `r`, `p`.
   */
  constructor(args: readonly Expr[]) {
    super('NegativeBinomialDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.NegativeBinomialDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals0;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `r > 0`, `0 < p < 1`.
   * @see SymPy `sympy.stats.drv_types.NegativeBinomialDistribution.check`
   */
  override check(): void {
    const [r, p] = [this.arg(0), this.arg(1)];
    valueCheck(Gt(r, 0), 'r should be positive');
    valueCheck([Gt(p, 0), Lt(p, 1)], 'p should be between 0 and 1');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.NegativeBinomialDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [r, p] = [this.arg(0), this.arg(1)];
    return mul(binomial(add(k, r, -1), k), pow(sub(1, p), k), pow(p, r));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [r, p] = [this.arg(0), this.arg(1)];
    return pow(div(p, sub(1, mul(sub(1, p), exp(mul(S.I, t))))), r);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [r, p] = [this.arg(0), this.arg(1)];
    return pow(div(p, sub(1, mul(sub(1, p), exp(t)))), r);
  }
}

/**
 * Constructs a random variable with the negative binomial distribution.
 *
 * @param name - Name of the symbol.
 * @param r - Positive shape, equal to the target number of successes for integer values.
 * @param p - Success probability on each trial, strictly between zero and one.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `r > 0`, `0 < p < 1`.
 * @see SymPy `sympy.stats.drv_types.NegativeBinomial`
 * @example
 * ```ts
 * import { Distribution, NegativeBinomial, density, ex, expectation, variance } from '@symjs/symjs';
 *
 * const X = NegativeBinomial('x', 5, ex`1/3`); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => (2/3)**z*binomial(z + 4, z)/243
 * expectation(X); // => 10
 * variance(X); // => 30
 * ```
 */
export function NegativeBinomial(name: string | Sym, r: ExprLike, p: ExprLike): RandomSymbol {
  return rv(name, NegativeBinomialDistribution, [r, p]);
}

/**
 * The count law for independent events with a specified mean count.
 *
 * @see SymPy `sympy.stats.drv_types.PoissonDistribution`
 */
export class PoissonDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `PoissonDistribution`.
   *
   * @param args - Distribution parameters in the order `lamda`.
   */
  constructor(args: readonly Expr[]) {
    super('PoissonDistribution', args);
  }
  /**
   * Specifies the expected number of events in the Poisson distribution.
   *
   * @returns The positive mean count.
   * @see SymPy `sympy.stats.drv_types.PoissonDistribution.lamda`
   */
  get lamda(): Expr {
    return this.arg(0);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.PoissonDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals0;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `lamda > 0`.
   * @see SymPy `sympy.stats.drv_types.PoissonDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.lamda, 0), 'Lambda must be positive');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.PoissonDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    return mul(div(pow(this.lamda, k), factorial(k)), exp(neg(this.lamda)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return exp(mul(this.lamda, sub(exp(mul(S.I, t)), 1)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return exp(mul(this.lamda, sub(exp(t), 1)));
  }
  /**
   * Computes the Poisson expectation using its mean and factorial moments.
   *
   * @param expr - Expression to evaluate.
   * @param v - Symbol distributed according to this law.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value.
   * @see SymPy `sympy.stats.drv_types.PoissonDistribution.expectation`
   */
  override expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    if (opts.evaluate ?? true) {
      if (expr.key === v.key) return this.lamda;
      if (expr instanceof Fn && expr.name === 'ff' && isIntegerValued(at(expr.args, 1)) === true && isPositive(at(expr.args, 1)) === true && at(expr.args, 0).key === v.key) {
        return pow(this.lamda, at(expr.args, 1));
      }
    }
    return super.expectation(expr, v, opts);
  }
}

/**
 * Constructs a random variable with the Poisson distribution.
 *
 * @param name - Name of the symbol.
 * @param lamda - Positive mean event count.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `lamda > 0`.
 * @see SymPy `sympy.stats.drv_types.Poisson`
 * @example
 * ```ts
 * import { Distribution, Poisson, density, ex, expectation, symbols } from '@symjs/symjs';
 *
 * const [rate] = symbols('lambda', { positive: true });
 * const X = Poisson('x', rate); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => lambda**z*exp(-lambda)/factorial(z)
 * expectation(X); // => lambda
 * ```
 */
export function Poisson(name: string | Sym, lamda: ExprLike): RandomSymbol {
  return rv(name, PoissonDistribution, [lamda]);
}

/**
 * The distribution of the difference of two independent Poisson counts.
 *
 * @see SymPy `sympy.stats.drv_types.SkellamDistribution`
 */
export class SkellamDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `SkellamDistribution`.
   *
   * @param args - Distribution parameters in the order `mu1`, `mu2`.
   */
  constructor(args: readonly Expr[]) {
    super('SkellamDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `mu1 >= 0`, `mu2 >= 0`.
   * @see SymPy `sympy.stats.drv_types.SkellamDistribution.check`
   */
  override check(): void {
    valueCheck(Ge(this.arg(0), 0), 'Parameter mu1 must be >= 0');
    valueCheck(Ge(this.arg(1), 0), 'Parameter mu2 must be >= 0');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.SkellamDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [mu1, mu2] = [this.arg(0), this.arg(1)];
    const term1 = mul(exp(neg(add(mu1, mu2))), pow(div(mu1, mu2), div(k, 2)));
    const term2 = besseli(k, mul(2, sqrt(mul(mu1, mu2))));
    return mul(term1, term2);
  }
  protected override cdfClosed(_x: Expr): ClosedForm {
    throw new NotImplementedError("Skellam doesn't have closed form for the CDF.");
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu1, mu2] = [this.arg(0), this.arg(1)];
    return exp(add(neg(add(mu1, mu2)), mul(mu1, exp(mul(S.I, t))), mul(mu2, exp(mul(-1, S.I, t)))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mu1, mu2] = [this.arg(0), this.arg(1)];
    return exp(add(neg(add(mu1, mu2)), mul(mu1, exp(t)), mul(mu2, exp(neg(t)))));
  }
}

/**
 * Constructs a random variable with the Skellam distribution.
 *
 * @param name - Name of the symbol.
 * @param mu1 - Mean of the first Poisson variable.
 * @param mu2 - Mean of the Poisson variable subtracted from the first.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `mu1 >= 0`, `mu2 >= 0`.
 * @see SymPy `sympy.stats.drv_types.Skellam`
 * @example
 * ```ts
 * import { Distribution, Skellam, density, symbols } from '@symjs/symjs';
 *
 * const [mu1, mu2] = symbols('mu1 mu2', { positive: true });
 * const [z] = symbols('z', { integer: true });
 * const X = Skellam('x', mu1, mu2); // => x
 * (density(X) as Distribution).pdf(z); // => (mu1/mu2)**(z/2)*exp(-mu1 - mu2)*besseli(z, 2*sqrt(mu1)*sqrt(mu2))
 * ```
 */
export function Skellam(name: string | Sym, mu1: ExprLike, mu2: ExprLike): RandomSymbol {
  return rv(name, SkellamDistribution, [mu1, mu2]);
}

/**
 * A heavy-tailed law on positive integers with shape parameter `rho`.
 *
 * @see SymPy `sympy.stats.drv_types.YuleSimonDistribution`
 */
export class YuleSimonDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `YuleSimonDistribution`.
   *
   * @param args - Distribution parameters in the order `rho`.
   */
  constructor(args: readonly Expr[]) {
    super('YuleSimonDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.YuleSimonDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `rho > 0`.
   * @see SymPy `sympy.stats.drv_types.YuleSimonDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'rho should be positive');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.YuleSimonDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const rho = this.arg(0);
    return mul(rho, beta(k, add(rho, 1)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const rho = this.arg(0);
    return piecewise([sub(1, mul(floor(x), beta(floor(x), add(rho, 1)))), Ge(x, 1)], [0, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const rho = this.arg(0);
    return div(mul(rho, hyper([1, 1], [add(rho, 2)], exp(mul(S.I, t))), exp(mul(S.I, t))), add(rho, 1));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const rho = this.arg(0);
    return div(mul(rho, hyper([1, 1], [add(rho, 2)], exp(t)), exp(t)), add(rho, 1));
  }
}

/**
 * Constructs a random variable with the Yule-Simon distribution.
 *
 * @param name - Name of the symbol.
 * @param rho - Positive shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `rho > 0`.
 * @see SymPy `sympy.stats.drv_types.YuleSimon`
 * @example
 * ```ts
 * import { Distribution, YuleSimon, density, ex } from '@symjs/symjs';
 *
 * const X = YuleSimon('x', 5); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 5*beta(z, 6)
 * ```
 */
export function YuleSimon(name: string | Sym, rho: ExprLike): RandomSymbol {
  return rv(name, YuleSimonDistribution, [rho]);
}

/**
 * A positive integer law with probability mass proportional to `k**(-s)`.
 *
 * @see SymPy `sympy.stats.drv_types.ZetaDistribution`
 */
export class ZetaDistribution extends SingleDiscreteDistribution {
  /**
   * Constructs a new `ZetaDistribution`.
   *
   * @param args - Distribution parameters in the order `s`.
   */
  constructor(args: readonly Expr[]) {
    super('ZetaDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv_types.ZetaDistribution.set`
   */
  override get set(): SetExpr {
    return Naturals;
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `s > 1`.
   * @see SymPy `sympy.stats.drv_types.ZetaDistribution.check`
   */
  override check(): void {
    valueCheck(Gt(this.arg(0), 1), 's should be greater than 1');
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   * @see SymPy `sympy.stats.drv_types.ZetaDistribution.pdf`
   */
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const s = this.arg(0);
    return pow(mul(pow(k, s), zeta(s)), -1);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return div(polylog(this.arg(0), exp(mul(S.I, t))), zeta(this.arg(0)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return div(polylog(this.arg(0), exp(t)), zeta(this.arg(0)));
  }
}

/**
 * Constructs a random variable with the Zeta distribution.
 *
 * @param name - Name of the symbol.
 * @param s - Exponent greater than one.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `s > 1`.
 * @see SymPy `sympy.stats.drv_types.Zeta`
 * @example
 * ```ts
 * import { Distribution, Zeta, density, ex } from '@symjs/symjs';
 *
 * const X = Zeta('x', 5); // => x
 * (density(X) as Distribution).pdf(ex`z`); // => 1/(z**5*zeta(5))
 * ```
 */
export function Zeta(name: string | Sym, s: ExprLike): RandomSymbol {
  return rv(name, ZetaDistribution, [s]);
}

statsClasses.discreteHandmade = (pdf) => new DiscreteDistributionHandmade([pdf]);
