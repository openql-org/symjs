// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/frv_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.frv_types: the finite distributions and the
 * functions that create random symbols with them (`Die('D', 6)`,
 * `Coin('C')`, `Binomial('X', n, p)`, ...).
 */

import { Dummy, Float, Rational, S, Sym, asRational } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, Lt, piecewise } from '../core/logic';
import { and, or } from '../core/boolalg';
import { Lambda } from '../core/lambda';
import { DictNode, Dict } from '../core/containers';
import { isIntegerQ as isIntegerValued, isNonNegative, isPositive } from '../core/assumptions';
import { at, cast, defined } from '../core/guard';
import type { SetExpr} from '../sets/sets';
import { FiniteSet, Integers, Naturals0, contains, finiteSet, intersection, interval } from '../sets/sets';
import { log } from '../functions/elementary/elementary';
import { beta as betaFn, binomial } from '../functions/special/special';
import { FiniteDensity, isRandom, statsClasses, valueCheck } from './rv';
import type { DensityResult , RandomSymbol} from './rv';
import { Density } from './rv';
import { SingleFiniteDistribution, SingleFinitePSpace } from './frv';
import type { RVOptions } from './crvtypes';

/** A finite distribution class (constructed from its parameters). */
type DistributionClass = new (args: readonly Expr[]) => SingleFiniteDistribution;

/** A random symbol with the distribution of the parameters (SymPy rv of frv_types). */
export function rv(name: string | Sym, cls: DistributionClass, params: readonly ExprLike[], opts: RVOptions = {}): RandomSymbol {
  const args = params.map(sympify);
  const dist = new cls(args);
  if (opts.check ?? true) dist.check();
  if (args.some((a) => isRandom(a))) return defined(statsClasses.compound, 'compound_rv')(name, dist);
  return new SingleFinitePSpace([typeof name === 'string' ? new Sym(name) : name, dist]).value;
}

/** x is a number, a symbol or a random expression (the argument check of the mass functions). */
function checkPmfArgument(x: Expr): void {
  if (!(x.isNumber || x instanceof Sym || isRandom(x))) {
    throw new RangeError(`'x' expected as an argument of type 'number', 'Symbol', or 'RandomSymbol' not ${x.kind}`);
  }
}

/** An integer value as a SymPy Integer. */
const int = (n: number): Expr => Rational.of(n);

/**
 * A distribution given by its values and probabilities.
 *
 * @see SymPy `sympy.stats.frv_types.FiniteDistributionHandmade`
 * @example
 * ```ts
 * import { FiniteDistributionHandmade, FiniteRV, density, ex } from '@symjs/symjs';
 *
 * const X = FiniteRV('X', [[0, ex`1/4`], [1, ex`3/4`]]);
 * (density(X) as FiniteDistributionHandmade).pmf(1); // => 3/4
 * ```
 */
export class FiniteDistributionHandmade extends SingleFiniteDistribution {
  /**
   * Constructs a new `FiniteDistributionHandmade`.
   *
   * @param args - Operands in the order `dict`.
   */
  constructor(args: readonly Expr[]) {
    super('FiniteDistributionHandmade', [cast(at(args, 0), DictNode, 'density dict')]);
  }
  /**
   * Associates each outcome with its probability mass.
   *
   * @returns The finite density map.
   * @see SymPy `sympy.stats.frv_types.FiniteDistributionHandmade.dict`
   */
  override get dict(): DensityResult {
    return new FiniteDensity(cast(this.arg(0), DictNode).items());
  }
  /**
   * Selects the stored probability for a matching value, using zero outside the finite support.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.FiniteDistributionHandmade.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = new Sym('x');
    const f = Lambda(x, piecewise(...cast(this.arg(0), DictNode).items().map(([k, v]) => [v, Eq(k, x)] as const), [S.Zero, true]));
    return f.call(xIn);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.FiniteDistributionHandmade.set`
   */
  override get set(): SetExpr {
    return finiteSet(...cast(this.arg(0), DictNode).keys());
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when a parameter is known to violate the distribution constraints.
   * @see SymPy `sympy.stats.frv_types.FiniteDistributionHandmade.check`
   */
  override check(): void {
    const items = cast(this.arg(0), DictNode).items();
    for (const [, p] of items) valueCheck([Ge(p, 0), Le(p, 1)], 'Probability at a point must be between 0 and 1.');
    const val = add(...items.map(([, p]) => p));
    valueCheck(Eq(val, 1) !== S.false, 'Total Probability must be 1.');
  }
}

/**
 * Constructs a random variable from the specified finite probability masses, validating them when
 * requested.
 *
 * @param name - Name of the symbol.
 * @param densityIn - Pairs of outcomes and probabilities, or a map from outcomes to their probabilities.
 * @param opts - Set `check` to true to verify normalization.
 * @returns The finite random symbol.
 * @throws RangeError when checking is enabled and the probabilities are invalid or do not sum to one.
 * @see SymPy `sympy.stats.frv_types.FiniteRV`
 * @example
 * ```ts
 * import { FiniteRV, ex, expectation } from '@symjs/symjs';
 *
 * expectation(FiniteRV('X', [[0, ex`1/10`], [1, ex`1/5`], [2, ex`3/10`], [3, ex`2/5`]])); // => 2
 * ```
 */
export function FiniteRV(name: string | Sym, densityIn: ReadonlyMap<ExprLike, ExprLike> | readonly (readonly [ExprLike, ExprLike])[], opts: RVOptions = {}): RandomSymbol {
  return rv(name, FiniteDistributionHandmade, [Dict(densityIn)], { check: opts.check ?? false });
}

/**
 * A finite law that assigns equal mass to each distinct supplied outcome.
 *
 * @see SymPy `sympy.stats.frv_types.DiscreteUniformDistribution`
 * @example
 * ```ts
 * import { DiscreteUniformDistribution, ex } from '@symjs/symjs';
 *
 * const law = new DiscreteUniformDistribution([ex`1`, ex`2`, ex`7`]);
 * law.pmf(7); // => 1/3
 * ```
 */
export class DiscreteUniformDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `DiscreteUniformDistribution`.
   *
   * @param args - The equally likely outcomes, one entry per distinct value.
   */
  constructor(args: readonly Expr[]) {
    super('DiscreteUniformDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the list contains duplicate outcomes.
   * @see SymPy `sympy.stats.frv_types.DiscreteUniformDistribution.check`
   */
  override check(): void {
    const keys = new Set(this.args.map((a) => a.key));
    if (keys.size !== this.args.length) {
      const n = this.args.length;
      const weights = new Map<string, [Expr, number]>();
      for (const a of this.args) weights.set(a.key, [a, (weights.get(a.key)?.[1] ?? 0) + 1]);
      const w = [...weights.values()].map(([k, c]) => `${k.toString()}: ${Rational.of(c, n).toString()}`).join(', ');
      throw new RangeError(`Repeated args detected but set expected. For a distribution having different weights for each item use the following:\nS("FiniteRV('X', {${w}})")`);
    }
  }
  /**
   * Gives the mass assigned to each equally likely outcome.
   *
   * @returns The common probability.
   * @see SymPy `sympy.stats.frv_types.DiscreteUniformDistribution.p`
   */
  get p(): Expr {
    return Rational.of(1, this.args.length);
  }
  /**
   * Associates each outcome with its probability mass.
   *
   * @returns The finite density map.
   * @see SymPy `sympy.stats.frv_types.DiscreteUniformDistribution.dict`
   */
  override get dict(): DensityResult {
    return new FiniteDensity(cast(this.set, FiniteSet).args.map((k) => [k, this.p] as const));
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.DiscreteUniformDistribution.set`
   */
  override get set(): SetExpr {
    return finiteSet(...this.args);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.DiscreteUniformDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return this.args.some((a) => a.key === x.key) ? this.p : S.Zero;
  }
}

/**
 * Constructs a finite random variable assigning equal probability to the supplied outcomes.
 *
 * @param name - Name of the symbol.
 * @param items - Equally likely outcomes.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the list contains duplicate outcomes.
 * @see SymPy `sympy.stats.frv_types.DiscreteUniform`
 * @example
 * ```ts
 * import { DiscreteUniform, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = DiscreteUniform('Y', [0, 1, 2, 3, 4]);
 * (density(X) as SingleFiniteDistribution).dict; // => {0: 1/5, 1: 1/5, 2: 1/5, 3: 1/5, 4: 1/5}
 * ```
 */
export function DiscreteUniform(name: string | Sym, items: readonly ExprLike[]): RandomSymbol {
  return rv(name, DiscreteUniformDistribution, items);
}

/**
 * The uniform law on the faces of a die numbered from one.
 *
 * @see SymPy `sympy.stats.frv_types.DieDistribution`
 * @example
 * ```ts
 * import { DieDistribution, ex } from '@symjs/symjs';
 *
 * const law = new DieDistribution([ex`6`]);
 * law.pmf(2); // => 1/6
 * ```
 */
export class DieDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `DieDistribution`.
   *
   * @param args - Distribution parameters in the order `sides`.
   */
  constructor(args: readonly Expr[]) {
    super('DieDistribution', args);
  }
  /**
   * Counts the faces of the die.
   *
   * @returns The positive number of sides.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.sides`
   */
  get sides(): Expr {
    return this.arg(0);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer number of sides.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.check`
   */
  override check(): void {
    valueCheck([isPositive(this.sides), isIntegerValued(this.sides)], 'number of sides must be a positive integer.');
  }
  /**
   * Indicates whether the distribution depends on symbolic parameters.
   *
   * @returns The symbolic-distribution flag.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.is_symbolic`
   */
  override get isSymbolic(): boolean {
    return !this.sides.isNumber;
  }
  /**
   * Identifies the upper endpoint of the possible outcomes.
   *
   * @returns The largest outcome.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.high`
   */
  override get high(): Expr {
    return this.sides;
  }
  /**
   * Identifies the lower endpoint of the possible outcomes.
   *
   * @returns The smallest outcome.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.low`
   */
  override get low(): Expr {
    return S.One;
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.set`
   */
  override get set(): SetExpr {
    if (this.isSymbolic) return intersection(Naturals0, interval(0, this.sides));
    return finiteSet(...Array.from({ length: Number(asRational(this.sides).p) }, (_, i) => int(i + 1)));
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.DieDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    const cond = and(Ge(x, 1), Le(x, this.sides), contains(Integers, x));
    return piecewise([pow(this.sides, -1), cond], [S.Zero, true]);
  }
}

/**
 * Constructs a fair die with the supplied number of sides.
 *
 * @param name - Name of the symbol.
 * @param sides - Positive integer number of faces.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the number of sides is not a positive integer.
 * @see SymPy `sympy.stats.frv_types.Die`
 * @example
 * ```ts
 * import { Die, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = Die('D4', 4);
 * (density(X) as SingleFiniteDistribution).dict; // => {1: 1/4, 2: 1/4, 3: 1/4, 4: 1/4}
 * ```
 */
export function Die(name: string | Sym, sides: ExprLike = 6): RandomSymbol {
  return rv(name, DieDistribution, [sides]);
}

/**
 * A two-outcome law assigning probability `p` to success.
 *
 * @see SymPy `sympy.stats.frv_types.BernoulliDistribution`
 * @example
 * ```ts
 * import { BernoulliDistribution, ex } from '@symjs/symjs';
 *
 * const law = new BernoulliDistribution([ex`3/4`, ex`1`, ex`0`]);
 * law.pmf(1); // => 3/4
 * ```
 */
export class BernoulliDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `BernoulliDistribution`.
   *
   * @param args - Distribution parameters in the order `p`, `succ`, `fail`.
   */
  constructor(args: readonly Expr[]) {
    super('BernoulliDistribution', args);
  }
  /**
   * Gives the chance that the trial succeeds.
   *
   * @returns The success probability.
   * @see SymPy `sympy.stats.frv_types.BernoulliDistribution.p`
   */
  get p(): Expr {
    return this.arg(0);
  }
  /**
   * Identifies the outcome assigned to a successful trial.
   *
   * @returns The success value.
   * @see SymPy `sympy.stats.frv_types.BernoulliDistribution.succ`
   */
  get succ(): Expr {
    return this.arg(1);
  }
  /**
   * Identifies the outcome assigned to a failed trial.
   *
   * @returns The failure value.
   * @see SymPy `sympy.stats.frv_types.BernoulliDistribution.fail`
   */
  get fail(): Expr {
    return this.arg(2);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters are known to violate `0 <= p <= 1`.
   * @see SymPy `sympy.stats.frv_types.BernoulliDistribution.check`
   */
  override check(): void {
    valueCheck([Ge(this.p, 0), Le(this.p, 1)], 'p should be in range [0, 1].');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.BernoulliDistribution.set`
   */
  override get set(): SetExpr {
    return finiteSet(this.succ, this.fail);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.BernoulliDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    // SymPy compares symbolic outcomes (H and T) structurally: x == succ
    if (this.succ instanceof Sym && this.fail instanceof Sym) {
      return piecewise([this.p, x.key === this.succ.key], [sub(1, this.p), x.key === this.fail.key], [S.Zero, true]);
    }
    return piecewise([this.p, Eq(x, this.succ)], [sub(1, this.p), Eq(x, this.fail)], [S.Zero, true]);
  }
}

/**
 * Constructs a Bernoulli variable with the specified success probability and two outcome values.
 *
 * @param name - Name of the symbol.
 * @param p - Probability of success.
 * @param succ - Value on success.
 * @param fail - Value on failure.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `0 <= p <= 1`.
 * @see SymPy `sympy.stats.frv_types.Bernoulli`
 * @example
 * ```ts
 * import { Bernoulli, SingleFiniteDistribution, density, ex } from '@symjs/symjs';
 *
 * const X = Bernoulli('X', ex`3/4`);
 * (density(X) as SingleFiniteDistribution).dict; // => {0: 1/4, 1: 3/4}
 * ```
 */
export function Bernoulli(name: string | Sym, p: ExprLike, succ: ExprLike | string = 1, fail: ExprLike | string = 0): RandomSymbol {
  return rv(name, BernoulliDistribution, [p, succ, fail].map((v) => (typeof v === 'string' ? new Sym(v) : v)));
}

/**
 * Constructs a coin that gives heads with the specified probability and tails otherwise.
 *
 * @param name - Name of the symbol.
 * @param p - Probability of heads.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters are known to violate `0 <= p <= 1`.
 * @see SymPy `sympy.stats.frv_types.Coin`
 * @remarks SymPy prints the probabilities in the order `{T: 1/2, H: 1/2}`.
 * @example
 * ```ts
 * import { Coin, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = Coin('C');
 * (density(X) as SingleFiniteDistribution).dict; // => {H: 1/2, T: 1/2}
 * ```
 */
export function Coin(name: string | Sym, p: ExprLike = S.Half): RandomSymbol {
  return rv(name, BernoulliDistribution, [p, new Sym('H'), new Sym('T')]);
}

/**
 * The distribution of the total value of independent trials with a common success probability.
 *
 * @see SymPy `sympy.stats.frv_types.BinomialDistribution`
 * @example
 * ```ts
 * import { BinomialDistribution, ex } from '@symjs/symjs';
 *
 * const law = new BinomialDistribution([ex`4`, ex`1/2`, ex`1`, ex`0`]);
 * law.pmf(2); // => 3/8
 * ```
 */
export class BinomialDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `BinomialDistribution`.
   *
   * @param args - Distribution parameters in the order `n`, `p`, `succ`, `fail`.
   */
  constructor(args: readonly Expr[]) {
    super('BinomialDistribution', args);
  }
  /**
   * Gives the chance of success on each independent trial.
   *
   * @returns The per-trial probability.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.p`
   */
  get p(): Expr {
    return this.arg(1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a nonnegative integer trial count and a probability between zero and one inclusive.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.check`
   */
  override check(): void {
    valueCheck([isIntegerValued(this.arg(0)), isNonNegative(this.arg(0))], "'n' must be nonnegative integer.");
    valueCheck([Le(this.p, 1), Ge(this.p, 0)], 'p should be in range [0, 1].');
  }
  /**
   * Identifies the upper endpoint of the possible outcomes.
   *
   * @returns The largest outcome.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.high`
   */
  override get high(): Expr {
    return this.arg(0);
  }
  /**
   * Identifies the lower endpoint of the possible outcomes.
   *
   * @returns The smallest outcome.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.low`
   */
  override get low(): Expr {
    return S.Zero;
  }
  /**
   * Indicates whether the distribution depends on symbolic parameters.
   *
   * @returns The symbolic-distribution flag.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.is_symbolic`
   */
  override get isSymbolic(): boolean {
    return !this.arg(0).isNumber;
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.set`
   */
  override get set(): SetExpr {
    if (this.isSymbolic) return intersection(Naturals0, interval(0, this.arg(0)));
    return finiteSet(...cast(this.dict, FiniteDensity).keys());
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    const [n, p] = [this.arg(0), this.p];
    const cond = and(Ge(x, 0), Le(x, n), contains(Integers, x));
    return piecewise([mul(binomial(n, x), pow(p, x), pow(sub(1, p), sub(n, x))), cond], [S.Zero, true]);
  }
  /**
   * Associates each outcome with its probability mass.
   *
   * @returns The finite density map.
   * @see SymPy `sympy.stats.frv_types.BinomialDistribution.dict`
   */
  override get dict(): DensityResult {
    if (this.isSymbolic) return new Density([this]);
    const [succ, fail] = [this.arg(2), this.arg(3)];
    const n = Number(asRational(this.arg(0)).p);
    return new FiniteDensity(Array.from({ length: n + 1 }, (_, k) => [add(mul(k, succ), mul(n - k, fail)), this.pmf(k)] as const));
  }
}

/**
 * Constructs the distribution of the number of successes in the specified Bernoulli trials.
 *
 * @param name - Name of the symbol.
 * @param n - Nonnegative integer number of trials.
 * @param p - Probability of success on each trial.
 * @param succ - Value of one success.
 * @param fail - Value of one failure.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for a nonnegative integer trial count and a probability between zero and one inclusive.
 * @see SymPy `sympy.stats.frv_types.Binomial`
 * @example
 * ```ts
 * import { Binomial, SingleFiniteDistribution, density, ex } from '@symjs/symjs';
 *
 * const X = Binomial('X', 4, ex`1/2`);
 * (density(X) as SingleFiniteDistribution).dict; // => {0: 1/16, 1: 1/4, 2: 3/8, 3: 1/4, 4: 1/16}
 * ```
 */
export function Binomial(name: string | Sym, n: ExprLike, p: ExprLike, succ: ExprLike = 1, fail: ExprLike = 0): RandomSymbol {
  return rv(name, BinomialDistribution, [n, p, succ, fail]);
}

/**
 * The distribution of a binomial count whose success probability follows a beta law.
 *
 * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution`
 * @example
 * ```ts
 * import { BetaBinomialDistribution, ex } from '@symjs/symjs';
 *
 * const law = new BetaBinomialDistribution([ex`2`, ex`1`, ex`1`]);
 * law.pmf(1); // => 2*beta(2, 2)
 * ```
 */
export class BetaBinomialDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `BetaBinomialDistribution`.
   *
   * @param args - Distribution parameters in the order `n`, `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('BetaBinomialDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a nonnegative integer trial count and positive shape parameters.
   * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution.check`
   */
  override check(): void {
    const [n, alpha, beta] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck([isIntegerValued(n), isNonNegative(n)], `'n' must be nonnegative integer. n = ${n.toString()}.`);
    valueCheck(Gt(alpha, 0), `'alpha' must be: alpha > 0 . alpha = ${alpha.toString()}`);
    valueCheck(Gt(beta, 0), `'beta' must be: beta > 0 . beta = ${beta.toString()}`);
  }
  /**
   * Identifies the upper endpoint of the possible outcomes.
   *
   * @returns The largest outcome.
   * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution.high`
   */
  override get high(): Expr {
    return this.arg(0);
  }
  /**
   * Identifies the lower endpoint of the possible outcomes.
   *
   * @returns The smallest outcome.
   * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution.low`
   */
  override get low(): Expr {
    return S.Zero;
  }
  /**
   * Indicates whether the distribution depends on symbolic parameters.
   *
   * @returns The symbolic-distribution flag.
   * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution.is_symbolic`
   */
  override get isSymbolic(): boolean {
    return !this.arg(0).isNumber;
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution.set`
   */
  override get set(): SetExpr {
    if (this.isSymbolic) return intersection(Naturals0, interval(0, this.arg(0)));
    return finiteSet(...Array.from({ length: Number(asRational(this.arg(0)).p) + 1 }, (_, i) => int(i)));
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.BetaBinomialDistribution.pmf`
   */
  pmf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [n, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(binomial(n, k), betaFn(add(k, a), add(sub(n, k), b)), pow(betaFn(a, b), -1));
  }
}

/**
 * Constructs a random variable with the Beta-binomial distribution.
 *
 * @param name - Name of the symbol.
 * @param n - Number of trials.
 * @param alpha - First beta shape parameter.
 * @param beta - Second beta shape parameter.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for a nonnegative integer trial count and positive shape parameters.
 * @see SymPy `sympy.stats.frv_types.BetaBinomial`
 * @example
 * ```ts
 * import { BetaBinomial, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = BetaBinomial('X', 2, 1, 1);
 * (density(X) as SingleFiniteDistribution).dict; // => {0: 1/3, 1: 2*beta(2, 2), 2: 1/3}
 * ```
 */
export function BetaBinomial(name: string | Sym, n: ExprLike, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, BetaBinomialDistribution, [n, alpha, beta]);
}

/**
 * The number of successes in a fixed-size sample drawn without replacement.
 *
 * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution`
 * @example
 * ```ts
 * import { HypergeometricDistribution, ex } from '@symjs/symjs';
 *
 * const law = new HypergeometricDistribution([ex`10`, ex`5`, ex`3`]);
 * law.pmf(1); // => 5/12
 * ```
 */
export class HypergeometricDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `HypergeometricDistribution`.
   *
   * @param args - Distribution parameters in the order `N`, `m`, `n`.
   */
  constructor(args: readonly Expr[]) {
    super('HypergeometricDistribution', args);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for nonnegative integer population and draw counts.
   * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution.check`
   */
  override check(): void {
    // SymPy check(n, N, m) receives (N, m, n): the names are shifted, the messages follow them
    const [n, N, m] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck([isIntegerValued(N), isNonNegative(N)], `'N' must be nonnegative integer. N = ${N.toString()}.`);
    valueCheck([isIntegerValued(n), isNonNegative(n)], `'n' must be nonnegative integer. n = ${n.toString()}.`);
    valueCheck([isIntegerValued(m), isNonNegative(m)], `'m' must be nonnegative integer. m = ${m.toString()}.`);
  }
  /**
   * Indicates whether the distribution depends on symbolic parameters.
   *
   * @returns The symbolic-distribution flag.
   * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution.is_symbolic`
   */
  override get isSymbolic(): boolean {
    return !this.args.every((x) => x.isNumber);
  }
  /**
   * Identifies the upper endpoint of the possible outcomes.
   *
   * @returns The largest outcome.
   * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution.high`
   */
  override get high(): Expr {
    const [, m, n] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise([n, Lt(n, m) !== S.false], [m, true]);
  }
  /**
   * Identifies the lower endpoint of the possible outcomes.
   *
   * @returns The smallest outcome.
   * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution.low`
   */
  override get low(): Expr {
    const [N, m, n] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise([0, Gt(0, sub(add(n, m), N)) !== S.false], [sub(add(n, m), N), true]);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution.set`
   */
  override get set(): SetExpr {
    const [N, m, n] = [this.arg(0), this.arg(1), this.arg(2)].map((a) => a);
    if (this.isSymbolic) return intersection(Naturals0, interval(this.low, this.high));
    const v = (e: Expr | undefined): number => Number(asRational(defined(e)).p);
    const lo = Math.max(0, v(n) + v(m) - v(N));
    const hi = Math.min(v(n), v(m));
    return finiteSet(...Array.from({ length: Math.max(0, hi - lo + 1) }, (_, i) => int(lo + i)));
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param kIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.HypergeometricDistribution.pmf`
   */
  pmf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [N, m, n] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(binomial(m, k), binomial(sub(N, m), sub(n, k)), pow(binomial(N, n), -1));
  }
}

/**
 * Constructs the distribution of successes in a sample of `n` draws without replacement from `N` items
 * containing `m` successes.
 *
 * @param name - Name of the symbol.
 * @param N - Population size.
 * @param m - Number of successes in the population.
 * @param n - Number of draws without replacement.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for nonnegative integer population and draw counts.
 * @see SymPy `sympy.stats.frv_types.Hypergeometric`
 * @example
 * ```ts
 * import { Hypergeometric, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = Hypergeometric('X', 10, 5, 3);
 * (density(X) as SingleFiniteDistribution).dict; // => {0: 1/12, 1: 5/12, 2: 5/12, 3: 1/12}
 * ```
 */
export function Hypergeometric(name: string | Sym, N: ExprLike, m: ExprLike, n: ExprLike): RandomSymbol {
  return rv(name, HypergeometricDistribution, [N, m, n]);
}

/**
 * The law placing probability one half on each of `-1` and `1`.
 *
 * @see SymPy `sympy.stats.frv_types.RademacherDistribution`
 * @example
 * ```ts
 * import { RademacherDistribution } from '@symjs/symjs';
 *
 * const law = new RademacherDistribution([]);
 * law.pmf(-1); // => 1/2
 * ```
 */
export class RademacherDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `RademacherDistribution`.
   *
   * @param args - Empty parameter list.
   */
  constructor(args: readonly Expr[] = []) {
    super('RademacherDistribution', args);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.RademacherDistribution.set`
   */
  override get set(): SetExpr {
    return finiteSet(-1, 1);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.RademacherDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const k = new Dummy('k');
    return Lambda(k, piecewise([S.Half, or(Eq(k, -1), Eq(k, 1))], [S.Zero, true])).call(xIn);
  }
}

/**
 * Constructs a random variable with the Rademacher distribution.
 *
 * @param name - Name of the symbol.
 * @returns The random symbol with the specified law.
 * @see SymPy `sympy.stats.frv_types.Rademacher`
 * @remarks SymPy prints the probabilities in the order `{1: 1/2, -1: 1/2}`.
 * @example
 * ```ts
 * import { Rademacher, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = Rademacher('X');
 * (density(X) as SingleFiniteDistribution).dict; // => {-1: 1/2, 1: 1/2}
 * ```
 */
export function Rademacher(name: string | Sym): RandomSymbol {
  return rv(name, RademacherDistribution, []);
}

/** Python `a and b` of three-valued SymPy assumptions (None is falsy). */
const pyAnd = (a: boolean | undefined, b: boolean | undefined): boolean | undefined => (a === true ? b : a);

/**
 * The ideal soliton degree distribution for a fixed number of source blocks.
 *
 * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution`
 * @example
 * ```ts
 * import { IdealSolitonDistribution, ex } from '@symjs/symjs';
 *
 * const law = new IdealSolitonDistribution([ex`5`]);
 * law.pmf(2); // => 1/2
 * ```
 */
export class IdealSolitonDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `IdealSolitonDistribution`.
   *
   * @param args - Distribution parameters in the order `k`.
   */
  constructor(args: readonly Expr[]) {
    super('IdealSolitonDistribution', args);
  }
  /**
   * Specifies how many source blocks the soliton distribution covers.
   *
   * @returns The source block count.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.k`
   */
  get k(): Expr {
    return this.arg(0);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer block count.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.check`
   */
  override check(): void {
    const k = this.k;
    valueCheck(pyAnd(isIntegerValued(k), isPositive(k)), "'k' must be a positive integer.");
  }
  /**
   * Identifies the lower endpoint of the possible outcomes.
   *
   * @returns The smallest outcome.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.low`
   */
  override get low(): Expr {
    return S.One;
  }
  /**
   * Identifies the upper endpoint of the possible outcomes.
   *
   * @returns The largest outcome.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.high`
   */
  override get high(): Expr {
    return this.k;
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.set`
   */
  override get set(): SetExpr {
    return finiteSet(...Array.from({ length: Number(asRational(this.k).p) }, (_, i) => int(i + 1)));
  }
  /**
   * Associates each outcome with its probability mass.
   *
   * @returns The finite density map.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.dict`
   */
  override get dict(): DensityResult {
    if (this.k instanceof Sym) return new Density([this]);
    const k = Number(asRational(this.k).p);
    const entries: (readonly [Expr, Expr])[] = [[S.One, Rational.of(1, k)]];
    for (let i = 2; i <= k; i++) entries.push([int(i), Rational.of(1, i * (i - 1))]);
    return new FiniteDensity(entries);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.IdealSolitonDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    return idealRho(x, this.k);
  }
}

/** Python `relational & x.is_integer` (SymPy raises a TypeError for None). */
function andBool(rel: Expr, b: boolean | undefined): Expr {
  if (b === undefined) throw new TypeError("unsupported operand type(s) for &: 'Equality' and 'NoneType'");
  return and(rel, b ? S.true : S.false);
}

/** The ideal soliton mass function at x (SymPy rho). */
function idealRho(x: Expr, k: Expr): Expr {
  const isInt = isIntegerValued(x);
  const cond1 = andBool(Eq(x, 1), isInt);
  const cond2 = andBool(and(Ge(x, 1), Le(x, k)), isInt);
  return piecewise([pow(k, -1), cond1], [pow(mul(x, sub(x, 1)), -1), cond2], [S.Zero, true]);
}

/**
 * Constructs a random variable with the ideal soliton distribution.
 *
 * @param name - Name of the symbol.
 * @param k - Number of source blocks.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for a positive integer block count.
 * @see SymPy `sympy.stats.frv_types.IdealSoliton`
 * @example
 * ```ts
 * import { IdealSoliton, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = IdealSoliton('sol', 5);
 * (density(X) as SingleFiniteDistribution).dict; // => {1: 1/5, 2: 1/2, 3: 1/6, 4: 1/12, 5: 1/20}
 * ```
 */
export function IdealSoliton(name: string | Sym, k: ExprLike): RandomSymbol {
  return rv(name, IdealSolitonDistribution, [k]);
}

/**
 * A soliton degree distribution with an additional weight determined by the block count and decoding failure probability.
 *
 * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution`
 * @example
 * ```ts
 * import { RobustSolitonDistribution, ex } from '@symjs/symjs';
 *
 * const law = new RobustSolitonDistribution([ex`5`, ex`1/2`, ex`1/100`]);
 * law.pmf(2); // => (0.00223606797749979*log(10) + 1/2)/(0.00447213595499958*(log(0.0447213595499958*log(10)) + 3699322246041458103739317199996707235031/718766754945489455304472257065075294400)*log(10) + 1)
 * ```
 */
export class RobustSolitonDistribution extends SingleFiniteDistribution {
  /**
   * Constructs a new `RobustSolitonDistribution`.
   *
   * @param args - Distribution parameters in the order `k`, `delta`, `c`.
   */
  constructor(args: readonly Expr[]) {
    super('RobustSolitonDistribution', args);
  }
  /**
   * Specifies how many source blocks the soliton distribution covers.
   *
   * @returns The source block count.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.k`
   */
  get k(): Expr {
    return this.arg(0);
  }
  /**
   * Specifies the permitted probability of decoding failure.
   *
   * @returns The failure tolerance.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.delta`
   */
  get delta(): Expr {
    return this.arg(1);
  }
  /**
   * Sets the positive scale of the robust soliton distribution.
   *
   * @returns The scale parameter.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.c`
   */
  get c(): Expr {
    return this.arg(2);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer block count, a failure probability strictly between zero and one, and a positive scaling constant.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.check`
   */
  override check(): void {
    const { k, delta, c } = this;
    valueCheck(pyAnd(isIntegerValued(k), isPositive(k)), "'k' must be a positive integer");
    valueCheck(and(Gt(delta, 0), Le(delta, 1)), "'delta' must be a real number in the interval (0,1)");
    valueCheck(isPositive(c), "'c' must be a positive real number.");
  }
  /**
   * Computes the cutoff `c*log(k/delta)*sqrt(k)` for the robust soliton distribution.
   *
   * @returns The cutoff parameter.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.R`
   */
  get R(): Expr {
    return mul(this.c, log(mul(this.k, pow(this.delta, -1))), pow(this.k, new Float(0.5)));
  }
  /**
   * Computes the factor normalizing the robust soliton probabilities.
   *
   * @returns The normalization constant.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.Z`
   */
  get Z(): Expr {
    let z: Expr = S.Zero;
    const top = pyRound(mul(this.k, pow(this.R, -1)));
    for (let i = 1; i < top; i++) z = add(z, Rational.of(1, i));
    z = add(z, log(mul(this.R, pow(this.delta, -1))));
    return add(1, mul(z, this.R, pow(this.k, -1)));
  }
  /**
   * Identifies the lower endpoint of the possible outcomes.
   *
   * @returns The smallest outcome.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.low`
   */
  override get low(): Expr {
    return S.One;
  }
  /**
   * Identifies the upper endpoint of the possible outcomes.
   *
   * @returns The largest outcome.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.high`
   */
  override get high(): Expr {
    return this.k;
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.set`
   */
  override get set(): SetExpr {
    return finiteSet(...Array.from({ length: Number(asRational(this.k).p) }, (_, i) => int(i + 1)));
  }
  /**
   * Indicates whether the distribution depends on symbolic parameters.
   *
   * @returns The symbolic-distribution flag.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.is_symbolic`
   */
  override get isSymbolic(): boolean {
    return !(this.k.isNumber && this.c.isNumber && this.delta.isNumber);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param xIn - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv_types.RobustSolitonDistribution.pmf`
   */
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    const { k, R, delta } = this;
    const rho = idealRho(x, k);
    const top = pyRound(mul(k, pow(R, -1)));
    const c1 = and(Ge(x, 1), Le(x, top - 1));
    const c2 = Eq(x, top);
    const tau = piecewise([mul(R, pow(mul(k, x), -1)), c1], [mul(R, log(mul(R, pow(delta, -1))), pow(k, -1)), c2], [S.Zero, true]);
    return mul(add(rho, tau), pow(this.Z, -1));
  }
}

/** Python round() of a number (to nearest, ties to even). */
export function pyRound(e: Expr): number {
  const v = e.evalf().toNumber();
  const r = Math.round(v);
  return Math.abs(v - Math.trunc(v)) === 0.5 && r % 2 !== 0 ? r - 1 : r;
}

/**
 * Constructs a random variable with the robust soliton distribution.
 *
 * @param name - Name of the symbol.
 * @param k - Number of source blocks.
 * @param delta - Allowed decoding failure probability.
 * @param c - Positive scaling constant.
 * @returns The random symbol with this distribution.
 * @throws RangeError when the parameters fail the requirement for a positive integer block count, a failure probability strictly between zero and one, and a positive scaling constant.
 * @see SymPy `sympy.stats.frv_types.RobustSoliton`
 * @example
 * ```ts
 * import { RobustSoliton, SingleFiniteDistribution, density } from '@symjs/symjs';
 *
 * const X = RobustSoliton('robSol', 5, 0.5, 0.01);
 * (density(X) as SingleFiniteDistribution).dict; // => {1: 0.204253668152708, 2: 0.490631107897393, 3: 0.165210624506162, 4: 0.0834387731899302, 5: 0.0505633404760675}
 * ```
 */
export function RobustSoliton(name: string | Sym, k: ExprLike, delta: ExprLike, c: ExprLike): RandomSymbol {
  return rv(name, RobustSolitonDistribution, [k, delta, c]);
}

