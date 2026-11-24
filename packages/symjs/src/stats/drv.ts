// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/drv.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.drv: discrete random variables, whose values are
 * integers (possibly infinitely many): expectations and probabilities are
 * sums of the probability mass function.
 */

import { Dummy, Expr, Rel, S, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, exp, mul, sympify } from '../core/ops';
import { Eq, Ge, Le, piecewise, rel } from '../core/logic';
import { Sum } from '../core/concrete';
import { xreplace } from '../core/traverse';
import { Lambda, LambdaNode } from '../core/lambda';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, first } from '../core/guard';
import type { SetExpr} from '../sets/sets';
import { EmptySet, FiniteSet, Integers, Range, SetOp, contains, inf, intersection, sup } from '../sets/sets';
import { summation } from '../concrete/summations';
import { polyCoefficients } from '../polys/poly';
import { series } from '../series/series';
import { factorial, floor } from '../functions/special/special';
import { doit } from '../calculus/doit';
import { ConditionalDomain, Distribution, PSpace, ProductDomain, RandomDomain, RandomSymbol, SingleDomain, conditionOnSymbols, density, randomSymbols, statsClasses, symbolConverter } from './rv';
import type { ComputeOptions, DensityResult } from './rv';
import { reduceRationalInequalitiesWrap, removeO } from './crv';
import type { ClosedForm } from './crv';

/**
 * Base class for distributions with a countable set of outcomes.
 *
 * @see SymPy `sympy.stats.drv.DiscreteDistribution`
 * @example
 * ```ts
 * import { PoissonDistribution, ex } from '@symjs/symjs';
 *
 * const law = new PoissonDistribution([ex`2`]);
 * law.pdf(0); // => exp(-2)
 * ```
 */
export abstract class DiscreteDistribution extends Distribution {}

/** summation(f, (x, a, b)) over the integers of [a, b]. */
const sum = (f: Expr, x: Sym, a: Expr, b: Expr): Expr => summation(f, [x, a, b]);

/**
 * A distribution on (a subset of) the
 * integers. Subclasses define `pdf` (the probability mass function) and
 * `set`, and may give closed forms of the cdf, characteristic and moment
 * generating functions and quantile.
 *
 * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution`
 */
export abstract class SingleDiscreteDistribution extends DiscreteDistribution {
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.set`
   */
  get set(): SetExpr {
    return Integers;
  }
  /**
   * Checks the parameters.
   *
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.check`
   */
  check(): void {}
  protected cdfClosed(_x: Expr): ClosedForm {
    return undefined;
  }
  protected characteristicFunctionClosed(_t: Expr): ClosedForm {
    return undefined;
  }
  protected momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    return undefined;
  }
  protected quantileClosed(_p: Expr): ClosedForm {
    return undefined;
  }
  /**
   * Sums the mass function up to a variable upper bound.
   *
   * @returns The cumulative distribution function.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.compute_cdf`
   */
  computeCdf(): LambdaNode {
    const x = new Dummy('x', { integer: true });
    const z = new Dummy('z', { real: true });
    const left = inf(this.set);
    const c = sum(this.pdf(x), x, left, floor(z));
    return Lambda(z, piecewise([c, Ge(z, left)], [0, true]));
  }
  /**
   * Evaluates the cumulative distribution at the supplied value.
   *
   * @param xIn - Variable of the expansion.
   * @returns The cumulative probability at the argument.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.cdf`
   */
  cdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return this.cdfClosed(x) ?? this.computeCdf().call(x);
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @returns The characteristic function.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.compute_characteristic_function`
   */
  computeCharacteristicFunction(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    return Lambda(t, sum(mul(exp(mul(S.I, t, x)), this.pdf(x)), x, inf(this.set), sup(this.set)));
  }
  /**
   * Evaluates the characteristic function at the specified argument.
   *
   * @param tIn - Argument of the transform.
   * @returns The transform value at `t`.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.characteristic_function`
   */
  characteristicFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.characteristicFunctionClosed(t) ?? this.computeCharacteristicFunction().call(t);
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @returns The moment generating function.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.compute_moment_generating_function`
   */
  computeMomentGeneratingFunction(): LambdaNode {
    const t = new Dummy('t', { real: true });
    const x = new Dummy('x', { integer: true });
    return Lambda(t, sum(mul(exp(mul(t, x)), this.pdf(x)), x, inf(this.set), sup(this.set)));
  }
  /**
   * Evaluates the moment generating function at the specified argument.
   *
   * @param tIn - Argument of the transform.
   * @returns The exponential moment at `t`.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.moment_generating_function`
   */
  momentGeneratingFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.momentGeneratingFunctionClosed(t) ?? this.computeMomentGeneratingFunction().call(t);
  }
  /**
   * Finds the least outcome whose cumulative probability reaches the requested probability.
   *
   * @returns The quantile function.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.compute_quantile`
   */
  computeQuantile(): LambdaNode {
    const x = new Dummy('x', { integer: true });
    const p = new Dummy('p', { real: true });
    const left = inf(this.set);
    const c = sum(this.pdf(x), x, left, x);
    return Lambda(p, piecewise([x, Le(p, c)]));
  }
  /**
   * Finds the quantile corresponding to the given cumulative probability.
   *
   * @param pIn - Cumulative probability at which to evaluate the quantile.
   * @returns The quantile at `p`.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.quantile`
   */
  quantile(pIn: ExprLike): Expr {
    const p = sympify(pIn);
    return this.quantileClosed(p) ?? this.computeQuantile().call(p);
  }
  /**
   * Computes expectation using moments from the generating function when available and summing otherwise.
   *
   * @param expr - Expression to evaluate.
   * @param v - Symbol distributed according to this law.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expectation expression.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDistribution.expectation`
   */
  expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    const [a, b] = [inf(this.set), sup(this.set)];
    if (opts.evaluate === false) return Sum(mul(expr, this.pdf(v)), [v, a, b]);
    const p = polyCoefficients(expr, v);
    if (p === undefined) return sum(mul(expr, this.pdf(v)), v, a, b);
    const t = new Dummy('t', { real: true });
    const mgf = this.momentGeneratingFunction(t);
    const deg = p.size ? Math.max(...p.keys()) : 0;
    const taylor = defined(polyCoefficients(removeO(series(mgf, t, 0, deg + 1)), t), 'Taylor series');
    const terms: Expr[] = [];
    for (let k = 0; k <= deg; k++) terms.push(mul(p.get(k) ?? S.Zero, taylor.get(k) ?? S.Zero, factorial(k)));
    return add(...terms);
  }
}

/**
 * A domain of countably many possible outcomes.
 *
 * @see SymPy `sympy.stats.drv.DiscreteDomain`
 */
export abstract class DiscreteDomain extends RandomDomain {}

/**
 * The support of a single discrete random variable.
 *
 * @see SymPy `sympy.stats.drv.SingleDiscreteDomain`
 */
export class SingleDiscreteDomain extends SingleDomain {
  /**
   * Constructs a new `SingleDiscreteDomain`.
   *
   * @param args - Operands in the order `symbol`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'SingleDiscreteDomain');
  }
  /**
   * Indicates whether the domain is discrete.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDomain.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.drv.SingleDiscreteDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return contains(this.set, this.symbol);
  }
}

/**
 * The outcomes of a discrete domain that satisfy a condition.
 *
 * @see SymPy `sympy.stats.drv.ConditionalDiscreteDomain`
 */
export class ConditionalDiscreteDomain extends ConditionalDomain {
  /**
   * Constructs a new `ConditionalDiscreteDomain`.
   *
   * @param args - Operands in the order `fulldomain`, `condition`.
   */
  constructor(args: readonly Expr[]) {
    super('ConditionalDiscreteDomain', [at(args, 0), conditionOnSymbols(at(args, 1))]);
  }
  /**
   * Indicates whether the domain is discrete.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.drv.ConditionalDiscreteDomain.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @throws NotImplementedError when the conditional domain is multivariate.
   * @see SymPy `sympy.stats.drv.ConditionalDiscreteDomain.set`
   */
  override get set(): SetExpr {
    if (this.symbols.length > 1) throw new NotImplementedError('Multivariate conditional domains are not yet implemented.');
    return intersection(reduceRationalInequalitiesWrap(this.condition, first(this.symbols)), this.fulldomain.set);
  }
}

/**
 * A probability space defined by a discrete domain and a probability mass function.
 *
 * @see SymPy `sympy.stats.drv.DiscretePSpace`
 */
export class DiscretePSpace extends PSpace {
  /**
   * Constructs a new `DiscretePSpace`.
   *
   * @param args - Operands in the order `domain`, `density`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'DiscretePSpace') {
    super(args, name);
  }
  /**
   * Indicates whether the space is real-valued.
   *
   * @returns `true` for this space.
   * @see SymPy `sympy.stats.drv.DiscretePSpace.is_real`
   */
  override get isReal(): boolean {
    return true;
  }
  /**
   * Indicates whether this probability space is discrete.
   *
   * @returns `true` for this space.
   * @see SymPy `sympy.stats.drv.DiscretePSpace.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.drv.DiscretePSpace.pdf`
   */
  override get pdf(): Expr {
    return cast(this.density, LambdaNode, 'density').call(...this.symbols);
  }
  /**
   * Restricts the domain to the subset satisfying the condition.
   *
   * @param condition - Condition on the random variables.
   * @returns The domain satisfying the condition.
   * @throws NotImplementedError when the condition involves several discrete random variables.
   * @see SymPy `sympy.stats.drv.DiscretePSpace.where`
   */
  override where(condition: Expr): RandomDomain {
    const rvs = randomSymbols(condition);
    if (rvs.length > 1) throw new NotImplementedError('Multivariate discrete random variables are not yet supported.');
    const conditionalDomain = intersection(reduceRationalInequalitiesWrap(condition, first(rvs)), this.domain.set);
    return new SingleDiscreteDomain([first(rvs).symbol, conditionalDomain]);
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param conditionIn - Condition on the random variables.
   * @returns The probability of the event.
   * @see SymPy `sympy.stats.drv.DiscretePSpace.probability`
   */
  override probability(conditionIn: Expr): Expr {
    let condition = conditionIn;
    const complement = condition instanceof Rel && condition.op === 'Ne';
    if (condition instanceof Rel && complement) condition = Eq(condition.lhs, condition.rhs);
    let prob: Expr | undefined;
    let domainSet: SetExpr | undefined;
    try {
      domainSet = this.where(condition).set;
    } catch (e) {
      if (!(e instanceof NotImplementedError)) throw e;
    }
    if (domainSet !== undefined) {
      // (SymPy also tests the condition for False and True, which where() does not accept)
      if (domainSet === EmptySet) return complement ? S.One : S.Zero;
      if (domainSet.key === this.domain.set.key) return complement ? S.Zero : S.One;
      prob = this.evalProb(domainSet);
    } else {
      const r = cast(condition, Rel, 'condition');
      const expr = add(r.lhs, mul(-1, r.rhs));
      const dens = density(expr);
      const dist = dens instanceof DiscreteDistribution ? dens : defined(statsClasses.discreteHandmade, 'drv_types')(cast(dens, Expr));
      const space = new SingleDiscretePSpace([new Dummy('z', { real: true }), dist]);
      prob = space.probability(rel(r.op, space.value, 0));
    }
    const p = prob ?? defined(statsClasses.probabilityNode, 'symbolic_probability')(condition);
    return complement ? add(1, mul(-1, p)) : p;
  }
  /** The probability of a set of values (SymPy eval_prob); undefined for a set it cannot sum over. */
  protected evalProb(domain: SetExpr): Expr | undefined {
    const sym = first(this.symbols);
    if (domain instanceof Range) {
      const n = new Sym('n', { integer: true });
      const [lo, hi, step] = domain.args.map((a) => a);
      const summand = xreplace(this.pdf, [[sym, mul(n, defined(step))]]);
      return doit(sum(summand, n, mul(defined(lo), defined(step).pow(-1)), add(mul(defined(hi), defined(step).pow(-1)), -1)));
    }
    if (domain instanceof FiniteSet) {
      const pdf = Lambda(sym, this.pdf);
      return add(...domain.args.map((x) => pdf.call(x)));
    }
    if (domain instanceof SetOp && domain.op === 'Union') {
      return add(...domain.args.map((x) => defined(this.evalProb(x), 'probability of a part')));
    }
    return undefined;
  }
  /**
   * Restricts the probability space to outcomes that satisfy the condition.
   *
   * @param conditionIn - Condition on the random variables.
   * @returns The conditioned probability space.
   * @see SymPy `sympy.stats.drv.DiscretePSpace.conditional_space`
   */
  override conditionalSpace(conditionIn: Expr): PSpace {
    const densityL = Lambda(this.symbols, mul(this.pdf, this.probability(conditionIn).pow(-1)));
    const condition = xreplace(conditionIn, this.values.map((rv) => [rv, rv.symbol] as const));
    const domain = new ConditionalDiscreteDomain([this.domain, condition]);
    return new DiscretePSpace([domain, densityL]);
  }
}

/**
 * The Cartesian product of discrete domains.
 *
 * @see SymPy `sympy.stats.drv.ProductDiscreteDomain`
 */
export class ProductDiscreteDomain extends ProductDomain {
  /**
   * Constructs a new `ProductDiscreteDomain`.
   *
   * @param args - Operands in the order `domains`.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'ProductDiscreteDomain');
  }
  /**
   * Indicates whether the domain is discrete.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.drv.ProductDiscreteDomain.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
}

/**
 * A discrete random variable with a distribution.
 *
 * @see SymPy `sympy.stats.drv.SingleDiscretePSpace`
 */
export class SingleDiscretePSpace extends DiscretePSpace {
  /**
   * Constructs a new `SingleDiscretePSpace`.
   *
   * @param args - Operands in the order `s`, `distribution`.
   */
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution')], 'SingleDiscretePSpace');
  }
  /**
   * Checks whether the probability space governs a single random variable.
   *
   * @returns `true` for this space.
   */
  override get isSingle(): boolean {
    return true;
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the law of the random variable in this space.
   *
   * @returns The distribution object.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.distribution`
   */
  get distribution(): SingleDiscreteDistribution {
    return cast(at(this.args, 1), SingleDiscreteDistribution);
  }
  /**
   * Constructs the random symbol associated with this probability space.
   *
   * @returns The space's random variable.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.value`
   */
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.pdf`
   */
  override get pdf(): Expr {
    return this.distribution.pdf(this.symbol);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.set`
   */
  get set(): SetExpr {
    return this.distribution.set;
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.domain`
   */
  override get domain(): RandomDomain {
    return new SingleDiscreteDomain([this.symbol, this.set]);
  }
  /**
   * Expresses the density on the underlying probability space.
   *
   * @returns The density expression.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.density`
   */
  override get density(): Expr {
    return this.distribution;
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvsIn - Random variables to integrate or sum over.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value over the selected variables.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[], opts: ComputeOptions = {}): Expr {
    const rvs = rvsIn?.length ? rvsIn : [this.value];
    if (!rvs.some((rv) => rv.key === this.value.key)) return exprIn;
    const expr = xreplace(sympify(exprIn), rvs.map((rv) => [rv, rv.symbol] as const));
    const x = this.value.symbol;
    try {
      return this.distribution.expectation(expr, x, { evaluate: opts.evaluate ?? true });
    } catch (e) {
      if (!(e instanceof NotImplementedError)) throw e;
      return Sum(mul(expr, this.pdf), [x, inf(this.set), sup(this.set)]);
    }
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The cumulative distribution function.
   * @throws NotImplementedError when the expression is an unsupported transformation of the discrete variable.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.compute_cdf`
   */
  override computeCdf(expr: Expr): DensityResult {
    if (expr.key !== this.value.key) throw new NotImplementedError('cdf of a function of a discrete random variable');
    const x = new Dummy('x', { real: true });
    return Lambda(x, this.distribution.cdf(x));
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @throws NotImplementedError when the expression is an unsupported transformation of the discrete variable.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.compute_density`
   */
  override computeDensity(expr: Expr): DensityResult {
    if (expr.key === this.value.key) return this.distribution;
    throw new NotImplementedError('density of a function of a discrete random variable');
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The characteristic function.
   * @throws NotImplementedError when the expression is an unsupported transformation of the discrete variable.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.compute_characteristic_function`
   */
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) throw new NotImplementedError('characteristic function of a function of a discrete random variable');
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.characteristicFunction(t));
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param expr - Expression to evaluate.
   * @returns The moment generating function.
   * @throws NotImplementedError when the expression is an unsupported transformation of the discrete variable.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.compute_moment_generating_function`
   */
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) throw new NotImplementedError('moment generating function of a function of a discrete random variable');
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.momentGeneratingFunction(t));
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The quantile function.
   * @throws NotImplementedError when the expression is an unsupported transformation of the discrete variable.
   * @see SymPy `sympy.stats.drv.SingleDiscretePSpace.compute_quantile`
   */
  override computeQuantile(expr: Expr): Expr {
    if (expr.key !== this.value.key) throw new NotImplementedError('quantile of a function of a discrete random variable');
    const p = new Dummy('p', { real: true });
    return Lambda(p, this.distribution.quantile(p));
  }
}

statsClasses.discreteConditional = (domain, condition) => new ConditionalDiscreteDomain([domain, condition]);
statsClasses.discretePSpace = (domain, d) => new DiscretePSpace([domain, d]);
statsClasses.discreteSingle = (z, dist) => new SingleDiscretePSpace([z, dist]);
statsClasses.productDiscreteDomain = (domains) => new ProductDiscreteDomain(domains);
