// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/rv.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.rv: random symbols, probability spaces, random
 * domains and distributions, and the probability machinery built on them
 * (P, E, density, given, where, cdf, characteristic and moment generating
 * functions, quantile, dependence).
 *
 * A random symbol is a symbol (`Sym`) that carries its probability space,
 * so it can be differentiated, solved for and printed like any symbol (its
 * str form is its name, as in SymPy). Probability spaces, domains and
 * distributions are expression nodes (SymPy Basic): their arguments define
 * them, so substitution, structural equality and printing work as for any
 * other expression.
 *
 * The modules of the continuous, discrete and finite spaces, the compound
 * distributions and the symbolic probability nodes register their classes
 * in `statsClasses` when they are loaded (SymPy imports them locally to
 * avoid import cycles).
 */

import { BoolAtom, Dummy, Expr, ExtensionExpr, Rel, S, Sym, UndefFn } from '../core/nodes';
import type { Assumptions, ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { Eq, rel } from '../core/logic';
import { BoolOp, and } from '../core/boolalg';
import { xreplace } from '../core/traverse';
import { ordered } from '../core/match';
import { Lambda } from '../core/lambda';
import { TupleNode } from '../core/containers';
import { Indexed } from '../core/indexed';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, first } from '../core/guard';
import type { Truth } from '../core/truth';
import { FiniteSet, SetExpr, productSet } from '../sets/sets';
import { solveset } from '../solvers/inequalities';
import { DiracDelta } from '../integrals/transforms/delta';
import { KroneckerDelta } from '../functions/special/hyper';
import { doit } from '../calculus/doit';
import { MatrixExpr, MatrixSymbolNode, hasNode } from '../matrices/expressions/matexpr';
import { Matrix } from '../matrices/matrix';

/** The global symbol x of sympy/stats/rv.py (the variable of the density of a constant). */
const xGlobal = new Sym('x');

/**
 * Tests whether a value is a random symbol or contains one.
 *
 * @param x - Value to inspect for random symbols.
 * @returns Whether the value contains or is a random symbol.
 * @see SymPy `sympy.stats.rv.is_random`
 */
export function isRandom(x: unknown): boolean {
  if (x instanceof RandomSymbol || x instanceof RandomMatrixSymbol) return true;
  if (!(x instanceof Expr)) return false;
  return [...x.freeSymbols()].filter((s) => s instanceof Sym).some((s) => s instanceof RandomSymbol) || hasNode(x, (e) => e instanceof RandomMatrixSymbol);
}

/**
 * A map from outcomes to their probabilities. Structurally equal expressions refer to the same outcome.
 *
 * @see SymPy `sympy.stats.frv.FiniteDensity`
 * @example
 * ```ts
 * import { Die, DieDistribution, FiniteDensity, density } from '@symjs/symjs';
 *
 * const X = Die('X', 4);
 * const masses = (density(X) as DieDistribution).dict as FiniteDensity;
 * masses.call(2); // => 1/4
 * masses.call(5); // => 0
 * ```
 */
export class FiniteDensity extends Map<Expr, Expr> {
  readonly #byKey = new Map<string, Expr>();
  /**
   * Constructs a new `FiniteDensity`.
   *
   * @param entries - Outcome and probability pairs.
   */
  constructor(entries: Iterable<readonly [Expr, Expr]> = []) {
    super();
    for (const [k, v] of entries) this.set(k, v);
  }
  /**
   * Associates an outcome with its probability mass.
   *
   * @param k - Outcome at which to evaluate the probability mass.
   * @param v - Probability assigned to the outcome.
   * @returns This map.
   */
  override set(k: Expr, v: Expr): this {
    const c = this.#byKey.get(k.key);
    if (c !== undefined) return super.set(c, v);
    this.#byKey.set(k.key, k);
    return super.set(k, v);
  }
  /**
   * Looks up an outcome by structural equality using the standard map lookup contract.
   *
   * @param k - Outcome at which to evaluate the probability mass.
   * @returns The stored mass if the outcome is present.
   */
  override get(k: Expr): Expr | undefined {
    const c = this.#byKey.get(k.key);
    return c === undefined ? undefined : super.get(c);
  }
  /**
   * Tests whether a structurally equal outcome has a stored mass.
   *
   * @param k - Outcome at which to evaluate the probability mass.
   * @returns Whether the map contains the outcome.
   */
  override has(k: Expr): boolean {
    return this.#byKey.has(k.key);
  }
  /**
   * Looks up the probability mass at a value, assigning zero outside the support.
   *
   * @param item - Outcome at which to look up the mass.
   * @returns The mass at this outcome, or zero if absent.
   * @see SymPy `sympy.stats.frv.FiniteDensity.__call__`
   */
  call(item: ExprLike): Expr {
    return this.get(sympify(item)) ?? S.Zero;
  }
  /**
   * Copies the probabilities indexed by outcome.
   *
   * @returns An independent probability map.
   * @see SymPy `sympy.stats.frv.FiniteDensity.dict`
   */
  get dict(): FiniteDensity {
    return new FiniteDensity(this);
  }
}

/**
 * A vector or matrix parameter of a joint or matrix distribution: an
 * explicit matrix, a matrix expression, nested arrays (the rows) or a flat
 * array (a column vector), as SymPy's lists and matrices.
 */
export type MatrixParam = Matrix | MatrixExpr | readonly ExprLike[] | readonly (readonly ExprLike[])[];

/** The value is a vector or matrix parameter (SymPy isinstance(v, list) or v.is_Matrix). */
export const isMatrixParam = (v: unknown): v is MatrixParam => Array.isArray(v) || v instanceof Matrix || v instanceof MatrixExpr;

/** A distribution, a lambda expression, an outcome-to-mass map, or an unevaluated density. */
export type DensityResult = Expr | FiniteDensity;

// ---------------------------------------------------------------------------
// Class registry of the higher modules (SymPy imports them locally)
// ---------------------------------------------------------------------------

/** The constructors of the spaces of the other stats modules, registered when they are loaded. */
export const statsClasses: {
  /** sympy.stats.frv.ProductFinitePSpace(*spaces). */
  productFinitePSpace?: (spaces: readonly PSpace[]) => PSpace;
  /** ProductFiniteDomain, ProductContinuousDomain and ProductDiscreteDomain(*domains). */
  productFiniteDomain?: (domains: readonly RandomDomain[]) => RandomDomain;
  productContinuousDomain?: (domains: readonly RandomDomain[]) => RandomDomain;
  productDiscreteDomain?: (domains: readonly RandomDomain[]) => RandomDomain;
  /** sympy.stats.symbolic_probability.Probability(condition), unevaluated. */
  probabilityNode?: (condition: Expr) => Expr;
  /** sympy.stats.crv_types.ContinuousDistributionHandmade(pdf, set). */
  continuousHandmade?: (pdf: Expr, set?: SetExpr) => Distribution;
  /** SingleContinuousPSpace(z, distribution). */
  continuousSingle?: (z: Sym, dist: Distribution) => PSpace & SingleSpace;
  /** sympy.stats.drv_types.DiscreteDistributionHandmade(pdf, set). */
  discreteHandmade?: (pdf: Expr, set?: SetExpr) => Distribution;
  /** SingleDiscretePSpace(z, distribution). */
  discreteSingle?: (z: Sym, dist: Distribution) => PSpace & SingleSpace;
  /** ContinuousPSpace(ConditionalContinuousDomain(domain, condition), density). */
  continuousConditional?: (domain: RandomDomain, condition: Expr) => RandomDomain;
  continuousPSpace?: (domain: RandomDomain, density: Expr) => PSpace;
  /** DiscretePSpace(ConditionalDiscreteDomain(domain, condition), density). */
  discreteConditional?: (domain: RandomDomain, condition: Expr) => RandomDomain;
  discretePSpace?: (domain: RandomDomain, density: Expr) => PSpace;
  /** FinitePSpace.conditional_space(space, condition). */
  finiteConditionalSpace?: (space: PSpace, condition: Expr) => PSpace;
  /** CompoundPSpace(symbol, CompoundDistribution(dist)).value (sympy.stats.compound_rv). */
  compound?: (symbol: string | Sym, dist: Distribution) => RandomSymbol;
  /** sympy.stats.symbolic_probability.Expectation(expr, condition).doit(evaluate=...). */
  expectation?: (expr: Expr, condition: Expr | undefined, evaluate: boolean) => Expr;
  /** sympy.stats.symbolic_probability.Probability(condition, given).doit(evaluate=...). */
  probability?: (condition: Expr, given: Expr | undefined, evaluate: boolean) => Expr;
  /** ExpectationMatrix, VarianceMatrix and CrossCovarianceMatrix (sympy.stats.symbolic_multivariate_probability). */
  expectationMatrix?: (expr: Expr, condition: Expr | undefined) => Expr;
  varianceMatrix?: (arg: Expr, condition: Expr | undefined) => Expr;
  crossCovarianceMatrix?: (arg1: Expr, arg2: Expr, condition: Expr | undefined) => Expr;
  /** MultivariateNormal and MultivariateLaplace (sympy.stats.joint_rv_types), for Normal and Laplace with matrix parameters. */
  multivariateNormal?: (name: string | Sym, mu: MatrixParam, sigma: MatrixParam) => RandomSymbol;
  multivariateLaplace?: (name: string | Sym, mu: MatrixParam, sigma: MatrixParam) => RandomSymbol;
} = {};

// ---------------------------------------------------------------------------
// Random domains
// ---------------------------------------------------------------------------

/**
 * A set of variables and the values they can take.
 *
 * @see SymPy `sympy.stats.rv.RandomDomain`
 */
export abstract class RandomDomain extends ExtensionExpr {
  /**
   * Checks whether the domain is a product of domains.
   *
   * @returns `false` for this domain.
   * @see SymPy `sympy.stats.rv.RandomDomain.is_ProductDomain`
   */
  get isProductDomain(): boolean {
    return false;
  }
  /**
   * Indicates whether the outcome domain is finite.
   *
   * @returns `false` for this domain.
   * @see SymPy `sympy.stats.rv.RandomDomain.is_Finite`
   */
  get isFinite(): boolean {
    return false;
  }
  /**
   * Indicates whether the outcome domain is continuous.
   *
   * @returns `false` for this domain.
   * @see SymPy `sympy.stats.rv.RandomDomain.is_Continuous`
   */
  get isContinuous(): boolean {
    return false;
  }
  /**
   * Indicates whether the domain is discrete.
   *
   * @returns `false` for this domain.
   * @see SymPy `sympy.stats.rv.RandomDomain.is_Discrete`
   */
  get isDiscrete(): boolean {
    return false;
  }
  /**
   * Indicates whether an event restricts this domain.
   *
   * @returns `false` for this domain.
   */
  get isConditional(): boolean {
    return false;
  }
  /**
   * Lists the variables of the domain in sorted order.
   *
   * @returns The variables of the domain.
   * @see SymPy `sympy.stats.rv.RandomDomain.symbols`
   */
  abstract get symbols(): Sym[];
  /**
   * Specifies the possible values of the domain variables.
   *
   * @returns The outcome set.
   * @see SymPy `sympy.stats.rv.RandomDomain.set`
   */
  abstract get set(): SetExpr;
  /**
   * Translates the domain restrictions into a predicate on its variables.
   *
   * @returns A Boolean expression.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  asBoolean(): Expr {
    throw new NotImplementedError(`as_boolean is not implemented for ${this.name}`);
  }
  /**
   * Computes the expectation of the expression over the domain.
   *
   * @param _expr - Expression to evaluate.
   * @param _variables - Variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   * @see SymPy `sympy.stats.rv.RandomDomain.compute_expectation`
   */
  computeExpectation(_expr: Expr, _variables?: readonly Sym[]): Expr {
    throw new NotImplementedError(`compute_expectation is not implemented for ${this.name}`);
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @param print - Printer used for the component expressions.
   * @returns A plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    // SymPy _print_RandomDomain: the condition, or the variables and their set
    if (this.hasBoolean) return `Domain: ${print(this.asBoolean())}`;
    return `Domain: {${this.symbols.map(print).join(', ')}} in ${print(this.set)}`;
  }
  /**
   * Checks whether the domain can express membership by a Boolean condition.
   *
   * @returns `true` for this domain.
   */
  get hasBoolean(): boolean {
    return true;
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
}

/**
 * A single variable and its domain.
 *
 * @see SymPy `sympy.stats.rv.SingleDomain`
 */
export class SingleDomain extends RandomDomain {
  /**
   * Constructs a new `SingleDomain`.
   *
   * @param args - Operands in the order `symbol`, `set`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'SingleDomain') {
    super(name, args);
    cast(at(args, 0), Sym, 'domain symbol');
    cast(at(args, 1), SetExpr, 'domain set');
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.rv.SingleDomain.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.rv.SingleDomain.symbols`
   */
  get symbols(): Sym[] {
    return [this.symbol];
  }
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @see SymPy `sympy.stats.rv.SingleDomain.set`
   */
  get set(): SetExpr {
    return cast(at(this.args, 1), SetExpr);
  }
  /**
   * Indicates whether the domain supplies a Boolean membership predicate.
   *
   * @returns False for a plain single domain.
   */
  override get hasBoolean(): boolean {
    return this.name !== 'SingleDomain';
  }
}

/**
 * A random matrix variable and its domain.
 *
 * @see SymPy `sympy.stats.rv.MatrixDomain`
 */
export class MatrixDomain extends RandomDomain {
  /**
   * Constructs a new `MatrixDomain`.
   *
   * @param args - Operands in the order `symbol`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super('MatrixDomain', [symbolConverter(at(args, 0)), at(args, 1)]);
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.rv.MatrixDomain.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.rv.MatrixDomain.symbols`
   */
  get symbols(): Sym[] {
    return [this.symbol];
  }
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @see SymPy `sympy.stats.rv.MatrixDomain.set`
   */
  get set(): SetExpr {
    return cast(at(this.args, 1), SetExpr, 'domain set');
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @param print - Printer used for the component expressions.
   * @returns A plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    return `Domain: {${print(this.symbol)}} in ${print(this.set)}`;
  }
}

/**
 * A domain with an attached condition.
 *
 * @see SymPy `sympy.stats.rv.ConditionalDomain`
 */
export abstract class ConditionalDomain extends RandomDomain {
  /**
   * Tests whether the domain is restricted by a condition.
   *
   * @returns `true` for this domain.
   */
  override get isConditional(): boolean {
    return true;
  }
  /**
   * Identifies the original domain before imposing the event.
   *
   * @returns The unconditioned domain.
   * @see SymPy `sympy.stats.rv.ConditionalDomain.fulldomain`
   */
  get fulldomain(): RandomDomain {
    return cast(at(this.args, 0), RandomDomain);
  }
  /**
   * Identifies the event used to restrict the domain or computation.
   *
   * @returns The conditioning expression, when present.
   * @see SymPy `sympy.stats.rv.ConditionalDomain.condition`
   */
  get condition(): Expr {
    return at(this.args, 1);
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.rv.ConditionalDomain.symbols`
   */
  get symbols(): Sym[] {
    return this.fulldomain.symbols;
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.rv.ConditionalDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return and(this.fulldomain.asBoolean(), this.condition);
  }
}

/** The condition with its random symbols replaced by their symbols (SymPy ConditionalDomain.__new__). */
export function conditionOnSymbols(condition: Expr): Expr {
  return xreplace(condition, randomSymbols(condition).map((rs) => [rs, rs.symbol] as const));
}

/**
 * A domain resulting from the merger of independent domains.
 *
 * @see SymPy `sympy.stats.rv.ProductDomain`
 */
export class ProductDomain extends RandomDomain {
  /**
   * Constructs a new `ProductDomain`.
   *
   * @param args - Operands in the order `domains`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'ProductDomain') {
    super(name, args);
  }
  /**
   * Checks whether the domain is a product of domains.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.rv.ProductDomain.is_ProductDomain`
   */
  override get isProductDomain(): boolean {
    return true;
  }
  /**
   * Lists the factors that make up the product domain.
   *
   * @returns The component domains.
   * @see SymPy `sympy.stats.rv.ProductDomain.domains`
   */
  get domains(): RandomDomain[] {
    return this.args.map((d) => cast(d, RandomDomain));
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.rv.ProductDomain.symbols`
   */
  get symbols(): Sym[] {
    return sortedSymbols(this.domains.flatMap((d) => d.symbols));
  }
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @see SymPy `sympy.stats.rv.ProductDomain.set`
   */
  get set(): SetExpr {
    return productSet(...this.domains.map((d) => d.set));
  }
  /**
   * Associates each symbol with the domain that supplies its values.
   *
   * @returns A symbol-to-domain map.
   * @see SymPy `sympy.stats.rv.ProductDomain.sym_domain_dict`
   */
  get symDomainDict(): Map<string, RandomDomain> {
    return new Map(this.domains.flatMap((d) => d.symbols.map((s) => [s.key, d] as const)));
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.rv.ProductDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return and(...this.domains.map((d) => d.asBoolean()));
  }
}

/** Symbols in the order of a SymPy FiniteSet (default_sort_key), without duplicates. */
export function sortedSymbols(xs: readonly Sym[]): Sym[] {
  const seen = new Map(xs.map((s) => [s.key, s] as const));
  return ordered([...seen.values()]).map((s) => cast(s, Sym));
}

/**
 * SymPy ProductDomain(*domains): products of products are flattened, and
 * domains that are all finite, continuous or discrete give the product
 * domain of that kind.
 */
export function makeProductDomain(domains: readonly RandomDomain[]): RandomDomain {
  const flat = domains.flatMap((d) => (d instanceof ProductDomain ? d.domains : [d]));
  const unique = [...new Map(flat.map((d) => [d.key, d] as const)).values()];
  const sorted = ordered(unique).map((d) => cast(d, RandomDomain));
  // SymPy tests finite, then continuous, then discrete
  if (sorted.every((d) => d.isDiscrete)) return defined(statsClasses.productDiscreteDomain, 'drv')(sorted);
  if (sorted.every((d) => d.isContinuous)) return defined(statsClasses.productContinuousDomain, 'crv')(sorted);
  if (sorted.every((d) => d.isFinite)) return defined(statsClasses.productFiniteDomain, 'frv')(sorted);
  return new ProductDomain(sorted);
}

// ---------------------------------------------------------------------------
// Probability spaces
// ---------------------------------------------------------------------------

/**
 * A probability space. `new PSpace()` is SymPy's PSpace() of a random symbol without a space.
 *
 * @see SymPy `sympy.stats.rv.PSpace`
 */
export class PSpace extends ExtensionExpr {
  /**
   * Constructs a new `PSpace`.
   *
   * @param args - The defining expressions in structural order.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[] = [], name = 'PSpace') {
    super(name, args);
  }
  /**
   * Indicates whether this probability space has finitely many outcomes.
   *
   * @returns `false` for this space.
   * @see SymPy `sympy.stats.rv.PSpace.is_Finite`
   */
  get isFinite(): boolean {
    return false;
  }
  /**
   * Indicates whether this probability space is continuous.
   *
   * @returns `false` for this space.
   * @see SymPy `sympy.stats.rv.PSpace.is_Continuous`
   */
  get isContinuous(): boolean {
    return false;
  }
  /**
   * Indicates whether this probability space is discrete.
   *
   * @returns `false` for this space.
   * @see SymPy `sympy.stats.rv.PSpace.is_Discrete`
   */
  get isDiscrete(): boolean {
    return false;
  }
  /**
   * Indicates whether the space is real-valued.
   *
   * @returns `false` for this space.
   * @see SymPy `sympy.stats.rv.PSpace.is_real`
   */
  get isReal(): boolean {
    return false;
  }
  /**
   * Tests whether the space governs a single variable with a distribution.
   *
   * @returns `false` for this space.
   */
  get isSingle(): boolean {
    return false;
  }
  /**
   * Tests whether random parameters govern the distribution of this space.
   *
   * @returns `false` for this space.
   */
  get isCompound(): boolean {
    return false;
  }
  /**
   * Tests whether the space belongs to a time-indexed stochastic process.
   *
   * @returns `false` for this space.
   */
  get isStochastic(): boolean {
    return false;
  }
  /**
   * Indicates whether the space permits overlapping variables in a product because its distribution is
   * compound or marginal.
   *
   * @returns Whether this space can share a symbol with another factor of a product.
   */
  get sharesSymbols(): boolean {
    return this.isCompound;
  }
  /**
   * Indicates whether the space can directly supply its random symbol's distribution or ensemble model as
   * its density.
   *
   * @returns Whether this space directly supplies the density of its random symbol.
   */
  get hasValueDensity(): boolean {
    return this.isSingle && !this.isCompound;
  }
  /**
   * Identifies the density of the space's random value when the space supplies one.
   *
   * @returns The value distribution.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  get valueDensity(): Expr {
    if (isSingleSpace(this)) return this.distribution;
    throw new NotImplementedError(`the density of the value of ${this.name} is computed`);
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.rv.PSpace.domain`
   */
  get domain(): RandomDomain {
    return cast(at(this.args, 0), RandomDomain, 'domain');
  }
  /**
   * Expresses the density on the underlying probability space.
   *
   * @returns The density expression.
   * @see SymPy `sympy.stats.rv.PSpace.density`
   */
  get density(): Expr {
    return at(this.args, 1);
  }
  /**
   * Lists the random symbols governed by this space.
   *
   * @returns The random symbols of the space.
   * @see SymPy `sympy.stats.rv.PSpace.values`
   */
  get values(): RandomSymbol[] {
    return this.symbols.map((s) => new RandomSymbol(s, this));
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.rv.PSpace.symbols`
   */
  get symbols(): Sym[] {
    return this.domain.symbols;
  }
  /**
   * Expresses the probability density in terms of the space's own symbols.
   *
   * @returns The joint density in the symbols of the space.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  get pdf(): Expr {
    throw new NotImplementedError(`pdf is not implemented for ${this.name}`);
  }
  /**
   * Restricts the domain to the subset satisfying the condition.
   *
   * @param _condition - Condition on the random variables.
   * @returns The domain satisfying the condition.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   * @see SymPy `sympy.stats.rv.PSpace.where`
   */
  where(_condition: Expr): RandomDomain {
    throw new NotImplementedError(`where is not implemented for ${this.name}`);
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param _expr - Expression to evaluate.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The probability distribution of the expression.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   * @see SymPy `sympy.stats.rv.PSpace.compute_density`
   */
  computeDensity(_expr: Expr, _opts?: ComputeOptions): DensityResult {
    throw new NotImplementedError(`compute_density is not implemented for ${this.name}`);
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param _condition - Condition on the random variables.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The probability of the event.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   * @see SymPy `sympy.stats.rv.PSpace.probability`
   */
  probability(_condition: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`probability is not implemented for ${this.name}`);
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param _expr - Expression to evaluate.
   * @param _rvs - Random variables to integrate or sum over.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The expected value over the selected variables.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   * @see SymPy `sympy.stats.rv.PSpace.compute_expectation`
   */
  computeExpectation(_expr: Expr, _rvs?: readonly RandomSymbol[], _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_expectation is not implemented for ${this.name}`);
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param _expr - Expression to evaluate.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The cumulative distribution function.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  computeCdf(_expr: Expr, _opts?: ComputeOptions): DensityResult {
    throw new NotImplementedError(`compute_cdf is not implemented for ${this.name}`);
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param _expr - Expression to evaluate.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The characteristic function.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  computeCharacteristicFunction(_expr: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_characteristic_function is not implemented for ${this.name}`);
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param _expr - Expression to evaluate.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The moment generating function.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  computeMomentGeneratingFunction(_expr: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_moment_generating_function is not implemented for ${this.name}`);
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param _expr - Expression to evaluate.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The quantile function.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  computeQuantile(_expr: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_quantile is not implemented for ${this.name}`);
  }
  /**
   * Restricts the probability space to outcomes that satisfy the condition.
   *
   * @param _condition - Condition on the random variables.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The conditioned probability space.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  conditionalSpace(_condition: Expr, _opts?: ComputeOptions): PSpace {
    throw new NotImplementedError(`conditional_space is not implemented for ${this.name}`);
  }
  /**
   * Computes a conditional probability involving time-indexed random symbols.
   *
   * @param _condition - Condition on the random variables.
   * @param _givenCondition - Additional event assumed to hold.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The probability of a condition on random indexed symbols given another condition.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  probabilityGiven(_condition: Expr, _givenCondition: Expr | undefined, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`probability given a condition is not implemented for ${this.name}`);
  }
  /**
   * Computes a conditional expectation involving time-indexed random symbols.
   *
   * @param _expr - Expression to evaluate.
   * @param _condition - Condition on the random variables.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The expectation of an expression of random indexed symbols given a condition.
   * @throws NotImplementedError when the concrete probability space does not implement this operation.
   */
  expectationGiven(_expr: Expr, _condition: Expr | undefined, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`expectation given a condition is not implemented for ${this.name}`);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
}

/** Options of the computations of a probability space (SymPy keyword arguments). */
export interface ComputeOptions {
  /** False: integrals and sums are left unevaluated (SymPy evaluate=False). */
  readonly evaluate?: boolean;
  /** CompoundPSpace: the marginalised density is evaluated. */
  readonly compoundEvaluate?: boolean;
}

/** The symbol of a probability space or random symbol, from a name (SymPy _symbol_converter). */
export function symbolConverter(sym: string | Expr): Sym {
  if (typeof sym === 'string') return new Sym(sym);
  if (!(sym instanceof Sym)) throw new TypeError(`${sym.toString()} is neither a Symbol nor a string`);
  return sym;
}

/**
 * A space of one variable with a distribution.
 *
 * @see SymPy `sympy.stats.rv.SinglePSpace`
 */
export class SinglePSpace extends PSpace {
  /**
   * Constructs a new `SinglePSpace`.
   *
   * @param args - Operands in the order `s`, `distribution`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'SinglePSpace') {
    super([symbolConverter(at(args, 0)), at(args, 1)], name);
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
   * Identifies the random variable represented by this probability space.
   *
   * @returns The random symbol.
   * @see SymPy `sympy.stats.rv.SinglePSpace.value`
   */
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.rv.SinglePSpace.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the law of the random variable in this space.
   *
   * @returns The distribution object.
   * @see SymPy `sympy.stats.rv.SinglePSpace.distribution`
   */
  get distribution(): Distribution {
    return cast(at(this.args, 1), Distribution, 'distribution');
  }
  /**
   * Expresses the density in terms of the symbols underlying the space.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.rv.SinglePSpace.pdf`
   */
  override get pdf(): Expr {
    return this.distribution.pdf(this.symbol);
  }
}

/** The members of a single probability space (SymPy SinglePSpace, which the spaces of the other modules also derive from). */
export interface SingleSpace {
  /** The underlying symbol naming the random variable. */
  readonly symbol: Sym;
  /** The probability law governing the random variable. */
  readonly distribution: Distribution;
  /** The random symbol with this probability space. */
  readonly value: RandomSymbol;
}

/** The space is a single space (SymPy isinstance(space, SinglePSpace)). */
export function isSingleSpace(ps: PSpace): ps is PSpace & SingleSpace {
  return ps.isSingle;
}

/**
 * A symbol whose values are distributed as its probability space says.
 *
 * @see SymPy `sympy.stats.rv.RandomSymbol`
 */
export class RandomSymbol extends Sym {
  /**
   * The underlying symbol naming the random variable.
   *
   * @see SymPy `sympy.stats.rv.RandomSymbol.symbol`
   */
  readonly symbol: Sym;
  /**
   * The probability space governing this symbol.
   *
   * @see SymPy `sympy.stats.rv.RandomSymbol.pspace`
   */
  readonly pspace: PSpace;
  /**
   * Constructs a new `RandomSymbol`.
   *
   * @param symbol - Name or symbol for the random variable.
   * @param pspace - Probability space determining the joint law.
   * @throws TypeError when the supplied space is not a probability space.
   */
  constructor(symbol: string | Sym, pspace: PSpace = new PSpace()) {
    const s = symbolConverter(symbol);
    if (!(pspace instanceof PSpace)) throw new TypeError('pspace variable should be of type PSpace');
    // SymPy: is_positive and is_integer are the symbol's, is_real also holds when the space is real
    const a: Assumptions = { ...s.assumptions, ...(pspace.isReal ? { real: true } : {}) };
    super(s.name, a);
    this.symbol = s;
    this.pspace = pspace;
  }
  /**
   * Supplies the class name for canonical ordering of random symbols.
   *
   * @returns The class name used for canonical ordering.
   */
  override get sortClass(): string {
    return 'RandomSymbol';
  }
  /**
   * Determines where the symbol sorts relative to other expression classes.
   *
   * @returns The ordering priority.
   */
  override get sortPriority(): number {
    return 5;
  }
  /**
   * Applies substitution to the symbol and its probability space.
   *
   * @param f - Substitution applied to the inner expression.
   * @returns The replacement expression when this hook supplies one.
   */
  override substituteInner(f: (e: Expr) => Expr): Expr | undefined {
    // the symbol of the variable is bound: only the parameters of a single space's distribution are substituted
    // (SymPy also substitutes the symbol, and fails when it becomes an expression such as x + 1)
    const ps = this.pspace;
    if (!isSingleSpace(ps)) {
      const nps = f(ps);
      return nps === ps ? undefined : new RandomSymbol(this.symbol, cast(nps, PSpace, 'probability space'));
    }
    const dist = f(ps.distribution);
    return dist === ps.distribution ? undefined : new RandomSymbol(this.symbol, cast(ps.withArgs([ps.symbol, dist]), PSpace, 'probability space'));
  }
  /**
   * Searches both the symbol and its probability space for the operand.
   *
   * @param sub - Expression to locate.
   * @returns Whether the expression occurs in the symbol or its probability space.
   * @see SymPy `sympy.stats.rv.RandomSymbol.has`
   */
  override has(sub: Expr): boolean {
    return super.has(sub) || this.pspace.has(sub);
  }
  protected override computeKey(): string {
    return `RandomSymbol(${this.symbol.key};${this.pspace.key})`;
  }
}

/**
 * A random symbol that is an
 * indexed object X[n] (a discrete-time stochastic process) or the
 * application X(t) of a function (a continuous-time one). It prints as the
 * indexed object; `symbol` is the plain symbol of that name, and
 * `indexedSymbol` is SymPy's symbol (the Indexed or the applied function).
 *
 * @see SymPy `sympy.stats.rv.RandomIndexedSymbol`
 */
export class RandomIndexedSymbol extends RandomSymbol {
  /** The Indexed X[n] or the applied function X(t). */
  readonly indexedSymbol: Expr;
  /**
   * Constructs a new `RandomIndexedSymbol`.
   *
   * @param idxObj - Indexed expression naming this component.
   * @param pspace - Probability space determining the joint law.
   * @throws TypeError when the argument is neither indexed nor an applied undefined function.
   */
  constructor(idxObj: Expr, pspace: PSpace = new PSpace()) {
    if (!(idxObj instanceof Indexed || idxObj instanceof UndefFn)) throw new TypeError(`An Function or Indexed object is expected not ${idxObj.toString()}`);
    super(idxObj.toString(), pspace);
    this.indexedSymbol = idxObj;
  }
  /**
   * Identifies the class used to sort this expression.
   *
   * @returns The ordering class name.
   */
  override get sortClass(): string {
    return 'RandomIndexedSymbol';
  }
  /**
   * Identifies the index of the time-indexed random symbol.
   *
   * @returns The index of the symbol.
   */
  get indexKey(): Expr {
    const i = this.indexedSymbol;
    return i instanceof Indexed ? at(i.args, 1) : at(i.args, 0);
  }
  /**
   * Collects free symbols occurring in the index of the random variable.
   *
   * @returns The free symbols.
   */
  override innerFreeSymbols(): readonly Sym[] {
    return [...this.indexKey.freeSymbols()].filter((s) => s instanceof Sym);
  }
  /**
   * Applies a substitution to the expression inside the random symbol.
   *
   * @param f - Substitution applied to the inner expression.
   * @returns The replacement expression when this hook supplies one.
   */
  override substituteInner(f: (e: Expr) => Expr): Expr | undefined {
    const [i, ps] = [f(this.indexedSymbol), f(this.pspace)];
    return i === this.indexedSymbol && ps === this.pspace ? undefined : new RandomIndexedSymbol(i, cast(ps, PSpace, 'probability space'));
  }
  /**
   * Checks the expression tree for the specified subexpression.
   *
   * @param sub - Expression to locate.
   * @returns True if it occurs.
   * @see SymPy `sympy.stats.rv.RandomIndexedSymbol.has`
   */
  override has(sub: Expr): boolean {
    return super.has(sub) || this.indexedSymbol.has(sub);
  }
  protected override computeKey(): string {
    return `RandomIndexedSymbol(${this.indexedSymbol.key};${this.pspace.key})`;
  }
}

/**
 * A matrix symbol whose
 * values are distributed as its probability space says. It is a matrix
 * symbol (SymPy derives from RandomSymbol and MatrixSymbol), so it takes
 * part in matrix expressions; `isRandom` and `pspace` recognize it.
 *
 * @see SymPy `sympy.stats.rv.RandomMatrixSymbol`
 */
export class RandomMatrixSymbol extends MatrixSymbolNode {
  /**
   * The underlying symbol naming the random variable.
   *
   * @see SymPy `sympy.stats.rv.RandomMatrixSymbol.symbol`
   */
  readonly symbol: Sym;
  /**
   * The probability space governing this symbol.
   *
   * @see SymPy `sympy.stats.rv.RandomMatrixSymbol.pspace`
   */
  readonly pspace: PSpace;
  /**
   * Constructs a new `RandomMatrixSymbol`.
   *
   * @param symbol - Name or symbol for the random variable.
   * @param n - Number of rows.
   * @param m - Number of columns.
   * @param pspace - Probability space determining the joint law.
   */
  constructor(symbol: string | Sym, n: ExprLike, m: ExprLike, pspace: PSpace = new PSpace()) {
    const s = symbolConverter(symbol);
    super(s.name, n, m, [pspace]);
    this.symbol = s;
    this.pspace = pspace;
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new RandomMatrixSymbol(this.symbol, at(args, 1), at(args, 2), cast(args[3] ?? this.pspace, PSpace));
  }
  /**
   * Checks the expression tree for the specified subexpression.
   *
   * @param sub - Expression to locate.
   * @returns True if it occurs.
   * @see SymPy `sympy.stats.rv.RandomMatrixSymbol.has`
   */
  override has(sub: Expr): boolean {
    return super.has(sub) || this.pspace.has(sub);
  }
  protected override computeKey(): string {
    return `RandomMatrixSymbol(${super.computeKey()};${this.pspace.key})`;
  }
}

/** The expression contains a random indexed symbol (SymPy expr.has(RandomIndexedSymbol)). */
export function hasRandomIndexedSymbol(e: Expr): boolean {
  return e instanceof RandomIndexedSymbol || e.args.some(hasRandomIndexedSymbol);
}

/** The random matrix symbols of an expression (SymPy expr.atoms(RandomMatrixSymbol)). */
export function randomMatrixSymbols(expr: Expr): RandomMatrixSymbol[] {
  const out = new Map<string, RandomMatrixSymbol>();
  const go = (e: Expr): void => {
    if (e instanceof RandomMatrixSymbol) out.set(e.key, e);
    else e.args.forEach(go);
  };
  go(expr);
  return [...out.values()];
}

/**
 * A probability space with several random variables.
 *
 * @see SymPy `sympy.stats.rv.ProductPSpace`
 */
export class ProductPSpace extends PSpace {}

/**
 * The merger of independent
 * probability spaces. Use `independentProductPSpace` to build one (finite
 * spaces give a ProductFinitePSpace).
 *
 * @see SymPy `sympy.stats.rv.IndependentProductPSpace`
 */
export class IndependentProductPSpace extends ProductPSpace {
  /**
   * Constructs a new `IndependentProductPSpace`.
   *
   * @param args - Operands in the order `spaces`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'IndependentProductPSpace') {
    super(args, name);
  }
  /**
   * Expresses the density in terms of the symbols underlying the space.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.pdf`
   */
  override get pdf(): Expr {
    const p = mul(...this.spaces.map((s) => s.pdf));
    return xreplace(p, this.values.map((rv) => [rv, rv.symbol] as const));
  }
  /**
   * Associates each random symbol with the space that governs it.
   *
   * @returns A symbol-to-space map.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.rs_space_dict`
   */
  get rsSpaceDict(): Map<string, [RandomSymbol, PSpace]> {
    return new Map(this.spaces.flatMap((sp) => sp.values.map((v) => [v.key, [v, sp]] as const)));
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.symbols`
   */
  override get symbols(): Sym[] {
    return sortedSymbols([...this.rsSpaceDict.values()].map(([v]) => v.symbol));
  }
  /**
   * Lists the mutually independent spaces forming the product space.
   *
   * @returns The component probability spaces.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.spaces`
   */
  get spaces(): PSpace[] {
    return this.args.map((a) => cast(a, PSpace));
  }
  /**
   * Lists the random symbols belonging to the probability space.
   *
   * @returns The space's random variables.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.values`
   */
  override get values(): RandomSymbol[] {
    return [...this.rsSpaceDict.values()].map(([v]) => v);
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvsIn - Random variables to integrate or sum over.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expected value over the selected variables.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[], opts: ComputeOptions = {}): Expr {
    const rvs = rvsIn ?? this.values;
    let expr = exprIn;
    for (const space of this.spaces) {
      const keys = new Set(space.values.map((v) => v.key));
      expr = space.computeExpectation(
        expr,
        rvs.filter((v) => keys.has(v.key)),
        { ...opts, evaluate: false },
      );
    }
    return opts.evaluate === true ? doit(expr) : expr;
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.domain`
   */
  override get domain(): RandomDomain {
    return makeProductDomain(this.spaces.map((s) => s.domain));
  }
  /**
   * Expresses the density on the underlying probability space.
   *
   * @returns The density expression.
   * @throws NotImplementedError when the density of the product space itself is requested.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.density`
   */
  override get density(): Expr {
    throw new NotImplementedError('Density not available for ProductSpaces');
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param conditionIn - Condition on the random variables.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The probability of the event.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.probability`
   */
  override probability(conditionIn: Expr, opts: ComputeOptions = {}): Expr {
    let condition = conditionIn;
    let condInv = false;
    if (condition instanceof Rel && condition.op === 'Ne') {
      condition = Eq(condition.lhs, condition.rhs);
      condInv = true;
    } else if (condition instanceof BoolOp && condition.op === 'And') {
      // they are independent
      return mul(...condition.args.map((a) => this.probability(a)));
    } else if (condition instanceof BoolOp && condition.op === 'Or') {
      return add(...condition.args.map((a) => this.probability(a)));
    }
    const r = cast(condition, Rel, 'condition');
    const expr = add(r.lhs, mul(-1, r.rhs));
    const rvs = randomSymbols(expr);
    let space: PSpace & SingleSpace;
    if (rvs.length === 1) {
      // a condition on one random symbol of the product is a condition on its own space (SymPy marginalizes
      // the density of a continuous one with ProductContinuousDomain.integrate, which does not exist: AttributeError)
      const result = first(rvs).pspace.probability(condition, opts);
      return condInv ? add(1, mul(-1, result)) : result;
    }
    const dens = this.computeDensity(expr, opts);
    if (rvs.some((rv) => pspace(rv).isContinuous)) {
      const dist = defined(statsClasses.continuousHandmade, 'crv_types')(cast(dens, Expr));
      space = defined(statsClasses.continuousSingle, 'crv')(new Dummy('z', { real: true }), dist);
    } else {
      const dist = defined(statsClasses.discreteHandmade, 'drv_types')(cast(dens, Expr));
      space = defined(statsClasses.discreteSingle, 'drv')(new Dummy('z', { integer: true }), dist);
    }
    const result = space.probability(rel(r.op, space.value, 0));
    return condInv ? add(1, mul(-1, result)) : result;
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param expr - Expression to evaluate.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The probability distribution of the expression.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.compute_density`
   */
  override computeDensity(expr: Expr, opts: ComputeOptions = {}): DensityResult {
    const rvs = randomSymbols(expr);
    if (rvs.some((rv) => pspace(rv).isContinuous)) {
      const z = new Dummy('z', { real: true });
      return Lambda(z, this.computeExpectation(DiracDelta(add(expr, mul(-1, z))), undefined, opts));
    }
    const z = new Dummy('z', { integer: true });
    return Lambda(z, this.computeExpectation(KroneckerDelta(expr, z), undefined, opts));
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param _expr - Expression to evaluate.
   * @returns The cumulative distribution function.
   * @throws RangeError when the expression is multivariate.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.compute_cdf`
   */
  override computeCdf(_expr: Expr): DensityResult {
    throw new RangeError('CDF not well defined on multivariate expressions');
  }
  /**
   * Restricts the probability space to outcomes that satisfy the condition.
   *
   * @param conditionIn - Condition on the random variables.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The conditioned probability space.
   * @see SymPy `sympy.stats.rv.IndependentProductPSpace.conditional_space`
   */
  override conditionalSpace(conditionIn: Expr, _opts: ComputeOptions = {}): PSpace {
    const rvs = randomSymbols(conditionIn);
    const condition = xreplace(conditionIn, this.values.map((rv) => [rv, rv.symbol] as const));
    const pspaces = rvs.map((rv) => pspace(rv));
    let domain: RandomDomain;
    let make: (domain: RandomDomain, density: Expr) => PSpace;
    if (pspaces.some((ps) => ps.isContinuous)) {
      domain = defined(statsClasses.continuousConditional, 'crv')(this.domain, condition);
      make = defined(statsClasses.continuousPSpace, 'crv');
    } else if (pspaces.some((ps) => ps.isDiscrete)) {
      domain = defined(statsClasses.discreteConditional, 'drv')(this.domain, condition);
      make = defined(statsClasses.discretePSpace, 'drv');
    } else {
      return defined(statsClasses.finiteConditionalSpace, 'frv')(this, condition);
    }
    const replacement = this.symbols.map((s) => [s, new Dummy(s.name)] as const);
    const norm = domain.computeExpectation(this.pdf);
    const pdf = mul(this.pdf, xreplace(norm, replacement).pow(-1));
    return make(domain, Lambda(domain.symbols, pdf));
  }
}

/**
 * SymPy IndependentProductPSpace(*spaces): the spaces are ordered like a
 * FiniteSet, and finite spaces give a ProductFinitePSpace. Overlapping
 * random variables are rejected.
 */
export function independentProductPSpace(spacesIn: readonly PSpace[]): PSpace {
  const spaces = ordered([...new Map(spacesIn.map((s) => [s.key, s] as const)).values()]).map((s) => cast(s, PSpace));
  const symbols = new Set(spaces.flatMap((s) => s.values.map((v) => v.symbol.key)));
  const counted = spaces.filter((s) => !s.sharesSymbols).reduce((n, s) => n + s.symbols.length, 0);
  if (symbols.size < counted) throw new RangeError('Overlapping Random Variables');
  if (spaces.every((s) => s.isFinite)) return defined(statsClasses.productFinitePSpace, 'frv')(spaces);
  return new IndependentProductPSpace(spaces);
}

// ---------------------------------------------------------------------------
// Distributions
// ---------------------------------------------------------------------------

/**
 * The base class of the distributions (an expression node of its parameters).
 *
 * @see SymPy `sympy.stats.rv.Distribution`
 * @example
 * ```ts
 * import { BetaDistribution, ex } from '@symjs/symjs';
 *
 * const law = new BetaDistribution([ex`2`, ex`3`]);
 * law.pdf(ex`1/2`); // => 3/2
 * ```
 */
export abstract class Distribution extends ExtensionExpr {
  /**
   * Evaluates the probability density or mass function at the argument.
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   */
  abstract pdf(x: ExprLike): Expr;
  /**
   * Specifies the possible values of the distribution.
   *
   * @returns The support set.
   */
  abstract get set(): SetExpr;
  /**
   * Tests whether the law is a single finite distribution.
   *
   * @returns `false` for this distribution.
   */
  get isFinite(): boolean {
    return false;
  }
  /**
   * Associates the outcomes of the finite distribution with their masses.
   *
   * @returns The finite density.
   * @throws NotImplementedError when the distribution has no finite mass table.
   */
  get dict(): DensityResult {
    throw new NotImplementedError(`${this.name} is not a finite distribution`);
  }
  /**
   * Evaluates the density at the specified outcome.
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The density value.
   */
  call(x: ExprLike): Expr {
    return this.pdf(x);
  }
  /** The parameter at index i (SymPy NamedArgsMixin). */
  protected arg(i: number): Expr {
    return at(this.args, i);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
}

/**
 * SymPy _value_check: throws a RangeError with the message when the
 * condition is false; true when it holds and false when it is undecided.
 */
export function valueCheck(condition: Expr | boolean | undefined | readonly (Expr | boolean | undefined)[], message: string): boolean {
  const conds: readonly (Expr | boolean | undefined)[] = Array.isArray(condition) ? condition : [condition];
  const truths: Truth[] = conds.map((c) => (c === undefined ? 'unknown' : typeof c === 'boolean' ? c : c instanceof BoolAtom ? c.value : 'unknown'));
  if (truths.includes(false)) throw new RangeError(message);
  return truths.every((t) => t === true);
}

// ---------------------------------------------------------------------------
// Random symbols of an expression
// ---------------------------------------------------------------------------

/**
 * Collects the random symbols occurring in an expression in name order.
 *
 * @param expr - Expression to evaluate.
 * @returns The sorted random symbols.
 * @see SymPy `sympy.stats.rv.random_symbols`
 */
export function randomSymbols(expr: unknown): RandomSymbol[] {
  if (!(expr instanceof Expr)) return [];
  const out = new Map<string, RandomSymbol>();
  const go = (e: Expr): void => {
    if (e instanceof RandomSymbol) out.set(e.key, e);
    else e.args.forEach(go);
  };
  go(expr);
  return [...out.values()].sort((a, b) => (a.symbol.name < b.symbol.name ? -1 : a.symbol.name > b.symbol.name ? 1 : 0));
}

/** The value is an array of expressions (several expressions whose common space is wanted). */
const isExprArray = (x: ExprLike | readonly Expr[]): x is readonly Expr[] => Array.isArray(x);

/**
 * Finds the space governing a random expression.
 *
 * @param exprIn - Expression to evaluate.
 * @returns The expression's probability space.
 * @throws RangeError when the expression contains no random variables.
 * @see SymPy `sympy.stats.rv.pspace`
 * @example
 * ```ts
 * import { Normal, pspace } from '@symjs/symjs';
 *
 * const X = Normal('X', 0, 1);
 * pspace(X.mul(2).add(1)).equals(X.pspace); // => True
 * ```
 */
export function pspace(exprIn: ExprLike | readonly Expr[]): PSpace {
  const expr = isExprArray(exprIn) ? new TupleNode(exprIn) : sympify(exprIn);
  if (expr instanceof RandomSymbol || expr instanceof RandomMatrixSymbol) return expr.pspace;
  const rm = randomMatrixSymbols(expr);
  if (rm.length) return first(rm).pspace;
  const rvs = randomSymbols(expr);
  if (!rvs.length) throw new RangeError(`Expression containing Random Variable expected, not ${expr.toString()}`);
  const p0 = first(rvs).pspace;
  // if only one space present
  if (rvs.every((rv) => rv.pspace.key === p0.key)) return p0;
  const compound = rvs.find((rv) => rv.pspace.isCompound || rv.pspace.isStochastic);
  if (compound) return compound.pspace;
  // otherwise make a product space
  return independentProductPSpace(rvs.map((rv) => rv.pspace));
}

/** The random symbols of b paired with those of a with the same symbol (SymPy rs_swap). */
export function rsSwap(a: readonly RandomSymbol[], b: readonly RandomSymbol[]): [RandomSymbol, RandomSymbol][] {
  return a.map((rsa) => [rsa, defined(b.find((rsb) => rsa.symbol.key === rsb.symbol.key), 'matching random symbol')]);
}

/** The expression with its random symbols replaced by their symbols (SymPy rv_subs). */
export function rvSubs(expr: Expr, symbols?: readonly RandomSymbol[]): Expr {
  const rvs = symbols ?? randomSymbols(expr);
  if (!rvs.length) return expr;
  return expr.subs(rvs.map((rv) => [rv, rv.symbol] as const));
}

// ---------------------------------------------------------------------------
// The probability functions
// ---------------------------------------------------------------------------

/**
 * Restricts a random expression to the probability space conditioned on the event, treating a
 * conditioning random symbol as fixed.
 *
 * @param exprIn - Expression to evaluate.
 * @param conditionIn - Condition on the random variables.
 * @param opts - Evaluation controls for integrals, sums and compound distributions.
 * @returns The expression on the conditioned probability space.
 * @throws TypeError when the conditioning equation cannot be resolved to a finite set of values.
 * @see SymPy `sympy.stats.rv.given`
 * @example
 * ```ts
 * import { Die, FiniteDensity, Gt, density, given } from '@symjs/symjs';
 *
 * const X = Die('X', 6);
 * (density(given(X, Gt(X, 3))) as FiniteDensity).dict; // => {4: 1/3, 5: 1/3, 6: 1/3}
 * ```
 */
export function given(exprIn: ExprLike, conditionIn?: ExprLike, opts: ComputeOptions = {}): Expr {
  const expr = sympify(exprIn);
  if (conditionIn === undefined) return expr;
  let condition = sympify(conditionIn);
  if (!isRandom(condition) || pspaceIndependent(expr, condition) === true) return expr;
  if (condition instanceof RandomSymbol) condition = Eq(condition, condition.symbol);
  const condsymbols = randomSymbols(condition);
  if (condition instanceof Rel && condition.op === 'Eq' && condsymbols.length === 1 && !pspace(expr).domain.isConditional) {
    const rv = first(condsymbols);
    // (SymPy also unwraps Intersection(Reals, solutions), which solveset over the complex numbers does not give here)
    const results = solveset(condition, rv);
    // SymPy iterates over the solutions (a ConditionSet cannot be iterated)
    if (!(results instanceof FiniteSet)) throw new TypeError(`cannot iterate over ${results.toString()}`);
    let sums: Expr = S.Zero;
    for (const res of results.args) {
      const temp = expr.subs(rv, res);
      if (temp === S.true) return S.true;
      if (temp !== S.false) sums = sums === S.Zero && temp instanceof Rel ? temp : add(sums, temp);
    }
    if (sums === S.Zero) return S.false;
    return sums;
  }
  // full probability space of both the expression and the condition
  const fullspace = pspace([expr, condition]);
  // the new space given the condition
  const space = fullspace.conditionalSpace(condition, opts);
  // swap the random symbols of the expression for those of the new space
  return xreplace(expr, rsSwap(fullspace.values, space.values));
}

/** Options of the probability functions (SymPy keyword arguments). */
export interface ProbabilityOptions {
  /** False: integrals and sums are left unevaluated (SymPy evaluate=False). */
  readonly evaluate?: boolean;
}

/**
 * Computes the expected value of a random expression under the optional condition.
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The conditional or unconditional mean, or an unevaluated expectation.
 * @see SymPy `sympy.stats.rv.expectation`
 * @example
 * ```ts
 * import { Die, Gt, expectation } from '@symjs/symjs';
 *
 * const X = Die('X', 6);
 * expectation(X); // => 7/2
 * expectation(X, Gt(X, 3)); // => 5
 * ```
 */
export function expectation(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const e = sympify(expr);
  // expr isn't random
  if (!isRandom(e)) return e;
  return defined(statsClasses.expectation, 'stats symbolic_probability')(e, condition === undefined ? undefined : sympify(condition), opts.evaluate ?? true);
}

/**
 * Computes an event's probability under the optional conditioning event.
 *
 * @param condition - Condition on the random variables.
 * @param givenCondition - Additional event assumed to hold.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The probability expression.
 * @see SymPy `sympy.stats.rv.probability`
 * @example
 * ```ts
 * import { Die, Eq, Gt, P } from '@symjs/symjs';
 *
 * const X = Die('X', 6);
 * P(Gt(X, 3)); // => 1/2
 * P(Eq(X, 5), Gt(X, 2)); // => 1/4
 * ```
 */
export function P(condition: ExprLike | boolean, givenCondition?: ExprLike | boolean, opts: ProbabilityOptions = {}): Expr {
  const c = typeof condition === 'boolean' ? (condition ? S.true : S.false) : sympify(condition);
  const g = givenCondition === undefined ? undefined : typeof givenCondition === 'boolean' ? (givenCondition ? S.true : S.false) : sympify(givenCondition);
  return defined(statsClasses.probability, 'stats symbolic_probability')(c, g, opts.evaluate ?? true);
}

/**
 * The unevaluated density of a random expression.
 *
 * @see SymPy `sympy.stats.rv.Density`
 * @example
 * ```ts
 * import { Density, Normal } from '@symjs/symjs';
 *
 * const X = Normal('X', 0, 1);
 * new Density([X]).compute(); // => NormalDistribution(0, 1)
 * ```
 */
export class Density extends ExtensionExpr {
  /**
   * Constructs a new `Density`.
   *
   * @param args - Operands in the order `expr`, `condition`.
   */
  constructor(args: readonly Expr[]) {
    super('Density', args);
  }
  /**
   * Identifies the operand of the statistical operation.
   *
   * @returns The underlying expression.
   * @see SymPy `sympy.stats.rv.Density.expr`
   */
  get expr(): Expr {
    return at(this.args, 0);
  }
  /**
   * Identifies the event used to restrict the domain or computation.
   *
   * @returns The conditioning expression, when present.
   * @see SymPy `sympy.stats.rv.Density.condition`
   */
  get condition(): Expr | undefined {
    return this.args[1];
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new Density(args);
  }
  /**
   * Determines the law of the stored expression under its optional conditioning event.
   *
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns A density expression or finite probability map.
   * @see SymPy `sympy.stats.rv.Density.doit`
   */
  compute(opts: ComputeOptions = {}): DensityResult {
    let expr = this.expr;
    const condition = this.condition;
    if (expr instanceof Distribution && expr.isFinite) return expr.dict;
    if (condition !== undefined) expr = given(expr, condition, opts);
    if (!randomSymbols(expr).length && !randomMatrixSymbols(expr).length) return Lambda(xGlobal, DiracDelta(add(xGlobal, mul(-1, expr))));
    if ((expr instanceof RandomSymbol || expr instanceof RandomMatrixSymbol) && expr.pspace.hasValueDensity) return expr.pspace.valueDensity;
    const ps = pspace(expr);
    const result = ps.computeDensity(expr, ps.isCompound ? { ...opts, compoundEvaluate: opts.evaluate ?? true } : opts);
    return (opts.evaluate ?? true) && result instanceof Expr ? doit(result) : result;
  }
  /**
   * Evaluates the density when it has an expression representation.
   *
   * @returns The replacement expression when this hook supplies one.
   * @see SymPy `sympy.stats.rv.Density.doit`
   */
  override doitSelf(): Expr | undefined {
    const r = this.compute();
    return r instanceof Expr ? r : undefined;
  }
}

/** SymPy Density(expr, condition=None). */
export function makeDensity(expr: ExprLike, condition?: ExprLike): Density {
  return new Density(condition === undefined ? [sympify(expr)] : [sympify(expr), sympify(condition)]);
}

/**
 * Computes the law of a random expression, optionally conditioning on an event.
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The distribution or lambda density, a finite mass map, or an unevaluated density.
 * @see SymPy `sympy.stats.rv.density`
 * @example
 * ```ts
 * import { Distribution, Normal, density, ex } from '@symjs/symjs';
 *
 * const X = Normal('x', 0, 1);
 * (density(X) as Distribution).pdf(ex`x`); // => sqrt(2)*exp(-x**2/2)/(2*sqrt(pi))
 * ```
 */
export function density(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): DensityResult {
  return makeDensity(expr, condition).compute({ evaluate: opts.evaluate ?? true });
}

/** A result that is an expression is evaluated (SymPy `if evaluate and hasattr(result, 'doit')`). */
const evaluated = (r: DensityResult, evaluate: boolean): DensityResult => (evaluate && r instanceof Expr ? doit(r) : r);

/**
 * Computes the cumulative distribution of a random expression under the optional condition.
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The cumulative probabilities as a finite map or a cumulative distribution function.
 * @throws RangeError when the expression contains no random variables.
 * @throws NotImplementedError when the space cannot compute a cumulative distribution.
 * @see SymPy `sympy.stats.rv.cdf`
 * @example
 * ```ts
 * import { Die, cdf } from '@symjs/symjs';
 *
 * const D = Die('D', 6);
 * cdf(D); // => {1: 1/6, 2: 1/3, 3: 1/2, 4: 2/3, 5: 5/6, 6: 1}
 * ```
 */
export function cdf(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): DensityResult {
  // recompute on the conditional expression
  if (condition !== undefined) return cdf(given(expr, condition), undefined, opts);
  const e = sympify(expr);
  return evaluated(pspace(e).computeCdf(e, {}), opts.evaluate ?? true);
}

/**
 * Constructs the characteristic function of a random expression under the optional condition.
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns A characteristic-function lambda.
 * @throws RangeError when the expression contains no random variables.
 * @throws NotImplementedError when the space does not implement the transform.
 * @see SymPy `sympy.stats.rv.characteristic_function`
 * @example
 * ```ts
 * import { Normal, characteristicFunction } from '@symjs/symjs';
 *
 * const X = Normal('X', 0, 1);
 * characteristicFunction(X); // => Lambda(_t, exp(-_t**2/2))
 * ```
 */
export function characteristicFunction(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  if (condition !== undefined) return characteristicFunction(given(expr, condition), undefined, opts);
  const e = sympify(expr);
  const r = pspace(e).computeCharacteristicFunction(e);
  return opts.evaluate ?? true ? doit(r) : r;
}

/**
 * Constructs the moment generating function of a random expression under the optional condition.
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns A moment-generating lambda.
 * @throws RangeError when the expression contains no random variables.
 * @throws NotImplementedError when the distribution has no supported moment generating function.
 * @see SymPy `sympy.stats.rv.moment_generating_function`
 * @example
 * ```ts
 * import { Normal, momentGeneratingFunction } from '@symjs/symjs';
 *
 * const X = Normal('X', 0, 1);
 * momentGeneratingFunction(X); // => Lambda(_t, exp(_t**2/2))
 * ```
 */
export function momentGeneratingFunction(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  if (condition !== undefined) return momentGeneratingFunction(given(expr, condition), undefined, opts);
  const e = sympify(expr);
  const r = pspace(e).computeMomentGeneratingFunction(e);
  return opts.evaluate ?? true ? doit(r) : r;
}

/**
 * Finds the outcome domain satisfying an event under the optional condition.
 *
 * @param condition - Condition on the random variables.
 * @param givenCondition - Additional event assumed to hold.
 * @returns The domain restricted to outcomes satisfying the event.
 * @see SymPy `sympy.stats.rv.where`
 * @example
 * ```ts
 * import { Lt, Normal, where } from '@symjs/symjs';
 *
 * const X = Normal('x', 0, 1);
 * where(Lt(X.pow(2), 1)).set; // => Interval.open(-1, 1)
 * ```
 */
export function where(condition: ExprLike, givenCondition?: ExprLike): RandomDomain {
  if (givenCondition !== undefined) return where(given(condition, givenCondition));
  const c = sympify(condition);
  return pspace(c).where(c);
}

/**
 * Constructs the quantile function of a random expression.
 *
 * @param expr - Expression to evaluate.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The quantile lambda.
 * @throws RangeError when the expression contains no random variables.
 * @see SymPy `sympy.stats.rv.quantile`
 * @example
 * ```ts
 * import { Lambda, Exponential, ex, quantile, symbols } from '@symjs/symjs';
 *
 * const [rate] = symbols('lambda', { positive: true });
 * (quantile(Exponential('x', rate)) as Lambda).call(ex`p`); // => -log(1 - p)/lambda
 * ```
 */
export function quantile(expr: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const e = sympify(expr);
  const r = pspace(e).computeQuantile(e);
  return opts.evaluate ?? true ? doit(r) : r;
}

/** Two densities are equal (SymPy ==: dicts by their items, expressions structurally). */
function sameDensity(a: DensityResult, b: DensityResult): boolean {
  if (a instanceof FiniteDensity || b instanceof FiniteDensity) {
    if (!(a instanceof FiniteDensity && b instanceof FiniteDensity) || a.size !== b.size) return false;
    return [...a].every(([k, v]) => b.get(k)?.key === v.key);
  }
  return a.key === b.key;
}

/**
 * Tests whether two random expressions are dependent.
 *
 * @param a - First random expression.
 * @param b - Second random expression.
 * @returns True if conditioning changes the distribution.
 * @see SymPy `sympy.stats.rv.dependent`
 * @example
 * ```ts
 * import { Normal, dependent } from '@symjs/symjs';
 *
 * const X = Normal('X', 0, 1), Y = Normal('Y', 0, 1);
 * dependent(X, Y); // => False
 * ```
 */
export function dependent(a: ExprLike, b: ExprLike): boolean {
  const ea = sympify(a);
  const eb = sympify(b);
  if (pspaceIndependent(ea, eb) === true) return false;
  const z = new Sym('z', { real: true });
  return !sameDensity(density(ea, Eq(eb, z)), density(ea)) || !sameDensity(density(eb, Eq(ea, z)), density(eb));
}

/**
 * Tests whether two random expressions are independent.
 *
 * @param a - First random expression.
 * @param b - Second random expression.
 * @returns True if conditioning on the other expression leaves the distribution unchanged.
 * @see SymPy `sympy.stats.rv.independent`
 * @example
 * ```ts
 * import { Normal, independent } from '@symjs/symjs';
 *
 * const X = Normal('X', 0, 1), Y = Normal('Y', 0, 1);
 * independent(X, Y); // => True
 * ```
 */
export function independent(a: ExprLike, b: ExprLike): boolean {
  return !dependent(a, b);
}

/**
 * The random expressions have independent probability spaces (SymPy
 * pspace_independent): true when they share no symbols, false when they
 * share random symbols, 'unknown' otherwise.
 */
export function pspaceIndependent(a: Expr, b: Expr): Truth {
  const aSymbols = new Set(pspace(b).symbols.map((s) => s.key));
  const bSymbols = pspace(a).symbols.map((s) => s.key);
  // SymPy's atoms(RandomSymbol) also reaches the random parameters inside a variable's probability space
  const nested = (e: Expr): string[] => randomSymbols(e).flatMap((r) => [r.key, ...nested(r.pspace)]);
  const rb = new Set(nested(b));
  if (nested(a).some((k) => rb.has(k))) return false;
  if (!bSymbols.some((k) => aSymbols.has(k))) return true;
  return 'unknown';
}

