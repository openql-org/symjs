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

import { BoolAtom, Dummy, Expr, ExtensionExpr, Rel, S, Sym } from '../core/nodes';
import type { Assumptions, ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { Eq, rel } from '../core/logic';
import { BoolOp, and } from '../core/boolalg';
import { xreplace } from '../core/traverse';
import { ordered } from '../core/match';
import { Lambda } from '../core/lambda';
import { TupleNode } from '../core/containers';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, first } from '../core/guard';
import type { Truth } from '../core/truth';
import { FiniteSet, SetExpr, productSet } from '../sets/sets';
import { solveset } from '../solvers/inequalities';
import { DiracDelta } from '../integrals/transforms/delta';
import { KroneckerDelta } from '../functions/special/hyper';
import { doit } from '../calculus/doit';

/** The global symbol x of sympy/stats/rv.py (the variable of the density of a constant). */
const xGlobal = new Sym('x');

/** A random symbol, an expression of random symbols or any value is random (SymPy is_random). */
export function isRandom(x: unknown): boolean {
  if (x instanceof RandomSymbol) return true;
  if (!(x instanceof Expr)) return false;
  return [...x.freeSymbols()].some((s) => s instanceof RandomSymbol);
}

/** A dict of the probability spaces of a probability computation (SymPy FiniteDensity and the dicts of finite spaces). */
export class FiniteDensity extends Map<Expr, Expr> {
  readonly #byKey = new Map<string, Expr>();
  constructor(entries: Iterable<readonly [Expr, Expr]> = []) {
    super();
    for (const [k, v] of entries) this.set(k, v);
  }
  override set(k: Expr, v: Expr): this {
    const c = this.#byKey.get(k.key);
    if (c !== undefined) return super.set(c, v);
    this.#byKey.set(k.key, k);
    return super.set(k, v);
  }
  override get(k: Expr): Expr | undefined {
    const c = this.#byKey.get(k.key);
    return c === undefined ? undefined : super.get(c);
  }
  override has(k: Expr): boolean {
    return this.#byKey.has(k.key);
  }
  /** The probability of the value (SymPy FiniteDensity.__call__): 0 for a value that is not taken. */
  call(item: ExprLike): Expr {
    return this.get(sympify(item)) ?? S.Zero;
  }
  /** SymPy FiniteDensity.dict: a plain copy. */
  get dict(): FiniteDensity {
    return new FiniteDensity(this);
  }
}

/** A density: a distribution (callable through `call`), a Lambda, a dict of a finite space, or an unevaluated Density. */
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
} = {};

// ---------------------------------------------------------------------------
// Random domains
// ---------------------------------------------------------------------------

/** SymPy RandomDomain: a set of variables and the values they can take. */
export abstract class RandomDomain extends ExtensionExpr {
  /** SymPy is_ProductDomain. */
  get isProductDomain(): boolean {
    return false;
  }
  /** SymPy is_Finite. */
  get isFinite(): boolean {
    return false;
  }
  /** SymPy is_Continuous. */
  get isContinuous(): boolean {
    return false;
  }
  /** SymPy is_Discrete. */
  get isDiscrete(): boolean {
    return false;
  }
  /** The domain is a SymPy ConditionalDomain. */
  get isConditional(): boolean {
    return false;
  }
  /** The variables of the domain (SymPy symbols, a FiniteSet: sorted). */
  abstract get symbols(): Sym[];
  /** The values the variables take (SymPy set). */
  abstract get set(): SetExpr;
  /** The domain as a condition on its variables (SymPy as_boolean). */
  asBoolean(): Expr {
    throw new NotImplementedError(`as_boolean is not implemented for ${this.name}`);
  }
  /** The expectation of expr over the domain (SymPy compute_expectation). */
  computeExpectation(_expr: Expr, _variables?: readonly Sym[]): Expr {
    throw new NotImplementedError(`compute_expectation is not implemented for ${this.name}`);
  }
  /** SymPy StrPrinter._print_RandomDomain. */
  override printStr(print: (e: Expr) => string): string {
    return `Domain: ${print(this.asBoolean())}`;
  }
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
}

/** SymPy SingleDomain(symbol, set): a single variable and its domain. */
export class SingleDomain extends RandomDomain {
  constructor(args: readonly Expr[], name = 'SingleDomain') {
    super(name, args);
    cast(at(args, 0), Sym, 'domain symbol');
    cast(at(args, 1), SetExpr, 'domain set');
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get symbols(): Sym[] {
    return [this.symbol];
  }
  get set(): SetExpr {
    return cast(at(this.args, 1), SetExpr);
  }
}

/** SymPy ConditionalDomain(fulldomain, condition): a domain with an attached condition. */
export abstract class ConditionalDomain extends RandomDomain {
  override get isConditional(): boolean {
    return true;
  }
  get fulldomain(): RandomDomain {
    return cast(at(this.args, 0), RandomDomain);
  }
  get condition(): Expr {
    return at(this.args, 1);
  }
  get symbols(): Sym[] {
    return this.fulldomain.symbols;
  }
  override asBoolean(): Expr {
    return and(this.fulldomain.asBoolean(), this.condition);
  }
}

/** The condition with its random symbols replaced by their symbols (SymPy ConditionalDomain.__new__). */
export function conditionOnSymbols(condition: Expr): Expr {
  return xreplace(condition, randomSymbols(condition).map((rs) => [rs, rs.symbol] as const));
}

/** SymPy ProductDomain(*domains): a domain resulting from the merger of independent domains. */
export class ProductDomain extends RandomDomain {
  constructor(args: readonly Expr[], name = 'ProductDomain') {
    super(name, args);
  }
  override get isProductDomain(): boolean {
    return true;
  }
  get domains(): RandomDomain[] {
    return this.args.map((d) => cast(d, RandomDomain));
  }
  get symbols(): Sym[] {
    return sortedSymbols(this.domains.flatMap((d) => d.symbols));
  }
  get set(): SetExpr {
    return productSet(...this.domains.map((d) => d.set));
  }
  /** The domain of each symbol (SymPy sym_domain_dict). */
  get symDomainDict(): Map<string, RandomDomain> {
    return new Map(this.domains.flatMap((d) => d.symbols.map((s) => [s.key, d] as const)));
  }
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

/** SymPy PSpace: a probability space. `new PSpace()` is SymPy's PSpace() of a random symbol without a space. */
export class PSpace extends ExtensionExpr {
  constructor(args: readonly Expr[] = [], name = 'PSpace') {
    super(name, args);
  }
  /** SymPy is_Finite. */
  get isFinite(): boolean {
    return false;
  }
  /** SymPy is_Continuous. */
  get isContinuous(): boolean {
    return false;
  }
  /** SymPy is_Discrete. */
  get isDiscrete(): boolean {
    return false;
  }
  /** SymPy is_real (None for the generic space). */
  get isReal(): boolean {
    return false;
  }
  /** The space is a SymPy SinglePSpace (one variable with a distribution). */
  get isSingle(): boolean {
    return false;
  }
  /** The space is a SymPy CompoundPSpace. */
  get isCompound(): boolean {
    return false;
  }
  get domain(): RandomDomain {
    return cast(at(this.args, 0), RandomDomain, 'domain');
  }
  get density(): Expr {
    return at(this.args, 1);
  }
  /** The random symbols of the space (SymPy values, a frozenset). */
  get values(): RandomSymbol[] {
    return this.symbols.map((s) => new RandomSymbol(s, this));
  }
  get symbols(): Sym[] {
    return this.domain.symbols;
  }
  /** The probability density of the space as an expression of its symbols (SymPy pdf). */
  get pdf(): Expr {
    throw new NotImplementedError(`pdf is not implemented for ${this.name}`);
  }
  where(_condition: Expr): RandomDomain {
    throw new NotImplementedError(`where is not implemented for ${this.name}`);
  }
  computeDensity(_expr: Expr, _opts?: ComputeOptions): DensityResult {
    throw new NotImplementedError(`compute_density is not implemented for ${this.name}`);
  }
  probability(_condition: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`probability is not implemented for ${this.name}`);
  }
  computeExpectation(_expr: Expr, _rvs?: readonly RandomSymbol[], _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_expectation is not implemented for ${this.name}`);
  }
  computeCdf(_expr: Expr, _opts?: ComputeOptions): DensityResult {
    throw new NotImplementedError(`compute_cdf is not implemented for ${this.name}`);
  }
  computeCharacteristicFunction(_expr: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_characteristic_function is not implemented for ${this.name}`);
  }
  computeMomentGeneratingFunction(_expr: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_moment_generating_function is not implemented for ${this.name}`);
  }
  computeQuantile(_expr: Expr, _opts?: ComputeOptions): Expr {
    throw new NotImplementedError(`compute_quantile is not implemented for ${this.name}`);
  }
  conditionalSpace(_condition: Expr, _opts?: ComputeOptions): PSpace {
    throw new NotImplementedError(`conditional_space is not implemented for ${this.name}`);
  }
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
}

/** Options of the computations of a probability space (SymPy keyword arguments). */
export interface ComputeOptions {
  /** false: integrals and sums are left unevaluated (SymPy evaluate=False). */
  readonly evaluate?: boolean;
  /** CompoundPSpace: the marginalised density is evaluated (SymPy compound_evaluate). */
  readonly compoundEvaluate?: boolean;
}

/** The symbol of a probability space or random symbol, from a name (SymPy _symbol_converter). */
export function symbolConverter(sym: string | Expr): Sym {
  if (typeof sym === 'string') return new Sym(sym);
  if (!(sym instanceof Sym)) throw new TypeError(`${sym.toString()} is neither a Symbol nor a string`);
  return sym;
}

/** SymPy SinglePSpace(s, distribution): a space of one variable with a distribution. */
export class SinglePSpace extends PSpace {
  constructor(args: readonly Expr[], name = 'SinglePSpace') {
    super([symbolConverter(at(args, 0)), at(args, 1)], name);
  }
  override get isSingle(): boolean {
    return true;
  }
  /** The random symbol of the space (SymPy value). */
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get distribution(): Distribution {
    return cast(at(this.args, 1), Distribution, 'distribution');
  }
  override get pdf(): Expr {
    return this.distribution.pdf(this.symbol);
  }
}

/** The members of a single probability space (SymPy SinglePSpace, which the spaces of the other modules also derive from). */
export interface SingleSpace {
  readonly symbol: Sym;
  readonly distribution: Distribution;
  readonly value: RandomSymbol;
}

/** The space is a single space (SymPy isinstance(space, SinglePSpace)). */
export function isSingleSpace(ps: PSpace): ps is PSpace & SingleSpace {
  return ps.isSingle;
}

/** SymPy RandomSymbol(symbol, pspace): a symbol whose values are distributed as its probability space says. */
export class RandomSymbol extends Sym {
  readonly symbol: Sym;
  readonly pspace: PSpace;
  constructor(symbol: string | Sym, pspace: PSpace = new PSpace()) {
    const s = symbolConverter(symbol);
    if (!(pspace instanceof PSpace)) throw new TypeError('pspace variable should be of type PSpace');
    // SymPy: is_positive and is_integer are the symbol's, is_real also holds when the space is real
    const a: Assumptions = { ...s.assumptions, ...(pspace.isReal ? { real: true } : {}) };
    super(s.name, a);
    this.symbol = s;
    this.pspace = pspace;
  }
  /** Sorted as SymPy's RandomSymbol, a Basic (class key (5, 0, 'RandomSymbol')). */
  override get sortClass(): string {
    return 'RandomSymbol';
  }
  override get sortPriority(): number {
    return 5;
  }
  /** Substitution reaches the probability space (SymPy subs traverses the arguments (symbol, pspace)). */
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
  /** SymPy has: the symbol and the probability space are arguments. */
  override has(sub: Expr): boolean {
    return super.has(sub) || this.pspace.has(sub);
  }
  protected override computeKey(): string {
    return `RandomSymbol(${this.symbol.key};${this.pspace.key})`;
  }
}

/** SymPy ProductPSpace: a probability space with several random variables. */
export class ProductPSpace extends PSpace {}

/**
 * SymPy IndependentProductPSpace(*spaces): the merger of independent
 * probability spaces. Use `independentProductPSpace` to build one (finite
 * spaces give a ProductFinitePSpace).
 */
export class IndependentProductPSpace extends ProductPSpace {
  constructor(args: readonly Expr[], name = 'IndependentProductPSpace') {
    super(args, name);
  }
  override get pdf(): Expr {
    const p = mul(...this.spaces.map((s) => s.pdf));
    return xreplace(p, this.values.map((rv) => [rv, rv.symbol] as const));
  }
  /** The space of each random symbol (SymPy rs_space_dict). */
  get rsSpaceDict(): Map<string, [RandomSymbol, PSpace]> {
    return new Map(this.spaces.flatMap((sp) => sp.values.map((v) => [v.key, [v, sp]] as const)));
  }
  override get symbols(): Sym[] {
    return sortedSymbols([...this.rsSpaceDict.values()].map(([v]) => v.symbol));
  }
  get spaces(): PSpace[] {
    return this.args.map((a) => cast(a, PSpace));
  }
  override get values(): RandomSymbol[] {
    return [...this.rsSpaceDict.values()].map(([v]) => v);
  }
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
  override get domain(): RandomDomain {
    return makeProductDomain(this.spaces.map((s) => s.domain));
  }
  override get density(): Expr {
    throw new NotImplementedError('Density not available for ProductSpaces');
  }
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
  override computeDensity(expr: Expr, opts: ComputeOptions = {}): DensityResult {
    const rvs = randomSymbols(expr);
    if (rvs.some((rv) => pspace(rv).isContinuous)) {
      const z = new Dummy('z', { real: true });
      return Lambda(z, this.computeExpectation(DiracDelta(add(expr, mul(-1, z))), undefined, opts));
    }
    const z = new Dummy('z', { integer: true });
    return Lambda(z, this.computeExpectation(KroneckerDelta(expr, z), undefined, opts));
  }
  override computeCdf(_expr: Expr): DensityResult {
    throw new RangeError('CDF not well defined on multivariate expressions');
  }
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
  const counted = spaces.filter((s) => !s.isCompound).reduce((n, s) => n + s.symbols.length, 0);
  if (symbols.size < counted) throw new RangeError('Overlapping Random Variables');
  if (spaces.every((s) => s.isFinite)) return defined(statsClasses.productFinitePSpace, 'frv')(spaces);
  return new IndependentProductPSpace(spaces);
}

// ---------------------------------------------------------------------------
// Distributions
// ---------------------------------------------------------------------------

/** SymPy Distribution: the base class of the distributions (an expression node of its parameters). */
export abstract class Distribution extends ExtensionExpr {
  /** The probability density (or mass) function at x (SymPy pdf). */
  abstract pdf(x: ExprLike): Expr;
  /** The values the distribution takes (SymPy set). */
  abstract get set(): SetExpr;
  /** The distribution is a SymPy SingleFiniteDistribution. */
  get isFinite(): boolean {
    return false;
  }
  /** The values and their probabilities of a finite distribution (SymPy SingleFiniteDistribution.dict). */
  get dict(): DensityResult {
    throw new NotImplementedError(`${this.name} is not a finite distribution`);
  }
  /** SymPy __call__: the density at x. */
  call(x: ExprLike): Expr {
    return this.pdf(x);
  }
  /** The parameter at index i (SymPy NamedArgsMixin). */
  protected arg(i: number): Expr {
    return at(this.args, i);
  }
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

/** All random symbols of an expression, sorted by name (SymPy random_symbols). */
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

/** The probability space of a random expression (SymPy pspace). */
export function pspace(exprIn: ExprLike | readonly Expr[]): PSpace {
  const expr = isExprArray(exprIn) ? new TupleNode(exprIn) : sympify(exprIn);
  if (expr instanceof RandomSymbol) return expr.pspace;
  const rvs = randomSymbols(expr);
  if (!rvs.length) throw new RangeError(`Expression containing Random Variable expected, not ${expr.toString()}`);
  const p0 = first(rvs).pspace;
  // if only one space present
  if (rvs.every((rv) => rv.pspace.key === p0.key)) return p0;
  const compound = rvs.find((rv) => rv.pspace.isCompound);
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
 * Conditional random expression (SymPy given): the expression on the
 * probability space conditioned on the condition. A random symbol as the
 * condition is considered fixed.
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
  /** false: integrals and sums are left unevaluated (SymPy evaluate=False). */
  readonly evaluate?: boolean;
}

/** The expected value of a random expression, optionally given a condition (SymPy E, expectation). */
export function expectation(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const e = sympify(expr);
  // expr isn't random
  if (!isRandom(e)) return e;
  return defined(statsClasses.expectation, 'stats symbolic_probability')(e, condition === undefined ? undefined : sympify(condition), opts.evaluate ?? true);
}

/** The probability that a condition is true, optionally given a second condition (SymPy P, probability). */
export function P(condition: ExprLike | boolean, givenCondition?: ExprLike | boolean, opts: ProbabilityOptions = {}): Expr {
  const c = typeof condition === 'boolean' ? (condition ? S.true : S.false) : sympify(condition);
  const g = givenCondition === undefined ? undefined : typeof givenCondition === 'boolean' ? (givenCondition ? S.true : S.false) : sympify(givenCondition);
  return defined(statsClasses.probability, 'stats symbolic_probability')(c, g, opts.evaluate ?? true);
}

/** SymPy Density(expr, condition): the unevaluated density of a random expression. */
export class Density extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Density', args);
  }
  get expr(): Expr {
    return at(this.args, 0);
  }
  get condition(): Expr | undefined {
    return this.args[1];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Density(args);
  }
  /** The density (SymPy Density.doit). */
  compute(opts: ComputeOptions = {}): DensityResult {
    let expr = this.expr;
    const condition = this.condition;
    if (expr instanceof Distribution && expr.isFinite) return expr.dict;
    if (condition !== undefined) expr = given(expr, condition, opts);
    if (!randomSymbols(expr).length) return Lambda(xGlobal, DiracDelta(add(xGlobal, mul(-1, expr))));
    if (expr instanceof RandomSymbol && isSingleSpace(expr.pspace) && !expr.pspace.isCompound) return expr.pspace.distribution;
    const ps = pspace(expr);
    const result = ps.computeDensity(expr, ps.isCompound ? { ...opts, compoundEvaluate: opts.evaluate ?? true } : opts);
    return (opts.evaluate ?? true) && result instanceof Expr ? doit(result) : result;
  }
  /** SymPy doit: the density, when it is an expression (a finite space gives a dict: see `compute`). */
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
 * The probability density of a random expression, optionally given a
 * condition (SymPy density): a distribution for a random symbol (callable
 * through `call`), a dict for a finite space, a Lambda otherwise.
 */
export function density(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): DensityResult {
  return makeDensity(expr, condition).compute({ evaluate: opts.evaluate ?? true });
}

/** A result that is an expression is evaluated (SymPy `if evaluate and hasattr(result, 'doit')`). */
const evaluated = (r: DensityResult, evaluate: boolean): DensityResult => (evaluate && r instanceof Expr ? doit(r) : r);

/** The cumulative distribution function of a random expression, optionally given a condition (SymPy cdf). */
export function cdf(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): DensityResult {
  // recompute on the conditional expression
  if (condition !== undefined) return cdf(given(expr, condition), undefined, opts);
  const e = sympify(expr);
  return evaluated(pspace(e).computeCdf(e, {}), opts.evaluate ?? true);
}

/** The characteristic function of a random expression, optionally given a condition: a Lambda (SymPy characteristic_function). */
export function characteristicFunction(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  if (condition !== undefined) return characteristicFunction(given(expr, condition), undefined, opts);
  const e = sympify(expr);
  const r = pspace(e).computeCharacteristicFunction(e);
  return opts.evaluate ?? true ? doit(r) : r;
}

/** The moment generating function of a random expression, optionally given a condition: a Lambda (SymPy moment_generating_function). */
export function momentGeneratingFunction(expr: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  if (condition !== undefined) return momentGeneratingFunction(given(expr, condition), undefined, opts);
  const e = sympify(expr);
  const r = pspace(e).computeMomentGeneratingFunction(e);
  return opts.evaluate ?? true ? doit(r) : r;
}

/** The domain where a condition is true, optionally given a second condition (SymPy where). */
export function where(condition: ExprLike, givenCondition?: ExprLike): RandomDomain {
  if (givenCondition !== undefined) return where(given(condition, givenCondition));
  const c = sympify(condition);
  return pspace(c).where(c);
}

/** The quantile function of a random expression: a Lambda (SymPy quantile). */
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

/** The random expressions are dependent (SymPy dependent). */
export function dependent(a: ExprLike, b: ExprLike): boolean {
  const ea = sympify(a);
  const eb = sympify(b);
  if (pspaceIndependent(ea, eb) === true) return false;
  const z = new Sym('z', { real: true });
  return !sameDensity(density(ea, Eq(eb, z)), density(ea)) || !sameDensity(density(eb, Eq(ea, z)), density(eb));
}

/** The random expressions are independent (SymPy independent). */
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
  const rb = new Set(randomSymbols(b).map((r) => r.key));
  if (randomSymbols(a).some((r) => rb.has(r.key))) return false;
  if (!bSymbols.some((k) => aSymbols.has(k))) return true;
  return 'unknown';
}

