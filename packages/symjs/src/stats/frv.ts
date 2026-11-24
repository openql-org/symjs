// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/frv.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.frv: finite random variables, which take finitely
 * many values: densities are dicts, expectations and probabilities are
 * sums over the elements of the domain.
 *
 * An element of a finite domain is an assignment of values to the
 * symbols (SymPy frozenset({(symbol, value), ...})); as a key of a density
 * it is the FiniteSet of the (symbol, value) Tuples.
 */

import { BoolAtom, Dummy, Expr, Rational, Rel, S, Sym } from '../core/nodes';
import { gcd } from '../core/numbers';
import type { ExprLike } from '../core/nodes';
import { add, exp, mul, sympify } from '../core/ops';
import { Eq, Ge, Le, Lt, Gt, piecewise } from '../core/logic';
import { BoolOp, and, or } from '../core/boolalg';
import { Sum } from '../core/concrete';
import { xreplace } from '../core/traverse';
import { Lambda, LambdaNode } from '../core/lambda';
import { TupleNode } from '../core/containers';
import { DictNode, Dict } from '../core/containers';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, first } from '../core/guard';
import { FiniteSet, SetExpr, finiteSet } from '../sets/sets';
import { compareKeys, sortKey } from '../printing/sortkey';
import { cmpReal } from '../sets/sets';
import { doit } from '../calculus/doit';
import {
  ConditionalDomain,
  Density,
  Distribution,
  FiniteDensity,
  IndependentProductPSpace,
  PSpace,
  ProductDomain,
  RandomDomain,
  RandomSymbol,
  makeProductDomain,
  randomSymbols,
  rvSubs,
  statsClasses,
  symbolConverter,
} from './rv';
import type { DensityResult } from './rv';

/** An element of a finite domain: the value of each symbol (SymPy frozenset of (symbol, value) pairs). */
export type FiniteElement = readonly (readonly [Sym, Expr])[];

/** The element as the key of a density (SymPy FiniteSet((symbol, value), ...)). */
export function elementKey(elem: FiniteElement): Expr {
  return finiteSet(...elem.map(([s, v]) => new TupleNode([s, v])));
}

/** The pairs of an element key. */
function elementOf(key: Expr): FiniteElement {
  return cast(key, FiniteSet, 'element').args.map((t) => [cast(at(t.args, 0), Sym), at(t.args, 1)] as const);
}

/** The value of an expression at an element (SymPy expr.xreplace(dict(elem))). */
const at_ = (expr: Expr, elem: FiniteElement): Expr => xreplace(expr, elem);

// ---------------------------------------------------------------------------
// Domains
// ---------------------------------------------------------------------------

/** The elements as a FiniteSet of Dicts (SymPy FiniteDomain.dict). */
const elementsDict = (els: readonly FiniteElement[]): SetExpr => finiteSet(...els.map((el) => Dict(el.map(([s, v]) => [s, v] as const))));

/** The elements as a disjunction of conjunctions of equations (SymPy FiniteDomain.as_boolean). */
const elementsBoolean = (els: readonly FiniteElement[]): Expr => or(...els.map((item) => and(...item.map(([s, v]) => Eq(s, v)))));

/**
 * A domain of finitely many elements.
 *
 * @see SymPy `sympy.stats.frv.FiniteDomain`
 */
export abstract class FiniteDomain extends RandomDomain {
  /**
   * Indicates whether the outcome domain is finite.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.frv.FiniteDomain.is_Finite`
   */
  override get isFinite(): boolean {
    return true;
  }
  /**
   * Iterates over the elements of the domain.
   *
   * @returns The elements.
   * @see SymPy `sympy.stats.frv.FiniteDomain.elements`
   */
  abstract elements(): FiniteElement[];
  /**
   * Represents the finite domain's assignments as dictionaries.
   *
   * @returns A set of assignment dictionaries.
   * @see SymPy `sympy.stats.frv.FiniteDomain.dict`
   */
  get dict(): SetExpr {
    return elementsDict(this.elements());
  }
  /**
   * Tests whether the assignment belongs to the domain.
   *
   * @param other - Other operand.
   * @returns Whether the assignment is an element of this domain.
   */
  containsElement(other: FiniteElement): boolean {
    const k = elementKey(other).key;
    return this.elements().some((e) => elementKey(e).key === k);
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.frv.FiniteDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return elementsBoolean(this.elements());
  }
}

/**
 * A finite variable and its values.
 *
 * @see SymPy `sympy.stats.frv.SingleFiniteDomain`
 */
export class SingleFiniteDomain extends FiniteDomain {
  /**
   * Constructs a new `SingleFiniteDomain`.
   *
   * @param args - Operands in the order `symbol`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super('SingleFiniteDomain', [cast(at(args, 0), Sym, 'domain symbol'), cast(at(args, 1), SetExpr, 'domain set')]);
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.frv.SingleFiniteDomain.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the symbols whose assignments determine an outcome.
   *
   * @returns The domain symbols.
   * @see SymPy `sympy.stats.frv.SingleFiniteDomain.symbols`
   */
  get symbols(): Sym[] {
    return [this.symbol];
  }
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @see SymPy `sympy.stats.frv.SingleFiniteDomain.set`
   */
  override get set(): SetExpr {
    return cast(at(this.args, 1), SetExpr);
  }
  /**
   * Enumerates the assignments of values to symbols in the finite domain.
   *
   * @returns The possible assignments.
   * @see SymPy `sympy.stats.frv.SingleFiniteDomain.elements`
   */
  elements(): FiniteElement[] {
    return cast(this.set, FiniteSet, 'finite set').args.map((v) => [[this.symbol, v] as const]);
  }
}

/**
 * The Cartesian product of finite domains.
 *
 * @see SymPy `sympy.stats.frv.ProductFiniteDomain`
 */
export class ProductFiniteDomain extends ProductDomain {
  /**
   * Constructs a new `ProductFiniteDomain`.
   *
   * @param args - Operands in the order `domains`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'ProductFiniteDomain') {
    super(args, name);
  }
  /**
   * Indicates whether the outcome domain is finite.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.frv.ProductFiniteDomain.is_Finite`
   */
  override get isFinite(): boolean {
    return true;
  }
  /**
   * Forms joint assignments by combining one assignment from each component domain.
   *
   * @returns The product-domain elements.
   * @see SymPy `sympy.stats.frv.ProductFiniteDomain.elements`
   */
  elements(): FiniteElement[] {
    let out: FiniteElement[] = [[]];
    for (const d of this.domains) {
      const els = cast(d, FiniteDomain, 'finite domain').elements();
      out = out.flatMap((acc) => els.map((el) => [...acc, ...el]));
    }
    return out;
  }
  /**
   * Represents the finite domain's assignments as dictionaries.
   *
   * @returns A set of assignment dictionaries.
   * @see SymPy `sympy.stats.frv.ProductFiniteDomain.dict`
   */
  get dict(): SetExpr {
    return elementsDict(this.elements());
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.frv.ProductFiniteDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return elementsBoolean(this.elements());
  }
}

/** The elements of a finite domain, product or not. */
export function finiteElements(d: RandomDomain): FiniteElement[] {
  if (d instanceof FiniteDomain || d instanceof ProductFiniteDomain || d instanceof ConditionalFiniteDomain) return d.elements();
  throw new TypeError(`${d.name} is not a finite domain`);
}

/**
 * The elements of the domain where the condition holds.
 *
 * @see SymPy `sympy.stats.frv.ConditionalFiniteDomain`
 */
export class ConditionalFiniteDomain extends ConditionalDomain {
  /**
   * Constructs a new `ConditionalFiniteDomain`.
   *
   * @param args - Operands in the order `domain`, `condition`.
   */
  constructor(args: readonly Expr[]) {
    super('ConditionalFiniteDomain', [at(args, 0), rvSubs(at(args, 1))]);
  }
  /**
   * Indicates whether the outcome domain is finite.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.frv.ConditionalFiniteDomain.is_Finite`
   */
  override get isFinite(): boolean {
    return true;
  }
  /**
   * Checks whether the assignment satisfies the conditioning event.
   *
   * @param elem - Domain element to test.
   * @returns Whether the assignment satisfies the condition.
   * @throws RangeError when the condition cannot be decided at the given outcome.
   */
  test(elem: FiniteElement): boolean {
    const val = at_(this.condition, elem);
    if (val instanceof BoolAtom) return val.value;
    if (val instanceof Rel && val.op === 'Eq') return val.lhs.key === val.rhs.key;
    throw new RangeError(`Undecidable if ${val.toString()}`);
  }
  /**
   * Enumerates the assignments of values to symbols in the finite domain.
   *
   * @returns The possible assignments.
   * @see SymPy `sympy.stats.frv.ConditionalFiniteDomain.elements`
   */
  elements(): FiniteElement[] {
    return finiteElements(this.fulldomain).filter((e) => this.test(e));
  }
  /**
   * Represents the finite domain's assignments as dictionaries.
   *
   * @returns A set of assignment dictionaries.
   * @see SymPy `sympy.stats.frv.ConditionalFiniteDomain.dict`
   */
  get dict(): SetExpr {
    return elementsDict(this.elements());
  }
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @throws NotImplementedError when the conditional domain is multidimensional.
   * @see SymPy `sympy.stats.frv.ConditionalFiniteDomain.set`
   */
  override get set(): SetExpr {
    const full = this.fulldomain;
    if (full instanceof SingleFiniteDomain) return finiteSet(...this.elements().map((el) => at(first(el), 1)));
    throw new NotImplementedError('Not implemented on multi-dimensional conditional domain');
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.frv.ConditionalFiniteDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return elementsBoolean(this.elements());
  }
}

/** SymPy ConditionalFiniteDomain(domain, condition): the domain itself for a true condition. */
export function conditionalFiniteDomain(domain: RandomDomain, condition: Expr): RandomDomain {
  if (condition === S.true) return domain;
  return new ConditionalFiniteDomain([domain, condition]);
}

// ---------------------------------------------------------------------------
// Distributions
// ---------------------------------------------------------------------------

/**
 * A distribution of finitely many values.
 *
 * @see SymPy `sympy.stats.frv.SingleFiniteDistribution`
 * @example
 * ```ts
 * import { DieDistribution, ex } from '@symjs/symjs';
 *
 * const law = new DieDistribution([ex`6`]);
 * law.pmf(2); // => 1/6
 * ```
 */
export abstract class SingleFiniteDistribution extends Distribution {
  /**
   * Indicates whether the distribution has finite support.
   *
   * @returns `true` for this distribution.
   */
  override get isFinite(): boolean {
    return true;
  }
  /**
   * Checks the parameters.
   *
   * @see SymPy `sympy.stats.frv.SingleFiniteDistribution.check`
   */
  check(): void {}
  /**
   * Indicates whether the number of possible values is symbolic.
   *
   * @returns `false` for this distribution.
   * @see SymPy `sympy.stats.frv.SingleFiniteDistribution.is_symbolic`
   */
  get isSymbolic(): boolean {
    return false;
  }
  /**
   * Specifies the lower outcome bound for a symbolic number of outcomes.
   *
   * @returns The lower bound.
   * @throws NotImplementedError when the distribution does not define a lower endpoint.
   */
  get low(): Expr {
    throw new NotImplementedError(`${this.name} has no low value`);
  }
  /**
   * Specifies the upper outcome bound for a symbolic number of outcomes.
   *
   * @returns The upper bound.
   * @throws NotImplementedError when the distribution does not define an upper endpoint.
   */
  get high(): Expr {
    throw new NotImplementedError(`${this.name} has no high value`);
  }
  /**
   * Collects all possible outcomes of the distribution.
   *
   * @returns The support set.
   * @see SymPy `sympy.stats.frv.SingleFiniteDistribution.set`
   */
  abstract override get set(): SetExpr;
  /**
   * Evaluates the probability mass at the specified outcome.
   *
   * @param x - Outcome at which to evaluate the probability mass.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv.SingleFiniteDistribution.pmf`
   */
  abstract pmf(x: ExprLike): Expr;
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @param x - Outcome at which to evaluate the probability mass.
   * @returns The outcome probability.
   */
  pdf(x: ExprLike): Expr {
    return this.pmf(x);
  }
  /**
   * Associates values with probabilities, retaining a symbolic density when the outcomes cannot be
   * enumerated.
   *
   * @returns The finite density or unevaluated density expression.
   * @see SymPy `sympy.stats.frv.SingleFiniteDistribution.dict`
   */
  override get dict(): DensityResult {
    if (this.isSymbolic) return new Density([this]);
    return new FiniteDensity(cast(this.set, FiniteSet, 'values').args.map((k) => [k, this.pmf(k)] as const));
  }
  /**
   * Tests whether the value belongs to the distribution's support.
   *
   * @param other - Other operand.
   * @returns Whether the value is in the support.
   */
  containsValue(other: ExprLike): boolean {
    const k = sympify(other).key;
    return cast(this.set, FiniteSet).args.some((a) => a.key === k);
  }
}

/** The items (value, probability) of a finite distribution's dict. */
function distItems(d: SingleFiniteDistribution): (readonly [Expr, Expr])[] {
  return [...cast(d.dict, FiniteDensity, 'dict of a finite distribution')];
}

// ---------------------------------------------------------------------------
// Probability spaces
// ---------------------------------------------------------------------------

/**
 * A finite probability space. The
 * density maps elements (or, for the space of one distribution, values) to
 * probabilities.
 *
 * @see SymPy `sympy.stats.frv.FinitePSpace`
 */
export class FinitePSpace extends PSpace {
  /**
   * Constructs a new `FinitePSpace`.
   *
   * @param args - Operands in the order `domain`, `density`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'FinitePSpace') {
    super(args, name);
  }
  /**
   * Indicates whether this probability space has finitely many outcomes.
   *
   * @returns `true` for this space.
   * @see SymPy `sympy.stats.frv.FinitePSpace.is_Finite`
   */
  override get isFinite(): boolean {
    return true;
  }
  /**
   * Pairs each value of the distribution with its probability mass.
   *
   * @returns The outcome–probability entries.
   */
  get densityItems(): (readonly [Expr, Expr])[] {
    const d = this.density;
    return d instanceof DictNode ? d.items() : distItems(cast(d, SingleFiniteDistribution, 'density'));
  }
  #probabilities?: { mass: FiniteDensity; elementKeys: boolean };
  /**
   * Retrieves the mass of the specified assignment of values to random symbols.
   *
   * @param elem - Domain element to test.
   * @returns The assignment probability.
   * @see SymPy `sympy.stats.frv.FinitePSpace.prob_of`
   */
  probOf(elem: FiniteElement): Expr {
    // A finite space is immutable. Index its mass function once for all outcomes of an expectation.
    if (!this.#probabilities) {
      const items = this.densityItems;
      this.#probabilities = { mass: new FiniteDensity(items), elementKeys: items[0]?.[0] instanceof FiniteSet };
    }
    const { mass, elementKeys } = this.#probabilities;
    return mass.call(elementKeys ? elementKey(elem) : at(first(elem), 1));
  }
  /**
   * Restricts the domain to the subset satisfying the condition.
   *
   * @param condition - Condition on the random variables.
   * @returns The domain satisfying the condition.
   * @see SymPy `sympy.stats.frv.FinitePSpace.where`
   */
  override where(condition: Expr): RandomDomain {
    return conditionalFiniteDomain(this.domain, condition);
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param exprIn - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @see SymPy `sympy.stats.frv.FinitePSpace.compute_density`
   */
  override computeDensity(exprIn: Expr): DensityResult {
    const expr = rvSubs(exprIn, this.values);
    const d = new FiniteDensity();
    for (const elem of finiteElements(this.domain)) {
      const val = at_(expr, elem);
      d.set(val, add(d.get(val) ?? S.Zero, this.probOf(elem)));
    }
    return d;
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The cumulative distribution function.
   * @see SymPy `sympy.stats.frv.FinitePSpace.compute_cdf`
   */
  override computeCdf(expr: Expr): DensityResult {
    const d = cast(this.computeDensity(expr), FiniteDensity);
    let cum: Expr = S.Zero;
    const out = new FiniteDensity();
    for (const key of sortedKeys([...d.keys()])) {
      cum = add(cum, defined(d.get(key)));
      out.set(key, cum);
    }
    return out;
  }
  /**
   * Orders the cumulative distribution entries by cumulative probability.
   *
   * @param expr - Expression to evaluate.
   * @returns The sorted value–probability pairs.
   * @see SymPy `sympy.stats.frv.FinitePSpace.sorted_cdf`
   */
  sortedCdf(expr: Expr): (readonly [Expr, Expr])[] {
    const items = [...cast(this.computeCdf(expr), FiniteDensity)];
    return items.sort((a, b) => defined(cmpReal(a[1], b[1])));
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The characteristic function.
   * @see SymPy `sympy.stats.frv.FinitePSpace.compute_characteristic_function`
   */
  override computeCharacteristicFunction(expr: Expr): Expr {
    const d = cast(this.computeDensity(expr), FiniteDensity);
    const t = new Dummy('t', { real: true });
    return Lambda(t, add(...[...d].map(([k, v]) => mul(exp(mul(S.I, k, t)), v))));
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param expr - Expression to evaluate.
   * @returns The moment generating function.
   * @see SymPy `sympy.stats.frv.FinitePSpace.compute_moment_generating_function`
   */
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    const d = cast(this.computeDensity(expr), FiniteDensity);
    const t = new Dummy('t', { real: true });
    return Lambda(t, add(...[...d].map(([k, v]) => mul(exp(mul(k, t)), v))));
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvsIn - Random variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @see SymPy `sympy.stats.frv.FinitePSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[]): Expr {
    const rvs = rvsIn?.length ? rvsIn : this.values;
    const expr = rvSubs(exprIn, rvs);
    const elements = finiteElements(this.domain);
    const isBool = expr instanceof Rel || expr instanceof BoolOp || expr instanceof BoolAtom;
    let numerator = 0n;
    let denominator = 1n;
    const terms: Expr[] = [];
    for (const elem of elements) {
      const prob = this.probOf(elem);
      const value = isBool ? at(first(elem), 1) : at_(expr, elem);
      const condition = isBool ? at_(expr, elem) : S.true;
      if (condition === S.true && value instanceof Rational && prob instanceof Rational) {
        // Keep a common denominator and reduce the exact contribution once after summing the support.
        const termDenominator = value.q * prob.q;
        const common = gcd(denominator, termDenominator);
        const scale = termDenominator / common;
        numerator = numerator * scale + value.p * prob.p * (denominator / common);
        denominator *= scale;
      } else {
        terms.push(piecewise([mul(prob, value), condition], [S.Zero, true]));
      }
    }
    return add(Rational.of(numerator, denominator), ...terms);
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The quantile function.
   * @see SymPy `sympy.stats.frv.FinitePSpace.compute_quantile`
   */
  override computeQuantile(expr: Expr): Expr {
    const c = cast(this.computeCdf(expr), FiniteDensity);
    const p = new Dummy('p', { real: true });
    const pairs: [Expr, Expr][] = [[S.NaN, or(Lt(p, 0), Gt(p, 1))]];
    for (const [key, value] of c) pairs.push([key, Le(p, value)]);
    return Lambda(p, piecewise(...pairs));
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param condition - Condition on the random variables.
   * @returns The probability of the event.
   * @throws RangeError when the event contains random symbols outside this space.
   * @see SymPy `sympy.stats.frv.FinitePSpace.probability`
   */
  override probability(condition: Expr): Expr {
    const condSymbols = randomSymbols(condition).map((rs) => rs.symbol);
    const cond = rvSubs(condition);
    const mine = new Set(this.symbols.map((s) => s.key));
    const foreign = condSymbols.filter((s) => !mine.has(s.key));
    if (foreign.length) throw new RangeError(`Cannot compare foreign random symbols, ${foreign.map((s) => s.name).join(', ')}`);
    const domainFree = new Set([...this.domain.freeSymbols()].map((s) => s.key));
    if (cond instanceof Rel && [...cond.freeSymbols()].some((s) => !domainFree.has(s.key))) {
      // the side that is the random symbol takes the values (SymPy takes the left side when the right one is a
      // Symbol, and the right one otherwise: P(Eq(B, b + 1)) would substitute for b + 1 and leave B)
      const rv = mine.has(cond.rhs.key) ? cond.rhs : cond.lhs;
      return add(...finiteElements(this.domain).map((elem) => piecewise([this.probOf(elem), cond.subs(rv, at(first(elem), 1))], [S.Zero, true])));
    }
    return add(...finiteElements(this.where(condition)).map((elem) => this.probOf(elem)));
  }
  /**
   * Restricts the probability space to outcomes that satisfy the condition.
   *
   * @param condition - Condition on the random variables.
   * @returns The conditioned probability space.
   * @see SymPy `sympy.stats.frv.FinitePSpace.conditional_space`
   */
  override conditionalSpace(condition: Expr): PSpace {
    const domain = this.where(condition);
    const prob = this.probability(condition);
    const test = (key: Expr): boolean => !(domain instanceof ConditionalFiniteDomain) || domain.test(elementOf(key));
    const items = this.densityItems.filter(([key]) => test(key)).map(([key, val]) => [key, mul(val, prob.pow(-1))] as const);
    return new FinitePSpace([domain, Dict(items)]);
  }
}

/** Keys in Python's sorted() order: numbers by value, otherwise by sort key. */
function sortedKeys(keys: readonly Expr[]): Expr[] {
  return [...keys].sort((a, b) => cmpReal(a, b) ?? compareKeys(sortKey(a), sortKey(b)));
}

/**
 * A finite random variable with a distribution.
 *
 * @see SymPy `sympy.stats.frv.SingleFinitePSpace`
 */
export class SingleFinitePSpace extends FinitePSpace {
  /**
   * Constructs a new `SingleFinitePSpace`.
   *
   * @param args - Operands in the order `s`, `distribution`.
   */
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), SingleFiniteDistribution, 'distribution')], 'SingleFinitePSpace');
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
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the law of the random variable in this space.
   *
   * @returns The distribution object.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.distribution`
   */
  get distribution(): SingleFiniteDistribution {
    return cast(at(this.args, 1), SingleFiniteDistribution);
  }
  /**
   * Constructs the random symbol associated with this probability space.
   *
   * @returns The space's random variable.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.value`
   */
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.domain`
   */
  override get domain(): RandomDomain {
    return new SingleFiniteDomain([this.symbol, this.distribution.set]);
  }
  /**
   * Evaluates the probability mass function at one outcome.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.pdf`
   */
  override get pdf(): Expr {
    return this.distribution.pmf(this.symbol);
  }
  /**
   * Evaluates the probability mass function at the given expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability of the supplied outcome.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.pmf`
   */
  pmf(expr: ExprLike): Expr {
    return this.distribution.pmf(expr);
  }
  /**
   * Lists the mass associated with each finite outcome.
   *
   * @returns The outcome–probability pairs.
   */
  override get densityItems(): (readonly [Expr, Expr])[] {
    return distItems(this.distribution).map(([val, prob]) => [elementKey([[this.symbol, val]]), prob] as const);
  }
  /** The finite space of the distribution (SymPy FinitePSpace(self.domain, self.distribution)). */
  #plain(): FinitePSpace {
    return new FinitePSpace([this.domain, this.distribution]);
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The characteristic function.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.compute_characteristic_function`
   */
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (this.distribution.isSymbolic) {
      const d = cast(this.computeDensity(expr), Expr);
      const t = new Dummy('t', { real: true });
      const ki = new Dummy('ki');
      return Lambda(t, Sum(mul(callLambda(d, ki), exp(mul(S.I, ki, t))), [ki, this.distribution.low, this.distribution.high]));
    }
    return this.#plain().computeCharacteristicFunction(rvSubs(expr, this.values));
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param expr - Expression to evaluate.
   * @returns The moment generating function.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.compute_moment_generating_function`
   */
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (this.distribution.isSymbolic) {
      const d = cast(this.computeDensity(expr), Expr);
      const t = new Dummy('t', { real: true });
      const ki = new Dummy('ki');
      return Lambda(t, Sum(mul(callLambda(d, ki), exp(mul(ki, t))), [ki, this.distribution.low, this.distribution.high]));
    }
    return this.#plain().computeMomentGeneratingFunction(rvSubs(expr, this.values));
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The quantile function.
   * @throws NotImplementedError when the size of the distribution is symbolic.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.compute_quantile`
   */
  override computeQuantile(expr: Expr): Expr {
    if (this.distribution.isSymbolic) {
      throw new NotImplementedError(
        'Computing quantile for random variables with symbolic dimension because the bounds of searching the required value is undetermined.',
      );
    }
    return this.#plain().computeQuantile(rvSubs(expr, this.values));
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.compute_density`
   */
  override computeDensity(expr: Expr): DensityResult {
    if (this.distribution.isSymbolic) {
      const rv = first(randomSymbols(expr));
      const k = new Dummy('k', { integer: true });
      const isBool = expr instanceof Rel || expr instanceof BoolOp;
      const cond = isBool ? expr.subs(rv, k) : S.true;
      return Lambda(k, piecewise([this.pmf(k), and(Ge(k, this.distribution.low), Le(k, this.distribution.high), cond)], [S.Zero, true]));
    }
    return this.#plain().computeDensity(rvSubs(expr, this.values));
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The cumulative distribution function.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.compute_cdf`
   */
  override computeCdf(expr: Expr): DensityResult {
    if (this.distribution.isSymbolic) {
      const d = cast(this.computeDensity(expr), Expr);
      const k = new Dummy('k');
      const ki = new Dummy('ki');
      return Lambda(k, Sum(callLambda(d, ki), [ki, this.distribution.low, k]));
    }
    return this.#plain().computeCdf(rvSubs(expr, this.values));
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvs - Random variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvs?: readonly RandomSymbol[]): Expr {
    if (this.distribution.isSymbolic) {
      const rv = first(randomSymbols(exprIn));
      const k = new Dummy('k', { integer: true });
      const expr = exprIn.subs(rv, k);
      const isBool = expr instanceof Rel || expr instanceof BoolOp;
      const cond = isBool ? expr : S.true;
      const func = cond !== S.true ? mul(this.pmf(k), k) : mul(this.pmf(k), expr);
      return doit(Sum(piecewise([func, cond], [S.Zero, true]), [k, this.distribution.low, this.distribution.high]));
    }
    const expr = rvSubs(sympify(exprIn), rvs);
    return this.#plain().computeExpectation(expr, rvs);
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param condition - Condition on the random variables.
   * @returns The probability of the event.
   * @throws NotImplementedError when the distribution has symbolic size.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.probability`
   */
  override probability(condition: Expr): Expr {
    if (this.distribution.isSymbolic) {
      throw new NotImplementedError('Currently, probability queries are not supported for random variables with symbolic sized distributions.');
    }
    return this.#plain().probability(rvSubs(condition));
  }
  /**
   * Restricts the probability space to outcomes that satisfy the condition.
   *
   * @param condition - Condition on the random variables.
   * @returns The conditioned probability space.
   * @see SymPy `sympy.stats.frv.SingleFinitePSpace.conditional_space`
   */
  override conditionalSpace(condition: Expr): PSpace {
    const domain = this.where(condition);
    const prob = this.probability(condition);
    const test = (key: Expr): boolean => !(domain instanceof ConditionalFiniteDomain) || domain.test(elementOf(key));
    const items = this.densityItems.filter(([key]) => test(key)).map(([key, val]) => [key, mul(val, prob.pow(-1))] as const);
    return new FinitePSpace([domain, Dict(items)]);
  }
}

/** A Lambda density applied to a value. */
function callLambda(d: Expr, x: Expr): Expr {
  return cast(d, LambdaNode, 'density').call(x);
}

/**
 * Independent finite spaces.
 *
 * @see SymPy `sympy.stats.frv.ProductFinitePSpace`
 */
export class ProductFinitePSpace extends IndependentProductPSpace {
  /**
   * Constructs a new `ProductFinitePSpace`.
   *
   * @param args - Operands in the order `spaces`.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'ProductFinitePSpace');
  }
  /**
   * Indicates whether this probability space has finitely many outcomes.
   *
   * @returns `true` for this space.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.is_Finite`
   */
  override get isFinite(): boolean {
    return true;
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.domain`
   */
  override get domain(): RandomDomain {
    return makeProductDomain(this.spaces.map((s) => s.domain));
  }
  /**
   * Pairs the elements of the space with their probability masses.
   *
   * @returns The finite density entries.
   */
  get densityItems(): (readonly [Expr, Expr])[] {
    let out: [FiniteElement, Expr][] = [[[], S.One]];
    for (const space of this.spaces) {
      const items = densityItemsOf(space);
      out = out.flatMap(([el, p]) => items.map(([k, q]) => [[...el, ...elementOf(k)], mul(p, q)] as [FiniteElement, Expr]));
    }
    // (the elements of a product of spaces of distinct symbols are distinct)
    return out.map(([el, p]) => [elementKey(el), p] as const);
  }
  /**
   * Expresses the density on the underlying probability space.
   *
   * @returns The density expression.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.density`
   */
  override get density(): Expr {
    return Dict(this.densityItems);
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param condition - Condition on the random variables.
   * @returns The probability of the event.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.probability`
   */
  override probability(condition: Expr): Expr {
    return this.#plain().probability(condition);
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.compute_density`
   */
  override computeDensity(expr: Expr): DensityResult {
    return this.#plain().computeDensity(rvSubs(expr, this.values));
  }
  /** The finite space of the elements (the methods of SymPy FinitePSpace that ProductFinitePSpace inherits). */
  #plain(): FinitePSpace {
    return new FinitePSpace([this.domain, this.density]);
  }
  /**
   * Restricts the domain to the subset satisfying the condition.
   *
   * @param condition - Condition on the random variables.
   * @returns The domain satisfying the condition.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.where`
   */
  override where(condition: Expr): RandomDomain {
    return conditionalFiniteDomain(this.domain, condition);
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The characteristic function.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.compute_characteristic_function`
   */
  override computeCharacteristicFunction(expr: Expr): Expr {
    return this.#plain().computeCharacteristicFunction(rvSubs(expr, this.values));
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param expr - Expression to evaluate.
   * @returns The moment generating function.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.compute_moment_generating_function`
   */
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    return this.#plain().computeMomentGeneratingFunction(rvSubs(expr, this.values));
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The quantile function.
   * @see SymPy `sympy.stats.frv.ProductFinitePSpace.compute_quantile`
   */
  override computeQuantile(expr: Expr): Expr {
    return cast(this.computeCdf(expr), Expr);
  }
}

/** The density items of a finite space (single, product or plain). */
function densityItemsOf(space: PSpace): (readonly [Expr, Expr])[] {
  if (space instanceof FinitePSpace || space instanceof ProductFinitePSpace) return space.densityItems;
  // SymPy: the conditional space of a product with a space that is not finite is not implemented
  throw new NotImplementedError(`${space.name} is not a finite space`);
}

/** SymPy FinitePSpace.conditional_space(space, condition) of a product of finite spaces. */
function finiteConditionalSpace(space: PSpace, condition: Expr): PSpace {
  return new FinitePSpace([space.domain, Dict(densityItemsOf(space))]).conditionalSpace(condition);
}

statsClasses.productFinitePSpace = (spaces) => new ProductFinitePSpace(spaces);
statsClasses.productFiniteDomain = (domains) => new ProductFiniteDomain(domains);
statsClasses.finiteConditionalSpace = finiteConditionalSpace;
