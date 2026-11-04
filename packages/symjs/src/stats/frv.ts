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

import { BoolAtom, Dummy, Expr, Rel, S, Sym } from '../core/nodes';
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

/** SymPy FiniteDomain: a domain of finitely many elements. */
export abstract class FiniteDomain extends RandomDomain {
  override get isFinite(): boolean {
    return true;
  }
  /** The elements (SymPy iteration over the domain). */
  abstract elements(): FiniteElement[];
  /** The elements as Dicts (SymPy dict). */
  get dict(): SetExpr {
    return elementsDict(this.elements());
  }
  /** The element belongs to the domain (SymPy __contains__). */
  containsElement(other: FiniteElement): boolean {
    const k = elementKey(other).key;
    return this.elements().some((e) => elementKey(e).key === k);
  }
  override asBoolean(): Expr {
    return elementsBoolean(this.elements());
  }
}

/** SymPy SingleFiniteDomain(symbol, set): a finite variable and its values. */
export class SingleFiniteDomain extends FiniteDomain {
  constructor(args: readonly Expr[]) {
    super('SingleFiniteDomain', [cast(at(args, 0), Sym, 'domain symbol'), cast(at(args, 1), SetExpr, 'domain set')]);
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get symbols(): Sym[] {
    return [this.symbol];
  }
  override get set(): SetExpr {
    return cast(at(this.args, 1), SetExpr);
  }
  elements(): FiniteElement[] {
    return cast(this.set, FiniteSet, 'finite set').args.map((v) => [[this.symbol, v] as const]);
  }
}

/** SymPy ProductFiniteDomain(*domains). */
export class ProductFiniteDomain extends ProductDomain {
  constructor(args: readonly Expr[], name = 'ProductFiniteDomain') {
    super(args, name);
  }
  override get isFinite(): boolean {
    return true;
  }
  /** The elements: the unions of one element of each domain (SymPy itertools.product). */
  elements(): FiniteElement[] {
    let out: FiniteElement[] = [[]];
    for (const d of this.domains) {
      const els = cast(d, FiniteDomain, 'finite domain').elements();
      out = out.flatMap((acc) => els.map((el) => [...acc, ...el]));
    }
    return out;
  }
  /** The elements as Dicts (SymPy dict). */
  get dict(): SetExpr {
    return elementsDict(this.elements());
  }
  override asBoolean(): Expr {
    return elementsBoolean(this.elements());
  }
}

/** The elements of a finite domain, product or not. */
export function finiteElements(d: RandomDomain): FiniteElement[] {
  if (d instanceof FiniteDomain || d instanceof ProductFiniteDomain || d instanceof ConditionalFiniteDomain) return d.elements();
  throw new TypeError(`${d.name} is not a finite domain`);
}

/** SymPy ConditionalFiniteDomain(domain, condition): the elements of the domain where the condition holds. */
export class ConditionalFiniteDomain extends ConditionalDomain {
  constructor(args: readonly Expr[]) {
    super('ConditionalFiniteDomain', [at(args, 0), rvSubs(at(args, 1))]);
  }
  override get isFinite(): boolean {
    return true;
  }
  /** The condition holds at the element (SymPy _test). */
  test(elem: FiniteElement): boolean {
    const val = at_(this.condition, elem);
    if (val instanceof BoolAtom) return val.value;
    if (val instanceof Rel && val.op === 'Eq') return val.lhs.key === val.rhs.key;
    throw new RangeError(`Undecidable if ${val.toString()}`);
  }
  elements(): FiniteElement[] {
    return finiteElements(this.fulldomain).filter((e) => this.test(e));
  }
  /** The elements as Dicts (SymPy dict). */
  get dict(): SetExpr {
    return elementsDict(this.elements());
  }
  override get set(): SetExpr {
    const full = this.fulldomain;
    if (full instanceof SingleFiniteDomain) return finiteSet(...this.elements().map((el) => at(first(el), 1)));
    throw new NotImplementedError('Not implemented on multi-dimensional conditional domain');
  }
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

/** SymPy SingleFiniteDistribution: a distribution of finitely many values. */
export abstract class SingleFiniteDistribution extends Distribution {
  override get isFinite(): boolean {
    return true;
  }
  /** Checks the parameters (SymPy check). */
  check(): void {}
  /** The distribution has a symbolic number of values (SymPy is_symbolic). */
  get isSymbolic(): boolean {
    return false;
  }
  /** The smallest and largest values of a symbolic distribution (SymPy low and high). */
  get low(): Expr {
    throw new NotImplementedError(`${this.name} has no low value`);
  }
  get high(): Expr {
    throw new NotImplementedError(`${this.name} has no high value`);
  }
  /** The values (SymPy set). */
  abstract override get set(): SetExpr;
  /** The probability mass function (SymPy pmf). */
  abstract pmf(x: ExprLike): Expr;
  pdf(x: ExprLike): Expr {
    return this.pmf(x);
  }
  /** The values and their probabilities, or the unevaluated Density of a symbolic distribution (SymPy dict). */
  override get dict(): DensityResult {
    if (this.isSymbolic) return new Density([this]);
    return new FiniteDensity(cast(this.set, FiniteSet, 'values').args.map((k) => [k, this.pmf(k)] as const));
  }
  /** The value is one the distribution takes (SymPy __contains__). */
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
 * SymPy FinitePSpace(domain, density): a finite probability space. The
 * density maps elements (or, for the space of one distribution, values) to
 * probabilities.
 */
export class FinitePSpace extends PSpace {
  constructor(args: readonly Expr[], name = 'FinitePSpace') {
    super(args, name);
  }
  override get isFinite(): boolean {
    return true;
  }
  /** The density as (key, probability) pairs (SymPy _density). */
  get densityItems(): (readonly [Expr, Expr])[] {
    const d = this.density;
    return d instanceof DictNode ? d.items() : distItems(cast(d, SingleFiniteDistribution, 'density'));
  }
  /** The probability of an element (SymPy prob_of). */
  probOf(elem: FiniteElement): Expr {
    const items = this.densityItems;
    if (items.length && first(items)[0] instanceof FiniteSet) {
      const k = elementKey(elem).key;
      return items.find(([key]) => key.key === k)?.[1] ?? S.Zero;
    }
    const v = at(first(elem), 1).key;
    return items.find(([key]) => key.key === v)?.[1] ?? S.Zero;
  }
  override where(condition: Expr): RandomDomain {
    return conditionalFiniteDomain(this.domain, condition);
  }
  override computeDensity(exprIn: Expr): DensityResult {
    const expr = rvSubs(exprIn, this.values);
    const d = new FiniteDensity();
    for (const elem of finiteElements(this.domain)) {
      const val = at_(expr, elem);
      d.set(val, add(d.get(val) ?? S.Zero, this.probOf(elem)));
    }
    return d;
  }
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
  /** The cdf items sorted by cumulative probability (SymPy sorted_cdf). */
  sortedCdf(expr: Expr): (readonly [Expr, Expr])[] {
    const items = [...cast(this.computeCdf(expr), FiniteDensity)];
    return items.sort((a, b) => defined(cmpReal(a[1], b[1])));
  }
  override computeCharacteristicFunction(expr: Expr): Expr {
    const d = cast(this.computeDensity(expr), FiniteDensity);
    const t = new Dummy('t', { real: true });
    return Lambda(t, add(...[...d].map(([k, v]) => mul(exp(mul(S.I, k, t)), v))));
  }
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    const d = cast(this.computeDensity(expr), FiniteDensity);
    const t = new Dummy('t', { real: true });
    return Lambda(t, add(...[...d].map(([k, v]) => mul(exp(mul(k, t)), v))));
  }
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[]): Expr {
    const rvs = rvsIn?.length ? rvsIn : this.values;
    const expr = rvSubs(exprIn, rvs);
    const elements = finiteElements(this.domain);
    const isBool = expr instanceof Rel || expr instanceof BoolOp || expr instanceof BoolAtom;
    return add(
      ...elements.map((elem) => {
        const prob = this.probOf(elem);
        const value = isBool ? at(first(elem), 1) : at_(expr, elem);
        const blv: Expr = isBool ? at_(expr, elem) : S.true;
        return piecewise([mul(prob, value), blv], [S.Zero, true]);
      }),
    );
  }
  override computeQuantile(expr: Expr): Expr {
    const c = cast(this.computeCdf(expr), FiniteDensity);
    const p = new Dummy('p', { real: true });
    const pairs: [Expr, Expr][] = [[S.NaN, or(Lt(p, 0), Gt(p, 1))]];
    for (const [key, value] of c) pairs.push([key, Le(p, value)]);
    return Lambda(p, piecewise(...pairs));
  }
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

/** SymPy SingleFinitePSpace(s, distribution): a finite random variable with a distribution. */
export class SingleFinitePSpace extends FinitePSpace {
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), SingleFiniteDistribution, 'distribution')], 'SingleFinitePSpace');
  }
  override get isSingle(): boolean {
    return true;
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get distribution(): SingleFiniteDistribution {
    return cast(at(this.args, 1), SingleFiniteDistribution);
  }
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  override get domain(): RandomDomain {
    return new SingleFiniteDomain([this.symbol, this.distribution.set]);
  }
  override get pdf(): Expr {
    return this.distribution.pmf(this.symbol);
  }
  /** The mass function at expr (SymPy pmf). */
  pmf(expr: ExprLike): Expr {
    return this.distribution.pmf(expr);
  }
  override get densityItems(): (readonly [Expr, Expr])[] {
    return distItems(this.distribution).map(([val, prob]) => [elementKey([[this.symbol, val]]), prob] as const);
  }
  /** The finite space of the distribution (SymPy FinitePSpace(self.domain, self.distribution)). */
  #plain(): FinitePSpace {
    return new FinitePSpace([this.domain, this.distribution]);
  }
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (this.distribution.isSymbolic) {
      const d = cast(this.computeDensity(expr), Expr);
      const t = new Dummy('t', { real: true });
      const ki = new Dummy('ki');
      return Lambda(t, Sum(mul(callLambda(d, ki), exp(mul(S.I, ki, t))), [ki, this.distribution.low, this.distribution.high]));
    }
    return this.#plain().computeCharacteristicFunction(rvSubs(expr, this.values));
  }
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (this.distribution.isSymbolic) {
      const d = cast(this.computeDensity(expr), Expr);
      const t = new Dummy('t', { real: true });
      const ki = new Dummy('ki');
      return Lambda(t, Sum(mul(callLambda(d, ki), exp(mul(ki, t))), [ki, this.distribution.low, this.distribution.high]));
    }
    return this.#plain().computeMomentGeneratingFunction(rvSubs(expr, this.values));
  }
  override computeQuantile(expr: Expr): Expr {
    if (this.distribution.isSymbolic) {
      throw new NotImplementedError(
        'Computing quantile for random variables with symbolic dimension because the bounds of searching the required value is undetermined.',
      );
    }
    return this.#plain().computeQuantile(rvSubs(expr, this.values));
  }
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
  override computeCdf(expr: Expr): DensityResult {
    if (this.distribution.isSymbolic) {
      const d = cast(this.computeDensity(expr), Expr);
      const k = new Dummy('k');
      const ki = new Dummy('ki');
      return Lambda(k, Sum(callLambda(d, ki), [ki, this.distribution.low, k]));
    }
    return this.#plain().computeCdf(rvSubs(expr, this.values));
  }
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
  override probability(condition: Expr): Expr {
    if (this.distribution.isSymbolic) {
      throw new NotImplementedError('Currently, probability queries are not supported for random variables with symbolic sized distributions.');
    }
    return this.#plain().probability(rvSubs(condition));
  }
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

/** SymPy ProductFinitePSpace(*spaces): independent finite spaces. */
export class ProductFinitePSpace extends IndependentProductPSpace {
  constructor(args: readonly Expr[]) {
    super(args, 'ProductFinitePSpace');
  }
  override get isFinite(): boolean {
    return true;
  }
  override get domain(): RandomDomain {
    return makeProductDomain(this.spaces.map((s) => s.domain));
  }
  /** The density of the elements (SymPy _density). */
  get densityItems(): (readonly [Expr, Expr])[] {
    let out: [FiniteElement, Expr][] = [[[], S.One]];
    for (const space of this.spaces) {
      const items = densityItemsOf(space);
      out = out.flatMap(([el, p]) => items.map(([k, q]) => [[...el, ...elementOf(k)], mul(p, q)] as [FiniteElement, Expr]));
    }
    // (the elements of a product of spaces of distinct symbols are distinct)
    return out.map(([el, p]) => [elementKey(el), p] as const);
  }
  override get density(): Expr {
    return Dict(this.densityItems);
  }
  override probability(condition: Expr): Expr {
    return this.#plain().probability(condition);
  }
  override computeDensity(expr: Expr): DensityResult {
    return this.#plain().computeDensity(rvSubs(expr, this.values));
  }
  /** The finite space of the elements (the methods of SymPy FinitePSpace that ProductFinitePSpace inherits). */
  #plain(): FinitePSpace {
    return new FinitePSpace([this.domain, this.density]);
  }
  override where(condition: Expr): RandomDomain {
    return conditionalFiniteDomain(this.domain, condition);
  }
  override computeCharacteristicFunction(expr: Expr): Expr {
    return this.#plain().computeCharacteristicFunction(rvSubs(expr, this.values));
  }
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    return this.#plain().computeMomentGeneratingFunction(rvSubs(expr, this.values));
  }
  /** SymPy FinitePSpace.compute_quantile, which needs the cdf: not defined for a product space (RangeError). */
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
