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

/** SymPy DiscreteDistribution. */
export abstract class DiscreteDistribution extends Distribution {}

/** summation(f, (x, a, b)) over the integers of [a, b]. */
const sum = (f: Expr, x: Sym, a: Expr, b: Expr): Expr => summation(f, [x, a, b]);

/**
 * SymPy SingleDiscreteDistribution: a distribution on (a subset of) the
 * integers. Subclasses define `pdf` (the probability mass function) and
 * `set`, and may give closed forms of the cdf, characteristic and moment
 * generating functions and quantile.
 */
export abstract class SingleDiscreteDistribution extends DiscreteDistribution {
  get set(): SetExpr {
    return Integers;
  }
  /** Checks the parameters (SymPy check). */
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
  /** SymPy compute_cdf: the sum of the mass function up to floor(z). */
  computeCdf(): LambdaNode {
    const x = new Dummy('x', { integer: true });
    const z = new Dummy('z', { real: true });
    const left = inf(this.set);
    const c = sum(this.pdf(x), x, left, floor(z));
    return Lambda(z, piecewise([c, Ge(z, left)], [0, true]));
  }
  /** The cumulative distribution function at x (SymPy cdf). */
  cdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return this.cdfClosed(x) ?? this.computeCdf().call(x);
  }
  /** SymPy compute_characteristic_function. */
  computeCharacteristicFunction(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    return Lambda(t, sum(mul(exp(mul(S.I, t, x)), this.pdf(x)), x, inf(this.set), sup(this.set)));
  }
  /** The characteristic function at t (SymPy characteristic_function). */
  characteristicFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.characteristicFunctionClosed(t) ?? this.computeCharacteristicFunction().call(t);
  }
  /** SymPy compute_moment_generating_function. */
  computeMomentGeneratingFunction(): LambdaNode {
    const t = new Dummy('t', { real: true });
    const x = new Dummy('x', { integer: true });
    return Lambda(t, sum(mul(exp(mul(t, x)), this.pdf(x)), x, inf(this.set), sup(this.set)));
  }
  /** The moment generating function at t (SymPy moment_generating_function). */
  momentGeneratingFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.momentGeneratingFunctionClosed(t) ?? this.computeMomentGeneratingFunction().call(t);
  }
  /** SymPy compute_quantile: the least x with p <= cdf(x). */
  computeQuantile(): LambdaNode {
    const x = new Dummy('x', { integer: true });
    const p = new Dummy('p', { real: true });
    const left = inf(this.set);
    const c = sum(this.pdf(x), x, left, x);
    return Lambda(p, piecewise([x, Le(p, c)]));
  }
  /** The quantile function at p (SymPy quantile). */
  quantile(pIn: ExprLike): Expr {
    const p = sympify(pIn);
    return this.quantileClosed(p) ?? this.computeQuantile().call(p);
  }
  /**
   * The expectation of expr, an expression of var (SymPy expectation): the
   * moments of a polynomial come from the Taylor series of the moment
   * generating function; otherwise the sum.
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

/** SymPy DiscreteDomain. */
export abstract class DiscreteDomain extends RandomDomain {}

/** SymPy SingleDiscreteDomain(symbol, set). */
export class SingleDiscreteDomain extends SingleDomain {
  constructor(args: readonly Expr[]) {
    super(args, 'SingleDiscreteDomain');
  }
  override get isDiscrete(): boolean {
    return true;
  }
  override asBoolean(): Expr {
    return contains(this.set, this.symbol);
  }
}

/** SymPy ConditionalDiscreteDomain(fulldomain, condition). */
export class ConditionalDiscreteDomain extends ConditionalDomain {
  constructor(args: readonly Expr[]) {
    super('ConditionalDiscreteDomain', [at(args, 0), conditionOnSymbols(at(args, 1))]);
  }
  override get isDiscrete(): boolean {
    return true;
  }
  override get set(): SetExpr {
    if (this.symbols.length > 1) throw new NotImplementedError('Multivariate conditional domains are not yet implemented.');
    return intersection(reduceRationalInequalitiesWrap(this.condition, first(this.symbols)), this.fulldomain.set);
  }
}

/** SymPy DiscretePSpace(domain, density). */
export class DiscretePSpace extends PSpace {
  constructor(args: readonly Expr[], name = 'DiscretePSpace') {
    super(args, name);
  }
  override get isReal(): boolean {
    return true;
  }
  override get isDiscrete(): boolean {
    return true;
  }
  override get pdf(): Expr {
    return cast(this.density, LambdaNode, 'density').call(...this.symbols);
  }
  override where(condition: Expr): RandomDomain {
    const rvs = randomSymbols(condition);
    if (rvs.length > 1) throw new NotImplementedError('Multivariate discrete random variables are not yet supported.');
    const conditionalDomain = intersection(reduceRationalInequalitiesWrap(condition, first(rvs)), this.domain.set);
    return new SingleDiscreteDomain([first(rvs).symbol, conditionalDomain]);
  }
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
  override conditionalSpace(conditionIn: Expr): PSpace {
    const densityL = Lambda(this.symbols, mul(this.pdf, this.probability(conditionIn).pow(-1)));
    const condition = xreplace(conditionIn, this.values.map((rv) => [rv, rv.symbol] as const));
    const domain = new ConditionalDiscreteDomain([this.domain, condition]);
    return new DiscretePSpace([domain, densityL]);
  }
}

/** SymPy ProductDiscreteDomain(*domains). */
export class ProductDiscreteDomain extends ProductDomain {
  constructor(args: readonly Expr[]) {
    super(args, 'ProductDiscreteDomain');
  }
  override get isDiscrete(): boolean {
    return true;
  }
}

/** SymPy SingleDiscretePSpace(s, distribution): a discrete random variable with a distribution. */
export class SingleDiscretePSpace extends DiscretePSpace {
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution')], 'SingleDiscretePSpace');
  }
  override get isSingle(): boolean {
    return true;
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get distribution(): SingleDiscreteDistribution {
    return cast(at(this.args, 1), SingleDiscreteDistribution);
  }
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  override get pdf(): Expr {
    return this.distribution.pdf(this.symbol);
  }
  get set(): SetExpr {
    return this.distribution.set;
  }
  override get domain(): RandomDomain {
    return new SingleDiscreteDomain([this.symbol, this.set]);
  }
  override get density(): Expr {
    return this.distribution;
  }
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
  override computeCdf(expr: Expr): DensityResult {
    if (expr.key !== this.value.key) throw new NotImplementedError('cdf of a function of a discrete random variable');
    const x = new Dummy('x', { real: true });
    return Lambda(x, this.distribution.cdf(x));
  }
  override computeDensity(expr: Expr): DensityResult {
    if (expr.key === this.value.key) return this.distribution;
    throw new NotImplementedError('density of a function of a discrete random variable');
  }
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) throw new NotImplementedError('characteristic function of a function of a discrete random variable');
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.characteristicFunction(t));
  }
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) throw new NotImplementedError('moment generating function of a function of a discrete random variable');
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.momentGeneratingFunction(t));
  }
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
