// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/crv.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.crv: continuous random variables. Probability
 * spaces whose densities are integrated over intervals: expectations and
 * probabilities are integrals, densities of functions of a random symbol
 * come from solving for it.
 */

import { Add, Dummy, Expr, Integral, Order, Rel, S, Special, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { abs } from '../functions/elementary/elementary';
import { add, exp, mul, sympify } from '../core/ops';
import { Eq, Ge, Le, piecewise, rel } from '../core/logic';
import { BoolOp, and } from '../core/boolalg';
import { xreplace } from '../core/traverse';
import { Lambda, LambdaNode } from '../core/lambda';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, first } from '../core/guard';
import { EmptySet, FiniteSet, Interval, Reals, SetExpr, SetOp, asRelational, inf, interval, intersection, union } from '../sets/sets';
import { solveUnivariateInequality, solveset } from '../solvers/inequalities';
import { integrate } from '../integrals/integrate';
import { DiracDelta } from '../integrals/transforms/delta';
import { polyCoefficients } from '../polys/poly';
import { series } from '../series/series';
import { factorial } from '../functions/special/special';
import { doit } from '../calculus/doit';
import { cancel } from '../simplify/rational';
import {
  ConditionalDomain,
  Distribution,
  PSpace,
  ProductDomain,
  RandomSymbol,
  SingleDomain,
  conditionOnSymbols,
  density,
  isRandom,
  randomSymbols,
  statsClasses,
  symbolConverter,
} from './rv';
import type { ComputeOptions, DensityResult ,
  RandomDomain} from './rv';

// ---------------------------------------------------------------------------
// Integrals over sets
// ---------------------------------------------------------------------------

/** A limit of an integral: the variable and its bounds. */
export type Limit = readonly [Sym, Expr, Expr];

/** The set is an interval (SymPy is_Interval, which Reals is too). */
const isInterval = (s: SetExpr): boolean => s instanceof Interval || s === Reals;

/** The limits (x, a, b) of the variable over an interval (SymPy Integral(f, (x, Interval(a, b)))). */
export function limitOver(x: Sym, set: SetExpr): Limit {
  if (!isInterval(set)) throw new NotImplementedError(`integration over ${set.toString()} is not implemented`);
  return [x, inf(set), set instanceof Interval ? set.end : S.Infinity];
}

/** SymPy Integral(f, *limits) (unevaluated): nested integrals, innermost limit first. */
export function makeIntegral(f: Expr, limits: readonly Limit[]): Expr {
  return limits.reduce<Expr>((acc, [x, a, b]) => new Integral([acc, x, a, b]), f);
}

/** The integrand and the limits of a (multiple) definite integral (SymPy function, limits). */
export function integralParts(e: Expr): [Expr, Limit[]] {
  const limits: Limit[] = [];
  let cur = e;
  while (cur instanceof Integral && cur.args.length === 4) {
    limits.unshift([cast(cur.variable, Sym), at(cur.args, 2), at(cur.args, 3)]);
    cur = cur.integrand;
  }
  return [cur, limits];
}

/**
 * The integral of f from a finite left end to z, for z >= left (the branch
 * of the cdf where it is used): z is left + w with w > 0 while integrating,
 * so that a singularity left of the interval does not leave the integral
 * unevaluated.
 */
function integrateFromLeft(f: Expr, x: Sym, left: Expr, z: Expr): Expr {
  if (left instanceof Special) return integrate(f, x, [left, z]);
  const w = new Dummy('w', { positive: true });
  return integrate(f, x, [left, add(left, w)]).subs(w, add(z, mul(-1, left)));
}

/** The set where the condition on var holds (SymPy reduce_rational_inequalities_wrap). */
export function reduceRationalInequalitiesWrap(condition: Expr, v: Sym): SetExpr {
  const one = (c: Expr): SetExpr => cast(solveUnivariateInequality(c, v, { relational: false }), SetExpr);
  if (condition instanceof Rel) return one(condition);
  if (condition instanceof BoolOp && condition.op === 'Or') return union(...condition.args.map(one));
  if (condition instanceof BoolOp && condition.op === 'And') return intersection(...condition.args.map(one));
  throw new TypeError(`Condition ${condition.toString()} is not a relational or Boolean`);
}

// ---------------------------------------------------------------------------
// Domains
// ---------------------------------------------------------------------------

/** SymPy SingleContinuousDomain(symbol, set): a continuous variable and its interval. */
export class SingleContinuousDomain extends SingleDomain {
  constructor(args: readonly Expr[]) {
    super(args, 'SingleContinuousDomain');
  }
  override get isContinuous(): boolean {
    return true;
  }
  override computeExpectation(expr: Expr, variables?: readonly Sym[]): Expr {
    const vs = variables ?? this.symbols;
    if (!vs.length) return expr;
    if (vs.length !== 1 || first(vs).key !== this.symbol.key) throw new RangeError('Values should be equal');
    return makeIntegral(expr, [limitOver(this.symbol, this.set)]);
  }
  override asBoolean(): Expr {
    return asRelational(this.set, this.symbol);
  }
}

/** SymPy ProductContinuousDomain(*domains). */
export class ProductContinuousDomain extends ProductDomain {
  constructor(args: readonly Expr[]) {
    super(args, 'ProductContinuousDomain');
  }
  override get isContinuous(): boolean {
    return true;
  }
  override computeExpectation(exprIn: Expr, variables?: readonly Sym[]): Expr {
    const vs = new Set((variables ?? this.symbols).map((s) => s.key));
    let expr = exprIn;
    for (const domain of this.domains) {
      const domainVars = domain.symbols.filter((s) => vs.has(s.key));
      if (domainVars.length) expr = domain.computeExpectation(expr, domainVars);
    }
    return expr;
  }
}

/** SymPy ConditionalContinuousDomain(fulldomain, condition). */
export class ConditionalContinuousDomain extends ConditionalDomain {
  constructor(args: readonly Expr[]) {
    super('ConditionalContinuousDomain', [at(args, 0), conditionOnSymbols(at(args, 1))]);
  }
  override get isContinuous(): boolean {
    return true;
  }
  override computeExpectation(expr: Expr, variables?: readonly Sym[]): Expr {
    const vs = variables ?? this.symbols;
    if (!vs.length) return expr;
    const fullintgrl = this.fulldomain.computeExpectation(expr, vs);
    let [integrand, limits] = integralParts(fullintgrl);
    const conditions = [this.condition];
    while (conditions.length) {
      const cond = defined(conditions.pop());
      if (cond instanceof BoolOp) {
        if (cond.op === 'And') conditions.push(...cond.args);
        else if (cond.op === 'Or') throw new NotImplementedError('Or not implemented here');
      } else if (cond instanceof Rel) {
        if (cond.op === 'Eq') {
          integrand = mul(integrand, DiracDelta(add(cond.lhs, mul(-1, cond.rhs))));
        } else {
          const keys = new Set(this.symbols.map((s) => s.key));
          const symbols = [...cond.freeSymbols()].filter((s) => keys.has(s.key));
          if (symbols.length !== 1) throw new NotImplementedError('Multivariate Inequalities not yet implemented');
          const symbol = first(symbols);
          limits = limits.map((limit) => {
            if (limit[0].key !== symbol.key) return limit;
            const cintvl = reduceRationalInequalitiesWrap(cond, symbol);
            const lintvl = interval(limit[1], limit[2]);
            const intvl = cast(intersection(cintvl, lintvl), Interval, 'interval of the condition');
            return [symbol, intvl.start, intvl.end] as const;
          });
        }
      } else if (cond !== S.true) throw new TypeError(`Condition ${cond.toString()} is not a relational or Boolean`);
    }
    return makeIntegral(integrand, limits);
  }
  override get set(): SetExpr {
    if (this.symbols.length === 1) return intersection(this.fulldomain.set, reduceRationalInequalitiesWrap(this.condition, first(this.symbols)));
    throw new NotImplementedError('Set of Conditional Domain not Implemented');
  }
}

/** SymPy Interval(-oo, oo): the real line as an interval (equal to Reals, printed as an interval). */
export const realLine: SetExpr = new Interval(S.NegativeInfinity, S.Infinity, true, true);

// ---------------------------------------------------------------------------
// Distributions
// ---------------------------------------------------------------------------

/** SymPy ContinuousDistribution. */
export abstract class ContinuousDistribution extends Distribution {}

/** A result that a distribution defines in closed form, or undefined (SymPy None) to compute it by integration. */
export type ClosedForm = Expr | undefined;

/**
 * SymPy SingleContinuousDistribution: a continuous distribution of one
 * variable. Subclasses define `pdf` and `set` and may give closed forms of
 * the cdf, characteristic and moment generating functions and quantile
 * (SymPy _cdf, _characteristic_function, _moment_generating_function,
 * _quantile), which are otherwise computed by integration.
 */
export abstract class SingleContinuousDistribution extends ContinuousDistribution {
  /** SymPy Interval(-oo, oo) (which prints as an interval, unlike S.Reals). */
  get set(): SetExpr {
    return realLine;
  }
  /** Checks the parameters (SymPy check), called when a random symbol is created. */
  check(): void {}
  protected cdfClosed(_x: Expr): ClosedForm {
    return undefined;
  }
  protected characteristicFunctionClosed(_t: Expr): ClosedForm {
    return undefined;
  }
  /** SymPy _moment_generating_function (also used by expectation). */
  protected momentGeneratingFunctionClosed(_t: Expr): ClosedForm {
    return undefined;
  }
  protected quantileClosed(_p: Expr): ClosedForm {
    return undefined;
  }
  /** SymPy compute_cdf: the integral of the pdf from the left end. */
  computeCdf(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const z = new Dummy('z', { real: true });
    const left = inf(this.set);
    return Lambda(z, piecewise([integrateFromLeft(doit(this.pdf(x)), x, left, z), Ge(z, left)], [0, true]));
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
    const [, a, b] = limitOver(x, this.set);
    return Lambda(t, integrate(mul(exp(mul(S.I, t, x)), this.pdf(x)), x, [a, b]));
  }
  /** The characteristic function at t (SymPy characteristic_function). */
  characteristicFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.characteristicFunctionClosed(t) ?? this.computeCharacteristicFunction().call(t);
  }
  /** SymPy compute_moment_generating_function. */
  computeMomentGeneratingFunction(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    const [, a, b] = limitOver(x, this.set);
    return Lambda(t, integrate(mul(exp(mul(t, x)), this.pdf(x)), x, [a, b]));
  }
  /** The moment generating function at t (SymPy moment_generating_function). */
  momentGeneratingFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.momentGeneratingFunctionClosed(t) ?? this.computeMomentGeneratingFunction().call(t);
  }
  /**
   * The expectation of expr, an expression of var (SymPy expectation): the
   * moments of a polynomial come from the Taylor series of the moment
   * generating function when it has a closed form; otherwise the integral.
   */
  expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    const [, a, b] = limitOver(v, this.set);
    if (opts.evaluate === false) return new Integral([mul(expr, this.pdf(v)), v, a, b]);
    const p = polyCoefficients(expr, v);
    if (p === undefined) return integrate(mul(expr, this.pdf(v)), v, [a, b]);
    if (p.size === 0) return S.Zero;
    const t = new Dummy('t', { real: true });
    const mgf = this.momentGeneratingFunctionClosed(t);
    if (mgf === undefined) return integrate(mul(expr, this.pdf(v)), v, [a, b]);
    const deg = Math.max(...p.keys());
    const taylor = polyCoefficients(removeO(series(mgf, t, 0, deg + 1)), t);
    const terms: Expr[] = [];
    // (SymPy reads the coefficients of poly(series), whose rational function coefficients are cancelled)
    for (let k = 0; k <= deg; k++) terms.push(mul(p.get(k) ?? S.Zero, cancel(defined(taylor).get(k) ?? S.Zero), factorial(k)));
    return add(...terms);
  }
  /** SymPy compute_quantile: the solutions of cdf(x) = p in the set. */
  computeQuantile(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const p = new Dummy('p', { real: true });
    const left = inf(this.set);
    const c = integrate(this.pdf(x), x, [left, x]);
    const q = solveset(add(c, mul(-1, p)), x, this.set);
    return Lambda(p, piecewise([q, and(Ge(p, 0), Le(p, 1))], [S.NaN, true]));
  }
  /** The quantile function at p (SymPy quantile). */
  quantile(pIn: ExprLike): Expr {
    const p = sympify(pIn);
    return this.quantileClosed(p) ?? this.computeQuantile().call(p);
  }
}

/** The series without its order term (SymPy removeO). */
export function removeO(e: Expr): Expr {
  if (e instanceof Order) return S.Zero;
  return e instanceof Add ? add(...e.args.filter((a) => !(a instanceof Order))) : e;
}

// ---------------------------------------------------------------------------
// Probability spaces
// ---------------------------------------------------------------------------

/** SymPy ContinuousPSpace(domain, density): a continuous probability space; density is a Lambda of the symbols. */
export class ContinuousPSpace extends PSpace {
  constructor(args: readonly Expr[], name = 'ContinuousPSpace') {
    super(args, name);
  }
  override get isContinuous(): boolean {
    return true;
  }
  override get isReal(): boolean {
    return true;
  }
  override get pdf(): Expr {
    return cast(this.density, LambdaNode, 'density').call(...this.domain.symbols);
  }
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[], _opts: ComputeOptions = {}): Expr {
    const rvs = rvsIn ?? this.values;
    const expr = xreplace(exprIn, rvs.map((rv) => [rv, rv.symbol] as const));
    return this.domain.computeExpectation(mul(this.pdf, expr), rvs.map((rv) => rv.symbol));
  }
  override computeDensity(expr: Expr, _opts: ComputeOptions = {}): DensityResult {
    const keys = new Set(this.values.map((v) => v.key));
    if (expr instanceof RandomSymbol && keys.has(expr.key)) {
      const symbols = this.values.filter((v) => v.key !== expr.key).map((rs) => rs.symbol);
      return Lambda(expr.symbol, this.domain.computeExpectation(this.pdf, symbols));
    }
    const z = new Dummy('z', { real: true });
    return Lambda(z, this.computeExpectation(DiracDelta(add(expr, mul(-1, z)))));
  }
  override computeCdf(expr: Expr): DensityResult {
    if (!isInterval(this.domain.set)) throw new RangeError('CDF not well defined on multivariate expressions');
    const d = densityCall(this.computeDensity(expr));
    const x = new Dummy('x', { real: true });
    const z = new Dummy('z', { real: true });
    const left = inf(this.domain.set);
    return Lambda(z, piecewise([integrateFromLeft(d(x), x, left, z), Ge(z, left)], [0, true]));
  }
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (!isInterval(this.domain.set)) throw new NotImplementedError('Characteristic function of multivariate expressions not implemented');
    const d = densityCall(this.computeDensity(expr));
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    return Lambda(t, integrate(mul(exp(mul(S.I, t, x)), d(x)), x, [S.NegativeInfinity, S.Infinity]));
  }
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (!isInterval(this.domain.set)) throw new NotImplementedError('Moment generating function of multivariate expressions not implemented');
    const d = densityCall(this.computeDensity(expr));
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    return Lambda(t, integrate(mul(exp(mul(t, x)), d(x)), x, [S.NegativeInfinity, S.Infinity]));
  }
  override computeQuantile(expr: Expr): Expr {
    if (!isInterval(this.domain.set)) throw new RangeError('Quantile not well defined on multivariate expressions');
    const d = densityCall(this.computeCdf(expr));
    const x = new Dummy('x', { real: true });
    const p = new Dummy('p', { positive: true });
    return Lambda(p, solveset(add(d(x), mul(-1, p)), x, this.domain.set));
  }
  override probability(conditionIn: Expr, opts: ComputeOptions = {}): Expr {
    const z = new Dummy('z', { real: true });
    let condition = conditionIn;
    let condInv = false;
    if (condition instanceof Rel && condition.op === 'Ne') {
      condition = Eq(condition.lhs, condition.rhs);
      condInv = true;
    }
    let domain: RandomDomain | undefined;
    try {
      domain = this.where(condition);
    } catch (e) {
      if (!(e instanceof NotImplementedError)) throw e;
    }
    if (domain instanceof SingleDomain) {
      const sym = domain.symbol;
      const rv = defined(this.values.find((v) => v.symbol.key === sym.key), 'random symbol of the domain');
      const pdf = densityCall(this.computeDensity(rv, opts));
      const set = domain.set;
      if (set === EmptySet || set instanceof FiniteSet) return condInv ? S.One : S.Zero;
      if (set instanceof SetOp && set.op === 'Union') {
        return add(...set.args.filter((s) => s instanceof Interval).map((s) => makeIntegral(pdf(z), [limitOver(z, s)])));
      }
      return makeIntegral(pdf(z), [limitOver(z, set)]);
    }
    // several random symbols: the density of lhs - rhs
    const r = cast(condition, Rel, 'condition');
    const expr = add(r.lhs, mul(-1, r.rhs));
    let dens: Expr;
    let comp: Expr;
    if (!isRandom(expr)) {
      dens = this.density;
      comp = r.rhs;
    } else {
      dens = cast(density(expr), Expr);
      comp = S.Zero;
    }
    const dist = dens instanceof ContinuousDistribution ? dens : defined(statsClasses.continuousHandmade, 'crv_types')(dens, this.domain.set);
    const space = new SingleContinuousPSpace([z, dist]);
    const result = space.probability(rel(r.op, space.value, comp));
    return condInv ? add(1, mul(-1, result)) : result;
  }
  override where(condition: Expr): RandomDomain {
    const rvs = randomSymbols(condition);
    const keys = new Set(this.values.map((v) => v.key));
    if (!(rvs.length === 1 && keys.has(first(rvs).key))) throw new NotImplementedError('Multiple continuous random variables not supported');
    const rv = first(rvs);
    const iv = intersection(reduceRationalInequalitiesWrap(condition, rv), this.domain.set);
    return new SingleContinuousDomain([rv.symbol, iv]);
  }
  override conditionalSpace(conditionIn: Expr): PSpace {
    const condition = xreplace(conditionIn, this.values.map((rv) => [rv, rv.symbol] as const));
    const domain = new ConditionalContinuousDomain([this.domain, condition]);
    const replacement = this.symbols.map((rv) => [rv, new Dummy(rv.name)] as const);
    const norm = domain.computeExpectation(this.pdf);
    const pdf = mul(this.pdf, xreplace(norm, replacement).pow(-1));
    return new ContinuousPSpace([domain, Lambda(domain.symbols, pdf)]);
  }
}

/** A density as a function of its variable (a distribution or a Lambda). */
export function densityCall(d: DensityResult): (x: Expr) => Expr {
  if (d instanceof LambdaNode) return (x) => d.call(x);
  const dist = cast(d, Distribution, 'density');
  return (x) => dist.pdf(x);
}

/** SymPy SingleContinuousPSpace(s, distribution): a continuous random variable with a distribution. */
export class SingleContinuousPSpace extends ContinuousPSpace {
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution')], 'SingleContinuousPSpace');
  }
  override get isSingle(): boolean {
    return true;
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get distribution(): SingleContinuousDistribution {
    return cast(at(this.args, 1), SingleContinuousDistribution);
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
    return new SingleContinuousDomain([this.symbol, this.set]);
  }
  override get density(): Expr {
    return this.distribution;
  }
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[], opts: ComputeOptions = {}): Expr {
    const rvs = rvsIn?.length ? rvsIn : [this.value];
    if (!rvs.some((rv) => rv.key === this.value.key)) return exprIn;
    const expr = xreplace(sympify(exprIn), rvs.map((rv) => [rv, rv.symbol] as const));
    // (SymPy falls back to the integral on a PoleError, which the series of symjs does not raise)
    return this.distribution.expectation(expr, this.value.symbol, { evaluate: opts.evaluate ?? false });
  }
  override computeCdf(expr: Expr): DensityResult {
    if (expr.key !== this.value.key) return super.computeCdf(expr);
    const z = new Dummy('z', { real: true });
    return Lambda(z, this.distribution.cdf(z));
  }
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) return super.computeCharacteristicFunction(expr);
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.characteristicFunction(t));
  }
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) return super.computeMomentGeneratingFunction(expr);
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.momentGeneratingFunction(t));
  }
  override computeDensity(expr: Expr): DensityResult {
    if (expr.key === this.value.key) return this.density;
    const y = new Dummy('y', { real: true });
    let gs = solveset(add(expr, mul(-1, y)), this.value, Reals);
    if (gs instanceof SetOp && gs.op === 'Intersection' && gs.args.length === 2 && gs.args.includes(Reals)) gs = cast(gs.args.find((g) => g !== Reals), SetExpr);
    if (!(gs instanceof FiniteSet)) throw new RangeError(`Can not solve ${expr.toString()} for ${this.value.toString()}`);
    const fx = this.distribution;
    return Lambda(y, add(...gs.args.map((g) => mul(fx.pdf(g), abs(g.diff(y))))));
  }
  override computeQuantile(expr: Expr): Expr {
    if (expr.key !== this.value.key) return super.computeQuantile(expr);
    const p = new Dummy('p', { real: true });
    return Lambda(p, this.distribution.quantile(p));
  }
}

statsClasses.continuousConditional = (domain, condition) => new ConditionalContinuousDomain([domain, condition]);
statsClasses.continuousPSpace = (domain, density) => new ContinuousPSpace([domain, density]);
statsClasses.continuousSingle = (z, dist) => new SingleContinuousPSpace([z, dist]);
statsClasses.productContinuousDomain = (domains) => new ProductContinuousDomain(domains);
