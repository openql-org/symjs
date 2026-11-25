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

import { Add, Dummy, Expr, Integral, Order, Pow, Rational, Rel, S, Special, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { abs } from '../functions/elementary/elementary';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { Eq, Ge, Le, Lt, piecewise, rel } from '../core/logic';
import { fact } from '../core/exprfacts';
import { BoolOp, and } from '../core/boolalg';
import { xreplace } from '../core/traverse';
import { Lambda, LambdaNode } from '../core/lambda';
import { NotImplementedError } from '../core/errors';
import { asIndependent, isRationalFunction } from '../core/methods';
import { at, cast, defined, first } from '../core/guard';
import { EmptySet, FiniteSet, Interval, Reals, SetExpr, SetOp, asRelational, inf, interval, intersection, sup, union } from '../sets/sets';
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

/**
 * Builds nested unevaluated integrals from the integrand and limits, with the first limit
 * innermost.
 *
 * @see SymPy `sympy.integrals.integrals.Integral`
 */
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
  // SymPy reduces rational inequalities only: any other condition is a ValueError
  const one = (c: Expr): SetExpr => {
    if (c instanceof Rel && !isRationalFunction(add(c.lhs, mul(-1, c.rhs)), [v])) throw new RangeError(`Reduction of condition failed ${c.toString()}`);
    return cast(solveUnivariateInequality(c, v, { relational: false }), SetExpr);
  };
  if (condition instanceof Rel) return one(condition);
  if (condition instanceof BoolOp && condition.op === 'Or') return union(...condition.args.map(one));
  if (condition instanceof BoolOp && condition.op === 'And') return intersection(...condition.args.map(one));
  throw new TypeError(`Condition ${condition.toString()} is not a relational or Boolean`);
}

// ---------------------------------------------------------------------------
// Domains
// ---------------------------------------------------------------------------

/**
 * A continuous variable and its interval.
 *
 * @see SymPy `sympy.stats.crv.SingleContinuousDomain`
 */
export class SingleContinuousDomain extends SingleDomain {
  /**
   * Constructs a new `SingleContinuousDomain`.
   *
   * @param args - Operands in the order `symbol`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'SingleContinuousDomain');
  }
  /**
   * Indicates whether the outcome domain is continuous.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.crv.SingleContinuousDomain.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param expr - Expression to evaluate.
   * @param variables - Variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @throws RangeError when the requested variables do not match the domain symbol.
   * @see SymPy `sympy.stats.crv.SingleContinuousDomain.compute_expectation`
   */
  override computeExpectation(expr: Expr, variables?: Iterable<Sym>): Expr {
    const vs = variables === undefined ? this.symbols : [...variables];
    if (!vs.length) return expr;
    if (vs.length !== 1 || first(vs).key !== this.symbol.key) throw new RangeError('Values should be equal');
    return makeIntegral(expr, [limitOver(this.symbol, this.set)]);
  }
  /**
   * Expresses domain membership as a predicate on the outcome variables.
   *
   * @returns A Boolean condition.
   * @see SymPy `sympy.stats.crv.SingleContinuousDomain.as_boolean`
   */
  override asBoolean(): Expr {
    return asRelational(this.set, this.symbol);
  }
}

/**
 * The Cartesian product of continuous domains.
 *
 * @see SymPy `sympy.stats.crv.ProductContinuousDomain`
 */
export class ProductContinuousDomain extends ProductDomain {
  /**
   * Constructs a new `ProductContinuousDomain`.
   *
   * @param args - Operands in the order `domains`.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'ProductContinuousDomain');
  }
  /**
   * Indicates whether the outcome domain is continuous.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.crv.ProductContinuousDomain.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param variables - Variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @see SymPy `sympy.stats.crv.ProductContinuousDomain.compute_expectation`
   */
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

/**
 * The subset of a continuous domain satisfying a condition.
 *
 * @see SymPy `sympy.stats.crv.ConditionalContinuousDomain`
 */
export class ConditionalContinuousDomain extends ConditionalDomain {
  /**
   * Constructs a new `ConditionalContinuousDomain`.
   *
   * @param args - Operands in the order `fulldomain`, `condition`.
   */
  constructor(args: readonly Expr[]) {
    super('ConditionalContinuousDomain', [at(args, 0), conditionOnSymbols(at(args, 1))]);
  }
  /**
   * Indicates whether the outcome domain is continuous.
   *
   * @returns `true` for this domain.
   * @see SymPy `sympy.stats.crv.ConditionalContinuousDomain.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param expr - Expression to evaluate.
   * @param variables - Variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @throws NotImplementedError when the condition cannot be reduced to supported integration limits.
   * @throws TypeError when the condition cannot be reduced to supported integration limits.
   * @see SymPy `sympy.stats.crv.ConditionalContinuousDomain.compute_expectation`
   */
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
          const symbols = [...cond.freeSymbols()].filter((s) => s instanceof Sym).filter((s) => keys.has(s.key));
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
  /**
   * Collects the values admitted by the outcome domain.
   *
   * @returns The outcome set.
   * @throws NotImplementedError when the conditional domain has no implemented set representation.
   * @see SymPy `sympy.stats.crv.ConditionalContinuousDomain.set`
   */
  override get set(): SetExpr {
    if (this.symbols.length === 1) return intersection(this.fulldomain.set, reduceRationalInequalitiesWrap(this.condition, first(this.symbols)));
    throw new NotImplementedError('Set of Conditional Domain not Implemented');
  }
}

/** The real line represented by the open interval from negative to positive infinity. */
export const realLine: SetExpr = new Interval(S.NegativeInfinity, S.Infinity, true, true);

// ---------------------------------------------------------------------------
// Distributions
// ---------------------------------------------------------------------------

/**
 * Base class for probability laws described by a continuous density.
 *
 * @see SymPy `sympy.stats.crv.ContinuousDistribution`
 * @example
 * ```ts
 * import { NormalDistribution, ex } from '@symjs/symjs';
 *
 * const law = new NormalDistribution([ex`0`, ex`1`]);
 * law.pdf(0); // => sqrt(2)/(2*sqrt(pi))
 * ```
 */
export abstract class ContinuousDistribution extends Distribution {}

/** An optional closed-form result used by distribution hooks before falling back to integration or summation. */
export type ClosedForm = Expr | undefined;

/**
 * A continuous distribution of one
 * variable. Subclasses define `pdf` and `set` and may give closed forms of
 * the cdf, characteristic and moment generating functions and quantile
 * (SymPy _cdf, _characteristic_function, _moment_generating_function,
 * _quantile), which are otherwise computed by integration.
 *
 * @see SymPy `sympy.stats.crv.SingleContinuousDistribution`
 */
export abstract class SingleContinuousDistribution extends ContinuousDistribution {
  /**
   * Specifies the support of the continuous distribution, defaulting to the real line.
   *
   * @returns The support set.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.set`
   */
  get set(): SetExpr {
    return realLine;
  }
  /**
   * Checks the parameters, called when a random symbol is created.
   *
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.check`
   */
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
  /**
   * Integrates the density from the lower support endpoint to a variable upper limit.
   *
   * @returns The cumulative distribution function.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.compute_cdf`
   */
  computeCdf(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const z = new Dummy('z', { real: true });
    const left = inf(this.set);
    const right = sup(this.set);
    const F = integrateFromLeft(doit(this.pdf(x)), x, left, z);
    // the probability is complete above a finite upper end of the support
    if (fact(right, 'finite') === true) return Lambda(z, piecewise([0, Lt(z, left)], [F, Le(z, right)], [1, true]));
    return Lambda(z, piecewise([F, Ge(z, left)], [0, true]));
  }
  /**
   * Evaluates the cumulative distribution at the supplied value.
   *
   * @param xIn - Variable of the expansion.
   * @returns The cumulative probability at the argument.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.cdf`
   */
  cdf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return this.cdfClosed(x) ?? this.computeCdf().call(x);
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @returns The characteristic function.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.compute_characteristic_function`
   */
  computeCharacteristicFunction(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    const [, a, b] = limitOver(x, this.set);
    return Lambda(t, integrate(mul(exp(mul(S.I, t, x)), this.pdf(x)), x, [a, b]));
  }
  /**
   * Evaluates the characteristic function at the specified argument.
   *
   * @param tIn - Argument of the transform.
   * @returns The transform value at `t`.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.characteristic_function`
   */
  characteristicFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.characteristicFunctionClosed(t) ?? this.computeCharacteristicFunction().call(t);
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @returns The moment generating function.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.compute_moment_generating_function`
   */
  computeMomentGeneratingFunction(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    const [, a, b] = limitOver(x, this.set);
    return Lambda(t, integrate(mul(exp(mul(t, x)), this.pdf(x)), x, [a, b]));
  }
  /**
   * Evaluates the moment generating function at the specified argument.
   *
   * @param tIn - Argument of the transform.
   * @returns The exponential moment at `t`.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.moment_generating_function`
   */
  momentGeneratingFunction(tIn: ExprLike): Expr {
    const t = sympify(tIn);
    return this.momentGeneratingFunctionClosed(t) ?? this.computeMomentGeneratingFunction().call(t);
  }
  /**
   * Computes expectation by using moments from the generating function when available and integrating
   * otherwise.
   *
   * @param expr - Expression to evaluate.
   * @param v - Symbol distributed according to this law.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The expectation expression.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.expectation`
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
  /**
   * Solves the cumulative probability equation on the distribution's support.
   *
   * @returns The quantile function.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.compute_quantile`
   */
  computeQuantile(): LambdaNode {
    const x = new Dummy('x', { real: true });
    const p = new Dummy('p', { real: true });
    const left = inf(this.set);
    const c = integrate(this.pdf(x), x, [left, x]);
    const q = solveset(add(c, mul(-1, p)), x, this.set);
    return Lambda(p, piecewise([q, and(Ge(p, 0), Le(p, 1))], [S.NaN, true]));
  }
  /**
   * Finds the quantile corresponding to the given cumulative probability.
   *
   * @param pIn - Cumulative probability at which to evaluate the quantile.
   * @returns The quantile at `p`.
   * @see SymPy `sympy.stats.crv.SingleContinuousDistribution.quantile`
   */
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

/**
 * A continuous probability space; density is a Lambda of the symbols.
 *
 * @see SymPy `sympy.stats.crv.ContinuousPSpace`
 */
export class ContinuousPSpace extends PSpace {
  /**
   * Constructs a new `ContinuousPSpace`.
   *
   * @param args - Operands in the order `domain`, `density`.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'ContinuousPSpace') {
    super(args, name);
  }
  /**
   * Indicates whether this probability space is continuous.
   *
   * @returns `true` for this space.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Indicates whether the space is real-valued.
   *
   * @returns `true` for this space.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.is_real`
   */
  override get isReal(): boolean {
    return true;
  }
  /**
   * Expresses the density in terms of the symbols underlying the space.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.pdf`
   */
  override get pdf(): Expr {
    return cast(this.density, LambdaNode, 'density').call(...this.domain.symbols);
  }
  /**
   * Computes the expression's expectation over the specified variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvsIn - Random variables to integrate or sum over.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The expected value over the selected variables.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[], _opts: ComputeOptions = {}): Expr {
    const rvs = rvsIn ?? this.values;
    const expr = xreplace(exprIn, rvs.map((rv) => [rv, rv.symbol] as const));
    return this.domain.computeExpectation(mul(this.pdf, expr), rvs.map((rv) => rv.symbol));
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param expr - Expression to evaluate.
   * @param _opts - Evaluation options accepted by the probability-space interface.
   * @returns The probability distribution of the expression.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.compute_density`
   */
  override computeDensity(expr: Expr, _opts: ComputeOptions = {}): DensityResult {
    const keys = new Set(this.values.map((v) => v.key));
    if (expr instanceof RandomSymbol && keys.has(expr.key)) {
      const symbols = this.values.filter((v) => v.key !== expr.key).map((rs) => rs.symbol);
      return Lambda(expr.symbol, this.domain.computeExpectation(this.pdf, symbols));
    }
    const z = new Dummy('z', { real: true });
    return Lambda(z, this.computeExpectation(DiracDelta(add(expr, mul(-1, z)))));
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The cumulative distribution function.
   * @throws RangeError when the expression has several random variables.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.compute_cdf`
   */
  override computeCdf(expr: Expr): DensityResult {
    if (!isInterval(this.domain.set)) throw new RangeError('CDF not well defined on multivariate expressions');
    const d = densityCall(this.computeDensity(expr));
    const x = new Dummy('x', { real: true });
    const z = new Dummy('z', { real: true });
    const left = inf(this.domain.set);
    return Lambda(z, piecewise([integrateFromLeft(d(x), x, left, z), Ge(z, left)], [0, true]));
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The characteristic function.
   * @throws NotImplementedError when the expression has several random variables.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.compute_characteristic_function`
   */
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (!isInterval(this.domain.set)) throw new NotImplementedError('Characteristic function of multivariate expressions not implemented');
    const d = densityCall(this.computeDensity(expr));
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    const transform = integrate(mul(exp(mul(S.I, t, x)), d(x)), x, [S.NegativeInfinity, S.Infinity]);
    if (transform instanceof Integral) {
      const [scale, kernel] = asIndependent(transform.integrand, [x], { asAdd: false });
      return Lambda(t, mul(scale, new Integral([kernel, ...transform.args.slice(1)])));
    }
    return Lambda(t, transform);
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param expr - Expression to evaluate.
   * @returns The moment generating function.
   * @throws NotImplementedError when the expression has several random variables.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.compute_moment_generating_function`
   */
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (!isInterval(this.domain.set)) throw new NotImplementedError('Moment generating function of multivariate expressions not implemented');
    const d = densityCall(this.computeDensity(expr));
    const x = new Dummy('x', { real: true });
    const t = new Dummy('t', { real: true });
    return Lambda(t, integrate(mul(exp(mul(t, x)), d(x)), x, [S.NegativeInfinity, S.Infinity]));
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The quantile function.
   * @throws RangeError when the expression has several random variables.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.compute_quantile`
   */
  override computeQuantile(expr: Expr): Expr {
    if (!isInterval(this.domain.set)) throw new RangeError('Quantile not well defined on multivariate expressions');
    const d = densityCall(this.computeCdf(expr));
    const x = new Dummy('x', { real: true });
    const p = new Dummy('p', { positive: true });
    return Lambda(p, solveset(add(d(x), mul(-1, p)), x, this.domain.set));
  }
  /**
   * Computes the probability assigned to the event.
   *
   * @param conditionIn - Condition on the random variables.
   * @param opts - Evaluation controls for integrals, sums and compound distributions.
   * @returns The probability of the event.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.probability`
   */
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
  /**
   * Restricts the domain to the subset satisfying the condition.
   *
   * @param condition - Condition on the random variables.
   * @returns The domain satisfying the condition.
   * @throws NotImplementedError when the condition involves multiple continuous random variables.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.where`
   */
  override where(condition: Expr): RandomDomain {
    const rvs = randomSymbols(condition);
    const keys = new Set(this.values.map((v) => v.key));
    if (!(rvs.length === 1 && keys.has(first(rvs).key))) throw new NotImplementedError('Multiple continuous random variables not supported');
    const rv = first(rvs);
    const iv = intersection(reduceRationalInequalitiesWrap(condition, rv), this.domain.set);
    return new SingleContinuousDomain([rv.symbol, iv]);
  }
  /**
   * Restricts the probability space to outcomes that satisfy the condition.
   *
   * @param conditionIn - Condition on the random variables.
   * @returns The conditioned probability space.
   * @see SymPy `sympy.stats.crv.ContinuousPSpace.conditional_space`
   */
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

/**
 * A continuous random variable with a distribution.
 *
 * @see SymPy `sympy.stats.crv.SingleContinuousPSpace`
 */
export class SingleContinuousPSpace extends ContinuousPSpace {
  /**
   * Constructs a new `SingleContinuousPSpace`.
   *
   * @param args - Operands in the order `s`, `distribution`.
   */
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution')], 'SingleContinuousPSpace');
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
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the law of the random variable in this space.
   *
   * @returns The distribution object.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.distribution`
   */
  get distribution(): SingleContinuousDistribution {
    return cast(at(this.args, 1), SingleContinuousDistribution);
  }
  /**
   * Constructs the random symbol associated with this probability space.
   *
   * @returns The space's random variable.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.value`
   */
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  /**
   * Expresses the density in terms of the symbols underlying the space.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.pdf`
   */
  override get pdf(): Expr {
    return this.distribution.pdf(this.symbol);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.set`
   */
  get set(): SetExpr {
    return this.distribution.set;
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.domain`
   */
  override get domain(): RandomDomain {
    return new SingleContinuousDomain([this.symbol, this.set]);
  }
  /**
   * Expresses the density on the underlying probability space.
   *
   * @returns The density expression.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.density`
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
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvsIn?: readonly RandomSymbol[], opts: ComputeOptions = {}): Expr {
    const rvs = rvsIn?.length ? rvsIn : [this.value];
    if (!rvs.some((rv) => rv.key === this.value.key)) return exprIn;
    const expr = xreplace(sympify(exprIn), rvs.map((rv) => [rv, rv.symbol] as const));
    // (SymPy falls back to the integral on a PoleError, which the series of symjs does not raise)
    return this.distribution.expectation(expr, this.value.symbol, { evaluate: opts.evaluate ?? false });
  }
  /**
   * Computes the cumulative distribution of the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The cumulative distribution function.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.compute_cdf`
   */
  override computeCdf(expr: Expr): DensityResult {
    if (expr instanceof Pow && expr.base.key === this.value.key && expr.exp instanceof Rational && expr.exp.isInteger && expr.exp.isPositive && expr.exp.p % 2n === 0n) {
      // X**(2*n) <= z exactly when -z**(1/(2*n)) <= X <= z**(1/(2*n)).
      const z = new Dummy('z', { real: true });
      const positive = new Dummy('z', { positive: true });
      const root = pow(positive, Rational.of(1n, expr.exp.p));
      const mass = add(this.distribution.cdf(root), mul(-1, this.distribution.cdf(mul(-1, root))));
      return Lambda(z, piecewise([mass.subs(positive, z), Ge(z, 0)], [0, true]));
    }
    if (expr.key !== this.value.key) return super.computeCdf(expr);
    const z = new Dummy('z', { real: true });
    return Lambda(z, this.distribution.cdf(z));
  }
  /**
   * Computes the Fourier transform of the probability law for the expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The characteristic function.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.compute_characteristic_function`
   */
  override computeCharacteristicFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) return super.computeCharacteristicFunction(expr);
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.characteristicFunction(t));
  }
  /**
   * Computes the exponential moment transform of the expression's law.
   *
   * @param expr - Expression to evaluate.
   * @returns The moment generating function.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.compute_moment_generating_function`
   */
  override computeMomentGeneratingFunction(expr: Expr): Expr {
    if (expr.key !== this.value.key) return super.computeMomentGeneratingFunction(expr);
    const t = new Dummy('t', { real: true });
    return Lambda(t, this.distribution.momentGeneratingFunction(t));
  }
  /**
   * Computes the distribution induced by the expression on this space.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @throws RangeError when the transformation cannot be inverted.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.compute_density`
   */
  override computeDensity(expr: Expr): DensityResult {
    if (expr.key === this.value.key) return this.density;
    const y = new Dummy('y', { real: true });
    let gs = solveset(add(expr, mul(-1, y)), this.value, Reals);
    if (gs instanceof SetOp && gs.op === 'Intersection' && gs.args.length === 2 && gs.args.includes(Reals)) gs = cast(gs.args.find((g) => g !== Reals), SetExpr);
    if (!(gs instanceof FiniteSet)) throw new RangeError(`Can not solve ${expr.toString()} for ${this.value.toString()}`);
    const fx = this.distribution;
    return Lambda(y, add(...gs.args.map((g) => mul(fx.pdf(g), abs(g.diff(y))))));
  }
  /**
   * Computes the quantile function of the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The quantile function.
   * @see SymPy `sympy.stats.crv.SingleContinuousPSpace.compute_quantile`
   */
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
