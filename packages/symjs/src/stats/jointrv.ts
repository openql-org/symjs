// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/joint_rv.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.joint_rv: joint probability spaces of random
 * vectors, their distributions, the components `X.at(i)` (SymPy `X[i]`) of
 * a joint random symbol, and the marginal distributions.
 *
 * The components of a joint random symbol are Indexed objects `X[i]` of the
 * random symbol. The integration variables of the expectations and marginal
 * densities are symbols named like the components (`X[0]`, ...), which print
 * as SymPy's Indexed variables.
 */

import { Dummy, S, Sym } from '../core/nodes';
import type { Assumptions, Expr, ExprLike } from '../core/nodes';
import { mul, sub, sympify } from '../core/ops';
import { Ge, Le } from '../core/logic';
import { Lambda } from '../core/lambda';
import { Sum } from '../core/concrete';
import { Indexed } from '../core/indexed';
import { TupleNode } from '../core/containers';
import { xreplace } from '../core/traverse';
import { NotImplementedError } from '../core/errors';
import { at, cast } from '../core/guard';
import { Integers, Interval, Naturals, Naturals0, ProductSetNode, Range, Reals, SetExpr, inf, productSet, sup } from '../sets/sets';
import { integrate } from '../integrals/integrate';
import { summation } from '../concrete/summations';
import { Distribution, ProductPSpace, RandomSymbol, SingleDomain, makeProductDomain, pspace, randomSymbols, sortedSymbols, symbolConverter } from './rv';
import type { PSpace, RandomDomain } from './rv';
import { SingleContinuousDistribution, SingleContinuousPSpace, makeIntegral } from './crv';
import { SingleDiscreteDistribution, SingleDiscretePSpace } from './drv';

/** The limits (variable, lower, upper) of a variable over an interval or a range (SymPy _process_limits of (x, set)). */
function limitOf(x: Sym, set: SetExpr): [Sym, Expr, Expr] {
  if (set === Reals) return [x, S.NegativeInfinity, S.Infinity];
  if (set === Integers || set === Naturals || set === Naturals0 || set instanceof Interval || set instanceof Range) return [x, inf(set), sup(set)];
  throw new NotImplementedError(`integration or summation over ${set.toString()} is not implemented`);
}

/**
 * A symbol standing for the component sym[i] of a random vector: it prints
 * as sym[i] and sorts like SymPy's Indexed integration variables.
 */
class ComponentSymbol extends Sym {
  override get sortClass(): string {
    return 'Indexed';
  }
  override get sortPriority(): number {
    return 5;
  }
  protected override computeKey(): string {
    return `Component(${super.computeKey()})`;
  }
}

/** The symbol named like the component sym[i] (SymPy Symbol(str(Indexed(sym, i))) and Indexed(str(base), i)). */
const componentSymbol = (sym: Expr, i: number, assumptions: Assumptions = {}): Sym => new ComponentSymbol(new Indexed([sym, sympify(i)]).toString(), assumptions);

/** The integer value of a component count (a number of sets of a product set). */
const countOf = (n: Expr): number => Number(n.toString());

// ---------------------------------------------------------------------------
// Joint distributions
// ---------------------------------------------------------------------------

/**
 * A distribution of several variables, applied to one value of each (`pdf(x1, x2, ...)`).
 *
 * @see SymPy `sympy.stats.joint_rv.JointDistribution`
 */
export abstract class JointDistribution extends Distribution {
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `false` for this distribution.
   */
  get isContinuous(): boolean {
    return false;
  }
  /**
   * Indicates whether the law is discrete.
   *
   * @returns `false` for this distribution.
   */
  get isDiscrete(): boolean {
    return false;
  }
  /**
   * Evaluates the joint probability density at the supplied coordinates.
   *
   * @param xs - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv.JointDistribution.pdf`
   */
  abstract override pdf(...xs: ExprLike[]): Expr;
  /**
   * Evaluates the joint density at the supplied coordinates.
   *
   * @param xs - Outcome at which to evaluate the density.
   * @returns The joint density value.
   * @see SymPy `sympy.stats.joint_rv.JointDistribution.__call__`
   */
  override call(...xs: ExprLike[]): Expr {
    return this.pdf(...xs);
  }
}

/** A joint or marginal distribution applied to the values, another one to the first value. */
function callDistribution(d: Distribution, xs: readonly Expr[]): Expr {
  return d instanceof JointDistribution || d instanceof MarginalDistribution ? d.call(...xs) : d.call(at(xs, 0));
}

// ---------------------------------------------------------------------------
// Joint probability spaces
// ---------------------------------------------------------------------------

/**
 * The probability space of a random vector.
 * Use `jointPSpace`, which gives a single space for a single-variable
 * distribution as SymPy's constructor does.
 *
 * @see SymPy `sympy.stats.joint_rv.JointPSpace`
 */
export class JointPSpace extends ProductPSpace {
  /**
   * Constructs a new `JointPSpace`.
   *
   * @param args - Operands in the order `sym`, `dist`.
   */
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution')], 'JointPSpace');
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.symbol`
   */
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  /**
   * Identifies the law of the random variable in this space.
   *
   * @returns The distribution object.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.distribution`
   */
  get distribution(): Distribution {
    return cast(at(this.args, 1), Distribution);
  }
  /**
   * Constructs the random symbol for this joint probability space.
   *
   * @returns The joint random variable.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.value`
   */
  get value(): JointRandomSymbol {
    return new JointRandomSymbol(this.symbol, this);
  }
  /**
   * Lists the random symbols belonging to the probability space.
   *
   * @returns The space's random variables.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.values`
   */
  override get values(): RandomSymbol[] {
    return [this.value];
  }
  /**
   * Indicates whether the space defines a density for its random symbol.
   *
   * @returns `true` for this space.
   */
  override get hasValueDensity(): boolean {
    return true;
  }
  /**
   * Identifies the probability density of the space's random symbol.
   *
   * @returns The value density.
   */
  override get valueDensity(): Expr {
    return this.distribution;
  }
  /**
   * Indicates whether the space may share an underlying symbol with another component.
   *
   * @returns The symbol-sharing flag.
   */
  override get sharesSymbols(): boolean {
    return this.distribution instanceof MarginalDistribution;
  }
  /**
   * Specifies the possible values of the random vector.
   *
   * @returns The joint support.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.set`
   */
  get set(): SetExpr {
    return this.domain.set;
  }
  /**
   * Counts the coordinates of the random vector.
   *
   * @returns The component count.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.component_count`
   */
  get componentCount(): Expr {
    const set = this.distribution.set;
    return set instanceof ProductSetNode ? sympify(set.args.length) : S.One;
  }
  /**
   * Expresses the joint density in the indexed components of the space's random symbol.
   *
   * @returns The joint density in the symbols of the space.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.pdf`
   */
  override get pdf(): Expr {
    const n = countOf(this.componentCount);
    return callDistribution(this.distribution, Array.from({ length: n }, (_, i) => new Indexed([this.symbol, sympify(i)])));
  }
  /**
   * Describes the possible outcomes of this probability space.
   *
   * @returns The outcome domain.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.domain`
   */
  override get domain(): RandomDomain {
    const rvs = randomSymbols(this.distribution);
    if (!rvs.length) return new SingleDomain([this.symbol, this.distribution.set]);
    return makeProductDomain(rvs.map((rv) => rv.pspace.domain));
  }
  /**
   * Finds the support of the component at the supplied index.
   *
   * @param index - Index of the component.
   * @returns The component domain.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.component_domain`
   */
  componentDomain(index: number): SetExpr {
    return cast(at(this.set.args, index), SetExpr, 'component set');
  }
  /**
   * Marginalizes the joint density to the selected components.
   *
   * @param indices - Component indices to retain.
   * @returns The marginal density lambda.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.marginal_distribution`
   */
  marginalDistribution(...indices: number[]): Expr {
    const count = countOf(this.componentCount);
    const orig = Array.from({ length: count }, (_, i) => new Indexed([this.symbol, sympify(i)]));
    const dist = cast(this.distribution, JointDistribution, 'joint distribution');
    const set = cast(dist.set, ProductSetNode, 'product set');
    // the components of a discrete vector are summed over integers, here nonnegative ones (SymPy's summation
    // symbols have no assumptions; its numerical evaluation of the sums decides the convergence conditions)
    const assumptions = (i: number): Assumptions => (dist.isContinuous ? {} : { integer: true, nonnegative: Ge(inf(cast(at(set.args, i), SetExpr)), 0) === S.true });
    const allSyms = orig.map((_, i) => componentSymbol(this.symbol, i, assumptions(i)));
    const sym = indices.map((i) => at(allSyms, i));
    const kept = new Set(indices);
    const limits = allSyms.flatMap((s, i) => (kept.has(i) ? [] : [limitOf(s, cast(at(set.args, i), SetExpr))]));
    const f = dist.pdf(...allSyms);
    const body = dist.isContinuous ? limits.reduce((acc, [x, a, b]) => integrate(acc, x, [a, b]), f) : summation(f, ...limits);
    return xreplace(Lambda(sym, body), allSyms.map((s, i) => [s, at(orig, i)] as const));
  }
  /**
   * Forms the expectation by integrating the expression against the joint density and treating random
   * variables from other spaces separately.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvsIn - Random variables to integrate or sum over.
   * @returns The expected value over the selected variables.
   * @throws NotImplementedError when the expression contains a joint symbol without component indices.
   * @see SymPy `sympy.stats.joint_rv.JointPSpace.compute_expectation`
   */
  override computeExpectation(exprIn: Expr, rvsIn?: readonly Expr[]): Expr {
    const n = countOf(this.componentCount);
    const syms = Array.from({ length: n }, (_, i) => new Indexed([this.value, sympify(i)]));
    const rvs = rvsIn ?? syms;
    const keys = new Set(rvs.map((r) => r.key));
    if (!syms.some((s) => keys.has(s.key))) return exprIn;
    const vars = syms.map((_, i) => componentSymbol(this.symbol, i));
    let expr = mul(exprIn, this.pdf);
    // the components of the value and of the plain symbol are the integration variables
    expr = xreplace(expr, [
      ...syms.map((s, i) => [s, at(vars, i)] as const),
      ...vars.map((v, i) => [new Indexed([this.symbol, sympify(i)]), v] as const),
      ...rvs.filter((r): r is RandomSymbol => r instanceof RandomSymbol).map((r) => [r, r.symbol] as const),
    ]);
    if (randomSymbols(expr).some((r) => r.key === this.value.key)) {
      throw new NotImplementedError('Expectations of expression with unindexed joint random symbols cannot be calculated yet.');
    }
    const set = cast(this.distribution.set, ProductSetNode, 'product set');
    const limits = vars.map((v, i) => limitOf(v, cast(at(set.args, i), SetExpr)));
    // SymPy integrates a discrete vector too (and fails on its Range limits): its components are summed
    const discrete = this.distribution instanceof JointDistribution && this.distribution.isDiscrete;
    return discrete ? Sum(expr, ...limits) : makeIntegral(expr, limits);
  }
}

/**
 * SymPy JointPSpace(sym, dist): a single continuous or discrete space for a
 * single-variable distribution, a joint space otherwise.
 */
export function jointPSpace(sym: string | Sym, dist: Distribution): PSpace & { value: RandomSymbol } {
  if (dist instanceof SingleContinuousDistribution) return new SingleContinuousPSpace([symbolConverter(sym), dist]);
  if (dist instanceof SingleDiscreteDistribution) return new SingleDiscretePSpace([symbolConverter(sym), dist]);
  return new JointPSpace([symbolConverter(sym), dist]);
}

// ---------------------------------------------------------------------------
// Joint random symbols
// ---------------------------------------------------------------------------

/**
 * A random vector whose components can be accessed with `at(i)`.
 *
 * @see SymPy `sympy.stats.joint_rv.JointRandomSymbol`
 */
export class JointRandomSymbol extends RandomSymbol {
  /**
   * Selects one coordinate of the joint random symbol.
   *
   * @param keyIn - Time or component index.
   * @returns The indexed random component.
   * @throws RangeError when the component index exceeds the dimension.
   * @see SymPy `sympy.stats.joint_rv.JointRandomSymbol.__getitem__`
   */
  at(keyIn: ExprLike): Indexed {
    const key = sympify(keyIn);
    const ps = this.pspace;
    if (ps instanceof JointPSpace && Le(ps.componentCount, key) === S.true) {
      throw new RangeError(`Index keys for ${this.name} can only up to ${sub(ps.componentCount, 1).toString()}.`);
    }
    return new Indexed([this, key]);
  }
}

// ---------------------------------------------------------------------------
// Marginal distributions
// ---------------------------------------------------------------------------

/**
 * A distribution whose random parameters are marginalised out.
 *
 * @see SymPy `sympy.stats.joint_rv.MarginalDistribution`
 */
export class MarginalDistribution extends Distribution {
  /**
   * Constructs a new `MarginalDistribution`.
   *
   * @param args - Operands in the order `dist`, `rvs`.
   */
  constructor(args: readonly Expr[]) {
    super('MarginalDistribution', args);
  }
  /**
   * Lists the random variables over which the distribution marginalizes.
   *
   * @returns The random variables of the distribution.
   */
  get rvs(): Expr[] {
    return [...at(this.args, 1).args];
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv.MarginalDistribution.set`
   */
  get set(): SetExpr {
    return productSet(...this.rvs.filter((r): r is RandomSymbol => r instanceof RandomSymbol).map((r) => r.pspace.domain.set));
  }
  /**
   * Collects the symbols underlying the component probability spaces.
   *
   * @returns The component symbols.
   * @see SymPy `sympy.stats.joint_rv.MarginalDistribution.symbols`
   */
  get symbols(): Sym[] {
    return sortedSymbols(this.rvs.flatMap((r) => pspace(r).symbols));
  }
  /**
   * Evaluates the joint density at the supplied coordinates.
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The joint density value.
   * @see SymPy `sympy.stats.joint_rv.MarginalDistribution.__call__`
   */
  override call(...x: ExprLike[]): Expr {
    return this.pdf(...x);
  }
  /**
   * Evaluates the density after marginalizing the random parameters.
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv.MarginalDistribution.pdf`
   */
  pdf(...x: ExprLike[]): Expr {
    let expr = at(this.args, 0);
    const keys = new Set(this.rvs.map((r) => r.key));
    let syms: Expr[];
    if (expr instanceof JointDistribution) {
      // SymPy iterates over the integer count (TypeError): the components of a real Dummy vector are the variables
      const count = cast(expr.set, ProductSetNode, 'product set').args.length;
      const v = new Dummy('x', { real: true });
      syms = Array.from({ length: count }, (_, i) => new Indexed([v, sympify(i)]));
      expr = expr.pdf(...syms);
    } else {
      syms = this.rvs.map((r) => (r instanceof RandomSymbol ? r.symbol : at(r.args, 0)));
    }
    // SymPy's atoms(RandomSymbol) also reaches the random parameters inside a variable's probability space
    const nested = new Map<string, RandomSymbol>();
    const collect = (e: Expr): void => {
      for (const r of randomSymbols(e)) {
        if (nested.has(r.key)) continue;
        nested.set(r.key, r);
        collect(r.pspace);
      }
    };
    collect(expr);
    const marginaliseOut = [...nested.values()].sort((p, q) => (p.symbol.name < q.symbol.name ? -1 : p.symbol.name > q.symbol.name ? 1 : 0)).filter((r) => !keys.has(r.key));
    return Lambda(syms, this.computePdf(expr, marginaliseOut)).call(...x);
  }
  /**
   * Weights the density by the component laws and marginalizes the random variables.
   *
   * @param exprIn - Expression to evaluate.
   * @param rvs - Random variables to integrate or sum over.
   * @returns The resulting probability density.
   * @see SymPy `sympy.stats.joint_rv.MarginalDistribution.compute_pdf`
   */
  computePdf(exprIn: Expr, rvs: readonly RandomSymbol[]): Expr {
    let expr = exprIn;
    for (const rv of rvs) expr = this.marginaliseOut(mul(expr, rv.pspace.pdf), rv);
    return expr;
  }
  /**
   * Forms the integral or sum over the possible values of the random variable.
   *
   * @param exprIn - Expression to evaluate.
   * @param rv - Random variable whose distribution is requested.
   * @returns The unevaluated marginalization.
   * @see SymPy `sympy.stats.joint_rv.MarginalDistribution.marginalise_out`
   */
  marginaliseOut(exprIn: Expr, rv: RandomSymbol): Expr {
    const sym = rv.symbol;
    const expr = xreplace(exprIn, [[rv, sym]]);
    // a joint space is neither continuous nor discrete in SymPy (PSpace.is_Continuous and is_Discrete are None):
    // the variable is only replaced by its symbol
    if (rv.pspace instanceof JointPSpace) return expr;
    const [x, a, b] = limitOf(sym, rv.pspace.domain.set);
    if (rv.pspace.isContinuous) return makeIntegral(expr, [[x, a, b]]);
    return Sum(expr, [x, a, b]);
  }
}

/**
 * SymPy MarginalDistribution(dist, *rvs): a distribution that is not joint
 * and has no random parameters is returned as it is.
 */
export function makeMarginalDistribution(dist: Distribution, rvs: readonly Expr[]): Distribution {
  if (!rvs.every((r) => r instanceof Indexed || r instanceof RandomSymbol)) {
    throw new RangeError('Marginal distribution can be intitialised only in terms of random variables or indexed random variables');
  }
  if (!(dist instanceof JointDistribution) && randomSymbols(dist).length === 0) return dist;
  return new MarginalDistribution([dist, new TupleNode(rvs)]);
}
