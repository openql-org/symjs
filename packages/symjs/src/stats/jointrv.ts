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

/** SymPy JointDistribution: a distribution of several variables, applied to one value of each (`pdf(x1, x2, ...)`). */
export abstract class JointDistribution extends Distribution {
  /** SymPy is_Continuous. */
  get isContinuous(): boolean {
    return false;
  }
  /** SymPy is_Discrete. */
  get isDiscrete(): boolean {
    return false;
  }
  /** The joint density at the values (SymPy pdf(*args)). */
  abstract override pdf(...xs: ExprLike[]): Expr;
  /** SymPy __call__: the density at the values. */
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
 * SymPy JointPSpace(sym, dist): the probability space of a random vector.
 * Use `jointPSpace`, which gives a single space for a single-variable
 * distribution as SymPy's constructor does.
 */
export class JointPSpace extends ProductPSpace {
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution')], 'JointPSpace');
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get distribution(): Distribution {
    return cast(at(this.args, 1), Distribution);
  }
  /** The joint random symbol of the space (SymPy value). */
  get value(): JointRandomSymbol {
    return new JointRandomSymbol(this.symbol, this);
  }
  override get values(): RandomSymbol[] {
    return [this.value];
  }
  override get hasValueDensity(): boolean {
    return true;
  }
  override get valueDensity(): Expr {
    return this.distribution;
  }
  override get sharesSymbols(): boolean {
    return this.distribution instanceof MarginalDistribution;
  }
  /** The values of the random vector (SymPy set). */
  get set(): SetExpr {
    return this.domain.set;
  }
  /** The number of components (SymPy component_count). */
  get componentCount(): Expr {
    const set = this.distribution.set;
    return set instanceof ProductSetNode ? sympify(set.args.length) : S.One;
  }
  /** The joint density as an expression of the components sym[i] (SymPy pdf). */
  override get pdf(): Expr {
    const n = countOf(this.componentCount);
    return callDistribution(this.distribution, Array.from({ length: n }, (_, i) => new Indexed([this.symbol, sympify(i)])));
  }
  override get domain(): RandomDomain {
    const rvs = randomSymbols(this.distribution);
    if (!rvs.length) return new SingleDomain([this.symbol, this.distribution.set]);
    return makeProductDomain(rvs.map((rv) => rv.pspace.domain));
  }
  /** The set of the component at an index (SymPy component_domain). */
  componentDomain(index: number): SetExpr {
    return cast(at(this.set.args, index), SetExpr, 'component set');
  }
  /** The marginal density of the components at the indices: a Lambda (SymPy marginal_distribution). */
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
   * The expectation of an expression of the components: the unevaluated
   * integral of the expression times the density over the components
   * (SymPy compute_expectation). Random symbols of other spaces are
   * expected separately: an expression without components of this space is
   * returned unchanged.
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

/** SymPy JointRandomSymbol: a random vector, whose components are `X.at(i)` (SymPy X[i]). */
export class JointRandomSymbol extends RandomSymbol {
  /** The component at an index (SymPy __getitem__): the Indexed X[i]. */
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

/** SymPy MarginalDistribution(dist, rvs): a distribution whose random parameters are marginalised out. */
export class MarginalDistribution extends Distribution {
  constructor(args: readonly Expr[]) {
    super('MarginalDistribution', args);
  }
  /** The random variables of the distribution (SymPy args[1]). */
  get rvs(): Expr[] {
    return [...at(this.args, 1).args];
  }
  get set(): SetExpr {
    return productSet(...this.rvs.filter((r): r is RandomSymbol => r instanceof RandomSymbol).map((r) => r.pspace.domain.set));
  }
  /** The symbols of the spaces of the random variables (SymPy symbols). */
  get symbols(): Sym[] {
    return sortedSymbols(this.rvs.flatMap((r) => pspace(r).symbols));
  }
  /** SymPy __call__: the density at the values. */
  override call(...x: ExprLike[]): Expr {
    return this.pdf(...x);
  }
  /** The density at the values, with the random parameters marginalised out (SymPy pdf). */
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
    const marginaliseOut = randomSymbols(expr).filter((r) => !keys.has(r.key));
    return Lambda(syms, this.computePdf(expr, marginaliseOut)).call(...x);
  }
  /** The density times the densities of the random variables, each marginalised out (SymPy compute_pdf). */
  computePdf(exprIn: Expr, rvs: readonly RandomSymbol[]): Expr {
    let expr = exprIn;
    for (const rv of rvs) expr = this.marginaliseOut(mul(expr, rv.pspace.pdf), rv);
    return expr;
  }
  /** The unevaluated integral (or sum) of the expression over the values of the random variable (SymPy marginalise_out). */
  marginaliseOut(exprIn: Expr, rv: RandomSymbol): Expr {
    const sym = rv.symbol;
    const expr = xreplace(exprIn, [[rv, sym]]);
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
