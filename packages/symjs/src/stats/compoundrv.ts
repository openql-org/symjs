// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/compound_rv.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.compound_rv: compound distributions, whose
 * parameters are themselves random (`Normal('X', Normal('Y', 0, 1), 1)`).
 * The density is marginalised over the random parameters, which gives a
 * handmade distribution of the same kind.
 */

import { Dummy, Integral, Mul, Pow, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, exp, mul } from '../core/ops';
import { expandMul as expand } from '../simplify/expand';
import { Sum } from '../core/concrete';
import type { LambdaNode } from '../core/lambda';
import { Lambda } from '../core/lambda';
import { NotImplementedError } from '../core/errors';
import { at, cast } from '../core/guard';
import { inf, sup } from '../sets/sets';
import type { SetExpr } from '../sets/sets';
import { doit } from '../calculus/doit';
import { piecewiseFold } from '../core/traverse';
import { Distribution, PSpace, RandomSymbol, isRandom, randomSymbols, statsClasses, symbolConverter } from './rv';
import type { ComputeOptions, DensityResult , RandomDomain} from './rv';
import { ContinuousDistribution, SingleContinuousPSpace } from './crv';
import { DiscreteDistribution, SingleDiscretePSpace } from './drv';
import { SingleFiniteDistribution, SingleFinitePSpace } from './frv';
import { ContinuousDistributionHandmade } from './crvtypes';
import { DiscreteDistributionHandmade } from './drvtypes';
import { FiniteDistributionHandmade } from './frvtypes';
import { Dict } from '../core/containers';

/** SymPy CompoundDistribution(dist): a distribution with random parameters. Use `compoundDistribution` to build one. */
export class CompoundDistribution extends Distribution {
  constructor(args: readonly Expr[]) {
    super('CompoundDistribution', [cast(at(args, 0), Distribution, 'distribution')]);
  }
  /** The distribution with random parameters. */
  get dist(): Distribution {
    return cast(at(this.args, 0), Distribution);
  }
  /** Rebuilt like SymPy's constructor: the distribution itself once no parameter is random. */
  override withArgs(args: readonly Expr[]): Expr {
    return compoundDistribution(cast(at(args, 0), Distribution, 'distribution'));
  }
  get set(): SetExpr {
    return this.dist.set;
  }
  /** SymPy is_Continuous, is_Finite and is_Discrete. */
  get isContinuous(): boolean {
    return this.dist instanceof ContinuousDistribution;
  }
  override get isFinite(): boolean {
    return this.dist instanceof SingleFiniteDistribution;
  }
  get isDiscrete(): boolean {
    return this.dist instanceof DiscreteDistribution;
  }
  /** The density marginalised over the random parameters, evaluated or not (SymPy pdf(x, evaluate)). */
  pdf(x: ExprLike, evaluate = false): Expr {
    const dist = this.dist;
    const randoms = dist.args.filter((rv) => isRandom(rv));
    // SymPy marginalises the density at a dummy and applies the Lambda to x; marginalising the density at x
    // gives the same function, and the integral of a finite pmf at a value has no Piecewise left
    let e = dist instanceof SingleFiniteDistribution ? dist.pmf(x) : dist.pdf(x);
    for (const rv of randoms) e = marginalise(e, cast(rv, RandomSymbol, 'random parameter'), evaluate);
    return e;
  }
}

/** The density times the density of the random parameter, summed or integrated over it (SymPy _marginalise). */
function marginalise(e: Expr, rv: RandomSymbol, evaluate: boolean): Expr {
  const ps = rv.pspace;
  const dist = cast((ps as PSpace & { distribution?: unknown }).distribution, Distribution, 'distribution of the random parameter');
  const rvDens = dist instanceof SingleFiniteDistribution ? dist.pmf(rv) : dist.pdf(rv);
  const dom = ps.domain.set;
  // SymPy's Integral and Sum fold a Piecewise in their function (AddWithLimits: piecewise_fold)
  const body = piecewiseFold(mul(e, rvDens));
  if (ps.isDiscrete || ps.isFinite) {
    const sum = Sum(body, [rv, inf(dom), sup(dom)]);
    return evaluate ? doit(sum) : sum;
  }
  return evaluate ? doit(new Integral([combineExponentials(body, rv), rv, inf(dom), sup(dom)])) : new Integral([body, rv, inf(dom), sup(dom)]);
}

/** exp(a)*exp(b) with the parameter in both exponents as one exponential: a Gaussian mixture is then integrated in closed form. */
function combineExponentials(body: Expr, rv: RandomSymbol): Expr {
  if (!(body instanceof Mul)) return body;
  const exponentials = body.args.filter((g): g is Pow => g instanceof Pow && g.base === S.E && g.exp.has(rv));
  if (exponentials.length < 2) return body;
  return mul(...body.args.filter((g) => !exponentials.some((h) => h === g)), exp(expand(add(...exponentials.map((g) => g.exp)))));
}

/** SymPy CompoundDistribution(dist): the distribution itself when no parameter is random. */
export function compoundDistribution(dist: Distribution): Distribution {
  if (!(dist instanceof ContinuousDistribution || dist instanceof SingleFiniteDistribution || dist instanceof DiscreteDistribution)) {
    throw new NotImplementedError(`Compound Distribution for ${dist.toString()} is not implemented yet`);
  }
  if (!dist.args.some((a) => randomSymbols(a).length > 0)) return dist;
  return new CompoundDistribution([dist]);
}

/** SymPy CompoundPSpace(s, distribution): the probability space of a compound distribution. Use `compoundPSpace` to build one. */
export class CompoundPSpace extends PSpace {
  constructor(args: readonly Expr[]) {
    super([symbolConverter(at(args, 0)), cast(at(args, 1), CompoundDistribution, 'compound distribution')], 'CompoundPSpace');
  }
  /** Rebuilt like SymPy's constructor: the single space of its kind once the distribution is not compound. */
  override withArgs(args: readonly Expr[]): Expr {
    return compoundPSpace(symbolConverter(at(args, 0)), cast(at(args, 1), Distribution, 'distribution'));
  }
  override get isCompound(): boolean {
    return true;
  }
  override get isSingle(): boolean {
    return true;
  }
  get value(): RandomSymbol {
    return new RandomSymbol(this.symbol, this);
  }
  get symbol(): Sym {
    return cast(at(this.args, 0), Sym);
  }
  get distribution(): CompoundDistribution {
    return cast(at(this.args, 1), CompoundDistribution);
  }
  override get isContinuous(): boolean {
    return this.distribution.isContinuous;
  }
  override get isFinite(): boolean {
    return this.distribution.isFinite;
  }
  override get isDiscrete(): boolean {
    return this.distribution.isDiscrete;
  }
  override get pdf(): Expr {
    return this.distribution.pdf(this.symbol);
  }
  get set(): SetExpr {
    return this.distribution.set;
  }
  override get domain(): RandomDomain {
    return this.getNewPSpace().domain;
  }
  /** The space of the marginalised density (SymPy _get_newpspace). */
  getNewPSpace(evaluate = false): PSpace {
    const x = new Dummy('x');
    const parentDist = this.distribution.dist;
    const func = Lambda(x, this.distribution.pdf(x, evaluate));
    return transformPSpace(this.symbol, parentDist, func, evaluate);
  }
  override computeDensity(expr: Expr, opts: ComputeOptions = {}): DensityResult {
    const ps = this.getNewPSpace(opts.compoundEvaluate ?? true);
    return ps.computeDensity(expr.subs(this.value, valueOf(ps)), opts);
  }
  override computeCdf(expr: Expr, opts: ComputeOptions = {}): DensityResult {
    const ps = this.getNewPSpace(opts.compoundEvaluate ?? true);
    return ps.computeCdf(expr.subs(this.value, valueOf(ps)), opts);
  }
  override computeExpectation(expr: Expr, rvs?: readonly RandomSymbol[], opts: ComputeOptions = {}): Expr {
    const ps = this.getNewPSpace(opts.evaluate ?? false);
    const v = valueOf(ps);
    const e = expr.subs(this.value, v);
    const rvs2 = rvs?.map((r) => (r.key === this.value.key ? v : r));
    return ps.computeExpectation(e, rvs2, opts);
  }
  override probability(condition: Expr, opts: ComputeOptions = {}): Expr {
    const ps = this.getNewPSpace(opts.compoundEvaluate ?? true);
    return ps.probability(condition.subs(this.value, valueOf(ps)));
  }
  override conditionalSpace(condition: Expr, opts: ComputeOptions = {}): PSpace {
    const ps = this.getNewPSpace(opts.compoundEvaluate ?? true);
    return ps.conditionalSpace(condition.subs(this.value, valueOf(ps)));
  }
}

/** The random symbol of a single space. */
function valueOf(ps: PSpace): RandomSymbol {
  return cast((ps as PSpace & { value?: unknown }).value, RandomSymbol, 'value of the space');
}

/** The space of a handmade distribution with the marginalised density (SymPy _transform_pspace). */
function transformPSpace(sym: Sym, dist: Distribution, pdfIn: LambdaNode, evaluate: boolean): PSpace {
  const pdf = Lambda(sym, pdfIn.call(sym));
  const set = dist.set;
  if (dist instanceof ContinuousDistribution) return new SingleContinuousPSpace([sym, new ContinuousDistributionHandmade([pdf, set])]);
  if (dist instanceof DiscreteDistribution) return new SingleDiscretePSpace([sym, new DiscreteDistributionHandmade([pdf, set])]);
  const finite = cast(dist, SingleFiniteDistribution);
  const values = finite.set.args;
  return new SingleFinitePSpace([sym, new FiniteDistributionHandmade([Dict(values.map((k) => [k, evaluate ? doit(pdf.call(k)) : pdf.call(k)] as const))])]);
}

/**
 * SymPy CompoundPSpace(s, distribution): a compound distribution gives a
 * CompoundPSpace, any other the single space of its kind.
 */
export function compoundPSpace(s: string | Sym, distribution: Distribution): PSpace {
  const sym = symbolConverter(s);
  if (distribution instanceof ContinuousDistribution) return new SingleContinuousPSpace([sym, distribution]);
  if (distribution instanceof DiscreteDistribution) return new SingleDiscretePSpace([sym, distribution]);
  if (distribution instanceof SingleFiniteDistribution) return new SingleFinitePSpace([sym, distribution]);
  if (!(distribution instanceof CompoundDistribution)) throw new RangeError(`${distribution.toString()} should be an isinstance of CompoundDistribution`);
  return new CompoundPSpace([sym, distribution]);
}

statsClasses.compound = (symbol, dist) => valueOf(compoundPSpace(symbol, compoundDistribution(dist)));
