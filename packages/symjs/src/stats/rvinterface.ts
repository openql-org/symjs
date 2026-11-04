// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/rv_interface.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.rv_interface: the statistics of random
 * expressions built on the expectation (variance, standard deviation,
 * moments, skewness, kurtosis, covariance, correlation, coskewness,
 * entropy, median, factorial moments).
 */

import { Dummy, Rational, S } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { mul, pow, sqrt, sub, sympify } from '../core/ops';
import { Eq, Ge } from '../core/logic';
import { piecewiseFold } from '../core/traverse';
import { LambdaNode } from '../core/lambda';
import { NotImplementedError } from '../core/errors';
import { add } from '../core/ops';
import { cast } from '../core/guard';
import { SetExpr, finiteSet } from '../sets/sets';
import { solveset } from '../solvers/inequalities';
import { log } from '../functions/elementary/elementary';
import { ff } from '../functions/special/special';
import { rewrite } from '../simplify/rewrite';
import { Distribution, FiniteDensity, PSpace, density, expectation, isRandom, pspace } from './rv';
import type { ProbabilityOptions } from './rv';
import { ContinuousPSpace } from './crv';
import { DiscretePSpace } from './drv';
import { FinitePSpace, ProductFinitePSpace } from './frv';
import { CentralMomentNode, Covariance, MomentNode, VarianceNode, interfaceHooks } from './symbolicprobability';

/** The probability space is SymPy's PSpace() of a random symbol without a space. */
const isEmptySpace = (x: Expr): boolean => isRandom(x) && pspace(x).key === new PSpace().key;

/** The optional condition as an argument list. */
const cond = (args: readonly Expr[], condition: ExprLike | undefined): Expr[] => (condition === undefined ? [...args] : [...args, sympify(condition)]);

/** The n-th moment of X about c, optionally given a condition (SymPy moment). */
export function moment(X: ExprLike, n: ExprLike, c: ExprLike = 0, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const m = new MomentNode(cond([sympify(X), sympify(n), sympify(c)], condition));
  return opts.evaluate ?? true ? m.doit() : rewrite(m, 'Integral');
}

/** The variance of a random expression, optionally given a condition (SymPy variance). */
export function variance(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const x = sympify(X);
  if (isEmptySpace(x)) return new VarianceNode(cond([x], condition));
  return cmoment(x, 2, condition, opts);
}

/** The standard deviation of a random expression (SymPy std, standard_deviation). */
export function std(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return sqrt(variance(X, condition, opts));
}

/** Options of entropy. */
export interface EntropyOptions extends ProbabilityOptions {
  /** The base of the logarithm (SymPy b, default E). */
  readonly b?: ExprLike;
}

/** The entropy of a random expression (SymPy entropy, H). */
export function entropy(expr: ExprLike, condition?: ExprLike, opts: EntropyOptions = {}): Expr {
  const pdf = density(expr, condition, opts);
  const base = opts.b === undefined ? S.E : sympify(opts.b);
  const lg = (v: Expr): Expr => (base === S.E ? log(v) : log(v, base));
  if (pdf instanceof FiniteDensity) return add(...[...pdf.values()].map((prob) => mul(-1, prob, lg(prob))));
  const f = pdf instanceof LambdaNode ? pdf.call(sympify(expr)) : cast(pdf, Distribution, 'density').pdf(sympify(expr));
  return expectation(mul(-1, lg(f)));
}

/** SymPy H: the entropy. */
export const H = entropy;

/** The covariance of two random expressions (SymPy covariance). */
export function covariance(X: ExprLike, Y: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const [x, y] = [sympify(X), sympify(Y)];
  if (isEmptySpace(x) || isEmptySpace(y)) {
    return Covariance(x, y, condition);
  }
  return expectation(mul(sub(x, expectation(x, condition, opts)), sub(y, expectation(y, condition, opts))), condition, opts);
}

/** The correlation of two random expressions (SymPy correlation). */
export function correlation(X: ExprLike, Y: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return mul(covariance(X, Y, condition, opts), pow(mul(std(X, condition, opts), std(Y, condition, opts)), -1));
}

/** The n-th central moment of a random expression (SymPy cmoment). */
export function cmoment(X: ExprLike, n: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const m = new CentralMomentNode(cond([sympify(X), sympify(n)], condition));
  return opts.evaluate ?? true ? m.doit() : rewrite(m, 'Integral');
}

/** The n-th standardized moment of a random expression (SymPy smoment). */
export function smoment(X: ExprLike, n: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const sigma = std(X, condition, opts);
  return mul(pow(pow(sigma, -1), n), cmoment(X, n, condition, opts));
}

/** The skewness of a random expression (SymPy skewness). */
export function skewness(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return smoment(X, 3, condition, opts);
}

/** The kurtosis of a random expression (SymPy kurtosis). */
export function kurtosis(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return smoment(X, 4, condition, opts);
}

/** The n-th factorial moment E(X*(X - 1)*...*(X - n + 1)) (SymPy factorial_moment). */
export function factorialMoment(X: ExprLike, n: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return expectation(ff(X, n), condition, opts);
}

/** The median of a random expression: the set of medians (SymPy median). */
export function median(X: ExprLike): Expr {
  const x = sympify(X);
  if (!isRandom(x)) return x;
  const ps = pspace(x);
  // a product of finite spaces has no cdf (SymPy ValueError)
  if (ps instanceof FinitePSpace || ps instanceof ProductFinitePSpace) {
    const c = cast(ps.computeCdf(x), FiniteDensity);
    const result: Expr[] = [];
    for (const [key, value] of c) {
      const upper = add(sub(1, value), ps.probability(Eq(x, key)));
      if (Ge(value, Rational.of(1, 2)) === S.true && Ge(upper, Rational.of(1, 2)) === S.true) result.push(key);
    }
    return finiteSet(...result);
  }
  if (ps instanceof ContinuousPSpace || ps instanceof DiscretePSpace) {
    const c = ps.computeCdf(x);
    const v = new Dummy('x');
    const f = cast(c, LambdaNode, 'cdf').call(v);
    return solveset(piecewiseFold(sub(f, Rational.of(1, 2))), v, spaceSet(ps));
  }
  throw new NotImplementedError(`The median of ${ps.toString()} is not implemented.`);
}

/** The set of a single space (SymPy pspace(X).set). */
function spaceSet(ps: PSpace): SetExpr {
  const s = (ps as PSpace & { set?: unknown }).set;
  return cast(s, SetExpr, 'set of the probability space');
}

/** The coskewness of three random expressions (SymPy coskewness). */
export function coskewness(X: ExprLike, Y: ExprLike, Z: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const [x, y, z] = [sympify(X), sympify(Y), sympify(Z)];
  const num = expectation(
    mul(sub(x, expectation(x, condition, opts)), sub(y, expectation(y, condition, opts)), sub(z, expectation(z, condition, opts))),
    condition,
    opts,
  );
  const den = mul(std(x, condition, opts), std(y, condition, opts), std(z, condition, opts));
  return mul(num, pow(den, -1));
}

interfaceHooks.variance = (x, condition, evaluate) => variance(x, condition, { evaluate });
interfaceHooks.covariance = (x, y, condition, evaluate) => covariance(x, y, condition, { evaluate });
