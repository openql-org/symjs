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
import { ff } from '../functions/combinatorial/factorials';
import { rewrite } from '../simplify/rewrite';
import { Distribution, FiniteDensity, PSpace, density, expectation, isRandom, pspace } from './rv';
import type { ProbabilityOptions } from './rv';
import { ContinuousPSpace } from './crv';
import { DiscretePSpace } from './drv';
import { FinitePSpace, ProductFinitePSpace } from './frv';
import { CentralMomentNode, Covariance, MomentNode, Variance, interfaceHooks } from './symbolicprobability';

/** The probability space is SymPy's PSpace() of a random symbol without a space. */
const isEmptySpace = (x: Expr): boolean => isRandom(x) && pspace(x).key === new PSpace().key;

/** The optional condition as an argument list. */
const cond = (args: readonly Expr[], condition: ExprLike | undefined): Expr[] => (condition === undefined ? [...args] : [...args, sympify(condition)]);

/**
 * The n-th moment of X about c, optionally given a condition.
 *
 * @param X - Random expression.
 * @param n - Order of the moment.
 * @param c - Center about which to take the moment.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The expectation of `(X - c)**n`.
 * @see SymPy `sympy.stats.rv_interface.moment`
 * @example
 * ```ts
 * import { Die, moment } from '@symjs/symjs';
 *
 * const X = Die('X', 6);
 * moment(X, 1, 6); // => -5/2
 * ```
 */
export function moment(X: ExprLike, n: ExprLike, c: ExprLike = 0, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const m = new MomentNode(cond([sympify(X), sympify(n), sympify(c)], condition));
  return opts.evaluate ?? true ? m.doit() : rewrite(m, 'Integral');
}

/**
 * The variance of a random expression, optionally given a condition.
 *
 * @param X - Random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The second central moment.
 * @see SymPy `sympy.stats.rv_interface.variance`
 * @example
 * ```ts
 * import { Die, variance } from '@symjs/symjs';
 *
 * const X = Die('X', 6);
 * variance(X.mul(2)); // => 35/3
 * ```
 */
export function variance(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const x = sympify(X);
  if (isEmptySpace(x)) return Variance(x, condition);
  return cmoment(x, 2, condition, opts);
}

/**
 * The standard deviation of a random expression (SymPy std, standard_deviation).
 *
 * @param X - Random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The square root of the variance.
 * @see SymPy `sympy.stats.rv_interface.standard_deviation`
 * @example
 * ```ts
 * import { Bernoulli, ex, std } from '@symjs/symjs';
 *
 * const B = Bernoulli('B', ex`1/2`);
 * std(B); // => 1/2
 * ```
 */
export function std(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return sqrt(variance(X, condition, opts));
}

/** Options of entropy. */
export interface EntropyOptions extends ProbabilityOptions {
  /** The base of the logarithm (SymPy b, default E). */
  readonly b?: ExprLike;
}

/**
 * The entropy of a random expression (SymPy entropy, H).
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Use `b` for the logarithm base and `evaluate` to control evaluation.
 * @returns The entropy in the requested logarithm base.
 * @see SymPy `sympy.stats.rv_interface.entropy`
 * @example
 * ```ts
 * import { Die, entropy } from '@symjs/symjs';
 *
 * entropy(Die('D', 4)); // => log(4)
 * ```
 */
export function entropy(expr: ExprLike, condition?: ExprLike, opts: EntropyOptions = {}): Expr {
  const pdf = density(expr, condition, opts);
  const base = opts.b === undefined ? S.E : sympify(opts.b);
  const lg = (v: Expr): Expr => (base === S.E ? log(v) : log(v, base));
  if (pdf instanceof FiniteDensity) return add(...[...pdf.values()].map((prob) => mul(-1, prob, lg(prob))));
  const f = pdf instanceof LambdaNode ? pdf.call(sympify(expr)) : cast(pdf, Distribution, 'density').pdf(sympify(expr));
  return expectation(mul(-1, lg(f)));
}

/**
 * Computes the entropy of a random expression.
 *
 * @param expr - Expression to evaluate.
 * @param condition - Condition on the random variables.
 * @param opts - Use `b` for the logarithm base and `evaluate` to control evaluation.
 * @returns The entropy in the requested logarithm base.
 * @see SymPy `sympy.stats.rv_interface.entropy`
 * @example
 * ```ts
 * import { Die, H } from '@symjs/symjs';
 *
 * H(Die('D', 4)); // => log(4)
 * ```
 */
export const H = entropy;

/**
 * The covariance of two random expressions.
 *
 * @param X - Random expression.
 * @param Y - Second random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The expectation of the product of the centered variables.
 * @see SymPy `sympy.stats.rv_interface.covariance`
 * @example
 * ```ts
 * import { Exponential, covariance } from '@symjs/symjs';
 *
 * const X = Exponential('X', 1), Y = Exponential('Y', 1);
 * covariance(X, Y); // => 0
 * ```
 */
export function covariance(X: ExprLike, Y: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const [x, y] = [sympify(X), sympify(Y)];
  if (isEmptySpace(x) || isEmptySpace(y)) {
    return Covariance(x, y, condition);
  }
  return expectation(mul(sub(x, expectation(x, condition, opts)), sub(y, expectation(y, condition, opts))), condition, opts);
}

/**
 * The correlation of two random expressions.
 *
 * @param X - Random expression.
 * @param Y - Second random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The covariance divided by the product of the standard deviations.
 * @see SymPy `sympy.stats.rv_interface.correlation`
 * @example
 * ```ts
 * import { Exponential, correlation } from '@symjs/symjs';
 *
 * const X = Exponential('X', 1), Y = Exponential('Y', 1);
 * correlation(X, Y); // => 0
 * ```
 */
export function correlation(X: ExprLike, Y: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return mul(covariance(X, Y, condition, opts), pow(mul(std(X, condition, opts), std(Y, condition, opts)), -1));
}

/**
 * The n-th central moment of a random expression.
 *
 * @param X - Random expression.
 * @param n - Order of the moment.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The moment of order `n` about the mean.
 * @see SymPy `sympy.stats.rv_interface.cmoment`
 * @example
 * ```ts
 * import { Die, cmoment } from '@symjs/symjs';
 *
 * const X = Die('X', 6);
 * cmoment(X, 3); // => 0
 * ```
 */
export function cmoment(X: ExprLike, n: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const m = new CentralMomentNode(cond([sympify(X), sympify(n)], condition));
  return opts.evaluate ?? true ? m.doit() : rewrite(m, 'Integral');
}

/**
 * The n-th standardized moment of a random expression.
 *
 * @param X - Random expression.
 * @param n - Order of the moment.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The central moment divided by the standard deviation to power `n`.
 * @see SymPy `sympy.stats.rv_interface.smoment`
 * @example
 * ```ts
 * import { Exponential, smoment } from '@symjs/symjs';
 *
 * const Y = Exponential('Y', 1);
 * smoment(Y, 4); // => 9
 * ```
 */
export function smoment(X: ExprLike, n: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  const sigma = std(X, condition, opts);
  return mul(pow(pow(sigma, -1), n), cmoment(X, n, condition, opts));
}

/**
 * The skewness of a random expression.
 *
 * @param X - Random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The third standardized moment.
 * @see SymPy `sympy.stats.rv_interface.skewness`
 * @example
 * ```ts
 * import { Gt, Normal, simplify, skewness } from '@symjs/symjs';
 *
 * skewness(Normal('X', 0, 1)); // => 0
 * const X = Normal('X', 0, 1);
 * simplify(skewness(X, Gt(X, 0))); // => sqrt(2)*(4 - pi)/(-2 + pi)**(3/2)
 * ```
 */
export function skewness(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return smoment(X, 3, condition, opts);
}

/**
 * The kurtosis of a random expression.
 *
 * @param X - Random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The fourth standardized moment.
 * @see SymPy `sympy.stats.rv_interface.kurtosis`
 * @example
 * ```ts
 * import { Normal, kurtosis } from '@symjs/symjs';
 *
 * kurtosis(Normal('X', 0, 1)); // => 3
 * ```
 */
export function kurtosis(X: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return smoment(X, 4, condition, opts);
}

/**
 * The n-th factorial moment E(X*(X - 1)*...*(X - n + 1)).
 *
 * @param X - Random expression.
 * @param n - Order of the moment.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The expectation of the falling factorial of order `n`.
 * @see SymPy `sympy.stats.rv_interface.factorial_moment`
 * @example
 * ```ts
 * import { Binomial, ex, factorialMoment } from '@symjs/symjs';
 *
 * factorialMoment(Binomial('Y', 2, ex`1/2`), 2); // => 1/2
 * ```
 */
export function factorialMoment(X: ExprLike, n: ExprLike, condition?: ExprLike, opts: ProbabilityOptions = {}): Expr {
  return expectation(ff(X, n), condition, opts);
}

/**
 * The median of a random expression: the set of medians.
 *
 * @param X - Random expression.
 * @returns The set of medians of a random expression, or the input value for a deterministic expression.
 * @throws NotImplementedError when no median algorithm is available for the probability space.
 * @see SymPy `sympy.stats.rv_interface.median`
 * @example
 * ```ts
 * import { Normal, median } from '@symjs/symjs';
 *
 * median(Normal('N', 3, 1)); // => {3}
 * ```
 */
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

/**
 * The coskewness of three random expressions.
 *
 * @param X - Random expression.
 * @param Y - Second random expression.
 * @param Z - Third random expression.
 * @param condition - Condition on the random variables.
 * @param opts - Set `evaluate` to false to retain an unevaluated expression.
 * @returns The normalized mixed third central moment.
 * @see SymPy `sympy.stats.rv_interface.coskewness`
 * @example
 * ```ts
 * import { Exponential, coskewness } from '@symjs/symjs';
 *
 * const X = Exponential('X', 1), Y = Exponential('Y', 1);
 * coskewness(X, Y, Y); // => 0
 * ```
 */
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
