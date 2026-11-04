// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/symbolic_multivariate_probability.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.symbolic_multivariate_probability: the
 * unevaluated expectation, variance and cross-covariance of random vectors
 * and matrices (ExpectationMatrix, VarianceMatrix and
 * CrossCovarianceMatrix). They are matrix expressions (SymPy derives them
 * from Expectation, Variance and Covariance and from MatrixExpr); `expand`
 * uses the linearity of the expectation, and `doit` evaluates the
 * expectation of an explicit matrix entry by entry.
 */

import { S } from '../core/nodes';
import type { Expr, ExprLike } from '../core/nodes';
import { mul, sympify } from '../core/ops';
import { callableClass } from '../core/callable';
import { ShapeError } from '../core/errors';
import { at, cast } from '../core/guard';
import { doit } from '../calculus/doit';
import { ImmutableMatrixNode, MatAddNode, MatMulNode, MatrixExpr, ZeroMatrixNode, transposeOf } from '../matrices/expressions/matexpr';
import { RandomMatrixSymbol, RandomSymbol, isRandom, statsClasses } from './rv';
import { expectation } from './rv';

/** The arguments with an optional condition. */
const withCondition = (args: readonly Expr[], condition: Expr | undefined): Expr[] => (condition === undefined ? [...args] : [...args, condition]);

/** SymPy expand of a matrix expression or a scalar. */
const expand = (e: Expr): Expr => cast(e, MatrixExpr, 'matrix').expand();

/** The shape of a matrix argument. */
const shapeOf = (e: Expr): [Expr, Expr] => cast(e, MatrixExpr, 'matrix').shape;

/** SymPy isinstance(x, RandomSymbol): a random symbol or random matrix symbol. */
const isRandomSymbol = (e: Expr): boolean => e instanceof RandomSymbol || e instanceof RandomMatrixSymbol;

/** The product of the factors in order (SymPy Mul.fromiter of scalars and matrices). */
function product(fs: readonly Expr[]): Expr {
  return fs.reduce<Expr>((acc, f) => (acc instanceof MatrixExpr ? acc.mul(f) : f instanceof MatrixExpr ? f.rmul(acc) : mul(acc, f)), S.One);
}

/** The sum of the matrix terms (SymPy Add.fromiter of matrices). */
function sum(ts: readonly Expr[]): Expr {
  return ts.slice(1).reduce<Expr>((acc, t) => cast(acc, MatrixExpr, 'matrix').add(t), at(ts, 0));
}

/** The expression is a matrix product (SymPy Mul and MatMul). */
const isProduct = (e: Expr): boolean => e instanceof MatMulNode;

/** The expression is a matrix sum (SymPy Add and MatAdd). */
const isSum = (e: Expr): boolean => e instanceof MatAddNode;

/** A matrix-valued stats node: its shape is computed from the arguments. */
abstract class MatrixStatsNode extends MatrixExpr {
  /** The given condition, if any. */
  abstract get condition(): Expr | undefined;
}

// ---------------------------------------------------------------------------
// ExpectationMatrix
// ---------------------------------------------------------------------------

/** SymPy ExpectationMatrix(expr, condition): the expectation of a random vector or matrix. */
export class ExpectationMatrixNode extends MatrixStatsNode {
  constructor(args: readonly Expr[]) {
    super('ExpectationMatrix', args);
  }
  get condition(): Expr | undefined {
    return this.args[1];
  }
  get shape(): [Expr, Expr] {
    return shapeOf(at(this.args, 0));
  }
  withArgs(args: readonly Expr[]): Expr {
    return new ExpectationMatrixNode(args);
  }
  /** The expectations of the terms and of the random factors of products (SymPy ExpectationMatrix.expand). */
  override expand(): Expr {
    const e = at(this.args, 0);
    const condition = this.condition;
    if (!isRandom(e)) return e;
    if (isSum(e)) return sum(e.args.map((a) => expandExpectation(a, condition)));
    const expandExpr = expand(e);
    if (isSum(expandExpr)) return sum(expandExpr.args.map((a) => expandExpectation(a, condition)));
    if (isProduct(e)) {
      const rv: Expr[] = [];
      const nonrv: Expr[] = [];
      let postnon: Expr[] = [];
      for (const a of e.args) {
        if (isRandom(a)) {
          (rv.length ? rv : nonrv).push(...postnon);
          postnon = [];
          rv.push(a);
        } else if (a instanceof MatrixExpr) postnon.push(a);
        else nonrv.push(a);
      }
      // MatMul may call doit again: the node is not rebuilt (SymPy avoids an infinite loop)
      if (nonrv.length === 0) return this;
      return product([...nonrv, makeExpectationMatrix(product(rv), condition), ...postnon]);
    }
    return this;
  }
  /** The expected value: entry by entry for an explicit matrix (SymPy Expectation.doit). */
  override doit(hints: { deep?: boolean } = {}): Expr {
    const e = hints.deep ?? true ? doit(at(this.args, 0)) : at(this.args, 0);
    if (!isRandom(e) || e instanceof ExpectationMatrixNode) return e;
    const condition = this.condition;
    if (e instanceof ImmutableMatrixNode) return new ImmutableMatrixNode(e.matrix.map((x) => expectation(x, condition)));
    return new ExpectationMatrixNode(withCondition([e], condition));
  }
}

/** The expectation of a term, expanded (SymPy Expectation(a, condition).expand()). */
function expandExpectation(a: Expr, condition: Expr | undefined): Expr {
  const node = makeExpectationMatrix(a, condition);
  return node instanceof ExpectationMatrixNode ? node.expand() : node;
}

/** SymPy ExpectationMatrix(expr, condition=None): a value that is not random is its own expectation. */
export function makeExpectationMatrix(exprIn: ExprLike, conditionIn?: ExprLike): Expr {
  const e = sympify(exprIn);
  if (conditionIn === undefined) return isRandom(e) ? new ExpectationMatrixNode([e]) : e;
  return new ExpectationMatrixNode([e, sympify(conditionIn)]);
}

/** SymPy ExpectationMatrix(expr, condition=None). */
export const ExpectationMatrix = /* @__PURE__ */ callableClass(ExpectationMatrixNode, makeExpectationMatrix);
export type ExpectationMatrix = ExpectationMatrixNode;

// ---------------------------------------------------------------------------
// VarianceMatrix
// ---------------------------------------------------------------------------

/** The dimension is 1. */
const isOne = (d: Expr): boolean => d.key === S.One.key;

/** SymPy VarianceMatrix(arg, condition): the variance-covariance matrix of a random vector. */
export class VarianceMatrixNode extends MatrixStatsNode {
  constructor(args: readonly Expr[]) {
    const [r, c] = shapeOf(at(args, 0));
    if (!isOne(r) && !isOne(c)) throw new ShapeError('Expression is not a vector');
    super('VarianceMatrix', args);
  }
  get condition(): Expr | undefined {
    return this.args[1];
  }
  get shape(): [Expr, Expr] {
    const [r, c] = shapeOf(at(this.args, 0));
    return isOne(c) ? [r, r] : [c, c];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new VarianceMatrixNode(args);
  }
  /** The variances and cross-covariances of the terms (SymPy VarianceMatrix.expand). */
  override expand(): Expr {
    const arg = at(this.args, 0);
    const condition = this.condition;
    const [r, c] = this.shape;
    if (!isRandom(arg)) return new ZeroMatrixNode(r, c);
    if (isRandomSymbol(arg)) return this;
    if (isSum(arg)) {
      const rv = arg.args.filter((a) => isRandom(a));
      const variances = rv.map((xv) => new VarianceMatrixNode(withCondition([xv], condition)).expand());
      const covariances: Expr[] = [];
      for (let i = 0; i < rv.length; i++) {
        for (let j = i + 1; j < rv.length; j++) covariances.push(product([sympify(2), new CrossCovarianceMatrixNode(withCondition([at(rv, i), at(rv, j)], condition)).expand()]));
      }
      return sum([...variances, ...covariances]);
    }
    if (isProduct(arg)) {
      const rv = arg.args.filter((a) => isRandom(a));
      const nonrv = arg.args.filter((a) => !isRandom(a));
      // MatMul may call doit again: the node is not rebuilt; the variance of several random factors is not implemented
      if (nonrv.length === 0 || rv.length > 1) return this;
      const m = product(nonrv);
      return product([m, new VarianceMatrixNode(withCondition([product(rv)], condition)), transposeOf(m)]);
    }
    return this;
  }
}

/** SymPy VarianceMatrix(arg, condition=None). */
export const VarianceMatrix = /* @__PURE__ */ callableClass(
  VarianceMatrixNode,
  (arg: ExprLike, condition?: ExprLike): VarianceMatrixNode => new VarianceMatrixNode(withCondition([sympify(arg)], condition === undefined ? undefined : sympify(condition))),
);
export type VarianceMatrix = VarianceMatrixNode;

// ---------------------------------------------------------------------------
// CrossCovarianceMatrix
// ---------------------------------------------------------------------------

/** SymPy CrossCovarianceMatrix(arg1, arg2, condition): the cross-covariance matrix of two random vectors. */
export class CrossCovarianceMatrixNode extends MatrixStatsNode {
  constructor(args: readonly Expr[]) {
    const [s1, s2] = [shapeOf(at(args, 0)), shapeOf(at(args, 1))];
    if ((!isOne(s1[0]) && !isOne(s1[1])) || (!isOne(s2[0]) && !isOne(s2[1])) || s1[1].key !== s2[1].key) throw new ShapeError('Expression is not a vector');
    super('CrossCovarianceMatrix', args);
  }
  get condition(): Expr | undefined {
    return this.args[2];
  }
  get shape(): [Expr, Expr] {
    const [s1, s2] = [shapeOf(at(this.args, 0)), shapeOf(at(this.args, 1))];
    return isOne(s1[1]) && isOne(s2[1]) ? [s1[0], s2[0]] : [S.One, S.One];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CrossCovarianceMatrixNode(args);
  }
  /** The cross-covariances of the random terms (SymPy CrossCovarianceMatrix.expand). */
  override expand(): Expr {
    const [arg1, arg2] = [at(this.args, 0), at(this.args, 1)];
    const condition = this.condition;
    if (arg1.key === arg2.key) return new VarianceMatrixNode(withCondition([arg1], condition)).expand();
    const [r, c] = this.shape;
    if (!isRandom(arg1) || !isRandom(arg2)) return new ZeroMatrixNode(r, c);
    if (isRandomSymbol(arg1) && isRandomSymbol(arg2)) return this;
    const list1 = expandSingleArgument(expand(arg1));
    const list2 = expandSingleArgument(expand(arg2));
    return sum(list1.flatMap(([a, r1]) => list2.map(([b, r2]) => product([a, new CrossCovarianceMatrixNode(withCondition([r1, r2], condition)), transposeOf(b)]))));
  }
}

/** The (coefficient, random part) pairs of the terms (SymPy _expand_single_argument). */
function expandSingleArgument(e: Expr): [Expr, Expr][] {
  if (isRandomSymbol(e)) return [[S.One, e]];
  if (isSum(e)) {
    const out: [Expr, Expr][] = [];
    for (const a of e.args) {
      if (isProduct(a)) out.push(mulNonrvRv(a));
      else if (isRandom(a)) out.push([S.One, a]);
    }
    return out;
  }
  if (isProduct(e)) return [mulNonrvRv(e)];
  return [[S.One, e]];
}

/** The non-random and random factors of a product (SymPy _get_mul_nonrv_rv_tuple). */
function mulNonrvRv(m: Expr): [Expr, Expr] {
  return [product(m.args.filter((a) => !isRandom(a))), product(m.args.filter((a) => isRandom(a)))];
}

/** SymPy CrossCovarianceMatrix(arg1, arg2, condition=None). */
export const CrossCovarianceMatrix = /* @__PURE__ */ callableClass(
  CrossCovarianceMatrixNode,
  (arg1: ExprLike, arg2: ExprLike, condition?: ExprLike): CrossCovarianceMatrixNode =>
    new CrossCovarianceMatrixNode(withCondition([sympify(arg1), sympify(arg2)], condition === undefined ? undefined : sympify(condition))),
);
export type CrossCovarianceMatrix = CrossCovarianceMatrixNode;

statsClasses.expectationMatrix = (e, condition) => makeExpectationMatrix(e, condition);
statsClasses.varianceMatrix = (arg, condition) => new VarianceMatrixNode(withCondition([arg], condition));
statsClasses.crossCovarianceMatrix = (a, b, condition) => new CrossCovarianceMatrixNode(withCondition([a, b], condition));
