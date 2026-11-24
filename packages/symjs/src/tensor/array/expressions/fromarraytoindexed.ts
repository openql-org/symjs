// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_array_to_indexed.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Dummy, S, type Expr, type ExprLike } from '../../../core/nodes';
import { at, first } from '../../../core/guard';
import { add, mul, sub, sympify } from '../../../core/ops';
import { Sum } from '../../../core/concrete';
import { fn } from '../../../functions/elementary/elementary';
import { Mod } from '../../../functions/mod';
import { ImmutableMatrixNode, MatrixExpr } from '../../../matrices/expressions/matexpr';
import { Matrix } from '../../../matrices/matrix';
import { NDimArray } from '../../ndimarray';
import { ArrayExpr, ArrayElement, ArrayTensorProduct, ArrayContraction, ArrayDiagonal, ArrayAdd, ArrayElementwiseApplyFunc, OneArray, ZeroArray, PermuteDims, Reshape, getShape, getRank, remainingAxes } from './arrayexpressions';
import { applyPermutationToList } from './utils';

/**
 * Convert array operations to scalar entries and explicit, capture-free sums.
 *
 * @param expression - Expression to transform.
 * @param indices - Indices in slot order.
 * @returns The indexed entry, including explicit sums for contracted axes.
 * @throws RangeError when the number of indices does not match the rank.
 * @see SymPy `sympy.tensor.array.expressions.from_array_to_indexed.convert_array_to_indexed`
 */
export function convertArrayToIndexed(expression: ExprLike | Matrix, indices: readonly ExprLike[]): Expr {
  let dummyCount = 0;
  function convert(expr: Expr, ind: readonly Expr[]): Expr {
    const rank = getRank(expr);
    if ((rank > 0 || expr instanceof ArrayExpr || expr instanceof NDimArray) && ind.length !== rank) throw new RangeError('array index rank does not match the shape');
    if (expr instanceof ArrayTensorProduct) {
      let offset = 0;
      return mul(...expr.args.map((arg) => {
        const start = offset;
        offset += getRank(arg);
        return convert(arg, ind.slice(start, offset));
      }));
    }
    if (expr instanceof ArrayContraction) {
      const assigned = new Map<number, Expr>(), limits: [Dummy, Expr, Expr][] = [];
      for (const group of expr.contractionIndices) {
        const dummy = new Dummy(`d${dummyCount++}`);
        limits.push([dummy, S.Zero, sub(at(getShape(expr.expr), first(group)), 1)]);
        for (const axis of group) assigned.set(axis, dummy);
      }
      let free = 0;
      const next = getShape(expr.expr).map((_, axis) => assigned.get(axis) ?? at(ind, free++));
      const result = convert(expr.expr, next);
      return limits.length ? Sum(result, ...limits) : result;
    }
    if (expr instanceof ArrayDiagonal) {
      const groups = [...remainingAxes(getRank(expr.expr), expr.diagonalIndices).map((i) => [i]), ...expr.diagonalIndices];
      const next = getShape(expr.expr).map((_, axis) => at(ind, groups.findIndex((g) => g.includes(axis))));
      return convert(expr.expr, next);
    }
    if (expr instanceof PermuteDims) return convert(expr.expr, applyPermutationToList(expr.permutation, ind));
    if (expr instanceof ArrayAdd) return add(...expr.args.map((arg) => convert(arg, ind)));
    if (expr instanceof ArrayElementwiseApplyFunc) return expr.function.call(convert(expr.expr, ind));
    if (expr instanceof Reshape) {
      let stride: Expr = S.One, linear: Expr = S.Zero;
      for (let i = ind.length - 1; i >= 0; i--) {
        linear = add(linear, mul(at(ind, i), stride));
        stride = mul(stride, at(expr.shape, i));
      }
      const shape = getShape(expr.expr), next: Expr[] = [];
      stride = S.One;
      for (let i = shape.length - 1; i >= 0; i--) {
        const quotient = stride.key === S.One.key ? linear : fn('floor', [linear.div(stride)]);
        next.unshift(i === 0 ? quotient : Mod(quotient, at(shape, i)));
        stride = mul(stride, at(shape, i));
      }
      return convert(expr.expr, next);
    }
    if (expr instanceof ZeroArray) return S.Zero;
    if (expr instanceof OneArray) return S.One;
    if (expr instanceof ArrayExpr) return expr.at(...ind);
    if (expr instanceof MatrixExpr) return expr.at(...matrixIndices(ind));
    if (expr instanceof NDimArray) return expr.get(...ind);
    // A rank-zero coefficient is a scalar. SymPy wraps it as 2[] in a tensor
    // product, which is not scalar multiplication and prevents evaluation.
    return ind.length ? new ArrayElement(expr, ind) : expr;
  }
  return convert(expression instanceof Matrix ? new ImmutableMatrixNode(expression) : sympify(expression), indices.map(sympify));
}

function matrixIndices(indices: readonly Expr[]): [Expr, Expr] {
  return [at(indices, 0), at(indices, 1)];
}
