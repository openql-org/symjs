// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_matrix_to_array.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { first } from '../../../core/guard';
import type { Expr } from '../../../core/nodes';
import { MatAddNode, MatMulNode, MatPowNode, ElementwiseApplyFunctionNode, TraceNode, TransposeNode } from '../../../matrices/expressions/matexpr';
import { HadamardProductNode, HadamardPowerNode } from '../../../matrices/expressions/hadamard';
import { Rational } from '../../../core/nodes';
import { ArrayAdd, ArrayContraction, ArrayTensorProduct, ArrayDiagonal, ArrayElementwiseApplyFunc, PermuteDims, getRank } from './arrayexpressions';

/** Express matrix operations as tensor products, axis permutations and contractions. */
export function convertMatrixToArray(expr: Expr): Expr {
  if (expr instanceof ElementwiseApplyFunctionNode) return new ArrayElementwiseApplyFunc(expr.function, convertMatrixToArray(expr.expr));
  if (expr instanceof HadamardPowerNode) return new ArrayElementwiseApplyFunc((x) => x.pow(expr.exp), convertMatrixToArray(expr.base));
  if (expr instanceof HadamardProductNode) {
    if (expr.args.length === 1) return convertMatrixToArray(first(expr.args));
    return new ArrayDiagonal(new ArrayTensorProduct(...expr.args.map(convertMatrixToArray)), expr.args.map((_, i) => 2 * i), expr.args.map((_, i) => 2 * i + 1));
  }
  if (expr instanceof MatAddNode) return new ArrayAdd(...expr.args.map(convertMatrixToArray));
  if (expr instanceof TransposeNode) return new PermuteDims(convertMatrixToArray(expr.arg), [1, 0]).doit();
  if (expr instanceof TraceNode) return new ArrayContraction(convertMatrixToArray(expr.arg), [0, 1]).doit();
  if (expr instanceof MatPowNode && expr.exp instanceof Rational && expr.exp.isInteger && expr.exp.p > 0n) {
    return convertMatrixToArray(MatMulNode.create(Array.from({ length: Number(expr.exp.p) }, () => expr.base)));
  }
  if (!(expr instanceof MatMulNode)) return expr;
  const args = expr.args.map(convertMatrixToArray), groups: number[][] = [];
  let offset = 0, previous = -1;
  for (const arg of args) {
    const rank = getRank(arg);
    if (rank === 2) {
      if (previous >= 0) groups.push([previous, offset]);
      previous = offset + 1;
    }
    offset += rank;
  }
  const product = new ArrayTensorProduct(...args).doit();
  return groups.length ? new ArrayContraction(product, ...groups).doit() : product;
}
