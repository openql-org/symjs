// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_array_to_matrix.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import type { Expr } from '../../../core/nodes';
import { at, getOrThrow, first } from '../../../core/guard';
import { mul } from '../../../core/ops';
import { MatAdd, MatMulNode, MatrixExpr, Trace, Transpose } from '../../../matrices/expressions/matexpr';
import { ArrayExpr, ArraySymbol, ArrayAdd, ArrayContraction, ArrayTensorProduct, PermuteDims, factorBlocks, getRank, remainingAxes } from './arrayexpressions';

/** Recognize matrix chains and traces in pairwise tensor contractions. */
export function convertArrayToMatrix(expr: Expr): Expr {
  if (expr instanceof ArrayAdd) {
    const args = expr.args.map(convertArrayToMatrix);
    if (args.some((a) => a instanceof ArrayExpr && !(a instanceof ArraySymbol))) return new ArrayAdd(...args);
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    return MatAdd(...args).doit();
  }
  if (expr instanceof PermuteDims) {
    const inner = convertArrayToMatrix(expr.expr);
    if (inner instanceof MatrixExpr) return first(expr.permutation.arrayForm) === 0 ? inner : Transpose(inner).doit();
    return new PermuteDims(inner, expr.permutation).doit();
  }
  if (expr instanceof ArrayTensorProduct) {
    const args = expr.args.map(convertArrayToMatrix), scalars = args.filter((a) => getRank(a) === 0), arrays = args.filter((a) => getRank(a) > 0);
    if (!arrays.length) return mul(...scalars);
    if (arrays.length && scalars.length && first(arrays) instanceof MatrixExpr) arrays[0] = new MatMulNode([...scalars, first(arrays)]).doit();
    else arrays.unshift(...scalars);
    return new ArrayTensorProduct(...arrays).doit();
  }
  if (!(expr instanceof ArrayContraction)) return expr;
  const normalized = expr.doit();
  if (!(normalized instanceof ArrayContraction)) return convertArrayToMatrix(normalized);
  const product = normalized.expr instanceof ArrayTensorProduct ? normalized.expr : new ArrayTensorProduct(normalized.expr);
  const args = product.args.map(convertArrayToMatrix);
  if (args.some((a) => getRank(a) !== 0 && !(a instanceof MatrixExpr)) || normalized.contractionIndices.some((g) => g.length !== 2)) return normalized;
  const blocks = factorBlocks(product), edges = new Map<number, number>();
  for (const g of normalized.contractionIndices) { edges.set(first(g), at(g, 1)); edges.set(at(g, 1), first(g)); }
  const owner = new Map<number, number>();
  blocks.forEach((block, i) => block.forEach((axis) => owner.set(axis, i)));
  const used = new Set<number>(), scalars = args.filter((a) => getRank(a) === 0);
  const remaining = remainingAxes(getRank(product), normalized.contractionIndices);
  const matrices: Expr[] = [], outputAxes: number[] = [];
  const walk = (start: number): { value: Expr; end: number } => {
    let axis = start, end = start;
    const chain: Expr[] = [];
    for (;;) {
      const i = getOrThrow(owner, axis);
      if (used.has(i)) break;
      used.add(i);
      const block = at(blocks, i), A = at(args, i), forward = axis === first(block);
      chain.push(forward ? A : Transpose(A).doit());
      end = forward ? at(block, 1) : first(block);
      const next = edges.get(end);
      if (next === undefined) break;
      axis = next;
    }
    return { value: new MatMulNode(chain).doit(), end };
  };
  for (const axis of remaining) {
    if (used.has(getOrThrow(owner, axis))) continue;
    const result = walk(axis);
    matrices.push(result.value);
    outputAxes.push(axis, result.end);
  }
  for (const [i, arg] of args.entries()) if (arg instanceof MatrixExpr && !used.has(i)) scalars.push(Trace(walk(first(at(blocks, i))).value).doit());
  const scalar = mul(...scalars);
  if (matrices.length === 0) return scalar;
  if (matrices.length === 1) return new MatMulNode([scalar, first(matrices)]).doit();
  const result = new ArrayTensorProduct(new MatMulNode([scalar, first(matrices)]).doit(), ...matrices.slice(1));
  const permutation = remaining.map((axis) => outputAxes.indexOf(axis));
  return permutation.every((axis, i) => axis === i) ? result : new PermuteDims(result, permutation);
}
