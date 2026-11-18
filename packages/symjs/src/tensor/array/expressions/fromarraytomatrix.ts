// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_array_to_matrix.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Mul, Pow, S, type Expr } from '../../../core/nodes';
import { at, getOrThrow, first } from '../../../core/guard';
import { HadamardPower, hadamardProduct } from '../../../matrices/expressions/hadamard';
import { mul } from '../../../core/ops';
import { ElementwiseApplyFunction, MatAdd, MatMulNode, MatrixElementNode, MatrixExpr, Trace, Transpose, ZeroMatrix } from '../../../matrices/expressions/matexpr';
import { ArrayExpr, ArraySymbol, ArrayAdd, ArrayContraction, ArrayDiagonal, ArrayElement, ArrayElementwiseApplyFunc, ArrayTensorProduct, PermuteDims, ZeroArray, factorBlocks, getRank, remainingAxes } from './arrayexpressions';

/** Recognize matrix chains and traces in pairwise tensor contractions. */
export function convertArrayToMatrix(expr: Expr): Expr {
  if (expr instanceof ZeroArray && expr.shape.length === 2) return ZeroMatrix(first(expr.shape), at(expr.shape, 1));
  if (expr instanceof ArrayElement) {
    const parent = convertArrayToMatrix(expr.parent);
    return parent instanceof MatrixExpr ? new MatrixElementNode(parent, first(expr.indices), at(expr.indices, 1)) : new ArrayElement(parent, expr.indices);
  }
  if (expr instanceof ArrayElementwiseApplyFunc) {
    const inner = convertArrayToMatrix(expr.expr);
    if (!(inner instanceof MatrixExpr)) return new ArrayElementwiseApplyFunc(expr.function, inner);
    if (inner.rows.key !== '1' || inner.cols.key !== '1') {
      const variable = first(expr.function.variables), body = expr.function.expr;
      const factors = body instanceof Mul ? body.args : [body];
      const dependent = factors.filter((factor) => factor.has(variable));
      let exponent: Expr | undefined;
      if (dependent.length === 0) exponent = S.Zero;
      else if (dependent.length === 1) {
        const power = first(dependent);
        if (power.key === variable.key) exponent = S.One;
        else if (power instanceof Pow && power.base.key === variable.key && !power.exp.has(variable)) exponent = power.exp;
      }
      if (exponent !== undefined) return new MatMulNode([mul(...factors.filter((factor) => !factor.has(variable))), HadamardPower(inner, exponent)]).doit();
    }
    return ElementwiseApplyFunction(expr.function, inner);
  }
  if (expr instanceof ArrayDiagonal && expr.expr instanceof ArrayTensorProduct && expr.diagonalIndices.length === 2 && expr.shape.length === 2) {
    const product = expr.expr, groups = expr.diagonalIndices;
    const blocks = factorBlocks(product);
    if (product.args.every((a) => a instanceof MatrixExpr) && blocks.every((block) => groups.every((g) => block.filter((axis) => g.includes(axis)).length === 1))) {
      return hadamardProduct(...product.args.map((arg, i) => at(groups, 0).includes(first(at(blocks, i))) ? arg : Transpose(arg).doit()));
    }
  }
  if (expr instanceof ArrayAdd) {
    const args = expr.args.map(convertArrayToMatrix);
    if (args.some((a) => a instanceof ArrayExpr && !(a instanceof ArraySymbol))) return new ArrayAdd(...args);
    if (!args.every((a) => a instanceof MatrixExpr)) throw new TypeError('Mix of Matrix and Scalar symbols');
    return MatAdd(...args).doit();
  }
  if (expr instanceof PermuteDims) {
    const inner = convertArrayToMatrix(expr.expr);
    if (inner instanceof MatrixExpr) return first(expr.permutation.arrayForm) === 0 ? inner : Transpose(inner).doit();
    if (inner instanceof ArrayTensorProduct) {
      const p = expr.permutation.arrayForm, axes: number[] = [];
      const blocks = factorBlocks(inner);
      const args = inner.args.map((arg, i) => {
        const block = at(blocks, i);
        if (arg instanceof MatrixExpr && p.indexOf(first(block)) > p.indexOf(at(block, 1))) {
          axes.push(...[...block].reverse());
          return Transpose(arg).doit();
        }
        axes.push(...block);
        return arg;
      });
      return new PermuteDims(new ArrayTensorProduct(...args), p.map((axis) => axes.indexOf(axis))).doit();
    }
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
