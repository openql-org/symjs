// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_indexed_to_array.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Add, Mul, Sym, type Expr } from '../../../core/nodes';
import { Concrete } from '../../../core/concrete';
import { add } from '../../../core/ops';
import { at, first } from '../../../core/guard';
import { NotImplementedError } from '../../../core/errors';
import { MatrixElementNode } from '../../../matrices/expressions/matexpr';
import { ArrayElement, ArrayAdd, ArrayContraction, ArrayDiagonal, ArrayTensorProduct, PermuteDims, getShape, remainingAxes } from './arrayexpressions';

interface IndexedResult { expression: Expr; indices: readonly Expr[] }
function repeatedIndices(result: IndexedResult): IndexedResult {
  const groups = new Map<string, number[]>();
  result.indices.forEach((i, k) => { const group = groups.get(i.key); if (group) group.push(k); else groups.set(i.key, [k]); });
  const repeated = [...groups.values()].filter((g) => g.length > 1);
  if (!repeated.length) return result;
  return { expression: new ArrayDiagonal(result.expression, ...repeated), indices: [...remainingAxes(result.indices.length, repeated).map((i) => at(result.indices, i)), ...repeated.map((g) => at(result.indices, first(g)))] };
}
function align(result: IndexedResult, requested: readonly Expr[]): IndexedResult {
  const order = [...requested.filter((i) => result.indices.some((j) => i.key === j.key)), ...result.indices.filter((i) => !requested.some((j) => i.key === j.key))];
  const permutation = order.map((i) => result.indices.findIndex((j) => i.key === j.key));
  return { expression: permutation.every((v, i) => v === i) ? result.expression : new PermuteDims(result.expression, permutation).doit(), indices: order };
}
const hasIndexed = (expr: Expr): boolean => expr instanceof ArrayElement || expr instanceof MatrixElementNode || expr.args.some(hasIndexed);
const bareIndex = (expr: Expr, index: Expr): boolean => expr instanceof ArrayElement || expr instanceof MatrixElementNode ? false : expr.key === index.key || expr.args.some((a) => bareIndex(a, index));
function parseIndexed(expr: Expr): IndexedResult {
  if (expr instanceof ArrayElement || expr instanceof MatrixElementNode) {
    if (getShape(expr.parent).length !== expr.indices.length) throw new NotImplementedError('array conversion requires a shaped parent');
    if (expr.indices.some((i) => !(i instanceof Sym))) throw new NotImplementedError('fixed or shifted indices require array slicing');
    return { expression: expr.parent, indices: expr.indices };
  }
  if (expr instanceof Mul) {
    const parts = expr.args.map(parseIndexed);
    return { expression: new ArrayTensorProduct(...parts.map((r) => r.expression)).doit(), indices: parts.flatMap((r) => [...r.indices]) };
  }
  if (expr instanceof Add) {
    const parts = expr.args.map((a) => repeatedIndices(parseIndexed(a))), target = first(parts).indices;
    if (parts.some((r) => r.indices.length !== target.length || r.indices.some((i) => !target.some((j) => i.key === j.key)))) throw new RangeError('addends must have the same free indices');
    return { expression: new ArrayAdd(...parts.map((r) => align(r, target).expression)), indices: target };
  }
  if (expr instanceof Concrete && expr.kind2 === 'Sum') {
    if (!hasIndexed(expr.function)) return { expression: expr, indices: [] };
    if (expr.limits.some(([v]) => bareIndex(expr.function, v))) throw new NotImplementedError('index-dependent scalar weights require explicit array entries');
    let result = repeatedIndices(parseIndexed(expr.function));
    for (const [variable, lower, upper] of expr.limits) {
      const axis = result.indices.findIndex((i) => i.key === variable.key);
      if (axis < 0) throw new RangeError('summation index is not present in the array entries');
      if (lower.key !== '0' || add(upper, 1).key !== at(getShape(result.expression), axis).key) throw new NotImplementedError('array conversion requires summation over a complete axis');
      result = { expression: new ArrayContraction(result.expression, [axis]).doit(), indices: result.indices.filter((_, k) => k !== axis) };
    }
    return result;
  }
  if (hasIndexed(expr)) throw new NotImplementedError('unsupported operation on indexed array entries');
  return { expression: expr, indices: [] };
}

/** Turn explicit sums and repeated indices into contractions and diagonals. */
export function convertIndexedToArray(expr: Expr, firstIndices: readonly Expr[] = []): Expr {
  if (new Set(firstIndices.map((i) => i.key)).size !== firstIndices.length) throw new RangeError('free indices cannot be repeated');
  return align(repeatedIndices(parseIndexed(expr)), firstIndices).expression;
}
