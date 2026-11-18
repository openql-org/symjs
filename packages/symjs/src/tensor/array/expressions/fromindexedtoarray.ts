// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (tensor/array/expressions/from_indexed_to_array.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).
import { Add, Fn, Mul, Rational, Sym, type Expr } from '../../../core/nodes';
import { ArrayComprehensionNode } from '../../comprehension';
import { TupleNode } from '../../../core/containers';
import { Indexed, IndexedBase } from '../../../core/indexed';
import { Concrete } from '../../../core/concrete';
import { rebuild } from '../../../core/traverse';
import { add } from '../../../core/ops';
import { at, first } from '../../../core/guard';
import { NotImplementedError } from '../../../core/errors';
import { MatrixElementNode } from '../../../matrices/expressions/matexpr';
import { ArrayElement, ArrayElementwiseApplyFunc, ArrayAdd, ArrayContraction, ArrayDiagonal, ArrayTensorProduct, OneArray, PermuteDims, getShape, remainingAxes } from './arrayexpressions';

interface IndexedResult { expression: Expr; indices: readonly Expr[] }
type IndexRange = readonly [Expr, Expr, Expr];
function inferRanges(expr: Expr, ranges: Map<string, IndexRange>): void {
  if (expr instanceof ArrayElement || expr instanceof MatrixElementNode) {
    const shape = getShape(expr.parent);
    expr.indices.forEach((i, k) => { if (i instanceof Sym && k < shape.length) ranges.set(i.key, [i, Rational.of(0), add(at(shape, k), -1)]); });
    return;
  }
  expr.args.forEach((arg) => inferRanges(arg, ranges));
}
function repeatedIndices(result: IndexedResult): IndexedResult {
  const groups = new Map<string, number[]>();
  result.indices.forEach((i, k) => { if (i instanceof Rational) return; const group = groups.get(i.key); if (group) group.push(k); else groups.set(i.key, [k]); });
  const repeated = [...groups.values()].filter((g) => g.length > 1);
  if (!repeated.length) return result;
  return { expression: new ArrayDiagonal(result.expression, ...repeated), indices: [...remainingAxes(result.indices.length, repeated).map((i) => at(result.indices, i)), ...repeated.map((g) => at(result.indices, first(g)))] };
}
function align(result: IndexedResult, requested: readonly Expr[]): IndexedResult {
  const order = [...requested.filter((i) => result.indices.some((j) => i.key === j.key)), ...result.indices.filter((i) => !requested.some((j) => i.key === j.key))];
  const permutation = order.map((i) => result.indices.findIndex((j) => i.key === j.key));
  return { expression: permutation.every((v, i) => v === i) ? result.expression : new PermuteDims(result.expression, permutation).doit(), indices: order };
}
const hasIndexed = (expr: Expr): boolean => expr instanceof Indexed || expr instanceof ArrayElement || expr instanceof MatrixElementNode || expr.args.some(hasIndexed);
const hasShiftedIndices = (expr: Expr): boolean => expr instanceof Indexed || expr instanceof ArrayElement || expr instanceof MatrixElementNode
  ? expr.indices.some((i) => !(i instanceof Sym || i instanceof Rational && i.isInteger))
  : expr.args.some(hasShiftedIndices);
function parseIndexed(expr: Expr, ranges: readonly IndexRange[] = []): IndexedResult {
  if (!hasIndexed(expr)) {
    const dependent = ranges.filter(([v]) => expr.has(v));
    return dependent.length ? { expression: new ArrayComprehensionNode(expr, ...dependent).doit(), indices: dependent.map(([v]) => v) } : { expression: expr, indices: [] };
  }
  if (expr instanceof Indexed && expr.base instanceof IndexedBase) {
    if (!ranges.length || getShape(expr.base).length) return { expression: expr.base, indices: expr.indices };
    const shape = expr.indices.map((i) => {
      const range = ranges.find(([v]) => v.key === i.key);
      if (!range || !range[1].equals(0)) throw new NotImplementedError('array conversion requires a complete zero-based index range');
      return add(range[2], 1);
    });
    return { expression: expr.base.withArgs([expr.base.label, new TupleNode(shape)]), indices: expr.indices };
  }
  if (expr instanceof ArrayElement || expr instanceof MatrixElementNode) {
    if (getShape(expr.parent).length !== expr.indices.length) throw new NotImplementedError('array conversion requires a shaped parent');
    return { expression: expr.parent, indices: expr.indices };
  }
  if (expr instanceof Mul) {
    const parts = expr.args.map((a) => parseIndexed(a, ranges));
    return { expression: new ArrayTensorProduct(...parts.map((r) => r.expression)).doit(), indices: parts.flatMap((r) => [...r.indices]) };
  }
  if (expr instanceof Add) {
    const parts = expr.args.map((a) => repeatedIndices(parseIndexed(a, ranges)));
    const target: Expr[] = [], shape: Expr[] = [];
    for (const part of parts) for (const [axis, index] of part.indices.entries()) {
      if (!target.some((other) => other.key === index.key)) {
        target.push(index);
        shape.push(at(getShape(part.expression), axis));
      }
    }
    const args = parts.map((part) => {
      const missing = target.filter((index) => !part.indices.some((other) => other.key === index.key));
      const padded = missing.length ? {
        expression: new ArrayTensorProduct(new OneArray(...missing.map((index) => at(shape, target.indexOf(index)))), part.expression).doit(),
        indices: [...missing, ...part.indices],
      } : part;
      return align(padded, target).expression;
    });
    return { expression: new ArrayAdd(...args), indices: target };
  }
  if (expr instanceof Concrete && expr.kind2 === 'Sum') {
    const local = new Map(ranges.map((range) => [first(range).key, range]));
    for (const limit of expr.limits) local.set(first(limit).key, limit);
    let result = repeatedIndices(parseIndexed(expr.function, [...local.values()]));
    for (const [variable, lower, upper] of expr.limits) {
      const axis = result.indices.findIndex((i) => i.key === variable.key);
      if (axis < 0) throw new RangeError('summation index is not present in the array entries');
      if (lower.key !== '0' || add(upper, 1).key !== at(getShape(result.expression), axis).key) throw new NotImplementedError('array conversion requires summation over a complete axis');
      result = { expression: new ArrayContraction(result.expression, [axis]).doit(), indices: result.indices.filter((_, k) => k !== axis) };
    }
    return result;
  }
  if (expr instanceof Fn && expr.args.length === 1) {
    const inner = parseIndexed(first(expr.args), ranges);
    return { expression: new ArrayElementwiseApplyFunc((x) => rebuild(expr, [x]), inner.expression), indices: inner.indices };
  }
  throw new NotImplementedError('unsupported operation on indexed array entries');
}

/** Turn explicit sums and repeated indices into contractions and diagonals. */
export function convertIndexedToArray(expr: Expr, firstIndices: readonly Expr[] = []): Expr {
  if (new Set(firstIndices.map((i) => i.key)).size !== firstIndices.length) throw new RangeError('free indices cannot be repeated');
  if (hasShiftedIndices(expr)) return expr;
  const ranges = new Map<string, IndexRange>();
  inferRanges(expr, ranges);
  const result = repeatedIndices(parseIndexed(expr, [...ranges.values()]));
  if (result.indices.some((i) => i instanceof Rational)) return new ArrayElement(result.expression, result.indices);
  return align(result, firstIndices).expression;
}
