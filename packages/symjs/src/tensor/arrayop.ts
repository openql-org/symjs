// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Operations on N-dimensional arrays (sympy.tensor.array.arrayop):
 * tensorproduct, tensorcontraction, tensordiagonal and permutedims.
 */

import { at } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { S } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { Matrix } from '../matrices/matrix';
import type { ArrayInput, NestedArrayInput } from './ndimarray';
import { ImmutableDenseNDimArray, ImmutableSparseNDimArray, NDimArray, SparseNDimArray, permuteArray } from './ndimarray';

/** An argument of the array operations: an array, a Matrix, nested lists or (for tensorproduct) a scalar. */
export type TensorArg = NDimArray | Matrix | readonly NestedArrayInput[] | ExprLike;

/** SymPy _arrayfy: arrays stay, matrices and lists become ImmutableDenseNDimArray, scalars are sympified. */
const isNestedList = (a: TensorArg): a is readonly NestedArrayInput[] => Array.isArray(a);

function arrayfy(a: TensorArg): NDimArray | Expr {
  if (a instanceof NDimArray) return a;
  if (a instanceof Matrix || isNestedList(a)) return new ImmutableDenseNDimArray(a);
  return sympify(a);
}

function toArray(a: TensorArg): NDimArray {
  const r = arrayfy(a);
  if (!(r instanceof NDimArray)) throw new TypeError('an array is required');
  return r;
}

const newOfClass = (a: NDimArray, it: ArrayInput, shape: readonly number[]): NDimArray =>
  a.newLike(it, shape);

/**
 * SymPy tensorproduct(*args): the tensor (outer) product of arrays,
 * matrices and scalars. With no argument it is 1, with scalars only their
 * product.
 *
 * @example
 * tensorproduct(Array([[1, 2], [3, 4]]), Array([x, y]))
 * // [[[x, y], [2*x, 2*y]], [[3*x, 3*y], [4*x, 4*y]]]
 */
export function tensorproduct(...args: TensorArg[]): Expr {
  if (args.length === 0) return S.One;
  if (args.length === 1) return arrayfy(at(args, 0));
  if (args.length > 2) return tensorproduct(tensorproduct(at(args, 0), at(args, 1)), ...args.slice(2));
  const a = arrayfy(at(args, 0));
  const b = arrayfy(at(args, 1));
  if (!(a instanceof NDimArray) || !(b instanceof NDimArray)) {
    if (a instanceof NDimArray) return a.mul(b);
    if (b instanceof NDimArray) return b.rmul(a);
    return mul(a, b);
  }
  const shape = [...a.shape, ...b.shape];
  if (a instanceof SparseNDimArray && b instanceof SparseNDimArray) {
    const lp = b.length;
    const m = new Map<number, Expr>();
    for (const [k1, v1] of a.sparseArray) for (const [k2, v2] of b.sparseArray) m.set(k1 * lp + k2, mul(v1, v2));
    return new ImmutableSparseNDimArray(m, shape);
  }
  const bs = b.flatElements();
  return new ImmutableDenseNDimArray(
    a.flatElements().flatMap((i) => bs.map((j) => mul(i, j))),
    shape,
  );
}

/** SymPy _util_contraction_diagonal: checks the axes and computes the flat offsets. */
function contractionData(array: NDimArray, groups: readonly (readonly number[])[]): { remaining: number[][]; remainingShape: number[]; deltas: number[][] } {
  const taken = new Set<number>();
  for (const g of groups) {
    if (!Array.isArray(g)) throw new RangeError('collections of contraction/diagonal axes expected');
    const dim = array.shape[at(g, 0)];
    for (const d of g) {
      if (taken.has(d)) throw new RangeError('dimension specified more than once');
      if (dim !== array.shape[d]) throw new RangeError('cannot contract or diagonalize between axes of different dimension');
      taken.add(d);
    }
  }
  const rank = array.rank();
  const cum: number[] = Array.from({ length: rank }, () => 0);
  let c = 1;
  for (let i = rank - 1; i >= 0; i--) {
    cum[i] = c;
    c *= at(array.shape, i);
  }
  const keep = [...Array(rank).keys()].filter((i) => !taken.has(i));
  return {
    remaining: keep.map((i) => Array.from({ length: at(array.shape, i) }, (_, j) => at(cum, i) * j)),
    remainingShape: keep.map((i) => at(array.shape, i)),
    deltas: groups.map((g) => Array.from({ length: at(array.shape, at(g, 0)) }, (_, js) => g.reduce((s, ig) => s + at(cum, ig) * js, 0))),
  };
}

/** Sums of one element of each list, in itertools.product order. */
function productSums(lists: readonly (readonly number[])[]): number[] {
  let out = [0];
  for (const l of lists) out = out.flatMap((s) => l.map((v) => s + v));
  return out;
}

/**
 * SymPy tensorcontraction(array, *axes): the sum over equal indices of
 * each group of axes. Contracting every axis gives a scalar.
 *
 * @example
 * tensorcontraction(Array([[x, y], [z, t]]), [0, 1]) // t + x
 */
export function tensorcontraction(arrayIn: TensorArg, ...axes: (readonly number[])[]): Expr {
  const array = toArray(arrayIn);
  const { remaining, remainingShape, deltas } = contractionData(array, axes);
  const flat = array.flatElements();
  const offsets = productSums(deltas);
  const out = productSums(remaining).map((base) => add(...offsets.map((o) => at(flat, base + o))));
  if (remaining.length === 0) return at(out, 0);
  return newOfClass(array, out, remainingShape);
}

/**
 * SymPy tensordiagonal(array, *axes): the diagonal over each group of
 * axes, which become the last axes of the result.
 *
 * @example
 * tensordiagonal(Matrix.of([[a, b], [c, d]]), [0, 1]) // [a, d]
 */
export function tensordiagonal(arrayIn: TensorArg, ...axes: (readonly number[])[]): Expr {
  if (axes.some((g) => g.length <= 1)) throw new RangeError('need at least two axes to diagonalize');
  if (axes.length === 0) throw new TypeError('tensordiagonal: no axes to diagonalize');
  const array = toArray(arrayIn);
  // SymPy ArrayDiagonal._validate
  for (const g of axes) {
    if (g.some((j) => j >= array.rank())) throw new RangeError('index is larger than expression shape');
    if (new Set(g.map((j) => array.shape[j])).size !== 1) throw new RangeError('diagonalizing indices of different dimensions');
    if (new Set(g).size !== g.length) throw new RangeError('axis index cannot be repeated');
  }
  const { remaining, remainingShape, deltas } = contractionData(array, axes);
  const flat = array.flatElements();
  const offsets = productSums(deltas);
  const out = productSums(remaining).flatMap((base) => offsets.map((o) => at(flat, base + o)));
  return newOfClass(array, out, [...remainingShape, ...deltas.map((d) => d.length)]);
}

/** A permutation given as a list of positions or as a Permutation (anything with an `arrayForm`). */
export type PermutationLike = readonly number[] | { readonly arrayForm: readonly number[] };

/** Options of permutedims: the axes named before and after (SymPy index_order_old, index_order_new). */
export interface PermutedimsOptions {
  /** Names of the axes in the given order (a string of one-letter names or a list). */
  indexOrderOld?: string | readonly unknown[];
  /** Names of the axes in the new order. */
  indexOrderNew?: string | readonly unknown[];
}

/**
 * SymPy permutedims(expr, perm): the axes reordered so that axis i of the
 * result is axis perm[i] of `expr` (for rank 2, the transpose). The
 * permutation can also be given by naming the axes,
 * `permutedims(b, { indexOrderOld: 'cba', indexOrderNew: 'abc' })`.
 */
export function permutedims(expr: TensorArg, perm?: PermutationLike | PermutedimsOptions, opts: PermutedimsOptions = {}): NDimArray {
  const array = toArray(expr);
  let p: readonly number[];
  if (perm === undefined) p = permutationFromIndexOrders(opts, array.rank());
  else if (isPermutationLike(perm)) {
    if (opts.indexOrderNew !== undefined) throw new RangeError('index_order_new cannot be defined with permutation');
    if (opts.indexOrderOld !== undefined) throw new RangeError('index_order_old cannot be defined with permutation');
    p = isIndexArray(perm) ? perm : perm.arrayForm;
  } else p = permutationFromIndexOrders(perm, array.rank());
  return permuteArray(array, p);
}

const isIndexArray = (p: PermutationLike | PermutedimsOptions): p is readonly number[] => Array.isArray(p);
const isPermutationLike = (p: PermutationLike | PermutedimsOptions): p is PermutationLike => isIndexArray(p) || 'arrayForm' in p;

/** SymPy PermuteDims._get_permutation_from_index_orders. */
function permutationFromIndexOrders(opts: PermutedimsOptions, dim: number): number[] {
  const { indexOrderOld, indexOrderNew } = opts;
  if (indexOrderOld === undefined || indexOrderNew === undefined) throw new RangeError('Permutation not defined');
  const names = (o: string | readonly unknown[]): unknown[] => (typeof o === 'string' ? o.split('') : [...o]);
  const oldL = names(indexOrderOld);
  const newL = names(indexOrderNew);
  if (new Set(newL).size !== dim) throw new RangeError('wrong number of indices in index_order_new');
  if (new Set(oldL).size !== dim) throw new RangeError('wrong number of indices in index_order_old');
  if (newL.some((i) => !oldL.includes(i))) throw new RangeError('index_order_new and index_order_old must have the same indices');
  return newL.map((i) => oldL.indexOf(i));
}
