// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.tensor.array (N-dimensional arrays, array comprehensions
 * and array operations) and sympy.tensor.indexed.Idx.
 *
 * The classes can be called like SymPy's constructors
 * (`ImmutableDenseNDimArray([[1, 2], [3, 4]])`, `Array(range, [3, 4])`) or
 * used with `new`, and `instanceof` works with them.
 */

import { callableClass } from '../core/callable';
import type { Expr } from '../core/nodes';
import type { ComprehensionLambda, ComprehensionLimit } from './comprehension';
import { ArrayComprehensionMapNode, ArrayComprehensionNode } from './comprehension';
import type { IdxRange } from './idx';
import { IdxNode, makeIdx } from './idx';
import type { Kind } from '../core/kind';
import { ArrayKindNode, NumberKind } from '../core/kind';
import type { ArrayInput, ShapeInput } from './ndimarray';
import {
  DenseNDimArray as DenseNDimArrayNode,
  ImmutableDenseNDimArray as ImmutableDenseNDimArrayNode,
  ImmutableSparseNDimArray as ImmutableSparseNDimArrayNode,
  MutableDenseNDimArray as MutableDenseNDimArrayNode,
  MutableSparseNDimArray as MutableSparseNDimArrayNode,
  NDimArray as NDimArrayNode,
  SparseNDimArray as SparseNDimArrayNode,
} from './ndimarray';

export type {
  ArrayElementInput,
  ArrayInput,
  IndexItem,
  NestedArrayInput,
  NestedList,
  ShapeInput,
  SparseArrayInput,
} from './ndimarray';
export { Flatten, Slice, deriveByArray, kindOf, slice } from './ndimarray';
export type { PermutationLike, PermutedimsOptions, TensorArg } from './arrayop';
export { permutedims, tensorcontraction, tensordiagonal, tensorproduct } from './arrayop';
export type { ComprehensionLambda, ComprehensionLimit } from './comprehension';
export type { IdxRange } from './idx';
export { BooleanKind, Kind, NumberKind, UndefinedKind } from '../core/kind';

/**
 * SymPy NDimArray: the base class of N-dimensional arrays; calling it
 * builds an ImmutableDenseNDimArray.
 */
export const NDimArray = /* @__PURE__ */ callableClass(
  NDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableDenseNDimArrayNode => new ImmutableDenseNDimArrayNode(iterable, shape),
);
export type NDimArray = NDimArrayNode;

/** SymPy DenseNDimArray: dense arrays; calling it builds an ImmutableDenseNDimArray. */
export const DenseNDimArray = /* @__PURE__ */ callableClass(
  DenseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableDenseNDimArrayNode => new ImmutableDenseNDimArrayNode(iterable, shape),
);
export type DenseNDimArray = DenseNDimArrayNode;

/** SymPy SparseNDimArray: sparse arrays; calling it builds an ImmutableSparseNDimArray. */
export const SparseNDimArray = /* @__PURE__ */ callableClass(
  SparseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableSparseNDimArrayNode => new ImmutableSparseNDimArrayNode(iterable, shape),
);
export type SparseNDimArray = SparseNDimArrayNode;

/**
 * SymPy ImmutableDenseNDimArray(iterable, shape): an immutable dense array
 * from nested lists, a flat list and a shape, a Matrix or another array.
 *
 * @example
 * ImmutableDenseNDimArray([0, 1, 2, 3, 4, 5], [2, 3]).toString() // '[[0, 1, 2], [3, 4, 5]]'
 */
export const ImmutableDenseNDimArray = /* @__PURE__ */ callableClass(
  ImmutableDenseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableDenseNDimArrayNode => new ImmutableDenseNDimArrayNode(iterable, shape),
);
export type ImmutableDenseNDimArray = ImmutableDenseNDimArrayNode;

/** SymPy MutableDenseNDimArray(iterable, shape): a dense array changed in place with `set`. */
export const MutableDenseNDimArray = /* @__PURE__ */ callableClass(
  MutableDenseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): MutableDenseNDimArrayNode => new MutableDenseNDimArrayNode(iterable, shape),
);
export type MutableDenseNDimArray = MutableDenseNDimArrayNode;

/** SymPy ImmutableSparseNDimArray(iterable, shape): an immutable array storing its nonzero elements. */
export const ImmutableSparseNDimArray = /* @__PURE__ */ callableClass(
  ImmutableSparseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableSparseNDimArrayNode => new ImmutableSparseNDimArrayNode(iterable, shape),
);
export type ImmutableSparseNDimArray = ImmutableSparseNDimArrayNode;

/** SymPy MutableSparseNDimArray(iterable, shape): a sparse array changed in place with `set`. */
export const MutableSparseNDimArray = /* @__PURE__ */ callableClass(
  MutableSparseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): MutableSparseNDimArrayNode => new MutableSparseNDimArrayNode(iterable, shape),
);
export type MutableSparseNDimArray = MutableSparseNDimArrayNode;

/**
 * SymPy Array: ImmutableDenseNDimArray. Exported as `Array`, which shadows
 * JavaScript's Array where it is imported under that name.
 */
export { ImmutableDenseNDimArray as Array };

/**
 * SymPy ArrayComprehension(function, *limits): the array of `function`
 * over the index ranges [variable, lower, upper], evaluated by `doit()`.
 */
export const ArrayComprehension = /* @__PURE__ */ callableClass(
  ArrayComprehensionNode,
  (fn: Expr | number | bigint, ...limits: ComprehensionLimit[]): ArrayComprehensionNode => new ArrayComprehensionNode(fn, ...limits),
);
export type ArrayComprehension = ArrayComprehensionNode;

/** SymPy ArrayComprehensionMap(lambda, *limits): ArrayComprehension with a JavaScript function. */
export const ArrayComprehensionMap = /* @__PURE__ */ callableClass(
  ArrayComprehensionMapNode,
  (fn: ComprehensionLambda, ...limits: ComprehensionLimit[]): ArrayComprehensionMapNode => new ArrayComprehensionMapNode(fn, ...limits),
);
export type ArrayComprehensionMap = ArrayComprehensionMapNode;

/** SymPy ArrayKind(element_kind): the kind of arrays (cached, ArrayKind(NumberKind) by default). */
export const ArrayKind = /* @__PURE__ */ callableClass(ArrayKindNode, (elementKind: Kind = NumberKind): ArrayKindNode => ArrayKindNode.of(elementKind));
export type ArrayKind = ArrayKindNode;

/**
 * SymPy Idx(label, range): an integer index with an optional range (a
 * dimension n, or [lower, upper]); an integer label gives the integer.
 */
export const Idx = /* @__PURE__ */ callableClass(IdxNode, (label: string | Expr | number | bigint, range?: IdxRange): Expr => makeIdx(label, range));
export type Idx = IdxNode;
export { IndexConformanceException, getContractionStructure, getIndices } from './indexmethods';
export type { ContractionKey, ContractionStructure } from './indexmethods';
