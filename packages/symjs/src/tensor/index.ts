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
 * The base class of N-dimensional arrays; calling it builds an ImmutableDenseNDimArray.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.ndim_array.NDimArray`
 * @example
 * ```ts
 * import { NDimArray } from '@symjs/symjs';
 *
 * NDimArray([1, 2, 3, 4, 5, 6], [2, 3]); // => [[1, 2, 3], [4, 5, 6]]
 * ```
 */
export const NDimArray = /* @__PURE__ */ callableClass(
  NDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableDenseNDimArrayNode => new ImmutableDenseNDimArrayNode(iterable, shape),
);
export type NDimArray = NDimArrayNode;

/**
 * Dense arrays; calling it builds an ImmutableDenseNDimArray.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.dense_ndim_array.DenseNDimArray`
 * @example
 * ```ts
 * import { DenseNDimArray } from '@symjs/symjs';
 *
 * DenseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]); // => [[1, 2, 3], [4, 5, 6]]
 * ```
 */
export const DenseNDimArray = /* @__PURE__ */ callableClass(
  DenseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableDenseNDimArrayNode => new ImmutableDenseNDimArrayNode(iterable, shape),
);
export type DenseNDimArray = DenseNDimArrayNode;

/**
 * Sparse arrays; calling it builds an ImmutableSparseNDimArray.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.sparse_ndim_array.SparseNDimArray`
 * @example
 * ```ts
 * import { SparseNDimArray } from '@symjs/symjs';
 *
 * SparseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]); // => [[1, 2, 3], [4, 5, 6]]
 * ```
 */
export const SparseNDimArray = /* @__PURE__ */ callableClass(
  SparseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableSparseNDimArrayNode => new ImmutableSparseNDimArrayNode(iterable, shape),
);
export type SparseNDimArray = SparseNDimArrayNode;

/**
 * An immutable dense array from nested lists, a flat list and a shape, a Matrix or another array.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray`
 * @example
 * ```ts
 * import { ImmutableDenseNDimArray } from '@symjs/symjs';
 *
 * ImmutableDenseNDimArray([0, 1, 2, 3, 4, 5], [2, 3]).toString(); // => [[0, 1, 2], [3, 4, 5]]
 * ```
 */
export const ImmutableDenseNDimArray = /* @__PURE__ */ callableClass(
  ImmutableDenseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableDenseNDimArrayNode => new ImmutableDenseNDimArrayNode(iterable, shape),
);
export type ImmutableDenseNDimArray = ImmutableDenseNDimArrayNode;

/**
 * A dense array changed in place with `set`.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.dense_ndim_array.MutableDenseNDimArray`
 * @example
 * ```ts
 * import { MutableDenseNDimArray } from '@symjs/symjs';
 *
 * MutableDenseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]); // => [[1, 2, 3], [4, 5, 6]]
 * ```
 */
export const MutableDenseNDimArray = /* @__PURE__ */ callableClass(
  MutableDenseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): MutableDenseNDimArrayNode => new MutableDenseNDimArrayNode(iterable, shape),
);
export type MutableDenseNDimArray = MutableDenseNDimArrayNode;

/**
 * An immutable array storing its nonzero elements.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.sparse_ndim_array.ImmutableSparseNDimArray`
 * @example
 * ```ts
 * import { ImmutableSparseNDimArray } from '@symjs/symjs';
 *
 * ImmutableSparseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]); // => [[1, 2, 3], [4, 5, 6]]
 * ```
 */
export const ImmutableSparseNDimArray = /* @__PURE__ */ callableClass(
  ImmutableSparseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): ImmutableSparseNDimArrayNode => new ImmutableSparseNDimArrayNode(iterable, shape),
);
export type ImmutableSparseNDimArray = ImmutableSparseNDimArrayNode;

/**
 * A sparse array changed in place with `set`.
 *
 * @param iterable - Elements or nested collections of elements to store.
 * @param shape - Axis lengths in dimension order.
 * @returns The resulting array.
 * @see SymPy `sympy.tensor.array.sparse_ndim_array.MutableSparseNDimArray`
 * @example
 * ```ts
 * import { MutableSparseNDimArray } from '@symjs/symjs';
 *
 * MutableSparseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]); // => [[1, 2, 3], [4, 5, 6]]
 * ```
 */
export const MutableSparseNDimArray = /* @__PURE__ */ callableClass(
  MutableSparseNDimArrayNode,
  (iterable: ArrayInput, shape?: ShapeInput): MutableSparseNDimArrayNode => new MutableSparseNDimArrayNode(iterable, shape),
);
export type MutableSparseNDimArray = MutableSparseNDimArrayNode;

/**
 * Represents an immutable, dense multidimensional array.
 *
 * @see SymPy `sympy.tensor.array.Array`
 */
export { ImmutableDenseNDimArray as SymArray };

/**
 * The array of `function` over the index ranges [variable, lower, upper], evaluated by `doit()`.
 *
 * @param fn - Function defining each array entry.
 * @param limits - Bound variables and their inclusive limits.
 * @returns The resulting `ArrayComprehension` expression.
 * @throws RangeError when an index occurs in its own bounds or its lower bound exceeds its upper bound.
 * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension`
 * @example
 * ```ts
 * import { ArrayComprehension, ex } from '@symjs/symjs';
 *
 * ArrayComprehension(ex`10*i + j`, [ex`i`, 1, 4], [ex`j`, 1, 3]).doit(); // => [[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]
 * ```
 */
export const ArrayComprehension = /* @__PURE__ */ callableClass(
  ArrayComprehensionNode,
  (fn: Expr | number | bigint, ...limits: ComprehensionLimit[]): ArrayComprehensionNode => new ArrayComprehensionNode(fn, ...limits),
);
export type ArrayComprehension = ArrayComprehensionNode;

/**
 * ArrayComprehension with a JavaScript function.
 *
 * @param fn - Function defining each array entry.
 * @param limits - Bound variables and their inclusive limits.
 * @returns The resulting `ArrayComprehensionMap` expression.
 * @throws RangeError when an index occurs in its own bounds or its lower bound exceeds its upper bound.
 * @throws TypeError when the callback takes more than one argument.
 * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehensionMap`
 * @example
 * ```ts
 * import { ArrayComprehensionMap, ex } from '@symjs/symjs';
 *
 * ArrayComprehensionMap(() => 1, [ex`i`, 1, 4]).doit(); // => [1, 1, 1, 1]
 * ```
 */
export const ArrayComprehensionMap = /* @__PURE__ */ callableClass(
  ArrayComprehensionMapNode,
  (fn: ComprehensionLambda, ...limits: ComprehensionLimit[]): ArrayComprehensionMapNode => new ArrayComprehensionMapNode(fn, ...limits),
);
export type ArrayComprehensionMap = ArrayComprehensionMapNode;

/**
 * The kind of arrays (cached, ArrayKind(NumberKind) by default).
 *
 * @param elementKind - Kind of the component values.
 * @returns The cached kind for arrays with elements of the specified kind.
 * @see SymPy `sympy.tensor.array.ndim_array.ArrayKind`
 * @example
 * ```ts
 * import { ArrayKind, NDimArray, NumberKind, kindOf } from '@symjs/symjs';
 *
 * kindOf(NDimArray([1, 2, 3])) === ArrayKind(NumberKind); // => True
 * ```
 */
export const ArrayKind = /* @__PURE__ */ callableClass(ArrayKindNode, (elementKind: Kind = NumberKind): ArrayKindNode => ArrayKindNode.of(elementKind));
export type ArrayKind = ArrayKindNode;

/**
 * An integer index with an optional range (a dimension n, or [lower, upper]); an integer label
 * gives the integer.
 *
 * @param label - Symbolic label used to identify this object.
 * @param range - Dimension or pair of inclusive index bounds.
 * @returns An integer index, or the integer itself for a literal integer label.
 * @throws RangeError when a range does not contain exactly two bounds.
 * @throws TypeError when the label, dimension or bounds are known to be nonintegral.
 * @see SymPy `sympy.tensor.indexed.Idx`
 * @example
 * ```ts
 * import { Idx } from '@symjs/symjs';
 *
 * Idx('qwerty'); // => qwerty
 * ```
 */
export const Idx = /* @__PURE__ */ callableClass(IdxNode, (label: string | Expr | number | bigint, range?: IdxRange): Expr => makeIdx(label, range));
export type Idx = IdxNode;
export { IndexConformanceException, getContractionStructure, getIndices } from './indexmethods';
export type { ContractionKey, ContractionStructure } from './indexmethods';
export {
  TensorIndexType,
  TensorIndex,
  TensorSymmetry,
  TensorHead,
  TensExpr,
  Tensor,
  TensMul,
  TensAdd,
  TensorElement,
  TensorManager,
  WildTensorHead,
  WildTensor,
  WildTensorIndex,
  WildTensExpr,
  tensorIndices,
  tensorHeads,
  tensorMul,
  canonBp,
  contractMetric,
  substituteIndices,
  perm2tensor,
  riemannCyclic,
  riemannCyclicReplace,
} from './tensor';
export type { ArrayReplacements, CommGroup, Commutation, TensorIndexTypeOptions, TensorManagerClass } from './tensor';
export { bsgsDirectProduct, canonicalFree, canonicalizeNaive, doubleCosetCanRep, dummySgs, gensProducts, getSymmetricGroupSgs, graphCertificate, permAfDirectProduct, tensorGens } from './tensorcan';
export type { CanonComponent, PermLike } from './tensorcan';
export { shape, NoShapeError, TensorProduct, TensorProductNode } from './functions';
export type { Dimension } from './functions';
export { ArrayExpr, ArraySymbol, ArrayElement, ArrayTensorProduct, ArrayContraction, ArrayDiagonal, ArrayAdd, ArrayElementwiseApplyFunc, PermuteDims, Reshape, OneArray, ZeroArray, getShape, getRank } from './array/expressions/arrayexpressions';
export type { ArrayShape, ArrayAxes } from './array/expressions/arrayexpressions';
export { convertMatrixToArray } from './array/expressions/frommatrixtoarray';
export { convertArrayToMatrix, identifyRemovableIdentityMatrices } from './array/expressions/fromarraytomatrix';
export { convertIndexedToArray } from './array/expressions/fromindexedtoarray';
export { convertArrayToIndexed } from './array/expressions/fromarraytoindexed';
export { arrayDerive } from './array/expressions/arrayexprderivatives';
export { ArrayDerivative, ArrayDerivativeNode } from './array/arrayderivatives';
export type { ArrayDerivativeOptions, ArrayDerivativeVariable } from './array/arrayderivatives';
