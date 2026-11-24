// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy N-dimensional arrays (sympy.tensor.array): NDimArray and its
 * dense and sparse, immutable and mutable subclasses, indexing with
 * integers, slices and symbols, printing, Flatten and derive_by_array.
 *
 * Arrays are expression nodes (ExtensionExpr), as SymPy's arrays are Basic:
 * they can appear inside expressions (`A[i, j]` with symbolic indices is an
 * Indexed whose base is the array), and subs, xreplace, freeSymbols, has,
 * diff, conjugate, transpose and adjoint reach their elements through the
 * node arguments. The arguments of a dense array are its elements in
 * row-major order; those of a sparse array are its nonzero elements in
 * index order. The mutable classes are nodes too (SymPy's are not Basic):
 * their structural key follows their current contents.
 */

import { at, cast, defined, expectType } from '../core/guard';
import type { Key } from '../printing/sortkey';
import { classKey as classKeyExpr, sortKey as sortKeyExpr } from '../printing/sortkey';
import type { Query, Replacement } from '../core/match';
import { count as countExpr, countOps as countOpsExpr, find as findExpr, replace as replaceExpr } from '../core/match';
import { asContentPrimitive as asContentPrimitiveExpr, atoms as atomsExpr, dummyEq as dummyEqExpr, hasFree as hasFreeExpr, hasXfree as hasXfreeExpr, isSame as isSameExpr } from '../core/methods';
import { match as matchExpr } from '../core/public';
import type { NoMatchResult } from '../core/truth';
import type { Assumption } from '../core/refine';
import { refine as refineExpr } from '../core/refine';
import { LambdaNode } from '../core/lambda';
import { rebuild, xreplace as xreplaceExpr } from '../core/traverse';
import { isHypergeometric as isHypergeometricExpr } from '../simplify/gammasimp';
import type { EvalfOptions, ExprLike, NumericValues, Substitution } from '../core/nodes';
import { BoolAtom, Derivative, Expr, ExtensionExpr, Integral, Rational, Rel, S, UndefFn, compareExpr } from '../core/nodes';
import type { Sym } from '../core/nodes';
import { add, couldExtractMinusSign as couldExtractMinusSignExpr, mul, pow, sympify } from '../core/ops';
import { isNegative, isNonNegative } from '../core/assumptions';
import { BoolOp } from '../core/boolalg';
import { Indexed } from '../core/indexed';
import { isNoMatch } from '../core/truth';
import { diff as diffExpr } from '../calculus/diff';
import { conjugate as conjugateExpr } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
import { ImmutableMatrixNode } from '../matrices/expressions/matexpr';
import { MatrixKind } from '../matrices/kind';
import { evalf as evalfExpr } from '../numeric/evalf';
import { expand as expandExpr } from '../simplify/expand';
import { simplify as simplifyExpr } from '../simplify/simplify';
import { IdxNode } from './idx';
import type { Kind } from '../core/kind';
import { ArrayKindNode, BooleanKind, NumberKind, UndefinedKind } from '../core/kind';

// ---- inputs -------------------------------------------------------------------

/** An element of an array given as input (booleans become true and false). */
export type ArrayElementInput = ExprLike | boolean;

/**
 * Input of the array constructors: a scalar, nested lists (any iterable), a Matrix or another
 * array. With an explicit shape, a flat list.
 */
export type NestedArrayInput = ArrayElementInput | Matrix | NDimArray | Iterable<NestedArrayInput>;

/** Sparse input: flat index or index tuple -> element. */
export type SparseArrayInput = ReadonlyMap<number | readonly number[], ArrayElementInput>;

/** Input of the array constructors. */
export type ArrayInput = NestedArrayInput | SparseArrayInput;

/** A shape: a dimension or a list of dimensions. */
export type ShapeInput = number | readonly (number | bigint | Expr)[];

/**
 * A Python slice start:stop:step for array indexing; `slice()` is the full slice `:`. Strings in
 * Python syntax (':', '1:', '::-1') are accepted wherever a Slice is.
 */
export class Slice {
  readonly #start: number | undefined;
  readonly #stop: number | undefined;
  readonly #step: number | undefined;
  /**
   * Constructs an instance of `Slice`.
   *
   * @param start - First index of the slice.
   * @param stop - Exclusive upper bound of the slice.
   * @param step - Stride between successive indices.
   * @throws TypeError when a slice bound or stride is not an integer.
   */
  constructor(start?: number, stop?: number, step?: number) {
    for (const v of [start, stop, step]) if (v !== undefined && !Number.isInteger(v)) throw new TypeError('slice indices must be integers');
    this.#start = start;
    this.#stop = stop;
    this.#step = step;
  }
  /**
   * Python slice.indices(n): the normalized [start, stop, step] for a dimension of length n.
   *
   * @param n - Length of the indexed axis.
   * @returns The normalized start, stop and step.
   * @throws RangeError when the slice stride is zero.
   */
  indices(n: number): [number, number, number] {
    const step = this.#step ?? 1;
    if (step === 0) throw new RangeError('slice step cannot be zero');
    const lower = step < 0 ? -1 : 0;
    const upper = step < 0 ? n - 1 : n;
    const clip = (v: number | undefined, dflt: number): number => {
      if (v === undefined) return dflt;
      const w = v < 0 ? v + n : v;
      return w < lower ? lower : w > upper ? upper : w;
    };
    return [clip(this.#start, step < 0 ? upper : lower), clip(this.#stop, step < 0 ? lower : upper), step];
  }
  /**
   * The indices selected in a dimension of length n.
   *
   * @param n - Length of the indexed axis.
   * @returns The selected integer positions.
   */
  expand(n: number): number[] {
    const [start, stop, step] = this.indices(n);
    const len = Math.max(0, Math.ceil((stop - start) / step));
    return Array.from({ length: len }, (_, i) => start + i * step);
  }
  /**
   * Formats this slice as text.
   *
   * @returns The formatted text.
   */
  toString(): string {
    const f = (v: number | undefined): string => (v === undefined ? '' : `${v}`);
    return `${f(this.#start)}:${f(this.#stop)}${this.#step === undefined ? '' : `:${this.#step}`}`;
  }
}

/**
 * A Python slice start:stop:step (SymPy/Python `slice`).
 *
 * @param start - First index of the slice.
 * @param stop - Exclusive upper bound of the slice.
 * @param step - Stride between successive indices.
 * @returns A Python slice start:stop:step (SymPy/Python `slice`).
 */
export function slice(start?: number, stop?: number, step?: number): Slice {
  return new Slice(start, stop, step);
}

/**
 * One position of an array index: an integer, a symbolic index, a Slice or a slice string such as
 * ':'.
 */
export type IndexItem = number | bigint | Expr | Slice | string;

function parseSliceString(s: string): Slice {
  const m = /^\s*(-?\d+)?\s*:\s*(-?\d+)?\s*(?::\s*(-?\d+)?\s*)?$/.exec(s);
  if (!m) throw new TypeError(`invalid slice ${JSON.stringify(s)}`);
  const n = (v: string | undefined): number | undefined => (v === undefined ? undefined : Number(v));
  return new Slice(n(m[1]), n(m[2]), n(m[3]));
}

type Item = number | Expr | Slice;

const isIndexItem = (v: unknown): v is IndexItem =>
  typeof v === 'number' || typeof v === 'bigint' || typeof v === 'string' || v instanceof Expr || v instanceof Slice;

const isIndexList = (v: unknown): v is readonly IndexItem[] => Array.isArray(v) && v.every(isIndexItem);

/** The index items of get/set: one list is an index tuple, otherwise each argument is one index. */
function normItems(args: readonly (IndexItem | readonly IndexItem[])[]): Item[] {
  const a0 = args[0];
  if (args.length === 1 && isIndexList(a0)) return a0.map(normItem);
  return args.map((i) => {
    if (isIndexList(i)) throw new TypeError('array indices must be integers or slices');
    return normItem(i);
  });
}

function normItem(i: IndexItem): Item {
  if (typeof i === 'string') return parseSliceString(i);
  if (typeof i === 'bigint') return Number(i);
  if (typeof i === 'number') {
    if (!Number.isInteger(i)) throw new TypeError('array indices must be integers or slices');
    return i;
  }
  return i;
}

/** An integer index from a number or an integer Rational; other numbers are rejected. */
function intIndex(i: Item): number {
  if (typeof i === 'number') return i;
  if (i instanceof Rational && i.q === 1n) return Number(i.p);
  throw new TypeError('array indices must be integers or slices');
}

const isSymbolicItem = (i: Item): i is Expr => i instanceof Expr && !i.isNumber;

const pyTuple = (xs: readonly (number | string)[]): string => (xs.length === 1 ? `(${xs[0]},)` : `(${xs.join(', ')})`);

const toElement = (v: unknown): Expr => {
  if (typeof v === 'boolean') return v ? S.true : S.false;
  if (v instanceof Expr || typeof v === 'number' || typeof v === 'bigint') return sympify(v);
  throw new TypeError(`cannot convert ${String(v)} to an array element`);
};

const isIterable = (v: unknown): v is Iterable<unknown> =>
  typeof v === 'object' && v !== null && !(v instanceof Expr && !(v instanceof NDimArray)) && Symbol.iterator in v;

/** Input of the array constructors: a scalar, a Matrix or array, nested iterables or a sparse Map. */
const isArrayInput = (v: unknown): v is ArrayInput =>
  typeof v === 'number' || typeof v === 'bigint' || typeof v === 'boolean' || v instanceof Expr || v instanceof Matrix || (typeof v === 'object' && v !== null && Symbol.iterator in v);

/** SymPy _scan_iterable_shape: the flat elements and shape of nested lists. */
function scanShape(pointer: unknown): [unknown[], number[]] {
  if (pointer instanceof Matrix) return scanShape(pointer.toArray());
  if (!isIterable(pointer)) return [[pointer], []];
  const items = [...pointer];
  if (items.length === 0) return [[], [0]];
  const parts = items.map(scanShape);
  const s0 = at(parts, 0)[1].join(',');
  if (parts.some(([, s]) => s.join(',') !== s0)) throw new RangeError('could not determine shape unambiguously');
  return [parts.flatMap(([e]) => e), [parts.length, ...at(parts, 0)[1]]];
}

/** Flatten nested lists and matrices (SymPy flatten) for an explicit shape. */
function flattenInput(v: unknown): unknown[] {
  if (v instanceof NDimArray) return v.flatElements();
  if (v instanceof Matrix) return [...v.data];
  if (isIterable(v)) return [...v].flatMap(flattenInput);
  return [v];
}

function parseShape(shape: ShapeInput): number[] {
  const dims = typeof shape === 'number' ? [shape] : [...shape];
  return dims.map((d) => {
    if (typeof d === 'number' && Number.isInteger(d)) return d;
    if (typeof d === 'bigint') return Number(d);
    if (d instanceof Rational && d.q === 1n) return Number(d.p);
    throw new TypeError('Shape should contain integers only.');
  });
}

const product = (xs: readonly number[]): number => xs.reduce((a, b) => a * b, 1);

type Parsed = { shape: number[]; flat: Expr[]; sparse?: undefined } | { shape: number[]; sparse: Map<number, Expr>; flat?: undefined };

/** SymPy _handle_ndarray_creation_inputs. */
function parseInput(iterable: ArrayInput, shapeIn: ShapeInput | undefined): Parsed {
  if (shapeIn === undefined) {
    if (iterable instanceof SparseNDimArray) return { shape: [...iterable.shape], sparse: new Map(iterable.sparseArray) };
    if (iterable instanceof NDimArray) return { shape: [...iterable.shape], flat: iterable.flatElements() };
    if (iterable instanceof Matrix) return { shape: [iterable.rows, iterable.cols], flat: [...iterable.data] };
    if (iterable instanceof Map) throw new TypeError('a dict input needs a shape');
    if (isIterable(iterable)) {
      const [flat, shape] = scanShape(iterable);
      return { shape, flat: flat.map(toElement) };
    }
    return { shape: [], flat: [toElement(iterable)] };
  }
  const shape = parseShape(shapeIn);
  if (iterable instanceof Map) {
    const sparse = new Map<number, Expr>();
    for (const [k, v] of iterable as SparseArrayInput) {
      let key: number;
      if (typeof k === 'number') key = k;
      else {
        key = 0;
        k.forEach((idx, i) => (key = key * at(shape, i) + idx));
      }
      const e = toElement(v);
      if (!isZeroElement(e)) sparse.set(key, e);
    }
    return { shape, sparse };
  }
  return { shape, flat: flattenInput(iterable).map(toElement) };
}

const isZeroElement = (e: Expr): boolean => e instanceof Rational && e.isZero;

function checkSpecialBounds(n: number, shape: readonly number[]): void {
  if (shape.length === 0 && n !== 1) throw new RangeError('arrays without shape need one scalar value');
  if (shape.length === 1 && shape[0] === 0 && n > 0) throw new RangeError('if array shape is (0,) there cannot be elements');
}

// ---- NDimArray ------------------------------------------------------------------

/**
 * The base class of N-dimensional arrays. `NDimArray(...)` (like `Array(...)`) builds an
 * ImmutableDenseNDimArray.
 *
 * @see SymPy `sympy.tensor.array.ndim_array.NDimArray`
 */
export abstract class NDimArray extends ExtensionExpr {
  /**
   * The dimensions.
   *
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.shape`
   */
  readonly shape: readonly number[];
  readonly #loopSize: number;

  /**
   * Constructs an instance of `NDimArray`.
   *
   * @param name - Symbolic name.
   * @param args - Operands in their defining order.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(name: string, args: readonly Expr[], shape: readonly number[]) {
    super(name, args);
    this.shape = Object.freeze([...shape]);
    this.#loopSize = shape.length === 0 ? 1 : product(shape);
  }

  /** The element at a flat (row-major) position. */
  protected abstract item(k: number): Expr;

  /**
   * The array entries in row-major order.
   *
   * @returns The array entries in row-major order.
   * @internal
   */
  flatElements(): Expr[] {
    return Array.from({ length: this.#loopSize }, (_, k) => this.item(k));
  }

  /**
   * Builds an array of the same concrete class with the supplied entries.
   *
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   * @returns An array of the same concrete class.
   * @internal
   */
  newLike(iterable: ArrayInput, shape?: readonly number[]): this {
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- every concrete array class has the (iterable, shape) constructor, and this.constructor is typed as Function
    const C = this.constructor as new (it: ArrayInput, sh?: ShapeInput) => this;
    return new C(iterable, shape);
  }

  /**
   * The number of dimensions (SymPy rank()).
   *
   * @returns The number of dimensions (SymPy rank()).
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.rank`
   */
  rank(): number {
    return this.shape.length;
  }

  /**
   * The number of elements.
   *
   * @returns The number of elements.
   */
  get length(): number {
    return this.#loopSize;
  }

  /**
   * An array is not a scalar.
   *
   * @returns An array is not a scalar.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.is_scalar`
   */
  override get isScalar(): boolean {
    return false;
  }

  /**
   * The index tuple of a flat position.
   *
   * @param k - Flattened index.
   * @returns The index tuple of a flat position.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray._get_tuple_index`
   */
  tupleIndex(k: number): number[] {
    const out: number[] = [];
    let r = k;
    for (let d = this.shape.length - 1; d >= 0; d--) {
      const sh = at(this.shape, d);
      out.push(r % sh);
      r = Math.floor(r / sh);
    }
    return out.reverse();
  }

  /**
   * Converts an index tuple to its flat position.
   *
   * @param index - Zero-based index or indices selecting the desired component.
   * @returns The flattened row-major index.
   * @throws RangeError when the array is empty and an index is requested or the index is not a tuple of axis indices or the axis count does not match the array rank or an index is outside the array bounds.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray._parse_index`
   * @internal
   */
  parseIndex(index: number | readonly number[]): number {
    if (typeof index === 'number') {
      if (index >= this.#loopSize) throw new RangeError('Only a tuple index is accepted');
      return index < 0 ? index + this.#loopSize : index;
    }
    if (this.#loopSize === 0) throw new RangeError('Index not valid with an empty array');
    if (index.length !== this.rank()) throw new RangeError('Wrong number of array axes');
    let k = 0;
    index.forEach((i, d) => {
      const sh = at(this.shape, d);
      if (i >= sh || i < -sh) throw new RangeError(`Index ${pyTuple(index)} out of border`);
      k = k * sh + (i < 0 ? i + sh : i);
    });
    return k;
  }

  /**
   * `a.get(1, 1)` is an element, `a.get(0)` (fewer indices than the rank) or slices (`a.get(':',
   * 1)`, `a.get(slice(1))`) give a sub-array, and symbolic indices (`a.get(i, j)`) give the
   * unevaluated Indexed `a[i, j]`. A single list is an index tuple.
   *
   * @param indexIn - Index or slice along each addressed axis.
   * @returns The selected entry or subarray.
   * @throws RangeError when the index has more entries than the array has axes or an index is outside the array bounds.
   * @throws TypeError when a slice is combined with a symbolic index.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__getitem__`
   * @example
   * ```ts
   * import { SymArray, slice } from '@symjs/symjs';
   *
   * const a = SymArray([[1, 2], [3, 4]]);
   * a.get(1, 0); // => 3
   * a.get(slice(), 1); // => [2, 4]
   * ```
   */
  get(...indexIn: (IndexItem | readonly IndexItem[])[]): Expr {
    const raw = normItems(indexIn);
    if (raw.some(isSymbolicItem)) {
      const exprs = raw.map((i) => {
        if (i instanceof Slice) throw new TypeError('slices cannot be combined with symbolic indices');
        return sympify(i);
      });
      exprs.forEach((i, d) => {
        if (d < this.shape.length && outOfRange(i, at(this.shape, d))) throw new RangeError('index out of range');
      });
      return new ArrayIndexed([this, ...exprs]);
    }
    const index = [...raw];
    while (index.length < this.rank()) index.push(new Slice());
    if (index.length > this.rank()) throw new RangeError('Dimension of index greater than rank of array');
    if (index.some((i) => i instanceof Slice)) {
      const factors = index.map((i, d) => (i instanceof Slice ? i.expand(at(this.shape, d)) : [intIndex(i)]));
      const flat = cartesian(factors).map((t) => this.item(this.parseIndex(t)));
      const nshape = factors.filter((_, d) => index[d] instanceof Slice).map((f) => f.length);
      return this.newLike(flat, nshape);
    }
    return this.item(this.parseIndex(index.map(intIndex)));
  }

  /**
   * Nested lists of the elements.
   *
   * @returns The entries as a nested list in axis order.
   * @throws RangeError when the array has rank zero.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.tolist`
   */
  tolist(): NestedList {
    if (this.rank() === 0) throw new RangeError('tolist: an array of rank 0 has no list form');
    const build = (d: number, offset: number, size: number): NestedList => {
      const n = at(this.shape, d);
      const sub = n === 0 ? 0 : size / n;
      return Array.from({ length: n }, (_, e) =>
        d === this.rank() - 1 ? this.item(offset + e) : build(d + 1, offset + e * sub, sub),
      );
    };
    return build(0, 0, this.#loopSize);
  }

  /**
   * The sub-arrays along the first axis (the element for rank 0).
   *
   * @returns An iterator over the entries in row-major order.
   */
  *[Symbol.iterator](): Iterator<Expr> {
    if (this.rank() === 0) {
      yield this.item(0);
      return;
    }
    for (let i = 0; i < at(this.shape, 0); i++) yield this.get(i);
  }

  /**
   * The same elements with another shape.
   *
   * @param newshape - New axis lengths with the same total number of entries.
   * @returns An array with the requested dimensions and the original row-major entries.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.reshape`
   */
  abstract reshape(...newshape: number[]): this;

  /**
   * The Matrix of a rank-2 array.
   *
   * @returns A matrix with the same rows and columns.
   * @throws RangeError when the input does not have dimension two.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.tomatrix`
   */
  tomatrix(): Matrix {
    if (this.rank() !== 2) throw new RangeError('Dimensions must be of size of 2');
    return Matrix.fromFunction(at(this.shape, 0), at(this.shape, 1), (i, j) => this.item(i * at(this.shape, 1) + j));
  }

  /**
   * An immutable array with the same entries and shape.
   *
   * @returns An immutable array with the same entries and shape.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.as_immutable`
   */
  abstract asImmutable(): ImmutableDenseNDimArray | ImmutableSparseNDimArray;
  /**
   * A mutable copy with the same entries and shape.
   *
   * @returns A mutable copy with the same entries and shape.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.as_mutable`
   */
  abstract asMutable(): MutableDenseNDimArray | MutableSparseNDimArray;

  /**
   * F applied to every element (a sparse array stays sparse when f(0) = 0).
   *
   * @param f - Function applied to each array entry.
   * @returns An array of the same shape with transformed entries.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.applyfunc`
   */
  applyfunc(f: (e: Expr) => ExprLike): this {
    return this.newLike(this.flatElements().map((e) => sympify(f(e))), this.shape);
  }

  // ---- arithmetic ----------------------------------------------------------------

  #zip(o: unknown, f: (a: Expr, b: Expr) => Expr): this {
    if (!(o instanceof NDimArray)) throw new TypeError('unsupported operand: an array can only be added to an array');
    if (o.shape.join(',') !== this.shape.join(',')) throw new RangeError('array shape mismatch');
    const b = o.flatElements();
    return this.newLike(
      this.flatElements().map((a, k) => f(a, at(b, k))),
      this.shape,
    );
  }
  /**
   * Elementwise sum of arrays of the same shape (the class of this array).
   *
   * @param o - Other addend.
   * @returns A same-shaped array of entrywise sums.
   * @throws TypeError when the other operand is not an N-dimensional array.
   * @throws RangeError when the arrays have different shapes.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__add__`
   */
  override add(o: ExprLike): this {
    return this.#zip(o, (a, b) => add(a, b));
  }
  /**
   * Elementwise difference of arrays of the same shape.
   *
   * @param o - Operand to subtract.
   * @returns A same-shaped array of entrywise differences.
   * @throws TypeError when the other operand is not an N-dimensional array.
   * @throws RangeError when the arrays have different shapes.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__sub__`
   */
  override sub(o: ExprLike): this {
    return this.#zip(o, (a, b) => add(a, mul(-1, b)));
  }
  /**
   * Multiplication by a scalar on the right (SymPy array*scalar); use tensorproduct for arrays.
   *
   * @param o - Second factor.
   * @returns The array with each entry multiplied on the right by the scalar.
   * @throws RangeError when the other operand is an array or a matrix.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__mul__`
   */
  override mul(o: ExprLike): this {
    const s = scalarOperand(o, 'scalar expected, use tensorproduct(...) for tensorial product');
    return this.scaleBy((e) => mul(e, s), isZeroElement(s) ? 'zero' : 'sparse');
  }
  /**
   * Multiplication by a scalar on the left.
   *
   * @param o - Left-hand factor.
   * @returns The array with each entry multiplied on the left by the scalar.
   * @throws RangeError when the other operand is an array or a matrix.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__rmul__`
   */
  rmul(o: ExprLike): this {
    const s = scalarOperand(o, 'scalar expected, use tensorproduct(...) for tensorial product');
    return this.scaleBy((e) => mul(s, e), isZeroElement(s) ? 'zero' : 'sparse');
  }
  /**
   * Division by a scalar.
   *
   * @param o - Divisor.
   * @returns The entrywise quotient by the scalar.
   * @throws RangeError when the other operand is an array or a matrix.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__truediv__`
   */
  override div(o: ExprLike): this {
    const s = scalarOperand(o, 'scalar expected');
    return this.scaleBy((e) => mul(e, pow(s, -1)), isZeroElement(s) ? 'dense' : 'sparse');
  }
  /**
   * Elementwise negation.
   *
   * @returns The array of negated entries.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.__neg__`
   */
  override neg(): this {
    return this.scaleBy((e) => mul(-1, e), 'sparse');
  }
  /**
   * Array exponentiation is unsupported.
   *
   * @param _o - Exponent.
   * @returns This operation always throws a `TypeError`.
   * @throws TypeError when an array is used as the base of an unsupported power.
   */
  override pow(_o: ExprLike): Expr {
    throw new TypeError('unsupported operand type(s) for ** or pow(): an array');
  }

  /**
   * Elementwise scalar operation; for sparse arrays `mode` says whether
   * the result is zero, maps zeros to zeros ('sparse') or must be
   * computed on every element ('dense').
   */
  protected scaleBy(f: (e: Expr) => Expr, _mode: 'zero' | 'sparse' | 'dense'): this {
    return this.newLike(this.flatElements().map(f), this.shape);
  }

  // ---- equality and structure -------------------------------------------------------

  /**
   * The same shape and the same elements (dense and sparse, mutable and immutable arrays compare
   * equal).
   *
   * @param other - Object to compare with this one.
   * @returns Whether the operands are equal.
   */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof NDimArray)) return false;
    if (other.shape.join(',') !== this.shape.join(',')) return false;
    const b = other.flatElements();
    return this.flatElements().every((a, k) => a.key === at(b, k).key);
  }

  /**
   * The transpose of a rank-2 array.
   *
   * @returns The transpose of a rank-2 array.
   * @throws RangeError when the array does not have rank two.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.transpose`
   */
  transpose(): this {
    if (this.rank() !== 2) throw new RangeError('array rank not 2');
    return permuteArray(this, [1, 0]);
  }
  /**
   * Elementwise complex conjugate.
   *
   * @returns The array of complex conjugates of the entries.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.conjugate`
   */
  override conjugate(): this {
    return this.newLike(this.flatElements().map((e) => conjugateExpr(e)), this.shape);
  }
  /**
   * Conjugate transpose of a rank-2 array.
   *
   * @returns The conjugate transpose of the array.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.adjoint`
   */
  adjoint(): this {
    return this.transpose().conjugate();
  }
  /**
   * Interchanges the two axes of the array.
   *
   * @returns The resulting expression.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray._eval_transpose`
   */
  override transposeSelf(): Expr {
    return this.transpose();
  }
  /**
   * Computes the complex conjugate.
   *
   * @returns The resulting expression.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray._eval_conjugate`
   */
  override conjugateSelf(): Expr {
    return this.conjugate();
  }
  /**
   * Computes the conjugate transpose.
   *
   * @returns The resulting expression.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray._eval_adjoint`
   */
  override adjointSelf(): Expr {
    return this.adjoint();
  }

  /**
   * The derivative of every element; a count after a variable repeats it (`a.diff(x, 2)`), and an
   * array variable gives the derivative by each of its elements (derive_by_array). The result is
   * immutable.
   *
   * @param spec - Differentiation variables, optional repetition counts and evaluation options.
   * @returns The array of partial derivatives, with axes of array variables first.
   * @throws RangeError when a derivative count is not a nonnegative integer.
   * @throws TypeError when a count precedes the first differentiation variable or no differentiation variable is supplied.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray.diff`
   */
  override diff(...spec: (Expr | number | undefined)[]): NDimArray {
    const pairs: [Expr, number][] = [];
    for (const s of spec) {
      if (s === undefined) continue;
      if (typeof s === 'number') {
        if (pairs.length === 0) throw new TypeError('diff: a count must follow a variable');
        if (!Number.isInteger(s) || s < 0) throw new RangeError('diff: counts must be non-negative integers');
        at(pairs, pairs.length - 1)[1] += s - 1;
      } else pairs.push([s, 1]);
    }
    if (pairs.length === 0) throw new TypeError('diff: no variable given');
    let cur: NDimArray = this.asImmutable();
    for (const [v, n] of pairs) {
      for (let c = 0; c < n; c++) {
        cur = v instanceof NDimArray ? cast(deriveByArray(cur, v), NDimArray) : cur.applyfunc((e) => diffExpr(e, v));
      }
    }
    return cur;
  }
  /**
   * Computes the derivative of this expression.
   *
   * @param x - Variable of differentiation.
   * @param d - Derivative function for individual operands.
   * @returns The resulting expression.
   * @see SymPy `sympy.tensor.array.ndim_array.NDimArray._eval_derivative`
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return this.asImmutable().applyfunc((e) => d(e, x));
  }

  /**
   * Substitution in every element (a Substitution, or `from` and `to`).
   *
   * @param a - Expression to replace or collection of substitutions.
   * @param b - Replacement for a single expression.
   * @returns An array of the same class with the substitutions applied.
   * @throws TypeError when the expression to substitute has no replacement.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.subs`
   */
  override subs(a: Substitution | Expr | string, b?: ExprLike): this {
    let r: Expr;
    if (a instanceof Expr || typeof a === 'string') {
      if (b === undefined) throw new TypeError('subs(from, to) requires a replacement');
      r = super.subs(a, b);
    } else r = super.subs(a);
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- substitution rebuilds the array through withArgs/newLike, which keeps its class
    return r as this;
  }
  /**
   * Elementwise expand.
   *
   * @returns The array of expanded entries.
   */
  override expand(): this {
    return this.applyfunc((e) => expandExpr(e));
  }
  /**
   * Elementwise simplify (SymPy simplify(array)).
   *
   * @returns The array of simplified entries.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.simplify`
   */
  override simplify(): this {
    return this.applyfunc((e) => simplifyExpr(e));
  }
  /**
   * Elementwise numeric evaluation.
   *
   * @param n - Requested number of decimal digits.
   * @param opts - Settings described by {@link EvalfOptions}.
   * @returns The array of numerically evaluated entries.
   */
  override evalf(n?: number | NumericValues, opts?: EvalfOptions): this {
    return this.applyfunc((e) => evalfExpr(e, n, opts));
  }
  /**
   * Alias of evalf.
   *
   * @param n - Requested number of decimal digits.
   * @param opts - Settings described by {@link EvalfOptions}.
   * @returns The array of numerically evaluated entries.
   */
  override n(n?: number | NumericValues, opts?: EvalfOptions): this {
    return this.evalf(n, opts);
  }

  // ---- SymPy Basic methods (aliases of the functions) ------------------------------

  /**
   * Splits the array into scalar content one and the original array.
   *
   * @param opts - `clear`; `radical` extract radical content.
   * @returns The scalar content and primitive part.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.as_content_primitive`
   */
  asContentPrimitive(opts: { clear?: boolean; radical?: boolean } = {}): [Rational, Expr] {
    return asContentPrimitiveExpr(this, opts);
  }
  /**
   * An array binds no variables, so it is returned unchanged.
   *
   * @returns An array binds no variables, so it is returned unchanged.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.as_dummy`
   */
  asDummy(): this {
    return this;
  }
  /**
   * The atoms of the elements (those satisfying `pred`).
   *
   * @param pred - Predicate applied to expression nodes.
   * @returns The atoms of the elements (those satisfying `pred`).
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.atoms`
   */
  atoms(pred?: (a: Expr) => boolean): Expr[] {
    return atomsExpr(this, pred);
  }
  /**
   * The class portion of the expression ordering key.
   *
   * @returns The class portion of the expression ordering key.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.class_key`
   */
  classKey(): Key {
    return classKeyExpr(this);
  }
  /**
   * The key for sorting this expression in canonical order.
   *
   * @returns The key for sorting this expression in canonical order.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.sort_key`
   */
  sortKey(): Key {
    return sortKeyExpr(this);
  }
  /**
   * -1, 0 or 1 in the canonical order of expressions.
   *
   * @param other - Expression to compare in canonical order.
   * @returns −1, 0 or 1 according to canonical order.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.compare`
   */
  compare(other: ExprLike): number {
    return Math.sign(compareExpr(this, sympify(other)));
  }
  /**
   * An array of the same class with the same elements.
   *
   * @returns An array of the same class with the same elements.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.copy`
   */
  copy(): this {
    return this.newLike(this.flatElements(), this.shape);
  }
  /**
   * False for an array.
   *
   * @returns False for an array.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.could_extract_minus_sign`
   */
  couldExtractMinusSign(): boolean {
    return couldExtractMinusSignExpr(this);
  }
  /**
   * The number of matching subexpressions.
   *
   * @param query - Expression or predicate to match.
   * @returns The number of matching subexpressions.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.count`
   */
  count(query: Query): number {
    return countExpr(this, query);
  }
  /**
   * Counts the operations in the array expression.
   *
   * @returns The number of operations in the expression.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.count_ops`
   */
  countOps(): number {
    return countOpsExpr(this);
  }
  /**
   * Evaluates each array entry.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.doit`
   */
  doit(): this {
    return this.applyfunc(defined(arrayHooks.doit, 'doit is registered by the tensor entry point'));
  }
  /**
   * Tests equality up to renaming a dummy symbol.
   *
   * @param other - Expression compared up to dummy-variable renaming.
   * @param symbol - Symbol against which a dummy variable is compared.
   * @returns Whether the expressions agree up to dummy-variable renaming.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.dummy_eq`
   */
  dummyEq(other: ExprLike, symbol?: Expr): boolean {
    return dummyEqExpr(this, other, symbol);
  }
  /**
   * The matching subexpressions.
   *
   * @param query - Expression or predicate to match.
   * @returns The matching subexpressions.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.find`
   */
  find(query: Query): Expr[] {
    return findExpr(this, query);
  }
  /**
   * Tests whether a pattern occurs free in the expression.
   *
   * @param patterns - Patterns to search for.
   * @returns Whether a pattern occurs free in the expression.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.has_free`
   */
  hasFree(...patterns: (ExprLike | { fn: string })[]): boolean {
    return hasFreeExpr(this, ...patterns);
  }
  /**
   * Tests for exact free occurrences of the supplied expressions.
   *
   * @param items - Expressions sought as exact free subexpressions.
   * @returns Whether an exact free occurrence is present.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.has_xfree`
   */
  hasXfree(items: readonly Expr[]): boolean {
    return hasXfreeExpr(this, items);
  }
  /**
   * Tests whether the ratio of successive terms in the given index is rational.
   *
   * @param k - Index variable.
   * @returns Whether the ratio of successive terms is rational in `k`.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.is_hypergeometric`
   */
  isHypergeometric(k: Expr): boolean {
    return isHypergeometricExpr(this, k);
  }
  /**
   * Tests structural equality, optionally comparing numeric values with a supplied function.
   *
   * @param other - Expression to compare structurally.
   * @param approx - Optional numerical equality test for approximate values.
   * @returns Whether the expressions have the same structure and numerical types.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.is_same`
   */
  isSame(other: unknown, approx?: (x: Expr, y: Expr) => boolean): boolean {
    return isSameExpr(this, other, approx);
  }
  /**
   * This array matched against a pattern.
   *
   * @param pattern - Pattern to match.
   * @param opts - `old`.
   * @returns Bindings for the pattern symbols, or `NoMatch` if the match fails.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.match`
   */
  match(pattern: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
    return matchExpr(this, pattern, opts);
  }
  /**
   * `expr` matched against this array as the pattern.
   *
   * @param expr - Symbolic expression on which to operate.
   * @param opts - `old`.
   * @returns Bindings for the wildcard matches, or `NoMatch` if the pattern fails.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.matches`
   */
  matches(expr: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
    return matchExpr(expr, this, opts);
  }
  /**
   * The Lambda elements (and Lambdas inside elements) applied to the arguments.
   *
   * @param args - Operands in their defining order.
   * @returns The Lambda elements (and Lambdas inside elements) applied to the arguments.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.rcall`
   */
  rcall(...args: ExprLike[]): this {
    const call = (e: Expr): Expr => (e instanceof LambdaNode ? e.call(...args) : e.args.length ? rebuild(e, e.args.map(call)) : e);
    return this.applyfunc(call);
  }
  /**
   * Every element refined under the assumptions.
   *
   * @param assumptions - Assumptions to attach to the symbol.
   * @returns The array with each entry refined under the given assumptions.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.refine`
   */
  refine(assumptions?: Assumption): this {
    return this.applyfunc((e) => refineExpr(e, assumptions));
  }
  /**
   * Replace in every element.
   *
   * @param query - Expression or predicate to match.
   * @param value - Replacement expression or function.
   * @returns The array after pattern replacement in its entries.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.replace`
   */
  replace(query: Query, value: Replacement): this {
    return this.applyfunc((e) => cast(replaceExpr(e, query, value), Expr));
  }
  /**
   * Exact replacement in every element.
   *
   * @param s - Map of exact substitutions.
   * @returns The array after exact replacement of matching subexpressions.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.xreplace`
   */
  xreplace(s: Substitution): this {
    return this.applyfunc((e) => xreplaceExpr(e, s));
  }

  // ---- printing -------------------------------------------------------------------

  /**
   * Nested lists, `Class([], shape)` when empty, the element for rank 0.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    if (this.rank() === 0) return print(this.item(0));
    if (this.shape.includes(0)) return `${this.name}([], ${pyTuple(this.shape)})`;
    const f = (d: number, offset: number, size: number): string => {
      const n = at(this.shape, d);
      const sub = size / n;
      const parts = Array.from({ length: n }, (_, e) => (d === this.rank() - 1 ? print(this.item(offset + e)) : f(d + 1, offset + e * sub, sub)));
      return `[${parts.join(', ')}]`;
    };
    return f(0, 0, this.#loopSize);
  }

  /**
   * Nested `matrix` environments in brackets (`array` when the last dimension exceeds 10).
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    if (this.rank() === 0) return print(this.item(0));
    const rank = this.rank();
    const matStr = at(this.shape, rank - 1) <= 10 ? 'matrix' : 'array';
    const cols = matStr === 'array' ? `{${'c'.repeat(at(this.shape, 0))}}` : '';
    const block = (s: string): string => `\\left[\\begin{${matStr}}${cols}${s}\\end{${matStr}}\\right]`;
    if (this.shape.includes(0)) return block('');
    const level: string[][] = Array.from({ length: rank + 1 }, () => []);
    for (let k = 0; k < this.#loopSize; k++) {
      at(level, rank).push(print(this.item(k)));
      let even = true;
      for (let back = rank - 1; back >= 0; back--) {
        if (at(level, back + 1).length < at(this.shape, back)) break;
        if (even) at(level, back).push(at(level, back + 1).join(' & '));
        else {
          let s = block(at(level, back + 1).join('\\\\'));
          if (at(level, back + 1).length === 1) s = `\\left[${s}\\right]`;
          at(level, back).push(s);
        }
        even = !even;
        level[back + 1] = [];
      }
    }
    const out = at(at(level, 0), 0);
    return rank % 2 === 1 ? block(out) : out;
  }
}

/** @internal Late-bound functions of higher layers, installed by the tensor entry point. */
export const arrayHooks: { doit?: (e: Expr) => Expr } = {};

/** Nested lists of elements. */
export type NestedList = (Expr | NestedList)[];

function scalarOperand(o: unknown, message: string): Expr {
  if (o instanceof NDimArray || o instanceof Matrix || Array.isArray(o)) throw new RangeError(message);
  return toElement(o);
}

/** Whether a symbolic index is known to lie outside 0..dim-1 (SymPy (i < 0) == True or (i >= dim) == True). */
function outOfRange(i: Expr, dim: number): boolean {
  if (i instanceof IdxNode) {
    const lo = i.lower;
    const hi = i.upper;
    if (!isNoMatch(lo) && isNonNegative(add(lo, -dim)) === true) return true;
    if (!isNoMatch(hi) && isNegative(hi) === true) return true;
  }
  return isNegative(i) === true || isNonNegative(add(i, -dim)) === true;
}

function cartesian(factors: readonly (readonly number[])[]): number[][] {
  let out: number[][] = [[]];
  for (const f of factors) out = out.flatMap((t) => f.map((v) => [...t, v]));
  return out;
}

// ---- dense arrays -------------------------------------------------------------------

/**
 * Arrays storing every element. `DenseNDimArray(...)` builds an ImmutableDenseNDimArray.
 *
 * @see SymPy `sympy.tensor.array.dense_ndim_array.DenseNDimArray`
 */
export abstract class DenseNDimArray extends NDimArray {
  /**
   * Constructs an instance of `DenseNDimArray`.
   *
   * @param name - Symbolic name.
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   * @throws RangeError when the number of supplied elements does not fit the shape.
   */
  constructor(name: string, iterable: ArrayInput, shape?: ShapeInput) {
    const p = parseInput(iterable, shape);
    let flat: Expr[];
    if (p.sparse) {
      const sp = p.sparse;
      flat = Array.from({ length: product(p.shape) }, (_, k) => sp.get(k) ?? S.Zero);
    } else flat = p.flat;
    checkSpecialBounds(flat.length, p.shape);
    const size = p.shape.length === 0 ? 1 : product(p.shape);
    if (flat.length < size) throw new RangeError(`${pyTuple(p.shape)} needs ${size} elements, got ${flat.length}`);
    const cells = flat.length > size ? flat.slice(0, size) : flat;
    super(name, cells, p.shape);
    this.#cells = cells;
  }
  readonly #cells: Expr[];
  /** The stored elements (the args array itself), for in-place changes of the mutable subclass. */
  protected get cells(): Expr[] {
    return this.#cells;
  }
  protected item(k: number): Expr {
    return at(this.args, k);
  }
  /**
   * The array entries in row-major order.
   *
   * @returns The array entries in row-major order.
   */
  override flatElements(): Expr[] {
    return [...this.args];
  }
  /**
   * Reorganizes the same entries into the requested dimensions.
   *
   * @param newshape - New axis lengths with the same total number of entries.
   * @returns An array with the requested dimensions and the original row-major entries.
   * @throws RangeError when the new dimensions would change the number of entries.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.DenseNDimArray.reshape`
   */
  reshape(...newshape: number[]): this {
    const n = product(newshape);
    if (n !== this.length) throw new RangeError(`Expecting reshape size to ${this.length} but got prod(${pyTuple(newshape)}) = ${n}`);
    return this.newLike(this.args, newshape);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return this.newLike(args, this.shape);
  }
  protected override computeKey(): string {
    return `${this.name}[${this.shape.join(',')}](${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * An immutable dense array.
 *
 * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray`
 */
export class ImmutableDenseNDimArray extends DenseNDimArray {
  /**
   * From nested lists, a flat list and a shape, a Matrix or another array (SymPy
   * ImmutableDenseNDimArray(iterable, shape)).
   *
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('ImmutableDenseNDimArray', iterable, shape);
  }
  /** An array of zeros of the given shape. */
  /**
   * The array of the constructor arguments (iterable, shape).
   *
   * @param args - Operands in their defining order.
   * @returns The array of the constructor arguments (iterable, shape).
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.fromiter`
   */
  static fromiter(args: readonly [ArrayInput, ShapeInput?]): ImmutableDenseNDimArray {
    return new ImmutableDenseNDimArray(...args);
  }
  /**
   * Creates a zero-filled array of the requested shape.
   *
   * @param shape - Axis lengths in dimension order.
   * @returns An array of the specified shape with every entry zero.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.zeros`
   */
  static zeros(...shape: number[]): ImmutableDenseNDimArray {
    return new ImmutableDenseNDimArray(Array.from({ length: product(shape) }, () => 0), shape);
  }
  /**
   * An immutable array with the same entries and shape.
   *
   * @returns An immutable array with the same entries and shape.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.as_immutable`
   */
  asImmutable(): ImmutableDenseNDimArray {
    return this;
  }
  /**
   * A mutable copy with the same entries and shape.
   *
   * @returns A mutable copy with the same entries and shape.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.ImmutableDenseNDimArray.as_mutable`
   */
  asMutable(): MutableDenseNDimArray {
    return new MutableDenseNDimArray(this);
  }
}

/**
 * A dense array changed in place with `set`.
 *
 * @see SymPy `sympy.tensor.array.dense_ndim_array.MutableDenseNDimArray`
 */
export class MutableDenseNDimArray extends DenseNDimArray {
  /**
   * From nested lists, a flat list and a shape, a Matrix or another array.
   *
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('MutableDenseNDimArray', iterable, shape);
  }
  /**
   * An array of zeros of the given shape.
   *
   * @param shape - Axis lengths in dimension order.
   * @returns An array of the specified shape with every entry zero.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.MutableDenseNDimArray.zeros`
   */
  static zeros(...shape: number[]): MutableDenseNDimArray {
    return new MutableDenseNDimArray(Array.from({ length: product(shape) }, () => 0), shape);
  }
  /**
   * The key follows the current contents.
   *
   * @returns The key follows the current contents.
   */
  override get key(): string {
    return this.computeKey();
  }
  /**
   * `m.set(i, j, value)`; a single integer is a flat position, and slices assign a sub-array
   * (`m.set(0, ':', [9, 8])`).
   *
   * @param args - Index or indices followed by the new entry or subarray.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.MutableDenseNDimArray.__setitem__`
   */
  set(...args: [...(IndexItem | readonly IndexItem[])[], ArrayInput]): void {
    assignItems(this, args, (k, v) => (this.cells[k] = v));
  }
  /**
   * An immutable array with the same entries and shape.
   *
   * @returns An immutable array with the same entries and shape.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.MutableDenseNDimArray.as_immutable`
   */
  asImmutable(): ImmutableDenseNDimArray {
    return new ImmutableDenseNDimArray(this);
  }
  /**
   * A mutable copy with the same entries and shape.
   *
   * @returns A mutable copy with the same entries and shape.
   * @see SymPy `sympy.tensor.array.dense_ndim_array.MutableDenseNDimArray.as_mutable`
   */
  asMutable(): MutableDenseNDimArray {
    return this;
  }
}

// ---- sparse arrays ------------------------------------------------------------------

/**
 * Arrays storing only their nonzero elements. `SparseNDimArray(...)` builds an
 * ImmutableSparseNDimArray.
 *
 * @see SymPy `sympy.tensor.array.sparse_ndim_array.SparseNDimArray`
 */
export abstract class SparseNDimArray extends NDimArray {
  protected readonly sparse: Map<number, Expr>;
  /**
   * Constructs an instance of `SparseNDimArray`.
   *
   * @param name - Symbolic name.
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(name: string, iterable: ArrayInput, shape?: ShapeInput) {
    const p = parseInput(iterable, shape);
    let sparse: Map<number, Expr>;
    if (p.sparse) {
      sparse = p.sparse;
      checkSpecialBounds(p.sparse.size, p.shape);
    } else {
      checkSpecialBounds(p.flat.length, p.shape);
      sparse = new Map();
      p.flat.forEach((e, k) => {
        if (!isZeroElement(e)) sparse.set(k, e);
      });
    }
    sparse = new Map([...sparse].sort(([a], [b]) => a - b));
    const values = [...sparse.values()];
    super(name, values, p.shape);
    this.sparse = sparse;
    this.#values = values;
  }
  readonly #values: Expr[];
  /** The stored nonzero elements (the args array itself), for in-place changes of the mutable subclass. */
  protected get values(): Expr[] {
    return this.#values;
  }
  protected item(k: number): Expr {
    return this.sparse.get(k) ?? S.Zero;
  }
  /**
   * Stored nonzero entries keyed by their flat positions.
   *
   * @returns The entries indexed by their flat positions.
   * @internal
   */
  get sparseArray(): ReadonlyMap<number, Expr> {
    return this.sparse;
  }
  /**
   * Reorganizes the same entries into the requested dimensions.
   *
   * @param newshape - New axis lengths with the same total number of entries.
   * @returns An array with the requested dimensions and the original row-major entries.
   * @throws RangeError when a new dimension is invalid.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.SparseNDimArray.reshape`
   */
  reshape(...newshape: number[]): this {
    const n = product(newshape);
    if (n !== this.length) throw new RangeError(`Invalid reshape parameters ${pyTuple(newshape)}`);
    return this.newLike(new Map(this.sparse), newshape);
  }
  /**
   * Apply a function to each element of the N-dim array.
   *
   * @param f - Function applied to each array entry.
   * @returns An array of the same shape with transformed entries.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.SparseNDimArray.applyfunc`
   */
  override applyfunc(f: (e: Expr) => ExprLike): this {
    if (!isZeroElement(sympify(f(S.Zero)))) return super.applyfunc(f);
    const m = new Map<number, Expr>();
    for (const [k, v] of this.sparse) {
      const w = sympify(f(v));
      if (!isZeroElement(w)) m.set(k, w);
    }
    return this.newLike(m, this.shape);
  }
  protected override scaleBy(f: (e: Expr) => Expr, mode: 'zero' | 'sparse' | 'dense'): this {
    if (mode === 'zero') return this.newLike(new Map(), this.shape);
    if (mode === 'dense') return super.scaleBy(f, mode);
    const m = new Map<number, Expr>();
    for (const [k, v] of this.sparse) m.set(k, f(v));
    return this.newLike(m, this.shape);
  }
  /**
   * Tests equality of the entries and shape.
   *
   * @param other - Object to compare with this one.
   * @returns Whether the operands are equal.
   */
  override equals(other: ExprLike): boolean {
    if (other instanceof SparseNDimArray) {
      if (other.shape.join(',') !== this.shape.join(',') || other.sparse.size !== this.sparse.size) return false;
      return [...this.sparse].every(([k, v]) => other.sparse.get(k)?.key === v.key);
    }
    return super.equals(other);
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    const keys = [...this.sparse.keys()];
    return this.newLike(new Map(keys.map((k, i) => [k, at(args, i)])), this.shape);
  }
  protected override computeKey(): string {
    return `${this.name}[${this.shape.join(',')}](${[...this.sparse].map(([k, v]) => `${k}:${v.key}`).join(',')})`;
  }
}

/**
 * An immutable sparse array.
 *
 * @see SymPy `sympy.tensor.array.sparse_ndim_array.ImmutableSparseNDimArray`
 */
export class ImmutableSparseNDimArray extends SparseNDimArray {
  /**
   * From nested lists, a flat list and a shape, a Map of nonzero elements and a shape, a Matrix or
   * another array.
   *
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('ImmutableSparseNDimArray', iterable, shape);
  }
  /**
   * An array of zeros of the given shape.
   *
   * @param shape - Axis lengths in dimension order.
   * @returns An array of the specified shape with every entry zero.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.ImmutableSparseNDimArray.zeros`
   */
  static zeros(...shape: number[]): ImmutableSparseNDimArray {
    return new ImmutableSparseNDimArray(new Map(), shape);
  }
  /**
   * An immutable array with the same entries and shape.
   *
   * @returns An immutable array with the same entries and shape.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.ImmutableSparseNDimArray.as_immutable`
   */
  asImmutable(): ImmutableSparseNDimArray {
    return this;
  }
  /**
   * A mutable copy with the same entries and shape.
   *
   * @returns A mutable copy with the same entries and shape.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.ImmutableSparseNDimArray.as_mutable`
   */
  asMutable(): MutableSparseNDimArray {
    return new MutableSparseNDimArray(this);
  }
}

/**
 * A sparse array changed in place with `set`.
 *
 * @see SymPy `sympy.tensor.array.sparse_ndim_array.MutableSparseNDimArray`
 */
export class MutableSparseNDimArray extends SparseNDimArray {
  /**
   * From nested lists, a flat list and a shape, a Map of nonzero elements and a shape, a Matrix or
   * another array.
   *
   * @param iterable - Elements or nested collections of elements to store.
   * @param shape - Axis lengths in dimension order.
   */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('MutableSparseNDimArray', iterable, shape);
  }
  /**
   * An array of zeros of the given shape.
   *
   * @param shape - Axis lengths in dimension order.
   * @returns An array of the specified shape with every entry zero.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.MutableSparseNDimArray.zeros`
   */
  static zeros(...shape: number[]): MutableSparseNDimArray {
    return new MutableSparseNDimArray(new Map(), shape);
  }
  /**
   * The key follows the current contents.
   *
   * @returns The key follows the current contents.
   */
  override get key(): string {
    return this.computeKey();
  }
  /**
   * `m.set(i, j, value)`; a single integer is a flat position, and slices assign a sub-array. Zeros
   * are not stored.
   *
   * @param args - Index or indices followed by the new entry or subarray.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.MutableSparseNDimArray.__setitem__`
   */
  set(...args: [...(IndexItem | readonly IndexItem[])[], ArrayInput]): void {
    assignItems(this, args, (k, v) => {
      if (isZeroElement(v)) this.sparse.delete(k);
      else this.sparse.set(k, v);
    });
    const sorted = [...this.sparse].sort(([a], [b]) => a - b);
    this.sparse.clear();
    for (const [k, v] of sorted) this.sparse.set(k, v);
    const args2 = this.values;
    args2.length = 0;
    args2.push(...this.sparse.values());
  }
  /**
   * An immutable array with the same entries and shape.
   *
   * @returns An immutable array with the same entries and shape.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.MutableSparseNDimArray.as_immutable`
   */
  asImmutable(): ImmutableSparseNDimArray {
    return new ImmutableSparseNDimArray(this);
  }
  /**
   * A mutable copy with the same entries and shape.
   *
   * @returns A mutable copy with the same entries and shape.
   * @see SymPy `sympy.tensor.array.sparse_ndim_array.MutableSparseNDimArray.as_mutable`
   */
  asMutable(): MutableSparseNDimArray {
    return this;
  }
}

/** SymPy __setitem__ of the mutable arrays. */
function assignItems(a: NDimArray, args: readonly unknown[], store: (k: number, v: Expr) => void): void {
  if (args.length === 0) throw new TypeError('set: a value is required');
  const value: unknown = args[args.length - 1];
  const idxArgs = args.slice(0, -1).map((x) => {
    if (isIndexItem(x) || isIndexList(x)) return x;
    throw new TypeError('array indices must be integers or slices');
  });
  const tuple = !(idxArgs.length === 1 && !Array.isArray(idxArgs[0]));
  const items = normItems(idxArgs);
  if (items.some(isSymbolicItem)) throw new TypeError('cannot assign to a symbolic index');
  if (items.some((i) => i instanceof Slice)) {
    if (items.length > a.rank()) throw new RangeError('Dimension of index greater than rank of array');
    const v = value instanceof NDimArray ? value : a.newLike(expectType(value, isArrayInput, 'array value'));
    const factors = items.map((i, d) => (i instanceof Slice ? i.expand(at(a.shape, d)) : [intIndex(i)]));
    // SymPy: the position in the value is the index minus the smallest index of each slice
    const offsets = items.flatMap((i, d) => (i instanceof Slice && at(factors, d).length > 0 ? [[d, Math.min(...at(factors, d))] as const] : []));
    for (const t of cartesian(factors)) store(a.parseIndex(t), v.get(offsets.map(([d, o]) => at(t, d) - o)));
    return;
  }
  if (value instanceof NDimArray || value instanceof Matrix || (typeof value === 'object' && (value === null || Symbol.iterator in value))) {
    throw new TypeError('array element must be a scalar');
  }
  store(a.parseIndex(tuple ? items.map(intIndex) : intIndex(at(items, 0))), toElement(value));
}

// ---- Indexed with an array base ------------------------------------------------------

/**
 * Indexed(array, *indices) as produced by symbolic array indexing: printed
 * `[[0, 1], [2, 3]][i, j]`, it becomes the element once the indices are
 * numbers (SymPy Indexed.__new__ with an array base).
 */
class ArrayIndexed extends Indexed {
  override withArgs(args: readonly Expr[]): Expr {
    const [base, ...indices] = args;
    // A base substituted by something else than an array gives a plain Indexed.
    if (!(base instanceof NDimArray)) return new Indexed(args);
    if (indices.every((i) => i.isNumber)) return base.get(...indices);
    return new ArrayIndexed(args);
  }
  /** SymPy: the derivative of the array, indexed the same way (diff itself handles x == this). */
  override diffSelf(x: Expr): Expr {
    return new ArrayIndexed([cast(this.base, NDimArray).diff(x), ...this.indices]);
  }
}

// ---- Flatten, kinds, permutation and derive_by_array -----------------------------------

/**
 * Iterates the elements of an array, Matrix or nested list in row-major order.
 *
 * @see SymPy `sympy.tensor.array.arrayop.Flatten`
 * @example
 * ```ts
 * import { Flatten, SymArray } from '@symjs/symjs';
 *
 * const a = SymArray([0, 1, 2, 3, 4, 5], [2, 3]);
 * [...new Flatten(a)]; // => [0, 1, 2, 3, 4, 5]
 * ```
 */
export class Flatten implements Iterable<Expr> {
  readonly #source: NDimArray | Matrix;
  /**
   * Constructs an instance of `Flatten`.
   *
   * @param iterable - Elements or nested collections of elements to store.
   */
  constructor(iterable: NDimArray | Matrix | readonly NestedArrayInput[]) {
    this.#source = iterable instanceof NDimArray || iterable instanceof Matrix ? iterable : new ImmutableDenseNDimArray(iterable);
  }
  /**
   * Iterates over the individual array entries.
   *
   * @returns An iterator over the entries in row-major order.
   */
  *[Symbol.iterator](): Iterator<Expr> {
    yield* this.#source instanceof Matrix ? this.#source.data : this.#source.flatElements();
  }
  /**
   * Formats this flatten as text.
   *
   * @returns The formatted text.
   */
  toString(): string {
    return `Flatten(${this.#source.toString()})`;
  }
}

/**
 * The mathematical kind of an expression or matrix, including the element kind of an array.
 *
 * @param e - Expression to inspect.
 * @returns The mathematical kind of an expression or matrix, including the element kind of an array.
 * @see SymPy `sympy.core.basic.Basic.kind`
 */
export function kindOf(e: Expr | Matrix): Kind {
  if (e instanceof ImmutableMatrixNode) return kindOf(e.matrix);
  if (e instanceof Matrix) {
    const elementKind = e.data.length ? kindOf(at(e.data, 0)) : NumberKind;
    return MatrixKind(e.data.some((entry) => kindOf(entry) !== elementKind) ? UndefinedKind : elementKind);
  }
  if (e instanceof NDimArray) return ArrayKindNode.union(e.flatElements().map(kindOf));
  if (e instanceof BoolAtom || e instanceof Rel || e instanceof BoolOp) return BooleanKind;
  if (e instanceof Integral || e instanceof Derivative) return kindOf(at(e.args, 0));
  const own = e instanceof ExtensionExpr ? e.kindSelf() : undefined;
  if (own !== undefined) return own;
  if (e instanceof ExtensionExpr && !(e instanceof Indexed) && e.isScalar === false) return UndefinedKind;
  return e.isCommutative ? NumberKind : UndefinedKind;
}

/** @internal SymPy permutedims for an array and a permutation list. */
export function permuteArray<T extends NDimArray>(a: T, perm: readonly number[]): T {
  if (perm.length !== a.rank()) throw new RangeError('wrong permutation size');
  if ([...perm].sort((x, y) => x - y).some((v, i) => v !== i)) throw new RangeError(`invalid permutation ${pyTuple(perm)}`);
  const inv: number[] = [];
  perm.forEach((p, i) => (inv[p] = i));
  const newShape = perm.map((p) => at(a.shape, p));
  if (a instanceof SparseNDimArray) {
    const m = new Map<readonly number[], Expr>();
    for (const [k, v] of a.sparseArray) {
      const t = a.tupleIndex(k);
      m.set(
        perm.map((p) => at(t, p)),
        v,
      );
    }
    return a.newLike(m, newShape);
  }
  const flat = cartesian(newShape.map((n) => Array.from({ length: n }, (_, i) => i))).map((idx) => a.get(inv.map((j) => at(idx, j))));
  return a.newLike(flat, newShape);
}

const isArrayLike = (v: unknown): v is NDimArray | Matrix | readonly NestedArrayInput[] =>
  v instanceof NDimArray || v instanceof Matrix || Array.isArray(v);

/** SymPy _diff_wrt: symbols, undefined functions, Indexed, derivatives and arrays can be differentiated by. */
const diffWrt = (e: Expr): boolean =>
  e.kind === 'Symbol' || e instanceof UndefFn || e instanceof Indexed || e instanceof Derivative || e instanceof NDimArray ||
  (e instanceof ExtensionExpr && (e.name === 'MatrixElement' || e.name === 'ArrayElement'));

/**
 * The derivative of an expression or array by a symbol or by every element of an array; the
 * result has shape dx.shape + expr.shape.
 *
 * @param expr - Symbolic expression on which to operate.
 * @param dx - Scalar or array of differentiation variables.
 * @returns The derivative of an expression or array by a symbol or by every element of an array; the result has shape dx.shape + expr.shape.
 * @throws RangeError when the differentiation array contains an invalid variable.
 * @see SymPy `sympy.tensor.array.arrayop.derive_by_array`
 * @example
 * ```ts
 * import { cos, deriveByArray, ex } from '@symjs/symjs';
 *
 * deriveByArray(ex`cos(x*t)`, ex`x`); // => -t*sin(t*x)
 * ```
 */
export function deriveByArray(expr: ExprLike | Matrix | readonly NestedArrayInput[], dx: ExprLike | Matrix | readonly NestedArrayInput[]): Expr {
  if (isArrayLike(dx)) {
    const dxa = new ImmutableDenseNDimArray(dx);
    for (const i of dxa) if (!diffWrt(i)) throw new RangeError('cannot derive by this array');
    const vars = dxa.flatElements();
    if (!isArrayLike(expr)) {
      const e = sympify(expr);
      return new ImmutableDenseNDimArray(vars.map((v) => diffExpr(e, v)), dxa.shape);
    }
    const ea = expr instanceof NDimArray ? expr.asImmutable() : new ImmutableDenseNDimArray(expr);
    if (ea instanceof SparseNDimArray) {
      const lp = ea.length;
      const m = new Map<number, Expr>();
      vars.forEach((x, i) => {
        for (const [k, v] of cast(ea.diff(x), SparseNDimArray).sparseArray) m.set(k + i * lp, v);
      });
      return ea.newLike(m, [...dxa.shape, ...ea.shape]);
    }
    return ea.newLike(
      vars.flatMap((x) => ea.flatElements().map((y) => diffExpr(y, x))),
      [...dxa.shape, ...ea.shape],
    );
  }
  const x = sympify(dx);
  if (isArrayLike(expr)) return (expr instanceof NDimArray ? expr.asImmutable() : new ImmutableDenseNDimArray(expr)).diff(x);
  return diffExpr(sympify(expr), x);
}
