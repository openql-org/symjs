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

import { at, cast, expectType } from '../core/guard';
import type { EvalfOptions, ExprLike, NumericValues, Substitution } from '../core/nodes';
import { BoolAtom, Derivative, Expr, ExtensionExpr, Integral, Rational, Rel, S, UndefFn } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { isNegative, isNonNegative } from '../core/assumptions';
import { BoolOp } from '../core/boolalg';
import { Indexed } from '../core/indexed';
import { isNoMatch } from '../core/truth';
import { diff as diffExpr } from '../calculus/diff';
import { conjugate as conjugateExpr } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
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
 * Input of the array constructors: a scalar, nested lists (any iterable),
 * a Matrix or another array. With an explicit shape, a flat list.
 */
export type NestedArrayInput = ArrayElementInput | Matrix | NDimArray | Iterable<NestedArrayInput>;

/** Sparse input: flat index or index tuple -> element (SymPy dict input; needs a shape). */
export type SparseArrayInput = ReadonlyMap<number | readonly number[], ArrayElementInput>;

/** Input of the array constructors. */
export type ArrayInput = NestedArrayInput | SparseArrayInput;

/** A shape: a dimension or a list of dimensions. */
export type ShapeInput = number | readonly (number | bigint | Expr)[];

/**
 * A Python slice start:stop:step for array indexing; `slice()` is the
 * full slice `:`. Strings in Python syntax (':', '1:', '::-1') are
 * accepted wherever a Slice is.
 */
export class Slice {
  readonly #start: number | undefined;
  readonly #stop: number | undefined;
  readonly #step: number | undefined;
  constructor(start?: number, stop?: number, step?: number) {
    for (const v of [start, stop, step]) if (v !== undefined && !Number.isInteger(v)) throw new TypeError('slice indices must be integers');
    this.#start = start;
    this.#stop = stop;
    this.#step = step;
  }
  /** Python slice.indices(n): the normalized [start, stop, step] for a dimension of length n. */
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
  /** The indices selected in a dimension of length n. */
  expand(n: number): number[] {
    const [start, stop, step] = this.indices(n);
    const len = Math.max(0, Math.ceil((stop - start) / step));
    return Array.from({ length: len }, (_, i) => start + i * step);
  }
  toString(): string {
    const f = (v: number | undefined): string => (v === undefined ? '' : `${v}`);
    return `${f(this.#start)}:${f(this.#stop)}${this.#step === undefined ? '' : `:${this.#step}`}`;
  }
}

/** A Python slice start:stop:step (SymPy/Python `slice`). */
export function slice(start?: number, stop?: number, step?: number): Slice {
  return new Slice(start, stop, step);
}

/** One position of an array index: an integer, a symbolic index, a Slice or a slice string such as ':'. */
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
 * SymPy NDimArray: the base class of N-dimensional arrays. `NDimArray(...)`
 * (like `Array(...)`) builds an ImmutableDenseNDimArray.
 */
export abstract class NDimArray extends ExtensionExpr {
  /** The dimensions (SymPy shape). */
  readonly shape: readonly number[];
  readonly #loopSize: number;

  constructor(name: string, args: readonly Expr[], shape: readonly number[]) {
    super(name, args);
    this.shape = Object.freeze([...shape]);
    this.#loopSize = shape.length === 0 ? 1 : product(shape);
  }

  /** The element at a flat (row-major) position. */
  protected abstract item(k: number): Expr;

  /** @internal All elements in row-major order (SymPy Flatten). */
  flatElements(): Expr[] {
    return Array.from({ length: this.#loopSize }, (_, k) => this.item(k));
  }

  /** @internal A new array of the same class (SymPy type(self)(iterable, shape)). */
  newLike(iterable: ArrayInput, shape?: readonly number[]): this {
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- every concrete array class has the (iterable, shape) constructor, and this.constructor is typed as Function
    const C = this.constructor as new (it: ArrayInput, sh?: ShapeInput) => this;
    return new C(iterable, shape);
  }

  /** The number of dimensions (SymPy rank()). */
  rank(): number {
    return this.shape.length;
  }

  /** The number of elements (SymPy len). */
  get length(): number {
    return this.#loopSize;
  }

  /** SymPy is_scalar: an array is not a scalar. */
  override get isScalar(): boolean {
    return false;
  }

  /** SymPy _get_tuple_index: the index tuple of a flat position. */
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

  /** @internal SymPy _parse_index: the flat position of an index tuple (negative indices count from the end). */
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
   * SymPy __getitem__: `a.get(1, 1)` is an element, `a.get(0)` (fewer
   * indices than the rank) or slices (`a.get(':', 1)`, `a.get(slice(1))`)
   * give a sub-array, and symbolic indices (`a.get(i, j)`) give the
   * unevaluated Indexed `a[i, j]`. A single list is an index tuple.
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

  /** SymPy tolist: nested lists of the elements. */
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

  /** SymPy iteration: the sub-arrays along the first axis (the element for rank 0). */
  *[Symbol.iterator](): Iterator<Expr> {
    if (this.rank() === 0) {
      yield this.item(0);
      return;
    }
    for (let i = 0; i < at(this.shape, 0); i++) yield this.get(i);
  }

  /** SymPy reshape(*newshape): the same elements with another shape. */
  abstract reshape(...newshape: number[]): this;

  /** SymPy tomatrix: the Matrix of a rank-2 array. */
  tomatrix(): Matrix {
    if (this.rank() !== 2) throw new RangeError('Dimensions must be of size of 2');
    return Matrix.fromFunction(at(this.shape, 0), at(this.shape, 1), (i, j) => this.item(i * at(this.shape, 1) + j));
  }

  /** SymPy as_immutable. */
  abstract asImmutable(): ImmutableDenseNDimArray | ImmutableSparseNDimArray;
  /** SymPy as_mutable. */
  abstract asMutable(): MutableDenseNDimArray | MutableSparseNDimArray;

  /** SymPy applyfunc(f): f applied to every element (a sparse array stays sparse when f(0) = 0). */
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
  /** Elementwise sum of arrays of the same shape (the class of this array). */
  override add(o: ExprLike): this {
    return this.#zip(o, (a, b) => add(a, b));
  }
  /** Elementwise difference of arrays of the same shape. */
  override sub(o: ExprLike): this {
    return this.#zip(o, (a, b) => add(a, mul(-1, b)));
  }
  /** Multiplication by a scalar on the right (SymPy array*scalar); use tensorproduct for arrays. */
  override mul(o: ExprLike): this {
    const s = scalarOperand(o, 'scalar expected, use tensorproduct(...) for tensorial product');
    return this.scaleBy((e) => mul(e, s), isZeroElement(s) ? 'zero' : 'sparse');
  }
  /** Multiplication by a scalar on the left (SymPy scalar*array). */
  rmul(o: ExprLike): this {
    const s = scalarOperand(o, 'scalar expected, use tensorproduct(...) for tensorial product');
    return this.scaleBy((e) => mul(s, e), isZeroElement(s) ? 'zero' : 'sparse');
  }
  /** Division by a scalar. */
  override div(o: ExprLike): this {
    const s = scalarOperand(o, 'scalar expected');
    return this.scaleBy((e) => mul(e, pow(s, -1)), isZeroElement(s) ? 'dense' : 'sparse');
  }
  /** Elementwise negation. */
  override neg(): this {
    return this.scaleBy((e) => mul(-1, e), 'sparse');
  }
  /** Arrays have no powers (SymPy raises TypeError). */
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

  /** SymPy ==: the same shape and the same elements (dense and sparse, mutable and immutable arrays compare equal). */
  override equals(other: ExprLike): boolean {
    if (!(other instanceof NDimArray)) return false;
    if (other.shape.join(',') !== this.shape.join(',')) return false;
    const b = other.flatElements();
    return this.flatElements().every((a, k) => a.key === at(b, k).key);
  }

  /** SymPy transpose: the transpose of a rank-2 array. */
  transpose(): this {
    if (this.rank() !== 2) throw new RangeError('array rank not 2');
    return permuteArray(this, [1, 0]);
  }
  /** Elementwise complex conjugate. */
  override conjugate(): this {
    return this.newLike(this.flatElements().map((e) => conjugateExpr(e)), this.shape);
  }
  /** Conjugate transpose of a rank-2 array. */
  adjoint(): this {
    return this.transpose().conjugate();
  }
  override transposeSelf(): Expr {
    return this.transpose();
  }
  override conjugateSelf(): Expr {
    return this.conjugate();
  }
  override adjointSelf(): Expr {
    return this.adjoint();
  }

  /**
   * SymPy diff(*symbols): the derivative of every element; a count after
   * a variable repeats it (`a.diff(x, 2)`), and an array variable gives the
   * derivative by each of its elements (derive_by_array). The result is
   * immutable.
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
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    return this.asImmutable().applyfunc((e) => d(e, x));
  }

  /** Substitution in every element (a Substitution, or `from` and `to`). */
  override subs(a: Substitution | Expr, b?: ExprLike): this {
    let r: Expr;
    if (a instanceof Expr) {
      if (b === undefined) throw new TypeError('subs(from, to) requires a replacement');
      r = super.subs(a, b);
    } else r = super.subs(a);
    // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- substitution rebuilds the array through withArgs/newLike, which keeps its class
    return r as this;
  }
  /** Elementwise expand. */
  override expand(): this {
    return this.applyfunc((e) => expandExpr(e));
  }
  /** Elementwise simplify (SymPy simplify(array)). */
  override simplify(): this {
    return this.applyfunc((e) => simplifyExpr(e));
  }
  /** Elementwise numeric evaluation. */
  override evalf(n?: number | NumericValues, opts?: EvalfOptions): this {
    return this.applyfunc((e) => evalfExpr(e, n, opts));
  }
  /** Alias of evalf. */
  override n(n?: number | NumericValues, opts?: EvalfOptions): this {
    return this.evalf(n, opts);
  }

  // ---- printing -------------------------------------------------------------------

  /** SymPy str: nested lists, `Class([], shape)` when empty, the element for rank 0. */
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

  /** SymPy LaTeX: nested `matrix` environments in brackets (`array` when the last dimension exceeds 10). */
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

/** Nested lists of elements (SymPy tolist). */
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

/** SymPy DenseNDimArray: arrays storing every element. `DenseNDimArray(...)` builds an ImmutableDenseNDimArray. */
export abstract class DenseNDimArray extends NDimArray {
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
  override flatElements(): Expr[] {
    return [...this.args];
  }
  /** SymPy reshape(*newshape). */
  reshape(...newshape: number[]): this {
    const n = product(newshape);
    if (n !== this.length) throw new RangeError(`Expecting reshape size to ${this.length} but got prod(${pyTuple(newshape)}) = ${n}`);
    return this.newLike(this.args, newshape);
  }
  withArgs(args: readonly Expr[]): Expr {
    return this.newLike(args, this.shape);
  }
  protected override computeKey(): string {
    return `${this.name}[${this.shape.join(',')}](${this.args.map((a) => a.key).join(',')})`;
  }
}

/** SymPy ImmutableDenseNDimArray (also `Array`): an immutable dense array. */
export class ImmutableDenseNDimArray extends DenseNDimArray {
  /** From nested lists, a flat list and a shape, a Matrix or another array (SymPy ImmutableDenseNDimArray(iterable, shape)). */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('ImmutableDenseNDimArray', iterable, shape);
  }
  /** An array of zeros of the given shape. */
  static zeros(...shape: number[]): ImmutableDenseNDimArray {
    return new ImmutableDenseNDimArray(Array.from({ length: product(shape) }, () => 0), shape);
  }
  asImmutable(): ImmutableDenseNDimArray {
    return this;
  }
  asMutable(): MutableDenseNDimArray {
    return new MutableDenseNDimArray(this);
  }
}

/** SymPy MutableDenseNDimArray: a dense array changed in place with `set`. */
export class MutableDenseNDimArray extends DenseNDimArray {
  /** From nested lists, a flat list and a shape, a Matrix or another array. */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('MutableDenseNDimArray', iterable, shape);
  }
  /** An array of zeros of the given shape. */
  static zeros(...shape: number[]): MutableDenseNDimArray {
    return new MutableDenseNDimArray(Array.from({ length: product(shape) }, () => 0), shape);
  }
  /** The key follows the current contents. */
  override get key(): string {
    return this.computeKey();
  }
  /**
   * SymPy __setitem__: `m.set(i, j, value)`; a single integer is a flat
   * position, and slices assign a sub-array (`m.set(0, ':', [9, 8])`).
   */
  set(...args: [...(IndexItem | readonly IndexItem[])[], ArrayInput]): void {
    assignItems(this, args, (k, v) => (this.cells[k] = v));
  }
  asImmutable(): ImmutableDenseNDimArray {
    return new ImmutableDenseNDimArray(this);
  }
  asMutable(): MutableDenseNDimArray {
    return this;
  }
}

// ---- sparse arrays ------------------------------------------------------------------

/** SymPy SparseNDimArray: arrays storing only their nonzero elements. `SparseNDimArray(...)` builds an ImmutableSparseNDimArray. */
export abstract class SparseNDimArray extends NDimArray {
  protected readonly sparse: Map<number, Expr>;
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
  /** @internal The nonzero elements by flat position (SymPy _sparse_array). */
  get sparseArray(): ReadonlyMap<number, Expr> {
    return this.sparse;
  }
  /** SymPy reshape(*newshape). */
  reshape(...newshape: number[]): this {
    const n = product(newshape);
    if (n !== this.length) throw new RangeError(`Invalid reshape parameters ${pyTuple(newshape)}`);
    return this.newLike(new Map(this.sparse), newshape);
  }
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
  override equals(other: ExprLike): boolean {
    if (other instanceof SparseNDimArray) {
      if (other.shape.join(',') !== this.shape.join(',') || other.sparse.size !== this.sparse.size) return false;
      return [...this.sparse].every(([k, v]) => other.sparse.get(k)?.key === v.key);
    }
    return super.equals(other);
  }
  withArgs(args: readonly Expr[]): Expr {
    const keys = [...this.sparse.keys()];
    return this.newLike(new Map(keys.map((k, i) => [k, at(args, i)])), this.shape);
  }
  protected override computeKey(): string {
    return `${this.name}[${this.shape.join(',')}](${[...this.sparse].map(([k, v]) => `${k}:${v.key}`).join(',')})`;
  }
}

/** SymPy ImmutableSparseNDimArray: an immutable sparse array. */
export class ImmutableSparseNDimArray extends SparseNDimArray {
  /** From nested lists, a flat list and a shape, a Map of nonzero elements and a shape, a Matrix or another array. */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('ImmutableSparseNDimArray', iterable, shape);
  }
  /** An array of zeros of the given shape. */
  static zeros(...shape: number[]): ImmutableSparseNDimArray {
    return new ImmutableSparseNDimArray(new Map(), shape);
  }
  asImmutable(): ImmutableSparseNDimArray {
    return this;
  }
  asMutable(): MutableSparseNDimArray {
    return new MutableSparseNDimArray(this);
  }
}

/** SymPy MutableSparseNDimArray: a sparse array changed in place with `set`. */
export class MutableSparseNDimArray extends SparseNDimArray {
  /** From nested lists, a flat list and a shape, a Map of nonzero elements and a shape, a Matrix or another array. */
  constructor(iterable: ArrayInput, shape?: ShapeInput) {
    super('MutableSparseNDimArray', iterable, shape);
  }
  /** An array of zeros of the given shape. */
  static zeros(...shape: number[]): MutableSparseNDimArray {
    return new MutableSparseNDimArray(new Map(), shape);
  }
  /** The key follows the current contents. */
  override get key(): string {
    return this.computeKey();
  }
  /**
   * SymPy __setitem__: `m.set(i, j, value)`; a single integer is a flat
   * position, and slices assign a sub-array. Zeros are not stored.
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
  asImmutable(): ImmutableSparseNDimArray {
    return new ImmutableSparseNDimArray(this);
  }
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

/** SymPy Flatten(iterable): iterates the elements of an array, Matrix or nested list in row-major order. */
export class Flatten implements Iterable<Expr> {
  readonly #source: NDimArray | Matrix;
  constructor(iterable: NDimArray | Matrix | readonly NestedArrayInput[]) {
    this.#source = iterable instanceof NDimArray || iterable instanceof Matrix ? iterable : new ImmutableDenseNDimArray(iterable);
  }
  *[Symbol.iterator](): Iterator<Expr> {
    yield* this.#source instanceof Matrix ? this.#source.data : this.#source.flatElements();
  }
  toString(): string {
    return `Flatten(${this.#source.toString()})`;
  }
}

/** The kind of an expression (SymPy `expr.kind`): ArrayKind for arrays, BooleanKind, NumberKind or UndefinedKind. */
export function kindOf(e: Expr): Kind {
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
  e.kind === 'Symbol' || e instanceof UndefFn || e instanceof Indexed || e instanceof Derivative || e instanceof NDimArray;

/**
 * SymPy derive_by_array(expr, dx): the derivative of an expression or
 * array by a symbol or by every element of an array; the result has shape
 * dx.shape + expr.shape.
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
