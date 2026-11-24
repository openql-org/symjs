// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Immutable matrices with symbolic entries.
 */

import { at, defined, first } from '../core/guard';
import { NonInvertibleMatrixError, NonSquareMatrixError, ShapeError } from '../core/errors';
import type { ComplexValue, EvalfOptions, ExprLike, NumericValues, Substitution } from '../core/nodes';
import { Expr, Float, Rational, S, Sym, impl, isNum } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols, subs, xreplace } from '../core/traverse';
import { asRealImag, atoms } from '../core/methods';
import { ExprMap } from '../core/exprmap';
import { replace, type Query, type Replacement } from '../core/match';
import type { Truth } from '../core/truth';
import { toTruth, truthAnd } from '../core/truth';
import { isIntegerQ, isNonNegative, isPositive, isZero } from '../core/assumptions';
import { sympifyMethod } from '../core/sympify';
import { conjugate, fn } from '../functions/elementary/elementary';
import { evalf, lambdify, toComplex } from '../numeric/evalf';
import { roots } from '../polys/poly';
import { latex } from '../printing/latex';
import { str } from '../printing/str';
import { expandMul as expand } from '../simplify/expand';

/**
 * SymPy simplify, late-bound: the matrices entry loads it, and modules that
 * only use matrices of numbers (number fields, Lie algebras, ciphers) do not
 * bring the simplification engine with them.
 */
const simplify = (e: Expr): Expr => impl.simplify(e);

/** A position (row, column) of a matrix. */
export type MatrixPosition = readonly [number, number];

/** SymPy `value == 0` for an entry (structural: an exact or floating zero). */
const isZeroEntry = (v: Expr): boolean => (v instanceof Rational || v instanceof Float) && v.isZero;
const isZeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;
/** The value of an integer Rational or integer-valued Float; undefined for other expressions. */
const integerValue = (e: Expr): number | undefined => {
  if (e instanceof Rational) return e.q === 1n ? Number(e.p) : undefined;
  return e instanceof Float && Number.isInteger(e.toNumber()) ? e.toNumber() : undefined;
};
const isIndexList = (perm: readonly (readonly [number, number])[] | readonly number[]): perm is readonly number[] => typeof perm[0] === 'number';
const range = (a: number, b: number): number[] => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);

/**
 * Selects the result constructor of a mixed matrix operation by comparing coercion priorities.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The constructor with higher priority, choosing the second on a tie.
 * @throws TypeError when the operands do not specify compatible matrix classes.
 * @see SymPy `sympy.matrices.matrixbase.classof`
 * @example
 * ```ts
 * import { ImmutableMatrix, MutableDenseMatrix, classof } from '@symjs/symjs';
 *
 * const M = MutableDenseMatrix.of([[1, 2], [3, 4]]);
 * classof(M, ImmutableMatrix(M)) === ImmutableMatrix(M).constructor; // => True
 * ```
 */
export function classof(a: { readonly classPriority: number }, b: { readonly classPriority: number }): Function {
  if (typeof a.classPriority !== 'number' || typeof b.classPriority !== 'number') throw new TypeError('Incompatible matrix classes');
  return a.classPriority > b.classPriority ? a.constructor : b.constructor;
}

/**
 * A dense rectangular matrix of expressions, indexed by zero-based row and column.
 * @see SymPy `sympy.matrices.dense.MutableDenseMatrix`
 * @example
 * ```ts
 * import { Matrix } from '@symjs/symjs';
 *
 * const m = Matrix.of([[1, 2], [3, 4]]);
 * m.det(); // => -2
 * m.inv(); // => Matrix([
 * //   [ -2,    1],
 * //   [3/2, -1/2]])
 * m.mul(m).row(0); // => Matrix([[7, 10]])
 * ```
 */
export class Matrix {
  /**
   * Gets the priority for choosing the result class in mixed matrix operations.
   * @returns The priority for choosing the result class in mixed matrix operations.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix._class_priority`
   */
  get classPriority(): number { return 8; }

  #rows: number;
  #cols: number;
  /** Row-major entries. */
  readonly data: readonly Expr[];

  protected constructor(rows: number, cols: number, data: readonly Expr[]) {
    if (!Number.isSafeInteger(rows) || !Number.isSafeInteger(cols) || rows < 0 || cols < 0) throw new RangeError('Matrix dimensions must be nonnegative integers');
    if (data.length !== rows * cols) throw new RangeError('Matrix data does not match its dimensions');
    this.#rows = rows;
    this.#cols = cols;
    this.data = data;
  }

  /**
   * Union of the free symbols of all entries.
   * @returns The set of distinct free symbols that occur in the entries.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.free_symbols`
   */
  freeSymbols(): Set<Expr> {
    return new Set(new Map(this.data.flatMap((e) => [...freeSymbols(e)].map((s) => [s.key, s] as const))).values());
  }

  /**
   * The number of rows.
   * @returns The row count.
   */
  get rows(): number {
    return this.#rows;
  }
  /**
   * The number of columns.
   * @returns The column count.
   */
  get cols(): number {
    return this.#cols;
  }
  /** A new shape for the entries (the in-place operations of the mutable matrix). */
  protected reshapeInPlace(rows: number, cols: number): void {
    this.#rows = rows;
    this.#cols = cols;
  }

  // ---- construction --------------------------------------------------------

  /**
   * Builds a dense matrix from rows of entries.
   * @param rows - The rows of entries.
   * @returns The resulting matrix.
   * @throws RangeError when the rows have different lengths.
   */
  static of(rows: readonly (readonly (ExprLike | Matrix)[])[]): Matrix {
    const data: Expr[] = [];
    for (const row of rows) {
      for (const x of row) {
        // SymPy Matrix([[A, B], [C, D]]) of matrices joins the blocks
        if (x instanceof Matrix) return Matrix.ofBlocks(rows);
        data.push(sympify(x));
      }
    }
    const r = rows.length;
    const c = rows[0]?.length ?? 0;
    for (const row of rows) if (row.length !== c) throw new RangeError('Matrix.of: ragged rows');
    return new Matrix(r, c, data);
  }

  /** Join rows of blocks (matrices, or scalars as 1x1 blocks); `rows` holds at least one matrix. */
  private static ofBlocks(rows: readonly (readonly (ExprLike | Matrix)[])[]): Matrix {
    const block = (x: ExprLike | Matrix): Matrix => (x instanceof Matrix ? x : new Matrix(1, 1, [sympify(x)]));
    const bands = rows.map((row) => {
      const [left, ...rest] = row.map(block);
      return left ? left.hstack(...rest) : new Matrix(0, 0, []);
    });
    return first(bands).vstack(...bands.slice(1));
  }

  /**
   * Build from a generator f(i, j).
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @param f - The function to apply to the entries.
   * @returns The resulting matrix.
   * @throws RangeError when a dimension is negative or nonintegral.
   */
  static fromFunction(rows: number, cols: number, f: (i: number, j: number) => ExprLike): Matrix {
    if (!Number.isSafeInteger(rows) || !Number.isSafeInteger(cols) || rows < 0 || cols < 0) throw new RangeError('Matrix dimensions must be nonnegative integers');
    const data: Expr[] = [];
    for (let i = 0; i < rows; i++) for (let j = 0; j < cols; j++) data.push(sympify(f(i, j)));
    return new Matrix(rows, cols, data);
  }

  /**
   * Returns a matrix of zeros.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @returns A matrix of zeros.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.zeros`
   */
  static zeros(rows: number, cols = rows): Matrix {
    return new Matrix(rows, cols, Array.from({ length: rows * cols }, () => S.Zero));
  }

  /**
   * A matrix of ones (SymPy Matrix.ones(rows, cols)).
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.ones`
   */
  static ones(rows: number, cols = rows): Matrix {
    return new Matrix(rows, cols, Array.from({ length: rows * cols }, () => S.One));
  }

  /**
   * A matrix from its entries by position; the other entries are zero.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @param dok - The map from row and column index pairs to nonzero entries.
   * @returns A matrix from its entries by position.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.from_dok`
   */
  static fromDok(rows: number, cols: number, dok: Iterable<readonly [MatrixPosition, ExprLike]>): Matrix {
    const data: Expr[] = Array.from({ length: rows * cols }, () => S.Zero);
    for (const [[i, j], v] of dok) data[i * cols + j] = sympify(v);
    return new Matrix(rows, cols, data);
  }

  /**
   * Returns an identity matrix.
   * @param n - The order of the square matrix.
   * @returns An identity matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.eye`
   */
  static eye(n: number): Matrix {
    return Matrix.fromFunction(n, n, (i, j) => (i === j ? 1 : 0));
  }

  /**
   * Returns a matrix with the specified diagonal.
   * @param entries - The matrix entries in row-major order.
   * @returns A matrix with the specified diagonal.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.diag`
   */
  static diag(...entries: ExprLike[]): Matrix {
    const d = entries.map(sympify);
    return Matrix.fromFunction(d.length, d.length, (i, j) => (i === j ? at(d, i) : 0));
  }

  /**
   * Column vector.
   * @param entries - The matrix entries in row-major order.
   * @returns The resulting matrix.
   */
  static col(...entries: ExprLike[]): Matrix {
    return Matrix.of(entries.map((e) => [e]));
  }

  /**
   * Row vector.
   * @param entries - The matrix entries in row-major order.
   * @returns The resulting matrix.
   */
  static row(...entries: ExprLike[]): Matrix {
    return Matrix.of([entries]);
  }

  /**
   * Kronecker (tensor) product of several matrices, left to right.
   * @param ms - The matrices to combine by Kronecker product.
   * @returns The resulting matrix.
   */
  static kron(...ms: Matrix[]): Matrix {
    if (ms.length === 0) return Matrix.eye(1);
    return ms.slice(1).reduce((acc, m) => acc.kron(m), first(ms));
  }

  // ---- access ----------------------------------------------------------------

  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.shape`
   */
  get shape(): [number, number] {
    return [this.rows, this.cols];
  }
  /**
   * Tests whether the row and column counts agree.
   * @returns Whether the matrix is square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_square`
   */
  get isSquare(): boolean {
    return this.rows === this.cols;
  }

  /**
   * Whether this is a square identity matrix, using structural entry equality.
   * @returns Whether the matrix is identity.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_Identity`
   */
  get isIdentity(): boolean {
    return this.isSquare && this.data.every((e, k) => e.key === (Math.floor(k / this.cols) === k % this.cols ? S.One.key : S.Zero.key));
  }

  /**
   * Whether every entry is zero, with undecidable entries kept unknown.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_zero_matrix`
   */
  get isZeroMatrix(): Truth {
    return truthAnd(...this.data.map((e) => toTruth(isZero(e))));
  }

  /**
   * Checks if the matrix is in the lower-Hessenberg form.
   * @returns Whether the matrix is lower hessenberg.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_lower_hessenberg`
   */
  get isLowerHessenberg(): boolean {
    return this.data.every((e, k) => k % this.cols <= Math.floor(k / this.cols) + 1 || isZeroEntry(e));
  }

  /**
   * Checks if the matrix is the upper-Hessenberg form.
   * @returns Whether the matrix is upper hessenberg.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_upper_hessenberg`
   */
  get isUpperHessenberg(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) <= k % this.cols + 1 || isZeroEntry(e));
  }

  /**
   * Conjugates each entry of the matrix.
   * @returns The matrix of complex conjugates.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.C`
   */
  get C(): Matrix {
    return this.conjugate();
  }

  /**
   * Forms the Dirac conjugate of the matrix.
   * @returns The conjugate transpose multiplied by the Dirac gamma-zero matrix.
   * @throws ShapeError when the matrix has a row count other than four.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.D`
   */
  get D(): Matrix {
    if (this.rows !== 4) throw new ShapeError('Dirac conjugation requires four rows');
    return this.H.mul(Matrix.diag(1, 1, -1, -1));
  }

  /**
   * Selects the matrix entry at the given row and column.
   * @param i - The row or vector position.
   * @param j - The zero-based column index.
   * @returns The resulting symbolic expression.
   * @throws RangeError when an index is out of bounds.
   * @see SymPy `sympy.matrices.matrixbase.MatrixBase.__getitem__`
   */
  get(i: number, j: number): Expr {
    if (!Number.isInteger(i) || !Number.isInteger(j) || i < 0 || i >= this.rows || j < 0 || j >= this.cols) throw new RangeError(`Matrix index (${i}, ${j}) out of range`);
    return at(this.data, i * this.cols + j);
  }

  /**
   * Return a copy with entry (i, j) replaced.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param v - The replacement entry.
   * @returns A copy with entry (i, j) replaced.
   */
  with(i: number, j: number, v: ExprLike): Matrix {
    this.get(i, j);
    const data = [...this.data];
    data[i * this.cols + j] = sympify(v);
    return new Matrix(this.rows, this.cols, data);
  }

  /**
   * Elementary row selector.
   * @param i - The zero-based row index.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row`
   */
  row(i: number): Matrix {
    return Matrix.fromFunction(1, this.cols, (_, j) => this.get(i, j));
  }
  /**
   * Elementary column selector.
   * @param j - The zero-based column index.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.col`
   */
  col(j: number): Matrix {
    return Matrix.fromFunction(this.rows, 1, (i) => this.get(i, j));
  }

  /**
   * Sub-matrix of the given rows and columns.
   * @param rows - The row selector.
   * @param cols - The column selector.
   * @returns The resulting matrix.
   */
  slice(rows: readonly number[], cols: readonly number[]): Matrix {
    return Matrix.fromFunction(rows.length, cols.length, (i, j) => this.get(at(rows, i), at(cols, j)));
  }

  /**
   * Deletes the selected row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.matrixbase.MatrixBase.minor_submatrix`
   */
  minor(i: number, j: number): Matrix {
    this.get(i, j);
    const rs = [...Array(this.rows).keys()].filter((r) => r !== i);
    const cs = [...Array(this.cols).keys()].filter((c) => c !== j);
    return this.slice(rs, cs);
  }

  /**
   * Copies the matrix entries into nested row arrays.
   * @returns The entries grouped by row.
   * @see SymPy `sympy.matrices.matrixbase.MatrixBase.tolist`
   */
  toArray(): Expr[][] {
    return Array.from({ length: this.rows }, (_, i) => Array.from({ length: this.cols }, (_, j) => this.get(i, j)));
  }

  // ---- elementwise -------------------------------------------------------------

  /**
   * Builds a new matrix by applying a function to each entry and its indices.
   * @param f - The function to apply to the entries.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.matrixbase.MatrixBase.applyfunc`
   */
  map(f: (e: Expr, i: number, j: number) => ExprLike): Matrix {
    return Matrix.fromFunction(this.rows, this.cols, (i, j) => f(this.get(i, j), i, j));
  }

  private zip(o: Matrix, f: (a: Expr, b: Expr) => Expr, op: string): Matrix {
    if (this.rows !== o.rows || this.cols !== o.cols) {
      throw new ShapeError(`Matrix ${op}: shape mismatch ${this.rows}x${this.cols} vs ${o.rows}x${o.cols}`);
    }
    return new Matrix(this.rows, this.cols, this.data.map((a, k) => f(a, at(o.data, k))));
  }

  /**
   * Adds the corresponding entries of two matrices.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.add`
   */
  add(o: Matrix): Matrix {
    return this.zip(o, (a, b) => add(a, b), 'add');
  }
  /**
   * Subtracts the other operand.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.__sub__`
   */
  sub(o: Matrix): Matrix {
    return this.zip(o, (a, b) => add(a, mul(-1, b)), 'sub');
  }
  /**
   * Negates every entry.
   * @returns The resulting matrix.
   */
  neg(): Matrix {
    return this.map((e) => mul(-1, e));
  }
  /**
   * Scalar multiplication.
   * @param k - The diagonal offset, positive above the main diagonal.
   * @returns The resulting matrix.
   */
  scale(k: ExprLike): Matrix {
    const s = sympify(k);
    return this.map((e) => mul(s, e));
  }

  /**
   * Multiplies this matrix by a matrix or scalar on the right.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.__mul__`
   */
  mul(o: Matrix | ExprLike): Matrix {
    return this.product(o, (e) => e);
  }

  /** The product with each entry passed through `simp`. */
  private product(o: Matrix | ExprLike, simp: (e: Expr) => Expr): Matrix {
    if (!(o instanceof Matrix)) return this.scale(o);
    if (this.cols !== o.rows) throw new ShapeError(`Matrix size mismatch: (${this.rows}, ${this.cols}) * (${o.rows}, ${o.cols}).`);
    return Matrix.fromFunction(this.rows, o.cols, (i, j) => {
      const terms: Expr[] = [];
      for (let k = 0; k < this.cols; k++) {
        const a = this.get(i, k);
        const b = o.get(k, j);
        terms.push(mul(a, b));
      }
      return simp(add(...terms));
    });
  }

  /**
   * Matrix powers by repeated squaring for integers and confluent polynomial interpolation
   * for other exponents. Repeated eigenvalues use the same derivatives as Jordan block powers.
   * @param n - The order of the square matrix.
   * @returns The resulting matrix.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.pow`
   */
  pow(n: number | ExprLike): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('Matrix pow: matrix must be square');
    const k = typeof n === 'number' && Number.isInteger(n) ? n : integerValue(sympify(n));
    if (k === undefined) {
      const exp = sympify(n);
      if (this.isDiagonal()) return Matrix.fromFunction(this.rows, this.cols, (i, j) => (i === j ? pow(this.get(i, i), exp) : S.Zero));
      if (this.rows === 2 && this.freeSymbols().size > 0) {
        const [a, b, c, d] = [this.get(0, 0), this.get(0, 1), this.get(1, 0), this.get(1, 1)];
        const trace = add(a, d), gap = add(a, mul(-1, d));
        const disc = add(pow(trace, 2), mul(-4, a, d), mul(4, b, c));
        const radical = sqrt(expand(disc));
        if (!isZeroE(radical) && !isZeroE(b) && !isZeroE(c) && !isZeroE(this.det())) {
          // Columns of P are eigenvectors [b/(lambda - a), 1].
          const denominator = expand(mul(radical, gap)).add(expand(disc));
          const twiceBC = mul(2, b, c);
          const P = Matrix.of([[mul(-2, b, pow(add(gap, radical), -1)), mul(-2, b, pow(add(gap, mul(-1, radical)), -1))], [1, 1]]);
          const inverse = Matrix.of([[mul(-1, c, pow(radical, -1)), mul(add(denominator, mul(-1, twiceBC)), pow(denominator, -1))],
            [mul(c, pow(radical, -1)), mul(twiceBC, pow(denominator, -1))]]);
          const center = add(mul(S.Half, a), mul(S.Half, d)), offset = mul(S.Half, sqrt(disc));
          return P.mul(Matrix.diag(pow(add(center, mul(-1, offset)), exp), pow(add(center, offset), exp))).mul(inverse);
        }
      }
      return this.interpolatedPower(exp);
    }
    if (k < 0) return this.inv().pow(-k);
    // SymPy MatrixBase.pow: a diagonal or 1x1 matrix is raised entrywise; otherwise the products
    // are simplified as they go (dotprodsimp), here by expanding each entry
    if (k === 0) return Matrix.eye(this.rows);
    if (k === 1) return this;
    if (this.isDiagonal()) return this.map((x) => pow(x, k));
    let result: Matrix = this;
    for (const bit of k.toString(2).slice(1)) {
      result = result.product(result, expand);
      if (bit === '1') result = result.product(this, expand);
    }
    return result;
  }

  /** Hermite interpolation of z**exp on the eigenvalues, including their multiplicities. */
  private interpolatedPower(exp: Expr): Matrix {
    let eigenvalues = this.eigenvals().sort((a, b) => a.key.localeCompare(b.key));
    if (eigenvalues.length !== this.rows) throw new RangeError('Matrix pow: could not determine all eigenvalues');
    const identity = Matrix.eye(this.rows);
    const distinct = [...new Map(eigenvalues.map((v) => [v.key, v])).values()];
    if (distinct.length < eigenvalues.length && distinct.reduce((m, v) => m.mul(this.sub(identity.scale(v))).map(expand), identity).isZero) eigenvalues = distinct;
    let result = Matrix.zeros(this.rows);
    let basis = identity;
    let divided: Expr[] = [];
    for (let order = 0; order < eigenvalues.length; order++) {
      const next: Expr[] = [];
      for (let i = 0; i < eigenvalues.length - order; i++) {
        const lo = at(eigenvalues, i);
        const hi = at(eigenvalues, i + order);
        let coefficient: Expr;
        if (lo.key === hi.key) {
          if (isZeroE(lo)) {
            if (!(isPositive(exp) === true || (isIntegerQ(exp) === true && isNonNegative(exp) === true))) {
              throw new NonInvertibleMatrixError('Non-invertible matrix requires a nonnegative exponent');
            }
            if (order > 0 && isIntegerQ(exp) !== true) throw new NonInvertibleMatrixError('Non-invertible Jordan block requires a nonnegative integer exponent');
            coefficient = isIntegerQ(exp) === true ? fn('KroneckerDelta', [order, exp]) : S.Zero;
          } else {
            let binomial: Expr = S.One;
            for (let j = 0; j < order; j++) binomial = mul(binomial, add(exp, -j), Rational.of(1, j + 1));
            coefficient = mul(pow(lo, add(exp, -order)), binomial);
          }
        } else coefficient = mul(add(at(divided, i + 1), mul(-1, at(divided, i))), pow(add(hi, mul(-1, lo)), -1));
        next.push(coefficient);
      }
      divided = next;
      result = result.add(basis.scale(first(divided)));
      basis = basis.mul(this.sub(identity.scale(at(eigenvalues, order)))).map(expand);
    }
    return result.map(simplify);
  }

  /**
   * Kronecker (tensor) product this ⊗ o.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   */
  kron(o: Matrix): Matrix {
    return Matrix.fromFunction(this.rows * o.rows, this.cols * o.cols, (i, j) =>
      mul(this.get(Math.floor(i / o.rows), Math.floor(j / o.cols)), o.get(i % o.rows, j % o.cols)),
    );
  }

  /**
   * Commutator [A, B] = AB - BA.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   */
  commutator(o: Matrix): Matrix {
    return this.mul(o).sub(o.mul(this));
  }

  /**
   * Anticommutator {A, B} = AB + BA.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   */
  anticommutator(o: Matrix): Matrix {
    return this.mul(o).add(o.mul(this));
  }

  /**
   * Join a block on the right. A matrix with no columns accepts the block's row count.
   * @param other - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_join`
   */
  rowJoin(other: Matrix): Matrix {
    return this.cols === 0 ? other : this.hstack(other);
  }

  /**
   * Join a block below. A matrix with no rows accepts the block's column count.
   * @param other - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.col_join`
   */
  colJoin(other: Matrix): Matrix {
    return this.rows === 0 ? other : this.vstack(other);
  }

  /**
   * Stack horizontally.
   * @param others - The additional operands in order.
   * @returns The resulting matrix.
   * @throws RangeError when the row counts differ.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.hstack`
   */
  hstack(...others: Matrix[]): Matrix {
    const all = [this, ...others];
    if (all.some((m) => m.rows !== this.rows)) throw new RangeError('hstack: row count mismatch');
    return Matrix.of(Array.from({ length: this.rows }, (_, i) => all.flatMap((m) => m.row(i).data)));
  }

  /**
   * Stack vertically.
   * @param others - The additional operands in order.
   * @returns The resulting matrix.
   * @throws RangeError when the column counts differ.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.vstack`
   */
  vstack(...others: Matrix[]): Matrix {
    const all = [this, ...others];
    if (all.some((m) => m.cols !== this.cols)) throw new RangeError('vstack: column count mismatch');
    return Matrix.of(all.flatMap((m) => m.toArray()));
  }

  // ---- linear algebra -------------------------------------------------------------

  /**
   * Returns the transpose of the matrix.
   * @returns The transpose of the matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.transpose`
   */
  transpose(): Matrix {
    return Matrix.fromFunction(this.cols, this.rows, (i, j) => this.get(j, i));
  }
  /**
   * Matrix transposition.
   * @returns The transposed matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.T`
   */
  get T(): Matrix {
    return this.transpose();
  }

  /**
   * Return the by-element conjugation.
   * @returns The by-element conjugation.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.conjugate`
   */
  conjugate(): Matrix {
    return this.map((e) => conjugate(e));
  }

  /**
   * Conjugate transpose (Hermitian adjoint, dagger).
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.adjoint`
   */
  adjoint(): Matrix {
    return this.transpose().conjugate();
  }
  /**
   * Return Hermite conjugate.
   * @returns The conjugate transpose.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.H`
   */
  get H(): Matrix {
    return this.adjoint();
  }
  /**
   * Alias of adjoint().
   * @returns The resulting matrix.
   */
  dagger(): Matrix {
    return this.adjoint();
  }

  /**
   * Returns the trace of a square matrix i.e.
   * @returns The trace of a square matrix i.e.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.trace`
   */
  trace(): Expr {
    if (!this.isSquare) throw new NonSquareMatrixError('trace: matrix must be square');
    return add(...Array.from({ length: this.rows }, (_, i) => this.get(i, i)));
  }

  /**
   * Coefficients [1, c1, ..., cn] of det(λI - A) = λ^n + c1 λ^(n-1) + ... + cn,
   * computed with the division-free Berkowitz algorithm.
   * @returns The resulting expressions in order.
   * @throws NonSquareMatrixError when the matrix is not square.
   */
  charpolyCoeffs(): Expr[] {
    if (!this.isSquare) throw new NonSquareMatrixError('charpoly: matrix must be square');
    return berkowitz(this).map(simplify);
  }

  /**
   * Characteristic polynomial det(λI - A) as an expression in `lambda`.
   * @param lambda - The indeterminate of the characteristic polynomial.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.charpoly`
   */
  charpoly(lambda: Sym): Expr {
    const cs = this.charpolyCoeffs();
    const n = cs.length - 1;
    return expand(add(...cs.map((c, k) => mul(c, pow(lambda, n - k)))));
  }

  /**
   * Computes the determinant of a matrix if `M` is a concrete matrix object otherwise return an expressions `Determinant(M)` if `M` is a `MatrixSymbol` or other expression.
   * @returns The resulting symbolic expression.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.det`
   */
  det(): Expr {
    if (!this.isSquare) throw new NonSquareMatrixError('det: matrix must be square');
    const n = this.rows;
    if (n === 0) return S.One;
    if (n === 1) return this.get(0, 0);
    if (n === 2) return expand(add(mul(this.get(0, 0), this.get(1, 1)), mul(-1, this.get(0, 1), this.get(1, 0))));
    const cs = berkowitz(this);
    return expand(n % 2 === 0 ? at(cs, n) : mul(-1, at(cs, n)));
  }

  /**
   * Matrix of cofactors.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.cofactorMatrix`
   */
  cofactorMatrix(): Matrix {
    return Matrix.fromFunction(this.rows, this.cols, (i, j) => {
      const m = this.minor(i, j).det();
      return (i + j) % 2 === 0 ? m : mul(-1, m);
    });
  }

  /**
   * Adjugate (classical adjoint): transpose of the cofactor matrix.
   * @returns The resulting matrix.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.adjugate`
   */
  adjugate(): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('adjugate: matrix must be square');
    if (this.rows === 1) return Matrix.of([[1]]);
    return this.cofactorMatrix().transpose();
  }

  /**
   * Inverse via adjugate / determinant. The determinant is simplified first.
   * @returns The resulting matrix.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @throws NonInvertibleMatrixError when the matrix is singular.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.inv`
   */
  inv(): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('A Matrix must be square to invert.');
    const d = simplify(this.det());
    if (d instanceof Rational && d.isZero) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
    const invDet = pow(d, -1);
    const inverse = this.adjugate().scale(invDet);
    return d.isNumber ? inverse.expand() : inverse;
  }

  /**
   * Eigenvalues (with multiplicity) as roots of the characteristic polynomial.
   * @param simplifyRoots - Whether to simplify the eigenvalues.
   * @param errorWhenIncomplete - Whether to raise an error if some roots are missing.
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.eigenvals`
   */
  eigenvals(simplifyRoots = true, errorWhenIncomplete = true): Expr[] {
    // SymPy _eigenvals: a triangular matrix has its diagonal entries as eigenvalues, in order
    const n = this.rows;
    const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
    const below = this.data.filter((_, k) => Math.floor(k / this.cols) > k % this.cols);
    const above = this.data.filter((_, k) => Math.floor(k / this.cols) < k % this.cols);
    if (this.isSquare && (below.every(isZero) || above.every(isZero))) return Array.from({ length: n }, (_, i) => this.get(i, i));
    const lam = new Sym('lambda_');
    const values = roots(this.charpoly(lam), lam, { skipQuintic: !errorWhenIncomplete });
    return simplifyRoots ? values.map(simplify) : values;
  }

  // ---- transformation --------------------------------------------------------------

  /**
   * Return a new matrix with subs applied to each entry.
   * @param s - The input sequence.
   * @param from - The index where the selected segment starts.
   * @param to - The exclusive end of the selected segment.
   * @returns A new matrix with subs applied to each entry.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.subs`
   */
  subs(s: Substitution): Matrix;
  subs(from: Expr | string, to: ExprLike): Matrix;
  subs(a: Substitution | Expr | string, b?: ExprLike): Matrix {
    const spec: Substitution = a instanceof Expr || typeof a === 'string' ? [[typeof a === 'string' ? new Sym(a) : a, defined(b, 'subs replacement')]] : a;
    return this.map((e) => subs(e, spec));
  }
  /**
   * Apply core.function.expand to each entry of the matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.expand`
   */
  expand(): Matrix {
    return this.map(expand);
  }
  /**
   * Simplifies each entry of the matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.simplify`
   */
  simplify(): Matrix {
    return this.map((e) => simplify(e));
  }
  /**
   * Apply evalf() to each element of self.
   * @param n - The decimal precision.
   * @param opts - Numerical evaluation settings, including substitutions and precision controls.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.evalf`
   */
  evalf(n?: number | NumericValues, opts?: EvalfOptions): Matrix {
    return this.map((e) => evalf(e, n, opts));
  }
  /**
   * Numeric evaluation to nested arrays of complex values.
   * @param values - The numeric substitutions for the free symbols.
   * @returns The complex numeric values, grouped by matrix row.
   */
  toComplex(values?: NumericValues): ComplexValue[][] {
    return this.toArray().map((row) => row.map((e) => toComplex(e, values)));
  }
  /**
   * Compile into a function of the given parameters returning complex nested arrays.
   * @param params - The variables in the order expected by the numerical function.
   * @returns A callable that evaluates the matrix entries at the supplied argument values.
   */
  lambdify(params: readonly Sym[]): (...args: (number | ComplexValue)[]) => ComplexValue[][] {
    const fs = this.toArray().map((row) => row.map((e) => lambdify(e, params)));
    return (...args) => fs.map((row) => row.map((f) => f(...args)));
  }

  // ---- predicates ----------------------------------------------------------------

  /**
   * Structural equality of all entries.
   * @param o - The other matrix operand.
   * @returns The result of the comparison.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.equals`
   */
  equals(o: Matrix): boolean {
    return this.rows === o.rows && this.cols === o.cols && this.data.every((e, k) => e.key === at(o.data, k).key);
  }
  /**
   * The same class (mutable or immutable) and the
   * same entries; numbers are compared with `approx` when given.
   * @param o - The other matrix operand.
   * @param approx - An optional comparison for approximate numbers.
   * @returns Whether the matrix is same.
   */
  isSame(o: unknown, approx?: (a: Expr, b: Expr) => boolean): boolean {
    if (!(o instanceof Matrix) || o.constructor !== this.constructor || this.rows !== o.rows || this.cols !== o.cols) return false;
    return this.data.every((e, k) => {
      const b = at(o.data, k);
      return approx && e.isNumber && b.isNumber ? approx(e, b) : e.key === b.key;
    });
  }
  /**
   * Equality after simplifying the difference.
   * @param o - The other matrix operand.
   * @returns Whether all corresponding entries agree after simplification.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.equals`
   */
  equalsSimplified(o: Matrix): boolean {
    return this.rows === o.rows && this.cols === o.cols && this.sub(o).simplify().isZero;
  }
  /**
   * Tests whether every entry is zero.
   * @returns Whether the matrix is zero.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_zero`
   */
  get isZero(): boolean {
    return this.data.every((e) => e instanceof Rational && e.isZero);
  }
  /**
   * Checks if the matrix is Hermitian.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_hermitian`
   */
  isHermitian(): Truth {
    if (!this.isSquare) return false;
    return truthAnd(...this.sub(this.adjoint()).simplify().data.map((e) => {
      const zero = isZero(e);
      if (zero !== undefined) return zero;
      const [re, im] = asRealImag(e);
      return truthAnd(toTruth(isZero(re)), toTruth(isZero(im)));
    }));
  }
  /**
   * Tests whether the conjugate transpose is the inverse.
   * @returns Whether the matrix is unitary.
   */
  isUnitary(): boolean {
    return this.isSquare && this.mul(this.adjoint()).equalsSimplified(Matrix.eye(this.rows));
  }

  // ---- structure (SymPy MatrixBase methods) ----------------------------------------

  /**
   * A copy.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.copy`
   */
  copy(): Matrix {
    return new Matrix(this.rows, this.cols, [...this.data]);
  }
  /**
   * Returns the entries as nested arrays.
   * @returns The entries as nested arrays.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.tolist`
   */
  tolist(): Expr[][] {
    return this.toArray();
  }
  /**
   * The entries in row-major order.
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.flat`
   */
  flat(): Expr[] {
    return [...this.data];
  }
  /**
   * The nonzero entries in row-major order.
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.values`
   */
  values(): Expr[] {
    return this.data.filter((e) => !isZeroEntry(e));
  }
  /**
   * Returns the nonzero entries by position.
   * @returns The nonzero entries by position.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.todok`
   */
  todok(): Map<MatrixPosition, Expr> {
    const out = new Map<MatrixPosition, Expr>();
    this.data.forEach((v, k) => {
      if (!isZeroEntry(v)) out.set([Math.floor(k / this.cols), k % this.cols], v);
    });
    return out;
  }
  /**
   * Returns the nonzero entries as row -> column -> value.
   * @returns The nonzero entries as row -> column -> value.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.todod`
   */
  todod(): Map<number, Map<number, Expr>> {
    const out = new Map<number, Map<number, Expr>>();
    for (const [[i, j], v] of this.todok()) {
      const row = out.get(i) ?? new Map<number, Expr>();
      row.set(j, v);
      out.set(i, row);
    }
    return out;
  }

  /**
   * The matrix without row i and column j (negative indices count from the end).
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.minor_submatrix`
   */
  minorSubmatrix(i: number, j: number): Matrix {
    return this.minor(i < 0 ? i + this.rows : i, j < 0 ? j + this.cols : j);
  }
  /**
   * Deletes the selected row and column to form a minor submatrix.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.matrixbase.MatrixBase.minor_submatrix`
   */
  minorMatrix(i: number, j: number): Matrix {
    return this.minorSubmatrix(i, j);
  }
  /**
   * The determinant of the minor submatrix.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The resulting symbolic expression.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.minorEntry`
   */
  minorEntry(i: number, j: number): Expr {
    if (!this.isSquare) throw new NonSquareMatrixError('minor: matrix must be square');
    return this.minorSubmatrix(i, j).det();
  }
  /**
   * Calculate the cofactor of an element.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.cofactor`
   */
  cofactor(i: number, j: number): Expr {
    const m = this.minorEntry(i, j);
    return (i + j) % 2 === 0 ? m : mul(-1, m);
  }

  /**
   * The entries on and above the k-th diagonal.
   * @param k - The diagonal offset, positive above the main diagonal.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.upper_triangular`
   */
  upperTriangular(k = 0): Matrix {
    return this.map((e, i, j) => (j - i >= k ? e : 0));
  }
  /**
   * The entries on and below the k-th diagonal.
   * @param k - The diagonal offset, positive above the main diagonal.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.lower_triangular`
   */
  lowerTriangular(k = 0): Matrix {
    return this.map((e, i, j) => (j - i <= k ? e : 0));
  }
  /**
   * The k-th diagonal as a row (k > 0 above the main diagonal).
   * @param k - The diagonal offset, positive above the main diagonal.
   * @returns The resulting matrix.
   * @throws RangeError when the diagonal offset is outside the matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.diagonal`
   */
  diagonal(k = 0): Matrix {
    if (k <= -this.rows || k >= this.cols) throw new RangeError(`The ${k} diagonal is out of range [${1 - this.rows}, ${this.cols - 1}]`);
    const out: Expr[] = [];
    for (let i = Math.max(0, -k); i < this.rows && i + k < this.cols; i++) out.push(this.get(i, i + k));
    return Matrix.row(...out);
  }
  /**
   * The submatrix of the given rows and
   * columns (negative indices count from the end; a list of booleans selects).
   * @param rows - The row selector.
   * @param cols - The column selector.
   * @returns The submatrix of the given rows and columns (negative indices count from the end; a list of booleans selects).
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.extract`
   */
  extract(rows: readonly (number | boolean)[], cols: readonly (number | boolean)[]): Matrix {
    const norm = (idx: readonly (number | boolean)[], n: number): number[] =>
      idx.every((v) => typeof v === 'boolean')
        ? idx.flatMap((v, i) => (v ? [i] : []))
        : idx.map((v) => (typeof v === 'boolean' ? Number(v) : v < 0 ? v + n : v));
    return this.slice(norm(rows, this.rows), norm(cols, this.cols));
  }
  /**
   * The entries in row-major order in a new shape.
   * @param r - The requested row count.
   * @param c - The requested column count.
   * @returns The resulting matrix.
   * @throws RangeError when the dimensions do not preserve the number of entries.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.reshape`
   */
  reshape(r: number, c: number): Matrix {
    if (r * c !== this.data.length) throw new RangeError(`Invalid reshape parameters ${r} ${c}`);
    return new Matrix(r, c, [...this.data]);
  }
  /**
   * Rotated by k quarter turns clockwise.
   * @param k - The signed number of quarter turns.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.rot90`
   */
  rot90(k = 1): Matrix {
    const t = ((k % 4) + 4) % 4;
    let r: Matrix = this;
    for (let i = 0; i < t; i++) {
      const R = r;
      r = Matrix.fromFunction(R.cols, R.rows, (a, b) => R.get(R.rows - 1 - b, a));
    }
    return r;
  }
  /**
   * The columns stacked into one column.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.vec`
   */
  vec(): Matrix {
    return this.transpose().reshape(this.data.length, 1);
  }
  /**
   * The entries on and below
   * the diagonal (strictly below without the diagonal), column by column.
   * @param opts - Set `diagonal` to retain diagonal entries and `checkSymmetry` to verify symmetry.
   * @returns The resulting matrix.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @throws RangeError when the matrix is not symmetric.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.vech`
   */
  vech(opts: { diagonal?: boolean; checkSymmetry?: boolean } = {}): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('vech: matrix must be square');
    if ((opts.checkSymmetry ?? true) && !this.isSymmetric()) throw new RangeError('The matrix is not symmetric.');
    const out: Expr[] = [];
    for (let j = 0; j < this.cols; j++) for (let i = (opts.diagonal ?? true) ? j : j + 1; i < this.rows; i++) out.push(this.get(i, j));
    return Matrix.col(...out);
  }
  /**
   * Other's rows inserted before row pos (a new matrix).
   * @param pos - The position at which to insert or interchange entries.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @throws TypeError when the insertion position is not an integer.
   * @throws ShapeError when the column counts differ.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_insert`
   */
  rowInsert(pos: number, o: Matrix): Matrix {
    if (!Number.isInteger(pos)) throw new TypeError('row insertion position must be an integer');
    if (this.rows === 0 && this.cols === 0) return o;
    if (o.cols !== this.cols) throw new ShapeError('The matrices have incompatible number of columns.');
    let p = pos < 0 ? pos + this.rows : pos;
    p = Math.min(Math.max(p, 0), this.rows);
    const rows = this.toArray();
    return Matrix.of([...rows.slice(0, p), ...o.toArray(), ...rows.slice(p)]);
  }
  /**
   * Other's columns inserted before column pos (a new matrix).
   * @param pos - The position at which to insert or interchange entries.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @throws ShapeError when the row counts differ.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.col_insert`
   */
  colInsert(pos: number, o: Matrix): Matrix {
    if (this.rows === 0 && this.cols === 0) return o;
    if (o.rows !== this.rows) throw new ShapeError('The matrices have incompatible number of rows.');
    return this.transpose().rowInsert(pos, o.transpose()).transpose();
  }
  /**
   * Rows (or
   * columns) permuted by a list of swaps, applied in order ('forward') or in
   * reverse ('backward'), or by an index list (row i <- row perm[i]; as in
   * SymPy, the direction does not apply to an index list).
   * @param perm - The permutation to apply.
   * @param opts - Select row or column `orientation` and forward or backward `direction`.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.permute`
   */
  permute(perm: readonly (readonly [number, number])[] | readonly number[], opts: { orientation?: 'rows' | 'cols'; direction?: 'forward' | 'backward' } = {}): Matrix {
    const cols = opts.orientation === 'cols';
    const backward = opts.direction === 'backward';
    const n = cols ? this.cols : this.rows;
    const order = range(0, n);
    if (isIndexList(perm)) {
      perm.slice(0, n).forEach((v, i) => (order[i] = v));
    } else {
      const swaps = [...perm];
      if (backward) swaps.reverse();
      for (const [a, b] of swaps) [order[a], order[b]] = [at(order, b), at(order, a)];
    }
    return cols ? this.slice(range(0, this.rows), order) : this.slice(order, range(0, this.cols));
  }

  // ---- products ---------------------------------------------------------------------

  /**
   * The matrix product (a scalar scales).
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.multiply`
   */
  multiply(o: Matrix | ExprLike): Matrix {
    return this.mul(o);
  }
  /**
   * Other * this.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.rmultiply`
   */
  rmultiply(o: Matrix | ExprLike): Matrix {
    return o instanceof Matrix ? o.mul(this) : this.scale(o);
  }
  /**
   * The Hadamard product.
   * @param o - The other matrix operand.
   * @returns The resulting matrix.
   * @throws ShapeError when the matrix shapes differ.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.multiply_elementwise`
   */
  multiplyElementwise(o: Matrix): Matrix {
    if (this.rows !== o.rows || this.cols !== o.cols) throw new ShapeError(`Matrix shapes must agree (${this.rows}, ${this.cols}) != (${o.rows}, ${o.cols})`);
    return this.map((e, i, j) => mul(e, o.get(i, j)));
  }
  /**
   * The projection of this vector onto v.
   * @param v - The vector onto which to project.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.project`
   */
  project(v: Matrix): Matrix {
    const dot = (a: Matrix, b: Matrix): Expr => add(...a.data.map((e, k) => mul(e, at(b.data, k))));
    return v.scale(mul(dot(this, v), pow(dot(v, v), -1)));
  }
  /**
   * The skew-symmetric matrix of the cross product with this 3-vector.
   * @returns The resulting matrix.
   * @throws ShapeError when the matrix is not a three-entry column vector.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.hat`
   */
  hat(): Matrix {
    if (this.rows !== 3 || this.cols !== 1) throw new ShapeError(`Dimensions incorrect, expected (3, 1), got (${this.rows}, ${this.cols})`);
    const [x, y, z] = [this.get(0, 0), this.get(1, 0), this.get(2, 0)];
    return Matrix.of([
      [0, mul(-1, z), y],
      [z, 0, mul(-1, x)],
      [mul(-1, y), x, 0],
    ]);
  }
  /**
   * The 3-vector of a skew-symmetric 3x3 matrix (the inverse of hat).
   * @returns The resulting matrix.
   * @throws ShapeError when the matrix does not have shape three by three.
   * @throws RangeError when the matrix is not skew-symmetric.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.vee`
   */
  vee(): Matrix {
    if (this.rows !== 3 || this.cols !== 3) throw new ShapeError(`Dimensions incorrect, expected (3, 3), got (${this.rows}, ${this.cols})`);
    if (this.isAntiSymmetric() !== true) throw new RangeError('Matrix is not skew-symmetric');
    return Matrix.col(this.get(2, 1), this.get(0, 2), this.get(1, 0));
  }

  // ---- predicates on the entries --------------------------------------------------

  /**
   * Equal to its transpose (the differences simplified unless `simplify` is false).
   * @param simplifyEntries - Whether to simplify entries before comparing them.
   * @returns Whether the matrix is symmetric.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_symmetric`
   */
  isSymmetric(simplifyEntries = true): boolean {
    if (!this.isSquare) return false;
    for (let i = 0; i < this.rows; i++) for (let j = i + 1; j < this.cols; j++) {
      const a = this.get(i, j);
      const b = this.get(j, i);
      if (simplifyEntries ? !isZeroE(simplify(add(a, mul(-1, b)))) : !a.equals(b)) return false;
    }
    return true;
  }
  /**
   * Equal to minus its transpose;
   * 'unknown' when an unsimplified entry sum is not structurally zero.
   * @param simplifyEntries - Whether to simplify entries before comparing them.
   * @returns Whether the property holds, or `'unknown'` if undecidable.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_anti_symmetric`
   */
  isAntiSymmetric(simplifyEntries = true): Truth {
    if (!this.isSquare) return false;
    const sums = this.add(this.transpose()).data;
    if (simplifyEntries) return truthAnd(...sums.map((e) => toTruth(isZero(simplify(e)))));
    if (sums.every(isZeroE)) return true;
    return sums.some((e) => isNum(e) && !isZeroE(e)) ? false : 'unknown';
  }
  /**
   * The entries off the main diagonal are zero (rectangular matrices too).
   * @returns Whether the matrix is diagonal.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_diagonal`
   */
  isDiagonal(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) === k % this.cols || isZeroE(e));
  }
  /**
   * The entries below the main diagonal are zero.
   * @returns Whether the matrix is upper.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_upper`
   */
  isUpper(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) <= k % this.cols || isZeroE(e));
  }
  /**
   * The entries above the main diagonal are zero.
   * @returns Whether the matrix is lower.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_lower`
   */
  isLower(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) >= k % this.cols || isZeroE(e));
  }
  /**
   * Some power of the matrix is zero.
   * @returns Whether the matrix is nilpotent.
   * @throws NonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_nilpotent`
   */
  isNilpotent(): boolean {
    if (!this.isSquare) throw new NonSquareMatrixError('Nilpotency is valid only for square matrices');
    return this.pow(this.rows).data.every(isZeroE);
  }
  /**
   * Some entry contains a symbol.
   * @returns Whether the matrix is symbolic.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.is_symbolic`
   */
  isSymbolic(): boolean {
    return this.data.some((e) => freeSymbols(e).size > 0);
  }
  /**
   * Some entry contains one of the patterns.
   * @param patterns - The expressions to search for.
   * @returns Whether any entry contains one of the requested patterns.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.has`
   */
  has(...patterns: ExprLike[]): boolean {
    const ps = patterns.map((p) => sympify(p));
    return this.data.some((e) => ps.some((p) => e.has(p)));
  }
  /**
   * The atoms of the entries, optionally filtered by a predicate.
   * @param pred - Selects the expression atoms to collect.
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.atoms`
   */
  atoms(pred?: (a: Expr) => boolean): Expr[] {
    const out = new Map<string, Expr>();
    for (const e of this.data) for (const a of atoms(e, pred)) out.set(a.key, a);
    return [...out.values()];
  }

  // ---- entrywise operations (SymPy applies them to each entry) ---------------------

  /**
   * Alias of evalf.
   * @param n - The order of the square matrix.
   * @param opts - Numerical evaluation settings, including substitutions and precision controls.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.n`
   */
  n(n?: number | NumericValues, opts?: EvalfOptions): Matrix {
    return this.evalf(n, opts);
  }
  /**
   * Returns the matrices of the real and imaginary parts.
   * @returns The matrices of the real and imaginary parts.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.as_real_imag`
   */
  asRealImag(): [Matrix, Matrix] {
    const parts = this.data.map((e) => asRealImag(e));
    return [new Matrix(this.rows, this.cols, parts.map(([r]) => r)), new Matrix(this.rows, this.cols, parts.map(([, i]) => i))];
  }
  /**
   * Differentiates each entry with respect to the given variable.
   * @param x - The variable of differentiation, integration or substitution.
   * @param n - The order of the square matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.diff`
   */
  diff(x: Expr, n = 1): Matrix {
    return this.map((e) => e.diff(x, n));
  }
  /**
   * Integrates each entry with respect to the given variable.
   * @param x - The variable of differentiation, integration or substitution.
   * @param limits - The integration bounds, when a definite integral is required.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.integrate`
   */
  integrate(x: Sym, limits?: [ExprLike, ExprLike]): Matrix {
    return this.map((e) => e.integrate(x, limits));
  }
  /**
   * The limits of the entries.
   * @param z - The variable approaching the limit point.
   * @param z0 - The point approached by the variable.
   * @param dir - The side from which to approach the limit point.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.limit`
   */
  limit(z: Sym, z0: ExprLike, dir: '+' | '-' | '+-' = '+'): Matrix {
    return this.map((e) => e.limit(z, z0, dir));
  }
  /**
   * The entries with exact subtrees replaced.
   * @param rule - The mapping from subexpressions to replacements.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.xreplace`
   */
  xreplace(rule: Substitution): Matrix {
    return this.map((e) => xreplace(e, rule));
  }
  /**
   * Returns the entries with matching subexpressions replaced.
   * @param query - The pattern or predicate to match.
   * @param value - The value represented by this object.
   * @param opts - Set `map` to include the substitutions and `simultaneous` to control replacement order.
   * @returns The entries with matching subexpressions replaced.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.replace`
   */
  replace(query: Query, value: Replacement, opts: NonNullable<Parameters<typeof replace>[3]> & { map: true }): [Matrix, Map<Expr, Expr>];
  replace(query: Query, value: Replacement, opts?: Omit<NonNullable<Parameters<typeof replace>[3]>, 'map'>): Matrix;
  replace(query: Query, value: Replacement, opts: NonNullable<Parameters<typeof replace>[3]> = {}): Matrix | [Matrix, Map<Expr, Expr>] {
    const changes = new ExprMap<Expr>();
    const matrix = this.map((e) => {
      const result = replace(e, query, value, opts);
      if (result instanceof Expr) return result;
      for (const [from, to] of result[1]) changes.set(from, to);
      return result[0];
    });
    return opts.map ? [matrix, changes] : matrix;
  }

  // ---- printing ------------------------------------------------------------------

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    if (this.shape[0] === 0 || this.shape[1] === 0) return `Matrix(${this.shape[0]}, ${this.shape[1]}, [])`;
    return `Matrix([${this.toArray()
      .map((r) => `[${r.map(str).join(', ')}]`)
      .join(', ')}])`;
  }
  /**
   * LaTeX as SymPy latex(Matrix): a bracketed matrix environment, an array beyond 10 columns.
   * @returns The resulting text.
   */
  toLatex(): string {
    return latex(this);
  }
  [Symbol.for('nodejs.util.inspect.custom')](): string {
    return this.toString();
  }
  /** sympify of an (immutable) matrix is the matrix itself. */
  [sympifyMethod](): Matrix {
    return this;
  }
}

/** Berkowitz algorithm: returns [1, c1, ..., cn] for det(λI - M). */
function berkowitz(M: Matrix): Expr[] {
  const n = M.rows;
  if (n === 0) return [S.One];
  if (n === 1) return [S.One, mul(-1, M.get(0, 0))];
  const a = M.get(0, 0);
  const R = M.slice([0], [...Array(n - 1).keys()].map((k) => k + 1));
  const C = M.slice([...Array(n - 1).keys()].map((k) => k + 1), [0]);
  const A = M.minor(0, 0);
  // diags: [1, -a, -R C, -R A C, -R A^2 C, ...]
  const diags: Expr[] = [S.One, mul(-1, a)];
  let v = C;
  for (let k = 0; k < n - 1; k++) {
    diags.push(expand(mul(-1, R.mul(v).get(0, 0))));
    if (k < n - 2) v = A.mul(v).map(expand);
  }
  const sub = berkowitz(A); // length n
  // Toeplitz (n+1) x n lower-triangular times sub
  const out: Expr[] = [];
  for (let i = 0; i <= n; i++) {
    const terms: Expr[] = [];
    for (let j = 0; j < n; j++) if (j <= i) terms.push(mul(at(diags, i - j), at(sub, j)));
    out.push(expand(add(...terms)));
  }
  return out;
}
