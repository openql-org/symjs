// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Immutable matrices with symbolic entries.
 */

import { at, cast, defined, first } from '../core/guard';
import { NonInvertibleMatrixError, NonSquareMatrixError, ShapeError } from '../core/errors';
import type { ComplexValue, EvalfOptions, ExprLike, NumericValues, Substitution } from '../core/nodes';
import { Expr, Float, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols, subs, xreplace } from '../core/traverse';
import { asRealImag, atoms } from '../core/methods';
import { replace, type Query, type Replacement } from '../core/match';
import type { Truth } from '../core/truth';
import { sympifyMethod } from '../core/sympify';
import { conjugate } from '../functions/elementary/elementary';
import { evalf, lambdify, toComplex } from '../numeric/evalf';
import { roots } from '../polys/poly';
import { latex } from '../printing/latex';
import { str } from '../printing/str';
import { expandMul as expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';

/** A position (row, column) of a matrix. */
export type MatrixPosition = readonly [number, number];

/** SymPy `value == 0` for an entry (structural: an exact or floating zero). */
const isZeroEntry = (v: Expr): boolean => (v instanceof Rational || v instanceof Float) && v.isZero;
const isZeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isIndexList = (perm: readonly (readonly [number, number])[] | readonly number[]): perm is readonly number[] => typeof perm[0] === 'number';
const range = (a: number, b: number): number[] => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);

export class Matrix {
  #rows: number;
  #cols: number;
  /** Row-major entries. */
  readonly data: readonly Expr[];

  protected constructor(rows: number, cols: number, data: readonly Expr[]) {
    this.#rows = rows;
    this.#cols = cols;
    this.data = data;
  }

  get rows(): number {
    return this.#rows;
  }
  get cols(): number {
    return this.#cols;
  }
  /** A new shape for the entries (the in-place operations of the mutable matrix). */
  protected reshapeInPlace(rows: number, cols: number): void {
    this.#rows = rows;
    this.#cols = cols;
  }

  // ---- construction --------------------------------------------------------

  /** Build from nested arrays (row-major). */
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

  /** Build from a generator f(i, j). */
  static fromFunction(rows: number, cols: number, f: (i: number, j: number) => ExprLike): Matrix {
    const data: Expr[] = [];
    for (let i = 0; i < rows; i++) for (let j = 0; j < cols; j++) data.push(sympify(f(i, j)));
    return new Matrix(rows, cols, data);
  }

  static zeros(rows: number, cols = rows): Matrix {
    return new Matrix(rows, cols, Array.from({ length: rows * cols }, () => S.Zero));
  }

  /** A matrix of ones (SymPy Matrix.ones(rows, cols)). */
  static ones(rows: number, cols = rows): Matrix {
    return new Matrix(rows, cols, Array.from({ length: rows * cols }, () => S.One));
  }

  /** A matrix from its entries by position (SymPy Matrix.from_dok); the other entries are zero. */
  static fromDok(rows: number, cols: number, dok: Iterable<readonly [MatrixPosition, ExprLike]>): Matrix {
    const data: Expr[] = Array.from({ length: rows * cols }, () => S.Zero);
    for (const [[i, j], v] of dok) data[i * cols + j] = sympify(v);
    return new Matrix(rows, cols, data);
  }

  static eye(n: number): Matrix {
    return Matrix.fromFunction(n, n, (i, j) => (i === j ? 1 : 0));
  }

  static diag(...entries: ExprLike[]): Matrix {
    const d = entries.map(sympify);
    return Matrix.fromFunction(d.length, d.length, (i, j) => (i === j ? at(d, i) : 0));
  }

  /** Column vector. */
  static col(...entries: ExprLike[]): Matrix {
    return Matrix.of(entries.map((e) => [e]));
  }

  /** Row vector. */
  static row(...entries: ExprLike[]): Matrix {
    return Matrix.of([entries]);
  }

  /** Kronecker (tensor) product of several matrices, left to right. */
  static kron(...ms: Matrix[]): Matrix {
    if (ms.length === 0) return Matrix.eye(1);
    return ms.slice(1).reduce((acc, m) => acc.kron(m), first(ms));
  }

  // ---- access ----------------------------------------------------------------

  get shape(): [number, number] {
    return [this.rows, this.cols];
  }
  get isSquare(): boolean {
    return this.rows === this.cols;
  }

  get(i: number, j: number): Expr {
    if (i < 0 || i >= this.rows || j < 0 || j >= this.cols) throw new RangeError(`Matrix index (${i}, ${j}) out of range`);
    return at(this.data, i * this.cols + j);
  }

  /** Return a copy with entry (i, j) replaced. */
  with(i: number, j: number, v: ExprLike): Matrix {
    this.get(i, j);
    const data = [...this.data];
    data[i * this.cols + j] = sympify(v);
    return new Matrix(this.rows, this.cols, data);
  }

  row(i: number): Matrix {
    return Matrix.fromFunction(1, this.cols, (_, j) => this.get(i, j));
  }
  col(j: number): Matrix {
    return Matrix.fromFunction(this.rows, 1, (i) => this.get(i, j));
  }

  /** Sub-matrix of the given rows and columns. */
  slice(rows: readonly number[], cols: readonly number[]): Matrix {
    return Matrix.fromFunction(rows.length, cols.length, (i, j) => this.get(at(rows, i), at(cols, j)));
  }

  /** Remove row i and column j. */
  minor(i: number, j: number): Matrix {
    const rs = [...Array(this.rows).keys()].filter((r) => r !== i);
    const cs = [...Array(this.cols).keys()].filter((c) => c !== j);
    return this.slice(rs, cs);
  }

  toArray(): Expr[][] {
    return Array.from({ length: this.rows }, (_, i) => Array.from({ length: this.cols }, (_, j) => this.get(i, j)));
  }

  // ---- elementwise -------------------------------------------------------------

  map(f: (e: Expr, i: number, j: number) => ExprLike): Matrix {
    return Matrix.fromFunction(this.rows, this.cols, (i, j) => f(this.get(i, j), i, j));
  }

  private zip(o: Matrix, f: (a: Expr, b: Expr) => Expr, op: string): Matrix {
    if (this.rows !== o.rows || this.cols !== o.cols) {
      throw new ShapeError(`Matrix ${op}: shape mismatch ${this.rows}x${this.cols} vs ${o.rows}x${o.cols}`);
    }
    return new Matrix(this.rows, this.cols, this.data.map((a, k) => f(a, at(o.data, k))));
  }

  add(o: Matrix): Matrix {
    return this.zip(o, (a, b) => add(a, b), 'add');
  }
  sub(o: Matrix): Matrix {
    return this.zip(o, (a, b) => add(a, mul(-1, b)), 'sub');
  }
  neg(): Matrix {
    return this.map((e) => mul(-1, e));
  }
  /** Scalar multiplication. */
  scale(k: ExprLike): Matrix {
    const s = sympify(k);
    return this.map((e) => mul(s, e));
  }

  /**
   * Matrix product (or scalar multiplication when given a scalar). As in SymPy, each entry is
   * Add(*[a*b ...]) without expansion: Matrix([[x + 1]])*Matrix([[x - 1]]) is (x - 1)*(x + 1).
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
        if (a instanceof Rational && a.isZero) continue;
        const b = o.get(k, j);
        if (b instanceof Rational && b.isZero) continue;
        terms.push(mul(a, b));
      }
      return simp(add(...terms));
    });
  }

  /** Integer power (negative powers use the inverse). */
  pow(n: number): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('Matrix pow: matrix must be square');
    if (!Number.isInteger(n)) throw new RangeError('Matrix pow: exponent must be an integer');
    if (n < 0) return this.inv().pow(-n);
    // SymPy MatrixBase.pow: a diagonal or 1x1 matrix is raised entrywise; otherwise the products
    // are simplified as they go (dotprodsimp), here by expanding each entry
    if (n === 0) return Matrix.eye(this.rows);
    const diagonal = this.data.every((e, idx) => Math.floor(idx / this.cols) === idx % this.cols || (e instanceof Rational && e.isZero));
    if (diagonal) return this.map((e) => pow(e, n));
    let result = Matrix.eye(this.rows);
    let base: Matrix = this;
    let k = n;
    while (k > 0) {
      if (k & 1) result = result.product(base, expand);
      k >>= 1;
      if (k > 0) base = base.product(base, expand);
    }
    return result;
  }

  /** Kronecker (tensor) product this ⊗ o. */
  kron(o: Matrix): Matrix {
    return Matrix.fromFunction(this.rows * o.rows, this.cols * o.cols, (i, j) =>
      mul(this.get(Math.floor(i / o.rows), Math.floor(j / o.cols)), o.get(i % o.rows, j % o.cols)),
    );
  }

  /** Commutator [A, B] = AB - BA. */
  commutator(o: Matrix): Matrix {
    return this.mul(o).sub(o.mul(this));
  }

  /** Anticommutator {A, B} = AB + BA. */
  anticommutator(o: Matrix): Matrix {
    return this.mul(o).add(o.mul(this));
  }

  /** Stack horizontally. */
  hstack(...others: Matrix[]): Matrix {
    const all = [this, ...others];
    if (all.some((m) => m.rows !== this.rows)) throw new RangeError('hstack: row count mismatch');
    return Matrix.of(Array.from({ length: this.rows }, (_, i) => all.flatMap((m) => m.row(i).data)));
  }

  /** Stack vertically. */
  vstack(...others: Matrix[]): Matrix {
    const all = [this, ...others];
    if (all.some((m) => m.cols !== this.cols)) throw new RangeError('vstack: column count mismatch');
    return Matrix.of(all.flatMap((m) => m.toArray()));
  }

  // ---- linear algebra -------------------------------------------------------------

  transpose(): Matrix {
    return Matrix.fromFunction(this.cols, this.rows, (i, j) => this.get(j, i));
  }
  get T(): Matrix {
    return this.transpose();
  }

  conjugate(): Matrix {
    return this.map((e) => conjugate(e));
  }

  /** Conjugate transpose (Hermitian adjoint, dagger). */
  adjoint(): Matrix {
    return this.transpose().conjugate();
  }
  get H(): Matrix {
    return this.adjoint();
  }
  /** Alias of adjoint(). */
  dagger(): Matrix {
    return this.adjoint();
  }

  trace(): Expr {
    if (!this.isSquare) throw new NonSquareMatrixError('trace: matrix must be square');
    return add(...Array.from({ length: this.rows }, (_, i) => this.get(i, i)));
  }

  /**
   * Coefficients [1, c1, ..., cn] of det(λI - A) = λ^n + c1 λ^(n-1) + ... + cn,
   * computed with the division-free Berkowitz algorithm.
   */
  charpolyCoeffs(): Expr[] {
    if (!this.isSquare) throw new NonSquareMatrixError('charpoly: matrix must be square');
    return berkowitz(this);
  }

  /** Characteristic polynomial det(λI - A) as an expression in `lambda`. */
  charpoly(lambda: Sym): Expr {
    const cs = this.charpolyCoeffs();
    const n = cs.length - 1;
    return expand(add(...cs.map((c, k) => mul(c, pow(lambda, n - k)))));
  }

  det(): Expr {
    if (!this.isSquare) throw new NonSquareMatrixError('det: matrix must be square');
    const n = this.rows;
    if (n === 0) return S.One;
    if (n === 1) return this.get(0, 0);
    if (n === 2) return expand(add(mul(this.get(0, 0), this.get(1, 1)), mul(-1, this.get(0, 1), this.get(1, 0))));
    const cs = berkowitz(this);
    return expand(n % 2 === 0 ? at(cs, n) : mul(-1, at(cs, n)));
  }

  /** Matrix of cofactors. */
  cofactorMatrix(): Matrix {
    return Matrix.fromFunction(this.rows, this.cols, (i, j) => {
      const m = this.minor(i, j).det();
      return (i + j) % 2 === 0 ? m : mul(-1, m);
    });
  }

  /** Adjugate (classical adjoint): transpose of the cofactor matrix. */
  adjugate(): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('adjugate: matrix must be square');
    if (this.rows === 1) return Matrix.of([[1]]);
    return this.cofactorMatrix().transpose();
  }

  /** Inverse via adjugate / determinant. The determinant is simplified first. */
  inv(): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('A Matrix must be square to invert.');
    const d = simplify(this.det());
    if (d instanceof Rational && d.isZero) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
    const invDet = pow(d, -1);
    return this.adjugate().map((e) => expand(mul(e, invDet)));
  }

  /** Eigenvalues (with multiplicity) as roots of the characteristic polynomial. */
  eigenvals(): Expr[] {
    // SymPy _eigenvals: a triangular matrix has its diagonal entries as eigenvalues, in order
    const n = this.rows;
    const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
    const below = this.data.filter((_, k) => Math.floor(k / this.cols) > k % this.cols);
    const above = this.data.filter((_, k) => Math.floor(k / this.cols) < k % this.cols);
    if (this.isSquare && (below.every(isZero) || above.every(isZero))) return Array.from({ length: n }, (_, i) => this.get(i, i));
    const lam = new Sym('lambda_');
    return roots(this.charpoly(lam), lam).map((r) => simplify(r));
  }

  // ---- transformation --------------------------------------------------------------

  subs(s: Substitution): Matrix;
  subs(from: Expr, to: ExprLike): Matrix;
  subs(a: Substitution | Expr, b?: ExprLike): Matrix {
    const spec: Substitution = a instanceof Expr ? [[a, defined(b, 'subs replacement')]] : a;
    return this.map((e) => subs(e, spec));
  }
  expand(): Matrix {
    return this.map(expand);
  }
  simplify(): Matrix {
    return this.map((e) => simplify(e));
  }
  evalf(n?: number | NumericValues, opts?: EvalfOptions): Matrix {
    return this.map((e) => evalf(e, n, opts));
  }
  /** Numeric evaluation to nested arrays of complex values. */
  toComplex(values?: NumericValues): ComplexValue[][] {
    return this.toArray().map((row) => row.map((e) => toComplex(e, values)));
  }
  /** Compile into a function of the given parameters returning complex nested arrays. */
  lambdify(params: readonly Sym[]): (...args: (number | ComplexValue)[]) => ComplexValue[][] {
    const fs = this.toArray().map((row) => row.map((e) => lambdify(e, params)));
    return (...args) => fs.map((row) => row.map((f) => f(...args)));
  }

  // ---- predicates ----------------------------------------------------------------

  /** Structural equality of all entries. */
  equals(o: Matrix): boolean {
    return this.rows === o.rows && this.cols === o.cols && this.data.every((e, k) => e.key === at(o.data, k).key);
  }
  /**
   * SymPy Basic.is_same: the same class (mutable or immutable) and the
   * same entries; numbers are compared with `approx` when given.
   */
  isSame(o: unknown, approx?: (a: Expr, b: Expr) => boolean): boolean {
    if (!(o instanceof Matrix) || o.constructor !== this.constructor || this.rows !== o.rows || this.cols !== o.cols) return false;
    return this.data.every((e, k) => {
      const b = at(o.data, k);
      return approx && e.isNumber && b.isNumber ? approx(e, b) : e.key === b.key;
    });
  }
  /** Equality after simplifying the difference. */
  equalsSimplified(o: Matrix): boolean {
    return this.rows === o.rows && this.cols === o.cols && this.sub(o).simplify().isZero;
  }
  get isZero(): boolean {
    return this.data.every((e) => e instanceof Rational && e.isZero);
  }
  isHermitian(): boolean {
    return this.isSquare && this.equalsSimplified(this.adjoint());
  }
  isUnitary(): boolean {
    return this.isSquare && this.mul(this.adjoint()).equalsSimplified(Matrix.eye(this.rows));
  }

  // ---- structure (SymPy MatrixBase methods) ----------------------------------------

  /** A copy (SymPy copy; the mutable matrix gives a mutable copy). */
  copy(): Matrix {
    return new Matrix(this.rows, this.cols, [...this.data]);
  }
  /** The entries as nested arrays (SymPy tolist). */
  tolist(): Expr[][] {
    return this.toArray();
  }
  /** The entries in row-major order (SymPy flat). */
  flat(): Expr[] {
    return [...this.data];
  }
  /** The nonzero entries in row-major order (SymPy values). */
  values(): Expr[] {
    return this.data.filter((e) => !isZeroEntry(e));
  }
  /** The nonzero entries by position (SymPy todok). */
  todok(): Map<MatrixPosition, Expr> {
    const out = new Map<MatrixPosition, Expr>();
    this.data.forEach((v, k) => {
      if (!isZeroEntry(v)) out.set([Math.floor(k / this.cols), k % this.cols], v);
    });
    return out;
  }
  /** The nonzero entries as row -> column -> value (SymPy todod). */
  todod(): Map<number, Map<number, Expr>> {
    const out = new Map<number, Map<number, Expr>>();
    for (const [[i, j], v] of this.todok()) {
      const row = out.get(i) ?? new Map<number, Expr>();
      row.set(j, v);
      out.set(i, row);
    }
    return out;
  }

  /** SymPy minor_submatrix(i, j): the matrix without row i and column j (negative indices count from the end). */
  minorSubmatrix(i: number, j: number): Matrix {
    return this.minor(i < 0 ? i + this.rows : i, j < 0 ? j + this.cols : j);
  }
  /** SymPy minorMatrix (deprecated name of minor_submatrix). */
  minorMatrix(i: number, j: number): Matrix {
    return this.minorSubmatrix(i, j);
  }
  /** SymPy minor(i, j) (minorEntry): the determinant of the minor submatrix. */
  minorEntry(i: number, j: number): Expr {
    if (!this.isSquare) throw new NonSquareMatrixError('minor: matrix must be square');
    return this.minorSubmatrix(i, j).det();
  }
  /** SymPy cofactor(i, j): (-1)**(i + j) times the minor. */
  cofactor(i: number, j: number): Expr {
    const m = this.minorEntry(i, j);
    return (i + j) % 2 === 0 ? m : mul(-1, m);
  }

  /** SymPy upper_triangular(k): the entries on and above the k-th diagonal. */
  upperTriangular(k = 0): Matrix {
    return this.map((e, i, j) => (j - i >= k ? e : 0));
  }
  /** SymPy lower_triangular(k): the entries on and below the k-th diagonal. */
  lowerTriangular(k = 0): Matrix {
    return this.map((e, i, j) => (j - i <= k ? e : 0));
  }
  /** SymPy diagonal(k): the k-th diagonal as a row (k > 0 above the main diagonal). */
  diagonal(k = 0): Matrix {
    if (k <= -this.rows || k >= this.cols) throw new RangeError(`The ${k} diagonal is out of range [${1 - this.rows}, ${this.cols - 1}]`);
    const out: Expr[] = [];
    for (let i = Math.max(0, -k); i < this.rows && i + k < this.cols; i++) out.push(this.get(i, i + k));
    return Matrix.row(...out);
  }
  /**
   * SymPy extract(rowsList, colsList): the submatrix of the given rows and
   * columns (negative indices count from the end; a list of booleans selects).
   */
  extract(rows: readonly (number | boolean)[], cols: readonly (number | boolean)[]): Matrix {
    const norm = (idx: readonly (number | boolean)[], n: number): number[] =>
      idx.every((v) => typeof v === 'boolean')
        ? idx.flatMap((v, i) => (v ? [i] : []))
        : idx.map((v) => (typeof v === 'boolean' ? Number(v) : v < 0 ? v + n : v));
    return this.slice(norm(rows, this.rows), norm(cols, this.cols));
  }
  /** SymPy reshape(rows, cols): the entries in row-major order in a new shape. */
  reshape(r: number, c: number): Matrix {
    if (r * c !== this.data.length) throw new RangeError(`Invalid reshape parameters ${r} ${c}`);
    return new Matrix(r, c, [...this.data]);
  }
  /** SymPy rot90(k): rotated by k quarter turns clockwise. */
  rot90(k = 1): Matrix {
    const t = ((k % 4) + 4) % 4;
    let r: Matrix = this;
    for (let i = 0; i < t; i++) {
      const R = r;
      r = Matrix.fromFunction(R.cols, R.rows, (a, b) => R.get(R.rows - 1 - b, a));
    }
    return r;
  }
  /** SymPy vec(): the columns stacked into one column. */
  vec(): Matrix {
    return this.transpose().reshape(this.data.length, 1);
  }
  /**
   * SymPy vech(diagonal=True, check_symmetry=True): the entries on and below
   * the diagonal (strictly below without the diagonal), column by column.
   */
  vech(opts: { diagonal?: boolean; checkSymmetry?: boolean } = {}): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('vech: matrix must be square');
    if ((opts.checkSymmetry ?? true) && !this.isSymmetric()) throw new RangeError('The matrix is not symmetric.');
    const out: Expr[] = [];
    for (let j = 0; j < this.cols; j++) for (let i = (opts.diagonal ?? true) ? j : j + 1; i < this.rows; i++) out.push(this.get(i, j));
    return Matrix.col(...out);
  }
  /** SymPy row_insert(pos, other): other's rows inserted before row pos (a new matrix). */
  rowInsert(pos: number, o: Matrix): Matrix {
    if (this.rows === 0 && this.cols === 0) return o;
    if (o.cols !== this.cols) throw new ShapeError('The matrices have incompatible number of columns.');
    let p = pos < 0 ? pos + this.rows : pos;
    p = Math.min(Math.max(p, 0), this.rows);
    const rows = this.toArray();
    return Matrix.of([...rows.slice(0, p), ...o.toArray(), ...rows.slice(p)]);
  }
  /** SymPy col_insert(pos, other): other's columns inserted before column pos (a new matrix). */
  colInsert(pos: number, o: Matrix): Matrix {
    if (this.rows === 0 && this.cols === 0) return o;
    if (o.rows !== this.rows) throw new ShapeError('The matrices have incompatible number of rows.');
    return this.transpose().rowInsert(pos, o.transpose()).transpose();
  }
  /**
   * SymPy permute(perm, orientation='rows', direction='forward'): rows (or
   * columns) permuted by a list of swaps, applied in order ('forward') or in
   * reverse ('backward'), or by an index list (row i <- row perm[i]; as in
   * SymPy, the direction does not apply to an index list).
   */
  permute(perm: readonly (readonly [number, number])[] | readonly number[], opts: { orientation?: 'rows' | 'cols'; direction?: 'forward' | 'backward' } = {}): Matrix {
    const cols = opts.orientation === 'cols';
    const backward = opts.direction === 'backward';
    const n = cols ? this.cols : this.rows;
    const order = range(0, n);
    if (isIndexList(perm)) {
      perm.forEach((v, i) => (order[i] = v));
    } else {
      const swaps = [...perm];
      if (backward) swaps.reverse();
      for (const [a, b] of swaps) [order[a], order[b]] = [at(order, b), at(order, a)];
    }
    return cols ? this.slice(range(0, this.rows), order) : this.slice(order, range(0, this.cols));
  }

  // ---- products ---------------------------------------------------------------------

  /** SymPy multiply(other): the matrix product (a scalar scales). */
  multiply(o: Matrix | ExprLike): Matrix {
    return this.mul(o);
  }
  /** SymPy rmultiply(other): other * this. */
  rmultiply(o: Matrix | ExprLike): Matrix {
    return o instanceof Matrix ? o.mul(this) : this.scale(o);
  }
  /** SymPy multiply_elementwise(other): the Hadamard product. */
  multiplyElementwise(o: Matrix): Matrix {
    if (this.rows !== o.rows || this.cols !== o.cols) throw new ShapeError(`Matrix shapes must agree (${this.rows}, ${this.cols}) != (${o.rows}, ${o.cols})`);
    return this.map((e, i, j) => mul(e, o.get(i, j)));
  }
  /** SymPy project(v): the projection of this vector onto v. */
  project(v: Matrix): Matrix {
    const dot = (a: Matrix, b: Matrix): Expr => add(...a.data.map((e, k) => mul(e, at(b.data, k))));
    return v.scale(mul(dot(this, v), pow(dot(v, v), -1)));
  }
  /** SymPy hat(): the skew-symmetric matrix of the cross product with this 3-vector. */
  hat(): Matrix {
    if (this.rows !== 3 || this.cols !== 1) throw new ShapeError(`Dimensions incorrect, expected (3, 1), got (${this.rows}, ${this.cols})`);
    const [x, y, z] = [this.get(0, 0), this.get(1, 0), this.get(2, 0)];
    return Matrix.of([
      [0, mul(-1, z), y],
      [z, 0, mul(-1, x)],
      [mul(-1, y), x, 0],
    ]);
  }
  /** SymPy vee(): the 3-vector of a skew-symmetric 3x3 matrix (the inverse of hat). */
  vee(): Matrix {
    if (this.rows !== 3 || this.cols !== 3) throw new ShapeError(`Dimensions incorrect, expected (3, 3), got (${this.rows}, ${this.cols})`);
    if (this.isAntiSymmetric() !== true) throw new RangeError('Matrix is not skew-symmetric');
    return Matrix.col(this.get(2, 1), this.get(0, 2), this.get(1, 0));
  }

  // ---- predicates on the entries --------------------------------------------------

  /** SymPy is_symmetric(simplify=True): equal to its transpose (the differences simplified unless `simplify` is false). */
  isSymmetric(simplifyEntries = true): boolean {
    if (!this.isSquare) return false;
    const d = this.sub(this.transpose());
    return d.data.every((e) => isZeroE(simplifyEntries ? simplify(e) : e));
  }
  /**
   * SymPy is_anti_symmetric(simplify=True): equal to minus its transpose;
   * 'unknown' when an unsimplified entry sum is not structurally zero.
   */
  isAntiSymmetric(simplifyEntries = true): Truth {
    if (!this.isSquare) return false;
    const sums = this.add(this.transpose()).data;
    if (simplifyEntries) return sums.every((e) => isZeroE(simplify(e)));
    if (sums.every(isZeroE)) return true;
    return sums.some((e) => e.isNumber && !isZeroE(e)) ? false : 'unknown';
  }
  /** SymPy is_diagonal(): the entries off the main diagonal are zero (rectangular matrices too). */
  isDiagonal(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) === k % this.cols || isZeroE(e));
  }
  /** SymPy is_upper: the entries below the main diagonal are zero. */
  isUpper(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) <= k % this.cols || isZeroE(e));
  }
  /** SymPy is_lower: the entries above the main diagonal are zero. */
  isLower(): boolean {
    return this.data.every((e, k) => Math.floor(k / this.cols) >= k % this.cols || isZeroE(e));
  }
  /** SymPy is_nilpotent(): some power of the matrix is zero. */
  isNilpotent(): boolean {
    if (!this.isSquare) throw new NonSquareMatrixError('Nilpotency is valid only for square matrices');
    return this.pow(this.rows).data.every(isZeroE);
  }
  /** SymPy is_symbolic(): some entry contains a symbol. */
  isSymbolic(): boolean {
    return this.data.some((e) => freeSymbols(e).size > 0);
  }
  /** SymPy has(*patterns): some entry contains one of the patterns. */
  has(...patterns: ExprLike[]): boolean {
    const ps = patterns.map((p) => sympify(p));
    return this.data.some((e) => ps.some((p) => e.has(p)));
  }
  /** SymPy atoms(): the atoms of the entries, optionally filtered by a predicate. */
  atoms(pred?: (a: Expr) => boolean): Expr[] {
    const out = new Map<string, Expr>();
    for (const e of this.data) for (const a of atoms(e, pred)) out.set(a.key, a);
    return [...out.values()];
  }

  // ---- entrywise operations (SymPy applies them to each entry) ---------------------

  /** SymPy n(): alias of evalf. */
  n(n?: number | NumericValues, opts?: EvalfOptions): Matrix {
    return this.evalf(n, opts);
  }
  /** SymPy as_real_imag(): the matrices of the real and imaginary parts. */
  asRealImag(): [Matrix, Matrix] {
    const parts = this.data.map((e) => asRealImag(e));
    return [new Matrix(this.rows, this.cols, parts.map(([r]) => r)), new Matrix(this.rows, this.cols, parts.map(([, i]) => i))];
  }
  /** SymPy diff(x, n): the entries differentiated. */
  diff(x: Expr, n = 1): Matrix {
    return this.map((e) => e.diff(x, n));
  }
  /** SymPy integrate(x) or integrate((x, a, b)): the entries integrated. */
  integrate(x: Sym, limits?: [ExprLike, ExprLike]): Matrix {
    return this.map((e) => e.integrate(x, limits));
  }
  /** SymPy limit(z, z0, dir): the limits of the entries. */
  limit(z: Sym, z0: ExprLike, dir: '+' | '-' | '+-' = '+'): Matrix {
    return this.map((e) => e.limit(z, z0, dir));
  }
  /** SymPy xreplace(rule): the entries with exact subtrees replaced. */
  xreplace(rule: Substitution): Matrix {
    return this.map((e) => xreplace(e, rule));
  }
  /** SymPy replace(query, value): the entries with matching subexpressions replaced. */
  replace(query: Query, value: Replacement, opts: Omit<NonNullable<Parameters<typeof replace>[3]>, 'map'> = {}): Matrix {
    // (without the map option replace gives the expression only)
    return this.map((e) => cast(replace(e, query, value, opts), Expr));
  }

  // ---- printing ------------------------------------------------------------------

  toString(): string {
    if (this.shape[0] === 0 || this.shape[1] === 0) return `Matrix(${this.shape[0]}, ${this.shape[1]}, [])`;
    return `Matrix([${this.toArray()
      .map((r) => `[${r.map(str).join(', ')}]`)
      .join(', ')}])`;
  }
  /** LaTeX as SymPy latex(Matrix): a bracketed matrix environment, an array beyond 10 columns. */
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
    if (k < n - 2) v = A.mul(v);
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
