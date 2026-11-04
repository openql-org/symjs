// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Immutable matrices with symbolic entries.
 */

import { at, defined, first } from '../core/guard';
import { NonInvertibleMatrixError, NonSquareMatrixError } from '../core/errors';
import type { ComplexValue, EvalfOptions, ExprLike, NumericValues, Substitution } from '../core/nodes';
import { Expr, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { sympifyMethod } from '../core/sympify';
import { conjugate } from '../functions/elementary/elementary';
import { evalf, lambdify, toComplex } from '../numeric/evalf';
import { roots } from '../polys/poly';
import { latex } from '../printing/latex';
import { str } from '../printing/str';
import { expandMul as expand } from '../simplify/expand';
import { simplify } from '../simplify/simplify';

export class Matrix {
  readonly rows: number;
  readonly cols: number;
  /** Row-major entries. */
  readonly data: readonly Expr[];

  protected constructor(rows: number, cols: number, data: readonly Expr[]) {
    this.rows = rows;
    this.cols = cols;
    this.data = data;
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
      throw new RangeError(`Matrix ${op}: shape mismatch ${this.rows}x${this.cols} vs ${o.rows}x${o.cols}`);
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

  /** Matrix product (or scalar multiplication when given a scalar). */
  mul(o: Matrix | ExprLike): Matrix {
    if (!(o instanceof Matrix)) return this.scale(o);
    if (this.cols !== o.rows) throw new RangeError(`Matrix mul: shape mismatch ${this.rows}x${this.cols} * ${o.rows}x${o.cols}`);
    return Matrix.fromFunction(this.rows, o.cols, (i, j) => {
      const terms: Expr[] = [];
      for (let k = 0; k < this.cols; k++) {
        const a = this.get(i, k);
        if (a instanceof Rational && a.isZero) continue;
        const b = o.get(k, j);
        if (b instanceof Rational && b.isZero) continue;
        terms.push(mul(a, b));
      }
      return expand(add(...terms));
    });
  }

  /** Integer power (negative powers use the inverse). */
  pow(n: number): Matrix {
    if (!this.isSquare) throw new NonSquareMatrixError('Matrix pow: matrix must be square');
    if (!Number.isInteger(n)) throw new RangeError('Matrix pow: exponent must be an integer');
    if (n < 0) return this.inv().pow(-n);
    let result = Matrix.eye(this.rows);
    let base: Matrix = this;
    let k = n;
    while (k > 0) {
      if (k & 1) result = result.mul(base);
      k >>= 1;
      if (k > 0) base = base.mul(base);
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

  // ---- printing ------------------------------------------------------------------

  toString(): string {
    if (this.shape[0] === 0 || this.shape[1] === 0) return `Matrix(${this.shape[0]}, ${this.shape[1]}, [])`;
    return `Matrix([${this.toArray()
      .map((r) => `[${r.map(str).join(', ')}]`)
      .join(', ')}])`;
  }
  /** LaTeX as SymPy latex(Matrix): a bracketed matrix environment, an array beyond 10 columns. */
  toLatex(): string {
    const [env, spec] = this.cols <= 10 ? ['matrix', ''] : ['array', `{${'c'.repeat(this.cols)}}`];
    const body = this.toArray()
      .map((r) => r.map(latex).join(' & '))
      .join('\\\\');
    return `\\left[\\begin{${env}}${spec}${body}\\end{${env}}\\right]`;
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
