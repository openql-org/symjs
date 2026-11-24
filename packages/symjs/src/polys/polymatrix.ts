// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/polymatrix.py, BSD-3-Clause; see LICENSE.

import { at, first } from '../core/guard';
import { Expr, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { mul, pow, sympify } from '../core/ops';
import { Matrix } from '../matrices/matrix';
import { str } from '../printing/str';
import { constructDomain } from './constructor';
import { QQ } from './domains';
import type { Domain } from './domains';
import { DomainMatrix } from './matrices/domainmatrix';
import { parallelPolyFromExpr } from './fromexpr';
import { preprocessDomain } from './polyoptions';
import { Poly } from './sympoly';

/** An expression or polynomial accepted as a matrix entry. */
export type PolyMatrixEntry = ExprLike | Poly;
/** The generators of a polynomial matrix: one generator or a list of them (SymPy's tuple). */
export type PolyMatrixGens = Expr | readonly Expr[];
/** Options for constructing a polynomial matrix over a specified ring. */
export interface PolyMatrixOptions { /** The polynomial ring for the matrix entries. */
ring?: PolyMatrixRing | Domain | string }
/**
 * ...): the entry in row i and column j.
 *
 * @param i - Zero-based row index.
 * @param j - Zero-based column index.
 * @returns The entry to place at that position.
 */
export type PolyMatrixEntryFunction = (i: number, j: number) => PolyMatrixEntry;
/** An argument to the polynomial matrix constructor, including dimensions, entries, generators or options. */
export type PolyMatrixArgument = PolyMatrixEntry | readonly PolyMatrixEntry[] | readonly (readonly PolyMatrixEntry[])[] | PolyMatrixEntryFunction | readonly Expr[] | PolyMatrixOptions;

const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const isOptions = (a: unknown): a is PolyMatrixOptions => typeof a === 'object' && a !== null && !Array.isArray(a) && !(a instanceof Expr) && !(a instanceof Poly);
const isEntryFunction = (a: unknown): a is PolyMatrixEntryFunction => typeof a === 'function';
const isEntryArray = (a: unknown): a is readonly (PolyMatrixEntry | readonly PolyMatrixEntry[])[] => Array.isArray(a);
const isRowList = (a: readonly (PolyMatrixEntry | readonly PolyMatrixEntry[])[]): a is readonly (readonly PolyMatrixEntry[])[] => a.every((row) => Array.isArray(row));
const isExprList = (a: readonly unknown[]): a is readonly Expr[] => a.every((g) => g instanceof Expr);
const isInteger = (a: unknown): a is number => typeof a === 'number' && Number.isSafeInteger(a) && a >= 0;

/**
 * The polynomial ring K[gens] of a polynomial matrix (SymPy's PolynomialRing
 * domain of a PolyMatrix). The coefficient domain K may itself be a
 * polynomial ring or a fraction field, as in QQ[x][y] or ZZ(x)[y].
 */
export class PolyMatrixRing {
  /** The ordered generators. */
  readonly gens: readonly Expr[];
  /**
   * Construct a `PolyMatrixRing` instance.
   *
   * @param domain - Coefficient domain.
   * @param gens - Polynomial generators in the desired order.
   */
  constructor(
    /** The coefficient domain. */
    readonly domain: Domain, gens: PolyMatrixGens) {
    this.gens = gens instanceof Expr ? [gens] : [...gens];
  }
  /**
   * A ring given as a PolyMatrixRing, a polynomial ring domain or a string such as 'QQ[x]' or 'QQ[x][y]'.
   *
   * @param ring - Polynomial ring supplying the generators and coefficient domain.
   * @returns A ring given as a PolyMatrixRing, a polynomial ring domain or a string such as 'QQ[x]' or 'QQ[x][y]'.
   * @throws TypeError when the supplied domain is not a polynomial ring.
   */
  static of(ring: PolyMatrixRing | Domain | string): PolyMatrixRing {
    if (ring instanceof PolyMatrixRing) return ring;
    if (typeof ring === 'string') {
      const match = /^(.*)\[([^[\]]*)\]$/.exec(ring.replace(/\s+/g, ''));
      if (match === null) throw new TypeError(`expected a polynomial ring, got ${ring}`);
      return new PolyMatrixRing(preprocessDomain(match[1]), String(match[2]).split(',').filter((s) => s !== '').map((s) => new Sym(s)));
    }
    if (ring.isField || ring.symbols.length === 0) throw new TypeError(`expected a polynomial ring, got ${ring.toString()}`);
    return new PolyMatrixRing(ring.dom, ring.symbols);
  }
  /**
   * The element of the ring of an expression or a polynomial; throws CoercionFailed when it is not one.
   *
   * @param e - Expression to convert.
   * @returns The element of the ring of an expression or a polynomial.
   */
  element(e: PolyMatrixEntry): Poly {
    const p = Poly.from(e instanceof Poly ? e.asExpr() : e, this.gens, { domain: this.domain.toString() });
    for (const c of p.coeffs()) this.domain.fromSympy(c);
    return p;
  }
  /**
   * The smallest ring containing this one and another ring or coefficient domain.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The smallest ring containing this one and another ring or coefficient domain.
   */
  unify(other: PolyMatrixRing | Domain): PolyMatrixRing {
    const o = other instanceof PolyMatrixRing ? other : other.symbols.length && !other.isField ? new PolyMatrixRing(other.dom, other.symbols) : new PolyMatrixRing(other, []);
    const gens = [...this.gens];
    for (const g of o.gens) if (!gens.some((h) => h.key === g.key)) gens.push(g);
    return new PolyMatrixRing(this.domain.unify(o.domain), gens);
  }
  /**
   * Whether the operand represents the same value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   */
  equals(other: unknown): boolean {
    return other instanceof PolyMatrixRing && this.toString() === other.toString();
  }
  /**
   * The printable representation.
   *
   * @returns The formatted text.
   */
  toString(): string {
    return `${this.domain.toString()}[${this.gens.map((g) => str(g)).join(',')}]`;
  }
}

/**
 * A dense matrix of polynomials in a common polynomial ring.
 *
 * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix`
 * @example
 * ```ts
 * import { MutablePolyDenseMatrix, ex } from '@symjs/symjs';
 *
 * new MutablePolyDenseMatrix([[ex`x**2`]], ex`x`).toMatrix(); // => Matrix([[x**2]])
 * ```
 */
export class MutablePolyDenseMatrix implements Iterable<Poly> {
  /**
   * The polynomial ring to which the elements belong.
   *
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.ring`
   */
  readonly ring: PolyMatrixRing;
  private readonly nrows: number;
  private readonly ncols: number;
  private readonly entries: readonly Poly[];

  /**
   * From a list of rows, a list of entries (a column)
   * or rows, columns and a list or function of the entries, followed by the
   * generators; the ring option fixes the polynomial ring.
   *
   * @param args - Arguments to the operation.
   * @throws TypeError when an empty matrix is constructed without specifying its ring or the entries mix individual values and rows or the arguments do not describe a polynomial matrix or a generator is not an expression.
   * @throws RangeError when the entry count differs from the product of the dimensions.
   */
  constructor(...args: PolyMatrixArgument[]) {
    const last = args.at(-1);
    let options: PolyMatrixOptions = {};
    if (isOptions(last)) {
      options = last;
      args.pop();
    }
    let rows: number, cols: number, items: PolyMatrixEntry[], gens: PolyMatrixArgument[];
    const [a0, a1, a2] = args;
    if (!args.length) {
      if (options.ring === undefined) throw new TypeError('The ring needs to be specified for an empty PolyMatrix');
      [rows, cols, items, gens] = [0, 0, [], []];
    } else if (isEntryArray(a0)) {
      const elements = a0;
      gens = args.slice(1);
      if (!elements.length) [rows, cols, items] = [0, 0, []];
      else if (isRowList(elements)) {
        [rows, cols, items] = [elements.length, at(elements, 0).length, elements.flat()];
      } else {
        items = elements.filter((e): e is PolyMatrixEntry => !Array.isArray(e));
        if (items.length !== elements.length) throw new TypeError('PolyMatrix: a list of entries mixes rows and entries');
        [rows, cols] = [items.length, 1];
      }
    } else if (isInteger(a0) && isInteger(a1) && isEntryArray(a2)) {
      [rows, cols, items, gens] = [a0, a1, a2.flat(), args.slice(3)];
    } else if (isInteger(a0) && isInteger(a1) && isEntryFunction(a2)) {
      [rows, cols, gens] = [a0, a1, args.slice(3)];
      items = range(rows).flatMap((i) => range(cols).map((j) => a2(i, j)));
    } else throw new TypeError('Invalid arguments');
    if (items.length !== rows * cols) throw new RangeError('PolyMatrix: the number of entries does not match the shape');
    // PolyMatrix([[1]], x, y) and PolyMatrix([[1]], [x, y]) are the same
    const generators: readonly unknown[] = gens.length === 1 && Array.isArray(gens[0]) ? gens[0] : gens;
    if (!isExprList(generators)) throw new TypeError('PolyMatrix generators must be expressions');
    const built = MutablePolyDenseMatrix.fromList(rows, cols, items, generators, options.ring);
    this.ring = built.ring;
    [this.nrows, this.ncols, this.entries] = [rows, cols, built.entries];
  }

  /**
   * The matrix of rows x cols entries over the given ring, or over the ring of their polynomials.
   *
   * @param rows - Number of rows.
   * @param cols - Number of columns.
   * @param items - Entries of the matrix.
   * @param gens - Polynomial generators in the desired order.
   * @param ring - Polynomial ring supplying the generators and coefficient domain.
   * @returns The matrix of rows x cols entries over the given ring, or over the ring of their polynomials.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.from_list`
   */
  static fromList(rows: number, cols: number, items: readonly PolyMatrixEntry[], gens: readonly Expr[], ring?: PolyMatrixRing | Domain | string): MutablePolyDenseMatrix {
    let R: PolyMatrixRing;
    if (ring !== undefined) R = PolyMatrixRing.of(ring);
    else if (items.length && items.every((p) => p instanceof Poly)) {
      const polys = items.filter((q): q is Poly => q instanceof Poly);
      let p = first(polys);
      for (const q of polys.slice(1)) p = p.unify(q)[0];
      R = new PolyMatrixRing(preprocessDomain(p.domain), p.gens);
    } else {
      const [polys, info] = parallelPolyFromExpr(items.map((e) => e instanceof Poly ? e.asExpr() : e), gens);
      R = new PolyMatrixRing(constructDomain(polys.flatMap((p) => p.coeffs()), { field: true })[0], info.gens);
    }
    return MutablePolyDenseMatrix.create(R, rows, cols, items.map((e) => R.element(e)));
  }

  private static create(ring: PolyMatrixRing, rows: number, cols: number, entries: readonly Poly[]): MutablePolyDenseMatrix {
    const M: MutablePolyDenseMatrix = Object.create(MutablePolyDenseMatrix.prototype);
    Object.assign(M, { ring, nrows: rows, ncols: cols, entries });
    return M;
  }

  private withEntries(ring: PolyMatrixRing, rows: number, cols: number, values: readonly Expr[]): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.create(ring, rows, cols, values.map((e) => ring.element(e)));
  }

  /**
   * The matrix of a DomainMatrix over a polynomial ring.
   *
   * @param dm - Matrix over a coefficient domain.
   * @returns The matrix of a DomainMatrix over a polynomial ring.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.from_dm`
   */
  static fromDm(dm: DomainMatrix): MutablePolyDenseMatrix {
    const [rows, cols] = dm.shape;
    const ring = PolyMatrixRing.of(dm.domain);
    return MutablePolyDenseMatrix.create(ring, rows, cols, dm.toMatrix().flat().map((e) => ring.element(e)));
  }

  /**
   * The polynomial matrix of a Matrix in the given generators or ring.
   *
   * @param other - Operand to combine or compare with this value.
   * @param args - Arguments to the operation.
   * @returns The polynomial matrix of a Matrix in the given generators or ring.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.from_Matrix`
   */
  static fromMatrix(other: Matrix, ...args: (Expr | readonly Expr[] | PolyMatrixOptions)[]): MutablePolyDenseMatrix {
    return new MutablePolyDenseMatrix(other.rows, other.cols, other.flat(), ...args);
  }

  /**
   * The identity matrix over QQ[gens].
   *
   * @param n - Number of rows and columns.
   * @param gens - Polynomial generators in the desired order.
   * @returns The identity matrix over QQ[gens].
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.eye`
   */
  static eye(n: number, gens: PolyMatrixGens): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.fromDmOver(Matrix.eye(n), gens);
  }

  /**
   * The zero matrix over QQ[gens].
   *
   * @param m - Number of rows.
   * @param n - Number of columns.
   * @param gens - Polynomial generators in the desired order.
   * @returns The zero matrix over QQ[gens].
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.zeros`
   */
  static zeros(m: number, n: number, gens: PolyMatrixGens): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.fromDmOver(Matrix.zeros(m, n), gens);
  }

  private static fromDmOver(matrix: Matrix, gens: PolyMatrixGens): MutablePolyDenseMatrix {
    const ring = PolyMatrixRing.of(QQ.polyRing(...(gens instanceof Expr ? [gens] : gens).map((g) => {
      if (!(g instanceof Sym)) throw new TypeError('generators must be symbols');
      return g;
    })));
    return MutablePolyDenseMatrix.create(ring, matrix.rows, matrix.cols, matrix.flat().map((e) => ring.element(e)));
  }

  /**
   * The number of matrix rows.
   *
   * @returns The number of matrix rows.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.rows`
   */
  get rows(): number { return this.nrows; }
  /**
   * The number of matrix columns.
   *
   * @returns The number of matrix columns.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.cols`
   */
  get cols(): number { return this.ncols; }
  /**
   * The number of rows and columns, in that order.
   *
   * @returns The number of rows and columns, in that order.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.shape`
   */
  get shape(): [number, number] { return [this.rows, this.cols]; }
  /**
   * The coefficient domain of the ring.
   *
   * @returns The coefficient domain of the ring.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.domain`
   */
  get domain(): Domain { return this.ring.domain; }
  /**
   * The ordered generators.
   *
   * @returns The ordered generators.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.gens`
   */
  get gens(): readonly Expr[] { return this.ring.gens; }
  /**
   * The number of entries (Python len).
   *
   * @returns The number of entries (Python len).
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__len__`
   */
  get length(): number { return this.entries.length; }
  /**
   * Iterate over the polynomial entries in row-major order.
   *
   * @returns An iterator over the entries.
   */
  *[Symbol.iterator](): Iterator<Poly> { yield* this.entries; }
  /**
   * The entries in row-major order.
   *
   * @returns The entries in row-major order.
   */
  flat(): Poly[] { return [...this.entries]; }

  /**
   * The entry at row i and column j, or the entry at the row-major index i (negative indices count from the end).
   *
   * @param i - Zero-based row index.
   * @param j - Zero-based column index.
   * @returns The entry at row i and column j, or the entry at the row-major index i (negative indices count from the end).
   * @throws RangeError when a row or column index is out of bounds.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__getitem__`
   */
  get(i: number, j?: number): Poly {
    if (j === undefined) {
      const k = i < 0 ? i + this.entries.length : i;
      if (!Number.isSafeInteger(k) || k < 0 || k >= this.entries.length) throw new RangeError('PolyMatrix index out of range');
      return at(this.entries, k);
    }
    const r = i < 0 ? i + this.rows : i, c = j < 0 ? j + this.cols : j;
    if (!Number.isSafeInteger(r) || !Number.isSafeInteger(c) || r < 0 || r >= this.rows || c < 0 || c >= this.cols) throw new RangeError('PolyMatrix index out of range');
    return at(this.entries, r * this.cols + c);
  }

  /**
   * The submatrix of the given rows and columns.
   *
   * @param rows - Number of rows.
   * @param cols - Number of columns.
   * @returns The submatrix of the given rows and columns.
   */
  extract(rows: readonly number[], cols: readonly number[]): MutablePolyDenseMatrix {
    const entries = rows.flatMap((i) => cols.map((j) => this.get(i, j)));
    return MutablePolyDenseMatrix.create(this.ring, rows.length, cols.length, entries);
  }

  /**
   * The matrix with each polynomial entry converted to an expression.
   *
   * @returns The matrix with each polynomial entry converted to an expression.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.to_Matrix`
   */
  toMatrix(): Matrix {
    return Matrix.fromFunction(this.rows, this.cols, (i, j) => this.get(i, j).asExpr());
  }

  /**
   * The same matrix in other generators.
   *
   * @param gens - Polynomial generators in the desired order.
   * @returns The same matrix in other generators.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.set_gens`
   */
  setGens(gens: PolyMatrixGens): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.fromMatrix(this.toMatrix(), gens);
  }

  private values(): Expr[] { return this.entries.map((p) => p.asExpr()); }

  private static expect(other: unknown, op: string): MutablePolyDenseMatrix {
    if (!(other instanceof MutablePolyDenseMatrix)) throw new TypeError(`unsupported operand for ${op}: PolyMatrix and ${String(other)}`);
    return other;
  }

  private elementwise(otherIn: unknown, op: string, f: (a: Poly, b: Poly) => Poly): MutablePolyDenseMatrix {
    const other = MutablePolyDenseMatrix.expect(otherIn, op);
    if (this.rows !== other.rows || this.cols !== other.cols) throw new RangeError(`PolyMatrix shape mismatch for ${op}`);
    const ring = this.ring.unify(other.ring);
    return this.withEntries(ring, this.rows, this.cols, this.entries.map((a, k) => f(a, at(other.entries, k)).asExpr()));
  }

  /**
   * The sum of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__add__`
   */
  add(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix { return this.elementwise(other, '+', (a, b) => a.add(b)); }
  /**
   * The difference of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The difference of the operands.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__sub__`
   */
  sub(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix { return this.elementwise(other, '-', (a, b) => a.sub(b)); }
  /**
   * The additive inverse.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__neg__`
   */
  neg(): MutablePolyDenseMatrix { return this.withEntries(this.ring, this.rows, this.cols, this.entries.map((p) => p.neg().asExpr())); }

  /**
   * The matrix product, or the product with a scalar in the ring or in a larger domain.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The matrix product, or the product with a scalar in the ring or in a larger domain.
   * @throws RangeError when the inner matrix dimensions differ.
   * @throws TypeError when the operand is neither a compatible matrix nor a supported scalar.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__mul__`
   */
  mul(other: MutablePolyDenseMatrix | ExprLike): MutablePolyDenseMatrix {
    if (other instanceof MutablePolyDenseMatrix) {
      if (this.cols !== other.rows) throw new RangeError('PolyMatrix shape mismatch for *');
      const ring = this.ring.unify(other.ring);
      const values = range(this.rows).flatMap((i) => range(other.cols).map((j) =>
        range(this.cols).reduce((s, k) => s.add(this.get(i, k).mul(other.get(k, j))), ring.element(0)).asExpr()));
      return this.withEntries(ring, this.rows, other.cols, values);
    }
    if (!(other instanceof Expr) && typeof other !== 'number' && typeof other !== 'bigint') throw new TypeError(`unsupported operand for *: PolyMatrix and ${String(other)}`);
    return this.scale(sympify(other));
  }

  private scale(scalar: Expr): MutablePolyDenseMatrix {
    let ring: PolyMatrixRing;
    try {
      this.ring.element(scalar);
      ring = this.ring;
    } catch {
      ring = this.ring.unify(constructDomain([scalar])[0]);
    }
    return this.withEntries(ring, this.rows, this.cols, this.values().map((e) => mul(e, scalar)));
  }

  /**
   * Division by a scalar of the coefficient domain (or a constant polynomial).
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The matrix of polynomial quotients by the scalar.
   * @throws TypeError when the operand is neither a compatible matrix nor a supported scalar.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__truediv__`
   */
  div(other: ExprLike | Poly): MutablePolyDenseMatrix {
    if (!(other instanceof Expr) && !(other instanceof Poly) && typeof other !== 'number' && typeof other !== 'bigint') throw new TypeError(`unsupported operand for /: PolyMatrix and ${String(other)}`);
    const scalar = this.domain.fromSympy(other instanceof Poly ? other.asExpr() : other);
    const inverse = this.domain.fromSympy(pow(scalar, -1));
    return this.withEntries(this.ring, this.rows, this.cols, this.values().map((e) => mul(e, inverse)));
  }

  /**
   * The transposed matrix.
   *
   * @returns The transposed matrix.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.transpose`
   */
  transpose(): MutablePolyDenseMatrix {
    return this.extractAll(range(this.cols).flatMap((j) => range(this.rows).map((i) => this.get(i, j))), this.cols, this.rows);
  }

  private extractAll(entries: readonly Poly[], rows: number, cols: number, ring = this.ring): MutablePolyDenseMatrix {
    return this.withEntries(ring, rows, cols, entries.map((p) => p.asExpr()));
  }

  /**
   * The matrices side by side.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The matrices side by side.
   * @throws RangeError when the row counts differ.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.row_join`
   */
  rowJoin(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix {
    if (this.rows !== other.rows) throw new RangeError('PolyMatrix row_join: the numbers of rows differ');
    const cols = this.cols + other.cols;
    const entries = range(this.rows).flatMap((i) => range(cols).map((j) => j < this.cols ? this.get(i, j) : other.get(i, j - this.cols)));
    return this.extractAll(entries, this.rows, cols, this.ring.unify(other.ring));
  }

  /**
   * The matrices one above the other.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The matrices one above the other.
   * @throws RangeError when the column counts differ.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.col_join`
   */
  colJoin(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix {
    if (this.cols !== other.cols) throw new RangeError('PolyMatrix col_join: the numbers of columns differ');
    return this.extractAll([...this.entries, ...other.entries], this.rows + other.rows, this.cols, this.ring.unify(other.ring));
  }

  /**
   * The matrix of f applied to every entry (as an expression), in the same generators.
   *
   * @param f - Function applied to the arguments.
   * @returns The matrix of f applied to every entry (as an expression), in the same generators.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.applyfunc`
   */
  applyfunc(f: (e: Expr) => ExprLike): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.fromMatrix(this.toMatrix().map((e) => f(e)), this.gens);
  }

  private groundMatrix(what: string): DomainMatrix {
    if (!this.domain.isField || !this.entries.every((p) => p.isGround)) throw new RangeError(`PolyMatrix ${what} is only for ground field elements`);
    const K = this.domain;
    return new DomainMatrix(range(this.rows).map((i) => range(this.cols).map((j) => K.fromSympy(this.get(i, j).asExpr()))), [this.rows, this.cols], K);
  }

  /**
   * The reduced row echelon form over the coefficient field and the pivot columns.
   *
   * @returns The reduced row echelon form over the coefficient field and the pivot columns.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.rref`
   */
  rref(): [MutablePolyDenseMatrix, number[]] {
    const [R, pivots] = this.groundMatrix('rref').rref();
    return [this.withEntries(this.ring, this.rows, this.cols, R.toMatrix().flat()), pivots];
  }

  /**
   * A basis of the nullspace over the coefficient field, as column vectors whose last nonzero entry is 1.
   *
   * @returns A basis of the nullspace over the coefficient field, as column vectors whose last nonzero entry is 1.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.nullspace`
   */
  nullspace(): MutablePolyDenseMatrix[] {
    const basis = this.groundMatrix('nullspace').nullspace({ divideLast: true }).toMatrix();
    return range(basis.rows).map((k) => this.withEntries(this.ring, this.cols, 1, basis.row(k).flat()));
  }

  /**
   * The rank of the matrix.
   *
   * @returns The rank of the matrix.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.rank`
   */
  rank(): number {
    return this.cols - this.nullspace().length;
  }

  /**
   * Equal rings and entries.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.polymatrix.MutablePolyDenseMatrix.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof MutablePolyDenseMatrix && this.ring.equals(other.ring) && this.rows === other.rows && this.cols === other.cols
      && this.entries.every((p, k) => p.asExpr().equals(at(other.entries, k).asExpr()));
  }

  /**
   * The printable representation.
   *
   * @returns The formatted text.
   */
  toString(): string {
    if (!this.rows || !this.cols) return `PolyMatrix(${this.rows}, ${this.cols}, [], ring=${this.ring.toString()})`;
    // SymPy's repr of the Matrix: one row per line, the columns right-aligned
    const rows = range(this.rows).map((i) => range(this.cols).map((j) => str(this.get(i, j).asExpr())));
    const widths = range(this.cols).map((j) => Math.max(...rows.map((r) => at(r, j).length)));
    const body = this.rows === 1 ? `[${at(rows, 0).join(', ')}]` : '\n' + rows.map((r) => `[${r.map((s, j) => s.padStart(at(widths, j))).join(', ')}]`).join(',\n');
    return `PolyMatrix([${body}], ring=${this.ring.toString()})`;
  }
}

export { MutablePolyDenseMatrix as PolyMatrix, MutablePolyDenseMatrix as MutablePolyMatrix };
