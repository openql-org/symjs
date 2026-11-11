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

export type PolyMatrixEntry = ExprLike | Poly;
/** The generators of a polynomial matrix: one generator or a list of them (SymPy's tuple). */
export type PolyMatrixGens = Expr | readonly Expr[];
export interface PolyMatrixOptions { ring?: PolyMatrixRing | Domain | string }
/** SymPy PolyMatrix(rows, cols, lambda i, j: ...): the entry in row i and column j. */
export type PolyMatrixEntryFunction = (i: number, j: number) => PolyMatrixEntry;
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
  readonly gens: readonly Expr[];
  constructor(readonly domain: Domain, gens: PolyMatrixGens) {
    this.gens = gens instanceof Expr ? [gens] : [...gens];
  }
  /** A ring given as a PolyMatrixRing, a polynomial ring domain or a string such as 'QQ[x]' or 'QQ[x][y]'. */
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
  /** The element of the ring of an expression or a polynomial; throws CoercionFailed when it is not one. */
  element(e: PolyMatrixEntry): Poly {
    const p = Poly.from(e instanceof Poly ? e.asExpr() : e, this.gens, { domain: this.domain.toString() });
    for (const c of p.coeffs()) this.domain.fromSympy(c);
    return p;
  }
  /** The smallest ring containing this one and another ring or coefficient domain. */
  unify(other: PolyMatrixRing | Domain): PolyMatrixRing {
    const o = other instanceof PolyMatrixRing ? other : other.symbols.length && !other.isField ? new PolyMatrixRing(other.dom, other.symbols) : new PolyMatrixRing(other, []);
    const gens = [...this.gens];
    for (const g of o.gens) if (!gens.some((h) => h.key === g.key)) gens.push(g);
    return new PolyMatrixRing(this.domain.unify(o.domain), gens);
  }
  equals(other: unknown): boolean {
    return other instanceof PolyMatrixRing && this.toString() === other.toString();
  }
  toString(): string {
    return `${this.domain.toString()}[${this.gens.map((g) => str(g)).join(',')}]`;
  }
}

/** A dense matrix of polynomials in a common polynomial ring (SymPy PolyMatrix). */
export class MutablePolyDenseMatrix implements Iterable<Poly> {
  readonly ring: PolyMatrixRing;
  private readonly nrows: number;
  private readonly ncols: number;
  private readonly entries: readonly Poly[];

  /**
   * SymPy PolyMatrix(...): from a list of rows, a list of entries (a column)
   * or rows, columns and a list or function of the entries, followed by the
   * generators; the ring option fixes the polynomial ring.
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

  /** The matrix of rows x cols entries over the given ring, or over the ring of their polynomials (SymPy from_list). */
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

  /** The matrix of a DomainMatrix over a polynomial ring (SymPy from_dm). */
  static fromDm(dm: DomainMatrix): MutablePolyDenseMatrix {
    const [rows, cols] = dm.shape;
    const ring = PolyMatrixRing.of(dm.domain);
    return MutablePolyDenseMatrix.create(ring, rows, cols, dm.toMatrix().flat().map((e) => ring.element(e)));
  }

  /** The polynomial matrix of a Matrix in the given generators or ring (SymPy from_Matrix). */
  static fromMatrix(other: Matrix, ...args: (Expr | readonly Expr[] | PolyMatrixOptions)[]): MutablePolyDenseMatrix {
    return new MutablePolyDenseMatrix(other.rows, other.cols, other.flat(), ...args);
  }

  /** The identity matrix over QQ[gens]. */
  static eye(n: number, gens: PolyMatrixGens): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.fromDmOver(Matrix.eye(n), gens);
  }

  /** The zero matrix over QQ[gens]. */
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

  get rows(): number { return this.nrows; }
  get cols(): number { return this.ncols; }
  get shape(): [number, number] { return [this.rows, this.cols]; }
  /** The coefficient domain of the ring. */
  get domain(): Domain { return this.ring.domain; }
  get gens(): readonly Expr[] { return this.ring.gens; }
  /** The number of entries (Python len). */
  get length(): number { return this.entries.length; }
  *[Symbol.iterator](): Iterator<Poly> { yield* this.entries; }
  /** The entries in row-major order. */
  flat(): Poly[] { return [...this.entries]; }

  /** The entry at row i and column j, or the entry at the row-major index i (negative indices count from the end). */
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

  /** The submatrix of the given rows and columns. */
  extract(rows: readonly number[], cols: readonly number[]): MutablePolyDenseMatrix {
    const entries = rows.flatMap((i) => cols.map((j) => this.get(i, j)));
    return MutablePolyDenseMatrix.create(this.ring, rows.length, cols.length, entries);
  }

  toMatrix(): Matrix {
    return Matrix.fromFunction(this.rows, this.cols, (i, j) => this.get(i, j).asExpr());
  }

  /** The same matrix in other generators (SymPy set_gens). */
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

  add(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix { return this.elementwise(other, '+', (a, b) => a.add(b)); }
  sub(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix { return this.elementwise(other, '-', (a, b) => a.sub(b)); }
  neg(): MutablePolyDenseMatrix { return this.withEntries(this.ring, this.rows, this.cols, this.entries.map((p) => p.neg().asExpr())); }

  /** The matrix product, or the product with a scalar in the ring or in a larger domain. */
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

  /** Division by a scalar of the coefficient domain (or a constant polynomial). */
  div(other: ExprLike | Poly): MutablePolyDenseMatrix {
    if (!(other instanceof Expr) && !(other instanceof Poly) && typeof other !== 'number' && typeof other !== 'bigint') throw new TypeError(`unsupported operand for /: PolyMatrix and ${String(other)}`);
    const scalar = this.domain.fromSympy(other instanceof Poly ? other.asExpr() : other);
    const inverse = this.domain.fromSympy(pow(scalar, -1));
    return this.withEntries(this.ring, this.rows, this.cols, this.values().map((e) => mul(e, inverse)));
  }

  transpose(): MutablePolyDenseMatrix {
    return this.extractAll(range(this.cols).flatMap((j) => range(this.rows).map((i) => this.get(i, j))), this.cols, this.rows);
  }

  private extractAll(entries: readonly Poly[], rows: number, cols: number, ring = this.ring): MutablePolyDenseMatrix {
    return this.withEntries(ring, rows, cols, entries.map((p) => p.asExpr()));
  }

  /** The matrices side by side. */
  rowJoin(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix {
    if (this.rows !== other.rows) throw new RangeError('PolyMatrix row_join: the numbers of rows differ');
    const cols = this.cols + other.cols;
    const entries = range(this.rows).flatMap((i) => range(cols).map((j) => j < this.cols ? this.get(i, j) : other.get(i, j - this.cols)));
    return this.extractAll(entries, this.rows, cols, this.ring.unify(other.ring));
  }

  /** The matrices one above the other. */
  colJoin(other: MutablePolyDenseMatrix): MutablePolyDenseMatrix {
    if (this.cols !== other.cols) throw new RangeError('PolyMatrix col_join: the numbers of columns differ');
    return this.extractAll([...this.entries, ...other.entries], this.rows + other.rows, this.cols, this.ring.unify(other.ring));
  }

  /** The matrix of f applied to every entry (as an expression), in the same generators. */
  applyfunc(f: (e: Expr) => ExprLike): MutablePolyDenseMatrix {
    return MutablePolyDenseMatrix.fromMatrix(this.toMatrix().map((e) => f(e)), this.gens);
  }

  private groundMatrix(what: string): DomainMatrix {
    if (!this.domain.isField || !this.entries.every((p) => p.isGround)) throw new RangeError(`PolyMatrix ${what} is only for ground field elements`);
    const K = this.domain;
    return new DomainMatrix(range(this.rows).map((i) => range(this.cols).map((j) => K.fromSympy(this.get(i, j).asExpr()))), [this.rows, this.cols], K);
  }

  /** The reduced row echelon form over the coefficient field and the pivot columns. */
  rref(): [MutablePolyDenseMatrix, number[]] {
    const [R, pivots] = this.groundMatrix('rref').rref();
    return [this.withEntries(this.ring, this.rows, this.cols, R.toMatrix().flat()), pivots];
  }

  /** A basis of the nullspace over the coefficient field, as column vectors whose last nonzero entry is 1. */
  nullspace(): MutablePolyDenseMatrix[] {
    const basis = this.groundMatrix('nullspace').nullspace({ divideLast: true }).toMatrix();
    return range(basis.rows).map((k) => this.withEntries(this.ring, this.cols, 1, basis.row(k).flat()));
  }

  rank(): number {
    return this.cols - this.nullspace().length;
  }

  /** Equal rings and entries. */
  equals(other: unknown): boolean {
    return other instanceof MutablePolyDenseMatrix && this.ring.equals(other.ring) && this.rows === other.rows && this.cols === other.cols
      && this.entries.every((p, k) => p.asExpr().equals(at(other.entries, k).asExpr()));
  }

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
