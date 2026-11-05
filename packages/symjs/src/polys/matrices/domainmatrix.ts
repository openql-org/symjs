// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/domainmatrix.py; dup_content,
// dup_primitive, dup_clear_denoms and dup_transform of polys/densetools.py,
// _sort_factors of polys/polyutils.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file SymPy DomainMatrix: a matrix whose elements belong to a domain
 * (ZZ, QQ, a polynomial ring, ...), stored densely (DDM) or sparsely
 * (SDM), with exact fraction-free linear algebra: rref, nullspace,
 * determinant, inverse, characteristic polynomial, adjugate, ...
 */

import { NotImplementedError } from '../../core/errors';
import { at, defined, first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Dummy, Rational } from '../../core/nodes';
import { add, mul, pow } from '../../core/ops';
import type { Matrix } from '../../matrices/matrix';
import { MutableDenseMatrix } from '../../matrices/mutable';
import type { Domain } from '../domains';
import { ZZ } from '../domains';
import { EXRAW } from '../domains/expressionrawdomain';
import { Poly } from '../sympoly';
import type { Shape, Slice } from './ddm';
import { DDM } from './ddm';
import { canonicalUnit, cofactors, convertFrom, denom, domainOfExprs, elemEq, elemStr, gcd, hasAssocRing, isNegative, isQQ, isZZ, lcm, quo, rat } from './domainops';
import { DomainScalar } from './domainscalar';
import { DMBadInputError, DMDomainError, DMFormatError, DMNonInvertibleMatrixError, DMNonSquareMatrixError, DMNotAField, DMShapeError } from './exceptions';
import type { RrefMethod } from './rref';
import { dmRref, dmRrefDen } from './rref';
import { SDM } from './sdm';

/** The rows of a dense DomainMatrix or the dict of rows of a sparse one. */
export type DomainMatrixRows = readonly (readonly Expr[])[] | ReadonlyMap<number, ReadonlyMap<number, Expr>>;

/** A characteristic polynomial factor (coefficients from the highest degree) with its multiplicity. */
export type DomainFactor = [Expr[], number];

const isRows = (r: DomainMatrixRows): r is readonly (readonly Expr[])[] => Array.isArray(r);
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);

/**
 * SymPy DomainMatrix: a matrix over a domain, with the dense (DDM) or
 * sparse (SDM) representation in `rep`.
 */
export class DomainMatrix {
  readonly rep: DDM | SDM;

  /** The matrix of a list of rows (dense) or a dict of rows (sparse), optionally converted to the format `fmt`. */
  constructor(rows: DomainMatrixRows | DDM | SDM, shape?: Shape, domain?: Domain, opts: { fmt?: 'dense' | 'sparse' } = {}) {
    if (rows instanceof DDM || rows instanceof SDM) {
      this.rep = rows;
      return;
    }
    const sh = defined(shape, 'shape');
    const K = defined(domain, 'domain');
    let rep: DDM | SDM = isRows(rows) ? new DDM(rows, sh, K) : new SDM(new Map([...rows].map(([i, r]) => [i, new Map(r)] as const)), sh, K);
    if (opts.fmt === 'sparse') rep = rep.toSdm();
    else if (opts.fmt === 'dense') rep = rep.toDdm();
    this.rep = rep;
  }
  get shape(): Shape {
    return this.rep.shape;
  }
  get domain(): Domain {
    return this.rep.domain;
  }

  /** The element at (i, j) as a DomainScalar. */
  getitem(i: number, j: number): DomainScalar {
    return new DomainScalar(this.rep.getitem(i, j), this.domain);
  }
  /** The submatrix of a row and a column index or slice (SymPy M[i, j] with a slice). */
  extractSlice(i: number | Slice, j: number | Slice): DomainMatrix {
    const [m, n] = this.shape;
    const asSlice = (k: number | Slice, size: number, what: string): Slice => {
      if (typeof k !== 'number') return k;
      if (!(-size <= k && k < size)) throw new RangeError(`${what} index out of range`);
      const kk = (k + size) % size;
      return [kk, kk + 1];
    };
    return this.fromRep(this.rep.extractSlice(asSlice(i, m, 'Row'), asSlice(j, n, 'Column')));
  }
  /** The element at (i, j) as an expression. */
  getitemSympy(i: number, j: number): Expr {
    return this.domain.toSympy(this.rep.getitem(i, j));
  }
  /** The submatrix of the given rows and columns. */
  extract(rowslist: readonly number[], colslist: readonly number[]): DomainMatrix {
    return this.fromRep(this.rep.extract(rowslist, colslist));
  }
  /** Set an element in place. */
  setitem(i: number, j: number, value: Expr): void {
    this.rep.setitem(i, j, value);
  }
  /** The DomainMatrix of a DDM or SDM. */
  static fromRep(rep: DDM | SDM): DomainMatrix {
    return new DomainMatrix(rep);
  }
  /** A DomainMatrix of a DDM or SDM (SymPy from_rep called on an instance). */
  fromRep(rep: DDM | SDM): DomainMatrix {
    return new DomainMatrix(rep);
  }
  /** The dense matrix of rows of values converted to the domain. */
  static fromList(rows: readonly (readonly ExprLike[])[], domain: Domain): DomainMatrix {
    const nrows = rows.length;
    const ncols = nrows ? at(rows, 0).length : 0;
    return new DomainMatrix(
      rows.map((row) => row.map((e) => domain.fromSympy(e))),
      [nrows, ncols],
      domain,
    );
  }
  /** The dense matrix of rows of expressions over the domain construct_domain chooses. */
  static fromListSympy(nrows: number, ncols: number, rows: readonly (readonly ExprLike[])[], opts: { field?: boolean } = {}): DomainMatrix {
    if (rows.length !== nrows || rows.some((r) => r.length !== ncols)) throw new DMBadInputError('Inconsistent row-list/shape');
    const [domain, items] = domainOfExprs(rows.flat(), opts);
    return new DomainMatrix(
      range(nrows).map((r) => items.slice(ncols * r, ncols * (r + 1))),
      [nrows, ncols],
      domain,
    );
  }
  /** The sparse matrix of a dict of rows of expressions over the domain construct_domain chooses. */
  static fromDictSympy(nrows: number, ncols: number, elemsdict: ReadonlyMap<number, ReadonlyMap<number, ExprLike>>, opts: { field?: boolean } = {}): DomainMatrix {
    if (![...elemsdict.keys()].every((r) => r >= 0 && r < nrows)) throw new DMBadInputError('Row out of range');
    if (![...elemsdict.values()].every((row) => [...row.keys()].every((c) => c >= 0 && c < ncols))) throw new DMBadInputError('Column out of range');
    const [domain, items] = domainOfExprs([...elemsdict.values()].flatMap((row) => [...row.values()]), opts);
    let idx = 0;
    const dict = new Map([...elemsdict].map(([i, row]) => [i, new Map([...row.keys()].map((j) => [j, at(items, idx++)] as const))] as const));
    return new DomainMatrix(dict, [nrows, ncols], domain);
  }
  /** The DomainMatrix of a Matrix over the domain construct_domain chooses (sparse unless fmt is 'dense'). */
  static fromMatrix(M: Matrix, opts: { fmt?: 'dense' | 'sparse'; field?: boolean } = {}): DomainMatrix {
    const { fmt, ...rest } = opts;
    if (fmt === 'dense') return DomainMatrix.fromListSympy(M.rows, M.cols, M.toArray(), rest);
    return DomainMatrix.fromDictSympy(M.rows, M.cols, M.todod(), rest);
  }
  /** [domain, elements] of expressions (SymPy get_domain: construct_domain). */
  static getDomain(itemsSympy: readonly ExprLike[], opts: { field?: boolean } = {}): [Domain, Expr[]] {
    return domainOfExprs(itemsSympy, opts);
  }
  /** The matrix over the domain construct_domain chooses for its elements. */
  chooseDomain(opts: { field?: boolean } = {}): DomainMatrix {
    const [elements, data] = this.toFlatNz();
    const [dom, elementsDom] = domainOfExprs(
      elements.map((e) => this.domain.toSympy(e)),
      opts,
    );
    return this.fromFlatNz(elementsDom, data, dom);
  }
  copy(): DomainMatrix {
    return this.fromRep(this.rep.copy());
  }
  /** The matrix over another domain. */
  convertTo(K: Domain): DomainMatrix {
    if (K.equals(this.domain)) return this.copy();
    return this.fromRep(this.rep.convertTo(K));
  }
  /** The matrix over EXRAW (its elements as expressions). */
  toSympy(): DomainMatrix {
    return this.convertTo(EXRAW);
  }
  /** The matrix over the field of fractions of the domain. */
  toField(): DomainMatrix {
    return this.convertTo(this.domain.getField());
  }
  toSparse(): DomainMatrix {
    return this.rep instanceof SDM ? this : this.fromRep(this.rep.toSdm());
  }
  toDense(): DomainMatrix {
    return this.rep instanceof DDM ? this : this.fromRep(this.rep.toDdm());
  }
  toDdm(): DDM {
    return this.rep.toDdm();
  }
  toSdm(): SDM {
    return this.rep.toSdm();
  }
  /** The dense representation (python-flint matrices are not used). */
  toDfmOrDdm(): DDM {
    return this.rep.toDfmOrDdm();
  }
  /** The matrices over a common domain and, when fmt is given, in a common format. */
  unify(...others: DomainMatrix[]): DomainMatrix[];
  unify(other: DomainScalar): [DomainMatrix, DomainScalar];
  unify(...others: (DomainMatrix | DomainScalar)[]): (DomainMatrix | DomainScalar)[] {
    const all = [this, ...others];
    if (new Set(all.map((m) => m.domain.toString())).size === 1) return all;
    const domain = all.map((m) => m.domain).reduce((x, y) => x.unify(y));
    return all.map((m) => m.convertTo(domain));
  }
  /** The matrices over a common domain in the format fmt. */
  unifyFmt(others: readonly DomainMatrix[], fmt: 'dense' | 'sparse'): DomainMatrix[] {
    const ms = this.unify(...others);
    if (new Set(ms.map((m) => m.rep.fmt)).size === 1) return ms;
    return ms.map((m) => (fmt === 'sparse' ? m.toSparse() : m.toDense()));
  }
  /** The Matrix of the elements as expressions. */
  toMatrix(): MutableDenseMatrix {
    const [m, n] = this.shape;
    return MutableDenseMatrix.fromFunction(m, n, (i, j) => this.getitemSympy(i, j));
  }
  /** The list of rows. */
  toList(): Expr[][] {
    return this.rep.toList();
  }
  /** The elements row by row. */
  toListFlat(): Expr[] {
    return this.rep.toListFlat();
  }
  /** The dense matrix of a flat list of elements. */
  static fromListFlat(elements: readonly Expr[], shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(DDM.fromListFlat(elements, shape, domain));
  }
  /** The nonzero elements and the data to rebuild the matrix from them. */
  toFlatNz(): [Expr[], [[number, number][], Shape]] {
    return this.rep.toFlatNz();
  }
  /** The matrix (in the format of this one) of nonzero elements and the data of toFlatNz. */
  fromFlatNz(elements: readonly Expr[], data: readonly [readonly (readonly [number, number])[], Shape], domain: Domain): DomainMatrix {
    return this.fromRep(this.rep instanceof SDM ? SDM.fromFlatNz(elements, data, domain) : DDM.fromFlatNz(elements, data, domain));
  }
  /** The nonzero elements as row -> column -> element. */
  toDod(): Map<number, Map<number, Expr>> {
    return this.rep.toDod();
  }
  /** The sparse matrix of a dict of rows. */
  static fromDod(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.fromDod(dod, shape, domain));
  }
  /** A matrix of the shape and format of this one from a dict of rows. */
  fromDodLike(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, domain: Domain = this.domain): DomainMatrix {
    return this.fromRep(this.rep instanceof SDM ? SDM.fromDod(dod, this.shape, domain) : DDM.fromDod(dod, this.shape, domain));
  }
  /** The nonzero elements by position. */
  toDok(): Map<[number, number], Expr> {
    return this.rep.toDok();
  }
  /** The sparse matrix of elements by position. */
  static fromDok(dok: ReadonlyMap<readonly [number, number], Expr>, shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.fromDok(dok, shape, domain));
  }
  iterValues(): Expr[] {
    return this.rep.iterValues();
  }
  iterItems(): [[number, number], Expr][] {
    return this.rep.iterItems();
  }
  /** The number of nonzero elements. */
  nnz(): number {
    return this.rep.nnz();
  }
  /** SymPy repr: DomainMatrix(rows, (m, n), K) with the str of the representation. */
  toString(): string {
    return `DomainMatrix(${this.rep.toString()}, (${this.shape.join(', ')}), ${this.domain.toString()})`;
  }
  transpose(): DomainMatrix {
    return this.fromRep(this.rep.transpose());
  }
  /** The elements row by row. */
  flat(): Expr[] {
    return this.rep.toListFlat();
  }
  get isZeroMatrix(): boolean {
    return this.rep.isZeroMatrix();
  }
  get isUpper(): boolean {
    return this.rep.isUpper();
  }
  get isLower(): boolean {
    return this.rep.isLower();
  }
  get isDiagonal(): boolean {
    return this.rep.isDiagonal();
  }
  /** The diagonal elements. */
  diagonal(): Expr[] {
    return this.rep.diagonal();
  }
  get isSquare(): boolean {
    return this.shape[0] === this.shape[1];
  }
  rank(): number {
    return this.rref()[1].length;
  }
  /** The matrices side by side (in the format of this one). */
  hstack(...B: DomainMatrix[]): DomainMatrix {
    const [A, ...Bs] = this.unifyFmt(B, this.rep.fmt);
    const a = defined(A).rep;
    return new DomainMatrix(a instanceof SDM ? a.hstack(...Bs.map((b) => b.toSdm())) : a.hstack(...Bs.map((b) => b.toDdm())));
  }
  /** The matrices one above the other (dense when the formats differ). */
  vstack(...B: DomainMatrix[]): DomainMatrix {
    const [A, ...Bs] = this.unifyFmt(B, 'dense');
    const a = defined(A).rep;
    return new DomainMatrix(a instanceof SDM ? a.vstack(...Bs.map((b) => b.toSdm())) : a.vstack(...Bs.map((b) => b.toDdm())));
  }
  /** The matrix of func applied to the elements, over the given domain. */
  applyfunc(func: (e: Expr) => Expr, domain: Domain = this.domain): DomainMatrix {
    return this.fromRep(this.rep.applyfunc(func, domain));
  }
  private check(op: string, B: DomainMatrix, ashape: unknown, bshape: unknown): void {
    if (!this.domain.equals(B.domain)) throw new DMDomainError(`Domain mismatch: ${this.domain.toString()} ${op} ${B.domain.toString()}`);
    if (String(ashape) !== String(bshape)) throw new DMShapeError(`Shape mismatch: (${this.shape.join(', ')}) ${op} (${B.shape.join(', ')})`);
    if (this.rep.fmt !== B.rep.fmt) throw new DMFormatError(`Format mismatch: ${this.rep.fmt} ${op} ${B.rep.fmt}`);
  }
  /** The sum (same domain and format). */
  add(B: DomainMatrix): DomainMatrix {
    this.check('+', B, this.shape, B.shape);
    return this.fromRep(this.rep instanceof SDM ? this.rep.add(B.toSdm()) : this.rep.add(B.toDdm()));
  }
  /** The difference (same domain and format). */
  sub(B: DomainMatrix): DomainMatrix {
    this.check('-', B, this.shape, B.shape);
    return this.fromRep(this.rep instanceof SDM ? this.rep.sub(B.toSdm()) : this.rep.sub(B.toDdm()));
  }
  neg(): DomainMatrix {
    return this.fromRep(this.rep.neg());
  }
  /** Multiplication by a domain element on the right. */
  mul(b: Expr): DomainMatrix {
    return this.fromRep(this.rep.mul(b));
  }
  /** Multiplication by a domain element on the left. */
  rmul(b: Expr): DomainMatrix {
    return this.fromRep(this.rep.rmul(b));
  }
  /** The matrix product (same domain and format). */
  matmul(B: DomainMatrix): DomainMatrix {
    this.check('*', B, this.shape[1], B.shape[0]);
    return this.fromRep(this.rep instanceof SDM ? this.rep.matmul(B.toSdm()) : this.rep.matmul(B.toDdm()));
  }
  private scalarmul0(lamda: Expr, reverse: boolean): DomainMatrix {
    const K = this.domain;
    if (elemEq(lamda, K.zero)) return DomainMatrix.zeros(this.shape, K);
    if (elemEq(lamda, K.one)) return this.copy();
    return reverse ? this.rmul(lamda) : this.mul(lamda);
  }
  /** Multiplication by a scalar on the right (zero and one handled directly). */
  scalarmul(lamda: Expr): DomainMatrix {
    return this.scalarmul0(lamda, false);
  }
  /** Multiplication by a scalar on the left. */
  rscalarmul(lamda: Expr): DomainMatrix {
    return this.scalarmul0(lamda, true);
  }
  /** The elementwise product. */
  mulElementwise(B: DomainMatrix): DomainMatrix {
    this.check('*', B, this.shape, B.shape);
    return this.fromRep(this.rep instanceof SDM ? this.rep.mulElementwise(B.toSdm()) : this.rep.mulElementwise(B.toDdm()));
  }
  /** Division by a scalar over the field of fractions (SymPy A / lamda; an integer is a scalar of ZZ). */
  div(lamdaIn: DomainScalar | Expr | number): DomainMatrix {
    let lamda: DomainScalar;
    if (lamdaIn instanceof DomainScalar) lamda = lamdaIn;
    else if (typeof lamdaIn === 'number' || (lamdaIn instanceof Rational && lamdaIn.isInteger)) lamda = new DomainScalar(ZZ.fromSympy(lamdaIn), ZZ);
    else lamda = new DomainScalar(this.domain.getField().fromSympy(lamdaIn), this.domain.getField());
    const [A, l] = this.toField().unify(lamda);
    const K = l.domain;
    if (K.isZero(l.element)) throw new RangeError('division by zero');
    if (K.isOne(l.element)) return A;
    return A.mul(K.quo(K.one, l.element));
  }
  /** A**n for an integer n >= 0 (repeated squaring). */
  pow(n: number): DomainMatrix {
    const [nrows, ncols] = this.shape;
    if (nrows !== ncols) throw new DMNonSquareMatrixError('Power of a nonsquare matrix');
    if (n < 0) throw new NotImplementedError('Negative powers');
    if (n === 0) return DomainMatrix.eye(nrows, this.domain);
    if (n === 1) return this;
    if (n % 2 === 1) return opMul(this, this.pow(n - 1));
    const s = this.pow(n / 2);
    return opMul(s, s);
  }
  /** The strongly connected components of the graph of the nonzero elements. */
  scc(): number[][] {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square for scc');
    return this.rep.scc();
  }
  /** [den, num] with self = num/den and num over the associated ring (with convert) or the domain. */
  clearDenoms(convert = false): [DomainScalar, DomainMatrix] {
    const [elems0, data] = this.toFlatNz();
    const K0 = this.domain;
    const K1 = hasAssocRing(K0) ? K0.getRing() : K0;
    const [den, elems1] = dupClearDenoms(elems0, K0, K1, convert);
    const [Kden, Knum] = convert ? [K1, K1] : [K1, K0];
    return [new DomainScalar(den, Kden), this.fromFlatNz(elems1, data, Knum)];
  }
  /** [den, num] with self = den**-1 * num and den diagonal (one denominator per row). */
  clearDenomsRowwise(convert = false): [DomainMatrix, DomainMatrix] {
    const dod = this.toDod();
    const K0 = this.domain;
    const K1 = hasAssocRing(K0) ? K0.getRing() : K0;
    const diagonals = range(this.shape[0]).map(() => K0.one);
    const dodNum = new Map<number, Map<number, Expr>>();
    for (const [i, rowi] of dod) {
      const [den, elemsNum] = dupClearDenoms([...rowi.values()], K0, K1, convert);
      diagonals[i] = den;
      dodNum.set(i, new Map([...rowi.keys()].map((j, k) => [j, at(elemsNum, k)] as const)));
    }
    const [Kden, Knum] = convert ? [K1, K1] : [K1, K0];
    return [DomainMatrix.diag(diagonals, Kden), this.fromDodLike(dodNum, Knum)];
  }
  /** [M, d] with self/denom = M/d cancelled and d with a canonical sign. */
  cancelDenom(denomIn: Expr): [DomainMatrix, Expr] {
    const K = this.domain;
    let d = denomIn;
    if (K.isZero(d)) throw new RangeError('denominator is zero');
    if (K.isOne(d)) return [this.copy(), d];
    let [elements] = this.toFlatNz();
    const data = this.toFlatNz()[1];
    const u = isNegative(K, d) ? K.neg(K.one) : canonicalUnit(K, d);
    const content = dupContent(elements, K);
    let common = gcd(K, content, d);
    if (!K.isOne(content)) {
      common = gcd(K, content, d);
      if (!K.isOne(common)) {
        elements = dupQuoGround(elements, common, K);
        d = quo(K, d, common);
      }
    }
    if (!K.isOne(u)) {
      elements = elements.map((e) => K.mul(e, u));
      d = K.mul(u, d);
    } else if (K.isOne(common)) return [this.copy(), d];
    return [this.fromFlatNz(elements, data, K), d];
  }
  /** [numerators, denominators] of self/denom cancelled element by element. */
  cancelDenomElementwise(d: Expr): [DomainMatrix, DomainMatrix] {
    const K = this.domain;
    if (K.isZero(d)) throw new RangeError('denominator is zero');
    if (K.isOne(d)) return [this.copy(), DomainMatrix.ones(this.shape, K)];
    const [elements, data] = this.toFlatNz();
    const cof = elements.map((e) => cofactors(K, e, d));
    return [this.fromFlatNz(cof.map((c) => c[1]), data, K), this.fromFlatNz(cof.map((c) => c[2]), data, K)];
  }
  /** The gcd of the elements. */
  content(): Expr {
    return dupContent(this.toFlatNz()[0], this.domain);
  }
  /** [content, self/content]. */
  primitive(): [Expr, DomainMatrix] {
    const K = this.domain;
    const [elements, data] = this.toFlatNz();
    const [content, prims] = dupPrimitive(elements, K);
    return [content, this.fromFlatNz(prims, data, K)];
  }
  /** Reduced row echelon form over the field: [rref, pivots]. */
  rref(opts: { method?: RrefMethod } = {}): [DomainMatrix, number[]] {
    return dmRref(this, opts);
  }
  /** Fraction-free reduced row echelon form: [rref, denominator, pivots]. */
  rrefDen(opts: { method?: RrefMethod; keepDomain?: boolean } = {}): [DomainMatrix, Expr, number[]] {
    return dmRrefDen(this, opts);
  }
  /** A basis of the column space (the pivot columns) over a field. */
  columnspace(): DomainMatrix {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    const [, pivots] = this.rref();
    return this.extract(range(this.shape[0]), pivots);
  }
  /** A basis of the row space (the nonzero rows of the rref) over a field. */
  rowspace(): DomainMatrix {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    const [r, pivots] = this.rref();
    return r.extract(range(pivots.length), range(this.shape[1]));
  }
  /** A basis of the nullspace as rows (with divideLast over a field, the last nonzero element of each is 1). */
  nullspace(opts: { divideLast?: boolean } = {}): DomainMatrix {
    const K = this.domain;
    if (opts.divideLast && !K.isField) throw new DMNotAField('Cannot normalize vectors over a non-field');
    let A: DomainMatrix;
    let pivots: number[];
    if (opts.divideLast) [A, pivots] = this.rref();
    else {
      let den: Expr;
      [A, den, pivots] = this.rrefDen();
      const u = canonicalUnit(K, den);
      if (!K.isOne(u)) A = A.scalarmul(u);
    }
    return A.nullspaceFromRref(pivots);
  }
  /** The nullspace of a matrix in (fraction-free) reduced row echelon form. */
  nullspaceFromRref(pivots?: readonly number[]): DomainMatrix {
    return this.fromRep(this.rep.nullspaceFromRref(pivots)[0]);
  }
  /** The inverse over a field. */
  inv(): DomainMatrix {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    if (!this.isSquare) throw new DMNonSquareMatrixError();
    return this.fromRep(this.rep.inv());
  }
  /** The determinant (fraction-free). */
  det(): Expr {
    if (!this.isSquare) throw new DMNonSquareMatrixError();
    return this.rep.det();
  }
  /** [adjugate, determinant] without division (from the characteristic polynomial). */
  adjDet(): [DomainMatrix, Expr] {
    const m = this.shape[0];
    const I = DomainMatrix.eye([m, m], this.domain);
    const [adjA0, detA] = this.solveDenCharpoly(I, undefined, false);
    return [this.rep instanceof DDM ? adjA0.toDense() : adjA0, detA];
  }
  /** The adjugate (classical adjoint). */
  adjugate(): DomainMatrix {
    return this.adjDet()[0];
  }
  /** [adjugate-like numerator, denominator] of the inverse: self**-1 = num/den. */
  invDen(method?: 'rref' | 'charpoly'): [DomainMatrix, Expr] {
    return this.solveDen(DomainMatrix.eye(this.shape, this.domain), method);
  }
  /** [xnum, xden] with self*xnum = xden*b, without leaving the domain. */
  solveDen(b: DomainMatrix, method: 'rref' | 'charpoly' = 'rref'): [DomainMatrix, Expr] {
    const [m, n] = this.shape;
    if (m !== b.shape[0]) throw new DMShapeError('Matrix equation shape mismatch.');
    if (method === 'charpoly') {
      if (m !== n) throw new DMNonSquareMatrixError("method='charpoly' requires a square matrix.");
      return this.solveDenCharpoly(b);
    }
    return this.solveDenRref(b);
  }
  /** solveDen by fraction-free row reduction of the augmented matrix. */
  solveDenRref(b: DomainMatrix): [DomainMatrix, Expr] {
    const [m, n] = this.shape;
    if (m !== b.shape[0]) throw new DMShapeError('Matrix equation shape mismatch.');
    if (m < n) throw new DMShapeError('Underdetermined matrix equation.');
    const [aRref, den, pivots] = this.hstack(b).rrefDen();
    if (pivots.length !== n || (pivots.length && at(pivots, -1) >= n)) throw new DMNonInvertibleMatrixError('Non-unique solution.');
    return [aRref.extractSlice([null, n], [n, null]), den];
  }
  /** solveDen with the adjugate from the characteristic polynomial: [adj(A)*b, det(A)]. */
  solveDenCharpoly(bIn: DomainMatrix, cp?: readonly Expr[], check = true): [DomainMatrix, Expr] {
    const [, b] = this.unify(bIn);
    const [m, n] = this.shape;
    if (m !== n) throw new DMNonSquareMatrixError('Matrix must be square');
    if (defined(b).shape[0] !== m) throw new DMShapeError('Matrix and vector must have the same number of rows');
    const [f, detA] = this.adjPolyDet(cp);
    if (check && this.domain.isZero(detA)) throw new DMNonInvertibleMatrixError('Matrix is not invertible');
    return [this.evalPolyMul(f, defined(b)), detA];
  }
  /** [p, det(A)] with p(A) = adj(A), from the characteristic polynomial. */
  adjPolyDet(cpIn?: readonly Expr[]): [Expr[], Expr] {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square');
    const cp = cpIn ?? this.charpoly();
    const K = this.domain;
    if (cp.length % 2) return [cp.slice(0, -1).map((c) => K.neg(c)), at(cp, -1)];
    return [cp.slice(0, -1), K.neg(at(cp, -1))];
  }
  /** p(A) for coefficients p from the highest degree (Horner's scheme). */
  evalPoly(p: readonly Expr[]): DomainMatrix {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square');
    if (!p.length) return DomainMatrix.zeros(this.shape, this.domain);
    const I = DomainMatrix.eye(this.shape, this.domain);
    if (p.length === 1) return I.rscalarmul(first(p));
    let pA = I.rscalarmul(first(p));
    for (const pi of p.slice(1)) pA = opAdd(opMul(this, pA), I.rscalarmul(pi));
    return pA;
  }
  /** p(A)*B for coefficients p from the highest degree (Horner's scheme). */
  evalPolyMul(p: readonly Expr[], B: DomainMatrix): DomainMatrix {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square');
    if (B.shape[0] !== this.shape[1]) throw new DMShapeError('Matrices are not aligned');
    if (!this.domain.equals(B.domain)) throw new DMDomainError('Matrices must have the same domain');
    if (!p.length) return DomainMatrix.zeros(B.shape, B.domain);
    let pAB = B.rscalarmul(first(p));
    for (const pi of p.slice(1)) pAB = opAdd(opMul(this, pAB), B.rscalarmul(pi));
    return pAB;
  }
  /** LU decomposition over a field: [L, U, swaps]. */
  lu(): [DomainMatrix, DomainMatrix, [number, number][]] {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    const [L, U, swaps] = this.rep.lu();
    return [this.fromRep(L), this.fromRep(U), swaps];
  }
  /** QR decomposition (Gram-Schmidt with unnormalized columns): [Q, R]. */
  qr(): [DomainMatrix, DomainMatrix] {
    const [Q, R] = this.rep.qr();
    return [this.fromRep(Q), this.fromRep(R)];
  }
  /** Solve self*x = rhs over a field by LU decomposition. */
  luSolve(rhs: DomainMatrix): DomainMatrix {
    if (this.shape[0] !== rhs.shape[0]) throw new DMShapeError('Shape');
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    return this.fromRep(this.rep instanceof SDM ? this.rep.luSolve(rhs.toSdm()) : this.rep.luSolve(rhs.toDdm()));
  }
  /** Fraction-free LU decomposition P*A = L*D**-1*U: [P, L, D, U]. */
  fflu(): [DomainMatrix, DomainMatrix, DomainMatrix, DomainMatrix] {
    const [P, L, D, U] = this.rep.fflu();
    return [this.fromRep(P), this.fromRep(L), this.fromRep(D), this.fromRep(U)];
  }
  /** The characteristic polynomial coefficients from the highest degree. */
  charpoly(): Expr[] {
    const K = this.domain;
    let cp: Expr[] = [K.one];
    for (const [f, mult] of this.charpolyFactorBlocks()) for (let k = 0; k < mult; k++) cp = dupMul(cp, f, K);
    return cp;
  }
  /** The irreducible factors of the characteristic polynomial with their multiplicities. */
  charpolyFactorList(): DomainFactor[] {
    const K = this.domain;
    const out: DomainFactor[] = [];
    for (const [fi, mi] of this.charpolyFactorBlocks()) for (const [fj, mj] of dupFactorList(fi, K)) out.push([fj, mi * mj]);
    return collectFactors(out, K);
  }
  /** The characteristic polynomials of the diagonal blocks (strongly connected components), with multiplicities. */
  charpolyFactorBlocks(): DomainFactor[] {
    if (!this.isSquare) throw new DMNonSquareMatrixError('not square');
    return collectFactors(
      this.scc().map((idx) => [this.extract(idx, idx).charpolyBase(), 1]),
      this.domain,
    );
  }
  /** The characteristic polynomial without the block decomposition (denominators cleared first over QQ). */
  charpolyBase(): Expr[] {
    const K = this.domain;
    const density = this.nnz() / this.shape[0] ** 2;
    let M: DomainMatrix = density < 0.5 ? this.toSparse() : this.toDense();
    if (!(K.isField && hasAssocRing(K))) return M.charpolyBerk();
    const [dS, Mr] = M.clearDenoms(true);
    M = Mr;
    const d = dS.element;
    const cp = M.charpolyBerk().map((c) => convertFrom(K, c, M.domain));
    // cp(x) -> d**-n * cp(d*x): coefficient i divided by d**i
    const dinv = K.quo(K.one, convertFrom(K, d, dS.domain));
    let s = K.one;
    return cp.map((c) => {
      const r = K.mul(c, s);
      s = K.mul(s, dinv);
      return r;
    });
  }
  /** The characteristic polynomial by Berkowitz's algorithm on the representation. */
  charpolyBerk(): Expr[] {
    return this.rep.charpoly();
  }
  /** The identity matrix (sparse). */
  static eye(shape: number | Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.eye(typeof shape === 'number' ? [shape, shape] : shape, domain));
  }
  /** The diagonal matrix of the elements (sparse). */
  static diag(diagonal: readonly Expr[], domain: Domain, shape?: Shape): DomainMatrix {
    return new DomainMatrix(SDM.diag(diagonal, domain, shape));
  }
  /** The zero matrix (sparse). */
  static zeros(shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.zeros(shape, domain));
  }
  /** The matrix of ones (dense). */
  static ones(shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(DDM.ones(shape, domain));
  }
  /** Equal domains, formats and elements. */
  equals(B: unknown): boolean {
    return B instanceof DomainMatrix && this.domain.equals(B.domain) && this.rep.equals(B.rep);
  }
  /** Equal after unifying the domains (formats must agree). */
  unifyEq(B: DomainMatrix): boolean {
    if (String(this.shape) !== String(B.shape)) return false;
    const [A1, B1] = this.unify(B);
    return defined(A1).equals(B1);
  }
}

/** SymPy DM(rows, domain): the dense DomainMatrix of rows of values converted to the domain. */
export function DM(rows: readonly (readonly ExprLike[])[], domain: Domain): DomainMatrix {
  return DomainMatrix.fromList(rows, domain);
}

/** A*B of DomainMatrices (SymPy __mul__: domains unified, dense if the formats differ). */
function opMul(A: DomainMatrix, B: DomainMatrix): DomainMatrix {
  const [a, b] = A.unifyFmt([B], 'dense');
  return defined(a).matmul(defined(b));
}

/** A+B of DomainMatrices (SymPy __add__). */
function opAdd(A: DomainMatrix, B: DomainMatrix): DomainMatrix {
  const [a, b] = A.unifyFmt([B], 'dense');
  return defined(a).add(defined(b));
}

// ---- dense univariate polynomial helpers (densearith, densetools, factortools) ----

/** SymPy dup_mul. */
function dupMul(f: readonly Expr[], g: readonly Expr[], K: Domain): Expr[] {
  const out = Array.from({ length: f.length + g.length - 1 }, () => K.zero);
  f.forEach((a, i) => g.forEach((b, j) => (out[i + j] = K.add(at(out, i + j), K.mul(a, b)))));
  return out;
}

/** SymPy dup_content: the gcd of the coefficients. */
function dupContent(f: readonly Expr[], K: Domain): Expr {
  let cont = K.zero;
  for (const c of f) {
    cont = gcd(K, cont, c);
    if (!isQQ(K) && K.isOne(cont)) break;
  }
  return cont;
}

/** SymPy dup_quo_ground: f // c (exact division in a field). */
function dupQuoGround(f: readonly Expr[], c: Expr, K: Domain): Expr[] {
  return f.map((cf) => (K.isField ? K.quo(cf, c) : quo(K, cf, c)));
}

/** SymPy dup_primitive: [content, f/content]. */
function dupPrimitive(f: readonly Expr[], K: Domain): [Expr, Expr[]] {
  if (!f.length) return [K.zero, []];
  const cont = dupContent(f, K);
  return K.isOne(cont) ? [cont, [...f]] : [cont, dupQuoGround(f, cont, K)];
}

/** SymPy dup_clear_denoms: [common denominator, f times it] (converted to the ring K1 with convert). */
function dupClearDenoms(f: readonly Expr[], K0: Domain, K1: Domain, convert: boolean): [Expr, Expr[]] {
  let common = K1.one;
  for (const c of f) common = lcm(K1, common, denom(K0, c));
  const g = K1.isOne(common) ? [...f] : f.map((c) => K0.mul(c, convertFrom(K0, common, K1)));
  return [common, convert ? g.map((c) => convertFrom(K1, c, K0)) : g];
}

/** SymPy dup_factor_list over ZZ or QQ: the factors (primitive over ZZ, with a positive leading coefficient) and multiplicities. */
function dupFactorList(f: readonly Expr[], K: Domain): DomainFactor[] {
  if (!(isZZ(K) || isQQ(K))) throw new NotImplementedError(`factorization over ${K.toString()}`);
  const x = new Dummy('x');
  const n = f.length - 1;
  const [, Fz] = dupClearDenoms(f, K, ZZ, true);
  const e = add(...Fz.map((c, i) => mul(c, pow(x, n - i))));
  const [, factors] = Poly.from(e, [x], { domain: 'ZZ' }).factorList();
  return factors.map(([p, k]) => [p.allCoeffs().map((c) => K.fromSympy(c)), k]);
}

/** Lexicographic order of two different coefficient lists of ZZ or QQ of the same length. */
function cmpCoeffs(a: readonly Expr[], b: readonly Expr[]): number {
  // the lists have the same length and differ (equal factors were merged)
  const i = a.findIndex((c, k) => !elemEq(c, at(b, k)));
  const [x, y] = [rat(at(a, i)), rat(at(b, i))];
  return x.p * y.q < y.p * x.q ? -1 : 1;
}

/** SymPy _collect_factors: equal factors merged (multiplicities added), sorted by (degree, multiplicity, coefficients). */
function collectFactors(factors: readonly DomainFactor[], K: Domain): DomainFactor[] {
  const out: DomainFactor[] = [];
  for (const [f, e] of factors) {
    const key = f.map((c) => elemStr(K, c)).join(',');
    const found = out.find(([g]) => g.map((c) => elemStr(K, c)).join(',') === key);
    if (found) found[1] += e;
    else out.push([[...f], e]);
  }
  return out.sort((a, b) => a[0].length - b[0].length || a[1] - b[1] || cmpCoeffs(a[0], b[0]));
}
