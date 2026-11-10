// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/modules.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Modules over ZZ inside number fields (SymPy
 * sympy.polys.numberfields.modules): the power basis of an algebraic
 * integer theta (`PowerBasis`), its submodules (`Submodule`, e.g. orders
 * and ideals, kept as a matrix in Hermite normal form over a denominator),
 * their elements (`ModuleElement`, `PowerBasisElement`), module
 * homomorphisms and endomorphism rings, and `findMinPoly`.
 *
 * Coefficients and denominators are bigints; the column of an element and
 * the matrix of a submodule are DomainMatrix objects over ZZ, as in SymPy.
 */

import { NotImplementedError } from '../../core/errors';
import { at, defined, first, getOrThrow } from '../../core/guard';
import type { Expr, Sym } from '../../core/nodes';
import { Dummy, Rational } from '../../core/nodes';
import { add, mul, pow } from '../../core/ops';
import { igcd, ilcm } from '../../core/numberutils';
import { NoMatch, isNoMatch, type NoMatchResult } from '../../core/truth';
import { fdiv } from '../../ntheory/intutil';
import { str } from '../../printing/str';
import { QQ, ZZ } from '../domains';
import type { Domain } from '../domains';
import type { AlgebraicField } from '../domains/algebraicfield';
import { FiniteField, GF } from '../domains/finitefield';
import { PythonMPQ } from '../domains/pythonrational';
import { DomainMatrix } from '../matrices/domainmatrix';
import { rat } from '../matrices/domainops';
import { DomainScalar } from '../matrices/domainscalar';
import { hermiteNormalForm } from '../matrices/normalforms';
import type { AlgebraicNumber } from '../numberfields';
import { ANP } from '../polyclasses';
import { UnificationFailed } from '../polyerrors';
import { Poly } from '../sympoly';
import { ClosureFailure, MissingUnityError, StructureError } from './exceptions';
import { AlgIntPowers, getNumDenom, isRat, type RationalLike } from './utilities';

/** A multiplication table: M.get(u).get(v) (v >= u) is the product of the u-th and v-th basis elements in the basis. */
export type MultTab = Map<number, Map<number, bigint[]>>;

/** Options of the operations that put a matrix in Hermite normal form. */
export interface HnfOptions {
  /** Put the matrix in Hermite normal form (default true). */
  hnf?: boolean;
  /** A positive multiple of the determinant of the matrix, to compute the form modulo it. */
  hnfModulus?: bigint | number;
}

const int = (e: Expr): bigint => rat(e).p;
const ints = (M: DomainMatrix): bigint[] => M.flat().map(int);
const zz = (n: bigint): Expr => Rational.of(n);

/** The product A*B of DomainMatrices over a common domain, dense when the formats differ (SymPy A * B). */
export function dmMul(A: DomainMatrix, B: DomainMatrix): DomainMatrix {
  const [a, b] = A.unifyFmt([B], 'dense');
  return defined(a).matmul(defined(b));
}

/** The matrix times an integer (SymPy M * a and a * M). */
const times = (M: DomainMatrix, a: bigint): DomainMatrix => M.scalarmul(zz(a));

/**
 * A particular solution x (a row) of A*x = b over a field (SymPy
 * DomainMatrix._solve(b)[0]), or undefined when there is none (SymPy raises
 * DMBadInputError: its SDM constructor rejects the particular solution of an
 * inconsistent system, which has a pivot in the column of b).
 */
function particularSolution(A: DomainMatrix, b: DomainMatrix): DomainMatrix | undefined {
  const [R, pivots] = A.hstack(b).rref();
  if (pivots.includes(A.shape[1])) return undefined;
  return R.fromRep(R.rep.particular());
}

/** The column vector of integers (SymPy to_col). */
export function toCol(coeffs: readonly (bigint | number)[]): DomainMatrix {
  return new DomainMatrix([coeffs.map((c) => zz(BigInt(c)))], [1, coeffs.length], ZZ).transpose();
}

/**
 * A module over ZZ: a power basis or a submodule of another module (SymPy
 * Module). A module's elements are made with `call` (SymPy `M(spec, denom)`).
 */
export abstract class Module {
  /** The number of basis elements. */
  abstract get n(): number;
  /** The multiplication table of the basis elements. */
  abstract multTab(): MultTab;
  /** The module this one is a submodule of (undefined for a power basis). */
  abstract get parent(): Module | undefined;
  /** The coordinates of an element in this module's basis, as a column over ZZ; throws ClosureFailure. */
  abstract represent(elt: ModuleElement): DomainMatrix;
  /** The first basis element is 1. */
  abstract startsWithUnity(): boolean;
  /** The element of this module (or of an ancestor) equal to a rational number. */
  abstract elementFromRational(a: RationalLike): ModuleElement;
  /** SymPy ==. */
  abstract equals(other: unknown): boolean;
  /** SymPy repr. */
  abstract toString(): string;

  /** The modules of the chain of parents, from the power basis down (and this one with includeSelf). */
  ancestors(includeSelf = false): Module[] {
    const c = this.parent;
    const a = c === undefined ? [] : c.ancestors(true);
    if (includeSelf) a.push(this);
    return a;
  }
  /** The power basis at the root of the chain of parents. */
  abstract powerBasisAncestor(): PowerBasis;
  /** The last module both chains of ancestors share, or NoMatch. */
  nearestCommonAncestor(other: Module): Module | NoMatchResult {
    const sA = this.ancestors(true);
    const oA = other.ancestors(true);
    let nca: Module | NoMatchResult = NoMatch;
    for (let i = 0; i < Math.min(sA.length, oA.length); i++) {
      if (!at(sA, i).equals(at(oA, i))) break;
      nca = at(sA, i);
    }
    return nca;
  }
  /** The number field of the power basis at the root, if it was made from one. */
  get numberField(): AlgebraicField | undefined {
    return this.powerBasisAncestor().K;
  }
  /** A column vector over ZZ of length n. */
  isCompatCol(col: unknown): col is DomainMatrix {
    return col instanceof DomainMatrix && col.shape[0] === this.n && col.shape[1] === 1 && col.domain.equals(ZZ);
  }
  /**
   * The element with the coordinates of a column over ZZ divided by denom,
   * or the j-th basis element for an integer j (SymPy `M(spec, denom)`).
   */
  call(specIn: number | DomainMatrix, denom: bigint | number = 1n): ModuleElement {
    const spec = typeof specIn === 'number' && specIn >= 0 && specIn < this.n ? DomainMatrix.eye(this.n, ZZ).extractSlice([0, this.n], [specIn, specIn + 1]).toDense() : specIn;
    if (!this.isCompatCol(spec)) throw new RangeError('Compatible column vector required.');
    return makeModElt(this, spec, BigInt(denom));
  }
  /** The basis elements. */
  basisElements(): ModuleElement[] {
    return Array.from({ length: this.n }, (_, j) => this.call(j));
  }
  /** The zero element. */
  zero(): ModuleElement {
    return this.call(0).mul(0);
  }
  /** The unity element. */
  one(): ModuleElement {
    return this.elementFromRational(1);
  }
  /** The submodule generated by elements of this module (in Hermite normal form unless hnf is false). */
  submoduleFromGens(gens: readonly ModuleElement[], opts: HnfOptions = {}): Submodule {
    if (!gens.every((g) => g.module.equals(this))) throw new RangeError('Generators must belong to this module.');
    if (gens.length === 0) throw new RangeError('Need at least one generator.');
    const m = first(gens).n;
    const d = gens.length === 1 ? first(gens).denom : ilcm(...gens.map((g) => g.denom));
    let B = DomainMatrix.zeros([m, 0], ZZ).hstack(...gens.map((g) => g.col.rscalarmul(zz(d / g.denom))));
    if (opts.hnf ?? true) B = hermiteNormalForm(B, opts.hnfModulus === undefined ? {} : { D: opts.hnfModulus });
    return this.submoduleFromMatrix(B, d);
  }
  /** The submodule whose basis elements are the columns of a matrix over ZZ divided by denom. */
  submoduleFromMatrix(B: DomainMatrix, denom: bigint | number = 1n): Submodule {
    if (!B.domain.equals(ZZ)) throw new RangeError('Matrix must be over ZZ.');
    if (B.shape[0] !== this.n) throw new RangeError('Matrix row count must match base module.');
    return new Submodule(this, B, denom);
  }
  /** This module as a submodule of itself. */
  wholeSubmodule(): Submodule {
    return this.submoduleFromMatrix(DomainMatrix.eye(this.n, ZZ));
  }
  /** The ring of endomorphisms of this module. */
  endomorphismRing(): EndomorphismRing {
    return new EndomorphismRing(this);
  }
}

const isMonicOverZZ = (T: Poly): boolean => T.allCoeffs().every((c) => c instanceof Rational && c.q === 1n) && T.LC().equals(1);

/**
 * The power basis 1, theta, ..., theta**(n-1) of the ring ZZ[theta] for a
 * root theta of a monic irreducible polynomial T over ZZ, or of the
 * primitive element of a number field (SymPy PowerBasis).
 *
 * For a field whose primitive element is not an algebraic integer (its
 * minimal polynomial is not monic over ZZ) SymPy builds a power basis of a
 * non-monic polynomial, whose multiplication table is wrong (QQ<sqrt(2)/3>
 * gets the discriminant 0). Here the root is scaled first: the basis is
 * that of theta' = scale*theta, whose minimal polynomial T is monic over ZZ
 * (Poly.makeMonicOverIntegersByScalingRoots), and the conversions to and
 * from the field's elements account for the scale.
 */
export class PowerBasis extends Module {
  /** The number field, when the basis was made from one. */
  readonly K: AlgebraicField | undefined;
  /** The monic polynomial over ZZ of the generator. */
  readonly T: Poly;
  /** The generator of the basis is scale times the primitive element of the field. */
  readonly scale: bigint;
  /** The minimal polynomial of the field's primitive element (T unless scaled). */
  private readonly fieldPoly: Poly;
  private readonly degree: number;
  private multTable: MultTab | undefined;
  constructor(TIn: Poly | AlgebraicField) {
    super();
    let T0: Poly;
    if (TIn instanceof Poly) {
      this.K = undefined;
      T0 = TIn;
      // SymPy accepts any polynomial; the multiplication table needs a monic one
      if (!isMonicOverZZ(T0)) throw new RangeError('PowerBasis requires a monic polynomial over ZZ.');
    } else {
      this.K = TIn;
      T0 = TIn.ext.minpolyOfElement();
    }
    if (isMonicOverZZ(T0)) {
      this.T = Poly.from(T0.asExpr(), T0.gens, { domain: 'ZZ', pure: T0.pure });
      this.scale = 1n;
    } else {
      const [T, c] = T0.makeMonicOverIntegersByScalingRoots();
      this.T = T;
      this.scale = int(c);
    }
    this.fieldPoly = T0;
    this.degree = this.T.degree();
  }
  get numberField(): AlgebraicField | undefined {
    return this.K;
  }
  get parent(): undefined {
    return undefined;
  }
  powerBasisAncestor(): PowerBasis {
    return this;
  }
  /** SymPy repr: PowerBasis(x**2 - 5). */
  toString(): string {
    return `PowerBasis(${str(this.T.asExpr())})`;
  }
  equals(other: unknown): boolean {
    return other instanceof PowerBasis && this.T.equals(other.T);
  }
  get n(): number {
    return this.degree;
  }
  multTab(): MultTab {
    this.multTable ??= this.buildMultTab();
    return this.multTable;
  }
  /** Compute the multiplication table from the powers of theta. */
  computeMultTab(): void {
    this.multTable = this.buildMultTab();
  }
  private buildMultTab(): MultTab {
    const thetaPow = new AlgIntPowers(this.T);
    const M: MultTab = new Map();
    const n = this.n;
    for (let u = 0; u < n; u++) {
      const row = new Map<number, bigint[]>();
      for (let v = u; v < n; v++) row.set(v, thetaPow.get(u + v));
      M.set(u, row);
    }
    return M;
  }
  /** The coordinates of an element of this power basis without denominator; throws ClosureFailure otherwise. */
  represent(elt: ModuleElement): DomainMatrix {
    if (elt.module.equals(this) && elt.denom === 1n) return elt.column();
    throw new ClosureFailure('Element not representable in ZZ[theta].');
  }
  startsWithUnity(): boolean {
    return true;
  }
  elementFromRational(a: RationalLike): PowerBasisElement {
    return asPowerBasisElement(this, this.call(0).mul(a));
  }
  override call(spec: number | DomainMatrix, denom: bigint | number = 1n): PowerBasisElement {
    return asPowerBasisElement(this, super.call(spec, denom));
  }
  override zero(): PowerBasisElement {
    return asPowerBasisElement(this, super.zero());
  }
  /** The element of a polynomial in theta with rational coefficients (reduced modulo T). */
  elementFromPoly(fIn: Poly): PowerBasisElement {
    const n = this.n;
    const f = fIn.degree() >= n ? fIn.rem(this.T) : fIn;
    if (f.isZero) return this.zero();
    // SymPy dup_clear_denoms: the lcm of the denominators and the integer coefficients
    const cs = f.allCoeffs().map(rat);
    const d = ilcm(...cs.map((c) => c.q));
    const c = cs.map((x) => (x.p * d) / x.q).reverse();
    return this.call(toCol([...c, ...Array.from({ length: n - c.length }, () => 0n)]), d);
  }
  /** The coefficients (lowest power first) of an element in powers of the field's primitive element, from those in powers of the generator. */
  toFieldCoeffs(coeffs: readonly Rational[]): Rational[] {
    return coeffs.map((c, i) => Rational.of(c.p * this.scale ** BigInt(i), c.q));
  }
  /** The polynomial (highest coefficient first) defining the field's primitive element. */
  fieldMod(): Expr[] {
    return this.fieldPoly.allCoeffs();
  }
  private elementFromRepAndMod(rep: readonly Rational[], mod: readonly Expr[]): PowerBasisElement {
    const own = this.fieldMod();
    if (mod.length !== own.length || mod.some((c, i) => !c.equals(at(own, i)))) throw new UnificationFailed('Element does not appear to be in the same field.');
    const k = rep.length;
    const coeffs = rep.map((c, i) => Rational.of(c.p, c.q * this.scale ** BigInt(k - 1 - i)));
    const x = first(this.T.gens);
    return this.elementFromPoly(Poly.from(add(...coeffs.map((c, i) => mul(c, pow(x, k - 1 - i)))), [x], { domain: 'QQ' }));
  }
  /** The element of an element of the field (SymPy element_from_ANP). */
  elementFromANP(a: ANP): PowerBasisElement {
    return this.elementFromRepAndMod(
      a.toList().map((c) => Rational.of(c.numerator, c.denominator)),
      a.mod.map((c) => Rational.of(c.numerator, c.denominator)),
    );
  }
  /** The element of an algebraic number of the field (SymPy element_from_alg_num). */
  elementFromAlgNum(a: AlgebraicNumber): PowerBasisElement {
    return this.elementFromRepAndMod(a.coeffs().map(rat), a.minpoly().allCoeffs());
  }
}

/**
 * A submodule of a module: the ZZ-span of the columns of a matrix over ZZ
 * divided by a denominator (SymPy Submodule). It prints as
 * `Submodule[[2, 0], [1, 1]]/2` (the basis elements as rows).
 */
export class Submodule extends Module {
  private readonly parentModule: Module;
  private readonly mat: DomainMatrix;
  private readonly den: bigint;
  private multTable: MultTab | undefined;
  private readonly cols: number;
  private qqMatrix: DomainMatrix | undefined;
  private startsWithOne: boolean | undefined;
  private sqMaxrankHNF: boolean | undefined;
  constructor(parent: Module, matrix: DomainMatrix, denom: bigint | number = 1n, multTab?: MultTab) {
    super();
    this.parentModule = parent;
    this.mat = matrix;
    this.den = BigInt(denom);
    this.multTable = multTab;
    this.cols = matrix.shape[1];
  }
  /** SymPy repr: Submodule[[2, 0], [1, 1]]/2. */
  toString(): string {
    const rows = this.matrix.transpose().toList().map((r) => `[${r.map((e) => String(int(e))).join(', ')}]`);
    return `Submodule[${rows.join(', ')}]${this.den > 1n ? `/${this.den}` : ''}`;
  }
  /** The same submodule with the gcd of the denominator and the coefficients cancelled. */
  reduced(): Submodule {
    if (this.den === 1n) return this;
    const g = igcd(this.den, ...this.coeffs);
    if (g === 1n) return this;
    return new Submodule(this.parent, this.matrix.div(zz(g)).convertTo(ZZ), this.den / g, this.multTable);
  }
  /** The submodule spanned by the basis elements from the r-th on (keeping the multiplication table). */
  discardBefore(r: number): Submodule {
    const W = this.matrix.extractSlice([0, this.matrix.shape[0]], [r, this.n]);
    const s = this.n - r;
    const mt = this.multTable;
    let M: MultTab | undefined;
    if (mt !== undefined) {
      M = new Map();
      for (let u = 0; u < s; u++) {
        const row = new Map<number, bigint[]>();
        for (let v = u; v < s; v++) row.set(v, getOrThrow(getOrThrow(mt, r + u), r + v).slice(r));
        M.set(u, row);
      }
    }
    return new Submodule(this.parent, W, this.den, M);
  }
  get n(): number {
    return this.cols;
  }
  multTab(): MultTab {
    this.multTable ??= this.buildMultTab();
    return this.multTable;
  }
  /** Compute the multiplication table by representing the products of the basis elements. */
  computeMultTab(): void {
    this.multTable = this.buildMultTab();
  }
  private buildMultTab(): MultTab {
    const gens = this.basisElementPullbacks();
    const M: MultTab = new Map();
    const n = this.n;
    for (let u = 0; u < n; u++) {
      const row = new Map<number, bigint[]>();
      for (let v = u; v < n; v++) row.set(v, ints(this.represent(at(gens, u).mul(at(gens, v)))));
      M.set(u, row);
    }
    return M;
  }
  get parent(): Module {
    return this.parentModule;
  }
  powerBasisAncestor(): PowerBasis {
    return this.parent.powerBasisAncestor();
  }
  /** The matrix over ZZ whose columns (over the denominator) are the basis elements. */
  get matrix(): DomainMatrix {
    return this.mat;
  }
  /** The entries of the matrix, row by row. */
  get coeffs(): bigint[] {
    return ints(this.matrix);
  }
  get denom(): bigint {
    return this.den;
  }
  /** The matrix over QQ of the basis elements: matrix/denom (SymPy QQ_matrix). */
  get QQMatrix(): DomainMatrix {
    this.qqMatrix ??= this.matrix.div(zz(this.den)).toDense();
    return this.qqMatrix;
  }
  startsWithUnity(): boolean {
    this.startsWithOne ??= this.call(0).equiv(1);
    return this.startsWithOne;
  }
  /** The matrix is square, of maximal rank and in Hermite normal form. */
  isSqMaxrankHNF(): boolean {
    this.sqMaxrankHNF ??= isSqMaxrankHNF(this.mat);
    return this.sqMaxrankHNF;
  }
  /**
   * Record properties already known to hold, so they are not recomputed
   * (SymPy sets _starts_with_unity and _is_sq_maxrank_HNF).
   * @internal
   */
  presetProperties(startsWithUnity: boolean, sqMaxrankHNF: boolean): void {
    this.startsWithOne = startsWithUnity;
    this.sqMaxrankHNF = sqMaxrankHNF;
  }
  /** The parent is a power basis. */
  isPowerBasisSubmodule(): boolean {
    return this.parent instanceof PowerBasis;
  }
  elementFromRational(a: RationalLike): ModuleElement {
    if (this.startsWithUnity()) return this.call(0).mul(a);
    return this.parent.elementFromRational(a);
  }
  /** The basis elements as elements of the parent. */
  basisElementPullbacks(): ModuleElement[] {
    return this.basisElements().map((e) => e.toParent());
  }
  /** The coordinates of an element of this module, of its parent or of an ancestor; throws ClosureFailure. */
  represent(elt: ModuleElement): DomainMatrix {
    if (elt.module.equals(this)) return elt.column();
    if (elt.module.equals(this.parent)) {
      const x = particularSolution(this.QQMatrix, elt.QQCol);
      if (x === undefined) throw new ClosureFailure('Element outside QQ-span of this basis.');
      if (x.flat().some((c) => rat(c).q !== 1n)) throw new ClosureFailure('Element in QQ-span but not ZZ-span of this basis.');
      return x.transpose().convertTo(ZZ);
    }
    if (this.parent instanceof Submodule) return this.represent(this.parent.call(this.parent.represent(elt)));
    throw new ClosureFailure('Element outside ancestor chain of this module.');
  }
  /** A submodule of the same parent. */
  isCompatSubmodule(other: unknown): other is Submodule {
    return other instanceof Submodule && other.parent.equals(this.parent);
  }
  equals(other: unknown): boolean {
    return this.isCompatSubmodule(other) && other.QQMatrix.equals(this.QQMatrix);
  }
  /** The sum of two submodules of the same parent. */
  add(other: Submodule, opts: HnfOptions = {}): Submodule {
    if (!this.isCompatSubmodule(other)) throw new TypeError('unsupported operand: submodules of different modules');
    const d = this.den, e = other.den;
    const m = ilcm(d, e);
    const a = m / d, b = m / e;
    let B = this.matrix.rscalarmul(zz(a)).hstack(other.matrix.rscalarmul(zz(b)));
    if (opts.hnf ?? true) B = hermiteNormalForm(B, opts.hnfModulus === undefined ? {} : { D: opts.hnfModulus });
    return this.parent.submoduleFromMatrix(B, m);
  }
  /**
   * The product with a rational number, with an element of the parent, or
   * with a submodule of the same parent (the submodule generated by the
   * products of the basis elements).
   */
  mul(other: RationalLike | ModuleElement | Submodule, opts: HnfOptions = {}): Submodule {
    if (isRat(other)) {
      const [a, b] = getNumDenom(other);
      if (a === 1n && b === 1n) return this;
      return new Submodule(this.parent, times(this.matrix, a), this.den * b).reduced();
    }
    if (other instanceof ModuleElement) {
      if (!other.module.equals(this.parent)) throw new TypeError('unsupported operand: an element of another module');
      return this.parent.submoduleFromGens(this.basisElementPullbacks().map((e) => other.mul(e)), opts);
    }
    if (!this.isCompatSubmodule(other)) throw new TypeError('unsupported operand: submodules of different modules');
    const alphas = this.basisElementPullbacks(), betas = other.basisElementPullbacks();
    return this.parent.submoduleFromGens(alphas.flatMap((x) => betas.map((y) => x.mul(y))), opts);
  }
  /** The e-th power (e >= 1) by repeated multiplication. */
  pow(e: number): Submodule {
    if (e === 1) return this;
    if (e < 1 || !Number.isInteger(e)) throw new TypeError('unsupported power of a submodule');
    return binaryPower<Submodule>(this, e, (x, y) => x.mul(y));
  }
  /**
   * The representative of an element of the parent modulo this submodule,
   * whose matrix must be square, of maximal rank and in Hermite normal form:
   * its i-th coordinate is in [0, d_i) for the i-th diagonal entry d_i.
   */
  reduceElement(elt: ModuleElement): ModuleElement {
    if (!elt.module.equals(this.parent)) throw new NotImplementedError('reduceElement: the element must belong to the parent');
    if (!this.isSqMaxrankHNF()) throw new StructureError('Reduction not implemented unless matrix square max-rank HNF');
    const B = this.basisElementPullbacks();
    let a = elt;
    for (let i = this.n - 1; i >= 0; i--) {
      const b = at(B, i);
      const q = fdiv(at(a.coeffs, i) * b.denom, at(b.coeffs, i) * a.denom);
      a = a.sub(b.mul(q));
    }
    return a;
  }
}

/** Powering by binary expansion (SymPy IntegerPowerable.__pow__ for e >= 2). */
function binaryPower<T>(x: T, e: number, mulf: (a: T, b: T) => T): T {
  // the bits of e from the lowest: p runs through x**(2**i); r starts at the lowest set bit
  let p = x;
  let k = e;
  for (; k % 2 === 0; k /= 2) p = mulf(p, p);
  let r = p;
  for (k = (k - 1) / 2; k > 0; k = Math.floor(k / 2)) {
    p = mulf(p, p);
    if (k % 2 === 1) r = mulf(r, p);
  }
  return r;
}

/** A square matrix over ZZ, upper triangular with a positive diagonal and each entry right of it in [0, diagonal) (SymPy is_sq_maxrank_HNF). */
export function isSqMaxrankHNF(dm: DomainMatrix): boolean {
  if (!(dm.domain.equals(ZZ) && dm.isSquare && dm.isUpper)) return false;
  const n = dm.shape[0];
  for (let i = 0; i < n; i++) {
    const d = int(dm.getitemSympy(i, i));
    if (d <= 0n) return false;
    for (let j = i + 1; j < n; j++) {
      const e = int(dm.getitemSympy(i, j));
      if (!(e >= 0n && e < d)) return false;
    }
  }
  return true;
}

/** The element of a module with this column and denominator: a PowerBasisElement for a power basis (SymPy make_mod_elt). */
export function makeModElt(module: Module, col: DomainMatrix, denom: bigint | number = 1n): ModuleElement {
  if (module instanceof PowerBasis) return new PowerBasisElement(module, col, denom);
  return new ModuleElement(module, col, denom);
}

/** An element of a power basis as a PowerBasisElement (makeModElt makes one; a ModuleElement made directly is converted). */
function asPowerBasisElement(pb: PowerBasis, e: ModuleElement): PowerBasisElement {
  return e instanceof PowerBasisElement ? e : new PowerBasisElement(pb, e.col, e.denom);
}

/**
 * An element of a module: a column of integer coordinates in the module's
 * basis over a positive denominator (SymPy ModuleElement). It prints as
 * `[1, 2, 3, 4]/3`.
 */
export class ModuleElement {
  readonly module: Module;
  readonly col: DomainMatrix;
  readonly denom: bigint;
  private qqCol: DomainMatrix | undefined;
  constructor(module: Module, col: DomainMatrix, denom: bigint | number = 1n) {
    this.module = module;
    this.col = col;
    this.denom = BigInt(denom);
  }
  /** SymPy repr: [1, 2, 3, 4]/3. */
  toString(): string {
    return `[${this.coeffs.join(', ')}]${this.denom > 1n ? `/${this.denom}` : ''}`;
  }
  /** The same element with the gcd of the denominator and the coordinates cancelled. */
  reduced(): ModuleElement {
    if (this.denom === 1n) return this;
    const g = igcd(this.denom, ...this.coeffs);
    if (g === 1n) return this;
    return makeModElt(this.module, this.col.div(zz(g)).convertTo(ZZ), this.denom / g);
  }
  /** The element with its coordinates reduced to the symmetric residues modulo p. */
  reducedModP(p: bigint | number): ModuleElement {
    return makeModElt(this.module, this.col.convertTo(GF(p)).convertTo(ZZ), this.denom);
  }
  /** The element of a module with these integer coordinates (SymPy from_int_list). */
  static fromIntList(module: Module, coeffs: readonly (bigint | number)[], denom: bigint | number = 1n): ModuleElement {
    return makeModElt(module, toCol(coeffs), denom);
  }
  /** The number of coordinates. */
  get n(): number {
    return this.module.n;
  }
  /** A copy of the column of coordinates, optionally over another domain. */
  column(domain?: Domain): DomainMatrix {
    return domain === undefined ? this.col.copy() : this.col.convertTo(domain);
  }
  /** The integer coordinates. */
  get coeffs(): bigint[] {
    return ints(this.col);
  }
  /** The column over QQ of the coordinates divided by the denominator (SymPy QQ_col). */
  get QQCol(): DomainMatrix {
    this.qqCol ??= this.col.div(zz(this.denom)).toDense();
    return this.qqCol;
  }
  /** The same element as an element of the parent module. */
  toParent(): ModuleElement {
    const m = this.module;
    if (!(m instanceof Submodule)) throw new RangeError('Not an element of a Submodule.');
    return makeModElt(m.parent, dmMul(m.matrix, this.col), m.denom * this.denom);
  }
  /** The same element as an element of an ancestor module. */
  toAncestor(anc: Module): ModuleElement {
    if (anc.equals(this.module)) return this;
    return this.toParent().toAncestor(anc);
  }
  /** The same element as an element of the power basis at the root. */
  overPowerBasis(): PowerBasisElement {
    const m = this.module;
    if (m instanceof PowerBasis) return asPowerBasisElement(m, this);
    return this.toParent().overPowerBasis();
  }
  /** An element of the same module. */
  isCompat(other: unknown): boolean {
    return other instanceof ModuleElement && other.module.equals(this.module);
  }
  /** Both elements in their nearest common ancestor; throws UnificationFailed. */
  unify(other: ModuleElement): [ModuleElement, ModuleElement] {
    if (this.module.equals(other.module)) return [this, other];
    const nca = this.module.nearestCommonAncestor(other.module);
    if (!isNoMatch(nca)) return [this.toAncestor(nca), other.toAncestor(nca)];
    throw new UnificationFailed(`Cannot unify ${this.toString()} with ${other.toString()}`);
  }
  /** SymPy ==: elements of the same module with the same value. */
  equals(other: unknown): boolean {
    return other instanceof ModuleElement && this.isCompat(other) && this.QQCol.equals(other.QQCol);
  }
  /** The same number, possibly as elements of different modules, or equal to a rational number. */
  equiv(other: ModuleElement | RationalLike): boolean {
    if (this.equals(other)) return true;
    if (other instanceof ModuleElement) {
      const [a, b] = this.unify(other);
      return a.equals(b);
    }
    if (this instanceof PowerBasisElement) return this.equals(this.module.call(0).mul(other));
    return this.overPowerBasis().equiv(other);
  }
  /** The sum (the elements are unified first), reduced. */
  add(other: ModuleElement | RationalLike): ModuleElement {
    if (other instanceof ModuleElement && this.isCompat(other)) {
      const d = this.denom, e = other.denom;
      const m = ilcm(d, e);
      const u = m / d, v = m / e;
      const o = other.coeffs;
      return makeModElt(this.module, toCol(this.coeffs.map((a, i) => u * a + v * at(o, i))), m).reduced();
    }
    if (other instanceof ModuleElement) {
      const [a, b] = this.unifyOperands(other);
      return a.add(b);
    }
    return this.add(this.module.elementFromRational(other));
  }
  neg(): ModuleElement {
    return this.mul(-1);
  }
  sub(other: ModuleElement | RationalLike): ModuleElement {
    return this.add(other instanceof ModuleElement ? other.neg() : negRat(other));
  }
  /**
   * The product: by the multiplication table for elements of the same module
   * (not reduced), after unification for elements of different modules, or
   * by a rational number (reduced).
   */
  mul(other: ModuleElement | RationalLike): ModuleElement {
    if (other instanceof ModuleElement && this.isCompat(other)) {
      const M = this.module.multTab();
      const A = this.coeffs, B = other.coeffs;
      const n = this.n;
      const C = Array.from({ length: n }, () => 0n);
      for (let u = 0; u < n; u++) {
        for (let v = u; v < n; v++) {
          let c = at(A, u) * at(B, v);
          if (v > u) c += at(A, v) * at(B, u);
          if (c !== 0n) {
            const R = getOrThrow(getOrThrow(M, u), v);
            for (let k = 0; k < n; k++) C[k] = at(C, k) + c * at(R, k);
          }
        }
      }
      return ModuleElement.fromIntList(this.module, C, this.denom * other.denom);
    }
    if (other instanceof ModuleElement) {
      const [a, b] = this.unifyOperands(other);
      return a.mul(b);
    }
    const [a, b] = getNumDenom(other);
    if (a === 1n && b === 1n) return this;
    return makeModElt(this.module, times(this.col, a), this.denom * b).reduced();
  }
  /** Unify for an arithmetic operation: elements without a common ancestor are unsupported operands (SymPy returns NotImplemented). */
  private unifyOperands(other: ModuleElement): [ModuleElement, ModuleElement] {
    if (isNoMatch(this.module.nearestCommonAncestor(other.module))) throw new TypeError(`unsupported operands: ${this.toString()} and ${other.toString()}`);
    return this.unify(other);
  }
  /** The e-th power: 1 for e = 0, by repeated multiplication for e >= 1 (and the inverse for e < 0 of a PowerBasisElement). */
  pow(e: number): ModuleElement {
    if (!Number.isInteger(e)) throw new TypeError('unsupported power');
    if (e === 1) return this;
    if (e === 0) return this.module.one();
    if (e < 0) return this.negativePower(e);
    return binaryPower<ModuleElement>(this, e, (x, y) => x.mul(y));
  }
  protected negativePower(_e: number): ModuleElement {
    throw new TypeError('unsupported operand: negative power of a module element');
  }
  /** Division (SymPy //): by a rational number, or by an element (multiplying by its inverse in the power basis). */
  floordiv(a: ModuleElement | RationalLike): ModuleElement {
    if (a instanceof ModuleElement) return this.mul(a.overPowerBasis().inverse());
    const [p, q] = getNumDenom(a);
    if (p === 0n) throw new RangeError('division by zero');
    return this.mul(new PythonMPQ(q, p));
  }
  /** The representative modulo a submodule of this element's module, or modulo a rational times the whole module. */
  mod(m: RationalLike | Submodule): ModuleElement {
    const M = isRat(m) ? this.module.wholeSubmodule().mul(m) : m;
    if (!M.parent.equals(this.module)) throw new TypeError('unsupported operand: a submodule of another module');
    return M.reduceElement(this);
  }
}

const negRat = (c: RationalLike): RationalLike => {
  const [a, b] = getNumDenom(c);
  return new PythonMPQ(-a, b);
};

/** An element of a power basis: a polynomial in theta over a denominator (SymPy PowerBasisElement). */
export class PowerBasisElement extends ModuleElement {
  declare readonly module: PowerBasis;
  constructor(module: PowerBasis, col: DomainMatrix, denom: bigint | number = 1n) {
    super(module, col, denom);
  }
  /** The polynomial defining theta. */
  get T(): Poly {
    return this.module.T;
  }
  /** The numerator as a polynomial over ZZ in x (default: the variable of T). */
  numerator(x?: Expr): Poly {
    const v = x ?? first(this.T.gens);
    const cs = this.coeffs;
    return Poly.from(add(...cs.map((c, i) => mul(zz(c), pow(v, i)))), [v], { domain: 'ZZ' });
  }
  /** The element as a polynomial in x with rational coefficients. */
  poly(x?: Expr): Poly {
    const N = this.numerator(x);
    return N.quo(Poly.from(zz(this.denom), N.gens, { domain: 'ZZ' }));
  }
  /** The element is a rational number. */
  get isRational(): boolean {
    return this.col.extractSlice([1, this.n], [0, 1]).isZeroMatrix;
  }
  /** The symbol the element is written with: the alias of the field's primitive element, else the variable of T. */
  get generator(): Expr {
    const K = this.module.numberField;
    return K?.ext.alias ?? first(this.T.gens);
  }
  /** The element as an expression in x (default: the generator). */
  asExpr(x?: Expr): Expr {
    const alias = this.module.numberField?.ext.alias;
    if (x === undefined && alias !== undefined) return this.inFieldGenerator(alias);
    return this.poly(x ?? this.generator).asExpr();
  }
  /** The value written with the field's primitive element (theta = generator/scale). */
  private inFieldGenerator(alias: Sym): Expr {
    const cs = this.module.toFieldCoeffs(this.QQCol.flat().map(rat));
    return add(...cs.map((c, i) => mul(c, pow(alias, i))));
  }
  /**
   * The norm: the resultant of T and the numerator over the denominator to
   * the n-th power (for another T, the norm of the element of its field with
   * the same coordinates). SymPy floors the quotient, which is wrong for an
   * element that is not an algebraic integer (the norm of [1, 2, 3, 4]/6 in
   * the 5th cyclotomic field is 125/1296, not 0); the exact quotient is returned.
   */
  norm(TIn?: Poly): Rational {
    const T = TIn ?? this.T;
    const A = this.numerator(first(T.gens));
    return Rational.of(int(T.resultant(A)), this.denom ** BigInt(this.n));
  }
  /** The multiplicative inverse; throws NotInvertible for zero. */
  inverse(): PowerBasisElement {
    const f = this.poly();
    return this.module.elementFromPoly(f.invert(this.T));
  }
  protected override negativePower(e: number): ModuleElement {
    return this.inverse().pow(-e);
  }
  /** The element of the field (SymPy to_ANP). */
  toANP(): ANP {
    const cs = this.module.toFieldCoeffs(this.QQCol.flat().map(rat));
    return new ANP([...cs].reverse(), this.module.fieldMod(), QQ);
  }
  /** The element as an algebraic number of the field; throws StructureError without one. */
  toAlgNum(): AlgebraicNumber {
    const K = this.module.numberField;
    if (K) return K.toAlgNum(this.toANP());
    throw new StructureError('No associated AlgebraicField');
  }
}

/** The codomain of a module homomorphism: a module, or an endomorphism ring. */
export interface HomomorphismCodomain<X> {
  /** The dimension of the coordinates. */
  readonly n: number;
  represent(x: X): DomainMatrix;
}

/** A homomorphism of ZZ-modules, given by a mapping of elements (SymPy ModuleHomomorphism). */
export class ModuleHomomorphism<X = ModuleElement> {
  constructor(
    readonly domain: Module,
    readonly codomain: HomomorphismCodomain<X>,
    readonly mapping: (x: ModuleElement) => X,
  ) {}
  /** The matrix of the homomorphism in the bases (over GF(modulus) with a modulus). */
  matrix(modulus?: bigint | number): DomainMatrix {
    const cols = this.domain.basisElements().map((elt) => this.codomain.represent(this.mapping(elt)));
    if (!cols.length) return DomainMatrix.zeros([this.codomain.n, 0], ZZ).toDense();
    const M = first(cols).hstack(...cols.slice(1));
    return modulus === undefined ? M : M.convertTo(GF(modulus));
  }
  /** The kernel as a submodule of the domain (computed over GF(modulus) with a modulus, else over QQ). */
  kernel(modulus?: bigint | number): Submodule {
    let M = this.matrix(modulus);
    if (modulus === undefined) M = M.convertTo(QQ);
    const K = M.nullspace().convertTo(ZZ).transpose();
    return this.domain.submoduleFromMatrix(K);
  }
}

/** A homomorphism of a module to itself (SymPy ModuleEndomorphism). */
export class ModuleEndomorphism extends ModuleHomomorphism {
  constructor(domain: Module, mapping: (x: ModuleElement) => ModuleElement) {
    super(domain, domain, mapping);
  }
}

/** Multiplication by an element (SymPy InnerEndomorphism). */
export class InnerEndomorphism extends ModuleEndomorphism {
  constructor(
    domain: Module,
    readonly multiplier: ModuleElement,
  ) {
    super(domain, (x) => multiplier.mul(x));
  }
}

/** The ring of endomorphisms of a module (SymPy EndomorphismRing). */
export class EndomorphismRing implements HomomorphismCodomain<ModuleHomomorphism> {
  constructor(readonly domain: Module) {}
  /** The dimension of the representations: n**2. */
  get n(): number {
    return this.domain.n ** 2;
  }
  /** Multiplication by an element. */
  innerEndomorphism(multiplier: ModuleElement): InnerEndomorphism {
    return new InnerEndomorphism(this.domain, multiplier);
  }
  /** An endomorphism of the module as a column: its matrix with the columns stacked. */
  represent(element: ModuleHomomorphism): DomainMatrix {
    if (element instanceof ModuleEndomorphism && element.domain.equals(this.domain)) {
      const M = element.matrix();
      const n = M.shape[1];
      if (n === 0) return M;
      const col = (j: number): DomainMatrix => M.extractSlice([0, M.shape[0]], [j, j + 1]);
      return col(0).vstack(...Array.from({ length: n - 1 }, (_, j) => col(j + 1)));
    }
    throw new NotImplementedError('only endomorphisms of the module are represented');
  }
}

/**
 * The minimal polynomial over QQ or GF(p) of an element of a module that
 * starts with unity, by finding the first linear dependence among its
 * powers (SymPy find_min_poly). The powers found are appended to `powers`.
 *
 * SymPy reads the coordinates of the powers without their denominators,
 * which gives the wrong polynomial for an element with a denominator (the
 * powers of A(1)//2 are taken for those of 2*A(1), 4*A(1)**2, ...); here
 * the coordinates are divided by the denominator.
 */
export function findMinPoly(alpha: ModuleElement, domain: Domain, x?: Sym, powers: ModuleElement[] = []): Poly {
  const R = alpha.module;
  if (!R.startsWithUnity()) throw new MissingUnityError('alpha must belong to finitely generated ring with unity.');
  const column = (e: ModuleElement): DomainMatrix => (e.denom === 1n ? e.column(domain) : e.column(domain).div(new DomainScalar(domain.fromSympy(zz(e.denom)), domain)));
  const one = R.call(0);
  powers.push(one);
  let powersMatrix = column(one);
  let ak = alpha;
  // at most n powers are linearly independent, so a dependence is found by the n-th power
  for (;;) {
    powers.push(ak);
    const akCol = column(ak);
    const X = particularSolution(powersMatrix, akCol);
    if (X === undefined) {
      powersMatrix = powersMatrix.hstack(akCol);
      ak = ak.mul(alpha);
      continue;
    }
    const coeffs = [domain.one, ...X.flat().reverse().map((c) => domain.neg(c))];
    const v = x ?? new Dummy('x');
    const k = coeffs.length - 1;
    const e = add(...coeffs.map((c, i) => mul(domain.toSympy(c), pow(v, k - i))));
    return domain instanceof FiniteField ? Poly.from(e, [v], { modulus: domain.mod }) : Poly.from(e, [v], { domain: domain.toString() });
  }
}
