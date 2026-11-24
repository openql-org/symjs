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

/**
 * The column vector of integers.
 *
 * @param coeffs - Integer coordinates in row order.
 * @returns A single-column matrix over the integers.
 * @see SymPy `sympy.polys.numberfields.modules.to_col`
 */
export function toCol(coeffs: readonly (bigint | number)[]): DomainMatrix {
  return new DomainMatrix([coeffs.map((c) => zz(BigInt(c)))], [1, coeffs.length], ZZ).transpose();
}

/**
 * A module over ZZ: a power basis or a submodule of another module. A module's elements are made
 * with `call`.
 *
 * @see SymPy `sympy.polys.numberfields.modules.Module`
 */
export abstract class Module {
  /**
   * The number of basis elements.
   *
   * @returns The number of basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.Module.n`
   */
  abstract get n(): number;
  /**
   * The multiplication table of the basis elements.
   *
   * @returns The multiplication table of the basis.
   * @see SymPy `sympy.polys.numberfields.modules.Module.mult_tab`
   */
  abstract multTab(): MultTab;
  /**
   * Identifies the enclosing module, when present. A power basis is at the root of its module
   * hierarchy.
   *
   * @returns The containing module when one exists.
   * @see SymPy `sympy.polys.numberfields.modules.Module.parent`
   */
  abstract get parent(): Module | undefined;
  /**
   * Expresses an element in the integral basis of this module.
   *
   * @param elt - Element to represent or transform.
   * @returns The column of coordinates in this basis.
   * @throws ClosureFailure when the element has no integral coordinates in the module basis.
   * @see SymPy `sympy.polys.numberfields.modules.Module.represent`
   */
  abstract represent(elt: ModuleElement): DomainMatrix;
  /**
   * The first basis element is 1.
   *
   * @returns Whether the first basis element represents one.
   * @see SymPy `sympy.polys.numberfields.modules.Module.starts_with_unity`
   */
  abstract startsWithUnity(): boolean;
  /**
   * Embeds a rational scalar using the element representing unity.
   *
   * @param a - Element on which to operate.
   * @returns The rational value as a module element.
   * @see SymPy `sympy.polys.numberfields.modules.Module.element_from_rational`
   */
  abstract elementFromRational(a: RationalLike): ModuleElement;
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   */
  abstract equals(other: unknown): boolean;
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   */
  abstract toString(): string;

  /**
   * The modules of the chain of parents, from the power basis down (and this one with includeSelf).
   *
   * @param includeSelf - Include this module in the ancestor chain.
   * @returns The chain of containing modules.
   * @see SymPy `sympy.polys.numberfields.modules.Module.ancestors`
   */
  ancestors(includeSelf = false): Module[] {
    const c = this.parent;
    const a = c === undefined ? [] : c.ancestors(true);
    if (includeSelf) a.push(this);
    return a;
  }
  /**
   * The power basis at the root of the chain of parents.
   *
   * @returns The underlying power basis.
   * @see SymPy `sympy.polys.numberfields.modules.Module.power_basis_ancestor`
   */
  abstract powerBasisAncestor(): PowerBasis;
  /**
   * The last module both chains of ancestors share, or NoMatch.
   *
   * @param other - Module whose chain of parents to compare.
   * @returns The nearest shared ancestor or `NoMatch`.
   * @see SymPy `sympy.polys.numberfields.modules.Module.nearest_common_ancestor`
   */
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
  /**
   * The number field of the power basis at the root, if it was made from one.
   *
   * @returns The associated algebraic field, when specified.
   * @see SymPy `sympy.polys.numberfields.modules.Module.number_field`
   */
  get numberField(): AlgebraicField | undefined {
    return this.powerBasisAncestor().K;
  }
  /**
   * A column vector over ZZ of length n.
   *
   * @param col - Column of integer coordinate numerators.
   * @returns Whether the column has compatible dimensions and integer entries.
   * @see SymPy `sympy.polys.numberfields.modules.Module.is_compat_col`
   */
  isCompatCol(col: unknown): col is DomainMatrix {
    return col instanceof DomainMatrix && col.shape[0] === this.n && col.shape[1] === 1 && col.domain.equals(ZZ);
  }
  /**
   * The element with the coordinates of a column over ZZ divided by denom, or the j-th basis element
   * for an integer j.
   *
   * @param specIn - Basis index or column of coordinate numerators.
   * @param denom - Common denominator.
   * @returns The module element with those coordinates.
   * @throws RangeError when the coordinate column is incompatible with the module.
   * @see SymPy `sympy.polys.numberfields.modules.Module.__call__`
   */
  call(specIn: number | DomainMatrix, denom: bigint | number = 1n): ModuleElement {
    const spec = typeof specIn === 'number' && specIn >= 0 && specIn < this.n ? DomainMatrix.eye(this.n, ZZ).extractSlice([0, this.n], [specIn, specIn + 1]).toDense() : specIn;
    if (!this.isCompatCol(spec)) throw new RangeError('Compatible column vector required.');
    return makeModElt(this, spec, BigInt(denom));
  }
  /**
   * The basis elements.
   *
   * @returns The elements of the ordered basis.
   * @see SymPy `sympy.polys.numberfields.modules.Module.basis_elements`
   */
  basisElements(): ModuleElement[] {
    return Array.from({ length: this.n }, (_, j) => this.call(j));
  }
  /**
   * The zero element.
   *
   * @returns The additive identity.
   * @see SymPy `sympy.polys.numberfields.modules.Module.zero`
   */
  zero(): ModuleElement {
    return this.call(0).mul(0);
  }
  /**
   * The unity element.
   *
   * @returns The multiplicative identity.
   * @see SymPy `sympy.polys.numberfields.modules.Module.one`
   */
  one(): ModuleElement {
    return this.elementFromRational(1);
  }
  /**
   * The submodule generated by elements of this module (in Hermite normal form unless hnf is false).
   *
   * @param gens - Generators in their given order.
   * @param opts - Hermite normal form and determinant-multiple settings.
   * @returns The submodule spanned by the supplied generators.
   * @throws RangeError when no generators are given or a generator belongs to a different module.
   * @see SymPy `sympy.polys.numberfields.modules.Module.submodule_from_gens`
   */
  submoduleFromGens(gens: readonly ModuleElement[], opts: HnfOptions = {}): Submodule {
    if (!gens.every((g) => g.module.equals(this))) throw new RangeError('Generators must belong to this module.');
    if (gens.length === 0) throw new RangeError('Need at least one generator.');
    const m = first(gens).n;
    const d = gens.length === 1 ? first(gens).denom : ilcm(...gens.map((g) => g.denom));
    let B = DomainMatrix.zeros([m, 0], ZZ).hstack(...gens.map((g) => g.col.rscalarmul(zz(d / g.denom))));
    if (opts.hnf ?? true) B = hermiteNormalForm(B, opts.hnfModulus === undefined ? {} : { D: opts.hnfModulus });
    return this.submoduleFromMatrix(B, d);
  }
  /**
   * The submodule whose basis elements are the columns of a matrix over ZZ divided by denom.
   *
   * @param B - Matrix to combine with this one.
   * @param denom - Common denominator.
   * @returns The submodule spanned by the supplied generators.
   * @throws RangeError when the matrix is not over the integers or has the wrong row count.
   * @see SymPy `sympy.polys.numberfields.modules.Module.submodule_from_matrix`
   */
  submoduleFromMatrix(B: DomainMatrix, denom: bigint | number = 1n): Submodule {
    if (!B.domain.equals(ZZ)) throw new RangeError('Matrix must be over ZZ.');
    if (B.shape[0] !== this.n) throw new RangeError('Matrix row count must match base module.');
    return new Submodule(this, B, denom);
  }
  /**
   * This module as a submodule of itself.
   *
   * @returns The full module represented as a submodule.
   * @see SymPy `sympy.polys.numberfields.modules.Module.whole_submodule`
   */
  wholeSubmodule(): Submodule {
    return this.submoduleFromMatrix(DomainMatrix.eye(this.n, ZZ));
  }
  /**
   * Forms the ring of module homomorphisms from the module to itself.
   *
   * @returns The ring of endomorphisms of this module.
   * @see SymPy `sympy.polys.numberfields.modules.Module.endomorphism_ring`
   */
  endomorphismRing(): EndomorphismRing {
    return new EndomorphismRing(this);
  }
}

const isMonicOverZZ = (T: Poly): boolean => T.allCoeffs().every((c) => c instanceof Rational && c.q === 1n) && T.LC().equals(1);

/**
 * The power basis 1, theta,..., theta**(n-1) of the ring ZZ[theta] for a root theta of a monic
 * irreducible polynomial T over ZZ, or of the primitive element of a number field.
 *
 * For a field whose primitive element is not an algebraic integer (its minimal polynomial is not
 * monic over ZZ) SymPy builds a power basis of a non-monic polynomial, whose multiplication table
 * is wrong (QQ<sqrt(2)/3> gets the discriminant 0). Here the root is scaled first: the basis is
 * that of theta' = scale*theta, whose minimal polynomial T is monic over ZZ
 * (Poly.makeMonicOverIntegersByScalingRoots), and the conversions to and from the field's elements
 * account for the scale.
 *
 * @see SymPy `sympy.polys.numberfields.modules.PowerBasis`
 */
export class PowerBasis extends Module {
  /**
   * The number field, when the basis was made from one.
   *
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.K`
   */
  readonly K: AlgebraicField | undefined;
  /**
   * The monic polynomial over ZZ of the generator.
   *
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.T`
   */
  readonly T: Poly;
  /** The generator of the basis is scale times the primitive element of the field. */
  readonly scale: bigint;
  /** The minimal polynomial of the field's primitive element (T unless scaled). */
  private readonly fieldPoly: Poly;
  private readonly degree: number;
  private multTable: MultTab | undefined;
  /**
   * Builds the basis of successive powers of a root of the defining polynomial.
   *
   * @param TIn - Defining polynomial or algebraic field supplying the power basis.
   * @throws RangeError when the defining polynomial is not monic over the integers.
   */
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
  /**
   * Identifies the algebraic field from which the basis was constructed, when supplied.
   *
   * @returns The associated algebraic field, when specified.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.number_field`
   */
  get numberField(): AlgebraicField | undefined {
    return this.K;
  }
  /**
   * A power basis is the root of the module hierarchy and has no parent.
   *
   * @returns No enclosing module.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.parent`
   */
  get parent(): undefined {
    return undefined;
  }
  /**
   * Locates the power basis at the root of the chain of parent modules.
   *
   * @returns The underlying power basis.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.power_basis_ancestor`
   */
  powerBasisAncestor(): PowerBasis {
    return this;
  }
  /**
   * Formats the power basis using the defining polynomial.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.__repr__`
   */
  toString(): string {
    return `PowerBasis(${str(this.T.asExpr())})`;
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof PowerBasis && this.T.equals(other.T);
  }
  /**
   * Counts the elements in the module basis.
   *
   * @returns The number of basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.n`
   */
  get n(): number {
    return this.degree;
  }
  /**
   * Gives the basis coordinates of products of pairs of basis elements.
   *
   * @returns The multiplication table of the basis.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.mult_tab`
   */
  multTab(): MultTab {
    this.multTable ??= this.buildMultTab();
    return this.multTable;
  }
  /**
   * Compute the multiplication table from the powers of theta.
   *
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.compute_mult_tab`
   */
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
  /**
   * Expresses an integral element in the power basis.
   *
   * @param elt - Element to represent or transform.
   * @returns The column of coordinates in this basis.
   * @throws ClosureFailure when the element does not lie in the integer span of the module basis.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.represent`
   */
  represent(elt: ModuleElement): DomainMatrix {
    if (elt.module.equals(this) && elt.denom === 1n) return elt.column();
    throw new ClosureFailure('Element not representable in ZZ[theta].');
  }
  /**
   * Tests whether the first basis vector represents the multiplicative identity.
   *
   * @returns Whether the first basis element represents one.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.starts_with_unity`
   */
  startsWithUnity(): boolean {
    return true;
  }
  /**
   * Embeds a rational scalar using the element representing unity.
   *
   * @param a - Element on which to operate.
   * @returns The rational value as a module element.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.element_from_rational`
   */
  elementFromRational(a: RationalLike): PowerBasisElement {
    return asPowerBasisElement(this, this.call(0).mul(a));
  }
  /**
   * Selects a power of the generator or specifies its coordinates over a common denominator.
   *
   * @param spec - Basis index or column of coordinate numerators.
   * @param denom - Common denominator.
   * @returns The module element with those coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.__call__`
   */
  override call(spec: number | DomainMatrix, denom: bigint | number = 1n): PowerBasisElement {
    return asPowerBasisElement(this, super.call(spec, denom));
  }
  /**
   * Constructs the element with all power-basis coefficients zero.
   *
   * @returns The additive identity.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.zero`
   */
  override zero(): PowerBasisElement {
    return asPowerBasisElement(this, super.zero());
  }
  /**
   * The element of a polynomial in theta with rational coefficients (reduced modulo T).
   *
   * @param fIn - Element to convert or divide.
   * @returns The value in power-basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.element_from_poly`
   */
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
  /**
   * The coefficients (lowest power first) of an element in powers of the field's primitive element,
   * from those in powers of the generator.
   *
   * @param coeffs - Coefficients in the basis order.
   * @returns The coefficients relative to the field generator.
   */
  toFieldCoeffs(coeffs: readonly Rational[]): Rational[] {
    return coeffs.map((c, i) => Rational.of(c.p * this.scale ** BigInt(i), c.q));
  }
  /**
   * The polynomial (highest coefficient first) defining the field's primitive element.
   *
   * @returns The defining modulus of the field.
   */
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
  /**
   * The element of an element of the field.
   *
   * @param a - Element on which to operate.
   * @returns The value in power-basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.element_from_ANP`
   */
  elementFromANP(a: ANP): PowerBasisElement {
    return this.elementFromRepAndMod(
      a.toList().map((c) => Rational.of(c.numerator, c.denominator)),
      a.mod.map((c) => Rational.of(c.numerator, c.denominator)),
    );
  }
  /**
   * The element of an algebraic number of the field.
   *
   * @param a - Element on which to operate.
   * @returns The value in power-basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasis.element_from_alg_num`
   */
  elementFromAlgNum(a: AlgebraicNumber): PowerBasisElement {
    return this.elementFromRepAndMod(a.coeffs().map(rat), a.minpoly().allCoeffs());
  }
}

/**
 * A submodule of a module: the ZZ-span of the columns of a matrix over ZZ divided by a denominator.
 * It prints as `Submodule[[2, 0], [1, 1]]/2` (the basis elements as rows).
 *
 * @see SymPy `sympy.polys.numberfields.modules.Submodule`
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
  /**
   * Takes the integer span of the matrix columns divided by the common denominator.
   *
   * @param parent - Parent algebra or module.
   * @param matrix - Columns spanning the submodule in the parent basis.
   * @param denom - Common denominator.
   * @param multTab - Known multiplication table of the module basis.
   */
  constructor(parent: Module, matrix: DomainMatrix, denom: bigint | number = 1n, multTab?: MultTab) {
    super();
    this.parentModule = parent;
    this.mat = matrix;
    this.den = BigInt(denom);
    this.multTable = multTab;
    this.cols = matrix.shape[1];
  }
  /**
   * Formats the submodule generators as their coordinate lists over the common denominator.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.__repr__`
   */
  toString(): string {
    const rows = this.matrix.transpose().toList().map((r) => `[${r.map((e) => String(int(e))).join(', ')}]`);
    return `Submodule[${rows.join(', ')}]${this.den > 1n ? `/${this.den}` : ''}`;
  }
  /**
   * The same submodule with the gcd of the denominator and the coefficients cancelled.
   *
   * @returns The representation in lowest terms.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.reduced`
   */
  reduced(): Submodule {
    if (this.den === 1n) return this;
    const g = igcd(this.den, ...this.coeffs);
    if (g === 1n) return this;
    return new Submodule(this.parent, this.matrix.div(zz(g)).convertTo(ZZ), this.den / g, this.multTable);
  }
  /**
   * The submodule spanned by the basis elements from the r-th on (keeping the multiplication table).
   *
   * @param r - Number of initial basis columns to discard.
   * @returns The span of the remaining basis vectors.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.discard_before`
   */
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
  /**
   * Counts the elements in the module basis.
   *
   * @returns The number of basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.n`
   */
  get n(): number {
    return this.cols;
  }
  /**
   * Gives the basis coordinates of products of pairs of basis elements.
   *
   * @returns The multiplication table of the basis.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.mult_tab`
   */
  multTab(): MultTab {
    this.multTable ??= this.buildMultTab();
    return this.multTable;
  }
  /**
   * Compute the multiplication table by representing the products of the basis elements.
   *
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.compute_mult_tab`
   */
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
  /**
   * The algebra or domain containing this element.
   *
   * @returns The module containing the submodule.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.parent`
   */
  get parent(): Module {
    return this.parentModule;
  }
  /**
   * Locates the power basis at the root of the chain of parent modules.
   *
   * @returns The underlying power basis.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.power_basis_ancestor`
   */
  powerBasisAncestor(): PowerBasis {
    return this.parent.powerBasisAncestor();
  }
  /**
   * The matrix over ZZ whose columns (over the denominator) are the basis elements.
   *
   * @returns The matrix in the specified bases.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.matrix`
   */
  get matrix(): DomainMatrix {
    return this.mat;
  }
  /**
   * The entries of the matrix, row by row.
   *
   * @returns The coefficients of the elements in basis order.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.coeffs`
   */
  get coeffs(): bigint[] {
    return ints(this.matrix);
  }
  /**
   * The common denominator of the coordinates.
   *
   * @returns The denominator.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.denom`
   */
  get denom(): bigint {
    return this.den;
  }
  /**
   * The matrix over QQ of the basis elements: matrix/denom.
   *
   * @returns The basis matrix over the rationals.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.QQ_matrix`
   */
  get QQMatrix(): DomainMatrix {
    this.qqMatrix ??= this.matrix.div(zz(this.den)).toDense();
    return this.qqMatrix;
  }
  /**
   * Tests whether the first basis vector represents the multiplicative identity.
   *
   * @returns Whether the first basis element represents one.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.starts_with_unity`
   */
  startsWithUnity(): boolean {
    this.startsWithOne ??= this.call(0).equiv(1);
    return this.startsWithOne;
  }
  /**
   * The matrix is square, of maximal rank and in Hermite normal form.
   *
   * @returns Whether the basis matrix is square and in full-rank Hermite normal form.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.is_sq_maxrank_HNF`
   */
  isSqMaxrankHNF(): boolean {
    this.sqMaxrankHNF ??= isSqMaxrankHNF(this.mat);
    return this.sqMaxrankHNF;
  }
  /**
   * Record properties already known to hold, so they are not recomputed .
   *
   * @param startsWithUnity - Known value of the first-basis-element unity test.
   * @param sqMaxrankHNF - Whether the basis matrix is already in square full-rank Hermite normal
   *   form.
   * @internal
   */
  presetProperties(startsWithUnity: boolean, sqMaxrankHNF: boolean): void {
    this.startsWithOne = startsWithUnity;
    this.sqMaxrankHNF = sqMaxrankHNF;
  }
  /**
   * The parent is a power basis.
   *
   * @returns Whether the parent is a power basis.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.is_power_basis_submodule`
   */
  isPowerBasisSubmodule(): boolean {
    return this.parent instanceof PowerBasis;
  }
  /**
   * Embeds a rational scalar using the element representing unity.
   *
   * @param a - Element on which to operate.
   * @returns The rational value as a module element.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.element_from_rational`
   */
  elementFromRational(a: RationalLike): ModuleElement {
    if (this.startsWithUnity()) return this.call(0).mul(a);
    return this.parent.elementFromRational(a);
  }
  /**
   * The basis elements as elements of the parent.
   *
   * @returns The basis vectors expressed in the parent.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.basis_element_pullbacks`
   */
  basisElementPullbacks(): ModuleElement[] {
    return this.basisElements().map((e) => e.toParent());
  }
  /**
   * Finds integral coordinates in this submodule for an element of this module or an ancestor.
   *
   * @param elt - Element to represent or transform.
   * @returns The column of coordinates in this basis.
   * @throws ClosureFailure when the element does not lie in the integer span of the module basis.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.represent`
   */
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
  /**
   * A submodule of the same parent.
   *
   * @param other - Candidate submodule with the same parent.
   * @returns Whether the submodules have a common parent.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.is_compat_submodule`
   */
  isCompatSubmodule(other: unknown): other is Submodule {
    return other instanceof Submodule && other.parent.equals(this.parent);
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.__eq__`
   */
  equals(other: unknown): boolean {
    return this.isCompatSubmodule(other) && other.QQMatrix.equals(this.QQMatrix);
  }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @param opts - Hermite normal form and determinant-multiple settings.
   * @returns The sum of the operands.
   * @throws TypeError when the operands belong to incompatible modules.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.add`
   */
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
   * The product with a rational number, with an element of the parent, or with a submodule of the
   * same parent (the submodule generated by the products of the basis elements).
   *
   * @param other - Factor on the right.
   * @param opts - Hermite normal form and determinant-multiple settings.
   * @returns The product in operand order.
   * @throws TypeError when the operands belong to incompatible modules.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.mul`
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
  /**
   * Raises the value to the specified power.
   *
   * @param e - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @throws TypeError when the exponent is unsupported.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.__pow__`
   */
  pow(e: number): Submodule {
    if (e === 1) return this;
    if (e < 1 || !Number.isInteger(e)) throw new TypeError('unsupported power of a submodule');
    return binaryPower<Submodule>(this, e, (x, y) => x.mul(y));
  }
  /**
   * The representative of an element of the parent modulo this submodule, whose matrix must be
   * square, of maximal rank and in Hermite normal form: its i-th coordinate is in [0, d_i) for the
   * i-th diagonal entry d_i.
   *
   * @param elt - Element to represent or transform.
   * @returns A reduced representative of the element.
   * @throws NotImplementedError when the element does not belong to the parent module.
   * @throws StructureError when the basis matrix is not in square full-rank Hermite normal form.
   * @see SymPy `sympy.polys.numberfields.modules.Submodule.reduce_element`
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

/**
 * Tests whether the integer matrix is square, upper triangular and in Hermite normal form with
 * positive pivots.
 *
 * @param dm - Integer matrix to test.
 * @returns Whether the matrix has full rank and is in square Hermite normal form.
 * @see SymPy `sympy.polys.numberfields.modules.is_sq_maxrank_HNF`
 */
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

/**
 * The element of a module with this column and denominator: a PowerBasisElement for a power basis.
 *
 * @param module - Parent module.
 * @param col - Column of integer numerators.
 * @param denom - Common denominator.
 * @returns The element with the given rational coordinates.
 * @see SymPy `sympy.polys.numberfields.modules.make_mod_elt`
 */
export function makeModElt(module: Module, col: DomainMatrix, denom: bigint | number = 1n): ModuleElement {
  if (module instanceof PowerBasis) return new PowerBasisElement(module, col, denom);
  return new ModuleElement(module, col, denom);
}

/** An element of a power basis as a PowerBasisElement (makeModElt makes one; a ModuleElement made directly is converted). */
function asPowerBasisElement(pb: PowerBasis, e: ModuleElement): PowerBasisElement {
  return e instanceof PowerBasisElement ? e : new PowerBasisElement(pb, e.col, e.denom);
}

/**
 * An element of a module: a column of integer coordinates in the module's basis over a positive
 * denominator. It prints as `[1, 2, 3, 4]/3`.
 *
 * @see SymPy `sympy.polys.numberfields.modules.ModuleElement`
 */
export class ModuleElement {
  /**
   * The module containing the element.
   *
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__module__`
   */
  readonly module: Module;
  /**
   * The column of integer coordinate numerators.
   *
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.col`
   */
  readonly col: DomainMatrix;
  /**
   * The common denominator of the coordinates.
   *
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.denom`
   */
  readonly denom: bigint;
  private qqCol: DomainMatrix | undefined;
  /**
   * Constructs a new `ModuleElement`.
   *
   * @param module - Module in which to interpret the coordinates.
   * @param col - Column of integer coordinate numerators.
   * @param denom - Common denominator.
   */
  constructor(module: Module, col: DomainMatrix, denom: bigint | number = 1n) {
    this.module = module;
    this.col = col;
    this.denom = BigInt(denom);
  }
  /**
   * Displays the coordinates of the element in its module.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__repr__`
   */
  toString(): string {
    return `[${this.coeffs.join(', ')}]${this.denom > 1n ? `/${this.denom}` : ''}`;
  }
  /**
   * The same element with the gcd of the denominator and the coordinates cancelled.
   *
   * @returns The representation in lowest terms.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.reduced`
   */
  reduced(): ModuleElement {
    if (this.denom === 1n) return this;
    const g = igcd(this.denom, ...this.coeffs);
    if (g === 1n) return this;
    return makeModElt(this.module, this.col.div(zz(g)).convertTo(ZZ), this.denom / g);
  }
  /**
   * The element with its coordinates reduced to the symmetric residues modulo p.
   *
   * @param p - Rational prime.
   * @returns The element with centered residue coefficients.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.reduced_mod_p`
   */
  reducedModP(p: bigint | number): ModuleElement {
    return makeModElt(this.module, this.col.convertTo(GF(p)).convertTo(ZZ), this.denom);
  }
  /**
   * The element of a module with these integer coordinates.
   *
   * @param module - Module in which to interpret the coordinates.
   * @param coeffs - Coefficients in the basis order.
   * @param denom - Common denominator.
   * @returns The element with the supplied coordinate numerators.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.from_int_list`
   */
  static fromIntList(module: Module, coeffs: readonly (bigint | number)[], denom: bigint | number = 1n): ModuleElement {
    return makeModElt(module, toCol(coeffs), denom);
  }
  /**
   * The number of coordinates.
   *
   * @returns The number of basis coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.n`
   */
  get n(): number {
    return this.module.n;
  }
  /**
   * A copy of the column of coordinates, optionally over another domain.
   *
   * @param domain - Coefficient domain for the values.
   * @returns A copy of the coordinate column.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.column`
   */
  column(domain?: Domain): DomainMatrix {
    return domain === undefined ? this.col.copy() : this.col.convertTo(domain);
  }
  /**
   * The integer coordinates.
   *
   * @returns The coefficients of the elements in basis order.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.coeffs`
   */
  get coeffs(): bigint[] {
    return ints(this.col);
  }
  /**
   * The column over QQ of the coordinates divided by the denominator.
   *
   * @returns The column of rational coordinates.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.QQ_col`
   */
  get QQCol(): DomainMatrix {
    this.qqCol ??= this.col.div(zz(this.denom)).toDense();
    return this.qqCol;
  }
  /**
   * The same element as an element of the parent module.
   *
   * @returns The element in the specified ancestor basis.
   * @throws RangeError when the element does not belong to a submodule.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.to_parent`
   */
  toParent(): ModuleElement {
    const m = this.module;
    if (!(m instanceof Submodule)) throw new RangeError('Not an element of a Submodule.');
    return makeModElt(m.parent, dmMul(m.matrix, this.col), m.denom * this.denom);
  }
  /**
   * The same element as an element of an ancestor module.
   *
   * @param anc - Ancestor module in whose basis to express the element.
   * @returns The element in the specified ancestor basis.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.to_ancestor`
   */
  toAncestor(anc: Module): ModuleElement {
    if (anc.equals(this.module)) return this;
    return this.toParent().toAncestor(anc);
  }
  /**
   * The same element as an element of the power basis at the root.
   *
   * @returns The element in the specified ancestor basis.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.over_power_basis`
   */
  overPowerBasis(): PowerBasisElement {
    const m = this.module;
    if (m instanceof PowerBasis) return asPowerBasisElement(m, this);
    return this.toParent().overPowerBasis();
  }
  /**
   * An element of the same module.
   *
   * @param other - Element to check for compatibility.
   * @returns Whether the elements belong to compatible modules.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.is_compat`
   */
  isCompat(other: unknown): boolean {
    return other instanceof ModuleElement && other.module.equals(this.module);
  }
  /**
   * Expresses both elements relative to their nearest common ancestor.
   *
   * @param other - Operand to convert to a common module or coefficient domain.
   * @returns The two elements represented in a common ancestor.
   * @throws UnificationFailed when the elements have no common parent.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.unify`
   */
  unify(other: ModuleElement): [ModuleElement, ModuleElement] {
    if (this.module.equals(other.module)) return [this, other];
    const nca = this.module.nearestCommonAncestor(other.module);
    if (!isNoMatch(nca)) return [this.toAncestor(nca), other.toAncestor(nca)];
    throw new UnificationFailed(`Cannot unify ${this.toString()} with ${other.toString()}`);
  }
  /**
   * Elements of the same module with the same value.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof ModuleElement && this.isCompat(other) && this.QQCol.equals(other.QQCol);
  }
  /**
   * The same number, possibly as elements of different modules, or equal to a rational number.
   *
   * @param other - Value to compare against.
   * @returns Whether the elements represent the same algebraic value.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.equiv`
   */
  equiv(other: ModuleElement | RationalLike): boolean {
    if (this.equals(other)) return true;
    if (other instanceof ModuleElement) {
      const [a, b] = this.unify(other);
      return a.equals(b);
    }
    if (!isRat(other)) return false;
    if (this instanceof PowerBasisElement) return this.equals(this.module.call(0).mul(other));
    return this.overPowerBasis().equiv(other);
  }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__add__`
   */
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
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__neg__`
   */
  neg(): ModuleElement {
    return this.mul(-1);
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__sub__`
   */
  sub(other: ModuleElement | RationalLike): ModuleElement {
    return this.add(other instanceof ModuleElement ? other.neg() : negRat(other));
  }
  /**
   * The product: by the multiplication table for elements of the same module (not reduced), after
   * unification for elements of different modules, or by a rational number (reduced).
   *
   * @param other - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__mul__`
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
  /**
   * The e-th power: 1 for e = 0, by repeated multiplication for e >= 1 (and the inverse for e < 0 of
   * a PowerBasisElement).
   *
   * @param e - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @throws TypeError when the exponent is unsupported.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__pow__`
   */
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
  /**
   * Division: by a rational number, or by an element (multiplying by its inverse in the power basis).
   *
   * @param a - Divisor.
   * @returns The quotient under floor division.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__floordiv__`
   */
  floordiv(a: ModuleElement | RationalLike): ModuleElement {
    if (a instanceof ModuleElement) return this.mul(a.overPowerBasis().inverse());
    const [p, q] = getNumDenom(a);
    if (p === 0n) throw new RangeError('division by zero');
    return this.mul(new PythonMPQ(q, p));
  }
  /**
   * The representative modulo a submodule of this element's module, or modulo a rational times the
   * whole module.
   *
   * @param m - Divisor.
   * @returns A representative of the residue class.
   * @throws TypeError when the modulus is a submodule of another module.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleElement.__mod__`
   */
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

/**
 * An element of a power basis: a polynomial in theta over a denominator.
 *
 * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement`
 */
export class PowerBasisElement extends ModuleElement {
  /**
   * The module containing the element.
   *
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.__module__`
   */
  declare readonly module: PowerBasis;
  /**
   * Defines an element by its power-basis coefficients over a common denominator.
   *
   * @param module - Module in which to interpret the coordinates.
   * @param col - Column of integer coordinate numerators.
   * @param denom - Common denominator.
   */
  constructor(module: PowerBasis, col: DomainMatrix, denom: bigint | number = 1n) {
    super(module, col, denom);
  }
  /**
   * The polynomial defining theta.
   *
   * @returns The defining polynomial of the algebraic generator.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.T`
   */
  get T(): Poly {
    return this.module.T;
  }
  /**
   * The numerator as a polynomial over ZZ in x (default: the variable of T).
   *
   * @param x - Independent variable.
   * @returns The numerator of the reduced fraction.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.numerator`
   */
  numerator(x?: Expr): Poly {
    const v = x ?? first(this.T.gens);
    const cs = this.coeffs;
    return Poly.from(add(...cs.map((c, i) => mul(zz(c), pow(v, i)))), [v], { domain: 'ZZ' });
  }
  /**
   * The element as a polynomial in x with rational coefficients.
   *
   * @param x - Independent variable.
   * @returns The polynomial representative.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.poly`
   */
  poly(x?: Expr): Poly {
    const N = this.numerator(x);
    return N.quo(Poly.from(zz(this.denom), N.gens, { domain: 'ZZ' }));
  }
  /**
   * The element is a rational number.
   *
   * @returns Whether the element belongs to the rational field.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.is_rational`
   */
  get isRational(): boolean {
    return this.col.extractSlice([1, this.n], [0, 1]).isZeroMatrix;
  }
  /**
   * The symbol the element is written with: the alias of the field's primitive element, else the
   * variable of T.
   *
   * @returns The expression denoting the algebraic generator.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.generator`
   */
  get generator(): Expr {
    const K = this.module.numberField;
    return K?.ext.alias ?? first(this.T.gens);
  }
  /**
   * The element as an expression in x (default: the generator).
   *
   * @param x - Independent variable.
   * @returns The corresponding symbolic expression.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.as_expr`
   */
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
   * Computes the field norm as the resultant of the defining polynomial and the numerator divided by
   * the denominator raised to the field degree.
   *
   * @remarks For the element below SymPy returns 0 after taking the floor of the norm. The exact
   *   field norm is `125/1296`.
   * @param TIn - Polynomial defining the algebraic roots.
   * @returns The norm of the element.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.norm`
   * @example
   * ```ts
   * import { Poly, PowerBasis, ex, toCol } from '@symjs/symjs';
   *
   * const A = new PowerBasis(Poly.from(ex`x**4 + x**3 + x**2 + x + 1`));
   * A.call(toCol([1, 2, 3, 4]), 6).norm(); // => 125/1296
   * ```
   */
  norm(TIn?: Poly): Rational {
    const T = TIn ?? this.T;
    const A = this.numerator(first(T.gens));
    return Rational.of(int(T.resultant(A)), this.denom ** BigInt(this.n));
  }
  /**
   * Computes the multiplicative inverse in the number field.
   *
   * @returns The multiplicative inverse.
   * @throws NotInvertible when the element is zero.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.inverse`
   */
  inverse(): PowerBasisElement {
    const f = this.poly();
    return this.module.elementFromPoly(f.invert(this.T));
  }
  protected override negativePower(e: number): ModuleElement {
    return this.inverse().pow(-e);
  }
  /**
   * The element of the field.
   *
   * @returns The algebraic field element.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.to_ANP`
   */
  toANP(): ANP {
    const cs = this.module.toFieldCoeffs(this.QQCol.flat().map(rat));
    return new ANP([...cs].reverse(), this.module.fieldMod(), QQ);
  }
  /**
   * Expresses the element in the algebraic field associated with its power basis.
   *
   * @returns The corresponding algebraic number.
   * @throws StructureError when the power basis has no associated algebraic field.
   * @see SymPy `sympy.polys.numberfields.modules.PowerBasisElement.to_alg_num`
   */
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
  /**
   * Expresses an image in the coordinate basis of the codomain.
   *
   * @param x - Element whose coordinates to compute.
   * @returns The column of coordinates in this basis.
   */
  represent(x: X): DomainMatrix;
}

/**
 * A homomorphism of ZZ-modules, given by a mapping of elements.
 *
 * @see SymPy `sympy.polys.numberfields.modules.ModuleHomomorphism`
 */
export class ModuleHomomorphism<X = ModuleElement> {
  /**
   * Defines a map between modules by specifying how to compute the image of an element.
   *
   * @param domain - Module on which the map acts.
   * @param codomain - Target of the homomorphism.
   * @param mapping - Function assigning the image of a domain element.
   */
  constructor(
    /**
     * The source module of the homomorphism.
     *
     * @see SymPy `sympy.polys.numberfields.modules.ModuleHomomorphism.domain`
     */
    readonly domain: Module,
    /**
     * The target of the homomorphism.
     *
     * @see SymPy `sympy.polys.numberfields.modules.ModuleHomomorphism.codomain`
     */
    readonly codomain: HomomorphismCodomain<X>,
    /**
     * The map taking a domain element to its image.
     *
     * @see SymPy `sympy.polys.numberfields.modules.ModuleHomomorphism.mapping`
     */
    readonly mapping: (x: ModuleElement) => X,
  ) {}
  /**
   * The matrix of the homomorphism in the bases (over GF(modulus) with a modulus).
   *
   * @param modulus - Modulus used for the arithmetic.
   * @returns The matrix in the specified bases.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleHomomorphism.matrix`
   */
  matrix(modulus?: bigint | number): DomainMatrix {
    const cols = this.domain.basisElements().map((elt) => this.codomain.represent(this.mapping(elt)));
    if (!cols.length) return DomainMatrix.zeros([this.codomain.n, 0], ZZ).toDense();
    const M = first(cols).hstack(...cols.slice(1));
    return modulus === undefined ? M : M.convertTo(GF(modulus));
  }
  /**
   * The kernel as a submodule of the domain (computed over GF(modulus) with a modulus, else over QQ).
   *
   * @param modulus - Modulus used for the arithmetic.
   * @returns The submodule mapped to zero.
   * @see SymPy `sympy.polys.numberfields.modules.ModuleHomomorphism.kernel`
   */
  kernel(modulus?: bigint | number): Submodule {
    let M = this.matrix(modulus);
    if (modulus === undefined) M = M.convertTo(QQ);
    const K = M.nullspace().convertTo(ZZ).transpose();
    return this.domain.submoduleFromMatrix(K);
  }
}

/**
 * A homomorphism of a module to itself.
 *
 * @see SymPy `sympy.polys.numberfields.modules.ModuleEndomorphism`
 */
export class ModuleEndomorphism extends ModuleHomomorphism {
  /**
   * Defines a linear self-map by its action on elements.
   *
   * @param domain - Module on which the map acts.
   * @param mapping - Function assigning the image of a domain element.
   */
  constructor(domain: Module, mapping: (x: ModuleElement) => ModuleElement) {
    super(domain, domain, mapping);
  }
}

/**
 * Multiplication by an element.
 *
 * @see SymPy `sympy.polys.numberfields.modules.InnerEndomorphism`
 */
export class InnerEndomorphism extends ModuleEndomorphism {
  /**
   * Defines the endomorphism that multiplies by a fixed element.
   *
   * @param domain - Module on which the map acts.
   * @param multiplier - Element by which the endomorphism multiplies.
   */
  constructor(
    domain: Module,
    /**
     * The element defining the multiplication map.
     *
     * @see SymPy `sympy.polys.numberfields.modules.InnerEndomorphism.multiplier`
     */
    readonly multiplier: ModuleElement,
  ) {
    super(domain, (x) => multiplier.mul(x));
  }
}

/**
 * The ring of endomorphisms of a module.
 *
 * @see SymPy `sympy.polys.numberfields.modules.EndomorphismRing`
 */
export class EndomorphismRing implements HomomorphismCodomain<ModuleHomomorphism> {
  /**
   * Forms the ring of linear self-maps of a module.
   *
   * @param domain - Module on which the map acts.
   */
  constructor(
    /**
     * The module on which the endomorphisms act.
     *
     * @see SymPy `sympy.polys.numberfields.modules.EndomorphismRing.domain`
     */
    readonly domain: Module) {}
  /**
   * The dimension of the representations: n**2.
   *
   * @returns The number of basis coordinates.
   */
  get n(): number {
    return this.domain.n ** 2;
  }
  /**
   * Multiplication by an element.
   *
   * @param multiplier - Element by which the endomorphism multiplies.
   * @returns The map given by multiplication by the element.
   * @see SymPy `sympy.polys.numberfields.modules.EndomorphismRing.inner_endomorphism`
   */
  innerEndomorphism(multiplier: ModuleElement): InnerEndomorphism {
    return new InnerEndomorphism(this.domain, multiplier);
  }
  /**
   * Stacks the columns of the endomorphism’s matrix into a coordinate vector.
   *
   * @param element - Element to represent or transform.
   * @returns The column of coordinates in this basis.
   * @throws NotImplementedError when the map is not an endomorphism of this module.
   * @see SymPy `sympy.polys.numberfields.modules.EndomorphismRing.represent`
   */
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
 * Computes the minimal polynomial of a module element over `QQ` or a prime field from the first
 * linear dependence among its powers. The basis must start with unity.
 *
 * @remarks For a root of `x**2 - 5` divided by two, SymPy returns `x**2 - 5`. Accounting for the
 *   denominator gives `x**2 - 5/4`.
 * @param alpha - Element of the module.
 * @param domain - Base field for the linear dependence.
 * @param x - Variable of the minimal polynomial.
 * @param powers - List to receive the successive powers.
 * @returns The monic minimal polynomial over the specified domain.
 * @throws MissingUnityError when the basis of the ring does not start with unity.
 * @see SymPy `sympy.polys.numberfields.modules.find_min_poly`
 * @example
 * ```ts
 * import { Poly, PowerBasis, QQ, ex, findMinPoly, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const A = new PowerBasis(Poly.from(ex`x**2 - 5`));
 * findMinPoly(A.call(1), QQ, x).asExpr(); // => x**2 - 5
 * findMinPoly(A.call(1).floordiv(2), QQ, x).asExpr(); // => x**2 - 5/4
 * ```
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
