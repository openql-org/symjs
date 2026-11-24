// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/polyclasses.py: ANP, DMP_Python),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Dense recursive polynomials and elements of algebraic number fields.
 * SymPy ANP is a polynomial in
 * the primitive element theta with rational coefficients, reduced modulo the
 * minimal polynomial of theta. An element prints as
 * `ANP([MPQ(1,1), MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)`.
 */

import { DomainError, NotInvertible } from '../core/errors';
import { at, defined, first } from '../core/guard';
import { CoercionFailed, QQ, groundRational, domainArith, domainNeg } from './domains';
import type { Domain } from './domains';
import { UnificationFailed } from './polyerrors';
import { PythonMPQ } from './domains/pythonrational';

import { dmpFromDict, dmpValidate, dmpNormal, dmpConvert, dmpGround, dmpCopy, dmpToDict, dmpZeroP, dmpOneP, dmpDegreeIn, dmpDegreeList, dmpGroundLC, dmpGroundTC, dmpGroundNth, dmpZero, dmpExclude, groundEquals } from './densebasic';
import type { DensePoly } from './densebasic';
import { dmpAbs, dmpNeg, dmpAdd, dmpSub, dmpMul, dmpSqr, dmpPow, dmpMulGround, dmpQuoGround, dmpExquoGround, dmpDiv, dmpExquo, dmpPdiv, dmpPexquo, dmpMaxNorm, dmpL1Norm } from './densearith';
import type * as DenseTools from './densetools';

/** Advanced dense operations registered by the densetools module. */
export const dmpTools: Partial<Pick<typeof DenseTools, 'dmpDiffIn' | 'dmpEvalIn' | 'dmpGroundMonic' | 'dmpGroundContent' | 'dmpGroundPrimitive' | 'dmpGroundTrunc' | 'dmpCompose' | 'dupDecompose' | 'dmpClearDenoms'>> = {};

import { heuGcd } from './euclidtools';

type QP = PythonMPQ[];
const ZERO = new PythonMPQ(0n);
const ONE = new PythonMPQ(1n);

const strip = (f: readonly PythonMPQ[]): QP => {
  let i = 0;
  while (i < f.length && at(f, i).isZero) i++;
  return f.slice(i);
};
function polyAdd(f: QP, g: QP): QP {
  const n = Math.max(f.length, g.length);
  const pad = (h: QP): QP => [...Array.from({ length: n - h.length }, () => ZERO), ...h];
  const [F, G] = [pad(f), pad(g)];
  return strip(F.map((c, i) => c.add(at(G, i))));
}
function polyMul(f: QP, g: QP): QP {
  if (!f.length || !g.length) return [];
  const out: QP = Array.from({ length: f.length + g.length - 1 }, () => ZERO);
  f.forEach((a, i) => g.forEach((b, j) => (out[i + j] = at(out, i + j).add(a.mul(b)))));
  return strip(out);
}
/** [quotient, remainder] of f by a nonzero g. */
function polyDivmod(f: QP, g: QP): [QP, QP] {
  const r = [...f];
  const dg = g.length - 1;
  if (r.length - 1 < dg) return [[], strip(r)];
  const qq: QP = [];
  const lc = first(g);
  for (let i = 0; i <= f.length - 1 - dg; i++) {
    const c = at(r, i).div(lc);
    qq.push(c);
    for (let j = 0; j <= dg; j++) r[i + j] = at(r, i + j).sub(c.mul(at(g, j)));
  }
  return [strip(qq), strip(r.slice(f.length - dg))];
}
/** The inverse of f modulo m (SymPy dup_invert); throws NotInvertible. */
function polyInvert(f: QP, m: QP): QP {
  let [r0, r1, s0, s1]: [QP, QP, QP, QP] = [m, polyDivmod(f, m)[1], [], [ONE]];
  while (r1.length) {
    const [qq, r] = polyDivmod(r0, r1);
    [r0, r1] = [r1, r];
    [s0, s1] = [s1, polyAdd(s0, polyMul(qq, s1).map((c) => c.neg()))];
  }
  if (r0.length !== 1) throw new NotInvertible('zero divisor');
  const c = first(r0);
  return s0.map((a) => a.div(c));
}

/**
 * An element of an algebraic number field: a polynomial in the primitive element modulo its minimal polynomial.
 *
 * @see SymPy `sympy.polys.polyclasses.ANP`
 */
export class ANP {
  /**
   * The dense coefficient representation, leading coefficient first.
   *
   * @see SymPy `sympy.polys.polyclasses.ANP.rep`
   */
  readonly rep: QP;
  /**
   * The modulus defining the algebraic extension.
   *
   * @see SymPy `sympy.polys.polyclasses.ANP.mod`
   */
  readonly mod: QP;
  /**
   * Construct an element of an algebraic extension.
   *
   * @param rep - Dense coefficients in descending order.
   * @param mod - Polynomial modulus defining the extension.
   * @param dom - Ground coefficient domain.
   */
  constructor(
    rep: unknown,
    mod: readonly unknown[],
    /** The ground coefficient domain. @see SymPy `sympy.polys.polyclasses.ANP.dom` */
    readonly dom: Domain = QQ,
  ) {
    const conv = (a: unknown): PythonMPQ => QQ.convert(a);
    this.rep = strip(Array.isArray(rep) ? (rep as unknown[]).map(conv) : [conv(rep)]);
    this.mod = strip(mod.map(conv));
  }
  private per(rep: QP): ANP {
    return new ANP(polyDivmod(rep, this.mod)[1], this.mod, this.dom);
  }
  private repOf(o: unknown): QP {
    if (o instanceof ANP) {
      if (o.mod.length !== this.mod.length || o.mod.some((c, i) => !c.equals(this.mod[i]))) throw new CoercionFailed('cannot unify algebraic numbers of different fields');
      return o.rep;
    }
    return strip([QQ.convert(o)]);
  }
  /**
   * Whether the element is the multiplicative identity.
   *
   * @returns Whether the element is the multiplicative identity.
   * @see SymPy `sympy.polys.polyclasses.ANP.is_one`
   */
  get isOne(): boolean {
    return this.rep.length === 1 && this.LC().equals(1);
  }
  /**
   * Whether the element is zero.
   *
   * @returns Whether the element is zero.
   * @see SymPy `sympy.polys.polyclasses.ANP.is_zero`
   */
  get isZero(): boolean {
    return this.rep.length === 0;
  }
  /**
   * The coefficients, highest first.
   *
   * @returns The coefficients, highest first.
   * @see SymPy `sympy.polys.polyclasses.ANP.to_list`
   */
  toList(): PythonMPQ[] {
    return [...this.rep];
  }
  /**
   * The defining polynomial coefficients.
   *
   * @returns The defining polynomial coefficients.
   * @see SymPy `sympy.polys.polyclasses.ANP.mod_to_list`
   */
  modToList(): PythonMPQ[] {
    return [...this.mod];
  }
  /**
   * Representations over a common ground domain.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns Representations over a common ground domain.
   * @throws UnificationFailed when the input domains cannot be unified.
   * @see SymPy `sympy.polys.polyclasses.ANP.unify`
   */
  unify(o: ANP): [Domain, (rep: QP) => ANP, QP, QP, QP] {
    if (this.mod.length !== o.mod.length || this.mod.some((c, i) => !c.equals(o.mod[i]))) throw new UnificationFailed('cannot unify algebraic numbers of different fields');
    const dom = this.dom.unify(o.dom);
    return [dom, (rep) => new ANP(rep, this.mod, dom), [...this.rep], [...o.rep], [...this.mod]];
  }
  /**
   * The leading coefficient.
   *
   * @returns The leading coefficient.
   * @see SymPy `sympy.polys.polyclasses.ANP.LC`
   */
  LC(): PythonMPQ {
    return this.rep[0] ?? ZERO;
  }
  /**
   * The sum of the operands.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.polyclasses.ANP.add`
   */
  add(o: unknown): ANP {
    return this.per(polyAdd(this.rep, this.repOf(o)));
  }
  /**
   * The difference of the operands.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The difference of the operands.
   * @see SymPy `sympy.polys.polyclasses.ANP.sub`
   */
  sub(o: unknown): ANP {
    return this.per(polyAdd(this.rep, this.repOf(o).map((c) => c.neg())));
  }
  /**
   * The product of the operands.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The product of the operands.
   * @see SymPy `sympy.polys.polyclasses.ANP.mul`
   */
  mul(o: unknown): ANP {
    return this.per(polyMul(this.rep, this.repOf(o)));
  }
  /**
   * The additive inverse.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.polyclasses.ANP.neg`
   */
  neg(): ANP {
    return this.per(this.rep.map((c) => c.neg()));
  }
  /**
   * This/o; throws NotInvertible for o = 0.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns This/o; throws NotInvertible for o = 0.
   * @see SymPy `sympy.polys.polyclasses.ANP.div`
   */
  div(o: unknown): ANP {
    return this.per(polyMul(this.rep, polyInvert(this.repOf(o), this.mod)));
  }
  /**
   * The field quotient.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The field quotient.
   * @see SymPy `sympy.polys.polyclasses.ANP.quo`
   */
  quo(o: unknown): ANP {
    return this.div(o);
  }
  /**
   * The field remainder; division by a zero divisor is undefined.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The field remainder.
   * @see SymPy `sympy.polys.polyclasses.ANP.rem`
   */
  rem(o: unknown): ANP {
    this.div(o);
    return this.per([]);
  }
  /**
   * The field quotient and zero remainder.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The field quotient and zero remainder.
   * @see SymPy `sympy.polys.polyclasses.ANP.__divmod__`
   */
  divmod(o: unknown): [ANP, ANP] {
    return [this.div(o), this.per([])];
  }
  /**
   * This**n (a negative n inverts).
   *
   * @param n - Exponent or degree.
   * @returns The element raised to the specified exponent.
   * @see SymPy `sympy.polys.polyclasses.ANP.pow`
   */
  pow(n: number): ANP {
    let [r, b] = [this.per([ONE]), n < 0 ? this.per(polyInvert(this.rep, this.mod)) : this];
    for (let k = Math.abs(n); k; k >>= 1) {
      if (k & 1) r = r.mul(b);
      b = b.mul(b);
    }
    return r;
  }
  /**
   * Whether the operand represents the same value.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.polyclasses.ANP.__eq__`
   */
  equals(o: unknown): boolean {
    if (!(o instanceof ANP)) return this.rep.length <= 1 && groundRational(o) !== undefined && this.LC().equals(QQ.convert(o));
    return o.rep.length === this.rep.length && o.rep.every((c, i) => c.equals(this.rep[i])) && o.mod.length === this.mod.length && o.mod.every((c, i) => c.equals(this.mod[i]));
  }
  /**
   * The printable representation.
   *
   * @returns The formatted text.
   */
  toString(): string {
    const list = (f: QP): string => `[${f.map((c) => c.repr()).join(', ')}]`;
    return `ANP(${list(this.rep)}, ${list(this.mod)}, ${this.dom.toString()})`;
  }
  /**
   * The representation of the element with its construction data.
   *
   * @returns The representation of the element with its construction data.
   * @see SymPy `sympy.polys.polyclasses.ANP.__repr__`
   */
  repr(): string {
    return this.toString();
  }
}

/**
 * Dense recursive polynomials over a ground domain.
 *
 * @see SymPy `sympy.polys.polyclasses.DMP_Python`
 */
export class DMPJs {
  /**
   * The dense coefficient representation, leading coefficient first.
   *
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.rep`
   */
  readonly rep: unknown[];
  /**
   * The number of polynomial variables minus one.
   *
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.lev`
   */
  readonly lev: number;
  /**
   * Construct a dense recursive polynomial.
   *
   * @param rep - Dense coefficients in descending order.
   * @param dom - Ground coefficient domain.
   * @param lev - Number of variables minus one.
   * @throws RangeError when the nesting depth and specified polynomial level disagree.
   */
  constructor(rep: DensePoly,
    /** The ground coefficient domain. @see SymPy `sympy.polys.polyclasses.DMP_Python.dom` */
    readonly dom: Domain, lev?: number) {
    const [normal, level] = dmpValidate(rep);
    this.lev = lev ?? level;
    if (this.lev !== level) throw new RangeError('inconsistent polynomial level');
    this.rep = dmpNormal(normal, this.lev, dom);
  }
  private per(rep: DensePoly): DMPJs { return new DMPJs(rep, this.dom, this.lev); }
  private operand(other: unknown): DMPJs {
    if (other instanceof DMPJs) {
      if (other.lev !== this.lev) throw new UnificationFailed('cannot unify different polynomial levels');
      return new DMPJs(dmpConvert(other.rep, this.lev, other.dom, this.dom), this.dom, this.lev);
    }
    return this.per(denseList(dmpGround(this.dom.convert(other), this.lev)));
  }
  /**
   * Convert `f` to a list representation with native coefficients.
   *
   * @returns The dense coefficient list, leading coefficient first.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.to_list`
   */
  toList(): unknown[] { return dmpCopy(this.rep, this.lev); }
  /**
   * The map from exponent vectors to native domain coefficients.
   *
   * @returns The map from exponent vectors to native domain coefficients.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.to_dict`
   */
  toDict(): Map<number[], unknown> { return dmpToDict(this.rep, this.lev); }
  /**
   * The map from exponent vectors to symbolic coefficients.
   *
   * @returns The map from exponent vectors to symbolic coefficients.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.to_sympy_dict`
   */
  toSympyDict(): Map<number[], unknown> { return new Map([...this.toDict()].map(([m, c]) => [m, this.dom.toSympy(c)])); }
  /**
   * Whether the element is zero.
   *
   * @returns Whether the element is zero.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.is_zero`
   */
  get isZero(): boolean { return dmpZeroP(this.rep, this.lev); }
  /**
   * Whether the element is the multiplicative identity.
   *
   * @returns Whether the element is the multiplicative identity.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.is_one`
   */
  get isOne(): boolean { return dmpOneP(this.rep, this.lev, this.dom); }
  /**
   * Whether the polynomial is constant in its generators.
   *
   * @returns Whether the polynomial is constant in its generators.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.is_ground`
   */
  get isGround(): boolean { return this.toDict().size === 0 || [...this.toDict().keys()].every((m) => m.every((e) => e === 0)); }
  /**
   * Whether the leading coefficient is one.
   *
   * @returns Whether the leading coefficient is one.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.is_monic`
   */
  get isMonic(): boolean { return this.dom.isOne(this.LC()); }
  /**
   * Whether the coefficients have unit content.
   *
   * @returns Whether the coefficients have unit content.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.is_primitive`
   */
  get isPrimitive(): boolean { return this.dom.isOne(this.content()); }
  /**
   * Whether the polynomial is square-free.
   *
   * @returns Whether the polynomial is square-free.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.is_sqf`
   */
  get isSqf(): boolean {
    let g: DMPJs = this;
    for (let j = 0; j <= this.lev; j++) g = g.gcd(this.diff(1, j));
    return !this.isZero && g.isGround;
  }
  /**
   * Returns the leading degree of the polynomial in `x_j`.
   *
   * @param j - Index of the polynomial variable.
   * @returns The degree in the selected generator, or `-Infinity` for zero.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.degree`
   */
  degree(j = 0): number { return dmpDegreeIn(this.rep, j, this.lev); }
  /**
   * Returns a list of degrees of the polynomial.
   *
   * @returns A list of degrees of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.degree_list`
   */
  degreeList(): number[] { return dmpDegreeList(this.rep, this.lev); }
  /**
   * Returns the total degree of the polynomial.
   *
   * @returns The total degree of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.total_degree`
   */
  totalDegree(): number { return Math.max(0, ...[...this.toDict().keys()].map((m) => m.reduce((a, b) => a + b, 0))); }
  /**
   * Returns the leading coefficient of the polynomial.
   *
   * @returns The leading coefficient of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.LC`
   */
  LC(): unknown { return dmpGroundLC(this.rep, this.lev, this.dom); }
  /**
   * Returns the trailing coefficient of the polynomial.
   *
   * @returns The trailing coefficient.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.TC`
   */
  TC(): unknown { return dmpGroundTC(this.rep, this.lev, this.dom); }
  /**
   * Returns the `n`-th coefficient of the polynomial.
   *
   * @param N - Exponent vector of the requested coefficient.
   * @returns The coefficient at the specified exponents.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.nth`
   */
  nth(...N: number[]): unknown { return dmpGroundNth(this.rep, N, this.lev, this.dom); }
  /**
   * Returns maximum norm of the polynomial.
   *
   * @returns Maximum norm of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.max_norm`
   */
  maxNorm(): unknown { return dmpMaxNorm(this.rep, this.lev, this.dom); }
  /**
   * Returns l1 norm of the polynomial.
   *
   * @returns L1 norm of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.l1_norm`
   */
  l1Norm(): unknown { return dmpL1Norm(this.rep, this.lev, this.dom); }
  /**
   * Make all coefficients in `f` positive.
   *
   * @returns The polynomial with its coefficients replaced by their absolute values.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.abs`
   */
  abs(): DMPJs { return this.per(dmpAbs(this.rep, this.lev, this.dom)); }
  /**
   * The additive inverse.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.neg`
   */
  neg(): DMPJs { return this.per(dmpNeg(this.rep, this.lev, this.dom)); }
  /**
   * The sum of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.add`
   */
  add(other: unknown): DMPJs { return this.per(dmpAdd(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  /**
   * The difference of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The difference of the operands.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.sub`
   */
  sub(other: unknown): DMPJs { return this.per(dmpSub(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  /**
   * The product of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The product of the operands.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.mul`
   */
  mul(other: unknown): DMPJs { return this.per(dmpMul(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  /**
   * The square of the polynomial.
   *
   * @returns The square of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.sqr`
   */
  sqr(): DMPJs { return this.per(dmpSqr(this.rep, this.lev, this.dom)); }
  /**
   * The element raised to the specified exponent.
   *
   * @param n - Exponent or degree.
   * @returns The element raised to the specified exponent.
   * @throws TypeError when the exponent is not an integer.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.pow`
   */
  pow(n: number): DMPJs {
    if (!Number.isInteger(n)) throw new TypeError('polynomial exponent must be an integer');
    return this.per(dmpPow(this.rep, n, this.lev, this.dom));
  }
  /**
   * Multiply `f` by an element of the ground domain.
   *
   * @param c - Coefficient of the term.
   * @returns The polynomial scaled by the ground coefficient.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.mul_ground`
   */
  mulGround(c: unknown): DMPJs { return this.per(dmpMulGround(this.rep, this.dom.convert(c), this.lev, this.dom)); }
  /**
   * Quotient of the polynomial by an element of the ground domain.
   *
   * @param c - Coefficient of the term.
   * @returns The polynomial obtained by dividing its coefficients by the ground element.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.quo_ground`
   */
  quoGround(c: unknown): DMPJs { return this.per(dmpQuoGround(this.rep, this.dom.convert(c), this.lev, this.dom)); }
  /**
   * Exact quotient of the polynomial by an element of the ground domain.
   *
   * @param c - Coefficient of the term.
   * @returns The exact coefficientwise quotient.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.exquo_ground`
   */
  exquoGround(c: unknown): DMPJs { return this.per(dmpExquoGround(this.rep, this.dom.convert(c), this.lev, this.dom)); }
  /**
   * The quotient and remainder of polynomial division.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The quotient and remainder of polynomial division.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.div`
   */
  div(other: unknown): [DMPJs, DMPJs] { const [q, r] = dmpDiv(this.rep, this.operand(other).rep, this.lev, this.dom); return [this.per(q), this.per(r)]; }
  /**
   * The quotient in the coefficient domain.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The quotient in the coefficient domain.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.quo`
   */
  quo(other: unknown): DMPJs { return this.div(other)[0]; }
  /**
   * The remainder after division.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.rem`
   */
  rem(other: unknown): DMPJs { return this.div(other)[1]; }
  /**
   * The exact quotient, requiring divisibility.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The exact quotient, requiring divisibility.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.exquo`
   */
  exquo(other: unknown): DMPJs { return this.per(dmpExquo(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  /**
   * Polynomial pseudo-division of the polynomial and `g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.pdiv`
   */
  pdiv(other: unknown): [DMPJs, DMPJs] { const [q, r] = dmpPdiv(this.rep, this.operand(other).rep, this.lev, this.dom); return [this.per(q), this.per(r)]; }
  /**
   * Polynomial pseudo-quotient of the polynomial and `g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The pseudo-quotient.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.pquo`
   */
  pquo(other: unknown): DMPJs { return this.pdiv(other)[0]; }
  /**
   * Polynomial pseudo-remainder of the polynomial and `g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The pseudo-remainder.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.prem`
   */
  prem(other: unknown): DMPJs { return this.pdiv(other)[1]; }
  /**
   * Polynomial exact pseudo-quotient of the polynomial and `g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The exact pseudo-quotient.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.pexquo`
   */
  pexquo(other: unknown): DMPJs { return this.per(dmpPexquo(this.rep, this.operand(other).rep, this.lev, this.dom)); }
  /**
   * Computes the `m`-th order derivative of the polynomial in `x_j`.
   *
   * @param m - Order of the derivative.
   * @param j - Index of the polynomial variable.
   * @returns The `m`-th order derivative of the polynomial in `x_j`.
   * @throws TypeError when the derivative order or generator index is not an integer.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.diff`
   */
  diff(m = 1, j = 0): DMPJs {
    if (!Number.isInteger(m) || !Number.isInteger(j)) throw new TypeError('derivative order and generator index must be integers');
    return this.per(defined(dmpTools.dmpDiffIn, 'dense polynomial tools')(this.rep, m, j, this.lev, this.dom));
  }
  /**
   * Evaluates `f` at the given point `a` in `x_j`.
   *
   * @param a - Value substituted for the generator.
   * @param j - Index of the polynomial variable.
   * @returns Evaluates `f` at the given point `a` in `x_j`.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.eval`
   */
  eval(a: unknown, j = 0): unknown {
    const r = defined(dmpTools.dmpEvalIn, 'dense polynomial tools')(this.rep, this.dom.convert(a), j, this.lev, this.dom);
    return this.lev === 0 ? r : new DMPJs(denseList(r), this.dom, this.lev - 1);
  }
  /**
   * Divides all coefficients by `LC(f)`.
   *
   * @returns The polynomial normalized to have leading coefficient one.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.monic`
   */
  monic(): DMPJs { return this.per(defined(dmpTools.dmpGroundMonic, 'dense polynomial tools')(this.rep, this.lev, this.dom)); }
  /**
   * Returns GCD of polynomial coefficients.
   *
   * @returns GCD of polynomial coefficients.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.content`
   */
  content(): unknown { return defined(dmpTools.dmpGroundContent, 'dense polynomial tools')(this.rep, this.lev, this.dom); }
  /**
   * Returns content and a primitive form of the polynomial.
   *
   * @returns Content and a primitive form of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.primitive`
   */
  primitive(): [unknown, DMPJs] { const [c, p] = defined(dmpTools.dmpGroundPrimitive, 'dense polynomial tools')(this.rep, this.lev, this.dom); return [c, this.per(p)]; }
  /**
   * Reduce `f` modulo a constant `p`.
   *
   * @param p - Modulus for reducing coefficients.
   * @returns The polynomial with coefficients reduced modulo the supplied modulus.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.trunc`
   */
  trunc(p: unknown): DMPJs { return this.per(defined(dmpTools.dmpGroundTrunc, 'dense polynomial tools')(this.rep, this.dom.convert(p), this.lev, this.dom)); }
  /**
   * Computes functional composition of the polynomial and `g`.
   *
   * @param g - Second polynomial operand.
   * @returns Functional composition of the polynomial and `g`.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.compose`
   */
  compose(g: DMPJs): DMPJs { return this.per(defined(dmpTools.dmpCompose, 'dense polynomial tools')(this.rep, this.operand(g).rep, this.lev, this.dom)); }
  /**
   * Computes functional decomposition of the polynomial.
   *
   * @returns Functional decomposition of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.decompose`
   */
  decompose(): DMPJs[] { this.univariate(); return defined(dmpTools.dupDecompose, 'dense polynomial tools')(this.rep, this.dom).map((p) => this.per(p)); }
  private univariate(): void { if (this.lev !== 0) throw new RangeError('univariate polynomial expected'); }
  /**
   * Primitive polynomial remainder sequence over recursively polynomial coefficients.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The greatest common divisor.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.gcd`
   */
  gcd(other: unknown): DMPJs {
    let [a, b]: [DMPJs, DMPJs] = [this, this.operand(other)];
    if (a.isZero) return b.normalized();
    if (b.isZero) return a.normalized();
    if (this.dom.toString() === 'ZZ') {
      const terms = (p: DMPJs): Map<string, { e: readonly number[]; c: bigint }> => new Map([...p.toDict()].map(([e, c]) => [e.join(','), { e, c: BigInt(String(c)) }]));
      const candidate = heuGcd(terms(a), terms(b), this.lev + 1);
      if (candidate !== undefined) return this.per(dmpFromDict(new Map([...candidate[0].values()].map(({ e, c }) => [e, c])), this.lev, this.dom));
    }
    if (this.lev === 0) {
      const c = this.dom.isField ? this.dom.one : this.dom.gcd(a.content(), b.content());
      [a, b] = [a.primitive()[1], b.primitive()[1]];
      while (!b.isZero) [a, b] = [b, a.prem(b).primitive()[1]];
      return (this.dom.isField ? a.monic() : a.normalized()).mulGround(c);
    }
    const coefficientContent = (p: DMPJs): DMPJs => p.rep.map((c) => new DMPJs(denseList(c), p.dom, p.lev - 1)).reduce((g, c) => g.gcd(c));
    const primitive = (p: DMPJs): DMPJs => {
      if (p.isZero) return p;
      const c = coefficientContent(p);
      return p.per(p.rep.map((a) => new DMPJs(denseList(a), p.dom, p.lev - 1).exquo(c).rep));
    };
    const c = coefficientContent(a).gcd(coefficientContent(b));
    [a, b] = [primitive(a), primitive(b)];
    while (!b.isZero) [a, b] = [b, primitive(a.prem(b))];
    const h = primitive(a).mul(this.per([c.rep]));
    return this.dom.isField ? h.monic() : h.normalized();
  }
  private normalized(): DMPJs { return this.dom.isNegative(this.LC()) ? this.neg() : this; }
  /**
   * The least common multiple.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The least common multiple.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.lcm`
   */
  lcm(other: unknown): DMPJs {
    const b = this.operand(other);
    if (this.isZero || b.isZero) return this.per(dmpZero(this.lev));
    const h = this.mul(b).exquo(this.gcd(b));
    return this.dom.isField ? h.monic() : h.normalized();
  }
  /**
   * Returns GCD of the polynomial and `g` and their cofactors.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns GCD of the polynomial and `g` and their cofactors.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.cofactors`
   */
  cofactors(other: unknown): [DMPJs, DMPJs, DMPJs] {
    const b = this.operand(other), h = this.gcd(b);
    return h.isZero ? [h, h, h] : [h, this.exquo(h), b.exquo(h)];
  }
  /**
   * Extended Euclidean algorithm, if univariate.
   *
   * @param other - Operand to combine or compare with this value.
   * @param auto - Allow promotion to a field for division.
   * @returns Extended Euclidean algorithm, if univariate.
   * @throws DomainError when the coefficient domain is not a field.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.gcdex`
   */
  gcdex(other: unknown, auto = true): [DMPJs, DMPJs, DMPJs] {
    this.univariate();
    if (!auto && !this.dom.isField) throw new DomainError('Cannot compute extended GCD over a ring');
    const K = this.dom.getField();
    let a = new DMPJs(dmpConvert(this.rep, 0, this.dom, K), K);
    let b = new DMPJs(dmpConvert(this.operand(other).rep, 0, this.dom, K), K);
    let [s0, s1, t0, t1] = [a.operand(1), a.operand(0), a.operand(0), a.operand(1)];
    while (!b.isZero) {
      const [q, r] = a.div(b);
      [a, b, s0, s1, t0, t1] = [b, r, s1, s0.sub(q.mul(s1)), t1, t0.sub(q.mul(t1))];
    }
    const c = a.LC();
    return [s0.quoGround(c), t0.quoGround(c), a.monic()];
  }
  /**
   * Half extended Euclidean algorithm, if univariate.
   *
   * @param other - Operand to combine or compare with this value.
   * @param auto - Allow promotion to a field for division.
   * @returns A Bézout coefficient and the greatest common divisor.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.half_gcdex`
   */
  halfGcdex(other: unknown, auto = true): [DMPJs, DMPJs] { const [s, , h] = this.gcdex(other, auto); return [s, h]; }
  /**
   * Invert `f` modulo `g`, if possible.
   *
   * @param other - Operand to combine or compare with this value.
   * @param auto - Allow promotion to a field for division.
   * @returns The multiplicative inverse modulo the second polynomial.
   * @throws NotInvertible when the element has no multiplicative inverse modulo the given modulus.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.invert`
   */
  invert(other: unknown, auto = true): DMPJs {
    const [s, h] = this.halfGcdex(other, auto);
    if (!h.isOne) throw new NotInvertible('zero divisor');
    return s.rem(other);
  }
  /**
   * Computes the Sturm sequence of the polynomial.
   *
   * @returns The Sturm sequence of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.sturm`
   */
  sturm(): DMPJs[] {
    this.univariate();
    const K = this.dom.getField();
    const f = new DMPJs(dmpConvert(this.sqfPart().rep, 0, this.dom, K), K);
    const out = [f, f.diff()];
    while (!at(out, out.length - 1).isZero) out.push(at(out, out.length - 2).rem(at(out, out.length - 1)).neg());
    return out.slice(0, -1);
  }
  /**
   * Computes square-free part of the polynomial.
   *
   * @returns The square-free part of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.sqf_part`
   */
  sqfPart(): DMPJs {
    if (this.isZero) return this;
    let h: DMPJs = this;
    for (let j = 0; j <= this.lev; j++) h = h.gcd(this.diff(1, j));
    const p = this.exquo(h);
    return this.dom.isField ? p.monic() : p.normalized().primitive()[1];
  }
  /**
   * Returns a list of square-free factors of the polynomial.
   *
   * @returns A list of square-free factors of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.sqf_list`
   */
  sqfList(): [unknown, [DMPJs, number][]] {
    if (this.isZero) return [this.dom.zero, []];
    const c = this.dom.isField ? this.LC() : this.dom.isNegative(this.LC()) ? domainNeg(this.dom, this.content()) : this.content();
    const f = this.exquoGround(c);
    let g: DMPJs = f;
    for (let j = 0; j <= this.lev; j++) g = g.gcd(f.diff(1, j));
    let w = f.exquo(g), i = 1;
    const factors: [DMPJs, number][] = [];
    while (!w.isOne) {
      const y = w.gcd(g), z = w.exquo(y);
      if (!z.isOne) factors.push([z, i]);
      [w, g] = [y, g.exquo(y)];
      i++;
    }
    return [c, factors];
  }
  /** Subresultant PRS with recursive coefficient arithmetic (SymPy dmp_inner_subresultants). */
  private innerSubresultants(other: unknown): [DMPJs[], DMPJs[]] {
    let [f, g]: [DMPJs, DMPJs] = [this, this.operand(other)];
    if (f.degree() < g.degree()) [f, g] = [g, f];
    const coefficient = (p: DMPJs): DMPJs => new DMPJs(p.lev === 0 ? [p.LC()] : denseList(first(p.rep)), p.dom, Math.max(0, p.lev - 1));
    const one = coefficient(g).operand(1);
    if (f.isZero) return [[], []];
    if (g.isZero) return [[f], [one]];
    const times = (p: DMPJs, c: DMPJs): DMPJs => p.lev === 0 ? p.mulGround(c.LC()) : p.mul(p.per([c.rep]));
    const quotient = (p: DMPJs, c: DMPJs): DMPJs => p.lev === 0 ? p.exquoGround(c.LC()) : p.per(p.rep.map((a) => new DMPJs(denseList(a), p.dom, p.lev - 1).exquo(c).rep));
    const R = [f, g];
    let m = g.degree(), d = f.degree() - m;
    let h = times(f.prem(g), one.neg().pow(d + 1));
    let lc = coefficient(g), c = lc.pow(d);
    const S = [one, c];
    c = c.neg();
    while (!h.isZero) {
      const k = h.degree();
      R.push(h);
      [f, g, m, d] = [g, h, k, m - k];
      const b = lc.neg().mul(c.pow(d));
      h = quotient(f.prem(g), b);
      lc = coefficient(g);
      c = d > 1 ? lc.neg().pow(d).exquo(c.pow(d - 1)) : lc.neg();
      S.push(c.neg());
    }
    return [R, S];
  }
  /**
   * Computes subresultant PRS sequence of the polynomial and `g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Subresultant PRS sequence of the polynomial and `g`.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.subresultants`
   */
  subresultants(other: unknown): DMPJs[] { return this.innerSubresultants(other)[0]; }
  /**
   * Computes resultant of the polynomial and `g` via PRS.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The resultant with respect to the elimination variable.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.resultant`
   */
  resultant(other: unknown): unknown {
    const [R, S] = this.innerSubresultants(other);
    const r = R.length === 0 || at(R, R.length - 1).degree() > 0 ? new DMPJs(dmpZero(Math.max(0, this.lev - 1)), this.dom) : at(S, S.length - 1);
    const sign = this.degree() < this.operand(other).degree() && this.degree() * this.operand(other).degree() % 2 !== 0 ? -1 : 1;
    const value = r.mulGround(sign);
    return this.lev === 0 ? value.LC() : value;
  }
  /**
   * Computes discriminant of the polynomial.
   *
   * @returns Discriminant of the polynomial.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.discriminant`
   */
  discriminant(): unknown {
    const n = this.degree();
    if (n <= 0) return this.lev === 0 ? this.dom.zero : new DMPJs(dmpZero(this.lev - 1), this.dom);
    const r = this.resultant(this.diff());
    const sign = (-1) ** (n * (n - 1) / 2);
    return r instanceof DMPJs ? r.mulGround(sign).exquo(new DMPJs(denseList(first(this.rep)), this.dom)) : domainArith(this.dom, 'quo', domainArith(this.dom, 'mul', r, this.dom.convert(sign)), this.LC());
  }
  /**
   * Cancel the common factors of a numerator and denominator.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Cancel the common factors of a numerator and denominator.
   */
  cancelFraction(other: unknown): [unknown, DMPJs, DMPJs] {
    const [a, b, p, q] = this.cancel(other, false);
    return [domainArith(this.dom.getField(), 'quo', a, b), p, q];
  }
  /**
   * Cancel common factors in a rational function `f/g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @param include - Incorporate the scalar factors in the reduced numerator and denominator. If false, return the scalars separately.
   * @returns Cancel common factors in a rational function `f/g`.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.cancel`
   */
  cancel(other: unknown, include: false): [unknown, unknown, DMPJs, DMPJs];
  /**
   * Cancel common factors in a rational function `f/g`.
   *
   * @param other - Operand to combine or compare with this value.
   * @param include - Incorporate the scalar factors in the reduced numerator and denominator. If false, return the scalars separately.
   * @returns Cancel common factors in a rational function `f/g`.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.cancel`
   */
  cancel(other: unknown, include?: true): [DMPJs, DMPJs];
  cancel(other: unknown, include = true): [DMPJs, DMPJs] | [unknown, unknown, DMPJs, DMPJs] {
    const b = this.operand(other);
    const [cp, fp] = defined(dmpTools.dmpClearDenoms, 'dense polynomial tools')(this.rep, this.lev, this.dom);
    const [cq, gp] = defined(dmpTools.dmpClearDenoms, 'dense polynomial tools')(b.rep, this.lev, this.dom);
    const K = this.dom.getRing();
    const [h, f0, g0] = new DMPJs(fp, K).cofactors(new DMPJs(gp, K));
    const f = this.per(dmpConvert(f0.rep, this.lev, K, this.dom));
    const g = this.per(dmpConvert(g0.rep, this.lev, K, this.dom));
    if (h.isZero) return include ? [f, g] : [this.dom.one, this.dom.one, f, g];
    const common = this.dom.gcd(this.dom.convert(cp), this.dom.convert(cq));
    let a = domainArith(this.dom, 'quo', this.dom.convert(cq), common);
    const c = domainArith(this.dom, 'quo', this.dom.convert(cp), common);
    let [p, q] = [f, g];
    if (this.dom.isNegative(p.LC())) { p = p.neg(); a = domainNeg(this.dom, a); }
    if (this.dom.isNegative(q.LC())) { q = q.neg(); a = domainNeg(this.dom, a); }
    return include ? [p.mulGround(a), q.mulGround(c)] : [a, c, p, q];
  }
  /**
   * Remove useless generators from `f`.
   *
   * @returns The polynomial with unused generators removed.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.exclude`
   */
  exclude(): [number[], DMPJs] { const [J, f, u] = dmpExclude(this.rep, this.lev, this.dom); return [J, new DMPJs(f, this.dom, u)]; }
  /**
   * Whether the operand represents the same value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.polyclasses.DMP_Python.__eq__`
   */
  equals(other: unknown): boolean {
    if (!(other instanceof DMPJs) || this.lev !== other.lev) return false;
    const same = (a: unknown, b: unknown): boolean => Array.isArray(a) && Array.isArray(b) ? a.length === b.length && a.every((c, i) => same(c, b[i])) : groundEquals(a, b);
    return same(this.rep, other.rep);
  }
  /**
   * The printable representation.
   *
   * @returns The formatted text.
   */
  toString(): string {
    const format = (c: unknown): string => Array.isArray(c) ? `[${c.map(format).join(', ')}]` : c instanceof PythonMPQ ? c.repr() : String(c);
    return `DMP_Python(${format(this.rep)}, ${String(this.dom)})`;
  }
}

function denseList(value: unknown): unknown[] {
  if (!Array.isArray(value)) throw new TypeError('dense polynomial coefficient must be a list');
  return value;
}
