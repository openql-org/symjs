// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/gaussiandomains.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The Gaussian integers ZZ_I and Gaussian rationals QQ_I (SymPy
 * GaussianIntegerRing, GaussianRationalField) and their elements x + y*I
 * (SymPy GaussianInteger, GaussianRational). An element prints as
 * `3 + 4*I` (str) and `ZZ_I(3, 4)` (repr).
 */

import { ExactQuotientFailed } from '../../core/errors';
import { lcm as ilcm } from '../../core/numbers';
import { at, defined } from '../../core/guard';
import type { ExprLike } from '../../core/nodes';
import { Add, Expr, Mul, Rational, S } from '../../core/nodes';
import { add, mul, sympify } from '../../core/ops';
import { str } from '../../printing/str';
import { expand } from '../../simplify/expand';
import { CoercionFailed, Domain, QQ, ZZ, groundRational, type UnificationKind } from '../domains';
import { PythonMPQ } from './pythonrational';

type Num = PythonMPQ | bigint | number;
const q = (a: Num): PythonMPQ => (a instanceof PythonMPQ ? a : new PythonMPQ(a));
/** Python floor division of rationals that are integers (the Gaussian-integer quotient). */
const floorDiv = (a: bigint, b: bigint): bigint => {
  const r = a / b;
  return a % b !== 0n && a < 0n !== b < 0n ? r - 1n : r;
};

/**
 * An element x + y*I of ZZ_I or QQ_I.
 *
 * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement`
 */
export abstract class GaussianElement {
  /** The real component. */
  readonly re: PythonMPQ;
  /** The imaginary component. */
  readonly im: PythonMPQ;
  /**
   * Constructs a Gaussian value from its real and imaginary components.
   *
   * @param x - Real component.
   * @param y - Imaginary component.
   */
  constructor(x: Num, y: Num = 0n) {
    [this.re, this.im] = [q(x), q(y)];
  }
  /**
   * The domain of the element.
   *
   * @returns The algebra or domain containing this element.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.parent`
   */
  abstract parent(): GaussianDomain;
  protected abstract make(x: PythonMPQ, y: PythonMPQ): GaussianElement;
  /** The other operand as an element of this element's domain. */
  protected other(o: unknown): GaussianElement {
    return o instanceof GaussianElement ? o : this.parent().convert(o);
  }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  get isZero(): boolean {
    return this.re.isZero && this.im.isZero;
  }
  /**
   * Adds the other operand to this value.
   *
   * @param o - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__add__`
   */
  add(o: unknown): GaussianElement {
    const b = this.other(o);
    return this.make(this.re.add(b.re), this.im.add(b.im));
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param o - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__sub__`
   */
  sub(o: unknown): GaussianElement {
    const b = this.other(o);
    return this.make(this.re.sub(b.re), this.im.sub(b.im));
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param o - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__mul__`
   */
  mul(o: unknown): GaussianElement {
    const b = this.other(o);
    return this.make(this.re.mul(b.re).sub(this.im.mul(b.im)), this.re.mul(b.im).add(this.im.mul(b.re)));
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__neg__`
   */
  neg(): GaussianElement {
    return this.make(this.re.neg(), this.im.neg());
  }
  /**
   * This**n for an integer n (a negative n divides in QQ_I).
   *
   * @param n - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__pow__`
   */
  pow(n: number): GaussianElement {
    if (n < 0) return QQ_I.oneElement().div(this.pow(-n));
    let [r, base]: [GaussianElement, GaussianElement] = [this.parent().oneElement(), this];
    for (let k = n; k; k >>= 1) {
      if (k & 1) r = r.mul(base);
      base = base.mul(base);
    }
    return r;
  }
  /**
   * Divides in the field of Gaussian rationals.
   *
   * @param o - Divisor.
   * @returns The quotient.
   * @throws RangeError when the divisor is zero.
   */
  div(o: unknown): GaussianRational {
    const a = QQ_I.convert(this);
    const b = QQ_I.convert(o);
    if (b.isZero) throw new RangeError(`${this.toString()} / 0`);
    const c = b.re.mul(b.re).add(b.im.mul(b.im));
    return new GaussianRational(a.re.mul(b.re).add(a.im.mul(b.im)).div(c), a.im.mul(b.re).sub(a.re.mul(b.im)).div(c));
  }
  /**
   * Divides once to obtain both the quotient and the remainder.
   *
   * @param o - Divisor.
   * @returns The quotient and remainder.
   */
  abstract divmod(o: unknown): [GaussianElement, GaussianElement];
  /**
   * Computes the quotient under the division rule of this domain.
   *
   * @param o - Divisor.
   * @returns The quotient under floor division.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__floordiv__`
   */
  floordiv(o: unknown): GaussianElement { return this.divmod(o)[0]; }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @param o - Divisor.
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__mod__`
   */
  mod(o: unknown): GaussianElement { return this.divmod(o)[1]; }
  /**
   * The quadrant 0..3 of the element.
   *
   * @returns The quadrant index from zero through three.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.quadrant`
   */
  quadrant(): number {
    if (this.im.sign > 0) return this.re.sign > 0 ? 0 : 1;
    if (this.im.sign < 0) return this.re.sign < 0 ? 2 : 3;
    return this.re.sign >= 0 ? 0 : 2;
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__eq__`
   */
  equals(o: unknown): boolean {
    return o instanceof GaussianElement && o.constructor === this.constructor && o.re.equals(this.re) && o.im.equals(this.im);
  }
  /**
   * Displays the real and imaginary coefficients with the imaginary unit `I`.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__str__`
   */
  toString(): string {
    return str(this.parent().toSympy(this));
  }
  /**
   * Formats the element as a call to its Gaussian coefficient domain.
   *
   * @returns The constructor-style representation.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianElement.__repr__`
   */
  repr(): string {
    return `${this.parent().toString()}(${this.re.toString()}, ${this.im.toString()})`;
  }
}

/**
 * A Gaussian integer x + y*I.
 *
 * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger`
 * @example
 * ```ts
 * import { GaussianInteger } from '@symjs/symjs';
 *
 * new GaussianInteger(2, 3).toString(); // => 2 + 3*I
 * ```
 */
export class GaussianInteger extends GaussianElement {
  /**
   * Constructs a Gaussian value from its real and imaginary components.
   *
   * @param x - Real component.
   * @param y - Imaginary component.
   * @throws CoercionFailed when either component is not integral.
   */
  constructor(x: Num, y: Num = 0n) {
    super(x, y);
    if (this.re.denominator !== 1n || this.im.denominator !== 1n) throw new CoercionFailed(`${this.re.toString()} + ${this.im.toString()}*I is not a Gaussian integer`);
  }
  /**
   * Reads the coefficient of the real basis element.
   *
   * @returns The real coefficient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.x`
   */
  get x(): bigint {
    return this.re.numerator;
  }
  /**
   * Reads the coefficient of the imaginary unit.
   *
   * @returns The imaginary coefficient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.y`
   */
  get y(): bigint {
    return this.im.numerator;
  }
  /**
   * Returns the algebra or domain containing this element.
   *
   * @returns The algebra or domain containing this element.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.parent`
   */
  parent(): GaussianDomain {
    return ZZ_I;
  }
  /**
   * Adds the other operand to this value.
   *
   * @param o - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.__add__`
   */
  override add(o: unknown): GaussianInteger {
    return ZZ_I.convert(super.add(o));
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param o - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.__sub__`
   */
  override sub(o: unknown): GaussianInteger {
    return ZZ_I.convert(super.sub(o));
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param o - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.__mul__`
   */
  override mul(o: unknown): GaussianInteger {
    return ZZ_I.convert(super.mul(o));
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.__neg__`
   */
  override neg(): GaussianInteger {
    return ZZ_I.convert(super.neg());
  }
  protected make(x: PythonMPQ, y: PythonMPQ): GaussianInteger {
    return new GaussianInteger(x, y);
  }
  /**
   * Divides once to obtain both the quotient and the remainder.
   *
   * @param o - Divisor.
   * @returns The quotient and remainder.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianInteger.__divmod__`
   */
  divmod(o: unknown): [GaussianInteger, GaussianInteger] {
    const b = ZZ_I.convert(o);
    if (b.isZero) throw new RangeError(`divmod(${this.toString()}, 0)`);
    const [x, y] = [b.x, b.y];
    const a1 = this.x * x + this.y * y;
    const b1 = -this.x * y + this.y * x;
    const c = x * x + y * y;
    const qq = new GaussianInteger(floorDiv(2n * a1 + c, 2n * c), floorDiv(2n * b1 + c, 2n * c));
    return [qq, this.sub(qq.mul(b))];
  }
}

/**
 * A Gaussian rational x + y*I.
 *
 * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational`
 * @example
 * ```ts
 * import { GaussianRational, PythonMPQ } from '@symjs/symjs';
 *
 * new GaussianRational(new PythonMPQ(2, 3), new PythonMPQ(4, 5)).toString(); // => 2/3 + 4*I/5
 * ```
 */
export class GaussianRational extends GaussianElement {
  /**
   * Reads the coefficient of the real basis element.
   *
   * @returns The real coefficient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.x`
   */
  get x(): PythonMPQ {
    return this.re;
  }
  /**
   * Reads the coefficient of the imaginary unit.
   *
   * @returns The imaginary coefficient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.y`
   */
  get y(): PythonMPQ {
    return this.im;
  }
  /**
   * Returns the algebra or domain containing this element.
   *
   * @returns The algebra or domain containing this element.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.parent`
   */
  parent(): GaussianDomain {
    return QQ_I;
  }
  /**
   * Adds the other operand to this value.
   *
   * @param o - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.__add__`
   */
  override add(o: unknown): GaussianRational {
    return QQ_I.convert(super.add(o));
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param o - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.__sub__`
   */
  override sub(o: unknown): GaussianRational {
    return QQ_I.convert(super.sub(o));
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param o - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.__mul__`
   */
  override mul(o: unknown): GaussianRational {
    return QQ_I.convert(super.mul(o));
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.__neg__`
   */
  override neg(): GaussianRational {
    return QQ_I.convert(super.neg());
  }
  protected make(x: PythonMPQ, y: PythonMPQ): GaussianRational {
    return new GaussianRational(x, y);
  }
  /**
   * Divides once to obtain both the quotient and the remainder.
   *
   * @param o - Divisor.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRational.__divmod__`
   */
  divmod(o: unknown): [GaussianRational, GaussianRational] {
    return [this.div(o), QQ_I.new(0n, 0n)];
  }
}

/** Shared parts of ZZ_I and QQ_I (SymPy GaussianDomain). */
export abstract class GaussianDomain extends Domain {
  readonly ground = 'EX' as const;
  abstract override new(x: unknown, y?: unknown): GaussianElement;
  override get hasAssocRing(): boolean {
    return true;
  }
  override get hasCharacteristicZero(): boolean {
    return true;
  }
  /** Elements are expressions x + y*I with x, y in dom (the expression model of the domain). */
  canon(e: Expr): Expr {
    return expand(e);
  }
  fromSympy(eIn: ExprLike): Expr {
    return this.toSympy(this.convert(sympify(eIn)));
  }
  /** x + I*y (SymPy to_sympy). */
  override toSympy(a: unknown): Expr {
    if (!(a instanceof GaussianElement)) return super.toSympy(a);
    const [x, y] = [Rational.of(a.re.numerator, a.re.denominator), Rational.of(a.im.numerator, a.im.denominator)];
    return add(x, mul(S.I, y));
  }
  /** An element from x + y*I with x, y in dom (SymPy from_sympy); throws CoercionFailed. */
  protected elementFromSympy(a: Expr): GaussianElement {
    const terms = a instanceof Add ? a.args : [a];
    let [x, y]: [Expr, Expr] = [S.Zero, S.Zero];
    for (const t of terms) {
      const fs = t instanceof Mul ? t.args : [t];
      const iIdx = fs.findIndex((f) => f === S.I);
      if (iIdx < 0) x = add(x, t);
      else y = add(y, mul(...fs.filter((_f, k) => k !== iIdx)));
    }
    if (!(x instanceof Rational && y instanceof Rational)) throw new CoercionFailed(`${str(a)} is not Gaussian`);
    return this.new(this.dom.convert(x), this.dom.convert(y));
  }
  override convert(a: unknown, base?: Domain): GaussianElement {
    if (a instanceof GaussianElement) return this.new(a.re, a.im);
    const v = base !== undefined && !base.equals(this) ? base.toSympy(a) : a;
    if (v instanceof Expr) return this.elementFromSympy(expand(v));
    const r = groundRational(v);
    if (r === undefined) throw new CoercionFailed(`cannot convert ${String(a)} to ${this.toString()}`);
    return this.new(this.dom.convert(v), 0n);
  }
  override isZero(a: unknown): boolean {
    return a instanceof GaussianElement ? a.isZero : super.isZero(a);
  }
  /** SymPy: Gaussian elements are neither positive nor negative. */
  override isNegative(_a: unknown): boolean {
    return false;
  }
  override isPositive(_a: unknown): boolean {
    return false;
  }
  override isNonnegative(_a: unknown): boolean {
    return false;
  }
  override isNonpositive(_a: unknown): boolean {
    return false;
  }
  /** The unit u with u*d in the first quadrant (SymPy canonical_unit). */
  override canonicalUnit(a: unknown): GaussianElement {
    const units = [this.new(1n, 0n), this.new(0n, 1n), this.new(-1n, 0n), this.new(0n, -1n)];
    return at(units, (4 - this.convert(a).quadrant()) % 4);
  }
  /** The generator I of the extension (SymPy imag_unit). */
  imagUnit(): GaussianElement {
    return this.new(0n, 1n);
  }
  /** The element 1 (SymPy one). */
  oneElement(): GaussianElement {
    return this.new(1n, 0n);
  }
  override equals(o: Domain): boolean {
    return o.toString() === this.toString();
  }
  /** The characteristic 0. */
  characteristic(): bigint {
    return 0n;
  }
}

/**
 * Represents the ring of numbers with integer real and imaginary components.
 *
 * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing`
 * @example
 * ```ts
 * import { ZZ_I } from '@symjs/symjs';
 *
 * const z = ZZ_I.new(5, 1);
 * z.mul(ZZ_I.new(2, 3)).toString(); // => 7 + 17*I
 * ```
 */
export class GaussianIntegerRing extends GaussianDomain {
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.is_Field`
   */
  readonly isField = false;
  /**
   * The domain of the real and imaginary parts.
   *
   * @returns The underlying coefficient domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.dom`
   */
  override get dom(): Domain {
    return ZZ;
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.__str__`
   */
  toString(): string {
    return 'ZZ_I';
  }
  protected override get unificationKind(): UnificationKind {
    return 'ZZ_I';
  }
  /**
   * Builds a Gaussian element with the supplied real and imaginary parts.
   *
   * @param x - Real component.
   * @param y - Imaginary component.
   * @returns The newly constructed element.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.new`
   */
  override new(x: unknown, y: unknown = 0n): GaussianInteger {
    return new GaussianInteger(ZZ.convert(x), ZZ.convert(y));
  }
  /**
   * Coerces the input into the target domain.
   *
   * @param a - Element on which to operate.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.convert`
   */
  override convert(a: unknown, base?: Domain): GaussianInteger {
    const e = super.convert(a, base);
    return new GaussianInteger(e.re, e.im);
  }
  /**
   * Checks whether the input already belongs to the native element type.
   *
   * @param a - Element on which to operate.
   * @returns Whether the value is a native element of the domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.of_type`
   */
  override ofType(a: unknown): boolean {
    return a instanceof GaussianInteger;
  }
  /**
   * Tests for multiplicative invertibility.
   *
   * @param a - Element on which to operate.
   * @returns Whether the element has a multiplicative inverse.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.is_unit`
   */
  override isUnit(a: unknown): boolean {
    const e = this.convert(a);
    return e.re.mul(e.re).add(e.im.mul(e.im)).equals(1n);
  }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.get_field`
   */
  getField(): Domain {
    return QQ_I;
  }
  /**
   * Moves the first element into the canonical quadrant and applies the same unit to the remaining
   * elements.
   *
   * @param d - Denominator to cancel.
   * @param args - Components used to construct the value.
   * @returns The elements multiplied by the same normalizing unit.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.normalize`
   */
  normalize(d: GaussianInteger, ...args: GaussianInteger[]): GaussianInteger[] {
    const unit = this.canonicalUnit(d);
    return [d, ...args].map((a) => a.mul(unit));
  }
  /**
   * Computes a greatest common divisor of two Gaussian integers in the canonical quadrant.
   *
   * @param aIn - Element on which to operate.
   * @param bIn - Second operand.
   * @returns A greatest common divisor.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.gcd`
   */
  override gcd(aIn: unknown, bIn: unknown): GaussianInteger {
    let [a, b] = [this.convert(aIn), this.convert(bIn)];
    while (!b.isZero) [a, b] = [b, a.divmod(b)[1]];
    return at(this.normalize(a), 0);
  }
  /**
   * Computes Bézout coefficients and a greatest common divisor of two Gaussian integers.
   *
   * @param aIn - Element on which to operate.
   * @param bIn - Second operand.
   * @returns Bézout coefficients and their greatest common divisor.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.gcdex`
   */
  gcdex(aIn: unknown, bIn: unknown): [GaussianInteger, GaussianInteger, GaussianInteger] {
    let [a, b] = [this.convert(aIn), this.convert(bIn)];
    let [xa, xb, ya, yb] = [this.new(1n), this.new(0n), this.new(0n), this.new(1n)];
    while (!b.isZero) {
      const qq = a.divmod(b)[0];
      [a, b] = [b, a.sub(qq.mul(b))];
      [xa, xb] = [xb, xa.sub(qq.mul(xb))];
      [ya, yb] = [yb, ya.sub(qq.mul(yb))];
    }
    const [g, x, y] = this.normalize(a, xa, ya);
    return [defined(x), defined(y), defined(g)];
  }
  /**
   * Computes a least common multiple in this domain.
   *
   * @param a - Element on which to operate.
   * @param b - Second operand.
   * @returns A least common multiple.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.lcm`
   */
  override lcm(a: unknown, b: unknown): GaussianInteger {
    return this.convert(a).mul(b).divmod(this.gcd(a, b))[0];
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.div`
   */
  override div(a: unknown, b: unknown): [GaussianInteger, GaussianInteger] {
    return this.convert(a).divmod(b);
  }
  /**
   * Divides in the coefficient domain, requiring exact divisibility.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The exact quotient.
   * @throws ExactQuotientFailed when the divisor does not divide exactly in the domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.exquo`
   */
  override exquo(a: unknown, b: unknown): GaussianInteger {
    const [qq, r] = this.convert(a).divmod(b);
    if (!r.isZero) throw new ExactQuotientFailed(`${String(b)} does not divide ${String(a)} in ZZ_I`);
    return qq;
  }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianIntegerRing.rem`
   */
  override rem(a: unknown, b: unknown): GaussianInteger {
    return this.convert(a).divmod(b)[1];
  }
}

/**
 * Represents the field of numbers with rational real and imaginary components.
 *
 * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField`
 * @example
 * ```ts
 * import { QQ_I } from '@symjs/symjs';
 *
 * QQ_I.getRing().toString(); // => ZZ_I
 * ```
 */
export class GaussianRationalField extends GaussianDomain {
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.is_Field`
   */
  readonly isField = true;
  /**
   * The domain of the real and imaginary parts.
   *
   * @returns The underlying coefficient domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.dom`
   */
  override get dom(): Domain {
    return QQ;
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.__str__`
   */
  toString(): string {
    return 'QQ_I';
  }
  protected override get unificationKind(): UnificationKind {
    return 'QQ_I';
  }
  /**
   * Builds a Gaussian element with the supplied real and imaginary parts.
   *
   * @param x - Real component.
   * @param y - Imaginary component.
   * @returns The newly constructed element.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.new`
   */
  override new(x: unknown, y: unknown = 0n): GaussianRational {
    return new GaussianRational(QQ.convert(x), QQ.convert(y));
  }
  /**
   * Coerces the input into the target domain.
   *
   * @param a - Element on which to operate.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.convert`
   */
  override convert(a: unknown, base?: Domain): GaussianRational {
    const e = super.convert(a, base);
    return new GaussianRational(e.re, e.im);
  }
  /**
   * Checks whether the input already belongs to the native element type.
   *
   * @param a - Element on which to operate.
   * @returns Whether the value is a native element of the domain.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.of_type`
   */
  override ofType(a: unknown): boolean {
    return a instanceof GaussianRational;
  }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.get_field`
   */
  getField(): Domain {
    return this;
  }
  /**
   * Finds the ring associated with this domain.
   *
   * @returns The associated ring.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.get_ring`
   */
  override getRing(): Domain {
    return ZZ_I;
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.div`
   */
  override div(a: unknown, b: unknown): [GaussianRational, GaussianRational] {
    return this.convert(a).divmod(b);
  }
  /**
   * Divides in the coefficient domain, requiring exact divisibility.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The exact quotient.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.exquo`
   */
  override exquo(a: unknown, b: unknown): GaussianRational {
    return this.convert(a).div(b);
  }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @param _a - Dividend in the coefficient domain.
   * @param _b - Divisor.
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.rem`
   */
  override rem(_a: unknown, _b: unknown): GaussianRational {
    return this.new(0n, 0n);
  }
  /**
   * Gcd over a field: the gcd of the denominators' cleared form is 1 unless both are zero.
   *
   * @param a - Element on which to operate.
   * @param b - Second operand.
   * @returns A greatest common divisor.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.gcd`
   */
  override gcd(a: unknown, b: unknown): GaussianRational {
    return this.new(this.convert(a).isZero && this.convert(b).isZero ? 0n : 1n);
  }
  /**
   * Computes a least common multiple in this domain.
   *
   * @param a - Element on which to operate.
   * @param b - Second operand.
   * @returns A least common multiple.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.lcm`
   */
  override lcm(a: unknown, b: unknown): GaussianRational {
    return this.convert(a).mul(b);
  }
  /**
   * The common denominator of the parts, as a Gaussian integer.
   *
   * @param a - Element on which to operate.
   * @returns The denominator.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.denom`
   */
  denom(a: unknown): GaussianInteger {
    const e = this.convert(a);
    return ZZ_I.new(ilcm(e.re.denominator, e.im.denominator));
  }
  /**
   * A times its denominator.
   *
   * @param a - Element on which to operate.
   * @returns The numerator.
   * @see SymPy `sympy.polys.domains.gaussiandomains.GaussianRationalField.numer`
   */
  numer(a: unknown): GaussianInteger {
    return ZZ_I.convert(this.convert(a).mul(this.denom(a)));
  }
}

/**
 * The ring of Gaussian integers.
 *
 * @see SymPy `sympy.polys.domains.ZZ_I`
 * @example
 * ```ts
 * import { ZZ_I } from '@symjs/symjs';
 *
 * ZZ_I.new(3, 4).toString(); // => 3 + 4*I
 * ZZ_I.getField().toString(); // => QQ_I
 * ```
 */
export const ZZ_I: GaussianIntegerRing = new GaussianIntegerRing();
/**
 * The field of Gaussian rationals.
 *
 * @see SymPy `sympy.polys.domains.QQ_I`
 * @example
 * ```ts
 * import { PythonMPQ, QQ_I } from '@symjs/symjs';
 *
 * QQ_I.new(new PythonMPQ(2, 3), new PythonMPQ(4, 5)).toString(); // => 2/3 + 4*I/5
 * ```
 */
export const QQ_I: GaussianRationalField = new GaussianRationalField();
