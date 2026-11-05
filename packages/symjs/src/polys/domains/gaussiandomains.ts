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
import { CoercionFailed, Domain, QQ, ZZ, groundRational } from '../domains';
import { PythonMPQ } from './pythonrational';

type Num = PythonMPQ | bigint | number;
const q = (a: Num): PythonMPQ => (a instanceof PythonMPQ ? a : new PythonMPQ(a));
/** Python floor division of rationals that are integers (the Gaussian-integer quotient). */
const floorDiv = (a: bigint, b: bigint): bigint => {
  const r = a / b;
  return a % b !== 0n && a < 0n !== b < 0n ? r - 1n : r;
};

/** An element x + y*I of ZZ_I or QQ_I (SymPy GaussianElement). */
export abstract class GaussianElement {
  readonly re: PythonMPQ;
  readonly im: PythonMPQ;
  constructor(x: Num, y: Num = 0n) {
    [this.re, this.im] = [q(x), q(y)];
  }
  /** The domain of the element (SymPy parent). */
  abstract parent(): GaussianDomain;
  protected abstract make(x: PythonMPQ, y: PythonMPQ): GaussianElement;
  /** The other operand as an element of this element's domain. */
  protected other(o: unknown): GaussianElement {
    return o instanceof GaussianElement ? o : this.parent().convert(o);
  }
  get isZero(): boolean {
    return this.re.isZero && this.im.isZero;
  }
  add(o: unknown): GaussianElement {
    const b = this.other(o);
    return this.make(this.re.add(b.re), this.im.add(b.im));
  }
  sub(o: unknown): GaussianElement {
    const b = this.other(o);
    return this.make(this.re.sub(b.re), this.im.sub(b.im));
  }
  mul(o: unknown): GaussianElement {
    const b = this.other(o);
    return this.make(this.re.mul(b.re).sub(this.im.mul(b.im)), this.re.mul(b.im).add(this.im.mul(b.re)));
  }
  neg(): GaussianElement {
    return this.make(this.re.neg(), this.im.neg());
  }
  /** this**n for an integer n (a negative n divides in QQ_I). */
  pow(n: number): GaussianElement {
    if (n < 0) return QQ_I.oneElement().div(this.pow(-n));
    let [r, base]: [GaussianElement, GaussianElement] = [this.parent().oneElement(), this];
    for (let k = n; k; k >>= 1) {
      if (k & 1) r = r.mul(base);
      base = base.mul(base);
    }
    return r;
  }
  /** The exact quotient in QQ_I (SymPy a / b). */
  div(o: unknown): GaussianRational {
    const a = QQ_I.convert(this);
    const b = QQ_I.convert(o);
    if (b.isZero) throw new RangeError(`${this.toString()} / 0`);
    const c = b.re.mul(b.re).add(b.im.mul(b.im));
    return new GaussianRational(a.re.mul(b.re).add(a.im.mul(b.im)).div(c), a.im.mul(b.re).sub(a.re.mul(b.im)).div(c));
  }
  /** [quotient, remainder] (SymPy divmod). */
  abstract divmod(o: unknown): [GaussianElement, GaussianElement];
  /** The quadrant 0..3 of the element (SymPy quadrant). */
  quadrant(): number {
    if (this.im.sign > 0) return this.re.sign > 0 ? 0 : 1;
    if (this.im.sign < 0) return this.re.sign < 0 ? 2 : 3;
    return this.re.sign >= 0 ? 0 : 2;
  }
  equals(o: unknown): boolean {
    return o instanceof GaussianElement && o.constructor === this.constructor && o.re.equals(this.re) && o.im.equals(this.im);
  }
  /** SymPy str(a): `3 + 4*I`. */
  toString(): string {
    return str(this.parent().toSympy(this));
  }
  /** SymPy repr(a): `ZZ_I(3, 4)`. */
  repr(): string {
    return `${this.parent().toString()}(${this.re.toString()}, ${this.im.toString()})`;
  }
}

/** A Gaussian integer x + y*I (SymPy GaussianInteger). */
export class GaussianInteger extends GaussianElement {
  constructor(x: Num, y: Num = 0n) {
    super(x, y);
    if (this.re.denominator !== 1n || this.im.denominator !== 1n) throw new CoercionFailed(`${this.re.toString()} + ${this.im.toString()}*I is not a Gaussian integer`);
  }
  get x(): bigint {
    return this.re.numerator;
  }
  get y(): bigint {
    return this.im.numerator;
  }
  parent(): GaussianDomain {
    return ZZ_I;
  }
  override add(o: unknown): GaussianInteger {
    return ZZ_I.convert(super.add(o));
  }
  override sub(o: unknown): GaussianInteger {
    return ZZ_I.convert(super.sub(o));
  }
  override mul(o: unknown): GaussianInteger {
    return ZZ_I.convert(super.mul(o));
  }
  override neg(): GaussianInteger {
    return ZZ_I.convert(super.neg());
  }
  protected make(x: PythonMPQ, y: PythonMPQ): GaussianInteger {
    return new GaussianInteger(x, y);
  }
  /** The quotient rounding to the nearest Gaussian integer (SymPy GaussianInteger.__divmod__). */
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

/** A Gaussian rational x + y*I (SymPy GaussianRational). */
export class GaussianRational extends GaussianElement {
  get x(): PythonMPQ {
    return this.re;
  }
  get y(): PythonMPQ {
    return this.im;
  }
  parent(): GaussianDomain {
    return QQ_I;
  }
  override add(o: unknown): GaussianRational {
    return QQ_I.convert(super.add(o));
  }
  override sub(o: unknown): GaussianRational {
    return QQ_I.convert(super.sub(o));
  }
  override mul(o: unknown): GaussianRational {
    return QQ_I.convert(super.mul(o));
  }
  override neg(): GaussianRational {
    return QQ_I.convert(super.neg());
  }
  protected make(x: PythonMPQ, y: PythonMPQ): GaussianRational {
    return new GaussianRational(x, y);
  }
  divmod(o: unknown): [GaussianRational, GaussianRational] {
    return [this.div(o), QQ_I.new(0n, 0n)];
  }
}

/** Shared parts of ZZ_I and QQ_I (SymPy GaussianDomain). */
export abstract class GaussianDomain extends Domain {
  readonly ground = 'EX' as const;
  abstract override new(x: unknown, y?: unknown): GaussianElement;
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
  canonicalUnit(d: GaussianElement): GaussianElement {
    const units = [this.new(1n, 0n), this.new(0n, 1n), this.new(-1n, 0n), this.new(0n, -1n)];
    return at(units, (4 - d.quadrant()) % 4);
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

/** SymPy ZZ_I: the Gaussian integers. */
export class GaussianIntegerRing extends GaussianDomain {
  readonly isField = false;
  /** The domain of the real and imaginary parts (SymPy dom). */
  override get dom(): Domain {
    return ZZ;
  }
  toString(): string {
    return 'ZZ_I';
  }
  override new(x: unknown, y: unknown = 0n): GaussianInteger {
    return new GaussianInteger(ZZ.convert(x), ZZ.convert(y));
  }
  override convert(a: unknown, base?: Domain): GaussianInteger {
    const e = super.convert(a, base);
    return new GaussianInteger(e.re, e.im);
  }
  override ofType(a: unknown): boolean {
    return a instanceof GaussianInteger;
  }
  getField(): Domain {
    return QQ_I;
  }
  /** d made canonical (first quadrant), with the same unit applied to the others (SymPy normalize). */
  normalize(d: GaussianInteger, ...args: GaussianInteger[]): GaussianInteger[] {
    const unit = this.canonicalUnit(d);
    return [d, ...args].map((a) => a.mul(unit));
  }
  /** The gcd normalized to the first quadrant (SymPy ZZ_I.gcd). */
  override gcd(aIn: unknown, bIn: unknown): GaussianInteger {
    let [a, b] = [this.convert(aIn), this.convert(bIn)];
    while (!b.isZero) [a, b] = [b, a.divmod(b)[1]];
    return at(this.normalize(a), 0);
  }
  /** [x, y, g] with a*x + b*y = g = gcd(a, b) (SymPy ZZ_I.gcdex). */
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
  override lcm(a: unknown, b: unknown): GaussianInteger {
    return this.convert(a).mul(b).divmod(this.gcd(a, b))[0];
  }
  override div(a: unknown, b: unknown): [GaussianInteger, GaussianInteger] {
    return this.convert(a).divmod(b);
  }
  override exquo(a: unknown, b: unknown): GaussianInteger {
    const [qq, r] = this.convert(a).divmod(b);
    if (!r.isZero) throw new ExactQuotientFailed(`${String(b)} does not divide ${String(a)} in ZZ_I`);
    return qq;
  }
  override rem(a: unknown, b: unknown): GaussianInteger {
    return this.convert(a).divmod(b)[1];
  }
}

/** SymPy QQ_I: the Gaussian rationals. */
export class GaussianRationalField extends GaussianDomain {
  readonly isField = true;
  /** The domain of the real and imaginary parts (SymPy dom). */
  override get dom(): Domain {
    return QQ;
  }
  toString(): string {
    return 'QQ_I';
  }
  override new(x: unknown, y: unknown = 0n): GaussianRational {
    return new GaussianRational(QQ.convert(x), QQ.convert(y));
  }
  override convert(a: unknown, base?: Domain): GaussianRational {
    const e = super.convert(a, base);
    return new GaussianRational(e.re, e.im);
  }
  override ofType(a: unknown): boolean {
    return a instanceof GaussianRational;
  }
  getField(): Domain {
    return this;
  }
  override getRing(): Domain {
    return ZZ_I;
  }
  override div(a: unknown, b: unknown): [GaussianRational, GaussianRational] {
    return this.convert(a).divmod(b);
  }
  override exquo(a: unknown, b: unknown): GaussianRational {
    return this.convert(a).div(b);
  }
  override rem(_a: unknown, _b: unknown): GaussianRational {
    return this.new(0n, 0n);
  }
  /** gcd over a field: the gcd of the denominators' cleared form is 1 unless both are zero. */
  override gcd(a: unknown, b: unknown): GaussianRational {
    return this.new(this.convert(a).isZero && this.convert(b).isZero ? 0n : 1n);
  }
  override lcm(a: unknown, b: unknown): GaussianRational {
    return this.convert(a).mul(b);
  }
  /** The common denominator of the parts, as a Gaussian integer (SymPy denom). */
  denom(a: unknown): GaussianInteger {
    const e = this.convert(a);
    return ZZ_I.new(ilcm(e.re.denominator, e.im.denominator));
  }
  /** a times its denominator (SymPy numer). */
  numer(a: unknown): GaussianInteger {
    return ZZ_I.convert(this.convert(a).mul(this.denom(a)));
  }
}

/** SymPy ZZ_I. */
export const ZZ_I: GaussianIntegerRing = new GaussianIntegerRing();
/** SymPy QQ_I. */
export const QQ_I: GaussianRationalField = new GaussianRationalField();
