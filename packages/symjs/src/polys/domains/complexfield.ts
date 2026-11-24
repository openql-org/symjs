// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/complexfield.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The complex floating-point field CC (SymPy ComplexField). Elements
 * are expressions a + b*I with floats a and b at the field's precision.
 */

import { DomainError } from '../../core/errors';
import type { ExprLike } from '../../core/nodes';
import { type Expr, Float, S } from '../../core/nodes';
import { add, mul, pow, sympify } from '../../core/ops';
import { asRealImag } from '../../core/methods';
import { evalf } from '../../numeric/evalf';
import { str } from '../../printing/str';
import { CoercionFailed, Domain, domainHooks, type UnificationKind } from '../domains';
import { MPContext, type ComplexElement } from './mpelements';
import { GaussianElement, QQ_I } from './gaussiandomains';

/**
 * The field of complex floats; CC has 53 bits.
 *
 * @see SymPy `sympy.polys.domains.complexfield.ComplexField`
 */
export class ComplexField extends Domain {
  /** The identifier for the underlying coefficient domain. */
  readonly ground = 'RR' as const;
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_Field`
   */
  readonly isField = true;
  /**
   * The precision in bits.
   *
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.precision`
   */
  readonly precision: number;
  /**
   * The arithmetic context controlling precision.
   *
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField._context`
   */
  readonly context: MPContext;
  /**
   * Constructs a complex field element from two real components.
   *
   * @param real - Real component.
   * @param imag - Imaginary component.
   * @returns The complex element with these components.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.dtype`
   */
  dtype(real: unknown = 0, imag: unknown = 0): ComplexElement { return this.context.mpc(real, imag); }
  /**
   * Creates a complex floating-point field with the specified bit precision.
   *
   * @param prec - Precision in bits.
   */
  constructor(prec = 53) {
    super();
    this.context = new MPContext(prec, { parent: this });
    this.precision = this.context.prec;
  }
  /**
   * The precision in decimal digits.
   *
   * @returns The working precision in decimal digits.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.dps`
   */
  get dps(): number {
    return Math.max(1, Math.round(this.precision / 3.3219280948873626) - 1);
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.__str__`
   */
  toString(): string {
    return this.precision === 53 ? 'CC' : `CC_${this.precision}`;
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.__eq__`
   */
  override equals(o: Domain): boolean {
    return o instanceof ComplexField && o.precision === this.precision;
  }
  /**
   * Expresses a numeric value as a complex number with floating-point components.
   *
   * @param e - Expression to represent in this domain.
   * @returns The canonical expression in this domain.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   */
  canon(e: Expr): Expr {
    const [re, im] = asRealImag(evalf(e, this.dps));
    if (!(re instanceof Float || re === S.Zero) || !(im instanceof Float || im === S.Zero)) throw new CoercionFailed(`expected complex number, got ${str(e)}`);
    const f = (x: Expr): Expr => (x instanceof Float ? new Float(x.mpf, this.precision) : new Float(0, this.precision));
    return add(f(re), mul(S.I, f(im)));
  }
  /**
   * Interprets a symbolic expression in this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The expression converted into the domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.from_sympy`
   */
  fromSympy(e: ExprLike): Expr {
    return this.canon(sympify(e));
  }
  /**
   * Coerces the input into the target domain.
   *
   * @param value - Value to represent.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.convert`
   */
  override convert(value: unknown, base?: Domain): unknown {
    if (value instanceof GaussianElement && base === undefined) return this.fromSympy(QQ_I.toSympy(value));
    return super.convert(value, base);
  }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.get_field`
   */
  getField(): Domain {
    return this;
  }
  /**
   * Finds the ring associated with this domain.
   *
   * @returns The associated ring.
   * @throws DomainError when the field has no associated ring.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.get_ring`
   */
  override getRing(): Domain {
    throw new DomainError(`there is no ring associated with ${this.toString()}`);
  }
  /**
   * Finds the exact domain associated with this coefficient domain.
   *
   * @returns The associated exact domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.get_exact`
   */
  override getExact(): Domain {
    return QQ_I;
  }
  /**
   * Indicates whether operations in this domain use exact arithmetic.
   *
   * @returns Whether arithmetic in the domain is exact.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_Exact`
   */
  override get isExact(): boolean {
    return false;
  }
  protected override get unificationKind(): UnificationKind {
    return 'CC';
  }
  protected override get floatPrecision(): number {
    return this.precision;
  }
  /**
   * Checks the characteristic of the coefficient ring.
   *
   * @returns Whether the characteristic is zero.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.has_CharacteristicZero`
   */
  override get hasCharacteristicZero(): boolean {
    return true;
  }
  /**
   * Tests the sign of an element according to the ordering convention of this domain.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the value is negative in this domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_negative`
   */
  override isNegative(_a: unknown): boolean {
    return false;
  }
  /**
   * Tests the sign of an element according to the ordering convention of this domain.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the value is positive in this domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_positive`
   */
  override isPositive(_a: unknown): boolean {
    return false;
  }
  /**
   * Tests the sign of an element according to the ordering convention of this domain.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the value is nonnegative in this domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_nonnegative`
   */
  override isNonnegative(_a: unknown): boolean {
    return false;
  }
  /**
   * Tests the sign of an element according to the ordering convention of this domain.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the value is nonpositive in this domain.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_nonpositive`
   */
  override isNonpositive(_a: unknown): boolean {
    return false;
  }
  /**
   * The principal square root; every complex number is a square.
   *
   * @param a - Element whose square root to find.
   * @returns The exact square root when one exists.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.exsqrt`
   */
  override exsqrt(a: unknown): Expr {
    return this.canon(pow(this.toSympy(this.convert(a)), S.Half));
  }
  /**
   * Tests for the existence of a complex square root.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the element is a square.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.is_square`
   */
  override isSquare(_a: unknown): boolean {
    return true;
  }
  /**
   * Computes a greatest common divisor in this domain.
   *
   * @param _a - Element on which to operate.
   * @param _b - Second operand.
   * @returns A greatest common divisor.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.gcd`
   */
  override gcd(_a: unknown, _b: unknown): Expr {
    return this.canon(S.One);
  }
  /**
   * Computes a least common multiple in this domain.
   *
   * @param a - Element on which to operate.
   * @param b - Second operand.
   * @returns A least common multiple.
   * @see SymPy `sympy.polys.domains.complexfield.ComplexField.lcm`
   */
  override lcm(a: unknown, b: unknown): Expr {
    return this.canon(mul(this.toSympy(a), this.toSympy(b)));
  }
}

/**
 * The complex floating-point field with 53 bits of precision.
 *
 * @see SymPy `sympy.polys.domains.CC`
 */
export const CC: ComplexField = new ComplexField();

domainHooks.complexField = (prec) => new ComplexField(prec);
