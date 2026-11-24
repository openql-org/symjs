// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/finitefield.py, polys/domains/modularinteger.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The finite field GF(p) (SymPy FiniteField, alias GF and FF) and its
 * elements (SymPy ModularInteger). An element prints as `3 mod 5` (str) and
 * `SymmetricModularIntegerMod5(3)` (repr); with the symmetric
 * representation (the default) it converts to an integer in (-p/2, p/2].
 */

import { NotImplementedError, NotInvertible } from '../../core/errors';
import { first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Rational } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { asInt, type IntLike } from '../../ntheory/intutil';
import { isprime } from '../../ntheory/primetest';
import { sqrtModPrimePower } from '../../ntheory/residue';
import { NoMatch, type NoMatchResult } from '../../core/truth';
import { CoercionFailed, Domain, groundRational } from '../domains';

const pmod = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;

/** The inverse of a modulo m (SymPy invert). */
function invertMod(a: bigint, m: bigint): bigint {
  let [r0, r1, s0, s1] = [pmod(a, m), m, 1n, 0n];
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
  }
  if (r0 !== 1n) throw new NotInvertible('inverse of ' + String(a) + ' (mod ' + String(m) + ') does not exist');
  return pmod(s0, m);
}

/**
 * An element of GF(p): the residue `val` in [0, p).
 *
 * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger`
 */
export class ModularInteger {
  /**
   * The least nonnegative representative of the residue class.
   *
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.val`
   */
  readonly val: bigint;
  /**
   * Reduces an integer modulo the characteristic of its residue domain.
   *
   * @param val - Integer to reduce modulo the field modulus.
   * @param field - Field of the residue class.
   */
  constructor(
    val: bigint,
    /** The finite residue domain containing this element. */
    readonly field: FiniteField,
  ) {
    this.val = pmod(val, field.mod);
  }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.mod`
   */
  get mod(): bigint {
    return this.field.mod;
  }
  /**
   * The symmetric representation.
   *
   * @returns Whether integer representatives are centered.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.sym`
   */
  get sym(): boolean {
    return this.field.symmetric;
  }
  private of(o: ModularInteger | bigint | number): bigint {
    return o instanceof ModularInteger ? o.val : BigInt(o);
  }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  get isZero(): boolean {
    return this.val === 0n;
  }
  /**
   * The integer value: in (-p/2, p/2] for the symmetric representation.
   *
   * @returns The integer representative.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.to_int`
   */
  toInt(): bigint {
    return this.sym && this.val > this.mod / 2n ? this.val - this.mod : this.val;
  }
  /**
   * Adds the other operand to this value.
   *
   * @param o - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__add__`
   */
  add(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val + this.of(o), this.field);
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param o - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__sub__`
   */
  sub(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val - this.of(o), this.field);
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param o - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__mul__`
   */
  mul(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val * this.of(o), this.field);
  }
  /**
   * Multiplies by the modular inverse of the divisor.
   *
   * @param o - Divisor.
   * @returns The quotient.
   * @throws NotInvertible when the required modular inverse does not exist.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__truediv__`
   */
  div(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val * invertMod(this.of(o), this.mod), this.field);
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__neg__`
   */
  neg(): ModularInteger {
    return new ModularInteger(-this.val, this.field);
  }
  /**
   * This**n (a negative n inverts).
   *
   * @param n - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @throws NotInvertible when the required modular inverse does not exist.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__pow__`
   */
  pow(n: number): ModularInteger {
    let [b, e, r] = [n < 0 ? invertMod(this.val, this.mod) : this.val, BigInt(Math.abs(n)), 1n];
    for (; e > 0n; e >>= 1n) {
      if (e & 1n) r = (r * b) % this.mod;
      b = (b * b) % this.mod;
    }
    return new ModularInteger(r, this.field);
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__eq__`
   */
  equals(o: unknown): boolean {
    if (o instanceof ModularInteger) return o.mod === this.mod && o.val === this.val;
    const r = groundRational(o);
    return r?.[1] === 1n && pmod(r[0], this.mod) === this.val;
  }
  /**
   * Formats the residue together with its modulus.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__str__`
   */
  toString(): string {
    return `${this.val} mod ${this.mod}`;
  }
  /**
   * Formats the residue with the modular integer type and modulus.
   *
   * @returns The constructor-style representation.
   * @see SymPy `sympy.polys.domains.modularinteger.ModularInteger.__repr__`
   */
  repr(): string {
    return `${this.sym ? 'Symmetric' : ''}ModularIntegerMod${this.mod}(${this.val})`;
  }
}

/**
 * The finite field GF(p) for a prime p.
 *
 * @see SymPy `sympy.polys.domains.finitefield.FiniteField`
 * @example
 * ```ts
 * import { FiniteField } from '@symjs/symjs';
 *
 * const K = new FiniteField(5);
 * K.new(3).pow(2).toInt(); // => -1
 * ```
 */
export class FiniteField extends Domain {
  /** The identifier for the underlying coefficient domain. */
  readonly ground = 'ZZ' as const;
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.is_Field`
   */
  readonly isField: boolean;
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.mod`
   */
  readonly mod: bigint;
  /**
   * Defines arithmetic modulo a positive integer with a choice of integer representatives.
   *
   * @param mod - Modulus used for the arithmetic.
   * @param symmetric - Use centered integer representatives.
   * @throws RangeError when the modulus is not positive.
   */
  constructor(
    mod: bigint | number,
    /** The choice of centered rather than nonnegative integer representatives. */
    readonly symmetric = true,
  ) {
    super();
    this.mod = BigInt(mod);
    if (this.mod <= 0n) throw new RangeError(`modulus must be a positive integer, got ${this.mod}`);
    this.isField = isprime(this.mod);
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.__str__`
   */
  toString(): string {
    return `GF(${this.mod})`;
  }
  /**
   * Gives the characteristic of the residue domain.
   *
   * @returns The characteristic of the coefficient domain.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.characteristic`
   */
  override characteristic(): bigint {
    return this.mod;
  }
  /**
   * An integer expression reduced to the symmetric (or [0, p)) range.
   *
   * @param e - Expression to represent in this domain.
   * @returns The canonical expression in this domain.
   */
  canon(e: Expr): Expr {
    return this.toSympy(this.convert(e));
  }
  /**
   * Interprets a symbolic expression in this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The expression converted into the domain.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.from_sympy`
   */
  fromSympy(e: ExprLike): Expr {
    return this.canon(sympify(e));
  }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.get_field`
   */
  getField(): Domain {
    return this;
  }
  /**
   * Converts a residue to its integer expression using the field’s representative convention.
   *
   * @param a - Element on which to operate.
   * @returns The corresponding symbolic expression.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.to_sympy`
   */
  override toSympy(a: unknown): Expr {
    return a instanceof ModularInteger ? Rational.of(a.toInt()) : super.toSympy(a);
  }
  /**
   * Reduces the supplied integer to an element of the residue domain.
   *
   * @param args - Value or coefficients defining the domain element.
   * @returns The newly constructed element.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.new`
   */
  override new(...args: unknown[]): ModularInteger {
    return this.convert(first(args));
  }
  /**
   * Reduces an integer or modular element into this residue domain.
   *
   * @param a - Element on which to operate.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.convert`
   */
  override convert(a: unknown, base?: Domain): ModularInteger {
    if (a instanceof ModularInteger) return new ModularInteger(a.toInt(), this);
    const r = groundRational(base !== undefined && !base.equals(this) ? base.toSympy(a) : a);
    if (r?.[1] === 1n) return new ModularInteger(r[0], this);
    throw new CoercionFailed(`expected an integer, got ${String(a)}`);
  }
  /**
   * Checks whether the input already belongs to the native element type.
   *
   * @param a - Element on which to operate.
   * @returns Whether the value is a native element of the domain.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.of_type`
   */
  override ofType(a: unknown): boolean {
    return a instanceof ModularInteger && a.mod === this.mod;
  }
  /**
   * Tests for the additive identity.
   *
   * @param a - Element on which to operate.
   * @returns Whether the value equals zero.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.is_zero`
   */
  override isZero(a: unknown): boolean {
    return a instanceof ModularInteger ? a.isZero : super.isZero(a);
  }
  /**
   * Tests the sign of an element according to the ordering convention of this domain.
   *
   * @param a - Element on which to operate.
   * @returns Whether the value is positive in this domain.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.is_positive`
   */
  override isPositive(a: unknown): boolean {
    return !this.isZero(this.convert(a));
  }
  /**
   * Tests the sign of an element according to the ordering convention of this domain.
   *
   * @param _a - Element on which to operate.
   * @returns Whether the value is negative in this domain.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.is_negative`
   */
  override isNegative(_a: unknown): boolean {
    return false;
  }
  /**
   * Gcd over a field: 1 unless both are zero.
   *
   * @param a - Element on which to operate.
   * @param b - Second operand.
   * @returns A greatest common divisor.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.gcd`
   */
  override gcd(a: unknown, b: unknown): ModularInteger {
    return this.convert(this.convert(a).isZero && this.convert(b).isZero ? 0 : 1);
  }
  /**
   * Computes a least common multiple in this domain.
   *
   * @param a - Element on which to operate.
   * @param b - Second operand.
   * @returns A least common multiple.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.lcm`
   */
  override lcm(a: unknown, b: unknown): ModularInteger {
    return this.convert(a).mul(this.convert(b));
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.div`
   */
  override div(a: unknown, b: unknown): [ModularInteger, ModularInteger] {
    return [this.exquo(a, b), this.convert(0)];
  }
  /**
   * Divides in the coefficient domain, requiring exact divisibility.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The exact quotient.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.exquo`
   */
  override exquo(a: unknown, b: unknown): ModularInteger {
    return this.convert(a).div(this.convert(b));
  }
  /**
   * Division in GF(p) uses the modular inverse, including expression-backed coefficients.
   *
   * @param a - Dividend in the coefficient domain.
   * @param b - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.quo`
   */
  override quo(a: Expr, b: Expr): Expr {
    return this.toSympy(this.exquo(a, b));
  }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @param _a - Dividend in the coefficient domain.
   * @param _b - Divisor.
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.rem`
   */
  override rem(_a: unknown, _b: unknown): ModularInteger {
    return this.convert(0);
  }
  /**
   * Finds a modular square root in the lower half of the residue system.
   *
   * @param aIn - Element whose square root to find.
   * @returns The root in the lower half of the residue range, or `NoMatch` if no root exists.
   * @throws NotImplementedError when the modulus is composite.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.exsqrt`
   */
  override exsqrt(aIn: unknown): ModularInteger | NoMatchResult {
    const a = this.convert(aIn);
    if (this.mod === 2n || a.isZero) return a;
    if (!this.isField) throw new NotImplementedError(`square roots modulo the composite ${this.mod}`);
    const root = sqrtModPrimePower(a.val, this.mod, 1n)?.find((r) => r <= this.mod / 2n);
    return root === undefined ? NoMatch : this.convert(root);
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.finitefield.FiniteField.__eq__`
   */
  override equals(o: Domain): boolean {
    return o instanceof FiniteField && o.mod === this.mod && o.symmetric === this.symmetric;
  }
}

/**
 * Constructs the domain of residues modulo a positive integer. A prime modulus gives a field.
 *
 * @param mod - Positive modulus, prime for a field.
 * @param symmetric - Use centered integer representatives.
 * @returns The residue domain for the given modulus.
 * @throws RangeError when the modulus is not a positive integer.
 * @see SymPy `sympy.polys.domains.GF`
 * @example
 * ```ts
 * import { GF } from '@symjs/symjs';
 *
 * const K = GF(5);
 * K.new(3).pow(2).toInt(); // => -1
 * ```
 */
export function GF(mod: IntLike, symmetric = true): FiniteField {
  return new FiniteField(asInt(mod, 'modulus'), symmetric);
}

export { GF as FF };
