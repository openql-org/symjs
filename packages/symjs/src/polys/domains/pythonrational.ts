// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (external/pythonmpq.py, polys/domains/pythonrational.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The rational number type of the QQ domain (SymPy PythonMPQ, the
 * ground type of QQ without gmpy2): a reduced fraction of bigints that
 * prints as `1/2` (str) and `MPQ(1,2)` (repr).
 */

import { gcd as igcd } from '../../core/numbers';

/**
 * A rational number as a reduced fraction of bigints with a positive denominator.
 *
 * @see SymPy `sympy.external.pythonmpq.PythonMPQ`
 */
export class PythonMPQ {
  /**
   * The numerator of the reduced fraction.
   *
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.numerator`
   */
  readonly numerator: bigint;
  /**
   * The positive denominator of the reduced fraction.
   *
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.denominator`
   */
  readonly denominator: bigint;
  /**
   * Reduces the numerator and denominator to lowest terms and normalizes the denominator sign.
   *
   * @param numerator - Numerator before reduction.
   * @param denominator - Nonzero denominator before reduction.
   * @throws RangeError when the denominator is zero.
   */
  constructor(numerator: bigint | number | PythonMPQ, denominator: bigint | number = 1n) {
    const n = numerator instanceof PythonMPQ ? numerator.numerator : BigInt(numerator);
    const d0 = numerator instanceof PythonMPQ ? numerator.denominator * BigInt(denominator) : BigInt(denominator);
    if (d0 === 0n) throw new RangeError('Zero divisor');
    const g = igcd(n, d0);
    const s = d0 < 0n ? -1n : 1n;
    this.numerator = (s * n) / g;
    this.denominator = (s * d0) / g;
  }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  get isZero(): boolean {
    return this.numerator === 0n;
  }
  /**
   * The sign: -1, 0 or 1.
   *
   * @returns The sign of the rational number.
   */
  get sign(): number {
    return this.numerator === 0n ? 0 : this.numerator < 0n ? -1 : 1;
  }
  private static of(x: PythonMPQ | bigint | number): PythonMPQ {
    return x instanceof PythonMPQ ? x : new PythonMPQ(x);
  }
  /**
   * Adds the other operand to this value.
   *
   * @param o - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__add__`
   */
  add(o: PythonMPQ | bigint | number): PythonMPQ {
    const b = PythonMPQ.of(o);
    return new PythonMPQ(this.numerator * b.denominator + b.numerator * this.denominator, this.denominator * b.denominator);
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param o - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__sub__`
   */
  sub(o: PythonMPQ | bigint | number): PythonMPQ {
    return this.add(PythonMPQ.of(o).neg());
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param o - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__mul__`
   */
  mul(o: PythonMPQ | bigint | number): PythonMPQ {
    const b = PythonMPQ.of(o);
    return new PythonMPQ(this.numerator * b.numerator, this.denominator * b.denominator);
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param o - Divisor.
   * @returns The quotient.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__truediv__`
   */
  div(o: PythonMPQ | bigint | number): PythonMPQ {
    const b = PythonMPQ.of(o);
    return new PythonMPQ(this.numerator * b.denominator, this.denominator * b.numerator);
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__neg__`
   */
  neg(): PythonMPQ {
    return new PythonMPQ(-this.numerator, this.denominator);
  }
  /**
   * Computes the magnitude of the value.
   *
   * @returns The absolute value.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__abs__`
   */
  abs(): PythonMPQ {
    return this.numerator < 0n ? this.neg() : this;
  }
  /**
   * This**n for an integer n (a negative n inverts).
   *
   * @param n - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__pow__`
   */
  pow(n: number): PythonMPQ {
    const k = BigInt(Math.abs(n));
    const r = new PythonMPQ(this.numerator ** k, this.denominator ** k);
    return n < 0 ? new PythonMPQ(r.denominator, r.numerator) : r;
  }
  /**
   * Compares two rationals by cross multiplication.
   *
   * @param o - Value to compare against.
   * @returns The sign of the comparison.
   */
  compare(o: PythonMPQ | bigint | number): number {
    const b = PythonMPQ.of(o);
    const d = this.numerator * b.denominator - b.numerator * this.denominator;
    return d === 0n ? 0 : d < 0n ? -1 : 1;
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__eq__`
   */
  equals(o: unknown): boolean {
    if (typeof o === 'bigint') return this.compare(o) === 0;
    if (typeof o === 'number') return Number.isInteger(o) && this.compare(o) === 0;
    return o instanceof PythonMPQ && this.compare(o) === 0;
  }
  /**
   * Prints a reduced fraction, omitting the denominator when it is one.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__str__`
   */
  toString(): string {
    return this.denominator === 1n ? `${this.numerator}` : `${this.numerator}/${this.denominator}`;
  }
  /**
   * Displays the reduced numerator and denominator as arguments to `MPQ`.
   *
   * @returns The constructor-style representation.
   * @see SymPy `sympy.external.pythonmpq.PythonMPQ.__repr__`
   */
  repr(): string {
    return `MPQ(${this.numerator},${this.denominator})`;
  }
}
