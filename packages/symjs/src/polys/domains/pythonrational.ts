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

/** A rational number as a reduced fraction of bigints with a positive denominator (SymPy PythonMPQ). */
export class PythonMPQ {
  readonly numerator: bigint;
  readonly denominator: bigint;
  /** The fraction numerator/denominator, reduced (SymPy PythonMPQ(p, q)); throws on a zero denominator. */
  constructor(numerator: bigint | number | PythonMPQ, denominator: bigint | number = 1n) {
    const n = numerator instanceof PythonMPQ ? numerator.numerator : BigInt(numerator);
    const d0 = numerator instanceof PythonMPQ ? numerator.denominator * BigInt(denominator) : BigInt(denominator);
    if (d0 === 0n) throw new RangeError('Zero divisor');
    const g = igcd(n, d0);
    const s = d0 < 0n ? -1n : 1n;
    this.numerator = (s * n) / g;
    this.denominator = (s * d0) / g;
  }
  /** Is the number zero (SymPy bool(q) is False)? */
  get isZero(): boolean {
    return this.numerator === 0n;
  }
  /** The sign: -1, 0 or 1. */
  get sign(): number {
    return this.numerator === 0n ? 0 : this.numerator < 0n ? -1 : 1;
  }
  private static of(x: PythonMPQ | bigint | number): PythonMPQ {
    return x instanceof PythonMPQ ? x : new PythonMPQ(x);
  }
  add(o: PythonMPQ | bigint | number): PythonMPQ {
    const b = PythonMPQ.of(o);
    return new PythonMPQ(this.numerator * b.denominator + b.numerator * this.denominator, this.denominator * b.denominator);
  }
  sub(o: PythonMPQ | bigint | number): PythonMPQ {
    return this.add(PythonMPQ.of(o).neg());
  }
  mul(o: PythonMPQ | bigint | number): PythonMPQ {
    const b = PythonMPQ.of(o);
    return new PythonMPQ(this.numerator * b.numerator, this.denominator * b.denominator);
  }
  /** this/o; throws RangeError for o = 0 (SymPy ZeroDivisionError). */
  div(o: PythonMPQ | bigint | number): PythonMPQ {
    const b = PythonMPQ.of(o);
    return new PythonMPQ(this.numerator * b.denominator, this.denominator * b.numerator);
  }
  neg(): PythonMPQ {
    return new PythonMPQ(-this.numerator, this.denominator);
  }
  abs(): PythonMPQ {
    return this.numerator < 0n ? this.neg() : this;
  }
  /** this**n for an integer n (a negative n inverts). */
  pow(n: number): PythonMPQ {
    const k = BigInt(Math.abs(n));
    const r = new PythonMPQ(this.numerator ** k, this.denominator ** k);
    return n < 0 ? new PythonMPQ(r.denominator, r.numerator) : r;
  }
  /** Compare with another rational: negative, zero or positive. */
  compare(o: PythonMPQ | bigint | number): number {
    const b = PythonMPQ.of(o);
    const d = this.numerator * b.denominator - b.numerator * this.denominator;
    return d === 0n ? 0 : d < 0n ? -1 : 1;
  }
  equals(o: unknown): boolean {
    if (typeof o === 'bigint') return this.compare(o) === 0;
    if (typeof o === 'number') return Number.isInteger(o) && this.compare(o) === 0;
    return o instanceof PythonMPQ && this.compare(o) === 0;
  }
  /** SymPy str(q): `p/q`, or `p` for an integer. */
  toString(): string {
    return this.denominator === 1n ? `${this.numerator}` : `${this.numerator}/${this.denominator}`;
  }
  /** SymPy repr(q): `MPQ(p,q)`. */
  repr(): string {
    return `MPQ(${this.numerator},${this.denominator})`;
  }
}
