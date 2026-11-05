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

import { NotInvertible } from '../../core/errors';
import { first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Rational } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { asInt, type IntLike } from '../../ntheory/intutil';
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

/** An element of GF(p) (SymPy ModularInteger): the residue `val` in [0, p). */
export class ModularInteger {
  readonly val: bigint;
  constructor(
    val: bigint,
    readonly field: FiniteField,
  ) {
    this.val = pmod(val, field.mod);
  }
  get mod(): bigint {
    return this.field.mod;
  }
  /** The symmetric representation (SymPy sym). */
  get sym(): boolean {
    return this.field.symmetric;
  }
  private of(o: ModularInteger | bigint | number): bigint {
    return o instanceof ModularInteger ? o.val : BigInt(o);
  }
  get isZero(): boolean {
    return this.val === 0n;
  }
  /** The integer value: in (-p/2, p/2] for the symmetric representation (SymPy int(a)). */
  toInt(): bigint {
    return this.sym && this.val > this.mod / 2n ? this.val - this.mod : this.val;
  }
  add(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val + this.of(o), this.field);
  }
  sub(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val - this.of(o), this.field);
  }
  mul(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val * this.of(o), this.field);
  }
  /** this/o; throws NotInvertible for o = 0. */
  div(o: ModularInteger | bigint | number): ModularInteger {
    return new ModularInteger(this.val * invertMod(this.of(o), this.mod), this.field);
  }
  neg(): ModularInteger {
    return new ModularInteger(-this.val, this.field);
  }
  /** this**n (a negative n inverts). */
  pow(n: number): ModularInteger {
    let [b, e, r] = [n < 0 ? invertMod(this.val, this.mod) : this.val, BigInt(Math.abs(n)), 1n];
    for (; e > 0n; e >>= 1n) {
      if (e & 1n) r = (r * b) % this.mod;
      b = (b * b) % this.mod;
    }
    return new ModularInteger(r, this.field);
  }
  equals(o: unknown): boolean {
    if (o instanceof ModularInteger) return o.mod === this.mod && o.val === this.val;
    const r = groundRational(o);
    return r?.[1] === 1n && pmod(r[0], this.mod) === this.val;
  }
  /** SymPy str(a): `3 mod 5`. */
  toString(): string {
    return `${this.val} mod ${this.mod}`;
  }
  /** SymPy repr(a): `SymmetricModularIntegerMod5(3)`. */
  repr(): string {
    return `${this.sym ? 'Symmetric' : ''}ModularIntegerMod${this.mod}(${this.val})`;
  }
}

/** The finite field GF(p) for a prime p (SymPy FiniteField). */
export class FiniteField extends Domain {
  readonly ground = 'ZZ' as const;
  readonly isField = true;
  readonly mod: bigint;
  constructor(
    mod: bigint | number,
    readonly symmetric = true,
  ) {
    super();
    this.mod = BigInt(mod);
    if (this.mod <= 0n) throw new RangeError(`modulus must be a positive integer, got ${this.mod}`);
  }
  toString(): string {
    return `GF(${this.mod})`;
  }
  /** The characteristic p (SymPy characteristic). */
  characteristic(): bigint {
    return this.mod;
  }
  /** An integer expression reduced to the symmetric (or [0, p)) range. */
  canon(e: Expr): Expr {
    return this.toSympy(this.convert(e));
  }
  fromSympy(e: ExprLike): Expr {
    return this.canon(sympify(e));
  }
  getField(): Domain {
    return this;
  }
  override toSympy(a: unknown): Expr {
    return a instanceof ModularInteger ? Rational.of(a.toInt()) : super.toSympy(a);
  }
  override new(...args: unknown[]): ModularInteger {
    return this.convert(first(args));
  }
  /** An element from an integer (or an element of another GF(p)); throws CoercionFailed. */
  override convert(a: unknown, base?: Domain): ModularInteger {
    if (a instanceof ModularInteger) return new ModularInteger(a.toInt(), this);
    const r = groundRational(base !== undefined && !base.equals(this) ? base.toSympy(a) : a);
    if (r?.[1] === 1n) return new ModularInteger(r[0], this);
    throw new CoercionFailed(`expected an integer, got ${String(a)}`);
  }
  override ofType(a: unknown): boolean {
    return a instanceof ModularInteger && a.mod === this.mod;
  }
  override isZero(a: unknown): boolean {
    return a instanceof ModularInteger ? a.isZero : super.isZero(a);
  }
  /** SymPy GF(p).is_positive: a nonzero element. */
  override isPositive(a: unknown): boolean {
    return !this.isZero(this.convert(a));
  }
  override isNegative(_a: unknown): boolean {
    return false;
  }
  /** gcd over a field: 1 unless both are zero. */
  override gcd(a: unknown, b: unknown): ModularInteger {
    return this.convert(this.convert(a).isZero && this.convert(b).isZero ? 0 : 1);
  }
  override lcm(a: unknown, b: unknown): ModularInteger {
    return this.convert(a).mul(this.convert(b));
  }
  override div(a: unknown, b: unknown): [ModularInteger, ModularInteger] {
    return [this.exquo(a, b), this.convert(0)];
  }
  override exquo(a: unknown, b: unknown): ModularInteger {
    return this.convert(a).div(this.convert(b));
  }
  override rem(_a: unknown, _b: unknown): ModularInteger {
    return this.convert(0);
  }
  override equals(o: Domain): boolean {
    return o instanceof FiniteField && o.mod === this.mod && o.symmetric === this.symmetric;
  }
}

/** SymPy FiniteField(p, symmetric=True), GF(p), FF(p): the finite field of p elements. */
export function GF(mod: IntLike, symmetric = true): FiniteField {
  return new FiniteField(asInt(mod, 'modulus'), symmetric);
}

export { GF as FF };
