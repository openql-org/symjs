// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/mpelements.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/** Arbitrary-precision domain elements with explicitly owned numeric contexts. */
import { Float, Rational, S, type Expr } from '../../core/nodes';
import { add, mul } from '../../core/ops';
import { NoMatch, type NoMatchResult } from '../../core/truth';
import * as F from '../../numeric/mpf';
import * as C from '../../numeric/mpfun';
import type { Domain } from '../domains';

/** Finite binary values, or IEEE nonfinite values. Finite numbers use Mpf. */
type RealValue = F.Mpf | number;
class RawReal {
  constructor(readonly data: RealValue) {}
}
function complexParts(value: string): [string, string] {
  const s = value.trim().replace(/^\(|\)$/g, '').replace(/\s+/g, '').slice(0, -1);
  const coefficient = (v: string): string => v === '' || v === '+' || v === '-' ? v + '1' : v;
  for (let i = s.length - 1; i > 0; i--) {
    if ((s[i] === '+' || s[i] === '-') && s[i - 1]?.toLowerCase() !== 'e') return [s.slice(0, i), coefficient(s.slice(i))];
  }
  return ['0', coefficient(s)];
}

function realValue(value: unknown, prec: number): RealValue {
  if (value instanceof RawReal) return value.data;
  if (value instanceof RealElement) return rounded(value.data, prec);
  if (value instanceof Float) return F.round(value.mpf, prec);
  if (value instanceof Rational) return F.fromRational(value.p, value.q, prec);
  if (typeof value === 'bigint') return F.fromInt(value, prec);
  if (typeof value === 'boolean') return F.fromInt(BigInt(value));
  if (typeof value === 'number') return Number.isFinite(value) ? F.round(F.fromNumber(value), prec) : value;
  if (typeof value === 'string') {
    const s = value.trim().toLowerCase();
    if (/^[+-]?(inf(inity)?|nan)$/.test(s)) return s.includes('nan') ? NaN : s.startsWith('-') ? -Infinity : Infinity;
    return F.fromStr(s, prec);
  }
  if (typeof value === 'object' && value !== null && 'man' in value && 'exp' in value && typeof value.man === 'bigint' && typeof value.exp === 'bigint') return F.normalize(value.man, value.exp, prec);
  throw new TypeError(`cannot create a real element from ${String(value)}`);
}
function operand(value: unknown, prec: number): RealValue { return value instanceof RealElement ? value.data : realValue(value, prec); }
function rounded(v: RealValue, prec: number): RealValue { return typeof v === 'number' ? v : F.round(v, prec); }
function numberValue(v: RealValue): number { return typeof v === 'number' ? v : F.toNumber(v); }
function negative(v: RealValue): RealValue { return typeof v === 'number' ? -v : F.neg(v); }
function zero(v: RealValue): boolean { return typeof v !== 'number' && F.isZero(v); }
function compare(a: RealValue, b: RealValue): number {
  if (typeof a !== 'number' && typeof b !== 'number') return F.cmp(a, b);
  if (Number.isNaN(a) || Number.isNaN(b)) return NaN;
  if (a === b) return 0;
  return a === Infinity || b === -Infinity ? 1 : -1;
}
function arithmetic(a: RealValue, b: RealValue, op: 'add' | 'mul' | 'div', prec: number): RealValue {
  if (op === 'div' && zero(b)) throw new RangeError('division by zero');
  if (typeof a !== 'number' && typeof b !== 'number') return op === 'add' ? F.add(a, b, prec) : op === 'mul' ? F.mul(a, b, prec) : F.div(a, b, prec);
  // Only nonfinite arithmetic uses doubles: finite magnitudes never overflow here.
  const x = typeof a === 'number' ? a : F.sign(a);
  const y = typeof b === 'number' ? b : F.sign(b);
  const result = op === 'add' ? x + y : op === 'mul' ? x * y : x / y;
  return Number.isFinite(result) ? F.fromNumber(result) : result;
}

/**
 * An element of a real domain.
 *
 * @see SymPy `sympy.polys.domains.mpelements.RealElement`
 */
export class RealElement {
  /** The binary floating-point value or nonfinite special value. */
  readonly data: RealValue;
  /**
   * Represents a real number in the supplied precision context.
   *
   * @param value - Value to represent.
   * @param context - Arithmetic context governing precision.
   */
  constructor(value: unknown = 0,
    /**
     * The arithmetic context controlling precision.
     *
     * @see SymPy `sympy.polys.domains.mpelements.RealElement.context`
     */
    readonly context: MPContext = new MPContext()) {
    this.data = realValue(value, context.prec);
  }
  /**
   * Identifies the domain associated with this element’s arithmetic context.
   *
   * @returns The owning coefficient domain, or `NoMatch` for a context without a parent.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.parent`
   */
  parent(): Domain | NoMatchResult { return this.context.parent; }
  /**
   * Selects the real part, which is the element itself.
   *
   * @returns The real component.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.real`
   */
  get real(): RealElement { return this; }
  /**
   * Selects the imaginary part, which is zero for a real element.
   *
   * @returns The imaginary component.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.imag`
   */
  get imag(): RealElement { return this.context.zero; }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  get isZero(): boolean { return zero(this.data); }
  /**
   * Exposes the real value at JavaScript number precision.
   *
   * @returns The JavaScript numeric value.
   */
  get value(): number { return numberValue(this.data); }
  /**
   * Rounds the stored real value to a JavaScript number.
   *
   * @returns The JavaScript numeric value.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__float__`
   */
  toNumber(): number { return this.value; }
  /**
   * Truncates the real number toward zero.
   *
   * @returns The integer representative.
   * @throws RangeError when the value is not finite.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__int__`
   */
  toInt(): bigint {
    if (typeof this.data === 'number') throw new RangeError('nonfinite integer');
    const f = F.floor(F.abs(this.data));
    return F.sign(this.data) < 0 ? -f : f;
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__str__`
   */
  toString(): string { return typeof this.data === 'number' ? this.data === Infinity ? '+inf' : String(this.data).toLowerCase().replace('infinity', 'inf') : F.toStr(this.data, this.context.dps); }
  /**
   * Formats a constructor-style representation of the value.
   *
   * @returns The constructor-style representation.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__repr__`
   */
  repr(): string {
    if (this.context.pretty) return this.toString();
    const s = typeof this.data === 'number' ? this.toString() : F.toStr(this.data, (this.context.dps === 15 ? 17 : this.context.dps + 3));
    return `mpf('${s}')`;
  }
  /**
   * Expresses the value using symbolic expression nodes.
   *
   * @returns The corresponding symbolic expression.
   */
  toSympy(): Expr {
    if (typeof this.data !== 'number') return new Float(this.data, this.context.prec);
    return this.data === Infinity ? S.Infinity : this.data === -Infinity ? S.NegativeInfinity : S.NaN;
  }
  /**
   * Applies unary plus to the value.
   *
   * @returns The value with unary plus applied.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__pos__`
   */
  pos(): RealElement { return this.context.mpf(this); }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__neg__`
   */
  neg(): RealElement { return this.context.mpf(negative(this.data)); }
  /**
   * Computes the magnitude of the value.
   *
   * @returns The absolute value.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__abs__`
   */
  abs(): RealElement { return this.context.mpf(typeof this.data === 'number' ? Math.abs(this.data) : F.abs(this.data)); }
  /**
   * Applies complex conjugation.
   *
   * @returns The conjugate.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.conjugate`
   */
  conjugate(): RealElement { return this; }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__eq__`
   */
  equals(other: unknown): boolean {
    if (other instanceof ComplexElement) return other.equals(this);
    return compare(this.data, operand(other, this.context.prec)) === 0;
  }
  /**
   * Compares the real numbers in their usual numerical order.
   *
   * @param other - Value to compare against.
   * @returns Whether this value is smaller.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__lt__`
   */
  lt(other: unknown): boolean { return compare(this.data, operand(other, this.context.prec)) < 0; }
  /**
   * Compares the real numbers in their usual numerical order.
   *
   * @param other - Value to compare against.
   * @returns Whether this value is smaller or equal.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__le__`
   */
  le(other: unknown): boolean { return compare(this.data, operand(other, this.context.prec)) <= 0; }
  /**
   * Compares the real numbers in their usual numerical order.
   *
   * @param other - Value to compare against.
   * @returns Whether this value is greater.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__gt__`
   */
  gt(other: unknown): boolean { return compare(this.data, operand(other, this.context.prec)) > 0; }
  /**
   * Compares the real numbers in their usual numerical order.
   *
   * @param other - Value to compare against.
   * @returns Whether this value is greater or equal.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__ge__`
   */
  ge(other: unknown): boolean { return compare(this.data, operand(other, this.context.prec)) >= 0; }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__add__`
   */
  add(other: unknown): RealElement | ComplexElement {
    if (other instanceof ComplexElement) return this.context.mpc(this).add(other);
    return this.context.mpf(arithmetic(this.data, operand(other, this.context.prec), 'add', this.context.prec));
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__sub__`
   */
  sub(other: unknown): RealElement | ComplexElement { return this.add(this.context.convert(other).neg()); }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param other - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__mul__`
   */
  mul(other: unknown): RealElement | ComplexElement {
    if (other instanceof ComplexElement) return this.context.mpc(other).mul(this);
    return this.context.mpf(arithmetic(this.data, operand(other, this.context.prec), 'mul', this.context.prec));
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param other - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__div__`
   */
  div(other: unknown): RealElement | ComplexElement {
    if (other instanceof ComplexElement) return this.context.mpc(this).div(other);
    return this.context.mpf(arithmetic(this.data, operand(other, this.context.prec), 'div', this.context.prec));
  }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @param other - Divisor.
   * @returns The remainder after division.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__mod__`
   */
  mod(other: unknown): RealElement {
    const b = operand(other, this.context.prec);
    if (typeof this.data === 'number' || typeof b === 'number') return this.context.nan;
    if (zero(b)) throw new RangeError('modulo by zero');
    const [ap, aq] = F.toRational(this.data), [bp, bq] = F.toRational(b);
    let n = ap * bq, d = aq * bp;
    if (d < 0n) { n = -n; d = -d; }
    const q = n / d - (n < 0n && n % d !== 0n ? 1n : 0n);
    return this.context.mpf(F.sub(this.data, F.mulInt(b, q), this.context.prec));
  }
  /**
   * Raises the value to the specified power.
   *
   * @param other - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @throws RangeError when the result is nonreal.
   * @see SymPy `sympy.polys.domains.mpelements.RealElement.__pow__`
   */
  pow(other: unknown): RealElement | ComplexElement {
    const b = this.context.convert(other);
    if (b instanceof ComplexElement) return this.context.mpc(this).pow(b);
    if (typeof this.data === 'number' || typeof b.data === 'number') return this.context.mpf(this.value ** b.value);
    if (b.data.exp >= 0n) return this.context.mpf(F.powInt(this.data, F.floor(b.data), this.context.prec));
    if (F.sign(this.data) < 0) {
      if (this.context.trapComplex) throw new RangeError('complex result');
      return this.context.mpc(this).pow(b);
    }
    // Half-integer powers use square roots so the result has libmp's rounding.
    if (b.data.exp === -1n) {
      if (b.data.man === 1n) return this.context.mpf(F.sqrt(this.data, this.context.prec));
      return this.context.mpf(F.powInt(F.sqrt(this.data, this.context.prec + 10), b.data.man, this.context.prec));
    }
    if (this.isZero && b.gt(0)) return this.context.zero;
    return this.context.mpf(C.powReal(this.data, b.data, this.context.prec));
  }
}

/**
 * An element of a complex domain.
 *
 * @see SymPy `sympy.polys.domains.mpelements.ComplexElement`
 */
export class ComplexElement {
  /**
   * The real component.
   *
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.real`
   */
  readonly real: RealElement;
  /**
   * The imaginary component.
   *
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.imag`
   */
  readonly imag: RealElement;
  /**
   * Represents the real and imaginary components in one precision context.
   *
   * @param real - Real component.
   * @param imag - Imaginary component.
   * @param context - Arithmetic context governing precision.
   */
  constructor(real: unknown = 0, imag: unknown = 0,
    /**
     * The arithmetic context controlling precision.
     *
     * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.context`
     */
    readonly context: MPContext = new MPContext()) {
    if (typeof real === 'string' && /[ij]\)?$/i.test(real.trim())) {
      const [re, im] = complexParts(real);
      this.real = context.mpf(re); this.imag = context.mpf(im);
    } else if (real instanceof ComplexElement) {
      this.real = context.mpf(real.real); this.imag = context.mpf(real.imag);
    } else { this.real = context.mpf(real); this.imag = context.mpf(imag); }
  }
  /**
   * Identifies the domain associated with this element’s arithmetic context.
   *
   * @returns The owning coefficient domain, or `NoMatch` for a context without a parent.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.parent`
   */
  parent(): Domain | NoMatchResult { return this.context.parent; }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  get isZero(): boolean { return this.real.isZero && this.imag.isZero; }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__str__`
   */
  toString(): string { return `(${this.real.toString()} ${this.imag.lt(0) ? '-' : '+'} ${this.imag.abs().toString()}j)`; }
  /**
   * Formats a constructor-style representation of the value.
   *
   * @returns The constructor-style representation.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__repr__`
   */
  repr(): string { if (this.context.pretty) return this.toString(); return `mpc(real=${this.real.repr().slice(4, -1)}, imag=${this.imag.repr().slice(4, -1)})`; }
  /**
   * Expresses the value using symbolic expression nodes.
   *
   * @returns The corresponding symbolic expression.
   */
  toSympy(): Expr { return add(this.real.toSympy(), mul(S.I, this.imag.toSympy())); }
  /**
   * Applies unary plus to the value.
   *
   * @returns The value with unary plus applied.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__pos__`
   */
  pos(): ComplexElement { return this.context.mpc(this); }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__neg__`
   */
  neg(): ComplexElement { return this.context.mpc(this.real.neg(), this.imag.neg()); }
  /**
   * Applies complex conjugation.
   *
   * @returns The conjugate.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.conjugate`
   */
  conjugate(): ComplexElement { return this.context.mpc(this.real, this.imag.neg()); }
  /**
   * Computes the magnitude of the value.
   *
   * @returns The absolute value.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__abs__`
   */
  abs(): RealElement {
    if (typeof this.real.data === 'number' || typeof this.imag.data === 'number') return this.context.mpf(Math.hypot(this.real.value, this.imag.value));
    return this.context.mpf(C.cabs([this.real.data, this.imag.data], this.context.prec));
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__eq__`
   */
  equals(other: unknown): boolean {
    const b = this.context.convert(other);
    return this.real.equals(b.real) && this.imag.equals(b.imag);
  }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__add__`
   */
  add(other: unknown): ComplexElement {
    const b = this.context.convert(other);
    return this.context.mpc(this.real.add(b.real), this.imag.add(b.imag));
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__sub__`
   */
  sub(other: unknown): ComplexElement { return this.add(this.context.mpc(other).neg()); }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param other - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__mul__`
   */
  mul(other: unknown): ComplexElement {
    const converted = this.context.convert(other);
    if (converted instanceof RealElement) return this.context.mpc(this.real.mul(converted), this.imag.mul(converted));
    const b = converted;
    if (typeof this.real.data !== 'number' && typeof this.imag.data !== 'number' && typeof b.real.data !== 'number' && typeof b.imag.data !== 'number') {
      const [re, im] = C.cmul([this.real.data, this.imag.data], [b.real.data, b.imag.data], this.context.prec);
      return this.context.mpc(re, im);
    }
    return this.context.mpc(this.real.mul(b.real).sub(this.imag.mul(b.imag)), this.real.mul(b.imag).add(this.imag.mul(b.real)));
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param other - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__div__`
   */
  div(other: unknown): ComplexElement {
    const converted = this.context.convert(other);
    if (converted instanceof RealElement) return this.context.mpc(this.real.div(converted), this.imag.div(converted));
    const b = converted;
    if (typeof this.real.data !== 'number' && typeof this.imag.data !== 'number' && typeof b.real.data !== 'number' && typeof b.imag.data !== 'number') {
      const [re, im] = C.cdiv([this.real.data, this.imag.data], [b.real.data, b.imag.data], this.context.prec);
      return this.context.mpc(re, im);
    }
    const d = b.real.mul(b.real).add(b.imag.mul(b.imag));
    return this.context.mpc(this.real.mul(b.real).add(this.imag.mul(b.imag)).div(d), this.imag.mul(b.real).sub(this.real.mul(b.imag)).div(d));
  }
  /**
   * Raises the value to the specified power.
   *
   * @param other - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @see SymPy `sympy.polys.domains.mpelements.ComplexElement.__pow__`
   */
  pow(other: unknown): ComplexElement {
    const b = this.context.convert(other);
    const re = this.real.data, im = this.imag.data, br = b.real.data, bi = b.imag.data;
    if (b.isZero) return this.context.mpc(1);
    if (typeof re === 'number' || typeof im === 'number' || typeof br === 'number' || typeof bi === 'number') {
      if (this.imag.isZero && b.imag.isZero) return this.context.mpc(this.real.pow(b.real));
      if (typeof br !== 'number' && b.imag.isZero && br.exp >= 0n) {
        const n = F.floor(br);
        if (n < 0n) return this.context.mpc(1).div(this.pow(-n));
        let result = this.pos(), base: ComplexElement = this, k = n - 1n;
        while (k > 0n) {
          if (k & 1n) result = result.mul(base);
          k >>= 1n;
          if (k) base = base.mul(base);
        }
        return result;
      }
      return this.context.mpc(NaN, NaN);
    }
    const [r, i] = C.cpow([re, im], [br, bi], this.context.prec);
    return this.context.mpc(r, i);
  }
}

/** Configures the precision, tolerance and parent domain of a numeric context. */
export interface MPContextOptions {
  /** The working precision in decimal digits. */
  dps?: number;
  /** The tolerance for comparisons and rational approximation. */
  tol?: unknown;
  /** Reserved real-arithmetic option. The context currently accepts both real and complex elements. */
  real?: boolean;
  /** The domain associated with the numeric context. */
  parent?: Domain;
}

/**
 * Numeric context for domain elements; rounding is nearest with ties to even.
 *
 * @see SymPy `sympy.polys.domains.mpelements.MPContext`
 */
export class MPContext {
  private precision = 53;
  /** The domain owning the context, or `NoMatch` for an independent context. */
  readonly parent: Domain | NoMatchResult;
  /** The default tolerance for numerical comparisons. */
  readonly tolerance: RealElement;
  /** The denominator bound for rational approximation. */
  readonly maxDenom: bigint;
  /** The additive identity. */
  readonly zero: RealElement;
  /** The multiplicative identity. */
  readonly one: RealElement;
  /** The imaginary unit. */
  readonly j: ComplexElement;
  /** The positive infinity at the current precision. */
  readonly inf: RealElement;
  /** The negative infinity at the current precision. */
  readonly ninf: RealElement;
  /** The floating-point value representing an indeterminate number. */
  readonly nan: RealElement;
  /** The flag for trapping nonreal numerical results. */
  trapComplex = true;
  /** The flag selecting human-readable numeric representations. */
  pretty = true;
  /**
   * Sets the precision and comparison tolerance for real and complex arithmetic.
   *
   * @param prec - Precision in bits.
   * @param options - Precision in decimal digits, tolerance and parent domain.
   */
  constructor(prec = 53, options: MPContextOptions = {}) {
    this.prec = options.dps === undefined ? prec : F.dpsToPrec(options.dps);
    this.parent = options.parent ?? NoMatch;
    this.zero = this.mpf(0); this.one = this.mpf(1); this.j = this.mpc(0, 1);
    this.inf = this.mpf(Infinity); this.ninf = this.mpf(-Infinity); this.nan = this.mpf(NaN);
    const tol = options.tol;
    // Numeric tolerances retain their supplied binary value; only strings are parsed at context precision.
    this.tolerance = tol === undefined ? this.makeTol()
      : tol instanceof RealElement ? this.mpf(new RawReal(tol.data))
      : tol instanceof Float ? this.makeMpf(tol.mpf)
      : typeof tol === 'bigint' ? this.makeMpf(F.fromInt(tol))
      : typeof tol === 'number' && Number.isFinite(tol) ? this.makeMpf(F.fromNumber(tol))
      : this.mpf(tol);
    this.maxDenom = this.tolerance.isZero ? 1000000n : this.mpf(this.one.div(this.tolerance)).toInt();
  }
  /**
   * Selects the number of binary digits used for arithmetic.
   *
   * @returns The working precision in bits.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.prec`
   */
  get prec(): number { return this.precision; }
  /**
   * Selects the number of binary digits used for arithmetic.
   *
   * @param value - New precision in bits.
   * @throws RangeError when the precision is not finite.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.prec`
   */
  set prec(value: number) {
    if (!Number.isFinite(value)) throw new RangeError('precision must be finite');
    this.precision = Math.max(1, Math.trunc(value));
  }
  /**
   * Selects the working precision in decimal digits.
   *
   * @returns The working precision in decimal digits.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.dps`
   */
  get dps(): number { return F.precToDps(this.prec); }
  /**
   * Selects the working precision in decimal digits.
   *
   * @param value - New precision in decimal digits.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.dps`
   */
  set dps(value: number) { this.prec = F.dpsToPrec(value); }
  /**
   * Derives a comparison tolerance from the binary working precision.
   *
   * @returns The default tolerance at the current precision.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.make_tol`
   */
  makeTol(): RealElement { return this.makeMpf({ man: 25n, exp: BigInt(3 - this.prec) }); }
  /**
   * Creates a real value at the current precision.
   *
   * @param value - Value to represent.
   * @returns A real element at the context precision.
   */
  mpf(value: unknown = 0): RealElement { return new RealElement(value, this); }
  /**
   * Combines the real and imaginary parts into a complex value.
   *
   * @param real - Real component.
   * @param imag - Imaginary component.
   * @returns A complex element at the context precision.
   */
  mpc(real: unknown = 0, imag: unknown = 0): ComplexElement { return new ComplexElement(real, imag, this); }
  /**
   * Constructs a real element from its raw binary representation.
   *
   * @param value - Value to represent.
   * @returns A real element at the context precision.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.make_mpf`
   */
  makeMpf(value: F.Mpf): RealElement { return this.mpf(new RawReal(value)); }
  /**
   * Constructs a complex element from two raw binary components.
   *
   * @param value - Value to represent.
   * @returns A complex element at the context precision.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.make_mpc`
   */
  makeMpc(value: C.Mpc): ComplexElement { return this.mpc(new RawReal(value[0]), new RawReal(value[1])); }
  /**
   * Coerces the input into the target domain.
   *
   * @param value - Value to represent.
   * @param strings - Allow parsing of numeric strings.
   * @returns The value represented in the target domain.
   * @throws TypeError when string parsing is disabled for a string input.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.convert`
   */
  convert(value: unknown, strings = true): RealElement | ComplexElement {
    if (value instanceof RealElement || value instanceof ComplexElement) return value;
    if (typeof value === 'string' && !strings) throw new TypeError('string conversion disabled');
    if (typeof value === 'string' && /[ij]\)?$/i.test(value.trim())) {
      const [re, im] = complexParts(value);
      return this.mpc(re, im);
    }
    return this.mpf(value);
  }
  /**
   * Approximates a real value by a fraction, optionally bounding its denominator.
   *
   * @param value - Real number to approximate by a fraction.
   * @param limit - Limit the denominator according to the context tolerance.
   * @returns The numerator and denominator of the rational approximation.
   * @throws RangeError when the value is not finite.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.to_rational`
   */
  toRational(value: unknown, limit = true): [bigint, bigint] {
    const v = value instanceof RealElement ? value.data : this.mpf(value).data;
    if (typeof v === 'number') throw new RangeError('nonfinite rational');
    const [p, q] = F.toRational(v);
    if (!limit || q <= this.maxDenom) return [p, q];
    let p0 = 0n, q0 = 1n, p1 = 1n, q1 = 0n, n = p, d = q;
    for (;;) {
      const a = n / d - (n < 0n && n % d !== 0n ? 1n : 0n);
      const q2 = q0 + a * q1;
      if (q2 > this.maxDenom) break;
      [p0, q0, p1, q1] = [p1, q1, p0 + a * p1, q2];
      [n, d] = [d, n - a * d];
    }
    const k = (this.maxDenom - q0) / q1;
    const bp = p0 + k * p1, bq = q0 + k * q1;
    if (p1 === 0n || bp === 0n) return [p, q];
    const abs = (x: bigint): bigint => x < 0n ? -x : x;
    return abs(p1 * q - p * q1) * bq <= abs(bp * q - p * bq) * q1 ? [p1, q1] : [bp, bq];
  }
  /**
   * Compares two values using relative and absolute tolerances.
   *
   * @param s - First value to compare.
   * @param t - Second value to compare.
   * @param options - Relative and absolute tolerances, `relEps` and `absEps`.
   * @returns Whether the values agree within the tolerances.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.almosteq`
   */
  almosteq(s: unknown, t: unknown, options: { relEps?: unknown; absEps?: unknown } = {}): boolean {
    const a = this.convert(s), b = this.convert(t);
    const fallback = this.tolerance.isZero ? this.makeTol() : this.tolerance;
    const rel = this.mpf(options.relEps ?? options.absEps ?? fallback);
    const abs = this.mpf(options.absEps ?? options.relEps ?? fallback);
    const diff = a.sub(b).abs();
    if (diff.le(abs)) return true;
    const aa = a.abs(), bb = b.abs();
    return this.mpf(diff.div(aa.lt(bb) ? bb : aa)).le(rel);
  }
  /**
   * Sum with exact finite accumulation and a single final rounding.
   *
   * @param terms - Terms to sum.
   * @param options - Apply `absolute` or `squared` to the summands before addition.
   * @returns The sum of the terms.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.fsum`
   */
  fsum(terms: Iterable<unknown>, options: { absolute?: boolean; squared?: boolean } = {}): RealElement | ComplexElement {
    let re: RealValue = F.ZERO, im: RealValue = F.ZERO, complex = false;
    const sum = (a: RealValue, b: RealValue): RealValue => typeof a !== 'number' && typeof b !== 'number' ? F.add(a, b) : arithmetic(a, b, 'add', this.prec);
    const product = (a: RealValue, b: RealValue): RealValue => typeof a !== 'number' && typeof b !== 'number' ? F.mul(a, b) : arithmetic(a, b, 'mul', this.prec);
    for (const term of terms) {
      const v = this.convert(term);
      let a = v.real.data, b = v.imag.data;
      if (options.squared) {
        const aa = product(a, a), bb = product(b, b);
        b = options.absolute ? F.ZERO : product(F.fromInt(2n), product(a, b));
        a = sum(aa, options.absolute ? bb : negative(bb));
      } else if (options.absolute) { a = v.abs().data; b = F.ZERO; }
      re = sum(re, a); im = sum(im, b);
      complex ||= v instanceof ComplexElement && !options.absolute;
    }
    return complex ? this.mpc(re, im) : this.mpf(re);
  }
  /**
   * Dot product; a single iterable supplies pairs, two iterables supply vectors.
   *
   * @param a - First vector or iterable of coordinate pairs.
   * @param b - Second vector when the inputs are separate.
   * @param options - Set `conjugate` to conjugate the second factor.
   * @returns The dot product at the context precision.
   * @throws TypeError when a single iterable does not supply coordinate pairs.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.fdot`
   */
  fdot(a: Iterable<unknown>, b?: Iterable<unknown>, options: { conjugate?: boolean } = {}): RealElement | ComplexElement {
    const pairs: [unknown, unknown][] = [];
    if (b !== undefined) {
      const right = b[Symbol.iterator]();
      for (const left of a) {
        const next = right.next();
        if (next.done === true) break;
        pairs.push([left, next.value]);
      }
    } else {
      for (const pair of a) {
        if (!Array.isArray(pair) || pair.length !== 2) throw new TypeError('expected dot product pairs');
        pairs.push([pair[0], pair[1]]);
      }
    }
    const products: (RealElement | ComplexElement)[] = [];
    for (const [x, y] of pairs) {
      const u = this.convert(x), v0 = this.convert(y), v = options.conjugate ? v0.conjugate() : v0;
      const ar = u.real.data, ai = u.imag.data, br = v.real.data, bi = v.imag.data;
      if (typeof ar !== 'number' && typeof ai !== 'number' && typeof br !== 'number' && typeof bi !== 'number') {
        const re = F.sub(F.mul(ar, br), F.mul(ai, bi)), im = F.add(F.mul(ar, bi), F.mul(ai, br));
        products.push(u instanceof ComplexElement || v instanceof ComplexElement ? this.makeMpc([re, im]) : this.makeMpf(re));
      } else products.push(u.mul(v));
    }
    return this.fsum(products);
  }
  /**
   * Binary magnitude bound, retaining bigint exponents outside double range.
   *
   * @param value - Value to represent.
   * @returns A binary magnitude bound.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.mag`
   */
  mag(value: unknown): bigint | RealElement {
    const v = this.convert(value);
    if (v instanceof ComplexElement) {
      if (v.real.isZero) return this.mag(v.imag);
      if (v.imag.isZero) return this.mag(v.real);
      const a = this.mag(v.real), b = this.mag(v.imag);
      if (a instanceof RealElement || b instanceof RealElement) return this.isnan(v) ? this.nan : this.inf;
      return 1n + (a > b ? a : b);
    }
    if (typeof v.data === 'number') return Number.isNaN(v.data) ? this.nan : this.inf;
    if (v.isZero) return this.ninf;
    return F.magExact(v.data);
  }
  /**
   * Detects NaN in the real or imaginary component.
   *
   * @param value - Value to represent.
   * @returns Whether either component is NaN.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.isnan`
   */
  isnan(value: unknown): boolean {
    const v = this.convert(value);
    return v instanceof RealElement ? Number.isNaN(v.data) : this.isnan(v.real) || this.isnan(v.imag);
  }
  /**
   * Detects infinity in either component.
   *
   * @param value - Value to represent.
   * @returns Whether the value has an infinite component.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.isinf`
   */
  isinf(value: unknown): boolean {
    const v = this.convert(value);
    return v instanceof RealElement ? typeof v.data === 'number' && !Number.isNaN(v.data) : this.isinf(v.real) || this.isinf(v.imag);
  }
  /**
   * Tests for a finite, nonzero numeric value.
   *
   * @param value - Value to represent.
   * @returns Whether the value is finite and nonzero.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.isnormal`
   */
  isnormal(value: unknown): boolean { return !this.isnan(value) && !this.isinf(value) && !this.convert(value).isZero; }
  /**
   * Tests integrality, optionally allowing Gaussian integers.
   *
   * @param value - Value to represent.
   * @param gaussian - Allow a Gaussian integer with integral real and imaginary components.
   * @returns Whether the value is an integer in the selected sense.
   * @see SymPy `sympy.polys.domains.mpelements.MPContext.isint`
   */
  isint(value: unknown, gaussian = false): boolean {
    const v = this.convert(value);
    if (v instanceof ComplexElement) return this.isint(v.real) && (gaussian ? this.isint(v.imag) : v.imag.isZero);
    return typeof v.data !== 'number' && v.data.exp >= 0n;
  }
}
