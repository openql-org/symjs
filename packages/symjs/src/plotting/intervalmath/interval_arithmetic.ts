// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/intervalmath (BSD-3-Clause).
import type { Truth } from '../../core/truth';
import { truthAnd } from '../../core/truth';
import { intervalMembership } from './interval_membership';
export type IntervalLike = number | interval;
/** Closed numeric enclosure with three-valued domain validity. */
export class interval {
  readonly start: number;
  readonly end: number;
  isValid: Truth;
  constructor(start: IntervalLike, end?: number, options: { isValid?: Truth } = {}) {
    const a = start instanceof interval ? start.start : start;
    const b = start instanceof interval ? start.end : end ?? start;
    if (typeof a !== 'number' || typeof b !== 'number' || Number.isNaN(a) || Number.isNaN(b)) throw new TypeError('Interval endpoints must be numbers, not NaN.');
    // an interval has at most two endpoints; a third positional number is not an options object
    if (typeof options !== 'object' || options === null) throw new TypeError('Interval options must be an object.');
    this.start = Math.min(a, b); this.end = Math.max(a, b); this.isValid = options.isValid ?? true;
  }
  get mid(): number { return (this.start + this.end) / 2; }
  get width(): number { return this.end - this.start; }
  toString(): string { return `[${this.start.toFixed(6)}, ${this.end.toFixed(6)}]`; }
  contains(other: IntervalLike): boolean { const o = asInterval(other); return this.start <= o.start && o.end <= this.end; }
  lt(other: IntervalLike): intervalMembership { const o = asInterval(other); return new intervalMembership(this.end < o.start ? true : this.start > o.end ? false : 'unknown', truthAnd(this.isValid, o.isValid)); }
  le(other: IntervalLike): intervalMembership { const o = asInterval(other); return new intervalMembership(this.end <= o.start ? true : this.start > o.end ? false : 'unknown', truthAnd(this.isValid, o.isValid)); }
  gt(other: IntervalLike): intervalMembership { return asInterval(other).lt(this); }
  ge(other: IntervalLike): intervalMembership { return asInterval(other).le(this); }
  eq(other: IntervalLike): intervalMembership { const o = asInterval(other); return new intervalMembership(this.start === o.start && this.end === o.end ? true : this.end < o.start || this.start > o.end ? false : 'unknown', truthAnd(this.isValid, o.isValid)); }
  ne(other: IntervalLike): intervalMembership { return this.eq(other).not(); }
  add(other: IntervalLike): interval { const o = asInterval(other); return new interval(this.start + o.start, this.end + o.end, { isValid: truthAnd(this.isValid, o.isValid) }); }
  sub(other: IntervalLike): interval { return this.add(asInterval(other).neg()); }
  neg(): interval { return new interval(-this.end, -this.start, { isValid: this.isValid }); }
  mul(other: IntervalLike): interval {
    const o = asInterval(other), valid = truthAnd(this.isValid, o.isValid);
    if (valid !== true && other instanceof interval) return whole(valid);
    const product = (a: number, b: number): number => a === 0 || b === 0 ? 0 : a * b;
    const points = [product(this.start, o.start), product(this.start, o.end), product(this.end, o.start), product(this.end, o.end)];
    return new interval(Math.min(...points), Math.max(...points), { isValid: valid });
  }
  div(other: IntervalLike): interval {
    const o = asInterval(other), valid = truthAnd(this.isValid, o.isValid);
    if (valid !== true) return whole(valid);
    if (o.contains(0)) return whole(typeof other === 'number' ? false : 'unknown');
    const points = [this.start / o.start, this.start / o.end, this.end / o.start, this.end / o.end];
    return new interval(Math.min(...points), Math.max(...points));
  }
  pow(other: IntervalLike): interval {
    if (this.isValid !== true) return this;
    if (other instanceof interval) {
      if (this.end <= 0) return whole(false);
      if (this.start <= 0) return whole('unknown');
      const exponent = new interval(Math.log(this.start), Math.log(this.end)).mul(other);
      return new interval(Math.exp(exponent.start), Math.exp(exponent.end), { isValid: exponent.isValid });
    }
    if (!Number.isFinite(other)) throw new RangeError('Power must be finite.');
    if (other < 0) return new interval(1).div(this.pow(-other));
    if (other === 0) return new interval(1);
    // Recover simple rational exponents, including cube roots of negative numbers.
    let numerator = other, denominator = 1;
    if (!Number.isInteger(other)) for (let q = 2; q <= 1000; q++) if (Math.abs(other * q - Math.round(other * q)) < 1e-12) { numerator = Math.round(other * q); denominator = q; break; }
    const oddDenominator = Number.isInteger(numerator) && denominator % 2 === 1;
    if (this.start < 0 && !oddDenominator) return this.end < 0 ? whole(false) : new interval(0, this.end ** other, { isValid: 'unknown' });
    const even = Number.isInteger(numerator) && numerator % 2 === 0;
    const power = (x: number): number => x < 0 ? (even ? 1 : -1) * Math.abs(x) ** other : x ** other;
    const a = power(this.start), b = power(this.end);
    // SymPy 1.14 misses zero for fractional even numerators across the origin.
    return new interval(even && this.contains(0) ? 0 : Math.min(a, b), Math.max(a, b));
  }
  rpow(base: IntervalLike): interval { if (typeof base === 'number' && base < 0 && this.width === 0) return new interval(base).pow(this.start); return asInterval(base).pow(this); }
}
export function asInterval(value: IntervalLike): interval { return value instanceof interval ? value : new interval(value); }
export function whole(valid: Truth): interval { return new interval(-Infinity, Infinity, { isValid: valid }); }
