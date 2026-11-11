// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/intervalmath (BSD-3-Clause).
import type { Truth } from '../../core/truth';
import { truthAnd, truthOr, truthNot } from '../../core/truth';
/** An interval predicate and the validity of its underlying evaluation. */
export class intervalMembership {
  constructor(readonly value: Truth, readonly isValid: Truth) { if (![true, false, 'unknown'].includes(value) || ![true, false, 'unknown'].includes(isValid)) throw new TypeError('Membership values must be Truth values.'); }
  get(i: number): Truth { if (i !== 0 && i !== 1) throw new RangeError('Membership index must be 0 or 1.'); return i === 0 ? this.value : this.isValid; }
  get length(): number { return 2; }
  *[Symbol.iterator](): IterableIterator<Truth> { yield this.value; yield this.isValid; }
  and(other: intervalMembership): intervalMembership { if (!(other instanceof intervalMembership)) throw new TypeError('Expected an interval membership.'); return new intervalMembership(truthAnd(this.value, other.value), truthAnd(this.isValid, other.isValid)); }
  or(other: intervalMembership): intervalMembership { if (!(other instanceof intervalMembership)) throw new TypeError('Expected an interval membership.'); return new intervalMembership(truthOr(this.value, other.value), truthAnd(this.isValid, other.isValid)); }
  not(): intervalMembership { return new intervalMembership(truthNot(this.value), this.isValid); }
  xor(other: intervalMembership): intervalMembership { if (!(other instanceof intervalMembership)) throw new TypeError('Expected an interval membership.'); return new intervalMembership(this.value === 'unknown' || other.value === 'unknown' ? 'unknown' : this.value !== other.value, truthAnd(this.isValid, other.isValid)); }
  equals(other: intervalMembership | readonly [Truth, Truth]): boolean { const [a, b] = other; return this.value === a && this.isValid === b; }
  toString(): string { const show = (v: Truth): string => v === 'unknown' ? 'None' : v ? 'True' : 'False'; return `intervalMembership(${show(this.value)}, ${show(this.isValid)})`; }
}
