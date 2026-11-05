// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, sets/ordinals.py, BSD-3-Clause; see LICENSE.

/**
 * @file Ordinals in Cantor normal form (SymPy `sympy.sets.ordinals`): `Ordinal`, `OmegaPower`, the
 * ordinal zero `ord0` and the first infinite ordinal `omega`, with ordinal addition, multiplication
 * and `omega**a`. The objects are not expressions (as in SymPy, they do not take part in the arithmetic
 * of `Expr`); `a.add(b)`, `a.mul(b)` and `omega.pow(a)` are SymPy's `a + b`, `a * b` and `omega**a`.
 */

import { at, first, last } from '../core/guard';

/** A natural number or an ordinal (SymPy accepts Python ints where an ordinal is expected). */
export type OrdinalLike = OrdinalNode | number | bigint;

const toBigInt = (n: number | bigint): bigint => {
  if (typeof n === 'bigint') return n;
  if (!Number.isInteger(n)) throw new TypeError('an ordinal term needs an integer');
  return BigInt(n);
};

/**
 * A term `w**exp*mult` of an ordinal (SymPy OmegaPower): the exponent is an ordinal, the multiplicity
 * a positive integer.
 */
export class OmegaPowerNode {
  readonly exp: OrdinalNode;
  readonly mult: bigint;
  constructor(a: OrdinalLike, b: number | bigint) {
    const m = toBigInt(b);
    if (m <= 0n) throw new TypeError('multiplicity must be a positive integer');
    this.exp = a instanceof OrdinalNode ? a : convertOrdinal(a);
    this.mult = m;
  }
  /** SymPy `==`: equal exponents and multiplicities; a natural number n is the term w**0*n. */
  equals(other: OmegaPowerNode | number | bigint): boolean {
    const o = other instanceof OmegaPowerNode ? other : new OmegaPowerNode(0, other);
    return this.exp.equals(o.exp) && this.mult === o.mult;
  }
  /** SymPy `<`: by exponent, then by multiplicity. */
  lt(other: OmegaPowerNode | number | bigint): boolean {
    const o = other instanceof OmegaPowerNode ? other : new OmegaPowerNode(0, other);
    return this.exp.equals(o.exp) ? this.mult < o.mult : this.exp.lt(o.exp);
  }
  toString(): string {
    return `OmegaPower(${this.exp.toString()}, ${this.mult})`;
  }
}

/** An ordinal in Cantor normal form: a sum of terms with decreasing exponents (SymPy Ordinal). */
export class OrdinalNode {
  readonly terms: readonly OmegaPowerNode[];
  constructor(terms: readonly OmegaPowerNode[]) {
    for (let i = 0; i + 1 < terms.length; i++) {
      if (at(terms, i).exp.lt(at(terms, i + 1).exp)) throw new RangeError('powers must be in decreasing order');
    }
    this.terms = terms;
  }
  get isZero(): boolean {
    return this.terms.length === 0;
  }
  /** The first term (SymPy leading_term); the ordinal zero has none. */
  get leadingTerm(): OmegaPowerNode {
    if (this.isZero) throw new RangeError('ordinal zero has no leading term');
    return first(this.terms);
  }
  /** The last term (SymPy trailing_term); the ordinal zero has none. */
  get trailingTerm(): OmegaPowerNode {
    if (this.isZero) throw new RangeError('ordinal zero has no trailing term');
    return last(this.terms);
  }
  /** SymPy is_successor_ordinal: the last term is finite. */
  get isSuccessorOrdinal(): boolean {
    return !this.isZero && this.trailingTerm.exp.isZero;
  }
  /** SymPy is_limit_ordinal: a nonzero ordinal that is not a successor. */
  get isLimitOrdinal(): boolean {
    return !this.isZero && !this.trailingTerm.exp.isZero;
  }
  /** The exponent of the leading term (SymPy degree). */
  get degree(): OrdinalNode {
    return this.leadingTerm.exp;
  }
  equals(other: OrdinalLike): boolean {
    const o = convertOrdinal(other);
    return this.terms.length === o.terms.length && this.terms.every((t, i) => t.equals(at(o.terms, i)));
  }
  lt(other: OrdinalLike): boolean {
    const o = convertOrdinal(other);
    const n = Math.min(this.terms.length, o.terms.length);
    for (let i = 0; i < n; i++) {
      const a = at(this.terms, i);
      const b = at(o.terms, i);
      if (!a.equals(b)) return a.lt(b);
    }
    return this.terms.length < o.terms.length;
  }
  le(other: OrdinalLike): boolean {
    return this.equals(other) || this.lt(other);
  }
  gt(other: OrdinalLike): boolean {
    return !this.le(other);
  }
  ge(other: OrdinalLike): boolean {
    return !this.lt(other);
  }
  /** Ordinal addition (SymPy `self + other`); it is not commutative: `3 + w` is `w`. */
  add(other: OrdinalLike): OrdinalNode {
    const o = convertOrdinal(other);
    if (o.isZero) return this;
    const a = this.terms;
    const bExp = o.degree;
    let r = a.length - 1;
    while (r >= 0 && at(a, r).exp.lt(bExp)) r--;
    if (r < 0) return o;
    const ar = at(a, r);
    if (ar.exp.equals(bExp)) {
      return new OrdinalNode([...a.slice(0, r), new OmegaPowerNode(bExp, ar.mult + o.leadingTerm.mult), ...o.terms.slice(1)]);
    }
    return new OrdinalNode([...a.slice(0, r + 1), ...o.terms]);
  }
  /** Ordinal multiplication (SymPy `self * other`); it is not commutative: `2*w` is `w`. */
  mul(other: OrdinalLike): OrdinalNode {
    const o = convertOrdinal(other);
    if (this.isZero || o.isZero) return ord0;
    const aExp = this.degree;
    const aMult = this.leadingTerm.mult;
    if (o.isLimitOrdinal) return new OrdinalNode(o.terms.map((t) => new OmegaPowerNode(aExp.add(t.exp), t.mult)));
    return new OrdinalNode([
      ...o.terms.slice(0, -1).map((t) => new OmegaPowerNode(aExp.add(t.exp), t.mult)),
      new OmegaPowerNode(aExp, aMult * o.trailingTerm.mult),
      ...this.terms.slice(1),
    ]);
  }
  /** `omega**other` (SymPy defines `**` only for the base omega). */
  pow(other: OrdinalLike): OrdinalNode {
    if (!this.equals(omega)) throw new TypeError('only omega can be raised to an ordinal power');
    return new OrdinalNode([new OmegaPowerNode(other, 1)]);
  }
  /** SymPy's str: `w**(w + 1) + w**3*2`, `ord0` for zero. */
  toString(): string {
    if (this.isZero) return 'ord0';
    return this.terms
      .map((t) => {
        if (t.exp.isZero) return t.mult.toString();
        const base = t.exp.equals(1) ? 'w' : t.exp.terms.length > 1 || t.exp.isLimitOrdinal ? `w**(${t.exp.toString()})` : `w**${t.exp.toString()}`;
        return t.mult === 1n ? base : `${base}*${t.mult}`;
      })
      .join(' + ');
  }
}

/** The ordinal of a natural number (SymPy Ordinal.convert). */
export function convertOrdinal(value: OrdinalLike): OrdinalNode {
  if (value instanceof OrdinalNode) return value;
  return toBigInt(value) === 0n ? ord0 : new OrdinalNode([new OmegaPowerNode(0, value)]);
}

/** The ordinal zero (SymPy ord0, OrdinalZero). */
export const ord0: OrdinalNode = new OrdinalNode([]);
/** The first infinite ordinal w (SymPy omega, OrdinalOmega). */
export const omega: OrdinalNode = new OrdinalNode([new OmegaPowerNode(1, 1)]);

/** SymPy `OmegaPower(a, b)`: the term w**a*b. */
export function OmegaPower(a: OrdinalLike, b: number | bigint): OmegaPowerNode {
  return new OmegaPowerNode(a, b);
}

/** SymPy `Ordinal(*terms)`: the ordinal with these terms, in decreasing order of exponent. */
export function Ordinal(...terms: OmegaPowerNode[]): OrdinalNode {
  return new OrdinalNode(terms);
}
