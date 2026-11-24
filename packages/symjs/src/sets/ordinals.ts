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

/** A natural number or an ordinal. */
export type OrdinalLike = OrdinalNode | number | bigint;

const toBigInt = (n: number | bigint): bigint => {
  if (typeof n === 'bigint') return n;
  if (!Number.isInteger(n)) throw new TypeError('an ordinal term needs an integer');
  return BigInt(n);
};

/**
 * A term `w**exp*mult` of an ordinal: the exponent is an ordinal, the multiplicity
 * a positive integer.
 *
 * @see SymPy `sympy.sets.ordinals.OmegaPower`
 */
export class OmegaPowerNode {
  /**
   * The ordinal exponent of omega.
   *
   * @see SymPy `sympy.sets.ordinals.OmegaPower.exp`
   */
  readonly exp: OrdinalNode;
  /**
   * The positive integer coefficient of the power of omega.
   *
   * @see SymPy `sympy.sets.ordinals.OmegaPower.mult`
   */
  readonly mult: bigint;
  /**
   * Creates an OmegaPowerNode instance.
   *
   * @param a - The ordinal exponent of omega.
   * @param b - The positive integer multiplier.
   * @throws TypeError when the multiplicity is not a positive integer.
   */
  constructor(a: OrdinalLike, b: number | bigint) {
    const m = toBigInt(b);
    if (m <= 0n) throw new TypeError('multiplicity must be a positive integer');
    this.exp = a instanceof OrdinalNode ? a : convertOrdinal(a);
    this.mult = m;
  }
  /**
   * Equal exponents and multiplicities; a natural number n is the term w**0*n.
   *
   * @param other - The right-hand operand.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.sets.ordinals.OmegaPower.__eq__`
   */
  equals(other: OmegaPowerNode | number | bigint): boolean {
    const o = other instanceof OmegaPowerNode ? other : new OmegaPowerNode(0, other);
    return this.exp.equals(o.exp) && this.mult === o.mult;
  }
  /**
   * By exponent, then by multiplicity.
   *
   * @param other - The right-hand operand.
   * @returns Whether this ordinal is strictly smaller.
   * @see SymPy `sympy.sets.ordinals.OmegaPower.__lt__`
   */
  lt(other: OmegaPowerNode | number | bigint): boolean {
    const o = other instanceof OmegaPowerNode ? other : new OmegaPowerNode(0, other);
    return this.exp.equals(o.exp) ? this.mult < o.mult : this.exp.lt(o.exp);
  }
  /**
   * Formats this value as a string.
   *
   * @returns The formatted text.
   */
  toString(): string {
    return `OmegaPower(${this.exp.toString()}, ${this.mult})`;
  }
}

/**
 * An ordinal in Cantor normal form: a sum of terms with decreasing exponents.
 *
 * @see SymPy `sympy.sets.ordinals.Ordinal`
 * @example
 * ```ts
 * import { OmegaPower, OrdinalNode, omega } from '@symjs/symjs';
 * new OrdinalNode([OmegaPower(1, 1)]).equals(omega); // => True
 * ```
 */
export class OrdinalNode {
  /**
   * The terms of the ordinal in Cantor normal form.
   *
   * @see SymPy `sympy.sets.ordinals.Ordinal.terms`
   */
  readonly terms: readonly OmegaPowerNode[];
  /**
   * Creates an OrdinalNode instance.
   *
   * @param terms - The terms of the ordinal in Cantor normal form.
   * @throws RangeError when the powers of omega are not in decreasing order.
   */
  constructor(terms: readonly OmegaPowerNode[]) {
    for (let i = 0; i + 1 < terms.length; i++) {
      if (at(terms, i).exp.lt(at(terms, i + 1).exp)) throw new RangeError('powers must be in decreasing order');
    }
    this.terms = terms;
  }
  /**
   * Tests whether this ordinal is zero.
   *
   * @returns Whether the ordinal is zero.
   * @see SymPy `sympy.sets.ordinals.Ordinal.is_zero`
   */
  get isZero(): boolean {
    return this.terms.length === 0;
  }
  /**
   * The first term; the ordinal zero has none.
   *
   * @returns The first term.
   * @throws RangeError when the ordinal is zero.
   * @see SymPy `sympy.sets.ordinals.Ordinal.leading_term`
   */
  get leadingTerm(): OmegaPowerNode {
    if (this.isZero) throw new RangeError('ordinal zero has no leading term');
    return first(this.terms);
  }
  /**
   * The last term; the ordinal zero has none.
   *
   * @returns The last term.
   * @throws RangeError when the ordinal is zero.
   * @see SymPy `sympy.sets.ordinals.Ordinal.trailing_term`
   */
  get trailingTerm(): OmegaPowerNode {
    if (this.isZero) throw new RangeError('ordinal zero has no trailing term');
    return last(this.terms);
  }
  /**
   * The last term is finite.
   *
   * @returns Whether the ordinal belongs to this ordinal class.
   * @see SymPy `sympy.sets.ordinals.Ordinal.is_successor_ordinal`
   */
  get isSuccessorOrdinal(): boolean {
    return !this.isZero && this.trailingTerm.exp.isZero;
  }
  /**
   * A nonzero ordinal that is not a successor.
   *
   * @returns Whether the ordinal belongs to this ordinal class.
   * @see SymPy `sympy.sets.ordinals.Ordinal.is_limit_ordinal`
   */
  get isLimitOrdinal(): boolean {
    return !this.isZero && !this.trailingTerm.exp.isZero;
  }
  /**
   * Represents the exponent of the leading term.
   *
   * @returns The exponent of the leading term.
   * @see SymPy `sympy.sets.ordinals.Ordinal.degree`
   */
  get degree(): OrdinalNode {
    return this.leadingTerm.exp;
  }
  /**
   * Tests whether the two values are structurally equal.
   *
   * @param other - The right-hand operand.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__eq__`
   */
  equals(other: OrdinalLike): boolean {
    const o = convertOrdinal(other);
    return this.terms.length === o.terms.length && this.terms.every((t, i) => t.equals(at(o.terms, i)));
  }
  /**
   * Tests whether this ordinal is less than the other ordinal.
   *
   * @param other - The right-hand operand.
   * @returns Whether this ordinal is strictly smaller.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__lt__`
   */
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
  /**
   * Tests whether this ordinal is at most the other ordinal.
   *
   * @param other - The right-hand operand.
   * @returns Whether this ordinal is smaller or equal.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__le__`
   */
  le(other: OrdinalLike): boolean {
    return this.equals(other) || this.lt(other);
  }
  /**
   * Tests whether this ordinal is greater than the other ordinal.
   *
   * @param other - The right-hand operand.
   * @returns Whether this ordinal is strictly larger.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__gt__`
   */
  gt(other: OrdinalLike): boolean {
    return !this.le(other);
  }
  /**
   * Tests whether this ordinal is at least the other ordinal.
   *
   * @param other - The right-hand operand.
   * @returns Whether this ordinal is larger or equal.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__ge__`
   */
  ge(other: OrdinalLike): boolean {
    return !this.lt(other);
  }
  /**
   * Ordinal addition; it is not commutative: `3 + w` is `w`.
   *
   * @param other - The right-hand operand.
   * @returns The ordinal sum in operand order.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__add__`
   */
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
  /**
   * Ordinal multiplication; it is not commutative: `2*w` is `w`.
   *
   * @param other - The right-hand operand.
   * @returns The ordinal product in operand order.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__mul__`
   */
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
  /**
   * `omega**other`.
   *
   * @param other - The right-hand operand.
   * @returns The ordinal power.
   * @throws TypeError when the ordinal base is different from omega.
   * @see SymPy `sympy.sets.ordinals.Ordinal.__pow__`
   */
  pow(other: OrdinalLike): OrdinalNode {
    if (!this.equals(omega)) throw new TypeError('only omega can be raised to an ordinal power');
    return new OrdinalNode([new OmegaPowerNode(other, 1)]);
  }
  /**
   * SymPy's str: `w**(w + 1) + w**3*2`, `ord0` for zero.
   *
   * @returns The formatted text.
   */
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

/**
 * Returns the ordinal of a natural number.
 *
 * @param value - The value to assign or convert.
 * @returns The ordinal of a natural number.
 */
export function convertOrdinal(value: OrdinalLike): OrdinalNode {
  if (value instanceof OrdinalNode) return value;
  return toBigInt(value) === 0n ? ord0 : new OrdinalNode([new OmegaPowerNode(0, value)]);
}

/**
 * The ordinal zero.
 *
 * @see SymPy `sympy.sets.ordinals.ord0`
 */
export const ord0: OrdinalNode = new OrdinalNode([]);
/**
 * The first infinite ordinal w.
 *
 * @see SymPy `sympy.sets.ordinals.omega`
 * @example
 * ```ts
 * import { omega } from '@symjs/symjs';
 * omega.add(1).toString(); // => w + 1
 * ```
 */
export const omega: OrdinalNode = new OrdinalNode([new OmegaPowerNode(1, 1)]);

/**
 * Returns the term w**a*b.
 *
 * @param a - The ordinal exponent of omega.
 * @param b - The positive integer multiplier.
 * @returns The term w**a*b.
 * @see SymPy `sympy.sets.ordinals.OmegaPower`
 */
export function OmegaPower(a: OrdinalLike, b: number | bigint): OmegaPowerNode {
  return new OmegaPowerNode(a, b);
}

/**
 * Returns the ordinal with these terms, in decreasing order of exponent.
 *
 * @param terms - The terms of the ordinal in Cantor normal form.
 * @returns The ordinal with these terms, in decreasing order of exponent.
 * @see SymPy `sympy.sets.ordinals.Ordinal`
 * @example
 * ```ts
 * import { OmegaPower, Ordinal, omega } from '@symjs/symjs';
 * Ordinal(OmegaPower(1, 1)).equals(omega); // => True
 * ```
 */
export function Ordinal(...terms: OmegaPowerNode[]): OrdinalNode {
  return new OrdinalNode(terms);
}
