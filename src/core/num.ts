// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arithmetic on numeric nodes (Rational and Float).
 */

import { Float, Num, Rational } from './nodes';
import { ipow } from './numbers';

const toNumber = (a: Num): number => (a instanceof Rational ? a.value : a.value);

export function numAdd(a: Num, b: Num): Num {
  if (a instanceof Rational && b instanceof Rational) {
    if (a.q === b.q) return Rational.of(a.p + b.p, a.q);
    return Rational.of(a.p * b.q + b.p * a.q, a.q * b.q);
  }
  return new Float(toNumber(a) + toNumber(b));
}

export function numMul(a: Num, b: Num): Num {
  if (a instanceof Rational && b instanceof Rational) {
    if (a.isOne) return b;
    if (b.isOne) return a;
    return Rational.of(a.p * b.p, a.q * b.q);
  }
  return new Float(toNumber(a) * toNumber(b));
}

export function numNeg(a: Num): Num {
  return a instanceof Rational ? Rational.of(-a.p, a.q) : new Float(-a.value);
}

export function numInv(a: Num): Num {
  if (a.isZero) throw new RangeError('Division by zero');
  return a instanceof Rational ? Rational.of(a.q, a.p) : new Float(1 / a.value);
}

/** a^n for integer n. */
export function numPowInt(a: Num, n: bigint): Num {
  if (a instanceof Rational) {
    if (n >= 0n) return Rational.of(ipow(a.p, n), ipow(a.q, n));
    if (a.isZero) throw new RangeError('Division by zero: 0 raised to a negative power');
    return Rational.of(ipow(a.q, -n), ipow(a.p, -n));
  }
  return new Float(Math.pow(a.value, Number(n)));
}

export function numCmp(a: Num, b: Num): number {
  if (a instanceof Rational && b instanceof Rational) {
    const d = a.p * b.q - b.p * a.q;
    return d < 0n ? -1 : d > 0n ? 1 : 0;
  }
  const d = toNumber(a) - toNumber(b);
  return d < 0 ? -1 : d > 0 ? 1 : 0;
}

export function numIsOne(a: Num): boolean {
  return a instanceof Rational ? a.isOne : a.value === 1;
}

export function numAbs(a: Num): Num {
  return a.isNegative ? numNeg(a) : a;
}

export function numToNumber(a: Num): number {
  return toNumber(a);
}

/** floor(a) for a rational. */
export function ratFloor(a: Rational): bigint {
  const q = a.p / a.q;
  return a.p < 0n && q * a.q !== a.p ? q - 1n : q;
}

/** a mod m for rationals, result in [0, m). */
export function ratMod(a: Rational, m: Rational): Rational {
  const k = ratFloor(Rational.of(a.p * m.q, a.q * m.p));
  return numAdd(a, numNeg(numMul(Rational.of(k), m))) as Rational;
}

