// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arithmetic on numeric nodes (Rational and Float).
 */

import * as F from '../numeric/mpf';
import type { Num } from './nodes';
import { Float, Rational } from './nodes';
import { ipow } from './numbers';

const toNumber = (a: Num): number => (a instanceof Rational ? a.value : a.value);

/** Working precision of a Float operation (SymPy: the larger Float precision). */
function opPrec(a: Num, b: Num): number {
  if (a instanceof Float && b instanceof Float) return Math.max(a.prec, b.prec);
  return a instanceof Float ? a.prec : (b as Float).prec;
}

/** Value as mpf; rationals are rounded to prec (SymPy Rational._as_mpf_op). */
export function toMpf(a: Num, prec: number): F.Mpf {
  if (a instanceof Float) return a.mpf;
  return a.q === 1n ? F.normalize(a.p, 0, prec) : F.fromRational(a.p, a.q, prec);
}

/** Float result; an exact zero becomes the integer 0 (SymPy Float._new). */
export function mkFloat(v: F.Mpf, prec: number): Num {
  return F.isZero(v) ? Rational.of(0n) : new Float(v, prec);
}

export function numAdd(a: Num, b: Num): Num {
  if (a instanceof Rational && b instanceof Rational) {
    if (a.q === b.q) return Rational.of(a.p + b.p, a.q);
    return Rational.of(a.p * b.q + b.p * a.q, a.q * b.q);
  }
  const prec = opPrec(a, b);
  return mkFloat(F.add(toMpf(a, prec), toMpf(b, prec), prec), prec);
}

export function numMul(a: Num, b: Num): Num {
  if (a instanceof Rational && b instanceof Rational) {
    if (a.isOne) return b;
    if (b.isOne) return a;
    return Rational.of(a.p * b.p, a.q * b.q);
  }
  const prec = opPrec(a, b);
  return mkFloat(F.mul(toMpf(a, prec), toMpf(b, prec), prec), prec);
}

export function numNeg(a: Num): Num {
  return a instanceof Rational ? Rational.of(-a.p, a.q) : new Float(F.neg(a.mpf), a.prec);
}

export function numInv(a: Num): Num {
  if (a.isZero) throw new RangeError('Division by zero');
  return a instanceof Rational ? Rational.of(a.q, a.p) : new Float(F.div(F.ONE, a.mpf, a.prec), a.prec);
}

/** a^n for integer n. */
export function numPowInt(a: Num, n: bigint): Num {
  if (a instanceof Rational) {
    if (n >= 0n) return Rational.of(ipow(a.p, n), ipow(a.q, n));
    if (a.isZero) throw new RangeError('Division by zero: 0 raised to a negative power');
    return Rational.of(ipow(a.q, -n), ipow(a.p, -n));
  }
  return mkFloat(F.powInt(a.mpf, n, a.prec), a.prec);
}

export function numCmp(a: Num, b: Num): number {
  if (a instanceof Rational && b instanceof Rational) {
    const d = a.p * b.q - b.p * a.q;
    return d < 0n ? -1 : d > 0n ? 1 : 0;
  }
  const [ap, aq] = a instanceof Float ? F.toRational(a.mpf) : [a.p, a.q];
  const [bp, bq] = b instanceof Float ? F.toRational(b.mpf) : [b.p, b.q];
  const d = ap * bq - bp * aq;
  return d < 0n ? -1 : d > 0n ? 1 : 0;
}

export function numIsOne(a: Num): boolean {
  return a instanceof Rational ? a.isOne : a.mpf.man === 1n && a.mpf.exp === 0;
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

