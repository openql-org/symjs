// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Digits of integers (SymPy sympy.ntheory.digits): digits,
 * count_digits and is_palindromic.
 */

import type { IntLike } from './intutil';
import { asInt, babs } from './intutil';

/**
 * The digits of n in base b, preceded by b (or -b for negative n) (SymPy
 * digits); `digits` pads with leading zeros to that many digits.
 */
export function digits(nIn: IntLike, bIn: IntLike = 10, ndigits?: number): bigint[] {
  const b = asInt(bIn);
  const n = asInt(nIn);
  if (b < 2n) throw new RangeError('b must be greater than 1');
  let x = babs(n);
  const y: bigint[] = [];
  while (x >= b) {
    y.push(x % b);
    x /= b;
  }
  y.push(x);
  y.push(n < 0n ? -b : b);
  y.reverse();
  const ndig = y.length - 1;
  if (ndigits !== undefined) {
    if (ndig > ndigits) throw new RangeError(`For ${n}, at least ${ndig} digits are needed.`);
    if (ndig < ndigits) y.splice(1, 0, ...new Array<bigint>(ndigits - ndig).fill(0n));
  }
  return y;
}

/** The count of each digit of n in base b, as digit -> count (SymPy count_digits). */
export function countDigits(n: IntLike, bIn: IntLike = 10): Map<bigint, bigint> {
  const b = asInt(bIn);
  const ds = digits(n, b);
  const rv = new Map<bigint, bigint>();
  for (const d of ds.slice(1)) rv.set(d, (rv.get(d) ?? 0n) + 1n);
  return rv;
}

/** SymPy is_palindromic of an integer in base b, or of a sequence (one definition, in utilities). */
export { isPalindromic } from '../utilities/iterables';
