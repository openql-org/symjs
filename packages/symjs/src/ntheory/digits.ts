// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Digits of integers (SymPy sympy.ntheory.digits): digits,
 * count_digits and is_palindromic.
 */

import type { IntLike } from './intutil';
import { asInt, babs } from './intutil';

/**
 * The digits of n in base b, preceded by b (or -b for negative n); `digits` pads with leading zeros
 * to that many digits.
 *
 * @param nIn - Integer to expand.
 * @param bIn - Radix of the expansion.
 * @param digitsIn - Minimum number of digits, padding on the left with zeros.
 * @returns The signed radix followed by the digits from most significant to least.
 * @throws RangeError when the base is less than two or the requested width is too small.
 * @see SymPy `sympy.ntheory.digits.digits`
 * @example
 * ```ts
 * import { digits } from '@symjs/symjs';
 *
 * digits(35); // => [10, 3, 5]
 * digits(-35); // => [-10, 3, 5]
 * ```
 */
export function digits(nIn: IntLike, bIn: IntLike = 10, digitsIn?: IntLike): bigint[] {
  const ndigits = digitsIn === undefined ? undefined : Number(asInt(digitsIn));
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

/**
 * Counts the occurrences of each digit in the specified radix.
 *
 * @param n - Integer whose digits to count.
 * @param bIn - Radix of the expansion.
 * @returns A map from each digit to its occurrence count.
 * @see SymPy `sympy.ntheory.digits.count_digits`
 * @example
 * ```ts
 * import { countDigits } from '@symjs/symjs';
 *
 * countDigits(1111339); // => {1: 4, 3: 2, 9: 1}
 * ```
 */
export function countDigits(n: IntLike, bIn: IntLike = 10): Map<bigint, bigint> {
  const b = asInt(bIn);
  const ds = digits(n, b);
  const rv = new Map<bigint, bigint>();
  for (const d of ds.slice(1)) rv.set(d, (rv.get(d) ?? 0n) + 1n);
  return rv;
}

/**
 * Tests whether an integer's digits in the given base or the elements of a sequence read the
 * same forwards and backwards.
 *
 * @see SymPy `sympy.ntheory.digits.is_palindromic`
 * @see SymPy `sympy.utilities.iterables.is_palindromic`
 */
export { isPalindromic } from '../utilities/iterables';
