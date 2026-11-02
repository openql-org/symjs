// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Digits of integers (SymPy sympy.ntheory.digits): digits,
 * count_digits and is_palindromic.
 */

import type { IntLike } from './intutil';
import { asInt, babs } from './intutil';
import { isPalindromic as sequenceIsPalindromic } from '../utilities/iterables';

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

function isSequenceArg<T>(n: IntLike | readonly T[] | string): n is readonly T[] | string {
  return typeof n === 'string' || Array.isArray(n);
}

/** n reads the same forwards and backwards in base b (SymPy is_palindromic). */
export function isPalindromic(n: IntLike, b?: IntLike): boolean;
/** A sequence (array or string) reads the same backwards, optionally s[i:j] (SymPy utilities.iterables.is_palindromic). */
export function isPalindromic<T>(s: readonly T[] | string, i?: number, j?: number): boolean;
export function isPalindromic<T>(n: IntLike | readonly T[] | string, b?: IntLike, j?: number): boolean {
  if (isSequenceArg(n)) return sequenceIsPalindromic(n, b === undefined ? 0 : Number(b), j);
  const ds = digits(n, b ?? 10).slice(1);
  for (let i = 0, k = ds.length - 1; i < k; i++, k--) if (ds[i] !== ds[k]) return false;
  return true;
}
