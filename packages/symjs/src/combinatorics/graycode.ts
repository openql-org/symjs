// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/graycode.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.graycode: binary reflected Gray codes.
 */

import { at } from '../core/guard';

/** Options of {@link GrayCode}: the starting bit string or the starting rank. */
export interface GrayCodeOptions {
  /** The initial Gray codeword. */
  start?: string;
  /** The starting rank in reflected Gray order. */
  rank?: number | bigint;
}

/**
 * The n-bit binary reflected Gray
 * code, a Hamiltonian walk on the n-dimensional cube, positioned at a bit
 * string (default '0...0').
 * @see SymPy `sympy.combinatorics.graycode.GrayCode`
 * @example
 * ```ts
 * import { GrayCode } from '@symjs/symjs';
 * GrayCode.unrank(5, 3); // => 00010
 * ```
 */
export class GrayCode {
  /**
   * Returns the dimension of the Gray code.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.n`
   */
  readonly n: number;
  #current: string | bigint = 0n;
  #rank: bigint | undefined;
  #skip = false;

  /**
   * Constructs a `GrayCode`.
   * @param n - The number of bits.
   * @param opts - The settings described by {@link GrayCodeOptions}.
   * @throws RangeError when the bit width is not a positive integer or the starting string exceeds the bit width.
   */
  constructor(n: number, opts: GrayCodeOptions = {}) {
    if (n < 1 || !Number.isInteger(n)) throw new RangeError(`Gray code dimension must be a positive integer, not ${n}`);
    this.n = n;
    if (opts.start !== undefined) {
      if (opts.start.length > n) throw new RangeError(`Gray code start has length ${opts.start.length} but should not be greater than ${n}`);
      this.#current = opts.start;
    } else if (opts.rank !== undefined) {
      const sel = this.selections;
      this.#rank = ((BigInt(opts.rank) % sel) + sel) % sel;
      this.#current = GrayCode.unrank(n, this.#rank);
    }
  }

  /**
   * Returns the Gray code delta steps further in canonical order.
   * @param delta - The signed number of codewords to advance.
   * @returns The Gray code delta steps further in canonical order.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.next`
   */
  next(delta: number | bigint = 1): GrayCode {
    return new GrayCode(this.n, { rank: (this.rank + BigInt(delta)) % this.selections });
  }

  /**
   * Gets the number of bit strings of the code (2**n).
   * @returns The number of bit strings of the code (2**n).
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.selections`
   */
  get selections(): bigint {
    return 1n << BigInt(this.n);
  }

  /**
   * The bit strings from the
   * current one (or the given start) to the end of the code.
   * @param hints - The settings in {@link GrayCodeOptions}.
   * @returns An iterator over successive codewords.
   * @throws RangeError when the starting string exceeds the bit width.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.generate_gray`
   * @example
   * ```ts
   * import { GrayCode } from '@symjs/symjs';
   * Array.from(new GrayCode(3).generateGray()); // => [000, 001, 011, 010, 110, 111, 101, 100]
   * ```
   */
  *generateGray(hints: GrayCodeOptions = {}): Generator<string> {
    const bits = this.n;
    let start: string | undefined;
    if (hints.start !== undefined) start = hints.start;
    else if (hints.rank !== undefined) start = GrayCode.unrank(this.n, hints.rank);
    if (start !== undefined) this.#current = start;
    const current = this.current;
    const graycodeBin = grayToBin(current);
    if (graycodeBin.length > this.n) throw new RangeError(`Gray code start has length ${graycodeBin.length} but should not be greater than ${bits}`);
    this.#current = BigInt(`0b${current}`);
    const graycodeInt = BigInt(`0b${graycodeBin}`);
    for (let i = graycodeInt; i < 1n << BigInt(bits); i++) {
      if (this.#skip) this.#skip = false;
      else yield this.current;
      const bbtc = i ^ (i + 1n);
      const gbtc = bbtc ^ (bbtc >> 1n);
      this.#current = BigInt(this.#current) ^ gbtc;
    }
    this.#current = 0n;
  }

  /**
   * The next bit string of generate_gray is not produced.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.skip`
   */
  skip(): void {
    this.#skip = true;
  }

  /**
   * Gets the position of the current bit string in the code.
   * @returns The position of the current bit string in the code.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.rank`
   */
  get rank(): bigint {
    this.#rank ??= BigInt(`0b${grayToBin(this.current)}`);
    return this.#rank;
  }

  /**
   * Gets the current bit string.
   * @returns The current bit string.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.current`
   */
  get current(): string {
    const rv = typeof this.#current === 'string' ? this.#current || '0' : this.#current.toString(2);
    return rv.padStart(this.n, '0');
  }

  /**
   * The n-bit Gray code of the given rank.
   * @param n - The number of bits.
   * @param rank - The zero-based position in the enumeration.
   * @returns The formatted text.
   * @see SymPy `sympy.combinatorics.graycode.GrayCode.unrank`
   */
  static unrank(n: number, rank: number | bigint): string {
    let out = '';
    let k = BigInt(rank);
    for (let m = n; m > 1; m--) {
      const half = 1n << BigInt(m - 1);
      if (k < half) out += '0';
      else {
        out += '1';
        k = half - (k % half) - 1n;
      }
    }
    return out + String(k % 2n);
  }

  /**
   * Formats the Gray code by its dimension.
   * @returns The printable representation.
   */
  toString(): string {
    return `GrayCode(${this.n})`;
  }
}

/**
 * A random bit string of length n.
 * @param n - The number of bits.
 * @returns The formatted text.
 * @see SymPy `sympy.combinatorics.graycode.random_bitstring`
 * @example
 * ```ts
 * import { randomBitstring } from '@symjs/symjs';
 * randomBitstring(3).length; // => 3
 * ```
 */
export function randomBitstring(n: number): string {
  let s = '';
  for (let i = 0; i < n; i++) s += Math.random() < 0.5 ? '0' : '1';
  return s;
}

/**
 * Converts a reflected Gray codeword to its binary representation.
 * @param binList - The bit string to convert, most significant bit first.
 * @returns The resulting text.
 * @see SymPy `sympy.combinatorics.graycode.gray_to_bin`
 * @example
 * ```ts
 * import { grayToBin } from '@symjs/symjs';
 * grayToBin('100'); // => 111
 * ```
 */
export function grayToBin(binList: string): string {
  let b = binList.slice(0, 1);
  for (let i = 1; i < binList.length; i++) b += at(b, i - 1) !== at(binList, i) ? '1' : '0';
  return b;
}

/**
 * Converts a binary word to its reflected Gray codeword.
 * @param binList - The bit string to convert, most significant bit first.
 * @returns The resulting text.
 * @see SymPy `sympy.combinatorics.graycode.bin_to_gray`
 * @example
 * ```ts
 * import { binToGray } from '@symjs/symjs';
 * binToGray('111'); // => 100
 * ```
 */
export function binToGray(binList: string): string {
  let b = binList.slice(0, 1);
  for (let i = 1; i < binList.length; i++) b += at(binList, i) === at(binList, i - 1) ? '0' : '1';
  return b;
}

/**
 * Returns the elements whose bit is 1.
 * @param superSet - The ordered set from which the subset is drawn.
 * @param bitstring - The membership bits in superset order.
 * @returns The elements whose bit is 1.
 * @throws RangeError when the operand sizes differ.
 * @see SymPy `sympy.combinatorics.graycode.get_subset_from_bitstring`
 * @example
 * ```ts
 * import { getSubsetFromBitstring } from '@symjs/symjs';
 * getSubsetFromBitstring([1, 2, 3, 4], '0011'); // => [3, 4]
 * ```
 */
export function getSubsetFromBitstring<T>(superSet: readonly T[], bitstring: string): T[] {
  if (superSet.length !== bitstring.length) throw new RangeError('The sizes of the lists are not equal');
  return superSet.filter((_x, i) => bitstring[i] === '1');
}

/**
 * The subsets in the order of the Gray code.
 * @param grayCodeSet - The ordered elements whose subsets are enumerated.
 * @returns An iterator over the successive subsets.
 * @see SymPy `sympy.combinatorics.graycode.graycode_subsets`
 * @example
 * ```ts
 * import { graycodeSubsets } from '@symjs/symjs';
 * Array.from(graycodeSubsets([1, 2, 3])); // => [[], [3], [2, 3], [2], [1, 2], [1, 2, 3], [1, 3], [1]]
 * ```
 */
export function* graycodeSubsets<T>(grayCodeSet: readonly T[]): Generator<T[]> {
  for (const bitstring of [...new GrayCode(grayCodeSet.length).generateGray()]) yield getSubsetFromBitstring(grayCodeSet, bitstring);
}
