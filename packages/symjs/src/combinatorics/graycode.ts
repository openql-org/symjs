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
  start?: string;
  rank?: number | bigint;
}

/**
 * SymPy GrayCode(n, start=..., rank=...): the n-bit binary reflected Gray
 * code, a Hamiltonian walk on the n-dimensional cube, positioned at a bit
 * string (default '0...0').
 */
export class GrayCode {
  readonly n: number;
  #current: string | bigint = 0n;
  #rank: bigint | undefined;
  #skip = false;

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

  /** SymPy next(delta=1): the Gray code delta steps further in canonical order. */
  next(delta: number | bigint = 1): GrayCode {
    return new GrayCode(this.n, { rank: (this.rank + BigInt(delta)) % this.selections });
  }

  /** SymPy selections: the number of bit strings of the code (2**n). */
  get selections(): bigint {
    return 1n << BigInt(this.n);
  }

  /**
   * SymPy generate_gray(start=..., rank=...): the bit strings from the
   * current one (or the given start) to the end of the code.
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

  /** SymPy skip(): the next bit string of generate_gray is not produced. */
  skip(): void {
    this.#skip = true;
  }

  /** SymPy rank: the position of the current bit string in the code. */
  get rank(): bigint {
    this.#rank ??= BigInt(`0b${grayToBin(this.current)}`);
    return this.#rank;
  }

  /** SymPy current: the current bit string. */
  get current(): string {
    const rv = typeof this.#current === 'string' ? this.#current || '0' : this.#current.toString(2);
    return rv.padStart(this.n, '0');
  }

  /** SymPy GrayCode.unrank(n, rank): the n-bit Gray code of the given rank. */
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

  /** SymPy str: GrayCode(3). */
  toString(): string {
    return `GrayCode(${this.n})`;
  }
}

/** SymPy random_bitstring(n): a random bit string of length n. */
export function randomBitstring(n: number): string {
  let s = '';
  for (let i = 0; i < n; i++) s += Math.random() < 0.5 ? '0' : '1';
  return s;
}

/** SymPy gray_to_bin(bin_list): the binary code of a Gray code (big endian). */
export function grayToBin(binList: string): string {
  let b = binList.slice(0, 1);
  for (let i = 1; i < binList.length; i++) b += at(b, i - 1) !== at(binList, i) ? '1' : '0';
  return b;
}

/** SymPy bin_to_gray(bin_list): the Gray code of a binary code (big endian). */
export function binToGray(binList: string): string {
  let b = binList.slice(0, 1);
  for (let i = 1; i < binList.length; i++) b += at(binList, i) === at(binList, i - 1) ? '0' : '1';
  return b;
}

/** SymPy get_subset_from_bitstring(super_set, bitstring): the elements whose bit is 1. */
export function getSubsetFromBitstring<T>(superSet: readonly T[], bitstring: string): T[] {
  if (superSet.length !== bitstring.length) throw new RangeError('The sizes of the lists are not equal');
  return superSet.filter((_x, i) => bitstring[i] === '1');
}

/** SymPy graycode_subsets(gray_code_set): the subsets in the order of the Gray code. */
export function* graycodeSubsets<T>(grayCodeSet: readonly T[]): Generator<T[]> {
  for (const bitstring of [...new GrayCode(grayCodeSet.length).generateGray()]) yield getSubsetFromBitstring(grayCodeSet, bitstring);
}
