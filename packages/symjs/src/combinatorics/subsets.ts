// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/subsets.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.subsets: subsets of a superset in binary,
 * lexicographic and Gray code order.
 */

import { Expr } from '../core/nodes';
import { sympify } from '../core/ops';
import { at, getOrThrow } from '../core/guard';
import { GrayCode } from './graycode';

/** A hashable identity of an element (Python equality: 1 == Integer(1), expressions compare structurally). */
function elementKey(v: unknown): string {
  if (v instanceof Expr) return `e:${v.key}`;
  if (typeof v === 'number' || typeof v === 'bigint') return `e:${sympify(v).key}`;
  return `${typeof v}:${String(v)}`;
}

/**
 * A subset of a superset (both given as
 * lists), with its ranks and neighbours in binary, lexicographic and Gray
 * code order.
 * @see SymPy `sympy.combinatorics.subsets.Subset`
 * @example
 * ```ts
 * import { Subset } from '@symjs/symjs';
 * new Subset([], ['a', 'b', 'c', 'd']).rankBinary; // => 0
 * ```
 */
export class Subset<T = unknown> {
  readonly #subset: readonly T[];
  readonly #superset: readonly T[];
  #rankBinary: bigint | undefined;
  #rankLex: bigint | undefined;
  #rankGray: bigint | undefined;

  /**
   * Constructs a `Subset`.
   * @param subset - The selected elements.
   * @param superset - The ordered set from which the subset is drawn.
   * @throws RangeError when the proposed subset is larger than the superset or the proposed subset contains an element outside the superset.
   */
  constructor(subset: readonly T[], superset: readonly T[]) {
    if (subset.length > superset.length) throw new RangeError('Invalid arguments have been provided. The superset must be larger than the subset.');
    const keys = new Set(superset.map(elementKey));
    for (const elem of subset) {
      if (!keys.has(elementKey(elem))) throw new RangeError(`The superset provided is invalid as it does not contain the element ${String(elem)}`);
    }
    this.#subset = subset;
    this.#superset = superset;
  }

  /**
   * The same subset and superset.
   * @param other - The value to combine with or compare against.
   * @returns The result of the comparison.
   */
  equals(other: Subset<T>): boolean {
    const same = (a: readonly T[], b: readonly T[]) => a.length === b.length && a.every((x, i) => elementKey(x) === elementKey(b[i]));
    return same(this.#subset, other.#subset) && same(this.#superset, other.#superset);
  }

  /**
   * The subset k steps further in binary order.
   * @param k - The signed number of steps in the enumeration.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.iterate_binary`
   */
  iterateBinary(k: number | bigint): Subset<T> {
    const binList = Subset.bitlistFromSubset(this.#subset, this.#superset);
    const card = this.cardinality;
    const n = (((BigInt(`0b0${binList}`) + BigInt(k)) % card) + card) % card;
    const bits = n.toString(2).padStart(this.supersetSize, '0');
    return Subset.subsetFromBitlist(this.#superset, bits);
  }

  /**
   * The next subset in binary order.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.next_binary`
   */
  nextBinary(): Subset<T> {
    return this.iterateBinary(1);
  }

  /**
   * The previous subset in binary order.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.prev_binary`
   */
  prevBinary(): Subset<T> {
    return this.iterateBinary(-1);
  }

  /**
   * The next subset in lexicographic order.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.next_lexicographic`
   */
  nextLexicographic(): Subset<T> {
    let i = this.supersetSize - 1;
    const indices = Subset.subsetIndices(this.#subset, this.#superset);
    const remove = (v: number) => indices.splice(indices.indexOf(v), 1);
    if (indices.includes(i)) {
      if (indices.includes(i - 1)) remove(i - 1);
      else {
        remove(i);
        i--;
        while (i >= 0 && !indices.includes(i)) i--;
        if (i >= 0) {
          remove(i);
          indices.push(i + 1);
        }
      }
    } else {
      while (!indices.includes(i) && i >= 0) i--;
      indices.push(i + 1);
    }
    return new Subset(
      indices.map((j) => at(this.#superset, j)),
      this.#superset,
    );
  }

  /**
   * The previous subset in lexicographic order.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.prev_lexicographic`
   */
  prevLexicographic(): Subset<T> {
    let i = this.supersetSize - 1;
    const indices = Subset.subsetIndices(this.#subset, this.#superset);
    const remove = (v: number) => indices.splice(indices.indexOf(v), 1);
    while (i >= 0 && !indices.includes(i)) i--;
    if (i === 0 || indices.includes(i - 1)) remove(i);
    else {
      if (i >= 0) {
        remove(i);
        indices.push(i - 1);
      }
      indices.push(this.supersetSize - 1);
    }
    return new Subset(
      indices.map((j) => at(this.#superset, j)),
      this.#superset,
    );
  }

  /**
   * The subset k steps further in Gray code order.
   * @param k - The signed number of steps in the enumeration.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.iterate_graycode`
   */
  iterateGraycode(k: number | bigint): Subset<T> {
    const card = this.cardinality;
    const unranked = GrayCode.unrank(this.supersetSize, (((this.rankGray + BigInt(k)) % card) + card) % card);
    return Subset.subsetFromBitlist(this.#superset, unranked);
  }

  /**
   * The next subset in Gray code order.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.next_gray`
   */
  nextGray(): Subset<T> {
    return this.iterateGraycode(1);
  }

  /**
   * The previous subset in Gray code order.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.prev_gray`
   */
  prevGray(): Subset<T> {
    return this.iterateGraycode(-1);
  }

  /**
   * Gets the rank in binary order.
   * @returns The rank in binary order.
   * @see SymPy `sympy.combinatorics.subsets.Subset.rank_binary`
   */
  get rankBinary(): bigint {
    this.#rankBinary ??= BigInt(`0b0${Subset.bitlistFromSubset(this.#subset, this.#superset)}`);
    return this.#rankBinary;
  }

  /**
   * Gets the rank in lexicographic order.
   * @returns The rank in lexicographic order.
   * @see SymPy `sympy.combinatorics.subsets.Subset.rank_lexicographic`
   */
  get rankLexicographic(): bigint {
    if (this.#rankLex === undefined) {
      const indices = Subset.subsetIndices(this.#subset, this.#superset);
      const n = this.supersetSize;
      let rank = 0n;
      for (let i = 0; indices.length && i <= n; i++) {
        const k = indices.indexOf(i);
        if (k >= 0) {
          indices.splice(k, 1);
          rank += 1n;
        } else rank += 1n << BigInt(n - i - 1);
      }
      this.#rankLex = rank;
    }
    return this.#rankLex;
  }

  /**
   * Gets the rank in Gray code order.
   * @returns The rank in Gray code order.
   * @see SymPy `sympy.combinatorics.subsets.Subset.rank_gray`
   */
  get rankGray(): bigint {
    if (this.#rankGray === undefined) {
      const bits = Subset.bitlistFromSubset(this.#subset, this.#superset);
      this.#rankGray = new GrayCode(bits.length, { start: bits }).rank;
    }
    return this.#rankGray;
  }

  /**
   * Gets the elements of the subset.
   * @returns The elements of the subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.subset`
   */
  get subset(): T[] {
    return [...this.#subset];
  }

  /**
   * The number of elements of the subset.
   * @returns The size of the object.
   * @see SymPy `sympy.combinatorics.subsets.Subset.size`
   */
  get size(): number {
    return this.#subset.length;
  }

  /**
   * Gets the elements of the superset.
   * @returns The elements of the superset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.superset`
   */
  get superset(): T[] {
    return [...this.#superset];
  }

  /**
   * Gets the number of elements of the superset.
   * @returns The number of elements of the superset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.superset_size`
   */
  get supersetSize(): number {
    return this.#superset.length;
  }

  /**
   * Gets the number of subsets of the superset.
   * @returns The number of subsets of the superset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.cardinality`
   */
  get cardinality(): bigint {
    return 1n << BigInt(this.supersetSize);
  }

  /**
   * The subset of the elements whose bit is 1.
   * @param superSet - The ordered set from which the subset is drawn.
   * @param bitlist - The membership bits in superset order.
   * @returns The resulting subset.
   * @throws RangeError when the operand sizes differ.
   * @see SymPy `sympy.combinatorics.subsets.Subset.subset_from_bitlist`
   */
  static subsetFromBitlist<U>(superSet: readonly U[], bitlist: string): Subset<U> {
    if (superSet.length !== bitlist.length) throw new RangeError('The sizes of the lists are not equal');
    return new Subset(
      superSet.filter((_x, i) => bitlist[i] === '1'),
      superSet,
    );
  }

  /**
   * The bit string of a subset.
   * @param subsetIn - The selected elements.
   * @param superset - The ordered set from which the subset is drawn.
   * @returns The formatted text.
   * @see SymPy `sympy.combinatorics.subsets.Subset.bitlist_from_subset`
   */
  static bitlistFromSubset<U>(subsetIn: readonly U[] | Subset<U>, superset: readonly U[]): string {
    const subset = subsetIn instanceof Subset ? subsetIn.subset : subsetIn;
    const bitlist = superset.map(() => '0');
    for (const i of Subset.subsetIndices(subset, superset)) bitlist[i] = '1';
    return bitlist.join('');
  }

  /**
   * The subset of the given rank in binary order.
   * @param rank - The zero-based position in the enumeration.
   * @param superset - The ordered set from which the subset is drawn.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.unrank_binary`
   * @example
   * ```ts
   * import { Subset } from '@symjs/symjs';
   * Subset.unrankBinary(3, [1, 2, 3]).subset; // => [2, 3]
   * ```
   */
  static unrankBinary<U>(rank: number | bigint, superset: readonly U[]): Subset<U> {
    return Subset.subsetFromBitlist(superset, BigInt(rank).toString(2).padStart(superset.length, '0'));
  }

  /**
   * The subset of the given rank in Gray code order.
   * @param rank - The zero-based position in the enumeration.
   * @param superset - The ordered set from which the subset is drawn.
   * @returns The resulting subset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.unrank_gray`
   */
  static unrankGray<U>(rank: number | bigint, superset: readonly U[]): Subset<U> {
    return Subset.subsetFromBitlist(superset, GrayCode.unrank(superset.length, rank));
  }

  /**
   * The indices of the
   * elements of subset in superset, or [] when some element is not in
   * superset.
   * @param subset - The selected elements.
   * @param superset - The ordered set from which the subset is drawn.
   * @returns The indices of the elements of subset in superset.
   * @see SymPy `sympy.combinatorics.subsets.Subset.subset_indices`
   */
  static subsetIndices(subset: readonly unknown[], superset: readonly unknown[]): number[] {
    const sb = new Set(subset.map(elementKey));
    const d = new Map<string, number>();
    for (const [i, ai] of superset.entries()) {
      const k = elementKey(ai);
      if (sb.has(k)) {
        d.set(k, i);
        sb.delete(k);
        if (!sb.size) return subset.map((bi) => getOrThrow(d, elementKey(bi)));
      }
    }
    return [];
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return `Subset([${this.#subset.map(String).join(', ')}], [${this.#superset.map(String).join(', ')}])`;
  }
}

/**
 * The subsets of k elements in lexicographic order.
 * @param superset - The ordered set from which the subset is drawn.
 * @param k - The subset size.
 * @returns An iterator over the successive subsets.
 * @see SymPy `sympy.combinatorics.subsets.ksubsets`
 * @example
 * ```ts
 * import { ksubsets } from '@symjs/symjs';
 * Array.from(ksubsets([1, 2, 3], 2)); // => [[1, 2], [1, 3], [2, 3]]
 * ```
 */
export function* ksubsets<T>(superset: readonly T[], k: number): Generator<T[]> {
  const n = superset.length;
  if (k > n || k < 0) return;
  const idx = [...Array(k).keys()];
  for (;;) {
    yield idx.map((i) => at(superset, i));
    let i = k - 1;
    while (i >= 0 && at(idx, i) === i + n - k) i--;
    if (i < 0) return;
    idx[i] = at(idx, i) + 1;
    for (let j = i + 1; j < k; j++) idx[j] = at(idx, j - 1) + 1;
  }
}
