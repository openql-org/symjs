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
 * SymPy Subset(subset, superset): a subset of a superset (both given as
 * lists), with its ranks and neighbours in binary, lexicographic and Gray
 * code order.
 */
export class Subset<T = unknown> {
  readonly #subset: readonly T[];
  readonly #superset: readonly T[];
  #rankBinary: bigint | undefined;
  #rankLex: bigint | undefined;
  #rankGray: bigint | undefined;

  constructor(subset: readonly T[], superset: readonly T[]) {
    if (subset.length > superset.length) throw new RangeError('Invalid arguments have been provided. The superset must be larger than the subset.');
    const keys = new Set(superset.map(elementKey));
    for (const elem of subset) {
      if (!keys.has(elementKey(elem))) throw new RangeError(`The superset provided is invalid as it does not contain the element ${String(elem)}`);
    }
    this.#subset = subset;
    this.#superset = superset;
  }

  /** SymPy a == b: the same subset and superset. */
  equals(other: Subset<T>): boolean {
    const same = (a: readonly T[], b: readonly T[]) => a.length === b.length && a.every((x, i) => elementKey(x) === elementKey(b[i]));
    return same(this.#subset, other.#subset) && same(this.#superset, other.#superset);
  }

  /** SymPy iterate_binary(k): the subset k steps further in binary order. */
  iterateBinary(k: number | bigint): Subset<T> {
    const binList = Subset.bitlistFromSubset(this.#subset, this.#superset);
    const card = this.cardinality;
    const n = (((BigInt(`0b0${binList}`) + BigInt(k)) % card) + card) % card;
    const bits = n.toString(2).padStart(this.supersetSize, '0');
    return Subset.subsetFromBitlist(this.#superset, bits);
  }

  /** SymPy next_binary(): the next subset in binary order. */
  nextBinary(): Subset<T> {
    return this.iterateBinary(1);
  }

  /** SymPy prev_binary(): the previous subset in binary order. */
  prevBinary(): Subset<T> {
    return this.iterateBinary(-1);
  }

  /** SymPy next_lexicographic(): the next subset in lexicographic order. */
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

  /** SymPy prev_lexicographic(): the previous subset in lexicographic order. */
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

  /** SymPy iterate_graycode(k): the subset k steps further in Gray code order. */
  iterateGraycode(k: number | bigint): Subset<T> {
    const card = this.cardinality;
    const unranked = GrayCode.unrank(this.supersetSize, (((this.rankGray + BigInt(k)) % card) + card) % card);
    return Subset.subsetFromBitlist(this.#superset, unranked);
  }

  /** SymPy next_gray(): the next subset in Gray code order. */
  nextGray(): Subset<T> {
    return this.iterateGraycode(1);
  }

  /** SymPy prev_gray(): the previous subset in Gray code order. */
  prevGray(): Subset<T> {
    return this.iterateGraycode(-1);
  }

  /** SymPy rank_binary: the rank in binary order. */
  get rankBinary(): bigint {
    this.#rankBinary ??= BigInt(`0b0${Subset.bitlistFromSubset(this.#subset, this.#superset)}`);
    return this.#rankBinary;
  }

  /** SymPy rank_lexicographic: the rank in lexicographic order. */
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

  /** SymPy rank_gray: the rank in Gray code order. */
  get rankGray(): bigint {
    if (this.#rankGray === undefined) {
      const bits = Subset.bitlistFromSubset(this.#subset, this.#superset);
      this.#rankGray = new GrayCode(bits.length, { start: bits }).rank;
    }
    return this.#rankGray;
  }

  /** SymPy subset: the elements of the subset. */
  get subset(): T[] {
    return [...this.#subset];
  }

  /** SymPy size: the number of elements of the subset. */
  get size(): number {
    return this.#subset.length;
  }

  /** SymPy superset: the elements of the superset. */
  get superset(): T[] {
    return [...this.#superset];
  }

  /** SymPy superset_size: the number of elements of the superset. */
  get supersetSize(): number {
    return this.#superset.length;
  }

  /** SymPy cardinality: the number of subsets of the superset. */
  get cardinality(): bigint {
    return 1n << BigInt(this.supersetSize);
  }

  /** SymPy Subset.subset_from_bitlist(super_set, bitlist): the subset of the elements whose bit is 1. */
  static subsetFromBitlist<U>(superSet: readonly U[], bitlist: string): Subset<U> {
    if (superSet.length !== bitlist.length) throw new RangeError('The sizes of the lists are not equal');
    return new Subset(
      superSet.filter((_x, i) => bitlist[i] === '1'),
      superSet,
    );
  }

  /** SymPy Subset.bitlist_from_subset(subset, superset): the bit string of a subset. */
  static bitlistFromSubset<U>(subsetIn: readonly U[] | Subset<U>, superset: readonly U[]): string {
    const subset = subsetIn instanceof Subset ? subsetIn.subset : subsetIn;
    const bitlist = superset.map(() => '0');
    for (const i of Subset.subsetIndices(subset, superset)) bitlist[i] = '1';
    return bitlist.join('');
  }

  /** SymPy Subset.unrank_binary(rank, superset): the subset of the given rank in binary order. */
  static unrankBinary<U>(rank: number | bigint, superset: readonly U[]): Subset<U> {
    return Subset.subsetFromBitlist(superset, BigInt(rank).toString(2).padStart(superset.length, '0'));
  }

  /** SymPy Subset.unrank_gray(rank, superset): the subset of the given rank in Gray code order. */
  static unrankGray<U>(rank: number | bigint, superset: readonly U[]): Subset<U> {
    return Subset.subsetFromBitlist(superset, GrayCode.unrank(superset.length, rank));
  }

  /**
   * SymPy Subset.subset_indices(subset, superset): the indices of the
   * elements of subset in superset, or [] when some element is not in
   * superset.
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

  /** The subset and superset, as SymPy's repr shows the object. */
  toString(): string {
    return `Subset([${this.#subset.map(String).join(', ')}], [${this.#superset.map(String).join(', ')}])`;
  }
}

/** SymPy ksubsets(superset, k): the subsets of k elements in lexicographic order. */
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
