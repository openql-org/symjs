// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/utilities/memoization.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's memoized recurrences: `recurrence_memo` (a sequence each of
 * whose terms is computed from the earlier ones) and `assoc_recurrence_memo`
 * (a triangle of sequences, each row from a base sequence and the earlier
 * rows).
 */

import { at } from '../core/guard';

/** A memoized sequence (SymPy's function decorated by `recurrence_memo`). */
export interface RecurrenceMemo<T> {
  /** The n-th term, computed with the earlier ones and remembered. */
  (n: number): T;
  /** The number of terms computed so far (SymPy `cache_length`). */
  cacheLength(): number;
  /** The i-th computed term (SymPy `fetch_item(i)`). */
  fetchItem(i: number): T;
  /** The computed terms from start up to stop, excluded (SymPy `fetch_item(slice(start, stop))`). */
  fetchItem(start: number, stop: number): T[];
}

/**
 * Memoizes the recurrence `f(n, prev)`,
 * where `prev` holds the terms 0 .., n - 1 (the first ones are `initial`).
 *
 * @param initial - The already known terms, starting at index zero.
 * @returns A decorator caching previously computed recurrence values.
 * @see SymPy `sympy.utilities.memoization.recurrence_memo`
 * @example
 * ```ts
 * import { recurrenceMemo } from '@symjs/symjs';
 * recurrenceMemo([1])((n, prev) => n * prev[n - 1])(4); // => 24
 * ```
 */
export function recurrenceMemo<T>(initial: readonly T[]): (f: (n: number, prev: readonly T[]) => T) => RecurrenceMemo<T> {
  const cache = [...initial];
  return (f) => {
    const g = (n: number): T => {
      if (n < cache.length) return at(cache, n);
      for (let i = cache.length; i <= n; i++) cache.push(f(i, cache));
      return at(cache, cache.length - 1);
    };
    function fetchItem(i: number): T;
    function fetchItem(start: number, stop: number): T[];
    function fetchItem(start: number, stop?: number): T | T[] {
      return stop === undefined ? at(cache, start) : cache.slice(start, stop);
    }
    return Object.assign(g, { cacheLength: (): number => cache.length, fetchItem });
  };
}

/**
 * Memoizes the triangle `F(n, m)`
 * (0 <= m <= n) whose rows start with `baseSeq(n)` and continue with
 * `f(n, m, rows)`, where `rows` holds the rows computed so far (the row
 * being built last).
 *
 * @param baseSeq - The function giving the first entry of each row.
 * @returns A decorator caching previously computed recurrence values.
 * @see SymPy `sympy.utilities.memoization.assoc_recurrence_memo`
 */
export function assocRecurrenceMemo<T>(baseSeq: (n: number) => T): (f: (n: number, m: number, rows: readonly (readonly T[])[]) => T) => (n: number, m: number) => T {
  const cache: T[][] = [];
  return (f) => (n, m) => {
    for (let i = cache.length; i <= n; i++) {
      const row = [baseSeq(i)];
      cache.push(row);
      // only m <= n is defined
      for (let j = 1; j <= i; j++) row.push(f(i, j, cache));
    }
    return at(at(cache, n), m);
  };
}
