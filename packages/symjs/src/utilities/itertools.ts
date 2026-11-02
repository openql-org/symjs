// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Ports of Python's `itertools` generators used by the iterable
 * utilities, yielding in the same order as Python.
 */

import { at } from '../core/guard';

/** Python `itertools.permutations(pool, r)`. */
export function* permutations<T>(iterable: Iterable<T>, r?: number | null): Generator<T[], void, undefined> {
  const pool = [...iterable];
  const n = pool.length;
  const k = r ?? n;
  if (k > n || k < 0) return;
  const indices = Array.from({ length: n }, (_, i) => i);
  const cycles = Array.from({ length: k }, (_, i) => n - i);
  yield indices.slice(0, k).map((i) => at(pool, i));
  for (;;) {
    let i = k - 1;
    for (; i >= 0; i--) {
      const j = at(cycles, i) - 1;
      cycles[i] = j;
      if (j === 0) {
        indices.push(...indices.splice(i, 1));
        cycles[i] = n - i;
      } else {
        const a = at(indices, i);
        indices[i] = at(indices, n - j);
        indices[n - j] = a;
        yield indices.slice(0, k).map((t) => at(pool, t));
        break;
      }
    }
    if (i < 0) return;
  }
}

/** Python `itertools.combinations(pool, r)`. */
export function* combinations<T>(iterable: Iterable<T>, r: number): Generator<T[], void, undefined> {
  const pool = [...iterable];
  const n = pool.length;
  if (r > n || r < 0) return;
  const indices = Array.from({ length: r }, (_, i) => i);
  yield indices.map((i) => at(pool, i));
  for (;;) {
    let i = r - 1;
    while (i >= 0 && indices[i] === i + n - r) i--;
    if (i < 0) return;
    let v = at(indices, i);
    for (let j = i; j < r; j++) indices[j] = ++v;
    yield indices.map((t) => at(pool, t));
  }
}

/** Python `itertools.combinations_with_replacement(pool, r)`. */
export function* combinationsWithReplacement<T>(iterable: Iterable<T>, r: number): Generator<T[], void, undefined> {
  const pool = [...iterable];
  const n = pool.length;
  if (r < 0 || (n === 0 && r > 0)) return;
  const indices: number[] = new Array<number>(r).fill(0);
  yield indices.map((i) => at(pool, i));
  for (;;) {
    let i = r - 1;
    while (i >= 0 && indices[i] === n - 1) i--;
    if (i < 0) return;
    const v = at(indices, i) + 1;
    for (let j = i; j < r; j++) indices[j] = v;
    yield indices.map((t) => at(pool, t));
  }
}

/** Python `itertools.product(*pools)`: the last pool varies fastest. */
export function* product<T>(pools: readonly (readonly T[])[]): Generator<T[], void, undefined> {
  if (pools.some((p) => p.length === 0)) return;
  const idx: number[] = new Array<number>(pools.length).fill(0);
  for (;;) {
    yield idx.map((i, j) => at(at(pools, j), i));
    let j = pools.length - 1;
    while (j >= 0) {
      const v = at(idx, j) + 1;
      idx[j] = v;
      if (v < at(pools, j).length) break;
      idx[j] = 0;
      j--;
    }
    if (j < 0) return;
  }
}
