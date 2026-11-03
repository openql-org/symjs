// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Port of the doctests of sympy.utilities.iterables (SymPy 1.14), plus a
// table of further reference outputs computed with SymPy.

import { describe, expect, it } from 'vitest';
import { Add, Dummy, E, Expr, Sym, add, exp, isRational, mul, pi, pow, sqrt, sub } from '../src';
import * as I from '../src/utilities';
import {
  GeneratorType,
  NotIterable,
  ValueMap,
  binaryPartitions,
  bracelets,
  capture,
  commonPrefix,
  commonSuffix,
  connectedComponents,
  dictMerge,
  filterSymbols,
  flatten,
  generateBell,
  generateDerangements,
  generateInvolutions,
  generateOrientedForest,
  group,
  hasDups,
  hasVariety,
  ibin,
  iproduct,
  isPalindromic,
  isSequence,
  iterable,
  kbins,
  leastRotation,
  minlex,
  multiset,
  multisetCombinations,
  multisetDerangements,
  multisetPartitions,
  multisetPermutations,
  necklaces,
  numberedSymbols,
  orderedPartitions,
  partitions,
  permuteSigns,
  postfixes,
  postorderTraversal,
  prefixes,
  randomDerangement,
  reshape,
  rotateLeft,
  rotateRight,
  rotations,
  roundrobin,
  runs,
  sequencePartitions,
  sequencePartitionsEmpty,
  sift,
  signedPermutations,
  stronglyConnectedComponents,
  subsets,
  take,
  topologicalSort,
  unflatten,
  uniq,
  variations,
} from '../src/utilities';

const [w, x, y, z] = ['w', 'x', 'y', 'z'].map((n) => new Sym(n)) as [Sym, Sym, Sym, Sym];
const str = (v: unknown): unknown => (Array.isArray(v) ? v.map(str) : v instanceof Map ? [...v].map(([k, u]) => [str(k), str(u)]) : v instanceof Set ? new Set([...v].map(str)) : v instanceof Expr ? v.toString() : v);
const list = <T>(g: Iterable<T>): T[] => [...g];
/** Sort by JSON text (what the default sort does with the string form of arrays of numbers and strings). */
const sorted = <T>(xs: T[]): T[] =>
  xs.sort((a, b) => {
    const [p, q] = [JSON.stringify(a), JSON.stringify(b)];
    return p < q ? -1 : p > q ? 1 : 0;
  });
const join = (g: Iterable<readonly string[]>): string[] => [...g].map((p) => p.join(''));

/** Python's itertools.permutations, for the comparisons in the doctests. */
function* perms<T>(xs: readonly T[]): Generator<T[]> {
  if (xs.length === 0) {
    yield [];
    return;
  }
  for (let i = 0; i < xs.length; i++) for (const p of perms([...xs.slice(0, i), ...xs.slice(i + 1)])) yield [xs[i]!, ...p];
}

/** SymPy's iteration order of S.Integers: 0, 1, -1, 2, -2, ... */
function* integers(): Generator<number> {
  yield 0;
  for (let i = 1; ; i++) {
    yield i;
    yield -i;
  }
}

const includes = (g: Iterable<unknown[]>, t: unknown[], limit = 10000): boolean => {
  let n = 0;
  for (const v of g) {
    if (JSON.stringify(v) === JSON.stringify(t)) return true;
    if (++n > limit) return false;
  }
  return false;
};

// reference outputs computed with SymPy 1.14
const REF = {"multisetPartitions": [[[[1, 1, 2, 2, 3], null], [[[1, 1, 2, 2, 3]], [[1, 1, 2, 2], [3]], [[1, 1, 2, 3], [2]], [[1, 1, 2], [2, 3]], [[1, 1, 2], [2], [3]], [[1, 1, 3], [2, 2]], [[1, 1, 3], [2], [2]], [[1, 1], [2, 2, 3]], [[1, 1], [2, 2], [3]], [[1, 1], [2, 3], [2]], [[1, 1], [2], [2], [3]], [[1, 2, 2, 3], [1]], [[1, 2, 2], [1, 3]], [[1, 2, 2], [1], [3]], [[1, 2, 3], [1, 2]], [[1, 2, 3], [1], [2]], [[1, 2], [1, 2], [3]], [[1, 2], [1, 3], [2]], [[1, 2], [1], [2, 3]], [[1, 2], [1], [2], [3]], [[1, 3], [1], [2, 2]], [[1, 3], [1], [2], [2]], [[1], [1], [2, 2, 3]], [[1], [1], [2, 2], [3]], [[1], [1], [2, 3], [2]], [[1], [1], [2], [2], [3]]]], [[[1, 1, 2, 2, 3], 2], [[[1, 1, 2, 2], [3]], [[1, 1, 2, 3], [2]], [[1, 1, 2], [2, 3]], [[1, 1, 3], [2, 2]], [[1, 1], [2, 2, 3]], [[1, 2, 2, 3], [1]], [[1, 2, 2], [1, 3]], [[1, 2, 3], [1, 2]]]], [[[1, 1, 2, 2, 3], 3], [[[1, 1, 2], [2], [3]], [[1, 1, 3], [2], [2]], [[1, 1], [2, 2], [3]], [[1, 1], [2, 3], [2]], [[1, 2, 2], [1], [3]], [[1, 2, 3], [1], [2]], [[1, 2], [1, 2], [3]], [[1, 2], [1, 3], [2]], [[1, 2], [1], [2, 3]], [[1, 3], [1], [2, 2]], [[1], [1], [2, 2, 3]]]], [[["a", "b", "b", "c"], null], [[["a", "b", "b", "c"]], [["a", "b", "b"], ["c"]], [["a", "b", "c"], ["b"]], [["a", "b"], ["b", "c"]], [["a", "b"], ["b"], ["c"]], [["a", "c"], ["b", "b"]], [["a", "c"], ["b"], ["b"]], [["a"], ["b", "b", "c"]], [["a"], ["b", "b"], ["c"]], [["a"], ["b", "c"], ["b"]], [["a"], ["b"], ["b"], ["c"]]]], [[["a", "b", "b", "c"], 2], [[["a", "b", "b"], ["c"]], [["a", "b", "c"], ["b"]], [["a", "b"], ["b", "c"]], [["a", "c"], ["b", "b"]], [["a"], ["b", "b", "c"]]]], [[["a", "b", "b", "c"], 3], [[["a", "b"], ["b"], ["c"]], [["a", "c"], ["b"], ["b"]], [["a"], ["b", "b"], ["c"]], [["a"], ["b", "c"], ["b"]]]], [[[0, 0, 1, 1, 1], null], [[[0, 0, 1, 1, 1]], [[0, 0, 1, 1], [1]], [[0, 0, 1], [1, 1]], [[0, 0, 1], [1], [1]], [[0, 0], [1, 1, 1]], [[0, 0], [1, 1], [1]], [[0, 0], [1], [1], [1]], [[0, 1, 1, 1], [0]], [[0, 1, 1], [0, 1]], [[0, 1, 1], [0], [1]], [[0, 1], [0, 1], [1]], [[0, 1], [0], [1, 1]], [[0, 1], [0], [1], [1]], [[0], [0], [1, 1, 1]], [[0], [0], [1, 1], [1]], [[0], [0], [1], [1], [1]]]], [[[0, 0, 1, 1, 1], 2], [[[0, 0, 1, 1], [1]], [[0, 0, 1], [1, 1]], [[0, 0], [1, 1, 1]], [[0, 1, 1, 1], [0]], [[0, 1, 1], [0, 1]]]], [[[0, 0, 1, 1, 1], 3], [[[0, 0, 1], [1], [1]], [[0, 0], [1, 1], [1]], [[0, 1, 1], [0], [1]], [[0, 1], [0, 1], [1]], [[0, 1], [0], [1, 1]], [[0], [0], [1, 1, 1]]]], [[[], null], [[]]], [[[], 2], []], [[[], 3], []]], "partitions": [[[0, null, null], [[]]], [[0, null, 3], [[]]], [[0, 3, null], [[]]], [[0, 3, 3], [[]]], [[6, null, null], [[[6, 1]], [[5, 1], [1, 1]], [[4, 1], [2, 1]], [[4, 1], [1, 2]], [[3, 2]], [[3, 1], [2, 1], [1, 1]], [[3, 1], [1, 3]], [[2, 3]], [[2, 2], [1, 2]], [[2, 1], [1, 4]], [[1, 6]]]], [[6, null, 3], [[[3, 2]], [[3, 1], [2, 1], [1, 1]], [[3, 1], [1, 3]], [[2, 3]], [[2, 2], [1, 2]], [[2, 1], [1, 4]], [[1, 6]]]], [[6, 3, null], [[[6, 1]], [[5, 1], [1, 1]], [[4, 1], [2, 1]], [[4, 1], [1, 2]], [[3, 2]], [[3, 1], [2, 1], [1, 1]], [[2, 3]]]], [[6, 3, 3], [[[3, 2]], [[3, 1], [2, 1], [1, 1]], [[2, 3]]]], [[7, null, null], [[[7, 1]], [[6, 1], [1, 1]], [[5, 1], [2, 1]], [[5, 1], [1, 2]], [[4, 1], [3, 1]], [[4, 1], [2, 1], [1, 1]], [[4, 1], [1, 3]], [[3, 2], [1, 1]], [[3, 1], [2, 2]], [[3, 1], [2, 1], [1, 2]], [[3, 1], [1, 4]], [[2, 3], [1, 1]], [[2, 2], [1, 3]], [[2, 1], [1, 5]], [[1, 7]]]], [[7, null, 3], [[[3, 2], [1, 1]], [[3, 1], [2, 2]], [[3, 1], [2, 1], [1, 2]], [[3, 1], [1, 4]], [[2, 3], [1, 1]], [[2, 2], [1, 3]], [[2, 1], [1, 5]], [[1, 7]]]], [[7, 3, null], [[[7, 1]], [[6, 1], [1, 1]], [[5, 1], [2, 1]], [[5, 1], [1, 2]], [[4, 1], [3, 1]], [[4, 1], [2, 1], [1, 1]], [[3, 2], [1, 1]], [[3, 1], [2, 2]]]], [[7, 3, 3], [[[3, 2], [1, 1]], [[3, 1], [2, 2]]]]], "orderedPartitions": [[[6, null, true], [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2], [1, 1, 1, 3], [1, 1, 2, 2], [1, 1, 4], [1, 2, 3], [1, 5], [2, 2, 2], [2, 4], [3, 3], [6]]], [[6, null, false], [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2], [1, 1, 1, 3], [1, 1, 2, 2], [1, 1, 4], [1, 2, 3], [1, 5], [2, 2, 2], [2, 4], [3, 3], [6]]], [[6, 2, true], [[1, 5], [2, 4], [3, 3]]], [[6, 2, false], [[1, 5], [3, 3], [2, 4]]], [[6, 3, true], [[1, 1, 4], [1, 2, 3], [2, 2, 2]]], [[6, 3, false], [[2, 2, 2], [1, 2, 3], [1, 1, 4]]], [[8, null, true], [[1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 3], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 4], [1, 1, 1, 2, 3], [1, 1, 1, 5], [1, 1, 2, 2, 2], [1, 1, 2, 4], [1, 1, 3, 3], [1, 1, 6], [1, 2, 2, 3], [1, 2, 5], [1, 3, 4], [1, 7], [2, 2, 2, 2], [2, 2, 4], [2, 3, 3], [2, 6], [3, 5], [4, 4], [8]]], [[8, null, false], [[1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 2], [1, 1, 1, 1, 1, 3], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 4], [1, 1, 1, 2, 3], [1, 1, 1, 5], [1, 1, 2, 2, 2], [1, 1, 2, 4], [1, 1, 3, 3], [1, 1, 6], [1, 2, 2, 3], [1, 2, 5], [1, 3, 4], [1, 7], [2, 2, 2, 2], [2, 2, 4], [2, 3, 3], [2, 6], [3, 5], [4, 4], [8]]], [[8, 2, true], [[1, 7], [2, 6], [3, 5], [4, 4]]], [[8, 2, false], [[1, 7], [2, 6], [4, 4], [3, 5]]], [[8, 3, true], [[1, 1, 6], [1, 2, 5], [1, 3, 4], [2, 2, 4], [2, 3, 3]]], [[8, 3, false], [[1, 1, 6], [1, 2, 5], [1, 3, 4], [2, 3, 3], [2, 2, 4]]]], "binaryPartitions": [[1, [[1]]], [6, [[4, 2], [4, 1, 1], [2, 2, 2], [2, 2, 1, 1], [2, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]]], [9, [[8, 1], [4, 4, 1], [4, 2, 2, 1], [4, 2, 1, 1, 1], [4, 1, 1, 1, 1, 1], [2, 2, 2, 2, 1], [2, 2, 2, 1, 1, 1], [2, 2, 1, 1, 1, 1, 1], [2, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1]]]], "generateBell": [[1, [[0]]], [2, [[0, 1], [1, 0]]], [3, [[0, 1, 2], [0, 2, 1], [2, 0, 1], [2, 1, 0], [1, 2, 0], [1, 0, 2]]], [4, [[0, 1, 2, 3], [0, 1, 3, 2], [0, 3, 1, 2], [3, 0, 1, 2], [3, 0, 2, 1], [0, 3, 2, 1], [0, 2, 3, 1], [0, 2, 1, 3], [2, 0, 1, 3], [2, 0, 3, 1], [2, 3, 0, 1], [3, 2, 0, 1], [3, 2, 1, 0], [2, 3, 1, 0], [2, 1, 3, 0], [2, 1, 0, 3], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 2, 0], [3, 1, 2, 0], [3, 1, 0, 2], [1, 3, 0, 2], [1, 0, 3, 2], [1, 0, 2, 3]]]], "generateDerangements": [[[0, 1, 2, 3], [[1, 0, 3, 2], [1, 2, 3, 0], [1, 3, 0, 2], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 2, 0, 1], [3, 2, 1, 0]]], [[1, 1, 2, 2], [[2, 2, 1, 1]]], [[1, 1, 2, 3, 4], [[2, 4, 3, 1, 1], [4, 2, 3, 1, 1], [2, 3, 4, 1, 1], [3, 2, 4, 1, 1], [3, 4, 1, 2, 1], [4, 3, 1, 2, 1], [3, 2, 1, 4, 1], [2, 3, 1, 4, 1], [4, 3, 1, 1, 2], [3, 4, 1, 1, 2], [4, 2, 1, 1, 3], [2, 4, 1, 1, 3]]], [[1, 1, 2, 2, 3, 3, 4], [[3, 3, 1, 4, 2, 2, 1], [3, 3, 4, 1, 2, 2, 1], [3, 3, 1, 1, 2, 4, 2], [3, 3, 1, 4, 2, 1, 2], [3, 3, 4, 1, 2, 1, 2], [3, 3, 1, 1, 4, 2, 2], [3, 3, 1, 4, 1, 2, 2], [3, 3, 4, 1, 1, 2, 2], [3, 2, 3, 1, 2, 4, 1], [3, 2, 3, 4, 2, 1, 1], [3, 2, 3, 1, 4, 2, 1], [3, 2, 3, 4, 1, 2, 1], [3, 2, 3, 1, 1, 4, 2], [3, 2, 3, 1, 4, 1, 2], [3, 2, 3, 4, 1, 1, 2], [3, 4, 3, 1, 2, 2, 1], [3, 4, 3, 1, 2, 1, 2], [3, 4, 3, 1, 1, 2, 2], [3, 2, 1, 3, 2, 4, 1], [3, 2, 4, 3, 2, 1, 1], [3, 2, 1, 3, 4, 2, 1], [3, 2, 4, 3, 1, 2, 1], [3, 2, 1, 3, 1, 4, 2], [3, 2, 1, 3, 4, 1, 2], [3, 2, 4, 3, 1, 1, 2], [3, 4, 1, 3, 2, 2, 1], [3, 4, 1, 3, 2, 1, 2], [3, 4, 1, 3, 1, 2, 2], [3, 2, 1, 1, 2, 4, 3], [3, 2, 1, 4, 2, 1, 3], [3, 2, 4, 1, 2, 1, 3], [3, 2, 1, 1, 4, 2, 3], [3, 2, 1, 4, 1, 2, 3], [3, 2, 4, 1, 1, 2, 3], [3, 4, 1, 1, 2, 2, 3], [2, 3, 3, 1, 2, 4, 1], [2, 3, 3, 4, 2, 1, 1], [2, 3, 3, 1, 4, 2, 1], [2, 3, 3, 4, 1, 2, 1], [2, 3, 3, 1, 1, 4, 2], [2, 3, 3, 1, 4, 1, 2], [2, 3, 3, 4, 1, 1, 2], [4, 3, 3, 1, 2, 2, 1], [4, 3, 3, 1, 2, 1, 2], [4, 3, 3, 1, 1, 2, 2], [2, 3, 1, 3, 2, 4, 1], [2, 3, 4, 3, 2, 1, 1], [2, 3, 1, 3, 4, 2, 1], [2, 3, 4, 3, 1, 2, 1], [2, 3, 1, 3, 1, 4, 2], [2, 3, 1, 3, 4, 1, 2], [2, 3, 4, 3, 1, 1, 2], [4, 3, 1, 3, 2, 2, 1], [4, 3, 1, 3, 2, 1, 2], [4, 3, 1, 3, 1, 2, 2], [2, 3, 1, 1, 2, 4, 3], [2, 3, 1, 4, 2, 1, 3], [2, 3, 4, 1, 2, 1, 3], [2, 3, 1, 1, 4, 2, 3], [2, 3, 1, 4, 1, 2, 3], [2, 3, 4, 1, 1, 2, 3], [4, 3, 1, 1, 2, 2, 3], [2, 2, 3, 3, 1, 4, 1], [2, 2, 3, 3, 4, 1, 1], [2, 4, 3, 3, 2, 1, 1], [2, 4, 3, 3, 1, 2, 1], [2, 4, 3, 3, 1, 1, 2], [4, 2, 3, 3, 2, 1, 1], [4, 2, 3, 3, 1, 2, 1], [4, 2, 3, 3, 1, 1, 2], [2, 2, 3, 1, 1, 4, 3], [2, 2, 3, 1, 4, 1, 3], [2, 2, 3, 4, 1, 1, 3], [2, 4, 3, 1, 2, 1, 3], [2, 4, 3, 1, 1, 2, 3], [4, 2, 3, 1, 2, 1, 3], [4, 2, 3, 1, 1, 2, 3], [2, 2, 1, 3, 1, 4, 3], [2, 2, 1, 3, 4, 1, 3], [2, 2, 4, 3, 1, 1, 3], [2, 4, 1, 3, 2, 1, 3], [2, 4, 1, 3, 1, 2, 3], [4, 2, 1, 3, 2, 1, 3], [4, 2, 1, 3, 1, 2, 3]]], [[1, 1, 1, 2, 2, 2, 3, 3], [[2, 2, 2, 1, 3, 3, 1, 1], [2, 2, 2, 3, 1, 3, 1, 1], [2, 2, 2, 3, 3, 1, 1, 1], [2, 2, 3, 1, 1, 3, 2, 1], [2, 2, 3, 1, 3, 1, 2, 1], [2, 2, 3, 3, 1, 1, 2, 1], [2, 2, 3, 1, 1, 3, 1, 2], [2, 2, 3, 1, 3, 1, 1, 2], [2, 2, 3, 3, 1, 1, 1, 2], [2, 3, 2, 1, 1, 3, 2, 1], [2, 3, 2, 1, 3, 1, 2, 1], [2, 3, 2, 3, 1, 1, 2, 1], [2, 3, 2, 1, 1, 3, 1, 2], [2, 3, 2, 1, 3, 1, 1, 2], [2, 3, 2, 3, 1, 1, 1, 2], [2, 3, 3, 1, 1, 1, 2, 2], [3, 2, 2, 1, 1, 3, 2, 1], [3, 2, 2, 1, 3, 1, 2, 1], [3, 2, 2, 3, 1, 1, 2, 1], [3, 2, 2, 1, 1, 3, 1, 2], [3, 2, 2, 1, 3, 1, 1, 2], [3, 2, 2, 3, 1, 1, 1, 2], [3, 2, 3, 1, 1, 1, 2, 2], [3, 3, 2, 1, 1, 1, 2, 2]]]], "necklaces": [[[0, 0, false], [[]]], [[0, 0, true], [[]]], [[0, 2, false], [[]]], [[0, 2, true], [[]]], [[0, 3, false], [[]]], [[0, 3, true], [[]]], [[3, 0, false], []], [[3, 0, true], []], [[3, 2, false], [[0, 0, 0], [0, 0, 1], [0, 1, 1], [1, 1, 1]]], [[3, 2, true], [[0, 0, 0], [0, 0, 1], [0, 1, 1], [1, 1, 1]]], [[3, 3, false], [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 1], [0, 1, 2], [0, 2, 1], [0, 2, 2], [1, 1, 1], [1, 1, 2], [1, 2, 2], [2, 2, 2]]], [[3, 3, true], [[0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 1], [0, 1, 2], [0, 2, 2], [1, 1, 1], [1, 1, 2], [1, 2, 2], [2, 2, 2]]], [[5, 0, false], []], [[5, 0, true], []], [[5, 2, false], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 1, 1, 1], [1, 1, 1, 1, 1]]], [[5, 2, true], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1], [0, 1, 0, 1, 1], [0, 1, 1, 1, 1], [1, 1, 1, 1, 1]]], [[5, 3, false], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 2], [0, 0, 0, 1, 1], [0, 0, 0, 1, 2], [0, 0, 0, 2, 1], [0, 0, 0, 2, 2], [0, 0, 1, 0, 1], [0, 0, 1, 0, 2], [0, 0, 1, 1, 1], [0, 0, 1, 1, 2], [0, 0, 1, 2, 1], [0, 0, 1, 2, 2], [0, 0, 2, 0, 1], [0, 0, 2, 0, 2], [0, 0, 2, 1, 1], [0, 0, 2, 1, 2], [0, 0, 2, 2, 1], [0, 0, 2, 2, 2], [0, 1, 0, 1, 1], [0, 1, 0, 1, 2], [0, 1, 0, 2, 1], [0, 1, 0, 2, 2], [0, 1, 1, 0, 2], [0, 1, 1, 1, 1], [0, 1, 1, 1, 2], [0, 1, 1, 2, 1], [0, 1, 1, 2, 2], [0, 1, 2, 0, 2], [0, 1, 2, 1, 1], [0, 1, 2, 1, 2], [0, 1, 2, 2, 1], [0, 1, 2, 2, 2], [0, 2, 0, 2, 1], [0, 2, 0, 2, 2], [0, 2, 1, 1, 1], [0, 2, 1, 1, 2], [0, 2, 1, 2, 1], [0, 2, 1, 2, 2], [0, 2, 2, 1, 1], [0, 2, 2, 1, 2], [0, 2, 2, 2, 1], [0, 2, 2, 2, 2], [1, 1, 1, 1, 1], [1, 1, 1, 1, 2], [1, 1, 1, 2, 2], [1, 1, 2, 1, 2], [1, 1, 2, 2, 2], [1, 2, 1, 2, 2], [1, 2, 2, 2, 2], [2, 2, 2, 2, 2]]], [[5, 3, true], [[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 2], [0, 0, 0, 1, 1], [0, 0, 0, 1, 2], [0, 0, 0, 2, 2], [0, 0, 1, 0, 1], [0, 0, 1, 0, 2], [0, 0, 1, 1, 1], [0, 0, 1, 1, 2], [0, 0, 1, 2, 1], [0, 0, 1, 2, 2], [0, 0, 2, 0, 2], [0, 0, 2, 1, 2], [0, 0, 2, 2, 2], [0, 1, 0, 1, 1], [0, 1, 0, 1, 2], [0, 1, 0, 2, 2], [0, 1, 1, 0, 2], [0, 1, 1, 1, 1], [0, 1, 1, 1, 2], [0, 1, 1, 2, 1], [0, 1, 1, 2, 2], [0, 1, 2, 0, 2], [0, 1, 2, 1, 2], [0, 1, 2, 2, 1], [0, 1, 2, 2, 2], [0, 2, 0, 2, 2], [0, 2, 1, 1, 2], [0, 2, 1, 2, 2], [0, 2, 2, 2, 2], [1, 1, 1, 1, 1], [1, 1, 1, 1, 2], [1, 1, 1, 2, 2], [1, 1, 2, 1, 2], [1, 1, 2, 2, 2], [1, 2, 1, 2, 2], [1, 2, 2, 2, 2], [2, 2, 2, 2, 2]]]], "generateOrientedForest": [[1, [[0]]], [2, [[0, 1], [0, 0]]], [3, [[0, 1, 2], [0, 1, 1], [0, 1, 0], [0, 0, 0]]], [5, [[0, 1, 2, 3, 4], [0, 1, 2, 3, 3], [0, 1, 2, 3, 2], [0, 1, 2, 3, 1], [0, 1, 2, 3, 0], [0, 1, 2, 2, 2], [0, 1, 2, 2, 1], [0, 1, 2, 2, 0], [0, 1, 2, 1, 2], [0, 1, 2, 1, 1], [0, 1, 2, 1, 0], [0, 1, 2, 0, 1], [0, 1, 2, 0, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 0], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0]]]], "multisetCombinations": [[["abracadabra", 0], [[]]], [["abracadabra", 2], [["a", "a"], ["a", "b"], ["a", "c"], ["a", "d"], ["a", "r"], ["b", "b"], ["b", "c"], ["b", "d"], ["b", "r"], ["c", "d"], ["c", "r"], ["d", "r"], ["r", "r"]]], [["abracadabra", 5], [["a", "a", "a", "a", "a"], ["a", "a", "a", "a", "b"], ["a", "a", "a", "a", "c"], ["a", "a", "a", "a", "d"], ["a", "a", "a", "a", "r"], ["a", "a", "a", "b", "b"], ["a", "a", "a", "b", "c"], ["a", "a", "a", "b", "d"], ["a", "a", "a", "b", "r"], ["a", "a", "a", "c", "d"], ["a", "a", "a", "c", "r"], ["a", "a", "a", "d", "r"], ["a", "a", "a", "r", "r"], ["a", "a", "b", "b", "c"], ["a", "a", "b", "b", "d"], ["a", "a", "b", "b", "r"], ["a", "a", "b", "c", "d"], ["a", "a", "b", "c", "r"], ["a", "a", "b", "d", "r"], ["a", "a", "b", "r", "r"], ["a", "a", "c", "d", "r"], ["a", "a", "c", "r", "r"], ["a", "a", "d", "r", "r"], ["a", "b", "b", "c", "d"], ["a", "b", "b", "c", "r"], ["a", "b", "b", "d", "r"], ["a", "b", "b", "r", "r"], ["a", "b", "c", "d", "r"], ["a", "b", "c", "r", "r"], ["a", "b", "d", "r", "r"], ["a", "c", "d", "r", "r"], ["b", "b", "c", "d", "r"], ["b", "b", "c", "r", "r"], ["b", "b", "d", "r", "r"], ["b", "c", "d", "r", "r"]]], [["aab", 0], [[]]], [["aab", 2], [["a", "a"], ["a", "b"]]], [["aab", 5], []], [["", 0], [[]]], [["", 2], []], [["", 5], []]], "multisetPermutations": [[["aabb", null], [["a", "a", "b", "b"], ["a", "b", "a", "b"], ["a", "b", "b", "a"], ["b", "a", "a", "b"], ["b", "a", "b", "a"], ["b", "b", "a", "a"]]], [["aabb", 0], [[]]], [["aabb", 2], [["a", "a"], ["a", "b"], ["b", "a"], ["b", "b"]]], [["aabb", 5], []], [["abc", null], [["a", "b", "c"], ["a", "c", "b"], ["b", "a", "c"], ["b", "c", "a"], ["c", "a", "b"], ["c", "b", "a"]]], [["abc", 0], [[]]], [["abc", 2], [["a", "b"], ["a", "c"], ["b", "a"], ["b", "c"], ["c", "a"], ["c", "b"]]], [["abc", 5], []], [["", null], [[]]], [["", 0], [[]]], [["", 2], []], [["", 5], []]], "kbins": [[[[0, 1, 2, 3], 2, null], [[[0], [1, 2, 3]], [[0, 1], [2, 3]], [[0, 1, 2], [3]]]], [[[0, 1, 2, 3], 2, 0], [[[0, 1, 2], [3]], [[0, 1, 3], [2]], [[0, 1], [2, 3]], [[0, 2, 3], [1]], [[0, 2], [1, 3]], [[0, 3], [1, 2]], [[0], [1, 2, 3]]]], [[[0, 1, 2, 3], 2, 1], [[[0], [1, 2, 3]], [[0], [1, 3, 2]], [[0], [2, 1, 3]], [[0], [2, 3, 1]], [[0], [3, 1, 2]], [[0], [3, 2, 1]], [[1], [0, 2, 3]], [[1], [0, 3, 2]], [[1], [2, 0, 3]], [[1], [2, 3, 0]], [[1], [3, 0, 2]], [[1], [3, 2, 0]], [[2], [0, 1, 3]], [[2], [0, 3, 1]], [[2], [1, 0, 3]], [[2], [1, 3, 0]], [[2], [3, 0, 1]], [[2], [3, 1, 0]], [[3], [0, 1, 2]], [[3], [0, 2, 1]], [[3], [1, 0, 2]], [[3], [1, 2, 0]], [[3], [2, 0, 1]], [[3], [2, 1, 0]], [[0, 1], [2, 3]], [[0, 1], [3, 2]], [[0, 2], [1, 3]], [[0, 2], [3, 1]], [[0, 3], [1, 2]], [[0, 3], [2, 1]], [[1, 0], [2, 3]], [[1, 0], [3, 2]], [[1, 2], [0, 3]], [[1, 2], [3, 0]], [[1, 3], [0, 2]], [[1, 3], [2, 0]], [[2, 0], [1, 3]], [[2, 0], [3, 1]], [[2, 1], [0, 3]], [[2, 1], [3, 0]], [[2, 3], [0, 1]], [[2, 3], [1, 0]], [[3, 0], [1, 2]], [[3, 0], [2, 1]], [[3, 1], [0, 2]], [[3, 1], [2, 0]], [[3, 2], [0, 1]], [[3, 2], [1, 0]]]], [[[0, 1, 2, 3], 2, 10], [[[0, 1, 2], [3]], [[3], [0, 1, 2]], [[0, 1, 3], [2]], [[2], [0, 1, 3]], [[0, 1], [2, 3]], [[2, 3], [0, 1]], [[0, 2, 3], [1]], [[1], [0, 2, 3]], [[0, 2], [1, 3]], [[1, 3], [0, 2]], [[0, 3], [1, 2]], [[1, 2], [0, 3]], [[0], [1, 2, 3]], [[1, 2, 3], [0]]]], [[[0, 1, 2, 3], 2, 11], [[[0], [1, 2, 3]], [[0, 1], [2, 3]], [[0, 1, 2], [3]], [[0], [1, 3, 2]], [[0, 1], [3, 2]], [[0, 1, 3], [2]], [[0], [2, 1, 3]], [[0, 2], [1, 3]], [[0, 2, 1], [3]], [[0], [2, 3, 1]], [[0, 2], [3, 1]], [[0, 2, 3], [1]], [[0], [3, 1, 2]], [[0, 3], [1, 2]], [[0, 3, 1], [2]], [[0], [3, 2, 1]], [[0, 3], [2, 1]], [[0, 3, 2], [1]], [[1], [0, 2, 3]], [[1, 0], [2, 3]], [[1, 0, 2], [3]], [[1], [0, 3, 2]], [[1, 0], [3, 2]], [[1, 0, 3], [2]], [[1], [2, 0, 3]], [[1, 2], [0, 3]], [[1, 2, 0], [3]], [[1], [2, 3, 0]], [[1, 2], [3, 0]], [[1, 2, 3], [0]], [[1], [3, 0, 2]], [[1, 3], [0, 2]], [[1, 3, 0], [2]], [[1], [3, 2, 0]], [[1, 3], [2, 0]], [[1, 3, 2], [0]], [[2], [0, 1, 3]], [[2, 0], [1, 3]], [[2, 0, 1], [3]], [[2], [0, 3, 1]], [[2, 0], [3, 1]], [[2, 0, 3], [1]], [[2], [1, 0, 3]], [[2, 1], [0, 3]], [[2, 1, 0], [3]], [[2], [1, 3, 0]], [[2, 1], [3, 0]], [[2, 1, 3], [0]], [[2], [3, 0, 1]], [[2, 3], [0, 1]], [[2, 3, 0], [1]], [[2], [3, 1, 0]], [[2, 3], [1, 0]], [[2, 3, 1], [0]], [[3], [0, 1, 2]], [[3, 0], [1, 2]], [[3, 0, 1], [2]], [[3], [0, 2, 1]], [[3, 0], [2, 1]], [[3, 0, 2], [1]], [[3], [1, 0, 2]], [[3, 1], [0, 2]], [[3, 1, 0], [2]], [[3], [1, 2, 0]], [[3, 1], [2, 0]], [[3, 1, 2], [0]], [[3], [2, 0, 1]], [[3, 2], [0, 1]], [[3, 2, 0], [1]], [[3], [2, 1, 0]], [[3, 2], [1, 0]], [[3, 2, 1], [0]]]], [[[0, 1, 2, 3], 3, null], [[[0], [1], [2, 3]], [[0], [1, 2], [3]], [[0, 1], [2], [3]]]], [[[0, 1, 2, 3], 3, 0], [[[0, 1], [2], [3]], [[0, 2], [1], [3]], [[0], [1, 2], [3]], [[0, 3], [1], [2]], [[0], [1, 3], [2]], [[0], [1], [2, 3]]]], [[[0, 1, 2, 3], 3, 1], [[[0], [1], [2, 3]], [[0], [1], [3, 2]], [[0], [2], [1, 3]], [[0], [2], [3, 1]], [[0], [3], [1, 2]], [[0], [3], [2, 1]], [[1], [0], [2, 3]], [[1], [0], [3, 2]], [[1], [2], [0, 3]], [[1], [2], [3, 0]], [[1], [3], [0, 2]], [[1], [3], [2, 0]], [[2], [0], [1, 3]], [[2], [0], [3, 1]], [[2], [1], [0, 3]], [[2], [1], [3, 0]], [[2], [3], [0, 1]], [[2], [3], [1, 0]], [[3], [0], [1, 2]], [[3], [0], [2, 1]], [[3], [1], [0, 2]], [[3], [1], [2, 0]], [[3], [2], [0, 1]], [[3], [2], [1, 0]]]], [[[0, 1, 2, 3], 3, 10], [[[0, 1], [2], [3]], [[0, 1], [3], [2]], [[2], [0, 1], [3]], [[2], [3], [0, 1]], [[3], [0, 1], [2]], [[3], [2], [0, 1]], [[0, 2], [1], [3]], [[0, 2], [3], [1]], [[1], [0, 2], [3]], [[1], [3], [0, 2]], [[3], [0, 2], [1]], [[3], [1], [0, 2]], [[0], [1, 2], [3]], [[0], [3], [1, 2]], [[1, 2], [0], [3]], [[1, 2], [3], [0]], [[3], [0], [1, 2]], [[3], [1, 2], [0]], [[0, 3], [1], [2]], [[0, 3], [2], [1]], [[1], [0, 3], [2]], [[1], [2], [0, 3]], [[2], [0, 3], [1]], [[2], [1], [0, 3]], [[0], [1, 3], [2]], [[0], [2], [1, 3]], [[1, 3], [0], [2]], [[1, 3], [2], [0]], [[2], [0], [1, 3]], [[2], [1, 3], [0]], [[0], [1], [2, 3]], [[0], [2, 3], [1]], [[1], [0], [2, 3]], [[1], [2, 3], [0]], [[2, 3], [0], [1]], [[2, 3], [1], [0]]]], [[[0, 1, 2, 3], 3, 11], [[[0], [1], [2, 3]], [[0], [1, 2], [3]], [[0, 1], [2], [3]], [[0], [1], [3, 2]], [[0], [1, 3], [2]], [[0, 1], [3], [2]], [[0], [2], [1, 3]], [[0], [2, 1], [3]], [[0, 2], [1], [3]], [[0], [2], [3, 1]], [[0], [2, 3], [1]], [[0, 2], [3], [1]], [[0], [3], [1, 2]], [[0], [3, 1], [2]], [[0, 3], [1], [2]], [[0], [3], [2, 1]], [[0], [3, 2], [1]], [[0, 3], [2], [1]], [[1], [0], [2, 3]], [[1], [0, 2], [3]], [[1, 0], [2], [3]], [[1], [0], [3, 2]], [[1], [0, 3], [2]], [[1, 0], [3], [2]], [[1], [2], [0, 3]], [[1], [2, 0], [3]], [[1, 2], [0], [3]], [[1], [2], [3, 0]], [[1], [2, 3], [0]], [[1, 2], [3], [0]], [[1], [3], [0, 2]], [[1], [3, 0], [2]], [[1, 3], [0], [2]], [[1], [3], [2, 0]], [[1], [3, 2], [0]], [[1, 3], [2], [0]], [[2], [0], [1, 3]], [[2], [0, 1], [3]], [[2, 0], [1], [3]], [[2], [0], [3, 1]], [[2], [0, 3], [1]], [[2, 0], [3], [1]], [[2], [1], [0, 3]], [[2], [1, 0], [3]], [[2, 1], [0], [3]], [[2], [1], [3, 0]], [[2], [1, 3], [0]], [[2, 1], [3], [0]], [[2], [3], [0, 1]], [[2], [3, 0], [1]], [[2, 3], [0], [1]], [[2], [3], [1, 0]], [[2], [3, 1], [0]], [[2, 3], [1], [0]], [[3], [0], [1, 2]], [[3], [0, 1], [2]], [[3, 0], [1], [2]], [[3], [0], [2, 1]], [[3], [0, 2], [1]], [[3, 0], [2], [1]], [[3], [1], [0, 2]], [[3], [1, 0], [2]], [[3, 1], [0], [2]], [[3], [1], [2, 0]], [[3], [1, 2], [0]], [[3, 1], [2], [0]], [[3], [2], [0, 1]], [[3], [2, 0], [1]], [[3, 2], [0], [1]], [[3], [2], [1, 0]], [[3], [2, 1], [0]], [[3, 2], [1], [0]]]], [[[1, 1, 2], 2, null], [[[1], [1, 2]], [[1, 1], [2]]]], [[[1, 1, 2], 2, 0], [[[1, 1], [2]], [[1, 2], [1]]]], [[[1, 1, 2], 2, 1], [[[1], [1, 2]], [[1], [2, 1]], [[2], [1, 1]]]], [[[1, 1, 2], 2, 10], [[[1, 1], [2]], [[2], [1, 1]], [[1, 2], [1]], [[1], [1, 2]]]], [[[1, 1, 2], 2, 11], [[[1], [1, 2]], [[1, 1], [2]], [[1], [2, 1]], [[1, 2], [1]], [[2], [1, 1]], [[2, 1], [1]]]], [[[1, 1, 2], 3, null], [[[1], [1], [2]]]], [[[1, 1, 2], 3, 0], [[[1], [1], [2]]]], [[[1, 1, 2], 3, 1], [[[1], [1], [2]], [[1], [2], [1]], [[2], [1], [1]]]], [[[1, 1, 2], 3, 10], [[[1], [1], [2]], [[1], [2], [1]], [[1], [1], [2]], [[1], [2], [1]], [[2], [1], [1]], [[2], [1], [1]]]], [[[1, 1, 2], 3, 11], [[[1], [1], [2]], [[1], [2], [1]], [[2], [1], [1]]]]]} as const;

describe('sequences', () => {
  it('isPalindromic', () => {
    expect(isPalindromic([1, 0, 1])).toBe(true);
    expect(isPalindromic('abcbb')).toBe(false);
    expect(isPalindromic('abcbb', 1)).toBe(false);
    expect(isPalindromic('abcbb', 1, -1)).toBe(true);
    expect(isPalindromic('abcbb', -4, -1)).toBe(true);
    expect(isPalindromic([x, add(x, 1), x])).toBe(true);
  });
  it('flatten', () => {
    expect(flatten([1, 2, 3])).toEqual([1, 2, 3]);
    expect(flatten([1, 2, [3]])).toEqual([1, 2, 3]);
    expect(flatten([1, [2, 3], [4, 5]])).toEqual([1, 2, 3, 4, 5]);
    expect(flatten([1.5, 2, [1, null]])).toEqual([1.5, 2, 1, null]);
    const ls = [[[-2, -1], [1, 2]], [[0, 0]]];
    expect(flatten(ls, { levels: 1 })).toEqual([[-2, -1], [1, 2], [0, 0]]);
    expect(flatten(ls, { levels: 0 })).toBe(ls);
    expect(flatten([1, [2, [3, [4]]]], { levels: 2 })).toEqual([1, 2, 3, [4]]);
    expect(flatten([new Set([1]), 'ab'])).toEqual([1, 'ab']);
    // cls flattens expressions of that class through their arguments
    expect(str(flatten([add(x, mul(y, add(z, w)))], { cls: Add }))).toEqual(['x', 'y*(w + z)']);
    expect(() => flatten([1], { levels: -1 })).toThrow(RangeError);
  });
  it('unflatten', () => {
    expect(unflatten([1, 2, 3, 4])).toEqual([[1, 2], [3, 4]]);
    expect(unflatten([1, 2, 3, 4, 5, 6], 3)).toEqual([[1, 2, 3], [4, 5, 6]]);
    expect(() => unflatten([1, 2, 3])).toThrow(RangeError);
  });
  it('reshape', () => {
    const seq = [1, 2, 3, 4, 5, 6, 7, 8];
    expect(reshape(seq, [4])).toEqual([[1, 2, 3, 4], [5, 6, 7, 8]]);
    expect(reshape(seq, [2, 2])).toEqual([[1, 2, 3, 4], [5, 6, 7, 8]]);
    expect(reshape(seq, [2, [2]])).toEqual([[1, 2, [3, 4]], [5, 6, [7, 8]]]);
    expect(reshape(seq, [[2], [2]])).toEqual([[[1, 2], [3, 4]], [[5, 6], [7, 8]]]);
    expect(reshape(seq, [1, [2], 1])).toEqual([[1, [2, 3], 4], [5, [6, 7], 8]]);
    expect(reshape(seq, [[[1], 1, [2]]])).toEqual([[[[1], 2, [3, 4]]], [[[5], 6, [7, 8]]]]);
    expect(reshape(seq, [[1], 1, [2]])).toEqual([[[1], 2, [3, 4]], [[5], 6, [7, 8]]]);
    const r = reshape([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [2, [3], new Set([2]), [1, [3], 1]]);
    expect(r).toEqual([[0, 1, [2, 3, 4], new Set([5, 6]), [7, [8, 9, 10], 11]]]);
    expect(() => reshape([1, 2, 3], [2])).toThrow(RangeError);
  });
  it('group', () => {
    expect(group([1, 1, 1, 2, 2, 3])).toEqual([[1, 1, 1], [2, 2], [3]]);
    expect(group([1, 1, 1, 2, 2, 3], { multiple: false })).toEqual([[1, 3], [2, 2], [3, 1]]);
    expect(group([1, 1, 3, 2, 2, 1], { multiple: false })).toEqual([[1, 2], [3, 1], [2, 2], [1, 1]]);
    expect(group('aabccc')).toEqual([['a', 'a'], ['b'], ['c', 'c', 'c']]);
  });
  it('iproduct', () => {
    expect(sorted(list(iproduct([1, 2], [3, 4])))).toEqual([[1, 3], [1, 4], [2, 3], [2, 4]]);
    expect(list(iproduct([1, 2, 3], [4, 5]))).toEqual([[1, 4], [2, 4], [1, 5], [3, 4], [2, 5], [3, 5]]);
    expect(list(iproduct([1, 2], [3, 4], [5, 6]))).toEqual([[1, 3, 5], [2, 3, 5], [1, 4, 5], [2, 4, 5], [1, 3, 6], [2, 3, 6], [1, 4, 6], [2, 4, 6]]);
    expect(list(iproduct())).toEqual([[]]);
    expect(list(iproduct([1, 2], []))).toEqual([]);
    // infinite iterables (S.Integers in SymPy)
    expect(includes(iproduct(integers()), [3])).toBe(true);
    expect(includes(iproduct(integers(), integers()), [3, 4])).toBe(true);
  });
  it('multiset', () => {
    expect(sorted([...multiset('mississippi')])).toEqual([['i', 4], ['m', 1], ['p', 2], ['s', 4]]);
    expect([...multiset('mississippi')]).toEqual([['m', 1], ['i', 4], ['s', 4], ['p', 2]]);
    const m = multiset([x, 1, new Sym('x')]);
    expect(str(m)).toEqual([['x', 2], [1, 1]]);
    expect(m.get(new Sym('x'))).toBe(2);
    expect(multiset([[1], [1]]).get([1])).toBe(2);
  });
  it('ibin', () => {
    expect(ibin(2)).toEqual([1, 0]);
    expect(ibin(2, 4)).toEqual([0, 0, 1, 0]);
    expect(list(ibin(2, 'all'))).toEqual([[0, 0], [0, 1], [1, 0], [1, 1]]);
    expect(ibin(123, 10, { str: true })).toBe('0001111011');
    expect(ibin(123, 10, { str: true }).split('').reverse().join('')).toBe('1101111000');
    expect(list(ibin(3, 'all', { str: true }))).toEqual(['000', '001', '010', '011', '100', '101', '110', '111']);
    expect(ibin(0)).toEqual([0]);
    expect(ibin(0, 3)).toEqual([0, 0, 0]);
    expect(ibin(0, null, { str: true })).toBe('0');
    expect(list(ibin(0, 'all'))).toEqual([[]]);
    expect(ibin(2n ** 70n, null, { str: true })).toBe(`1${'0'.repeat(70)}`);
    expect(() => ibin(-1)).toThrow(RangeError);
    expect(() => ibin(8, 2)).toThrow('`bits` must be >= 4');
  });
  it('variations', () => {
    expect(list(variations([1, 2], 2))).toEqual([[1, 2], [2, 1]]);
    expect(list(variations([1, 2], 2, { repetition: true }))).toEqual([[1, 1], [1, 2], [2, 1], [2, 2]]);
    expect(list(variations([0, 1], 3, { repetition: false }))).toEqual([]);
    expect(list(variations([0, 1], 3, { repetition: true })).slice(0, 4)).toEqual([[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1]]);
    expect(list(variations([0, 1], 0, { repetition: true }))).toEqual([[]]);
  });
  it('subsets', () => {
    expect(list(subsets([1, 2], 2))).toEqual([[1, 2]]);
    expect(list(subsets([1, 2]))).toEqual([[], [1], [2], [1, 2]]);
    expect(list(subsets([1, 2, 3], 2))).toEqual([[1, 2], [1, 3], [2, 3]]);
    expect(list(subsets([1, 2], 2, { repetition: true }))).toEqual([[1, 1], [1, 2], [2, 2]]);
    expect(list(subsets([0, 1], 3, { repetition: false }))).toEqual([]);
    expect(list(subsets([0, 1], 3, { repetition: true }))).toEqual([[0, 0, 0], [0, 0, 1], [0, 1, 1], [1, 1, 1]]);
    expect(list(subsets([1, 2, 3], null, { repetition: true }))).toEqual([[], [1], [2], [3], [1, 1], [1, 2], [1, 3], [2, 2], [2, 3], [3, 3], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 2, 2], [1, 2, 3], [1, 3, 3], [2, 2, 2], [2, 2, 3], [2, 3, 3], [3, 3, 3]]);
  });
  it('filterSymbols and numberedSymbols', () => {
    expect(str(list(filterSymbols([x, y, z], [new Sym('y')])))).toEqual(['x', 'z']);
    expect(str(take(numberedSymbols(), 3))).toEqual(['x0', 'x1', 'x2']);
    expect(str(take(numberedSymbols('y', { start: 3, exclude: [new Sym('y4')] }), 3))).toEqual(['y3', 'y5', 'y6']);
    const [p] = take(numberedSymbols('a', { positive: true }), 1);
    expect(p!.assumptions.positive).toBe(true);
    const [d] = take(numberedSymbols('_', { cls: Dummy }), 1);
    expect(d).toBeInstanceOf(Dummy);
  });
  it('capture', () => {
    const foo = (print: I.PrintFunction) => print('hello world!');
    expect(capture(foo).includes('hello')).toBe(true);
    expect(capture(foo)).toBe('hello world!\n');
    // SymPy: capture(lambda: pprint(2/x)) == '2\n-\nx\n' (symjs has no pretty printer)
    expect(capture((print) => print(mul(2, pow(x, -1))))).toBe('2/x\n');
    expect(capture((print) => print(1, 'a', x))).toBe('1 a x\n');
  });
  it('sift', () => {
    expect([...sift([0, 1, 2, 3, 4], (v) => v % 2)]).toEqual([[0, [0, 2, 4]], [1, [1, 3]]]);
    const m = sift([x], (v) => v.isCommutative);
    expect([...m]).toEqual([[true, [x]]]);
    expect(m.get(false) ?? []).toEqual([]);
    const s = sift([sqrt(x), exp(x), pow(pow(y, x), 2)], (v: Expr) => (v.args.length === 2 ? v.args[0]! : v));
    expect(str(s)).toEqual([['x', ['sqrt(x)']], ['E', ['exp(x)']], ['y', ['y**(2*x)']]]);
    expect(str(s.get(new Sym('y')))).toEqual(['y**(2*x)']);
    expect(sift([0, 1, 2, 3], (v) => v % 2, { binary: true })).toEqual([[1, 3], [0, 2]]);
    expect(str(sift([add(1, 0), pi], (v) => isRational(v), { binary: true }))).toEqual([['1'], ['pi']]);
    const unknown = sub(E, pi);
    const truth = (v: unknown): boolean | 'unknown' => (v === unknown ? 'unknown' : typeof v === 'number');
    expect(() => sift([1, pi, unknown] as unknown[], truth, { binary: true })).toThrow('keyfunc gave non-binary output');
    expect(new Set(sift([1, pi, unknown] as unknown[], truth).keys())).toEqual(new Set([true, false, 'unknown']));
  });
  it('take and dictMerge', () => {
    expect(take([1, 2, 3], 2)).toEqual([1, 2]);
    expect(take(integers(), 3)).toEqual([0, 1, -1]);
    expect(take([1], 0)).toEqual([]);
    const m = dictMerge(new Map([[1, 'a'], [2, 'b']]), new Map([[2, 'c'], [3, 'd']]));
    expect([...m]).toEqual([[1, 'a'], [2, 'c'], [3, 'd']]);
  });
  it('commonPrefix and commonSuffix', () => {
    expect(commonPrefix([0, 1, 2])).toEqual([0, 1, 2]);
    expect(commonPrefix([0, 1, 2], [0, 1, 2, 3])).toEqual([0, 1, 2]);
    expect(commonPrefix([1, 2, 3], [1, 2, 5])).toEqual([1, 2]);
    expect(commonPrefix([1, 2, 3], [1, 3, 5])).toEqual([1]);
    expect(commonPrefix([1, 2], [])).toEqual([]);
    expect(commonSuffix([0, 1, 2])).toEqual([0, 1, 2]);
    expect(commonSuffix([0, 1, 2], [0, 1, 2, 3])).toEqual([]);
    expect(commonSuffix([1, 2, 3], [9, 2, 3])).toEqual([2, 3]);
    expect(commonSuffix([1, 2, 3], [9, 7, 3])).toEqual([3]);
    expect(commonSuffix([1, 2, 3], [1, 2, 3])).toEqual([1, 2, 3]);
  });
  it('prefixes and postfixes', () => {
    expect(list(prefixes([1, 2, 3, 4]))).toEqual([[1], [1, 2], [1, 2, 3], [1, 2, 3, 4]]);
    expect(list(postfixes([1, 2, 3, 4]))).toEqual([[4], [3, 4], [2, 3, 4], [1, 2, 3, 4]]);
  });
});

describe('graphs', () => {
  const V = [2, 3, 5, 7, 8, 9, 10, 11];
  const E: [number, number][] = [[7, 11], [7, 8], [5, 11], [3, 8], [3, 10], [11, 2], [11, 9], [11, 10], [8, 9]];
  it('topologicalSort', () => {
    expect(topologicalSort([V, E])).toEqual([3, 5, 7, 8, 11, 2, 9, 10]);
    expect(topologicalSort([V, E], (v) => -v)).toEqual([7, 5, 11, 3, 10, 8, 9, 2]);
    expect(() => topologicalSort([V, [...E, [10, 7]]])).toThrow('cycle detected');
  });
  it('stronglyConnectedComponents', () => {
    const V2 = ['A', 'B', 'C', 'D'];
    const E2: [string, string][] = [['A', 'B'], ['A', 'C'], ['B', 'C'], ['C', 'B'], ['B', 'D']];
    expect(stronglyConnectedComponents([V2, E2])).toEqual([['D'], ['B', 'C'], ['A']]);
    expect(stronglyConnectedComponents([[1, 2, 3, 4, 5, 6], [[1, 2], [2, 3], [3, 1], [4, 5], [5, 4], [3, 4], [6, 6]]])).toEqual([[4, 5], [1, 2, 3], [6]]);
  });
  it('connectedComponents', () => {
    const V2 = ['A', 'B', 'C', 'D'];
    const E2: [string, string][] = [['A', 'B'], ['B', 'A'], ['C', 'D'], ['D', 'C']];
    expect(connectedComponents([V2, E2])).toEqual([['A', 'B'], ['C', 'D']]);
    expect(connectedComponents([[1, 2, 3, 4, 5, 6], [[1, 2], [3, 4], [5, 6], [6, 1]]])).toEqual([[1, 2, 6, 5], [3, 4]]);
  });
});

describe('rotations', () => {
  it('rotateLeft and rotateRight', () => {
    expect(rotateLeft([0, 1, 2], 1)).toEqual([1, 2, 0]);
    expect(rotateRight([0, 1, 2], 1)).toEqual([2, 0, 1]);
    expect(rotateLeft('abc', -1)).toBe('cab');
    expect(rotateLeft([], 3)).toEqual([]);
  });
  it('leastRotation', () => {
    const a = [3, 1, 5, 1, 2];
    expect(leastRotation(a)).toBe(3);
    expect(rotateLeft(a, 3)).toEqual([1, 2, 3, 1, 5]);
    expect([[1, 1, 1], [2, 1, 2, 1], 'bcaab', ''].map((v) => leastRotation(v as number[]))).toEqual([0, 1, 2, 0]);
  });
  it('minlex', () => {
    expect(minlex([1, 2, 0])).toEqual([0, 1, 2]);
    expect(minlex([1, 0, 2])).toEqual([0, 2, 1]);
    expect(minlex([1, 0, 2], { directed: false })).toEqual([0, 1, 2]);
    expect(minlex('11010011000', { directed: true })).toBe('00011010011');
    expect(minlex('11010011000', { directed: false })).toBe('00011001011');
    expect(minlex(['bb', 'aaa', 'c', 'a'])).toEqual(['a', 'bb', 'aaa', 'c']);
    expect(minlex(['bb', 'aaa', 'c', 'a'], { key: (s) => s.length })).toEqual(['c', 'a', 'bb', 'aaa']);
    expect(minlex([3, 2, 1, 2, 0], { directed: false })).toEqual([0, 2, 1, 2, 3]);
    expect(minlex('cba', { directed: false })).toBe('abc');
  });
  it('runs', () => {
    expect(runs([0, 1, 2, 2, 1, 4, 3, 2, 2])).toEqual([[0, 1, 2], [2], [1, 4], [3], [2], [2]]);
    expect(runs([0, 1, 2, 2, 1, 4, 3, 2, 2], (a, b) => a >= b)).toEqual([[0, 1, 2, 2], [1, 4], [3], [2, 2]]);
    expect(runs([])).toEqual([]);
  });
  it('rotations and roundrobin', () => {
    expect(list(rotations([1, 2, 3]))).toEqual([[1, 2, 3], [2, 3, 1], [3, 1, 2]]);
    expect(list(rotations([1, 2, 3], -1))).toEqual([[1, 2, 3], [3, 1, 2], [2, 3, 1]]);
    expect(list(roundrobin('ABC', 'D', 'EF')).join(' ')).toBe('A D E B F C');
  });
});

describe('combinatorics', () => {
  it('multisetCombinations', () => {
    expect(join(multisetCombinations('baby', 3))).toEqual(['abb', 'aby', 'bby']);
    const count = (s: string) => list(multisetCombinations(s, 3)).length;
    expect(count('abracadabra')).toBe(23);
    expect(count('banana tree')).toBe(54);
    expect(list(multisetCombinations(new Map([['a', 2], ['b', 1]]), 2))).toEqual([['a', 'a'], ['a', 'b']]);
    expect(list(multisetCombinations(['b', 'a', 10, 2], 2))).toEqual([['a', 'b'], ['a', 2], ['a', 10], ['b', 2], ['b', 10], [2, 10]]);
    expect(() => list(multisetCombinations(new Map([['a', -1]]), 1))).toThrow('counts cannot be negative');
  });
  it('multisetPermutations', () => {
    expect(join(multisetPermutations('aab'))).toEqual(['aab', 'aba', 'baa']);
    expect(list(multisetPermutations('banana')).length).toBe(60);
    expect(str(list(multisetPermutations([y, x, 2, 1])).slice(0, 2))).toEqual([[1, 2, 'x', 'y'], [1, 2, 'y', 'x']]);
    expect(list(multisetPermutations(new Map([['a', 1], ['b', 1]])))).toEqual([['a', 'b'], ['b', 'a']]);
  });
  it('multisetPartitions', () => {
    expect(list(multisetPartitions([1, 2, 3, 4], 2))).toEqual([[[1, 2, 3], [4]], [[1, 2, 4], [3]], [[1, 2], [3, 4]], [[1, 3, 4], [2]], [[1, 3], [2, 4]], [[1, 4], [2, 3]], [[1], [2, 3, 4]]]);
    expect(list(multisetPartitions([1, 2, 3, 4], 1))).toEqual([[[1, 2, 3, 4]]]);
    const a = [1, 2, 2, 1];
    expect(list(multisetPartitions(a, 2))).toEqual(list(multisetPartitions(sorted([...a]), 2)));
    expect(list(multisetPartitions([3, 2]))).toEqual(list(multisetPartitions([2, 3])));
    expect(list(multisetPartitions([1, 1, 2]))).toEqual([[[1, 1, 2]], [[1, 1], [2]], [[1, 2], [1]], [[1], [1], [2]]]);
    expect(list(multisetPartitions([1, 1, 1]))).toEqual([[[1, 1, 1]], [[1], [1, 1]], [[1], [1], [1]]]);
    expect(list(multisetPartitions(5)).length).toBe(52); // bell(5)
    expect(list(multisetPartitions(5, 2)).length).toBe(15); // stirling(5, 2)
    expect(list(multisetPartitions(3))).toEqual([[[0, 1, 2]], [[0, 1], [2]], [[0, 2], [1]], [[0], [1, 2]], [[0], [1], [2]]]);
    expect(list(multisetPartitions(3, 4))).toEqual([]);
    expect(list(multisetPartitions(0))).toEqual([[]]);
    expect(str(list(multisetPartitions([x, y, x])))).toEqual([[['x', 'x', 'y']], [['x', 'x'], ['y']], [['x', 'y'], ['x']], [['x'], ['x'], ['y']]]);
    // a string is the multiset of its characters
    expect(list(multisetPartitions('aa'))).toEqual([[['a', 'a']], [['a'], ['a']]]);
  });
  it('partitions', () => {
    expect(list(partitions(6, { k: 2 }))).toEqual([new Map([[2, 3]]), new Map([[2, 2], [1, 2]]), new Map([[2, 1], [1, 4]]), new Map([[1, 6]])]);
    expect(list(partitions(6, { m: 2 }))).toEqual([new Map([[6, 1]]), new Map([[5, 1], [1, 1]]), new Map([[4, 1], [2, 1]]), new Map([[3, 2]])]);
    expect(list(partitions(4, { size: true }))[1]).toEqual([2, new Map([[3, 1], [1, 1]])]);
    expect(list(partitions(0))).toEqual([new Map()]);
    expect(list(partitions(0, { size: true }))).toEqual([[0, new Map()]]);
  });
  it('orderedPartitions', () => {
    expect(list(orderedPartitions(5))).toEqual([[1, 1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 3], [1, 2, 2], [1, 4], [2, 3], [5]]);
    expect(list(orderedPartitions(5, 2))).toEqual([[1, 4], [2, 3]]);
    // SymPy reuses one list here ([[1, 1, 1], [1, 1, 1], [1, 1, 1], [2, 2, 2]]); symjs yields copies
    expect(list(orderedPartitions(7, 3))).toEqual([[1, 1, 5], [1, 2, 4], [1, 3, 3], [2, 2, 3]]);
    expect(list(orderedPartitions(6, 2))).toEqual([[1, 5], [2, 4], [3, 3]]);
    expect(list(orderedPartitions(6, 2, { sort: false }))).toEqual([[1, 5], [3, 3], [2, 4]]);
    expect(list(orderedPartitions(0))).toEqual([[]]);
  });
  it('binaryPartitions', () => {
    expect(list(binaryPartitions(5))).toEqual([[4, 1], [2, 2, 1], [2, 1, 1, 1], [1, 1, 1, 1, 1]]);
  });
  it('hasDups, hasVariety and uniq', () => {
    expect(hasDups([1, 2, 1])).toBe(true);
    expect(hasDups([0, 1, 2])).toBe(false);
    expect([new Set(), new Map()].every((c) => !hasDups(c))).toBe(true);
    expect(hasDups([[1], [1]])).toBe(true);
    expect(hasVariety([1, 2, 1])).toBe(true);
    expect(hasVariety([1, 1, 1])).toBe(false);
    const dat = [1, 4, 1, 5, 4, 2, 1, 2];
    expect(Array.isArray(uniq(dat))).toBe(false);
    expect(list(uniq(dat))).toEqual([1, 4, 5, 2]);
    expect(list(uniq((function* () {
      yield* dat;
    })()))).toEqual([1, 4, 5, 2]);
    expect(list(uniq([[1], [2, 1], [1]]))).toEqual([[1], [2, 1]]);
    const grow = [1, 2];
    expect(() => {
      for (const v of uniq(grow)) grow.push(v);
    }).toThrow('sequence changed size during iteration');
  });
  it('generateBell', () => {
    expect(list(perms([0, 1, 2, 3])).slice(0, 5)).toEqual([[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2]]);
    expect(list(generateBell(4)).slice(0, 5)).toEqual([[0, 1, 2, 3], [0, 1, 3, 2], [0, 3, 1, 2], [3, 0, 1, 2], [3, 0, 2, 1]]);
    // m.print_nonzero('X') of the positions of the largest element
    const rows = [0, 1, 2, 3].map((r) => list(generateBell(4)).map((p) => (p[r] === 3 ? ' ' : 'X')).join(''));
    expect(rows).toEqual(['XXX  XXXXXX  XXXXXX  XXX', 'XX XX XXXX XX XXXX XX XX', 'X XXXX XX XXXX XX XXXX X', ' XXXXXX  XXXXXX  XXXXXX ']);
    expect(() => list(generateBell(0))).toThrow(RangeError);
  });
  it('generateInvolutions', () => {
    expect(list(generateInvolutions(3))).toEqual([[0, 1, 2], [0, 2, 1], [1, 0, 2], [2, 1, 0]]);
    expect(list(generateInvolutions(4)).length).toBe(10);
  });
  it('multisetDerangements', () => {
    // SymPy fills one list in place (uniq gives [[None, None, None, None]]); symjs yields copies
    expect(list(multisetDerangements('1233'))).toEqual([['3', '3', '1', '2'], ['3', '3', '2', '1']]);
    expect(join(multisetDerangements('1233'))).toEqual(['3312', '3321']);
    expect(list(multisetDerangements('aaab'))).toEqual([]);
  });
  it('randomDerangement', () => {
    const t = 'SymPy: a CAS in pure Python';
    const d = randomDerangement(t);
    expect(d.every((c, i) => c !== t[i])).toBe(true);
    const d1 = [0, 1, 2, 3, 4].map((i) => randomDerangement(t, 1 + i).join(''));
    expect(new Set(d1).size).not.toBe(1);
    const d2 = [0, 1, 2, 3, 4].map((i) => randomDerangement(t, 1 + i).join(''));
    expect(d2).toEqual(d1);
    for (const s of ['abcd', 'aabbc', 'aabb', [1, 1, 2, 3]] as (string | number[])[]) {
      for (let seed = 0; seed < 20; seed++) {
        const r = randomDerangement<unknown>(s, seed);
        const items: unknown[] = typeof s === 'string' ? Array.from(s) : s;
        expect(r.every((c, i) => c !== items[i])).toBe(true);
        expect(sorted([...r])).toEqual(sorted(items));
      }
    }
    expect(() => randomDerangement('aaab', 1)).toThrow('no derangement possible');
    const ns = randomDerangement('aaabc', 3, { strict: false });
    expect(ns.filter((c, i) => c === 'aaabc'[i])).toEqual(['a']);
    expect(randomDerangement([])).toEqual([]);
  });
  it('generateDerangements', () => {
    expect(list(generateDerangements([0, 1, 2]))).toEqual([[1, 2, 0], [2, 0, 1]]);
    expect(list(generateDerangements([0, 1, 2, 2]))).toEqual([[2, 2, 0, 1], [2, 2, 1, 0]]);
    expect(list(generateDerangements([0, 1, 1]))).toEqual([]);
    expect(list(generateDerangements('aabbc'))).toEqual([['b', 'b', 'a', 'c', 'a'], ['b', 'b', 'c', 'a', 'a'], ['b', 'c', 'a', 'a', 'b'], ['c', 'b', 'a', 'a', 'b']]);
  });
  it('necklaces and bracelets', () => {
    const show = (s: string, i: number[]) => i.map((j) => s[j]).join('');
    const B = list(bracelets(3, 3)).map((i) => show('ABC', i));
    const N = list(necklaces(3, 3)).map((i) => show('ABC', i));
    expect(N.filter((n) => !B.includes(n))).toEqual(['ACB']);
    expect(list(necklaces(4, 2))).toEqual([[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]]);
    expect(list(bracelets(4, 2)).map((i) => show('.o', i))).toEqual(['....', '...o', '..oo', '.o.o', '.ooo', 'oooo']);
  });
  it('generateOrientedForest', () => {
    expect(list(generateOrientedForest(4))).toEqual([[0, 1, 2, 3], [0, 1, 2, 2], [0, 1, 2, 1], [0, 1, 2, 0], [0, 1, 1, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 1, 0, 0], [0, 0, 0, 0]]);
  });
  it('sequencePartitions and sequencePartitionsEmpty', () => {
    expect(list(sequencePartitions([1, 2, 3, 4], 2))).toEqual([[[1], [2, 3, 4]], [[1, 2], [3, 4]], [[1, 2, 3], [4]]]);
    expect(list(sequencePartitionsEmpty([1, 2, 3, 4], 2))).toEqual([[[], [1, 2, 3, 4]], [[1], [2, 3, 4]], [[1, 2], [3, 4]], [[1, 2, 3], [4]], [[1, 2, 3, 4], []]]);
    expect(list(sequencePartitions('abc', 2))).toEqual([['a', 'bc'], ['ab', 'c']]);
    expect(list(sequencePartitionsEmpty('ab', 0))).toEqual([]);
  });
  it('kbins', () => {
    expect(list(kbins([0, 1, 2, 3, 4], 2))).toEqual([[[0], [1, 2, 3, 4]], [[0, 1], [2, 3, 4]], [[0, 1, 2], [3, 4]], [[0, 1, 2, 3], [4]]]);
    const l = [0, 1, 2];
    expect(list(kbins(l, 2, null))).toEqual([[[0], [1, 2]], [[0, 1], [2]]]);
    expect(list(kbins(l, 2, 0))).toEqual([[[0, 1], [2]], [[0, 2], [1]], [[0], [1, 2]]]);
    expect(list(kbins(l, 2, 1))).toEqual([[[0], [1, 2]], [[0], [2, 1]], [[1], [0, 2]], [[1], [2, 0]], [[2], [0, 1]], [[2], [1, 0]]]);
    expect(list(kbins(l, 2, 10))).toEqual([[[0, 1], [2]], [[2], [0, 1]], [[0, 2], [1]], [[1], [0, 2]], [[0], [1, 2]], [[1, 2], [0]]]);
    expect(list(kbins(l, 2, 11))).toEqual([[[0], [1, 2]], [[0, 1], [2]], [[0], [2, 1]], [[0, 2], [1]], [[1], [0, 2]], [[1, 0], [2]], [[1], [2, 0]], [[1, 2], [0]], [[2], [0, 1]], [[2, 0], [1]], [[2], [1, 0]], [[2, 1], [0]]]);
    expect(() => list(kbins(l, 2, 2))).toThrow('ordered must be one of 00, 01, 10 or 11, not 2');
  });
  it('permuteSigns and signedPermutations', () => {
    expect(list(permuteSigns([0, 1, 2]))).toEqual([[0, 1, 2], [0, -1, 2], [0, 1, -2], [0, -1, -2]]);
    expect(str(list(permuteSigns<Expr | number>([x, 0, -2])))).toEqual([['x', 0, -2], ['-x', 0, -2], ['x', 0, 2], ['-x', 0, 2]]);
    expect(list(permuteSigns([1n, 0n]))).toEqual([[1n, 0n], [-1n, 0n]]);
    expect(list(signedPermutations([0, 1, 2]))).toEqual([
      [0, 1, 2], [0, -1, 2], [0, 1, -2], [0, -1, -2], [0, 2, 1], [0, -2, 1], [0, 2, -1], [0, -2, -1],
      [1, 0, 2], [-1, 0, 2], [1, 0, -2], [-1, 0, -2], [1, 2, 0], [-1, 2, 0], [1, -2, 0], [-1, -2, 0],
      [2, 0, 1], [-2, 0, 1], [2, 0, -1], [-2, 0, -1], [2, 1, 0], [-2, 1, 0], [2, -1, 0], [-2, -1, 0],
    ]);
  });
});

describe('type tests and traversal', () => {
  it('iterable', () => {
    const gen = (function* () {
      yield 1;
    })();
    const things: unknown[] = [[1], new Set([1]), gen, new Map([[1, 2]]), '1', 1, x];
    expect(things.map((t) => iterable(t))).toEqual([true, true, true, false, false, false, false]);
    expect(iterable(new Map(), null)).toBe(true);
    expect(iterable(new Map(), String)).toBe(true);
    expect(iterable('no', String)).toBe(false);
    class Never extends NotIterable {
      *[Symbol.iterator]() {
        yield 1;
      }
    }
    expect(iterable(new Never())).toBe(false);
    expect(iterable({ _iterable: true })).toBe(true);
  });
  it('isSequence', () => {
    expect(isSequence([])).toBe(true);
    expect(isSequence(new Set())).toBe(false);
    expect(isSequence('abc')).toBe(false);
    expect(isSequence('abc', String)).toBe(true);
    const generator = (function* () {
      yield* 'abc';
    })();
    expect(isSequence(generator)).toBe(false);
    expect(isSequence(generator, [String, GeneratorType])).toBe(true);
  });
  it('postorderTraversal', () => {
    const e = add(w, mul(add(x, y), z));
    expect(str(list(postorderTraversal(e, true)))).toEqual(['w', 'z', 'x', 'y', 'x + y', 'z*(x + y)', 'w + z*(x + y)']);
    expect(str(list(postorderTraversal([x, [y, 1]])))).toEqual(['x', 'y', 1, ['y', 1], ['x', ['y', 1]]]);
  });
});

describe('ValueMap', () => {
  it('compares keys by value', () => {
    const m = new ValueMap<unknown, number>([[[1, 2], 1]]);
    m.set([1, 2], 3);
    m.set(add(x, 1), 4);
    expect(m.size).toBe(2);
    expect(m.get([1, 2])).toBe(3);
    expect(m.get(add(1, new Sym('x')))).toBe(4);
    expect(m.delete([1, 2])).toBe(true);
    expect(m.delete([1, 2])).toBe(false);
    m.clear();
    expect(m.has(add(x, 1))).toBe(false);
  });
});

describe('reference outputs computed with SymPy', () => {
  const run: Record<string, (args: never) => Iterable<unknown>> = {
    multisetPartitions: ([ms, m]: [number[], number | null]) => multisetPartitions(ms, m),
    partitions: ([n, m, k]: [number, number | null, number | null]) => [...partitions(n, { m, k })].map((p) => [...p]),
    orderedPartitions: ([n, m, s]: [number, number | null, boolean]) => orderedPartitions(n, m, { sort: s }),
    binaryPartitions: (n: number) => binaryPartitions(n),
    generateBell: (n: number) => generateBell(n),
    generateDerangements: (s: number[]) => generateDerangements(s),
    necklaces: ([n, k, f]: [number, number, boolean]) => necklaces(n, k, { free: f }),
    generateOrientedForest: (n: number) => generateOrientedForest(n),
    multisetCombinations: ([s, n]: [string, number]) => multisetCombinations(s, n),
    multisetPermutations: ([s, n]: [string, number | null]) => multisetPermutations(s, n),
    kbins: ([l, k, o]: [number[], number, number | null]) => kbins(l, k, o),
  };
  for (const [name, cases] of Object.entries(REF)) {
    it(name, () => {
      for (const [args, expected] of cases as unknown as [never, unknown][]) {
        expect([...run[name]!(args)], `${name}(${JSON.stringify(args)})`).toEqual(expected);
      }
    });
  }
});

describe('value semantics', () => {
  it('orderedValues follows SymPy ordered', () => {
    const s3 = new Set([3]);
    const d = new Map([[1, 2]]);
    const got = I.orderedValues<unknown>([[2, 1], 'b', 3, x, d, s3, 2.5, 'a']);
    expect(got).toEqual(['a', 'b', 2.5, 3, x, s3, d, [2, 1]]);
    expect(str(I.orderedValues([pow(x, 2), y, x], (e) => -String(e).length))).toEqual(['x**2', 'x', 'y']);
    expect(I.orderedValues([3, 1, 2], [(v) => v % 2], false)).toEqual([2, 3, 1]);
    expect(I.orderedValues([3, 1, 2], [(v) => v % 2])).toEqual([2, 1, 3]);
  });
  it('compareValues and valueEquals', () => {
    expect(I.compareValues(1, 2n)).toBeLessThan(0);
    expect(I.compareValues(true, 0)).toBeGreaterThan(0);
    expect(I.compareValues([1, 2], [1, 3])).toBeLessThan(0);
    expect(I.compareValues([1, 2], [1])).toBeGreaterThan(0);
    expect(I.compareValues(add(x, 0), 2)).toBeGreaterThan(0);
    expect(I.compareValues(1, mul(1, 3))).toBeLessThan(0);
    expect(I.compareValues(x, y)).toBeLessThan(0);
    expect(() => I.compareValues('a', 1)).toThrow(TypeError);
    expect(() => I.compareValues({}, null)).toThrow(TypeError);
    expect(I.valueEquals(new Set([1, 2]), new Set([2, 1]))).toBe(true);
    expect(I.valueEquals(-0, 0)).toBe(true);
    expect(I.valueEquals({}, {})).toBe(false);
    expect(I.valueEquals(undefined, null)).toBe(false);
    expect(I.valueEquals(Symbol.for('a'), Symbol.for('a'))).toBe(true);
    expect(I.valueKey(true)).not.toBe(I.valueKey(false));
    expect(I.defaultSortKeyOf(true)).toEqual(I.defaultSortKeyOf(true));
  });
});
