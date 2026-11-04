// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/prufer.ts (SymPy sympy/combinatorics/prufer.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Prufer } from '../../src';

describe('Prufer', () => {
  it('converts between trees and Prufer sequences', () => {
    const p = new Prufer([
      [0, 3],
      [1, 3],
      [2, 3],
      [3, 4],
      [4, 5],
    ]);
    expect(p.pruferRepr).toEqual([3, 3, 3, 4]);
    expect(p.treeRepr).toEqual([
      [0, 3],
      [1, 3],
      [2, 3],
      [3, 4],
      [4, 5],
    ]);
    expect(p.nodes).toBe(6);
    expect(p.rank).toBe(778n);
    expect(p.next(1).rank).toBe(779n);
    expect(p.prev().rank).toBe(777n);
    expect(String(p)).toBe('Prufer([[0, 3], [1, 3], [2, 3], [3, 4], [4, 5]])');
    expect(new Prufer([0, 0, 0, 0]).size).toBe(1296n);

    const q = new Prufer([1, 0, 0]);
    expect(q.treeRepr).toEqual([
      [1, 2],
      [0, 1],
      [0, 3],
      [0, 4],
    ]);
    expect(q.nodes).toBe(5);
    expect(q.pruferRepr).toEqual([1, 0, 0]);
    expect(new Prufer([1, 3]).treeRepr).toEqual([
      [0, 1],
      [1, 3],
      [2, 3],
    ]);
    const given = new Prufer(
      [
        [0, 1],
        [0, 2],
        [0, 3],
      ],
      4,
    );
    expect(String(given)).toBe('Prufer([[0, 1], [0, 2], [0, 3]], 4)');
    expect(given.pruferRepr).toEqual([0, 0]);
    expect(given.pruferRank()).toBe(0n);
    expect(given.next().treeRepr).toEqual([
      [0, 2],
      [0, 1],
      [1, 3],
    ]);
    const empty = new Prufer([]);
    expect(String(empty)).toBe('Prufer(())');
    expect(empty.treeRepr).toEqual([[0, 1]]);
  });

  it('ranks and unranks', () => {
    expect(String(Prufer.unrank(0, 4))).toBe('Prufer([0, 0])');
    expect(String(Prufer.unrank(5n, 2n))).toBe('Prufer(())');
    const a = new Prufer([
      [0, 1],
      [1, 2],
      [2, 3],
      [1, 4],
    ]);
    expect(a.rank).toBe(36n);
    expect(String(a.prev())).toBe('Prufer([1, 2, 0])');
    expect(a.prev().rank).toBe(35n);
  });

  it('has the static conversions', () => {
    expect(
      Prufer.toPrufer(
        [
          [0, 1],
          [0, 2],
          [0, 3],
        ],
        4,
      ),
    ).toEqual([0, 0]);
    expect(Prufer.toTree([0, 2])).toEqual([
      [0, 1],
      [0, 2],
      [2, 3],
    ]);
    expect(Prufer.toTree([])).toEqual([[0, 1]]);
    expect(Prufer.toTree([0])).toEqual([
      [0, 1],
      [0, 2],
    ]);
    expect(Prufer.edges([1, 2, 3], [2, 4, 5])).toEqual([
      [
        [0, 1],
        [1, 2],
        [1, 3],
        [3, 4],
      ],
      5,
    ]);
    expect(Prufer.edges([0, 1, 2, 3], [1, 4, 5], [1, 4, 6])).toEqual([
      [
        [0, 1],
        [1, 2],
        [1, 4],
        [2, 3],
        [4, 5],
        [4, 6],
      ],
      7,
    ]);
    expect(Prufer.edges([3, 2])).toEqual([[[0, 1]], 2]);
  });

  it('rejects invalid trees', () => {
    expect(() => new Prufer([[1, 2]])).toThrow('Node 0 is missing.');
    expect(() => new Prufer([[2, 3]])).toThrow('Nodes [0, 1] are missing.');
    expect(() => new Prufer([[]])).toThrow('Prufer expects at least one edge in the tree.');
    // SymPy reports the missing label shifted by the smallest label
    expect(() => Prufer.edges([1, 2], [4, 5])).toThrow('Node 4 is missing.');
    expect(() => Prufer.edges([0, 1], [3, 4], [6, 7])).toThrow('Nodes [2, 5] are missing.');
    // SymPy raises a TypeError (min of None)
    expect(() => Prufer.edges([1])).toThrow(RangeError);
  });
});
