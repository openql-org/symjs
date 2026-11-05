// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference values from SymPy 1.14 combinatorics.named_groups.
import { expect, it } from 'vitest';
import { AbelianGroup, AlternatingGroup, CyclicGroup, DihedralGroup, RubikGroup, SymmetricGroup } from '../../src/combinatorics';
import type { PermutationGroup } from '../../src/combinatorics';

const gens = (G: PermutationGroup): number[][] => G.generators.map((g) => g.arrayForm);

it.each([1, 2, 3, 4, 5])('constructs named groups for n=%i', (n) => {
  expect(CyclicGroup(n).order()).toBe(BigInt(n));
  expect(CyclicGroup(n).isAbelian).toBe(true);
  expect(DihedralGroup(n).order()).toBe(BigInt(n * 2));
  expect(DihedralGroup(n).isAbelian).toBe(n <= 2);
  expect(DihedralGroup(n).degree).toBe(n < 3 ? n * 2 : n);
  expect(AlternatingGroup(n).order()).toBe([1n, 1n, 3n, 12n, 60n][n - 1]);
  // SymPy: AlternatingGroup(1) and (2) are the trivial group of degree 1, which is_symmetric, not is_alternating
  expect(AlternatingGroup(n).isAlternating).toBe(n >= 3);
});

it('uses SymPy generators and properties', () => {
  const groups = [AlternatingGroup(1), AlternatingGroup(2), AlternatingGroup(3), AlternatingGroup(6), DihedralGroup(1), DihedralGroup(2), SymmetricGroup(1), SymmetricGroup(2), AbelianGroup(3), AbelianGroup(2, 2)];
  expect(groups.map((G) => [G.order(), gens(G)])).toEqual([
    [1n, [[0]]],
    [1n, [[0]]],
    [3n, [[1, 2, 0]]],
    [360n, [[1, 2, 0, 3, 4, 5], [0, 2, 3, 4, 5, 1]]],
    [2n, [[1, 0]]],
    [4n, [[1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]]],
    [1n, [[0]]],
    [2n, [[1, 0]]],
    [3n, [[1, 2, 0]]],
    [4n, [[1, 0, 2, 3], [0, 1, 3, 2]]],
  ]);
  const props = [AlternatingGroup(1), AlternatingGroup(4), AlternatingGroup(5), SymmetricGroup(2), SymmetricGroup(5), DihedralGroup(4), DihedralGroup(6)];
  expect(props.map((G) => [G.isAlternating, G.isSymmetric, G.isNilpotent, G.isSolvable])).toEqual([
    [false, true, true, true],
    [true, false, false, true],
    [true, false, false, false],
    [false, true, true, true],
    [false, true, false, false],
    [false, false, true, true],
    [false, false, false, true],
  ]);
  expect(RubikGroup(2).order()).toBe(3674160n);
});

it('requires positive integer parameters', () => {
  // SymPy CyclicGroup(0) reports order zero, which violates the group axioms.
  // symjs deliberately rejects this invalid parameter instead.
  for (const f of [AlternatingGroup, CyclicGroup, DihedralGroup, SymmetricGroup]) {
    for (const n of [0, -1, 1.5, Infinity]) expect(() => f(n)).toThrow('positive integer');
  }
  expect(() => RubikGroup(1)).toThrow('greater than 1');
  expect(() => RubikGroup(2.5)).toThrow('greater than 1');
});
