// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 combinatorics.group_constructs.
import { expect, it } from 'vitest';
import { CyclicGroup, DihedralGroup, DirectProduct, Permutation, PermutationGroup } from '../../src/combinatorics';

it('forms direct products', () => {
  expect(DirectProduct(CyclicGroup(2), DihedralGroup(3)).generators.map((g) => g.arrayForm)).toEqual([[1, 0, 2, 3, 4], [0, 1, 3, 4, 2], [0, 1, 4, 3, 2]]);
  expect(DirectProduct(PermutationGroup(new Permutation(1)), PermutationGroup(new Permutation(1))).generators.map((g) => g.arrayForm)).toEqual([[0, 1, 2, 3]]);
});
