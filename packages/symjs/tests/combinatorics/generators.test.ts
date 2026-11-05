// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 combinatorics.generators.
import { expect, it } from 'vitest';
import { PermutationGroup } from '../../src/combinatorics';
import { rubik, rubikCubeGenerators } from '../../src/combinatorics/generators';

it('generates the Rubik cube groups', () => {
  expect(PermutationGroup(rubikCubeGenerators()).order()).toBe(43252003274489856000n);
  expect(rubik(2).map((g) => g.arrayForm[2])).toEqual([19, 2, 2]);
  expect(() => rubik(1)).toThrow('must be > 1');
});
