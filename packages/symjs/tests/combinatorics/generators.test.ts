// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 combinatorics.generators.
import { expect, it } from 'vitest';
import { PermutationGroup } from '../../src/combinatorics';
import { alternating, cyclic, dihedral, rubik, rubikCubeGenerators, symmetric } from '../../src/combinatorics/generators';

it('generates the Rubik cube groups', () => {
  expect(PermutationGroup(rubikCubeGenerators()).order()).toBe(43252003274489856000n);
  expect(rubik(2).map((g) => g.arrayForm[2])).toEqual([19, 2, 2]);
  expect(() => rubik(1)).toThrow('must be > 1');
});

it('enumerates the symmetric, cyclic, alternating and dihedral groups', () => {
  const s = (g: Iterable<{ toString(): string }>): string[] => [...g].map(String);
  expect(s(symmetric(3))).toEqual(['(2)', '(1 2)', '(2)(0 1)', '(0 1 2)', '(0 2 1)', '(0 2)']);
  expect(s(cyclic(3))).toEqual(['(2)', '(0 1 2)', '(0 2 1)']);
  expect(s(alternating(4))).toEqual(['(3)', '(1 2 3)', '(1 3 2)', '(0 1)(2 3)', '(3)(0 1 2)', '(0 1 3)', '(3)(0 2 1)', '(0 2 3)', '(0 2)(1 3)', '(0 3 1)', '(0 3 2)', '(0 3)(1 2)']);
  expect(s(dihedral(1))).toEqual(['(1)', '(0 1)']);
  expect(s(dihedral(2))).toEqual(['(3)', '(0 1)(2 3)', '(0 2)(1 3)', '(0 3)(1 2)']);
  expect(s(dihedral(3))).toEqual(['(2)', '(0 2)', '(0 1 2)', '(1 2)', '(0 2 1)', '(2)(0 1)']);
});
