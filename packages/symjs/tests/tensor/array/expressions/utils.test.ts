// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { NoMatch, Rational, Sym } from '../../../../src/core';
import { Permutation } from '../../../../src/combinatorics';
import { applyPermutationToList, applyRecursivelyOverNestedLists, buildPushIndicesDownFuncTransformation, buildPushIndicesUpFuncTransformation, getArgindex, getContractionLinks, getDiagonalIndices, getMappingFromSubranks, sortContractionIndices } from '../../../../src/tensor/array/expressions/utils';

it('maps tensor-product axes and bidirectional contraction links', () => {
  expect(getMappingFromSubranks([2, 0, 3])).toEqual(new Map([[0, [0, 0]], [1, [0, 1]], [2, [2, 0]], [3, [2, 1]], [4, [2, 2]]]));
  expect(getMappingFromSubranks([]).size).toBe(0);
  const args = ['A', 'B'];
  expect(getContractionLinks(args, [2, 2], [0, 2], [1, 3])).toEqual([args, new Map([[0, new Map([[0, [1, 0]], [1, [1, 1]]])], [1, new Map([[0, [0, 0]], [1, [0, 1]]])]])]);
  expect(getContractionLinks(args, [2, 2], [0, 1, 2])[1].size).toBe(0);
  expect(() => getContractionLinks(args, [2, 2], [0, 4])).toThrow(RangeError);
  expect(sortContractionIndices([[5, 2], [3, 0]])).toEqual([[0, 3], [2, 5]]);
});
it('collects repeated symbolic indices, skipping fixed integer coordinates', () => {
  const i = new Sym('i'), j = new Sym('j'), one = Rational.of(1), half = Rational.of(1, 2);
  expect(getDiagonalIndices([i, one, j, i, one, j])).toEqual([[[0, 3], [2, 5]], [one, one, i, j]]);
  expect(getDiagonalIndices([half, half, i])).toEqual([[[0, 1]], [i, half]]);
  expect(getDiagonalIndices([])).toEqual([[], []]);
  expect(getArgindex([i, new Set([j])], i)).toBe(0);
  expect(getArgindex([i, new Set([j])], new Sym('j'))).toBe(1);
  expect(getArgindex([1, new Set([2])], 2)).toBe(1);
  expect(() => getArgindex<unknown>([i], 1)).toThrow(RangeError);
  expect(() => getArgindex([i], j)).toThrow(RangeError);
});
it('pushes nested axes through disjoint and consecutive contractions', () => {
  for (const contracted of [[], [0], [1, 2, 5, 6], [0, 1, 2], [2, 5]]) {
    const up = buildPushIndicesUpFuncTransformation(contracted), down = buildPushIndicesDownFuncTransformation(contracted);
    for (let axis = 0; axis < 12; axis++) {
      if (contracted.includes(axis)) expect(up(axis)).toBe(NoMatch);
      else expect(down(Number(up(axis)))).toBe(axis);
    }
  }
  expect(applyRecursivelyOverNestedLists((n: number) => n + 1, [0, [1, [2]], []])).toEqual([1, [2, [3]], []]);
});
it('scatters permutations rather than applying their inverse', () => {
  expect(applyPermutationToList([1, 2, 0], ['i', 'j', 'k'])).toEqual(['k', 'i', 'j']);
  expect(applyPermutationToList(new Permutation([1, 0]), ['i', 'j'])).toEqual(['j', 'i']);
  expect(applyPermutationToList([], [])).toEqual([]);
  for (const p of [[0], [0, 0], [-1, 0], [0.5, 1], [0, 2]]) expect(() => applyPermutationToList(p, [1, 2])).toThrow(RangeError);
});
