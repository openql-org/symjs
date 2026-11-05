// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 combinatorics.polyhedron.
import { expect, it } from 'vitest';
import { str } from '../../src';
import { Permutation, Polyhedron } from '../../src/combinatorics';

const s = (xs: readonly { toString(): string }[]): string[] => xs.map(String);

it('moves its corners by the permutation group', () => {
  const p = new Polyhedron(['a', 'b', 'c'], [[1, 2, 0]], [new Permutation(0, 1, 2)]);
  expect([s(p.corners), str(p.faces), str(p.edges), p.size, str(p.pgroup)]).toEqual([['a', 'b', 'c'], '{(0, 1, 2)}', '{(0, 1), (0, 2), (1, 2)}', 3, 'PermutationGroup([\n    (0 1 2)])']);
  p.rotate(0);
  expect([s(p.corners), p.arrayForm, p.cyclicForm]).toEqual([['b', 'c', 'a'], [1, 2, 0], [[0, 1, 2]]]);
  p.rotate(new Permutation(0, 1, { size: 3 }));
  expect([s(p.corners), p.arrayForm]).toEqual([['c', 'b', 'a'], [2, 1, 0]]);
  p.reset();
  expect([s(p.corners), s(p.vertices)]).toEqual([['a', 'b', 'c'], ['a', 'b', 'c']]);
  expect(() => p.rotate(new Permutation(0, 1, 2, 3))).toThrow('sizes differ');
  expect(p.withArgs(p.args).key).toBe(p.key);
});

it('defaults to the trivial group and checks the sizes', () => {
  const q = new Polyhedron(['a', 'b']);
  expect([str(q.pgroup), str(q.faces), str(q.edges), str(q)]).toEqual(['PermutationGroup([\n    (1)])', 'EmptySet', 'EmptySet', 'Polyhedron((a, b), (), ())']);
  expect(() => new Polyhedron(['a', 'b'], [], [new Permutation(0, 1, 2)])).toThrow('unequal to number of corners');
  const t = new Polyhedron([1, 2, 3, 4], [[0, 1, 2], [0, 3, 2], [2, 1, 3]]);
  expect([str(t.faces), str(t.edges)]).toEqual(['{(0, 1, 2), (0, 2, 3), (1, 2, 3)}', '{(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}']);
});
