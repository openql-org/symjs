// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14 combinatorics.util.
import { expect, it } from 'vitest';
import { Permutation, SymmetricGroup } from '../../src/combinatorics';
import { baseOrdering, checkCyclesAltSym, distributeGensByBase, handlePrecomputedBsgs, orbitsTransversalsFromBsgs, removeGens, strip, strongGensFromDistr } from '../../src/combinatorics/util';

const af = (g: Permutation): number[] => g.arrayForm;
const P = (...a: number[]): Permutation => new Permutation(...a);

it('distributes, removes and recombines strong generators', () => {
  const [b, s] = SymmetricGroup(4).schreierSimsIncremental();
  expect([b, s.map(af)]).toEqual([[0, 1, 2], [[1, 2, 3, 0], [1, 0, 2, 3], [0, 3, 1, 2], [0, 1, 3, 2]]]);
  expect(removeGens(b, s).map(af)).toEqual([[1, 0, 2, 3], [0, 3, 1, 2], [0, 1, 3, 2]]);
  const d = distributeGensByBase(b, s);
  expect(d.map((x) => x.map(af))).toEqual([[[1, 2, 3, 0], [1, 0, 2, 3], [0, 3, 1, 2], [0, 1, 3, 2]], [[0, 3, 1, 2], [0, 1, 3, 2]], [[0, 1, 3, 2]]]);
  const { basicOrbits, transversals } = orbitsTransversalsFromBsgs(b, d);
  expect(basicOrbits).toEqual([[0, 1, 2, 3], [1, 3, 2], [2, 3]]);
  expect(removeGens(b, s, basicOrbits, d).map(af)).toEqual([[1, 0, 2, 3], [0, 3, 1, 2], [0, 1, 3, 2]]);
  expect(handlePrecomputedBsgs(b, s, transversals).basicOrbits).toEqual([[0, 1, 2, 3], [1, 3, 2], [2, 3]]);
  expect(handlePrecomputedBsgs(b, s, undefined, basicOrbits).transversals.map((t) => [...t].map(([k, v]) => [k, af(v)]))).toEqual([
    [[0, [0, 1, 2, 3]], [1, [1, 2, 3, 0]], [2, [2, 3, 0, 1]], [3, [3, 1, 2, 0]]],
    [[1, [0, 1, 2, 3]], [3, [0, 3, 1, 2]], [2, [0, 2, 3, 1]]],
    [[2, [0, 1, 2, 3]], [3, [0, 1, 3, 2]]],
  ]);
  expect(handlePrecomputedBsgs(b, s, transversals, basicOrbits, d).basicOrbits).toEqual([[0, 1, 2, 3], [1, 3, 2], [2, 3]]);
  expect(handlePrecomputedBsgs(b, s).strongGensDistr.map((x) => x.length)).toEqual([4, 2, 1]);
  expect(strongGensFromDistr([[P(0, 1)]]).map(af)).toEqual([[1, 0]]);
  expect(strongGensFromDistr([[P(0, 1, 2)], [P(1, 2), P(0, 1, 2)]]).map(af)).toEqual([[1, 2, 0], [0, 2, 1]]);
  const [h, j] = strip(new Permutation([1, 0, 2, 3]).mul(new Permutation([1, 0, 2, 3])), b, basicOrbits, transversals);
  expect([af(h), j]).toEqual([[0, 1, 2, 3], 4]);
  const [h2, j2] = strip(P(0, 1), [0], [[0]], [new Map([[0, P(1)]])]);
  expect([af(h2), j2]).toEqual([[1, 0], 1]);
});

it('orders bases and finds long prime cycles', () => {
  expect(baseOrdering([2, 0], 4)).toEqual([1, 2, 0, 3]);
  const sized = (p: Permutation): Permutation => p.resize(8);
  expect([P(0, 1, 2, 3, 4), P(1, 2, 3, 4, 5), P(0, 1, 2), P(0, 1, 2, 3, 4, 5)].map((p) => checkCyclesAltSym(sized(p)))).toEqual([true, true, false, false]);
});
