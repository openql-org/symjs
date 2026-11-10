// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Presentations of permutation groups (after SymPy 1.14 test_perm_groups.py test_presentation): a
// presentation defines a group of the same order, a strong presentation has one generator per
// strong generator.
import { describe, expect, it } from 'vitest';
import { AlternatingGroup, CyclicGroup, DihedralGroup, Permutation, PermutationGroup, SymmetricGroup } from '../../src/combinatorics';

const presents = (P: PermutationGroup): boolean => String(P.presentation().order()) === String(P.order());
const presentsStrongly = (P: PermutationGroup): boolean => {
  const G = P.strongPresentation();
  return G.generators.length === P.strongGens.length && String(G.order()) === String(P.order());
};

describe('presentations', () => {
  it('SymPy test_presentation', () => {
    expect(presents(new PermutationGroup(new Permutation(0, 1, 5, 2).call(3, 7, 4, 6), new Permutation(0, 3, 5, 4).call(1, 6, 2, 7)))).toBe(true);
    expect(presents(AlternatingGroup(5))).toBe(true);
    expect(presents(SymmetricGroup(5))).toBe(true);
    expect(presentsStrongly(new PermutationGroup([new Permutation(0, 3, 1, 2), new Permutation(3).call(0, 1), new Permutation(0, 1).call(2, 3)]))).toBe(true);
    expect(presentsStrongly(DihedralGroup(6))).toBe(true);
    expect(presentsStrongly(new PermutationGroup(new Permutation(4, 5), new Permutation(0, 1).call(2, 3), new Permutation(0, 2).call(3, 1)))).toBe(true);
  });
  it('the first relator is a power of the first new generator, not of the last strong generator (SymPy: order oo)', () => {
    const G = new PermutationGroup([new Permutation(0, 5).call(3, 4), new Permutation(5).call(3, 4), new Permutation(0, 5)]);
    expect(presentsStrongly(G)).toBe(true);
  });
  it('a level where the orbit grows again (SymPy raises IndexError in block_homomorphism)', () => {
    const G = new PermutationGroup([new Permutation(1, 5).call(3, 4), new Permutation(5).call(0, 4).call(2, 3), new Permutation(5).call(0, 2).call(3, 4)]);
    expect(presentsStrongly(G)).toBe(true);
    const H = new PermutationGroup([new Permutation(5).call(0, 1), new Permutation(5).call(0, 1).call(2, 3), new Permutation(2, 4).call(3, 5)]);
    expect(presentsStrongly(H)).toBe(true);
  });
  it('more groups', () => {
    for (const P of [SymmetricGroup(4), AlternatingGroup(4), CyclicGroup(6), DihedralGroup(5), AlternatingGroup(5)]) expect(presentsStrongly(P)).toBe(true);
    // cached (not for a group with one generator, like SymPy)
    const D = DihedralGroup(4);
    expect(D.presentation()).toBe(D.presentation());
    expect(String(new PermutationGroup([new Permutation(2)]).presentation())).toBe('<fp group on the generators ()>');
  });
});
