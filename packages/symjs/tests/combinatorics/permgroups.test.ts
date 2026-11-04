// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected group orders, orbits and stabilizers from SymPy 1.14.
import { describe, expect, it } from 'vitest';
import { Permutation, PermutationGroup, SymmetricGroup, AlternatingGroup, CyclicGroup, DihedralGroup } from '../../src/combinatorics';

describe('stabilizer chains', () => {
  it.each([[1, 1n], [2, 2n], [3, 6n], [4, 24n], [5, 120n], [8, 40320n], [10, 3628800n]] as const)('computes S_%i without enumerating its elements', (n, order) => {
    const g = SymmetricGroup(n);
    expect(g.order()).toBe(order); expect(g.order()).toBe(order);
    expect(g.isSymmetric).toBe(true); expect(g.isTransitive()).toBe(true);
    expect(g.isAbelian).toBe(n <= 2);
    expect(g.contains(new Permutation(Array.from({ length: n }, (_, i) => n - i - 1)))).toBe(true);
    expect(g.basicOrbits.reduce((p, o) => p * BigInt(o.length), 1n)).toBe(order);
    expect(g.pointwiseStabilizer(g.base).order()).toBe(1n);
  });
  it('distinguishes subgroups and sifts permutations that move a base point outside its orbit', () => {
    const a = AlternatingGroup(4), s = SymmetricGroup(4);
    expect(a.order()).toBe(12n); expect(a.isAlternating).toBe(true); expect(a.isSymmetric).toBe(false);
    expect(s.isAlternating).toBe(false);
    expect(a.isSubgroup(s)).toBe(true); expect(s.isSubgroup(a)).toBe(false);
    expect(a.contains(new Permutation([1, 0, 2, 3]))).toBe(false);
    const cyclic = CyclicGroup(4);
    expect(cyclic.contains(new Permutation([1, 0, 2, 3]))).toBe(false);
    const small = PermutationGroup(new Permutation([1, 0, 2]));
    expect(small.contains(new Permutation([2, 1, 0]))).toBe(false);
    expect(small.contains(new Permutation([1, 0]))).toBe(false);
    expect(small.contains(new Permutation([1, 0]), false)).toBe(true);
    expect(small.contains(new Permutation([0, 1, 2, 3]), false)).toBe(false);
    expect(PermutationGroup(new Permutation([1, 0])).isSubgroup(small)).toBe(false);
    expect(PermutationGroup(new Permutation([1, 0])).isSubgroup(small, false)).toBe(true);
  });
  it('computes orbits, representatives and point stabilizers', () => {
    const s = SymmetricGroup(4);
    expect([...s.orbit(2)].sort((a, b) => a - b)).toEqual([0, 1, 2, 3]);
    expect(new Set(s.orbitTransversal(2).map((g) => g.arrayForm[2]))).toEqual(new Set([0, 1, 2, 3]));
    const stabilizer = s.stabilizer(2);
    expect(stabilizer.order()).toBe(6n);
    expect(stabilizer.generators.every((g) => g.arrayForm[2] === 2)).toBe(true);
    expect(stabilizer.isTransitive()).toBe(false); expect(stabilizer.isTransitive(false)).toBe(true);
    expect(stabilizer.orbits().map((o) => [...o].sort((a, b) => a - b)).sort((a, b) => String(a).localeCompare(String(b)))).toEqual([[0, 1, 3], [2]]);
    const two = PermutationGroup(new Permutation([1, 0, 3, 2]));
    expect(two.isTransitive(false)).toBe(false);
    expect(() => s.orbit(4)).toThrow('outside'); expect(() => s.stabilizer(-1)).toThrow('outside');
    expect(() => s.orbit(0.5)).toThrow('outside');
  });
  it('enumerates each element once and respects closure', () => {
    const g = DihedralGroup(4), elements = [...g.generateSchreierSims()];
    expect(elements).toHaveLength(8); expect(new Set(elements.map((p) => p.key)).size).toBe(8);
    for (const p of elements) { expect(g.contains(p)).toBe(true); for (const q of elements) expect(g.contains(p.mul(q))).toBe(true); }
    expect(g.withArgs(g.args).equals(g)).toBe(true);
  });
  it('handles trivial groups, mixed degrees and repeated generators', () => {
    const g = PermutationGroup();
    expect(g.degree).toBe(0); expect(g.order()).toBe(1n); expect(g.isTrivial).toBe(true);
    expect(g.contains(new Permutation([]))).toBe(true);
    expect(g.isTransitive()).toBe(true); expect(g.isTransitive(false)).toBe(true);
    expect(g.isAlternating).toBe(true); expect(g.isSymmetric).toBe(true);
    expect([...g.generateSchreierSims()]).toHaveLength(1);
    expect(CyclicGroup(3).stabilizer(0).order()).toBe(1n);
    const p = new Permutation([1, 0]);
    expect(PermutationGroup([p, p, new Permutation([0, 1, 2])]).order()).toBe(2n);
    expect(SymmetricGroup(2).isAlternating).toBe(false);
  });
});
