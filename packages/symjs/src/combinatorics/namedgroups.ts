// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 combinatorics/named_groups.py, BSD-3-Clause; see LICENSE.
import { Permutation } from './permutations';
import { PermutationGroup, type PermutationGroupNode } from './permgroups';
const positive = (n: number): void => { if (!Number.isSafeInteger(n) || n < 1) throw new RangeError('group size must be a positive integer'); };
const cycle = (n: number): Permutation => new Permutation(Array.from({ length: n }, (_, i) => (i + 1) % n));
/** The cyclic group acting regularly on n points. */
export function CyclicGroup(n: number): PermutationGroupNode { positive(n); return PermutationGroup(cycle(n)); }
/** The full symmetric group on n points. */
export function SymmetricGroup(n: number): PermutationGroupNode {
  positive(n); if (n === 1) return CyclicGroup(1);
  return PermutationGroup(cycle(n), new Permutation([1, 0, ...Array.from({ length: n - 2 }, (_, i) => i + 2)]));
}
/** The even permutations on n points (SymPy's degree-one representation for n < 3). */
export function AlternatingGroup(n: number): PermutationGroupNode {
  positive(n); if (n < 3) return CyclicGroup(1);
  const gs = Array.from({ length: n - 2 }, (_, k) => new Permutation(Array.from({ length: n }, (_, i) => i === 0 ? 1 : i === 1 ? k + 2 : i === k + 2 ? 0 : i)));
  return PermutationGroup(gs);
}
/** Dihedral group; n=1 and n=2 use faithful actions of degree 2 and 4. */
export function DihedralGroup(n: number): PermutationGroupNode {
  positive(n);
  if (n === 1) return CyclicGroup(2);
  if (n === 2) return PermutationGroup(new Permutation([1, 0, 3, 2]), new Permutation([2, 3, 0, 1]));
  return PermutationGroup(cycle(n), new Permutation(Array.from({ length: n }, (_, i) => n - i - 1)));
}
