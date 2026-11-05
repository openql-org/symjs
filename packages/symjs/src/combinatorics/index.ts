// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.combinatorics: permutations (Permutation, Cycle), permutation groups (PermutationGroup, named groups, cosets), partitions, Prufer sequences, subsets and Gray codes.
 */

export {
  AppliedPermutation,
  Cycle,
  Perm,
  Permutation,
  afCommutesWith,
  afInvert,
  afParity,
  afPow,
  afRmul,
  afRmuln,
  permutationLatex,
  permutationRepr,
  permutationStr,
} from './permutations';
export type { CycleArgs, PermutationInput, PermutationOptions, PermutationPrintOptions, RandomOptions } from './permutations';
export { GrayCode, binToGray, getSubsetFromBitstring, grayToBin, graycodeSubsets, randomBitstring } from './graycode';
export type { GrayCodeOptions } from './graycode';
export { IntegerPartition, Partition, RGSEnum, RGSGeneralized, RGSRank, RGSUnrank, randomIntegerPartition } from './partitions';
export type { IntegerPartitionInput, PartitionBlock, PartitionElement } from './partitions';
export { Prufer } from './prufer';
export type { PruferEdge } from './prufer';
export { Subset, ksubsets } from './subsets';
export { Coset, PermutationGroup, SymmetricPermutationGroup } from './permgroups';
export type { OrbitAction, PermutationGroupOptions } from './permgroups';
export { AbelianGroup, AlternatingGroup, CyclicGroup, DihedralGroup, RubikGroup, SymmetricGroup } from './namedgroups';
export { DirectProduct } from './groupconstructs';
export { Polyhedron } from './polyhedron';
