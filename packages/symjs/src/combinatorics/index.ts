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
export { Polyhedron, cube, dodecahedron, icosahedron, octahedron, tetrahedron } from './polyhedron';
export { alternating, cyclic, dihedral, symmetric } from './generators';
export { groupsCount, isAbelianNumber, isCyclicNumber, isNilpotentNumber } from './groupnumbers';
export { SchurNumber, SchurNumberNode, schurPartition } from './schurnumber';
export { FreeGroup, FreeGroupElement, freeGroup, vfreeGroup, xfreeGroup } from './freegroups';
export type { FreeGroupSymbols } from './freegroups';
export { CosetLimitExceeded, CosetTable, cosetEnumerationC, cosetEnumerationR, modifiedCosetEnumerationR } from './cosettable';
export type { CosetEnumerationOptions, CosetGroup, CosetRow } from './cosettable';
export { RewritingRulesExceeded, RewritingSystem, State, StateMachine } from './rewritingsystem';
export type { RewritingGroup, StateName } from './rewritingsystem';
export {
  FpGroup,
  FpSubgroup,
  GroupHomomorphism,
  defineSchreierGenerators,
  descendantSubgroups,
  eliminationTechnique1,
  eliminationTechnique2,
  firstInClass,
  fpGroup,
  lowIndexSubgroups,
  reidemeisterPresentation,
  reidemeisterRelators,
  reidemeisterRewrite,
  simplifyPresentation,
  tryDescendant,
  vfpGroup,
  xfpGroup,
} from './fpgroups';
export type { CosetStrategy, FpCosetOptions, GroupElement, HomomorphismGroup } from './fpgroups';
export { blockHomomorphism, groupHomomorphism, groupIsomorphism, isIsomorphic, orbitHomomorphism } from './homomorphisms';
export type { IsomorphismResult } from './homomorphisms';
export { Collector, PolycyclicGroup } from './pcgroups';
export type { PcRelatorValue, PcSyllable } from './pcgroups';
