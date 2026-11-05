// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.assumptions beyond core/refine.ts: the CNF of the assumption system, satask with the class
 * facts and the known facts between predicates, the assumption wrappers and the helpers of lra_satask (exported by
 * `@symjs/symjs/logic`). The matrix handlers of ask (`handlers/matrices.ts`) register on load and are loaded by
 * `@symjs/symjs/matrices`.
 */

export { allargs, anyarg, exactlyonearg, ClassFactRegistry, classFactRegistry, isClassInstance } from './sathandlers';
export type { FactHandler, MultiFactHandler } from './sathandlers';
export { Literal, OR, AND, toNNF, distributeANDOverOR, CNF, EncodedCNF, predicateLikeKey } from './cnf';
export type { PredicateLike, NNF, CompositeMap, Clause } from './cnf';
export {
  getCompositePredicates,
  getKnownFacts,
  getNumberFacts,
  getMatrixFacts,
  generateKnownFactsDict,
  getKnownFactsKeys,
  singleFactLookup,
  askFullInference,
  predicateNamed,
} from './facts';
export type { KnownFactsDict } from './facts';
export { getAllKnownFacts, getAllKnownMatrixFacts, getAllKnownNumberFacts, getKnownFactsDict } from './askgenerated';
export { satask, checkSatisfiability, extractPredargs, findSymbols, getRelevantClsfacts, getAllRelevantFacts } from './satask';
export type { SataskOptions } from './satask';
export { extractPredFromOldAssum } from './lrasatask';
export { isInfinite, isExtendedReal, isExtendedNonnegative } from './wrapper';
export { BinaryRelation } from './relation/binrel';
export type { BinaryRelationHandler, BinaryRelationOptions } from './relation/binrel';
