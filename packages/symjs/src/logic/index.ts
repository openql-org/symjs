// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Propositional logic (SymPy sympy.logic): the boolean functions not in
 * the core, normal forms, two-level minimization and satisfiability.
 * And, Or, Not and Xor are the core's (core/boolalg).
 */

export type { BoolLike, LogicEvalOptions, LogicOpName, LogicGateName } from './boolalg';
export {
  LogicOp,
  LogicGate,
  Implies,
  Equivalent,
  Nand,
  Nor,
  Xnor,
  ITE,
  Exclusive,
  asBoolean,
  isLiteral,
  conjuncts,
  disjuncts,
  binarySymbols,
} from './boolalg';
export {
  toNnf,
  isNnf,
  isCnf,
  isDnf,
  isAnf,
  toAnf,
  eliminateImplications,
  distributeAndOverOr,
  distributeOrOverAnd,
  distributeXorOverAnd,
  toIntRepr,
  termToInteger,
  integerToTerm,
  truthTable,
  gateinputcount,
} from './normalforms';
export type { TermSpec, SimplifyLogicOptions, NormalFormOptions } from './minimize';
export { SOPform, POSform, ANFform, anfCoeffs, boolMinterm, boolMaxterm, boolMonomial, simplifyLogic, toCnf, toDnf, boolMap } from './minimize';
export type { SatisfiableOptions } from './inference';
export { satisfiable, valid, entails, plTrue, literalSymbol, PropKB, booleanEquals } from './inference';
