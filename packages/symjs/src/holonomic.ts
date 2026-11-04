// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/holonomic`: holonomic functions and
 * sequences (SymPy sympy.holonomic): differential and recurrence operators,
 * their closure operations, series, recurrences and conversions from and to
 * expressions, hypergeometric and Meijer G-functions.
 */

// every entry point brings the core with its registrations
import './core';

export {
  DifferentialOperatorAlgebra,
  DifferentialOperator,
  DifferentialOperators,
  HolonomicFunction,
  fromHyper,
  fromMeijerg,
  exprToHolonomic,
} from './holonomic/holonomic';
export type {
  DifferentialOperand,
  InitialConditions,
  InitialConditionsLike,
  SequenceSolution,
  ExprToHolonomicOptions,
} from './holonomic/holonomic';
export { RecurrenceOperatorAlgebra, RecurrenceOperator, RecurrenceOperators, HolonomicSequence } from './holonomic/recurrence';
export type { RecurrenceOperand } from './holonomic/recurrence';
export { BaseHolonomicError, SeriesExpansionError, NotPowerSeriesError, NotHolonomicError, SingularityError, NotHyperSeriesError } from './holonomic/holonomicerrors';
