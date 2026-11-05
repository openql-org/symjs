// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The linear real arithmetic theory of SymPy
 * (sympy.logic.algorithms.lra_theory). Only the exception raised for input
 * the theory cannot handle is ported so far; the LRASolver itself is not.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import { NotImplementedError } from '../../core/errors';

/**
 * Input that the linear real arithmetic solver cannot handle (SymPy
 * UnhandledInput): valid input outside the methods implemented, hence a
 * NotImplementedError.
 */
export class UnhandledInput extends NotImplementedError {
  constructor(message: string) {
    super(message);
    this.name = 'UnhandledInput';
  }
}
