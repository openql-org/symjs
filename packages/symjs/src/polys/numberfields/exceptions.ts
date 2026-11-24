// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/exceptions.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The errors of the number-field modules (SymPy
 * sympy.polys.numberfields.exceptions).
 */

/**
 * Indicates that an element has no integral coordinate representation in the specified module.
 *
 * @see SymPy `sympy.polys.numberfields.exceptions.ClosureFailure`
 * @example
 * ```ts
 * import { DomainMatrix, Poly, PowerBasis, ZZ, ex, toCol } from '@symjs/symjs';
 *
 * const A = new PowerBasis(Poly.from(ex`x**4 + x**3 + x**2 + x + 1`));
 * const B = A.submoduleFromMatrix(DomainMatrix.eye(4, ZZ).scalarmul(ex`2`));
 * B.represent(A.call(toCol([2, 4, 6, 8]))).toList(); // => [[1], [2], [3], [4]]
 * ```
 */
export class ClosureFailure extends RangeError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'ClosureFailure';
  }
}

/**
 * A module or order lacks a required structure.
 *
 * @see SymPy `sympy.polys.numberfields.exceptions.StructureError`
 */
export class StructureError extends TypeError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'StructureError';
  }
}

/**
 * A module that should contain 1 does not.
 *
 * @see SymPy `sympy.polys.numberfields.exceptions.MissingUnityError`
 */
export class MissingUnityError extends StructureError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'MissingUnityError';
  }
}
