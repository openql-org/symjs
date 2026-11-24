// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/exceptions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.exceptions: GeometryError, and the
 * Undecidable error of sympy.utilities.misc that the geometry raises.
 */

/**
 * An exception raised by geometry entities.
 *
 * @see SymPy `sympy.geometry.exceptions.GeometryError`
 */
export class GeometryError extends RangeError {
  /**
   * Constructs an instance of `GeometryError`.
   *
   * @param message - Explanation of the error.
   */
  constructor(message: string) {
    super(message);
    this.name = 'GeometryError';
  }
}

/**
 * An error indicating that a geometric predicate could not be decided from the given expressions.
 *
 * @see SymPy `sympy.utilities.misc.Undecidable`
 */
export class Undecidable extends RangeError {
  /**
   * Constructs an instance of `Undecidable`.
   *
   * @param message - Explanation of the error.
   */
  constructor(message: string) {
    super(message);
    this.name = 'Undecidable';
  }
}
