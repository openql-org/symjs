// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/exceptions.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The errors of the number-field modules (SymPy
 * sympy.polys.numberfields.exceptions).
 */

/**
 * An element is not representable in a module, e.g. in the ZZ-span of a
 * submodule's basis (SymPy ClosureFailure).
 */
export class ClosureFailure extends RangeError {
  constructor(message = '') {
    super(message);
    this.name = 'ClosureFailure';
  }
}

/** A module or order lacks a required structure (SymPy StructureError). */
export class StructureError extends TypeError {
  constructor(message = '') {
    super(message);
    this.name = 'StructureError';
  }
}

/** A module that should contain 1 does not (SymPy MissingUnityError). */
export class MissingUnityError extends StructureError {
  constructor(message = '') {
    super(message);
    this.name = 'MissingUnityError';
  }
}
