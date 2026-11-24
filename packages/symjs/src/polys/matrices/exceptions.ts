// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/exceptions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License
// (see LICENSE).

/**
 * @file The exceptions of the DomainMatrix modules (SymPy
 * sympy.polys.matrices.exceptions).
 */

/**
 * The base exception for domain-matrix operations.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMError`
 */
export class DMError extends TypeError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMError';
  }
}

/**
 * Indicates malformed input to a domain-matrix operation.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMBadInputError`
 */
export class DMBadInputError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMBadInputError';
  }
}

/**
 * Indicates incompatible or unsuitable coefficient domains.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMDomainError`
 */
export class DMDomainError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMDomainError';
  }
}

/**
 * Indicates that the coefficient domain is not a field for an operation requiring division.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMNotAField`
 */
export class DMNotAField extends DMDomainError {
  /**
   * Constructs a new `DMNotAField`.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMNotAField';
  }
}

/**
 * Indicates incompatible dense and sparse representations.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMFormatError`
 */
export class DMFormatError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMFormatError';
  }
}

/**
 * Indicates a singular matrix or matrix equation without a unique solution.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMNonInvertibleMatrixError`
 */
export class DMNonInvertibleMatrixError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMNonInvertibleMatrixError';
  }
}

/**
 * Indicates that the rank is insufficient for the requested matrix operation.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMRankError`
 */
export class DMRankError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMRankError';
  }
}

/**
 * Indicates that the matrix dimensions do not satisfy an operation’s requirements.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMShapeError`
 */
export class DMShapeError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMShapeError';
  }
}

/**
 * Indicates that an operation requiring a square matrix received a rectangular one.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMNonSquareMatrixError`
 */
export class DMNonSquareMatrixError extends DMShapeError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMNonSquareMatrixError';
  }
}

/**
 * Indicates an invalid value supplied to a domain-matrix operation.
 *
 * @see SymPy `sympy.polys.matrices.exceptions.DMValueError`
 */
export class DMValueError extends DMError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param message - Message describing the error.
   */
  constructor(message = '') {
    super(message);
    this.name = 'DMValueError';
  }
}
