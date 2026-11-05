// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/exceptions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License
// (see LICENSE).

/**
 * @file The exceptions of the DomainMatrix modules (SymPy
 * sympy.polys.matrices.exceptions).
 */

/** The base class of the DomainMatrix errors (SymPy DMError); a TypeError like the polynomial errors. */
export class DMError extends TypeError {
  constructor(message = '') {
    super(message);
    this.name = 'DMError';
  }
}

/** Malformed input (SymPy DMBadInputError). */
export class DMBadInputError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMBadInputError';
  }
}

/** Mismatched or unsuitable domains (SymPy DMDomainError). */
export class DMDomainError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMDomainError';
  }
}

/** An operation that needs a field (SymPy DMNotAField). */
export class DMNotAField extends DMDomainError {
  constructor(message = '') {
    super(message);
    this.name = 'DMNotAField';
  }
}

/** Mismatched dense and sparse formats (SymPy DMFormatError). */
export class DMFormatError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMFormatError';
  }
}

/** A singular matrix where an invertible one is needed (SymPy DMNonInvertibleMatrixError). */
export class DMNonInvertibleMatrixError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMNonInvertibleMatrixError';
  }
}

/** A matrix of the wrong rank (SymPy DMRankError). */
export class DMRankError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMRankError';
  }
}

/** Mismatched shapes (SymPy DMShapeError). */
export class DMShapeError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMShapeError';
  }
}

/** A nonsquare matrix where a square one is needed (SymPy DMNonSquareMatrixError). */
export class DMNonSquareMatrixError extends DMShapeError {
  constructor(message = '') {
    super(message);
    this.name = 'DMNonSquareMatrixError';
  }
}

/** An invalid value (SymPy DMValueError). */
export class DMValueError extends DMError {
  constructor(message = '') {
    super(message);
    this.name = 'DMValueError';
  }
}
