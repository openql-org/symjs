// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy's exception classes and seterr.
 */

/** A value that cannot be converted to an expression (SymPy SympifyError). */
export class SympifyError extends TypeError {
  constructor(
    message: string,
    /** The value that failed to convert. */
    readonly value?: unknown,
  ) {
    super(message);
    this.name = 'SympifyError';
  }
}

/** A series or limit computation met a pole (SymPy PoleError). */
export class PoleError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'PoleError';
  }
}

/** Numerical evaluation could not reach the requested precision (SymPy PrecisionExhausted). */
export class PrecisionExhausted extends Error {
  constructor(message = 'precision exhausted') {
    super(message);
    this.name = 'PrecisionExhausted';
  }
}

/** @internal Global error settings (SymPy _errdict). */
export const errorSettings = { divide: false };

/**
 * SymPy seterr(divide): with `divide: true`, 0/0 throws a RangeError
 * ("Indeterminate 0/0") instead of giving nan.
 */
export function seterr(opts: { divide?: boolean } = {}): void {
  errorSettings.divide = Boolean(opts.divide);
}

/** The equations are not linear in the unknowns (SymPy NonlinearError). */
export class NonlinearError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'NonlinearError';
  }
}

/**
 * The input is valid but the implemented methods cannot handle it (SymPy
 * NotImplementedError): an equation dsolve or solve cannot solve, a series
 * point or a set operation not supported yet. Unlike invalid input, the
 * same request may succeed in a later version.
 */
export class NotImplementedError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'NotImplementedError';
  }
}

/** A feature whose entry point has not been imported (e.g. simplify before importing '@symjs/symjs/simplify'). */
export class NotLoadedError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'NotLoadedError';
  }
}

/** The expression is not a polynomial as required, or a polynomial operation is not defined for it (SymPy PolynomialError). */
export class PolynomialError extends TypeError {
  constructor(message: string) {
    super(message);
    this.name = 'PolynomialError';
  }
}

/** The coefficients are outside the domain an algorithm needs, e.g. rational coefficients (SymPy DomainError). */
export class DomainError extends TypeError {
  constructor(message: string) {
    super(message);
    this.name = 'DomainError';
  }
}

/** An exact division that leaves a remainder (SymPy ExactQuotientFailed). */
export class ExactQuotientFailed extends RangeError {
  constructor(message: string) {
    super(message);
    this.name = 'ExactQuotientFailed';
  }
}

/** An element without an inverse (SymPy NotInvertible). */
export class NotInvertible extends RangeError {
  constructor(message: string) {
    super(message);
    this.name = 'NotInvertible';
  }
}

/** A matrix without the property an operation needs (SymPy MatrixError). */
export class MatrixError extends RangeError {
  constructor(message: string) {
    super(message);
    this.name = 'MatrixError';
  }
}

/** The shapes of matrices do not match (SymPy ShapeError). */
export class ShapeError extends MatrixError {
  constructor(message = 'Matrices are not aligned') {
    super(message);
    this.name = 'ShapeError';
  }
}

/** A square matrix is required (SymPy NonSquareMatrixError, a ShapeError). */
export class NonSquareMatrixError extends ShapeError {
  constructor(message = 'Matrix must be square') {
    super(message);
    this.name = 'NonSquareMatrixError';
  }
}

/** The matrix is singular (SymPy NonInvertibleMatrixError). */
export class NonInvertibleMatrixError extends MatrixError {
  constructor(message = 'Matrix det == 0; not invertible.') {
    super(message);
    this.name = 'NonInvertibleMatrixError';
  }
}

/** The matrix is not positive definite (SymPy NonPositiveDefiniteMatrixError). */
export class NonPositiveDefiniteMatrixError extends MatrixError {
  constructor(message = 'Matrix must be positive-definite') {
    super(message);
    this.name = 'NonPositiveDefiniteMatrixError';
  }
}

/**
 * An internal invariant does not hold: an index out of range, a missing map
 * entry or a node of an unexpected class where the algorithm guarantees one
 * (a bug in symjs, not an invalid input).
 */
export class InvariantError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'InvariantError';
  }
}
