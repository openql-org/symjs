// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy's exception classes and seterr.
 */

/**
 * A value that cannot be converted to an expression (SymPy SympifyError).
 *
 * @see SymPy `sympy.core.sympify.SympifyError`
 */
export class SympifyError extends TypeError {
  /**
   * Creates a `SympifyError` error.
   *
   * @param message - The diagnostic message.
   * @param value - The value to examine.
   */
  constructor(
    message: string,
    /** The value that failed to convert. */
    readonly value?: unknown,
  ) {
    super(message);
    this.name = 'SympifyError';
  }
}

/**
 * A series or limit computation met a pole (SymPy PoleError).
 *
 * @see SymPy `sympy.core.function.PoleError`
 */
export class PoleError extends Error {
  /**
   * Creates a `PoleError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'PoleError';
  }
}

/**
 * Numerical evaluation could not reach the requested precision (SymPy PrecisionExhausted).
 *
 * @see SymPy `sympy.core.evalf.PrecisionExhausted`
 */
export class PrecisionExhausted extends Error {
  /**
   * Creates a `PrecisionExhausted` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message = 'precision exhausted') {
    super(message);
    this.name = 'PrecisionExhausted';
  }
}

/**
 * A numerical evaluation that SymPy reports with a ValueError from mpmath (hypercomb() not
 * converging at a pole of its Gamma factors, ...). Unlike other failures, evalf passes it on.
 */
export class EvalfValueError extends RangeError {
  /**
   * Creates an `EvalfValueError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'ValueError';
  }
}

/** @internal Global error settings (SymPy _errdict). */
export const errorSettings = { divide: false };

/**
 * With `divide: true`, 0/0 throws a RangeError
 * ("Indeterminate 0/0") instead of giving nan.
 *
 * @param opts - `divide` makes zero divided by zero raise an error.
 * @see SymPy `sympy.core.numbers.seterr`
 */
export function seterr(opts: { divide?: boolean } = {}): void {
  errorSettings.divide = Boolean(opts.divide);
}

/**
 * The equations are not linear in the unknowns (SymPy NonlinearError).
 *
 * @see SymPy `sympy.solvers.solveset.NonlinearError`
 */
export class NonlinearError extends Error {
  /**
   * Creates a `NonlinearError` error.
   *
   * @param message - The diagnostic message.
   */
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
  /**
   * Creates a `NotImplementedError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'NotImplementedError';
  }
}

/**
 * The limits of a Sum or Product cannot be interchanged.
 *
 * @see SymPy `sympy.concrete.expr_with_intlimits.ReorderError`
 */
export class ReorderError extends NotImplementedError {
  /**
   * Creates a `ReorderError` error.
   *
   * @param expr - The input expression.
   * @param msg - The diagnostic message.
   */
  constructor(expr: string, msg: string) {
    super(`${expr} could not be reordered: ${msg}.`);
    this.name = 'ReorderError';
  }
}

/** A feature whose entry point has not been imported (e.g. simplify before importing '@symjs/symjs/simplify'). */
export class NotLoadedError extends Error {
  /**
   * Creates a `NotLoadedError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'NotLoadedError';
  }
}

/**
 * The expression is not a polynomial as required, or a polynomial operation is not defined for it (SymPy PolynomialError).
 *
 * @see SymPy `sympy.polys.polyerrors.PolynomialError`
 */
export class PolynomialError extends TypeError {
  /**
   * Creates a `PolynomialError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'PolynomialError';
  }
}

/**
 * The coefficients are outside the domain an algorithm needs, e.g. rational coefficients (SymPy DomainError).
 *
 * @see SymPy `sympy.polys.polyerrors.DomainError`
 */
export class DomainError extends TypeError {
  /**
   * Creates a `DomainError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'DomainError';
  }
}

/**
 * An exact division that leaves a remainder (SymPy ExactQuotientFailed).
 *
 * @see SymPy `sympy.polys.polyerrors.ExactQuotientFailed`
 */
export class ExactQuotientFailed extends RangeError {
  /**
   * Creates an `ExactQuotientFailed` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'ExactQuotientFailed';
  }
}

/**
 * An element without an inverse (SymPy NotInvertible).
 *
 * @see SymPy `sympy.polys.polyerrors.NotInvertible`
 */
export class NotInvertible extends RangeError {
  /**
   * Creates a `NotInvertible` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'NotInvertible';
  }
}

/**
 * A matrix without the property an operation needs (SymPy MatrixError).
 *
 * @see SymPy `sympy.matrices.exceptions.MatrixError`
 */
export class MatrixError extends RangeError {
  /**
   * Creates a `MatrixError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'MatrixError';
  }
}

/**
 * The shapes of matrices do not match (SymPy ShapeError).
 *
 * @see SymPy `sympy.matrices.exceptions.ShapeError`
 */
export class ShapeError extends MatrixError {
  /**
   * Creates a `ShapeError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message = 'Matrices are not aligned') {
    super(message);
    this.name = 'ShapeError';
  }
}

/**
 * A square matrix is required (SymPy NonSquareMatrixError, a ShapeError).
 *
 * @see SymPy `sympy.matrices.exceptions.NonSquareMatrixError`
 */
export class NonSquareMatrixError extends ShapeError {
  /**
   * Creates a `NonSquareMatrixError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message = 'Matrix must be square') {
    super(message);
    this.name = 'NonSquareMatrixError';
  }
}

/**
 * The matrix is singular (SymPy NonInvertibleMatrixError).
 *
 * @see SymPy `sympy.matrices.exceptions.NonInvertibleMatrixError`
 */
export class NonInvertibleMatrixError extends MatrixError {
  /**
   * Creates a `NonInvertibleMatrixError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message = 'Matrix det == 0; not invertible.') {
    super(message);
    this.name = 'NonInvertibleMatrixError';
  }
}

/**
 * The matrix is not positive definite (SymPy NonPositiveDefiniteMatrixError).
 *
 * @see SymPy `sympy.matrices.exceptions.NonPositiveDefiniteMatrixError`
 */
export class NonPositiveDefiniteMatrixError extends MatrixError {
  /**
   * Creates a `NonPositiveDefiniteMatrixError` error.
   *
   * @param message - The diagnostic message.
   */
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
