// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The polynomial exception classes of SymPy (sympy.polys.polyerrors)
 * that core/errors.ts does not define. PolynomialError, DomainError,
 * ExactQuotientFailed and NotInvertible are in core/errors.ts (they derive
 * from TypeError and RangeError there), CoercionFailed is in polys/domains.ts
 * and PolificationFailed in polys/sympoly.ts.
 */

import { PolynomialError } from '../core/errors';

/**
 * The base of the polynomial errors that have no more specific JavaScript
 * error class; a TypeError like PolynomialError.
 *
 * @see SymPy `sympy.polys.polyerrors.BasePolynomialError`
 */
export class BasePolynomialError extends TypeError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'BasePolynomialError';
  }
}

/**
 * A polynomial division whose leading coefficient vanishes in an inexact domain.
 *
 * @see SymPy `sympy.polys.polyerrors.PolynomialDivisionFailed`
 */
export class PolynomialDivisionFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'PolynomialDivisionFailed';
  }
}

/**
 * An operation that the polynomial representation does not support.
 *
 * @see SymPy `sympy.polys.polyerrors.OperationNotSupported`
 */
export class OperationNotSupported extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'OperationNotSupported';
  }
}

/**
 * The heuristic gcd algorithm exhausted its evaluation points.
 *
 * @see SymPy `sympy.polys.polyerrors.HeuristicGCDFailed`
 */
export class HeuristicGCDFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'HeuristicGCDFailed';
  }
}

/**
 * A modular gcd algorithm did not find the gcd.
 *
 * @see SymPy `sympy.polys.polyerrors.ModularGCDFailed`
 */
export class ModularGCDFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'ModularGCDFailed';
  }
}

/**
 * A homomorphism could not be computed.
 *
 * @see SymPy `sympy.polys.polyerrors.HomomorphismFailed`
 */
export class HomomorphismFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'HomomorphismFailed';
  }
}

/**
 * Two fields could not be shown isomorphic.
 *
 * @see SymPy `sympy.polys.polyerrors.IsomorphismFailed`
 */
export class IsomorphismFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'IsomorphismFailed';
  }
}

/**
 * A factorization produced factors that do not divide the polynomial.
 *
 * @see SymPy `sympy.polys.polyerrors.ExtraneousFactors`
 */
export class ExtraneousFactors extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'ExtraneousFactors';
  }
}

/**
 * An evaluation of a polynomial failed.
 *
 * @see SymPy `sympy.polys.polyerrors.EvaluationFailed`
 */
export class EvaluationFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'EvaluationFailed';
  }
}

/**
 * An isolating interval could not be refined.
 *
 * @see SymPy `sympy.polys.polyerrors.RefinementFailed`
 */
export class RefinementFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'RefinementFailed';
  }
}

/**
 * A power series without a reversion (compositional inverse).
 *
 * @see SymPy `sympy.polys.polyerrors.NotReversible`
 */
export class NotReversible extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'NotReversible';
  }
}

/**
 * An expression that is not an algebraic number.
 *
 * @see SymPy `sympy.polys.polyerrors.NotAlgebraic`
 */
export class NotAlgebraic extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'NotAlgebraic';
  }
}

/**
 * Two domains or polynomial representations could not be unified.
 *
 * @see SymPy `sympy.polys.polyerrors.UnificationFailed`
 */
export class UnificationFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'UnificationFailed';
  }
}

/**
 * A factor whose roots cannot be given in radicals.
 *
 * @see SymPy `sympy.polys.polyerrors.UnsolvableFactorError`
 */
export class UnsolvableFactorError extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'UnsolvableFactorError';
  }
}

/**
 * Invalid generators of a polynomial.
 *
 * @see SymPy `sympy.polys.polyerrors.GeneratorsError`
 */
export class GeneratorsError extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'GeneratorsError';
  }
}

/**
 * A polynomial operation that needs generators got none.
 *
 * @see SymPy `sympy.polys.polyerrors.GeneratorsNeeded`
 */
export class GeneratorsNeeded extends GeneratorsError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'GeneratorsNeeded';
  }
}

/**
 * A polynomial computation failed on its arguments.
 *
 * @see SymPy `sympy.polys.polyerrors.ComputationFailed`
 */
export class ComputationFailed extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'ComputationFailed';
  }
}

/**
 * A univariate polynomial was required.
 *
 * @see SymPy `sympy.polys.polyerrors.UnivariatePolynomialError`
 */
export class UnivariatePolynomialError extends PolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'UnivariatePolynomialError';
  }
}

/**
 * A multivariate polynomial was required.
 *
 * @see SymPy `sympy.polys.polyerrors.MultivariatePolynomialError`
 */
export class MultivariatePolynomialError extends PolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'MultivariatePolynomialError';
  }
}

/**
 * An invalid polynomial option.
 *
 * @see SymPy `sympy.polys.polyerrors.OptionError`
 */
export class OptionError extends BasePolynomialError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'OptionError';
  }
}

/**
 * An invalid polynomial flag.
 *
 * @see SymPy `sympy.polys.polyerrors.FlagError`
 */
export class FlagError extends OptionError {
  /**
   * Create the error with a diagnostic message.
   *
   * @param message - Error message describing the failure.
   */
  constructor(message = '') {
    super(message);
    this.name = 'FlagError';
  }
}
