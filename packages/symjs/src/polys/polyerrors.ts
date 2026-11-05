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
 * error class (SymPy BasePolynomialError); a TypeError like PolynomialError.
 */
export class BasePolynomialError extends TypeError {
  constructor(message = '') {
    super(message);
    this.name = 'BasePolynomialError';
  }
}

/** A polynomial division whose leading coefficient vanishes in an inexact domain (SymPy PolynomialDivisionFailed). */
export class PolynomialDivisionFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'PolynomialDivisionFailed';
  }
}

/** An operation that the polynomial representation does not support (SymPy OperationNotSupported). */
export class OperationNotSupported extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'OperationNotSupported';
  }
}

/** The heuristic gcd algorithm exhausted its evaluation points (SymPy HeuristicGCDFailed). */
export class HeuristicGCDFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'HeuristicGCDFailed';
  }
}

/** A modular gcd algorithm did not find the gcd (SymPy ModularGCDFailed). */
export class ModularGCDFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'ModularGCDFailed';
  }
}

/** A homomorphism could not be computed (SymPy HomomorphismFailed). */
export class HomomorphismFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'HomomorphismFailed';
  }
}

/** Two fields could not be shown isomorphic (SymPy IsomorphismFailed). */
export class IsomorphismFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'IsomorphismFailed';
  }
}

/** A factorization produced factors that do not divide the polynomial (SymPy ExtraneousFactors). */
export class ExtraneousFactors extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'ExtraneousFactors';
  }
}

/** An evaluation of a polynomial failed (SymPy EvaluationFailed). */
export class EvaluationFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'EvaluationFailed';
  }
}

/** An isolating interval could not be refined (SymPy RefinementFailed). */
export class RefinementFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'RefinementFailed';
  }
}

/** A power series without a reversion (compositional inverse) (SymPy NotReversible). */
export class NotReversible extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'NotReversible';
  }
}

/** An expression that is not an algebraic number (SymPy NotAlgebraic). */
export class NotAlgebraic extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'NotAlgebraic';
  }
}

/** Two domains or polynomial representations could not be unified (SymPy UnificationFailed). */
export class UnificationFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'UnificationFailed';
  }
}

/** A factor whose roots cannot be given in radicals (SymPy UnsolvableFactorError). */
export class UnsolvableFactorError extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'UnsolvableFactorError';
  }
}

/** Invalid generators of a polynomial (SymPy GeneratorsError). */
export class GeneratorsError extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'GeneratorsError';
  }
}

/** A polynomial operation that needs generators got none (SymPy GeneratorsNeeded). */
export class GeneratorsNeeded extends GeneratorsError {
  constructor(message = '') {
    super(message);
    this.name = 'GeneratorsNeeded';
  }
}

/** A polynomial computation failed on its arguments (SymPy ComputationFailed). */
export class ComputationFailed extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'ComputationFailed';
  }
}

/** A univariate polynomial was required (SymPy UnivariatePolynomialError). */
export class UnivariatePolynomialError extends PolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'UnivariatePolynomialError';
  }
}

/** A multivariate polynomial was required (SymPy MultivariatePolynomialError). */
export class MultivariatePolynomialError extends PolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'MultivariatePolynomialError';
  }
}

/** An invalid polynomial option (SymPy OptionError). */
export class OptionError extends BasePolynomialError {
  constructor(message = '') {
    super(message);
    this.name = 'OptionError';
  }
}

/** An invalid polynomial flag (SymPy FlagError). */
export class FlagError extends OptionError {
  constructor(message = '') {
    super(message);
    this.name = 'FlagError';
  }
}
