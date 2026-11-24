// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (holonomic/holonomicerrors.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The exceptions of the holonomic module (SymPy holonomicerrors).
 */

import type { Expr } from '../core/nodes';
import { str } from '../printing/str';

/** What the errors print of a holonomic function. */
interface Printable {
  toString(): string;
}

/**
 * Base class of the holonomic errors.
 *
 * @see SymPy `sympy.holonomic.holonomicerrors.BaseHolonomicError`
 */
export class BaseHolonomicError extends RangeError {}

/** The common base of NotPowerSeriesError and NotHyperSeriesError, the errors after which a numerical evaluation is used. */
export class SeriesExpansionError extends BaseHolonomicError {}

/**
 * A power series does not exist at the point.
 *
 * @see SymPy `sympy.holonomic.holonomicerrors.NotPowerSeriesError`
 */
export class NotPowerSeriesError extends SeriesExpansionError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param holonomic - Holonomic function at which the operation failed.
   * @param x0 - Point for the initial conditions.
   */
  constructor(
    /**
     * The function involved in the failed operation.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.NotPowerSeriesError.holonomic`
     */
    readonly holonomic: Printable,
    /**
     * The point at which the initial data are specified.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.NotPowerSeriesError.x0`
     */
    readonly x0: Expr,
  ) {
    super(`A Power Series does not exists for ${holonomic.toString()} about ${str(x0)}.`);
  }
}

/**
 * Indicates that the requested function cannot be represented as holonomic.
 *
 * @see SymPy `sympy.holonomic.holonomicerrors.NotHolonomicError`
 */
export class NotHolonomicError extends BaseHolonomicError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param m - Description of the failed operation.
   */
  constructor(
    /**
     * The message describing the holonomic error.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.NotHolonomicError.m`
     */
    readonly m: string) {
    super(m);
  }
}

/**
 * The differential equation is singular at the point.
 *
 * @see SymPy `sympy.holonomic.holonomicerrors.SingularityError`
 */
export class SingularityError extends BaseHolonomicError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param holonomic - Holonomic function at which the operation failed.
   * @param x0 - Point for the initial conditions.
   */
  constructor(
    /**
     * The function involved in the failed operation.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.SingularityError.holonomic`
     */
    readonly holonomic: Printable,
    /**
     * The point at which the initial data are specified.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.SingularityError.x0`
     */
    readonly x0: Expr,
  ) {
    super(`${holonomic.toString()} has a singularity at ${str(x0)}.`);
  }
}

/**
 * The power series is not hypergeometric.
 *
 * @see SymPy `sympy.holonomic.holonomicerrors.NotHyperSeriesError`
 */
export class NotHyperSeriesError extends SeriesExpansionError {
  /**
   * Creates the exception with the supplied error details.
   *
   * @param holonomic - Holonomic function at which the operation failed.
   * @param x0 - Point for the initial conditions.
   */
  constructor(
    /**
     * The function involved in the failed operation.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.NotHyperSeriesError.holonomic`
     */
    readonly holonomic: Printable,
    /**
     * The point at which the initial data are specified.
     *
     * @see SymPy `sympy.holonomic.holonomicerrors.NotHyperSeriesError.x0`
     */
    readonly x0: Expr,
  ) {
    super(`Power series expansion of ${holonomic.toString()} about ${str(x0)} is not hypergeometric`);
  }
}
