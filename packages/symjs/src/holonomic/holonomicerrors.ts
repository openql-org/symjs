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

/** Base class of the holonomic errors (SymPy BaseHolonomicError). */
export class BaseHolonomicError extends RangeError {}

/** The common base of NotPowerSeriesError and NotHyperSeriesError, the errors after which a numerical evaluation is used. */
export class SeriesExpansionError extends BaseHolonomicError {}

/** A power series does not exist at the point (SymPy NotPowerSeriesError). */
export class NotPowerSeriesError extends SeriesExpansionError {
  constructor(
    readonly holonomic: Printable,
    readonly x0: Expr,
  ) {
    super(`A Power Series does not exists for ${holonomic.toString()} about ${str(x0)}.`);
  }
}

/** The function is not holonomic (SymPy NotHolonomicError). */
export class NotHolonomicError extends BaseHolonomicError {
  constructor(readonly m: string) {
    super(m);
  }
}

/** The differential equation is singular at the point (SymPy SingularityError). */
export class SingularityError extends BaseHolonomicError {
  constructor(
    readonly holonomic: Printable,
    readonly x0: Expr,
  ) {
    super(`${holonomic.toString()} has a singularity at ${str(x0)}.`);
  }
}

/** The power series is not hypergeometric (SymPy NotHyperSeriesError). */
export class NotHyperSeriesError extends SeriesExpansionError {
  constructor(
    readonly holonomic: Printable,
    readonly x0: Expr,
  ) {
    super(`Power series expansion of ${holonomic.toString()} about ${str(x0)} is not hypergeometric`);
  }
}
