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
