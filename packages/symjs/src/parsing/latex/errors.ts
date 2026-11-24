// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Invalid or incomplete LaTeX mathematical input (SymPy LaTeXParsingError).
 *
 * @see SymPy `sympy.parsing.latex.errors.LaTeXParsingError`
 */
export class LaTeXParsingError extends TypeError {
  /**
   * Creates a `LaTeXParsingError` error.
   *
   * @param message - The diagnostic message.
   */
  constructor(message: string) {
    super(message);
    this.name = 'LaTeXParsingError';
  }
}
