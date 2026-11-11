// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Invalid or incomplete LaTeX mathematical input (SymPy LaTeXParsingError). */
export class LaTeXParsingError extends TypeError {
  constructor(message: string) {
    super(message);
    this.name = 'LaTeXParsingError';
  }
}
