// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/geometry/exceptions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.geometry.exceptions: GeometryError, and the
 * Undecidable error of sympy.utilities.misc that the geometry raises.
 */

/** An exception raised by geometry entities (SymPy GeometryError, a ValueError). */
export class GeometryError extends RangeError {
  constructor(message: string) {
    super(message);
    this.name = 'GeometryError';
  }
}

/** A question about a geometry entity that cannot be decided (SymPy Undecidable, a ValueError). */
export class Undecidable extends RangeError {
  constructor(message: string) {
    super(message);
    this.name = 'Undecidable';
  }
}
