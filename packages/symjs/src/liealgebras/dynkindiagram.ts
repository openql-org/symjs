// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Dynkin diagram of a Cartan type (SymPy sympy.liealgebras.dynkin_diagram).
 */

import type { CartanTypeLike } from './cartantype';
import { CartanType } from './cartantype';

/** SymPy DynkinDiagram: the Dynkin diagram of the Cartan type, as text. */
export function DynkinDiagram(t: CartanTypeLike): string {
  return CartanType(t).dynkinDiagram();
}
