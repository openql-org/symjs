// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Dynkin diagram of a Cartan type (SymPy sympy.liealgebras.dynkin_diagram).
 */

import type { CartanTypeLike } from './cartantype';
import { CartanType } from './cartantype';

/**
 * The Dynkin diagram of the Cartan type, as text.
 *
 * @param t - Cartan series and rank.
 * @returns The labeled diagram as multiline text.
 * @see SymPy `sympy.liealgebras.dynkin_diagram.DynkinDiagram`
 * @example
 * ```ts
 * import { DynkinDiagram } from '@symjs/symjs';
 *
 * DynkinDiagram('A3'); // => 0---0---0
 * //   1   2   3
 * ```
 */
export function DynkinDiagram(t: CartanTypeLike): string {
  return CartanType(t).dynkinDiagram();
}
