// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan matrix of a Cartan type (SymPy sympy.liealgebras.cartan_matrix).
 */

import type { Matrix } from '../matrices/matrix';
import type { CartanTypeLike } from './cartantype';
import { CartanType } from './cartantype';

/**
 * The Cartan matrix of the Cartan type ('A2', ['C', 3],...).
 *
 * @param ct - Cartan series and rank.
 * @returns The Cartan matrix in the simple-root basis.
 * @see SymPy `sympy.liealgebras.cartan_matrix.CartanMatrix`
 * @example
 * ```ts
 * import { CartanMatrix } from '@symjs/symjs';
 *
 * CartanMatrix('A2'); // => Matrix([
 * //   [ 2, -1],
 * //   [-1,  2]])
 * ```
 */
export function CartanMatrix(ct: CartanTypeLike): Matrix {
  return CartanType(ct).cartanMatrix();
}
