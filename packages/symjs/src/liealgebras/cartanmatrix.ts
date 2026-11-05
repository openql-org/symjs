// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan matrix of a Cartan type (SymPy sympy.liealgebras.cartan_matrix).
 */

import type { Matrix } from '../matrices/matrix';
import type { CartanTypeLike } from './cartantype';
import { CartanType } from './cartantype';

/** SymPy CartanMatrix: the Cartan matrix of the Cartan type ('A2', ['C', 3], ...). */
export function CartanMatrix(ct: CartanTypeLike): Matrix {
  return CartanType(ct).cartanMatrix();
}
