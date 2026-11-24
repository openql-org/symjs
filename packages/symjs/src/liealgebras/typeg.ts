// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type G_2 (SymPy sympy.liealgebras.type_g).
 */

import { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan } from './standard';

/**
 * The exceptional Cartan type G_2 (roots in a 3-dimensional space).
 *
 * @see SymPy `sympy.liealgebras.type_g.TypeG`
 */
export class TypeG extends StandardCartan {
  /**
   * Constructs the Cartan type of series G with the specified rank.
   *
   * @param n - Rank of the Cartan type.
   * @throws RangeError when the rank is outside the range supported by this Cartan family.
   */
  constructor(n: number) {
    if (n !== 2) throw new RangeError('n should be 2');
    super('G', 2);
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.dimension`
   */
  dimension(): number {
    return 3;
  }
  /**
   * Selects a simple root by its position in the Dynkin diagram.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.simple_root`
   */
  simpleRoot(i: number): Root {
    return i === 1 ? [0, 1, -1] : [1, -2, 1];
  }
  /**
   * Enumerates the positive roots in standard coordinates.
   *
   * @returns The positive roots indexed from one.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.positive_roots`
   */
  positiveRoots(): Map<number, Root> {
    return new Map<number, Root>([
      [1, [0, 1, -1]],
      [2, [1, -2, 1]],
      [3, [1, -1, 0]],
      [4, [1, 0, 1]],
      [5, [1, 1, -2]],
      [6, [2, -1, -1]],
    ]);
  }
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.roots`
   */
  roots(): number {
    return 12;
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    return Matrix.of([
      [2, -1],
      [-3, 2],
    ]);
  }
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @returns The dimension of the Lie algebra.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.basis`
   */
  basis(): number {
    return 14;
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.type_g.TypeG.dynkin_diagram`
   */
  dynkinDiagram(): string {
    return '0≡<≡0\n1   2';
  }
}
