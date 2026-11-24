// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type F_4 (SymPy sympy.liealgebras.type_f).
 */

import { Rational } from '../core/nodes';
import { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan, basicRoot, filled, labels } from './standard';
import { longShortRoots } from './typeb';

const HALF = Rational.of(1n, 2n);
const NEG_HALF = Rational.of(-1n, 2n);

/**
 * The exceptional Cartan type F_4.
 *
 * @see SymPy `sympy.liealgebras.type_f.TypeF`
 */
export class TypeF extends StandardCartan {
  /**
   * Constructs the Cartan type of series F with the specified rank.
   *
   * @param n - Rank of the Cartan type.
   * @throws RangeError when the rank is outside the range supported by this Cartan family.
   */
  constructor(n: number) {
    if (n !== 4) throw new RangeError('n should be 4');
    super('F', 4);
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.dimension`
   */
  dimension(): number {
    return 4;
  }
  /**
   * Constructs a coordinate root with nonzero components at the two specified indices.
   *
   * @param i - First zero-based coordinate index.
   * @param j - Second zero-based coordinate index.
   * @returns The root specified by the two coordinate indices.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.basic_root`
   */
  basicRoot(i: number, j: number): Root {
    return basicRoot(4, i, j);
  }
  /**
   * Selects a simple root by its position in the Dynkin diagram.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.simple_root`
   */
  simpleRoot(i: number): Root {
    if (i < 3) return this.basicRoot(i - 1, i);
    if (i === 3) return [0, 0, 0, 1];
    return filled(4, NEG_HALF);
  }
  /**
   * Enumerates the positive roots in standard coordinates.
   *
   * @returns The positive roots indexed from one.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.positive_roots`
   */
  positiveRoots(): Map<number, Root> {
    const out = longShortRoots(4, 1);
    out.set(out.size + 1, filled(4, HALF));
    for (let i = 1; i < 4; i++) {
      const root = filled(4, HALF);
      root[i] = NEG_HALF;
      out.set(out.size + 1, root);
    }
    for (const r of [[HALF, HALF, NEG_HALF, NEG_HALF], [HALF, NEG_HALF, HALF, NEG_HALF], [HALF, NEG_HALF, NEG_HALF, HALF], [HALF, NEG_HALF, NEG_HALF, NEG_HALF]]) out.set(out.size + 1, r);
    return out;
  }
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.roots`
   */
  roots(): number {
    return 48;
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    return Matrix.of([
      [2, -1, 0, 0],
      [-1, 2, -2, 0],
      [0, -1, 2, -1],
      [0, 0, -1, 2],
    ]);
  }
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @returns The dimension of the Lie algebra.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.basis`
   */
  basis(): number {
    return 52;
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.type_f.TypeF.dynkin_diagram`
   */
  dynkinDiagram(): string {
    return `0---0=>=0---0\n${labels(1, 4)}`;
  }
}
