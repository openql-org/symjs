// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type A_n (SymPy sympy.liealgebras.type_a): the Lie algebra su(n + 1).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, labels } from './standard';

/**
 * The Cartan type A_n, n >= 1.
 *
 * @see SymPy `sympy.liealgebras.type_a.TypeA`
 */
export class TypeA extends StandardCartan {
  /**
   * Constructs the Cartan type of series A with the specified rank.
   *
   * @param n - Rank of the Cartan type.
   * @throws RangeError when the rank is outside the range supported by this Cartan family.
   */
  constructor(n: number) {
    if (n < 1) throw new RangeError('n cannot be less than 1');
    super('A', n);
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.dimension`
   */
  dimension(): number {
    return this.n + 1;
  }
  /**
   * Constructs the root with coefficient 1 at the first index and −1 at the second.
   *
   * @param i - First zero-based coordinate index.
   * @param j - Second zero-based coordinate index.
   * @returns The root specified by the two coordinate indices.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.basic_root`
   */
  basicRoot(i: number, j: number): Root {
    return basicRoot(this.n + 1, i, j);
  }
  /**
   * Selects a simple root by its position in the Dynkin diagram.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.simple_root`
   */
  simpleRoot(i: number): Root {
    return this.basicRoot(i - 1, i);
  }
  /**
   * Enumerates the positive roots in standard coordinates.
   *
   * @returns The positive roots indexed from one.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.positive_roots`
   */
  positiveRoots(): Map<number, Root> {
    const out = new Map<number, Root>();
    for (let i = 0; i < this.n; i++) for (let j = i + 1; j <= this.n; j++) out.set(out.size + 1, this.basicRoot(i, j));
    return out;
  }
  /**
   * Constructs the highest root in the standard coordinate basis.
   *
   * @returns The coordinates of the highest root.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.highest_root`
   */
  highestRoot(): Root {
    return this.basicRoot(0, this.n);
  }
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.roots`
   */
  roots(): number {
    return this.n * (this.n + 1);
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    const e: [number, number, number][] = [];
    for (let i = 0; i < this.n - 1; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    return cartanFrom(this.n, e);
  }
  /**
   * Computes the dimension of the Lie algebra of type A from its rank.
   *
   * @remarks For rank three the dimension of `su(4)` is 15. SymPy returns 8.
   * @returns The dimension of the Lie algebra.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.basis`
   * @example
   * ```ts
   * import { TypeA } from '@symjs/symjs';
   *
   * new TypeA(3).basis(); // => 15
   * ```
   */
  basis(): number {
    return (this.n + 1) ** 2 - 1;
  }
  /**
   * Names the special unitary Lie algebra associated with this rank.
   *
   * @returns The name of the corresponding Lie algebra.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.lie_algebra`
   */
  lieAlgebra(): string {
    return `su(${this.n + 1})`;
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.type_a.TypeA.dynkin_diagram`
   */
  dynkinDiagram(): string {
    return `${chain(this.n)}\n${labels(1, this.n)}`;
  }
}
