// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type D_n (SymPy sympy.liealgebras.type_d): the Lie algebra so(2n).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, filled, labels } from './standard';

/**
 * The Cartan type D_n, n >= 3.
 *
 * @see SymPy `sympy.liealgebras.type_d.TypeD`
 */
export class TypeD extends StandardCartan {
  /**
   * Constructs the Cartan type of series D with the specified rank.
   *
   * @param n - Rank of the Cartan type.
   * @throws RangeError when the rank is outside the range supported by this Cartan family.
   */
  constructor(n: number) {
    if (n < 3) throw new RangeError('n cannot be less than 3');
    super('D', n);
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.dimension`
   */
  dimension(): number {
    return this.n;
  }
  /**
   * Constructs the root with coefficient 1 at the first index and −1 at the second.
   *
   * @param i - First zero-based coordinate index.
   * @param j - Second zero-based coordinate index.
   * @returns The root specified by the two coordinate indices.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.basic_root`
   */
  basicRoot(i: number, j: number): Root {
    return basicRoot(this.n, i, j);
  }
  /**
   * Selects a simple root by its position in the Dynkin diagram.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.simple_root`
   */
  simpleRoot(i: number): Root {
    if (i < this.n) return this.basicRoot(i - 1, i);
    const root = filled(this.n, 0);
    root[this.n - 2] = 1;
    root[this.n - 1] = 1;
    return root;
  }
  /**
   * Enumerates the positive roots in standard coordinates.
   *
   * @returns The positive roots indexed from one.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.positive_roots`
   */
  positiveRoots(): Map<number, Root> {
    const n = this.n;
    const out = new Map<number, Root>();
    for (let i = 0; i < n - 1; i++) {
      for (let j = i + 1; j < n; j++) {
        out.set(out.size + 1, this.basicRoot(i, j));
        const root = this.basicRoot(i, j);
        root[j] = 1;
        out.set(out.size + 1, root);
      }
    }
    return out;
  }
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.roots`
   */
  roots(): number {
    return 2 * this.n * (this.n - 1);
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 0; i < n - 2; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    e.push([n - 3, n - 1, -1], [n - 1, n - 3, -1]);
    return cartanFrom(n, e);
  }
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @remarks The rank-four algebra has dimension 28. SymPy returns `6.0`.
   * @returns The dimension of the Lie algebra.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.basis`
   * @example
   * ```ts
   * import { TypeD } from '@symjs/symjs';
   *
   * new TypeD(4).basis(); // => 28
   * ```
   */
  basis(): number {
    return this.n * (2 * this.n - 1);
  }
  /**
   * Names the special orthogonal Lie algebra associated with this rank.
   *
   * @returns The name of the corresponding Lie algebra.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.lie_algebra`
   */
  lieAlgebra(): string {
    return `so(${2 * this.n})`;
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.type_d.TypeD.dynkin_diagram`
   */
  dynkinDiagram(): string {
    const n = this.n;
    const pad = ' '.repeat(4 * (n - 3));
    return `${pad}${n - 1}\n${pad}0\n${pad}|\n${pad}|\n${chain(n - 1)}\n${labels(1, n - 2)}   ${n}`;
  }
}
