// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type B_n (SymPy sympy.liealgebras.type_b): the Lie algebra so(2n + 1).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root, RootCoordinate } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, filled, labels } from './standard';

/**
 * The Cartan type B_n, n >= 2.
 *
 * @see SymPy `sympy.liealgebras.type_b.TypeB`
 */
export class TypeB extends StandardCartan {
  /**
   * Constructs the Cartan type of series B with the specified rank.
   *
   * @param n - Rank of the Cartan type.
   * @throws RangeError when the rank is outside the range supported by this Cartan family.
   */
  constructor(n: number) {
    if (n < 2) throw new RangeError('n cannot be less than 2');
    super('B', n);
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.dimension`
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
   * @see SymPy `sympy.liealgebras.type_b.TypeB.basic_root`
   */
  basicRoot(i: number, j: number): Root {
    return basicRoot(this.n, i, j);
  }
  /**
   * Selects a simple root by its position in the Dynkin diagram.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.simple_root`
   */
  simpleRoot(i: number): Root {
    if (i < this.n) return this.basicRoot(i - 1, i);
    const root = filled(this.n, 0);
    root[this.n - 1] = 1;
    return root;
  }
  /**
   * Enumerates the positive roots in standard coordinates.
   *
   * @returns The positive roots indexed from one.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.positive_roots`
   */
  positiveRoots(): Map<number, Root> {
    return longShortRoots(this.n, 1);
  }
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.roots`
   */
  roots(): number {
    return 2 * this.n ** 2;
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 0; i < n - 1; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    e.push([n - 2, n - 1, -2]);
    return cartanFrom(n, e);
  }
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @remarks The rank-four algebra has dimension 36. SymPy returns `6.0`.
   * @returns The dimension of the Lie algebra.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.basis`
   * @example
   * ```ts
   * import { TypeB } from '@symjs/symjs';
   *
   * new TypeB(4).basis(); // => 36
   * ```
   */
  basis(): number {
    return this.n * (2 * this.n + 1);
  }
  /**
   * Names the special orthogonal Lie algebra associated with this rank.
   *
   * @remarks SymPy gives `so(8)` at rank four. The odd orthogonal algebra at that rank is `so(9)`.
   * @returns The name of the corresponding Lie algebra.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.lie_algebra`
   * @example
   * ```ts
   * import { TypeB } from '@symjs/symjs';
   *
   * new TypeB(4).lieAlgebra(); // => so(9)
   * ```
   */
  lieAlgebra(): string {
    return `so(${2 * this.n + 1})`;
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.type_b.TypeB.dynkin_diagram`
   */
  dynkinDiagram(): string {
    return `${chain(this.n - 1)}=>=0\n${labels(1, this.n)}`;
  }
}

/** The positive roots e_i - e_j, e_i + e_j (i < j) and c*e_i of the B and C series. */
export function longShortRoots(n: number, c: RootCoordinate): Map<number, Root> {
  const out = new Map<number, Root>();
  for (let i = 0; i < n - 1; i++) {
    for (let j = i + 1; j < n; j++) {
      out.set(out.size + 1, basicRoot(n, i, j));
      const root = basicRoot(n, i, j);
      root[j] = 1;
      out.set(out.size + 1, root);
    }
  }
  for (let i = 0; i < n; i++) {
    const root = filled(n, 0);
    root[i] = c;
    out.set(out.size + 1, root);
  }
  return out;
}
