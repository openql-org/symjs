// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan types E_6, E_7 and E_8 (SymPy sympy.liealgebras.type_e).
 */

import { Rational } from '../core/nodes';
import { at } from '../core/guard';
import type { Matrix } from '../matrices/matrix';
import type { Root, RootCoordinate } from './standard';
import { StandardCartan, cartanFrom, chain, filled } from './standard';

const HALF = Rational.of(1n, 2n);
const NEG_HALF = Rational.of(-1n, 2n);

/**
 * The exceptional Cartan types E_6, E_7 and E_8 (roots in an 8-dimensional space).
 *
 * @see SymPy `sympy.liealgebras.type_e.TypeE`
 */
export class TypeE extends StandardCartan {
  /**
   * Constructs the Cartan type of series E with the specified rank.
   *
   * @param n - Rank of the Cartan type.
   * @throws RangeError when the rank is outside the range supported by this Cartan family.
   */
  constructor(n: number) {
    if (n < 6 || n > 8) throw new RangeError('Invalid value of n');
    super('E', n);
  }
  /**
   * Gives the dimension of the vector space used for the root coordinates.
   *
   * @returns The dimension of the ambient root space.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.dimension`
   */
  dimension(): number {
    return 8;
  }
  /**
   * Constructs the root with coefficient −1 at the first index and 1 at the second.
   *
   * @param i - First zero-based coordinate index.
   * @param j - Second zero-based coordinate index.
   * @returns The root specified by the two coordinate indices.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.basic_root`
   */
  basicRoot(i: number, j: number): Root {
    const root = filled(8, 0);
    root[i] = -1;
    root[j] = 1;
    return root;
  }
  /**
   * Constructs the simple root at the given one-based index. The first root has half-integer
   * coordinates.
   *
   * @param i - One-based simple-root index.
   * @returns The coordinates of the indexed simple root.
   * @throws RangeError when the simple-root index is outside the series.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.simple_root`
   */
  simpleRoot(i: number): Root {
    if (i === 1) {
      const root = filled(8, -0.5);
      root[0] = 0.5;
      root[7] = 0.5;
      return root;
    }
    if (i === 2) {
      const root = filled(8, 0);
      root[0] = 1;
      root[1] = 1;
      return root;
    }
    if (i > this.n) throw new RangeError(`E${this.n} only has ${at(['six', 'seven', 'eight'], this.n - 6)} simple roots!`);
    return this.basicRoot(i - 3, i - 2);
  }
  /**
   * Enumerates the positive integer and half-integer roots of the exceptional root system.
   *
   * @returns The positive roots indexed from one.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.positive_roots`
   */
  positiveRoots(): Map<number, Root> {
    const n = this.n;
    const out = new Map<number, Root>();
    const m = n === 8 ? 8 : n - 1;
    for (let i = 0; i < m; i++) {
      for (let j = i + 1; j < m; j++) {
        out.set(out.size + 1, this.basicRoot(i, j));
        const root = this.basicRoot(i, j);
        root[i] = 1;
        out.set(out.size + 1, root);
      }
    }
    if (n === 7) out.set(out.size + 1, [0, 0, 0, 0, 0, 1, 1, 0]);
    // the sign flips: the first five coordinates to -1/2, the sixth and seventh (E7, E8) to +1/2, an even number of them
    const flips = n - 1;
    for (let mask = 0; mask < 1 << flips; mask++) {
      const bits = Array.from({ length: flips }, (_x, k) => (mask >> (flips - 1 - k)) & 1);
      if (bits.reduce((a, b) => a + b, 0) % 2) continue;
      const root: RootCoordinate[] = [HALF, HALF, HALF, HALF, HALF, NEG_HALF, NEG_HALF, HALF];
      bits.forEach((b, k) => {
        if (b) root[k] = k < 5 ? NEG_HALF : HALF;
      });
      out.set(out.size + 1, root);
    }
    return out;
  }
  /**
   * Counts both positive and negative roots.
   *
   * @returns The total number of roots.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.roots`
   */
  roots(): number {
    return at([72, 126, 240], this.n - 6);
  }
  /**
   * Builds the matrix of pairings between simple roots and coroots.
   *
   * @returns The matrix of Cartan integers.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.cartan_matrix`
   */
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 3; i < n - 1; i++) e.push([i, i + 1, -1], [i, i - 1, -1]);
    e.push([0, 2, -1], [2, 0, -1], [1, 3, -1], [3, 1, -1], [2, 3, -1], [n - 1, n - 2, -1]);
    return cartanFrom(n, e);
  }
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @returns The dimension of the Lie algebra.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.basis`
   */
  basis(): number {
    return at([78, 133, 248], this.n - 6);
  }
  /**
   * Draws the bonds and labels of the Dynkin diagram.
   *
   * @returns The labeled Dynkin diagram as text.
   * @see SymPy `sympy.liealgebras.type_e.TypeE.dynkin_diagram`
   */
  dynkinDiagram(): string {
    const pad = ' '.repeat(8);
    const rest = Array.from({ length: this.n - 2 }, (_x, i) => String(i + 3)).join('   ');
    return `${pad}2\n${pad}0\n${pad}|\n${pad}|\n${chain(this.n - 1)}\n1   ${rest}`;
  }
}
