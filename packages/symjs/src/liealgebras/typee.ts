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

/** SymPy TypeE: the exceptional Cartan types E_6, E_7 and E_8 (roots in an 8-dimensional space). */
export class TypeE extends StandardCartan {
  constructor(n: number) {
    if (n < 6 || n > 8) throw new RangeError('Invalid value of n');
    super('E', n);
  }
  dimension(): number {
    return 8;
  }
  /** SymPy basic_root: -1 at i and 1 at j. */
  basicRoot(i: number, j: number): Root {
    const root = filled(8, 0);
    root[i] = -1;
    root[j] = 1;
    return root;
  }
  /** The i-th simple root (the first one has the float coordinates +-0.5, as in SymPy). */
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
   * The positive roots: +-e_i + e_j and the half-integer roots
   * (1/2)(+-e_1 ... +-e_8) of the series (SymPy reuses one list for the
   * half-integer roots, so that several of them coincide; here each is built anew).
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
  roots(): number {
    return at([72, 126, 240], this.n - 6);
  }
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 3; i < n - 1; i++) e.push([i, i + 1, -1], [i, i - 1, -1]);
    e.push([0, 2, -1], [2, 0, -1], [1, 3, -1], [3, 1, -1], [2, 3, -1], [n - 1, n - 2, -1]);
    return cartanFrom(n, e);
  }
  basis(): number {
    return at([78, 133, 248], this.n - 6);
  }
  dynkinDiagram(): string {
    const pad = ' '.repeat(8);
    const rest = Array.from({ length: this.n - 2 }, (_x, i) => String(i + 3)).join('   ');
    return `${pad}2\n${pad}0\n${pad}|\n${pad}|\n${chain(this.n - 1)}\n1   ${rest}`;
  }
}
