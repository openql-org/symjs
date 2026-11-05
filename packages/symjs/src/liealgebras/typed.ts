// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type D_n (SymPy sympy.liealgebras.type_d): the Lie algebra so(2n).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, filled, labels } from './standard';

/** SymPy TypeD: the Cartan type D_n, n >= 3. */
export class TypeD extends StandardCartan {
  constructor(n: number) {
    if (n < 3) throw new RangeError('n cannot be less than 3');
    super('D', n);
  }
  dimension(): number {
    return this.n;
  }
  /** SymPy basic_root: 1 at i and -1 at j. */
  basicRoot(i: number, j: number): Root {
    return basicRoot(this.n, i, j);
  }
  simpleRoot(i: number): Root {
    if (i < this.n) return this.basicRoot(i - 1, i);
    const root = filled(this.n, 0);
    root[this.n - 2] = 1;
    root[this.n - 1] = 1;
    return root;
  }
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
  roots(): number {
    return 2 * this.n * (this.n - 1);
  }
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 0; i < n - 2; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    e.push([n - 3, n - 1, -1], [n - 1, n - 3, -1]);
    return cartanFrom(n, e);
  }
  /** The dimension n*(2*n - 1) of so(2n) (SymPy gives n*(n - 1)/2). */
  basis(): number {
    return this.n * (2 * this.n - 1);
  }
  /** SymPy lie_algebra: so(2n). */
  lieAlgebra(): string {
    return `so(${2 * this.n})`;
  }
  dynkinDiagram(): string {
    const n = this.n;
    const pad = ' '.repeat(4 * (n - 3));
    return `${pad}${n - 1}\n${pad}0\n${pad}|\n${pad}|\n${chain(n - 1)}\n${labels(1, n - 2)}   ${n}`;
  }
}
