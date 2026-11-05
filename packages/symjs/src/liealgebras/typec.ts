// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type C_n (SymPy sympy.liealgebras.type_c): the Lie algebra sp(2n).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, filled, labels } from './standard';
import { longShortRoots } from './typeb';

/** SymPy TypeC: the Cartan type C_n, n >= 3. */
export class TypeC extends StandardCartan {
  constructor(n: number) {
    if (n < 3) throw new RangeError('n cannot be less than 3');
    super('C', n);
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
    root[this.n - 1] = 2;
    return root;
  }
  positiveRoots(): Map<number, Root> {
    return longShortRoots(this.n, 2);
  }
  roots(): number {
    return 2 * this.n ** 2;
  }
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 0; i < n - 1; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    e.push([n - 1, n - 2, -2]);
    return cartanFrom(n, e);
  }
  /** The dimension n*(2*n + 1) of sp(2n). */
  basis(): number {
    return this.n * (2 * this.n + 1);
  }
  /** SymPy lie_algebra: sp(2n). */
  lieAlgebra(): string {
    return `sp(${2 * this.n})`;
  }
  dynkinDiagram(): string {
    return `${chain(this.n - 1)}=<=0\n${labels(1, this.n)}`;
  }
}
