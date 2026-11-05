// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type B_n (SymPy sympy.liealgebras.type_b): the Lie algebra so(2n + 1).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root, RootCoordinate } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, filled, labels } from './standard';

/** SymPy TypeB: the Cartan type B_n, n >= 2. */
export class TypeB extends StandardCartan {
  constructor(n: number) {
    if (n < 2) throw new RangeError('n cannot be less than 2');
    super('B', n);
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
    root[this.n - 1] = 1;
    return root;
  }
  positiveRoots(): Map<number, Root> {
    return longShortRoots(this.n, 1);
  }
  roots(): number {
    return 2 * this.n ** 2;
  }
  cartanMatrix(): Matrix {
    const n = this.n;
    const e: [number, number, number][] = [];
    for (let i = 0; i < n - 1; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    e.push([n - 2, n - 1, -2]);
    return cartanFrom(n, e);
  }
  /** The dimension n*(2*n + 1) of so(2n + 1) (SymPy gives (n**2 - n)/2). */
  basis(): number {
    return this.n * (2 * this.n + 1);
  }
  /** SymPy lie_algebra: so(2n + 1) (SymPy prints so(2n)). */
  lieAlgebra(): string {
    return `so(${2 * this.n + 1})`;
  }
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
