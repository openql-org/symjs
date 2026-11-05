// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type A_n (SymPy sympy.liealgebras.type_a): the Lie algebra su(n + 1).
 */

import type { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan, basicRoot, cartanFrom, chain, labels } from './standard';

/** SymPy TypeA: the Cartan type A_n, n >= 1. */
export class TypeA extends StandardCartan {
  constructor(n: number) {
    if (n < 1) throw new RangeError('n cannot be less than 1');
    super('A', n);
  }
  /** The roots live in an (n + 1)-dimensional space. */
  dimension(): number {
    return this.n + 1;
  }
  /** SymPy basic_root: 1 at i and -1 at j. */
  basicRoot(i: number, j: number): Root {
    return basicRoot(this.n + 1, i, j);
  }
  simpleRoot(i: number): Root {
    return this.basicRoot(i - 1, i);
  }
  positiveRoots(): Map<number, Root> {
    const out = new Map<number, Root>();
    for (let i = 0; i < this.n; i++) for (let j = i + 1; j <= this.n; j++) out.set(out.size + 1, this.basicRoot(i, j));
    return out;
  }
  /** SymPy highest_root: the highest root. */
  highestRoot(): Root {
    return this.basicRoot(0, this.n);
  }
  roots(): number {
    return this.n * (this.n + 1);
  }
  cartanMatrix(): Matrix {
    const e: [number, number, number][] = [];
    for (let i = 0; i < this.n - 1; i++) e.push([i, i + 1, -1], [i + 1, i, -1]);
    return cartanFrom(this.n, e);
  }
  /** The dimension (n + 1)**2 - 1 of su(n + 1) (SymPy gives n**2 - 1). */
  basis(): number {
    return (this.n + 1) ** 2 - 1;
  }
  /** SymPy lie_algebra: su(n + 1). */
  lieAlgebra(): string {
    return `su(${this.n + 1})`;
  }
  dynkinDiagram(): string {
    return `${chain(this.n)}\n${labels(1, this.n)}`;
  }
}
