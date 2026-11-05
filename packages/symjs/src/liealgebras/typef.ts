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

/** SymPy TypeF: the exceptional Cartan type F_4. */
export class TypeF extends StandardCartan {
  constructor(n: number) {
    if (n !== 4) throw new RangeError('n should be 4');
    super('F', 4);
  }
  dimension(): number {
    return 4;
  }
  /** SymPy basic_root: 1 at i and -1 at j. */
  basicRoot(i: number, j: number): Root {
    return basicRoot(4, i, j);
  }
  simpleRoot(i: number): Root {
    if (i < 3) return this.basicRoot(i - 1, i);
    if (i === 3) return [0, 0, 0, 1];
    return filled(4, NEG_HALF);
  }
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
  roots(): number {
    return 48;
  }
  cartanMatrix(): Matrix {
    return Matrix.of([
      [2, -1, 0, 0],
      [-1, 2, -2, 0],
      [0, -1, 2, -1],
      [0, 0, -1, 2],
    ]);
  }
  basis(): number {
    return 52;
  }
  dynkinDiagram(): string {
    return `0---0=>=0---0\n${labels(1, 4)}`;
  }
}
