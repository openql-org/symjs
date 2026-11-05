// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Cartan type G_2 (SymPy sympy.liealgebras.type_g).
 */

import { Matrix } from '../matrices/matrix';
import type { Root } from './standard';
import { StandardCartan } from './standard';

/** SymPy TypeG: the exceptional Cartan type G_2 (roots in a 3-dimensional space). */
export class TypeG extends StandardCartan {
  constructor(n: number) {
    if (n !== 2) throw new RangeError('n should be 2');
    super('G', 2);
  }
  dimension(): number {
    return 3;
  }
  simpleRoot(i: number): Root {
    return i === 1 ? [0, 1, -1] : [1, -2, 1];
  }
  positiveRoots(): Map<number, Root> {
    return new Map<number, Root>([
      [1, [0, 1, -1]],
      [2, [1, -2, 1]],
      [3, [1, -1, 0]],
      [4, [1, 0, 1]],
      [5, [1, 1, -2]],
      [6, [2, -1, -1]],
    ]);
  }
  roots(): number {
    return 12;
  }
  cartanMatrix(): Matrix {
    return Matrix.of([
      [2, -1],
      [-3, 2],
    ]);
  }
  basis(): number {
    return 14;
  }
  dynkinDiagram(): string {
    return '0≡<≡0\n1   2';
  }
}
