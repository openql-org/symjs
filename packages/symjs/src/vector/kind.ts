// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/vector/kind.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.vector.kind: VectorKind, the kind of vectors
 * (`kindOf(v)` of `@symjs/symjs/tensor`).
 */

import { Kind, NumberKind } from '../core/kind';
import { callableClass } from '../core/callable';

const vectorKinds = new Map<Kind, VectorKindNode>();

/**
 * The kind of vectors whose components have `elementKind`. Use `VectorKind(k)` (cached, so equal
 * kinds are the same object, as in SymPy).
 *
 * @see SymPy `sympy.vector.kind.VectorKind`
 * @example
 * ```ts
 * import { CoordSys3D, VectorKind, kindOf } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * kindOf(R.i) === VectorKind(); // => True
 * ```
 */
export class VectorKindNode extends Kind {
  /**
   * Constructs an instance of `VectorKindNode`.
   *
   * @param elementKind - Kind of the component values.
   */
  constructor(
    /** Kind of the component values. */
    readonly elementKind: Kind = NumberKind) {
    super();
  }
  /**
   * Obtains the vector kind associated with a particular element kind.
   *
   * @param elementKind - Kind of the component values.
   * @returns The corresponding vector kind.
   */
  static of(elementKind: Kind = NumberKind): VectorKindNode {
    let k = vectorKinds.get(elementKind);
    if (!k) {
      k = new VectorKindNode(elementKind);
      vectorKinds.set(elementKind, k);
    }
    return k;
  }
  /**
   * Formats this vector kind as text.
   *
   * @returns The formatted text.
   */
  toString(): string {
    return `VectorKind(${this.elementKind.toString()})`;
  }
}

/**
 * Constructs the kind of a vector from its component kind, defaulting to numeric components.
 *
 * @param elementKind - Kind of the component values.
 * @returns The cached kind for vectors with components of the specified kind.
 * @see SymPy `sympy.vector.kind.VectorKind`
 * @example
 * ```ts
 * import { CoordSys3D, VectorKind, kindOf } from '@symjs/symjs';
 *
 * const R = CoordSys3D('R');
 * kindOf(R.i) === VectorKind(); // => True
 * ```
 */
export const VectorKind = /* @__PURE__ */ callableClass(VectorKindNode, (elementKind: Kind = NumberKind): VectorKindNode => VectorKindNode.of(elementKind));
export type VectorKind = VectorKindNode;
