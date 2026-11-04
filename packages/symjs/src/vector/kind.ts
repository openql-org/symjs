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
 * SymPy VectorKind(element_kind): the kind of vectors whose components
 * have `elementKind`. Use `VectorKind(k)` (cached, so equal kinds are the
 * same object, as in SymPy).
 */
export class VectorKindNode extends Kind {
  constructor(readonly elementKind: Kind = NumberKind) {
    super();
  }
  /** The cached VectorKind of the given element kind. */
  static of(elementKind: Kind = NumberKind): VectorKindNode {
    let k = vectorKinds.get(elementKind);
    if (!k) {
      k = new VectorKindNode(elementKind);
      vectorKinds.set(elementKind, k);
    }
    return k;
  }
  toString(): string {
    return `VectorKind(${this.elementKind.toString()})`;
  }
}

/** SymPy VectorKind(element_kind): the kind of vectors (cached, VectorKind(NumberKind) by default). */
export const VectorKind = /* @__PURE__ */ callableClass(VectorKindNode, (elementKind: Kind = NumberKind): VectorKindNode => VectorKindNode.of(elementKind));
export type VectorKind = VectorKindNode;
