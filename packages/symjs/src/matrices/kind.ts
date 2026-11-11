// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/** Mathematical kind of matrix expressions (SymPy matrices.kind). */
import { Kind, NumberKind } from '../core/kind';
import { callableClass } from '../core/callable';
const cache = new Map<Kind, MatrixKindNode>();
export class MatrixKindNode extends Kind {
  constructor(readonly elementKind: Kind = NumberKind) { super(); }
  static of(elementKind: Kind = NumberKind): MatrixKindNode {
    let kind = cache.get(elementKind);
    if (kind === undefined) { kind = new MatrixKindNode(elementKind); cache.set(elementKind, kind); }
    return kind;
  }
  toString(): string { return `MatrixKind(${this.elementKind.toString()})`; }
}
/** Cached kind of a matrix with elements of the given kind. */
export const MatrixKind = callableClass(MatrixKindNode, (elementKind?: Kind): MatrixKindNode => MatrixKindNode.of(elementKind));
