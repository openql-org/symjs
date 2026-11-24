// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/** Mathematical kind of matrix expressions (SymPy matrices.kind). */
import { Kind, NumberKind } from '../core/kind';
import { callableClass } from '../core/callable';
const cache = new Map<Kind, MatrixKindNode>();
/**
 * The mathematical kind of a matrix with a given element kind.
 * @see SymPy `sympy.matrices.kind.MatrixKind`
 * @example
 * ```ts
 * import { MatrixKind, MatrixKindNode, NumberKind } from '@symjs/symjs';
 * MatrixKind(NumberKind) instanceof MatrixKindNode; // => True
 * ```
 */
export class MatrixKindNode extends Kind {
  /**
   * Constructs a `MatrixKind`.
   * @param elementKind - The mathematical kind of the entries.
   */
  constructor(
    /** The mathematical kind shared by the matrix entries. */
    readonly elementKind: Kind = NumberKind
  ) { super(); }
  /**
   * Gets the shared matrix kind for the specified element kind.
   * @param elementKind - The mathematical kind of the entries.
   * @returns The shared kind for these entries.
   */
  static of(elementKind: Kind = NumberKind): MatrixKindNode {
    let kind = cache.get(elementKind);
    if (kind === undefined) { kind = new MatrixKindNode(elementKind); cache.set(elementKind, kind); }
    return kind;
  }
  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string { return `MatrixKind(${this.elementKind.toString()})`; }
}
/**
 * Identifies matrices by the mathematical kind of their entries.
 * @param elementKind - The mathematical kind of the entries.
 * @returns The shared kind for the given element kind.
 * @see SymPy `sympy.matrices.kind.MatrixKind`
 * @example
 * ```ts
 * import { MatrixKind, NumberKind } from '@symjs/symjs';
 * String(MatrixKind(NumberKind)); // => MatrixKind(NumberKind)
 * ```
 */
export const MatrixKind = callableClass(MatrixKindNode, (elementKind?: Kind): MatrixKindNode => MatrixKindNode.of(elementKind));
