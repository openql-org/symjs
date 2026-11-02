// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy kinds (sympy.core.kind) as far as N-dimensional arrays need
 * them: NumberKind, BooleanKind, UndefinedKind and ArrayKind.
 */

/** SymPy Kind: the mathematical kind of an object (number, boolean, array, ...). */
export abstract class Kind {
  abstract toString(): string;
  [Symbol.for('nodejs.util.inspect.custom')](): string {
    return this.toString();
  }
}

class NamedKind extends Kind {
  constructor(readonly name: string) {
    super();
  }
  toString(): string {
    return this.name;
  }
}

/** SymPy NumberKind: the kind of numbers and commutative expressions. */
export const NumberKind: Kind = new NamedKind('NumberKind');
/** SymPy BooleanKind: the kind of relations and boolean values. */
export const BooleanKind: Kind = new NamedKind('BooleanKind');
/** SymPy UndefinedKind: the kind is not known. */
export const UndefinedKind: Kind = new NamedKind('UndefinedKind');

const arrayKinds = new Map<Kind, ArrayKindNode>();

/**
 * SymPy ArrayKind(element_kind): the kind of N-dimensional arrays whose
 * elements have `elementKind`. Use `ArrayKind(k)` (cached, so equal kinds
 * are the same object, as in SymPy).
 */
export class ArrayKindNode extends Kind {
  constructor(readonly elementKind: Kind = NumberKind) {
    super();
  }
  /** The cached ArrayKind of the given element kind. */
  static of(elementKind: Kind = NumberKind): ArrayKindNode {
    let k = arrayKinds.get(elementKind);
    if (!k) {
      k = new ArrayKindNode(elementKind);
      arrayKinds.set(elementKind, k);
    }
    return k;
  }
  /**
   * SymPy ArrayKind._union: ArrayKind of the common kind of the elements,
   * or ArrayKind(UndefinedKind) when they differ.
   */
  static union(kinds: readonly Kind[]): ArrayKindNode {
    const set = new Set(kinds);
    return ArrayKindNode.of(set.size === 1 ? [...set][0]! : UndefinedKind);
  }
  toString(): string {
    return `ArrayKind(${this.elementKind.toString()})`;
  }
}
