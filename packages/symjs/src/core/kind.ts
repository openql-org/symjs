// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy kinds (sympy.core.kind) as far as N-dimensional arrays need
 * them: NumberKind, BooleanKind, UndefinedKind and ArrayKind.
 */

import { at } from './guard';

/**
 * The mathematical kind of an object (number, boolean, array, ...).
 *
 * @see SymPy `sympy.core.kind.Kind`
 */
export abstract class Kind {
  /**
   * Formats the object as a string.
   *
   * @returns The formatted string.
   */
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

/**
 * The kind of numbers and commutative expressions.
 *
 * @see SymPy `sympy.core.kind.NumberKind`
 * @example
 * ```ts
 * import { NumberKind } from '@symjs/symjs';
 *
 * NumberKind.toString(); // => NumberKind
 * ```
 */
export const NumberKind: Kind = new NamedKind('NumberKind');
/**
 * The kind of relations and boolean values.
 *
 * @see SymPy `sympy.core.kind.BooleanKind`
 * @example
 * ```ts
 * import { BooleanKind } from '@symjs/symjs';
 *
 * BooleanKind.toString(); // => BooleanKind
 * ```
 */
export const BooleanKind: Kind = new NamedKind('BooleanKind');
/**
 * The kind is not known.
 *
 * @see SymPy `sympy.core.kind.UndefinedKind`
 * @example
 * ```ts
 * import { UndefinedKind } from '@symjs/symjs';
 *
 * UndefinedKind.toString(); // => UndefinedKind
 * ```
 */
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
    return ArrayKindNode.of(set.size === 1 ? at(kinds, 0) : UndefinedKind);
  }
  toString(): string {
    return `ArrayKind(${this.elementKind.toString()})`;
  }
}

/**
 * The kinds of the ordered elements of a SymPy Tuple.
 *
 * @see SymPy `sympy.core.containers.TupleKind`
 * @example
 * ```ts
 * import { BooleanKind, NumberKind, TupleKind } from '@symjs/symjs';
 *
 * new TupleKind(NumberKind, BooleanKind).toString(); // => TupleKind(NumberKind, BooleanKind)
 * ```
 */
export class TupleKind extends Kind {
  /** The kinds of the tuple elements in order. */
  readonly elementKind: readonly Kind[];
  /**
   * Creates a `TupleKind`.
   *
   * @param elementKind - The kinds of the tuple elements in order.
   */
  constructor(...elementKind: Kind[]) {
    super();
    this.elementKind = elementKind;
  }
  /**
   * Formats the object as a string.
   *
   * @returns The formatted string.
   */
  toString(): string {
    return `TupleKind(${this.elementKind.map((kind) => kind.toString()).join(', ')})`;
  }
}
