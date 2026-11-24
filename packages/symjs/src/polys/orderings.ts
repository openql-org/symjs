// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Monomial orderings (SymPy sympy.polys.orderings): lex, grlex,
 * grevlex and their inverses. An ordering maps an exponent tuple to a sort
 * key (SymPy calls the order object, `order(monom)`; symjs uses
 * `order.key(monom)`); keys are compared lexicographically with
 * `compareMonomialKeys`, and `order.compare(a, b)` compares two monomials.
 */

import { at } from '../core/guard';
import type { Expr } from '../core/nodes';
import { Poly } from './sympoly';

/** A sort key of a monomial: a number or a tuple of keys (Python tuple order). */
export type MonomialKey = number | readonly MonomialKey[];

/**
 * Python's ordering of keys: numbers numerically, tuples lexicographically.
 *
 * @param a - First monomial comparison key.
 * @param b - Second monomial comparison key.
 * @returns A negative, zero or positive number according to the comparison.
 */
export function compareMonomialKeys(a: MonomialKey, b: MonomialKey): number {
  if (typeof a === 'number' || typeof b === 'number') return Number(a) - Number(b);
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = compareMonomialKeys(at(a, i), at(b, i));
    if (c) return c;
  }
  return a.length - b.length;
}

/** A monomial ordering (SymPy MonomialOrder). */
abstract class Ordering {
  /** The name of the ordering (SymPy alias). */
  abstract readonly alias: string;
  /** Whether the ordering is global (a well-ordering) or local (SymPy is_global). */
  abstract readonly isGlobal: boolean;
  /** The sort key of an exponent tuple (SymPy order(monomial)). */
  abstract key(monomial: readonly number[]): MonomialKey;
  /** Negative, zero or positive as a is smaller than, equal to or greater than b. */
  compare(a: readonly number[], b: readonly number[]): number {
    return compareMonomialKeys(this.key(a), this.key(b));
  }
  toString(): string {
    return this.alias;
  }
}

/**
 * Lexicographic order of monomials.
 *
 * @see SymPy `sympy.polys.orderings.LexOrder`
 */
export class LexOrder extends Ordering {
  /**
   * The short name of the monomial order.
   *
   * @see SymPy `sympy.polys.orderings.LexOrder.alias`
   */
  readonly alias: string = 'lex';
  /**
   * Whether the identity monomial is minimal in this order.
   *
   * @see SymPy `sympy.polys.orderings.LexOrder.is_global`
   */
  readonly isGlobal: boolean = true;
  /**
   * The comparison key for a monomial in this order.
   *
   * @param monomial - Exponent vector of the monomial.
   * @returns The comparison key for a monomial in this order.
   * @see SymPy `sympy.polys.orderings.LexOrder.__call__`
   */
  key(monomial: readonly number[]): MonomialKey {
    return [...monomial];
  }
}

/**
 * Graded lexicographic order of monomials.
 *
 * @see SymPy `sympy.polys.orderings.GradedLexOrder`
 */
export class GradedLexOrder extends Ordering {
  /**
   * The short name of the monomial order.
   *
   * @see SymPy `sympy.polys.orderings.GradedLexOrder.alias`
   */
  readonly alias: string = 'grlex';
  /**
   * Whether the identity monomial is minimal in this order.
   *
   * @see SymPy `sympy.polys.orderings.GradedLexOrder.is_global`
   */
  readonly isGlobal: boolean = true;
  /**
   * The comparison key for a monomial in this order.
   *
   * @param monomial - Exponent vector of the monomial.
   * @returns The comparison key for a monomial in this order.
   * @see SymPy `sympy.polys.orderings.GradedLexOrder.__call__`
   */
  key(monomial: readonly number[]): MonomialKey {
    return [monomial.reduce((s, m) => s + m, 0), [...monomial]];
  }
}

/**
 * Reversed graded lexicographic order of monomials.
 *
 * @see SymPy `sympy.polys.orderings.ReversedGradedLexOrder`
 */
export class ReversedGradedLexOrder extends Ordering {
  /**
   * The short name of the monomial order.
   *
   * @see SymPy `sympy.polys.orderings.ReversedGradedLexOrder.alias`
   */
  readonly alias: string = 'grevlex';
  /**
   * Whether the identity monomial is minimal in this order.
   *
   * @see SymPy `sympy.polys.orderings.ReversedGradedLexOrder.is_global`
   */
  readonly isGlobal: boolean = true;
  /**
   * The comparison key for a monomial in this order.
   *
   * @param monomial - Exponent vector of the monomial.
   * @returns The comparison key for a monomial in this order.
   * @see SymPy `sympy.polys.orderings.ReversedGradedLexOrder.__call__`
   */
  key(monomial: readonly number[]): MonomialKey {
    return [monomial.reduce((s, m) => s + m, 0), monomial.map((m) => -m).reverse()];
  }
}

/**
 * The inverse of a monomial order, a local order.
 *
 * @see SymPy `sympy.polys.orderings.InverseOrder`
 * @remarks SymPy returns `(-2, -3)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { InverseOrder, lex } from '@symjs/symjs';
 *
 * new InverseOrder(lex).key([2, 3]); // => [-2, -3]
 * ```
 */
export class InverseOrder extends Ordering {
  /**
   * The short name of the monomial order.
   *
   * @see SymPy `sympy.polys.orderings.InverseOrder.alias`
   */
  readonly alias: string;
  /**
   * Whether the identity monomial is minimal in this order.
   *
   * @see SymPy `sympy.polys.orderings.InverseOrder.is_global`
   */
  readonly isGlobal: boolean;
  /**
   * Construct a `InverseOrder` instance.
   *
   * @param O - Monomial ordering used to compare terms.
   */
  constructor(
    /** The order whose comparison is reversed. @see SymPy `sympy.polys.orderings.InverseOrder.O` */
    readonly O: LexOrder | GradedLexOrder | ReversedGradedLexOrder) {
    super();
    this.alias = 'i' + O.alias;
    this.isGlobal = false;
  }
  /**
   * The comparison key for a monomial in this order.
   *
   * @param monomial - Exponent vector of the monomial.
   * @returns The comparison key for a monomial in this order.
   * @see SymPy `sympy.polys.orderings.InverseOrder.__call__`
   */
  key(monomial: readonly number[]): MonomialKey {
    const inv = (k: MonomialKey): MonomialKey => (typeof k === 'number' ? -k : k.map(inv));
    return inv(this.O.key(monomial));
  }
}

/** A monomial order object of symjs. */
export type MonomialOrdering = LexOrder | GradedLexOrder | ReversedGradedLexOrder | InverseOrder | ProductOrder;

/**
 * Lexicographic order.
 *
 * @see SymPy `sympy.polys.orderings.lex`
 */
export const lex: LexOrder = new LexOrder();
/**
 * Graded lexicographic order.
 *
 * @see SymPy `sympy.polys.orderings.grlex`
 */
export const grlex: GradedLexOrder = new GradedLexOrder();
/**
 * Reversed graded lexicographic order.
 *
 * @see SymPy `sympy.polys.orderings.grevlex`
 */
export const grevlex: ReversedGradedLexOrder = new ReversedGradedLexOrder();
/**
 * Inverse lexicographic order.
 *
 * @see SymPy `sympy.polys.orderings.ilex`
 * @remarks SymPy returns `(-2, -3)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ilex } from '@symjs/symjs';
 *
 * ilex.key([2, 3]); // => [-2, -3]
 * ```
 */
export const ilex: InverseOrder = new InverseOrder(lex);
/**
 * Inverse graded lexicographic order.
 *
 * @see SymPy `sympy.polys.orderings.igrlex`
 * @remarks SymPy returns `(-5, (-2, -3))` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { igrlex } from '@symjs/symjs';
 *
 * igrlex.key([2, 3]); // => [-5, [-2, -3]]
 * ```
 */
export const igrlex: InverseOrder = new InverseOrder(grlex);
/**
 * Inverse reversed graded lexicographic order.
 *
 * @see SymPy `sympy.polys.orderings.igrevlex`
 * @remarks SymPy returns `(-5, (3, 2))` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { igrevlex } from '@symjs/symjs';
 *
 * igrevlex.key([2, 3]); // => [-5, [3, 2]]
 * ```
 */
export const igrevlex: InverseOrder = new InverseOrder(grevlex);

const ORDERS: Readonly<Record<string, MonomialOrdering>> = { lex, grlex, grevlex, ilex, igrlex, igrevlex };

/**
 * The order of the keys of several orderings,
 * each applied to a selection of the exponents (a product order, compared
 * lexicographically).
 *
 * @see SymPy `sympy.polys.orderings.ProductOrder`
 * @remarks SymPy returns `((2,), (4, (3, 1)))` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ProductOrder, grlex, lex } from '@symjs/symjs';
 *
 * new ProductOrder([lex, [0]], [grlex, [1, 2]]).key([2, 3, 1]); // => [[2], [4, [3, 1]]]
 * ```
 */
export class ProductOrder {
  /**
   * The short name of the monomial order.
   *
   * @see SymPy `sympy.polys.orderings.ProductOrder.alias`
   */
  readonly alias = 'ProductOrder';
  /**
   * The component orders and the generator positions to which they apply.
   *
   * @see SymPy `sympy.polys.orderings.ProductOrder.args`
   */
  readonly args: readonly (readonly [MonomialOrdering, readonly number[]])[];
  /**
   * Construct a `ProductOrder` instance.
   *
   * @param args - Arguments to the operation.
   */
  constructor(...args: (readonly [MonomialOrdering, readonly number[]])[]) {
    this.args = args;
  }
  /**
   * The tuple of the keys of the selected exponents.
   *
   * @param monomial - Exponent vector of the monomial.
   * @returns The tuple of the keys of the selected exponents.
   * @see SymPy `sympy.polys.orderings.ProductOrder.__call__`
   */
  key(monomial: readonly number[]): MonomialKey[] {
    return this.args.map(([O, idx]) => O.key(idx.map((i) => at(monomial, i))));
  }
  /**
   * Negative, zero or positive as a is smaller than, equal to or greater than b.
   *
   * @param a - First operand.
   * @param b - Second operand.
   * @returns A negative, zero or positive number according to the product order.
   */
  compare(a: readonly number[], b: readonly number[]): number {
    return compareMonomialKeys(this.key(a), this.key(b));
  }
  /**
   * True when every ordering is global, false when none is, else 'unknown'.
   *
   * @returns True when every ordering is global, false when none is, else 'unknown'.
   * @see SymPy `sympy.polys.orderings.ProductOrder.is_global`
   */
  get isGlobal(): boolean | 'unknown' {
    if (this.args.every(([O]) => O.isGlobal === true)) return true;
    if (this.args.every(([O]) => O.isGlobal === false)) return false;
    return 'unknown';
  }
  /**
   * The printable representation.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.polys.orderings.ProductOrder.__str__`
   */
  toString(): string {
    return `ProductOrder(${this.args.map(([O]) => O.alias).join(', ')})`;
  }
}

/**
 * The product order of orderings
 * given by name, each on its own generators, e.g.
 * buildProductOrder([['grlex', x, y], ['grlex', z, t]], [x, y, z, t]).
 *
 * @param arg - Input value.
 * @param gens - Polynomial generators in the desired order.
 * @returns The product order of orderings given by name, each on its own generators, e.g. buildProductOrder([['grlex', x, y], ['grlex', z, t]], [x, y, z, t]).
 * @throws RangeError when the specified generator or index is invalid or the requested monomial order is not recognized.
 * @see SymPy `sympy.polys.orderings.build_product_order`
 * @example
 * ```ts
 * import { buildProductOrder, ex } from '@symjs/symjs';
 *
 * buildProductOrder([['grlex', ex`x`, ex`y`], ['grlex', ex`z`, ex`t`]], [ex`x`, ex`y`, ex`z`, ex`t`]).toString(); // => ProductOrder(grlex, grlex)
 * ```
 */
export function buildProductOrder(arg: readonly (readonly [string, ...Expr[]])[], gens: readonly Expr[]): ProductOrder {
  const index = (g: Expr): number => {
    const i = gens.findIndex((h) => h.key === g.key);
    if (i < 0) throw new RangeError(`${String(g)} is not a generator`);
    return i;
  };
  return new ProductOrder(
    ...arg.map(([name, ...vars]): readonly [MonomialOrdering, readonly number[]] => {
      const O = ORDERS[name];
      if (O === undefined) throw new RangeError(`supported monomial orderings are 'lex', 'grlex' and 'grevlex', got '${name}'`);
      return [O, vars.map(index)];
    }),
  );
}

/**
 * The key function of an ordering given by name or object (SymPy
 * monomial_key): on exponent tuples, or, given generators, on expressions
 * (by the degrees of their polynomial in the generators).
 *
 * @param order - Monomial order used to compare terms.
 * @returns The key function of an ordering given by name or object (SymPy monomial_key): on exponent tuples, or, given generators, on expressions (by the degrees of their polynomial in the generators).
 * @throws RangeError when the requested monomial order is not recognized.
 * @see SymPy `sympy.polys.orderings.monomial_key`
 */
export function monomialKey(order?: string | MonomialOrdering): (monomial: readonly number[]) => MonomialKey;
/**
 * The key function of an ordering given by name or object (SymPy
 * monomial_key): on exponent tuples, or, given generators, on expressions
 * (by the degrees of their polynomial in the generators).
 *
 * @param order - Monomial order used to compare terms.
 * @param gens - Polynomial generators in the desired order.
 * @returns The key function of an ordering given by name or object (SymPy monomial_key): on exponent tuples, or, given generators, on expressions (by the degrees of their polynomial in the generators).
 * @throws RangeError when the requested monomial order is not recognized.
 * @see SymPy `sympy.polys.orderings.monomial_key`
 */
export function monomialKey(order: string | MonomialOrdering | undefined, gens: readonly Expr[]): (expr: Expr) => MonomialKey;
export function monomialKey(order: string | MonomialOrdering = lex, gens?: readonly Expr[]): ((monomial: readonly number[]) => MonomialKey) | ((expr: Expr) => MonomialKey) {
  const O = typeof order === 'string' ? ORDERS[order] : order;
  if (O === undefined) throw new RangeError(`supported monomial orderings are 'lex', 'grlex' and 'grevlex', got '${String(order)}'`);
  if (gens) return (expr: Expr) => O.key(Poly.from(expr, gens).degreeList());
  return (monomial: readonly number[]) => O.key(monomial);
}
