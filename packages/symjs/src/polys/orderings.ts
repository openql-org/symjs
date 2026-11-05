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

/** Python's ordering of keys: numbers numerically, tuples lexicographically. */
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

/** Lexicographic order of monomials (SymPy LexOrder). */
export class LexOrder extends Ordering {
  readonly alias: string = 'lex';
  readonly isGlobal: boolean = true;
  key(monomial: readonly number[]): MonomialKey {
    return [...monomial];
  }
}

/** Graded lexicographic order of monomials (SymPy GradedLexOrder). */
export class GradedLexOrder extends Ordering {
  readonly alias: string = 'grlex';
  readonly isGlobal: boolean = true;
  key(monomial: readonly number[]): MonomialKey {
    return [monomial.reduce((s, m) => s + m, 0), [...monomial]];
  }
}

/** Reversed graded lexicographic order of monomials (SymPy ReversedGradedLexOrder). */
export class ReversedGradedLexOrder extends Ordering {
  readonly alias: string = 'grevlex';
  readonly isGlobal: boolean = true;
  key(monomial: readonly number[]): MonomialKey {
    return [monomial.reduce((s, m) => s + m, 0), monomial.map((m) => -m).reverse()];
  }
}

/** The inverse of a monomial order, a local order (SymPy InverseOrder). */
export class InverseOrder extends Ordering {
  readonly alias: string;
  readonly isGlobal: boolean;
  constructor(readonly O: LexOrder | GradedLexOrder | ReversedGradedLexOrder) {
    super();
    this.alias = 'i' + O.alias;
    this.isGlobal = false;
  }
  key(monomial: readonly number[]): MonomialKey {
    const inv = (k: MonomialKey): MonomialKey => (typeof k === 'number' ? -k : k.map(inv));
    return inv(this.O.key(monomial));
  }
}

/** A monomial order object of symjs. */
export type MonomialOrdering = LexOrder | GradedLexOrder | ReversedGradedLexOrder | InverseOrder;

/** Lexicographic order (SymPy lex). */
export const lex: LexOrder = new LexOrder();
/** Graded lexicographic order (SymPy grlex). */
export const grlex: GradedLexOrder = new GradedLexOrder();
/** Reversed graded lexicographic order (SymPy grevlex). */
export const grevlex: ReversedGradedLexOrder = new ReversedGradedLexOrder();
/** Inverse lexicographic order (SymPy ilex). */
export const ilex: InverseOrder = new InverseOrder(lex);
/** Inverse graded lexicographic order (SymPy igrlex). */
export const igrlex: InverseOrder = new InverseOrder(grlex);
/** Inverse reversed graded lexicographic order (SymPy igrevlex). */
export const igrevlex: InverseOrder = new InverseOrder(grevlex);

const ORDERS: Readonly<Record<string, MonomialOrdering>> = { lex, grlex, grevlex, ilex, igrlex, igrevlex };

/**
 * The key function of an ordering given by name or object (SymPy
 * monomial_key): on exponent tuples, or, given generators, on expressions
 * (by the degrees of their polynomial in the generators).
 */
export function monomialKey(order?: string | MonomialOrdering): (monomial: readonly number[]) => MonomialKey;
export function monomialKey(order: string | MonomialOrdering | undefined, gens: readonly Expr[]): (expr: Expr) => MonomialKey;
export function monomialKey(order: string | MonomialOrdering = lex, gens?: readonly Expr[]): ((monomial: readonly number[]) => MonomialKey) | ((expr: Expr) => MonomialKey) {
  const O = typeof order === 'string' ? ORDERS[order] : order;
  if (O === undefined) throw new RangeError(`supported monomial orderings are 'lex', 'grlex' and 'grevlex', got '${String(order)}'`);
  if (gens) return (expr: Expr) => O.key(Poly.from(expr, gens).degreeList());
  return (monomial: readonly number[]) => O.key(monomial);
}
