// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (holonomic/recurrence.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Recurrence operators and holonomic sequences (SymPy
 * sympy.holonomic.recurrence): the algebra of operators in the shift `Sn`
 * with polynomial coefficients, following the rule Sn*a(n) = a(n + 1)*Sn.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Rational, Sym } from '../core/nodes';
import { at, first } from '../core/guard';
import { sympify } from '../core/ops';
import { str } from '../printing/str';
import { DMP } from '../polys/domains';
import type { GlobalPolynomialRing } from '../polys/domains';

const isList = (u: readonly ExprLike[] | ExprLike): u is readonly ExprLike[] => Array.isArray(u);

/** An operand of the operator arithmetic: an operator, a polynomial of the base ring or an expression. */
export type RecurrenceOperand = RecurrenceOperator | DMP | ExprLike;

/**
 * The algebra of recurrence operators over a base polynomial ring and the
 * shift operator `Sn` (SymPy RecurrenceOperators).
 */
export function RecurrenceOperators(base: GlobalPolynomialRing, generator?: string | Sym): [RecurrenceOperatorAlgebra, RecurrenceOperator] {
  const ring = new RecurrenceOperatorAlgebra(base, generator);
  return [ring, ring.shiftOperator];
}

/**
 * Noncommutative polynomials in `Sn` with coefficients in a base ring, with
 * Sn*a(n) = a(n + 1)*Sn (SymPy RecurrenceOperatorAlgebra).
 */
export class RecurrenceOperatorAlgebra {
  /** The shift operator `Sn` (SymPy shift_operator). */
  readonly shiftOperator: RecurrenceOperator;
  /** The generator symbol (SymPy gen_symbol). */
  readonly genSymbol: Sym;
  constructor(
    readonly base: GlobalPolynomialRing,
    generator?: string | Sym,
  ) {
    this.shiftOperator = new RecurrenceOperator([base.zero, base.one], this);
    this.genSymbol = generator instanceof Sym ? generator : new Sym(generator ?? 'Sn', { commutative: false });
  }
  toString(): string {
    return `Univariate Recurrence Operator Algebra in intermediate ${str(this.genSymbol)} over the base ring ${this.base.toString()}`;
  }
  equals(o: RecurrenceOperatorAlgebra): boolean {
    return this.base.equals(o.base) && this.genSymbol.key === o.genSymbol.key;
  }
}

/** Polynomials of two lists added termwise (SymPy _add_lists). */
export function addLists<T extends { add(o: T): T }>(list1: readonly T[], list2: readonly T[]): T[] {
  const n = Math.min(list1.length, list2.length);
  const sol: T[] = [];
  for (let i = 0; i < n; i++) sol.push(at(list1, i).add(at(list2, i)));
  return [...sol, ...(list1.length <= list2.length ? list2 : list1).slice(n)];
}

/** Equal lists of polynomials (Python list equality). */
export function listsEqual(a: readonly DMP[], b: readonly DMP[]): boolean {
  return a.length === b.length && a.every((p, i) => p.equals(at(b, i)));
}

/**
 * A recurrence operator: a list of polynomials of the base ring, one for each
 * power of `Sn` (SymPy RecurrenceOperator).
 */
export class RecurrenceOperator {
  /** The coefficients of Sn**0, Sn**1, ... (SymPy listofpoly). */
  readonly listofpoly: DMP[];
  constructor(
    listOfPoly: readonly (DMP | ExprLike)[],
    readonly parent: RecurrenceOperatorAlgebra,
  ) {
    this.listofpoly = listOfPoly.map((j) => (j instanceof DMP ? j : parent.base.fromSympy(j)));
  }
  /** The highest power of `Sn`. */
  get order(): number {
    return this.listofpoly.length - 1;
  }
  private poly(o: DMP | ExprLike): DMP {
    return o instanceof DMP ? o : this.parent.base.fromSympy(sympify(o));
  }
  /** self*other with Sn*a(n) = a(n + 1)*Sn (SymPy __mul__). */
  mul(other: RecurrenceOperand): RecurrenceOperator {
    const listofself = this.listofpoly;
    let listofother = other instanceof RecurrenceOperator ? other.listofpoly : [this.poly(other)];
    const mulDmp = (b: DMP, l: readonly DMP[]): DMP[] => l.map((i) => i.mul(b));
    let sol = mulDmp(first(listofself), listofother);
    // Sn**i * b
    const mulSnB = (b: readonly DMP[]): DMP[] => [this.parent.base.zero, ...b.map((i) => i.shift(Rational.of(1n)))];
    for (const p of listofself.slice(1)) {
      listofother = mulSnB(listofother);
      sol = addLists(sol, mulDmp(p, listofother));
    }
    return new RecurrenceOperator(sol, this.parent);
  }
  /** other*self for a polynomial or expression (SymPy __rmul__). */
  rmul(other: DMP | ExprLike): RecurrenceOperator {
    const o = this.poly(other);
    return new RecurrenceOperator(
      this.listofpoly.map((j) => o.mul(j)),
      this.parent,
    );
  }
  /** self + other (SymPy __add__ and __radd__). */
  add(other: RecurrenceOperand): RecurrenceOperator {
    if (other instanceof RecurrenceOperator) return new RecurrenceOperator(addLists(this.listofpoly, other.listofpoly), this.parent);
    return new RecurrenceOperator([first(this.listofpoly).add(this.poly(other)), ...this.listofpoly.slice(1)], this.parent);
  }
  /** self - other. */
  sub(other: RecurrenceOperand): RecurrenceOperator {
    return this.add(other instanceof RecurrenceOperator ? other.rmul(-1) : this.poly(other).neg());
  }
  /** other - self. */
  rsub(other: DMP | ExprLike): RecurrenceOperator {
    return this.rmul(-1).add(other);
  }
  /** -self. */
  neg(): RecurrenceOperator {
    return this.rmul(-1);
  }
  /** self**n for an integer n >= 0 (SymPy __pow__). */
  pow(nIn: number): RecurrenceOperator {
    if (nIn === 1) return this;
    let result = new RecurrenceOperator([this.parent.base.one], this.parent);
    if (nIn === 0) return result;
    const base = this.parent.base;
    if (listsEqual(this.listofpoly, this.parent.shiftOperator.listofpoly)) {
      return new RecurrenceOperator([...Array.from({ length: nIn }, () => base.zero), base.one], this.parent);
    }
    let x: RecurrenceOperator = this;
    let n = nIn;
    for (;;) {
      if (n % 2) result = result.mul(x);
      n = Math.floor(n / 2);
      if (!n) break;
      x = x.mul(x);
    }
    return result;
  }
  toString(): string {
    let printStr = '';
    for (const [i, j] of this.listofpoly.entries()) {
      if (j.isZero) continue;
      const s = str(j.toSympy());
      if (i === 0) {
        printStr += `(${s})`;
        continue;
      }
      if (printStr) printStr += ' + ';
      printStr += i === 1 ? `(${s})Sn` : `(${s})Sn**${i}`;
    }
    return printStr;
  }
  /**
   * Equality with an operator, or with a polynomial or expression (the
   * operator of order 0). SymPy compares the higher coefficients with the
   * zero element by identity, so an operator with zero higher coefficients
   * never equals a polynomial there; here they are compared by value.
   */
  equals(other: RecurrenceOperand): boolean {
    if (other instanceof RecurrenceOperator) return listsEqual(this.listofpoly, other.listofpoly) && this.parent.equals(other.parent);
    return first(this.listofpoly).equals(other instanceof DMP ? other : sympify(other)) && this.listofpoly.slice(1).every((p) => p.isZero);
  }
}

/**
 * A sequence satisfying a linear homogeneous recurrence with polynomial
 * coefficients, with optional initial values u(0), u(1), ... (SymPy
 * HolonomicSequence).
 */
export class HolonomicSequence {
  /** The initial values. */
  readonly u0: Expr[];
  /** The variable of the recurrence. */
  readonly n: Sym;
  constructor(
    readonly recurrence: RecurrenceOperator,
    u0: readonly ExprLike[] | ExprLike = [],
  ) {
    this.u0 = isList(u0) ? u0.map((u) => sympify(u)) : [sympify(u0)];
    this.n = recurrence.parent.base.gen;
  }
  /** Whether initial values are given (SymPy _have_init_cond). */
  get haveInitCond(): boolean {
    return this.u0.length > 0;
  }
  toString(): string {
    const s = `HolonomicSequence(${this.recurrence.toString()}, ${str(this.n)})`;
    return s + this.u0.map((u, i) => `, u(${i}) = ${str(u)}`).join('');
  }
  equals(o: HolonomicSequence): boolean {
    if (!this.recurrence.equals(o.recurrence) || this.n.key !== o.n.key) return false;
    if (this.haveInitCond && o.haveInitCond) return this.u0.length === o.u0.length && this.u0.every((u, i) => u.key === at(o.u0, i).key);
    return true;
  }
}
