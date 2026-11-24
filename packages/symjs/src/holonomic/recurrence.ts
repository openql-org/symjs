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
 * The algebra of recurrence operators over a base polynomial ring and the shift operator `Sn`.
 *
 * @param base - Coefficient ring of the operators.
 * @param generator - Name or symbol for the operator.
 * @returns The operator algebra and its generator.
 * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperators`
 * @example
 * ```ts
 * import { RecurrenceOperators, ZZ, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n', { integer: true });
 * const [, Sn] = RecurrenceOperators(ZZ.oldPolyRing(n), 'Sn');
 * Sn.mul(n).toString(); // => (n + 1)Sn
 * ```
 */
export function RecurrenceOperators(base: GlobalPolynomialRing, generator?: string | Sym): [RecurrenceOperatorAlgebra, RecurrenceOperator] {
  const ring = new RecurrenceOperatorAlgebra(base, generator);
  return [ring, ring.shiftOperator];
}

/**
 * Noncommutative polynomials in `Sn` with coefficients in a base ring, with Sn*a(n) = a(n + 1)*Sn.
 *
 * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperatorAlgebra`
 * @example
 * ```ts
 * import { RecurrenceOperators, ZZ, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n', { integer: true });
 * const [ring] = RecurrenceOperators(ZZ.oldPolyRing(n), 'Sn');
 * ring.toString(); // => Univariate Recurrence Operator Algebra in intermediate Sn over the base ring ZZ[n]
 * ```
 */
export class RecurrenceOperatorAlgebra {
  /**
   * The shift operator `Sn`.
   *
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperatorAlgebra.shift_operator`
   */
  readonly shiftOperator: RecurrenceOperator;
  /**
   * The generator symbol.
   *
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperatorAlgebra.gen_symbol`
   */
  readonly genSymbol: Sym;
  /**
   * Defines a shift operator algebra over the given polynomial ring.
   *
   * @param base - Polynomial coefficient ring.
   * @param generator - Name or symbol of the algebra generator.
   */
  constructor(
    /**
     * The base polynomial ring of the operator algebra.
     *
     * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperatorAlgebra.base`
     */
    readonly base: GlobalPolynomialRing,
    generator?: string | Sym,
  ) {
    this.shiftOperator = new RecurrenceOperator([base.zero, base.one], this);
    this.genSymbol = generator instanceof Sym ? generator : new Sym(generator ?? 'Sn', { commutative: false });
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperatorAlgebra.__str__`
   */
  toString(): string {
    return `Univariate Recurrence Operator Algebra in intermediate ${str(this.genSymbol)} over the base ring ${this.base.toString()}`;
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperatorAlgebra.__eq__`
   */
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
 * A recurrence operator: a list of polynomials of the base ring, one for each power of `Sn`.
 *
 * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator`
 * @example
 * ```ts
 * import { RecurrenceOperator, RecurrenceOperators, ZZ, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n', { integer: true });
 * const [ring] = RecurrenceOperators(ZZ.oldPolyRing(n), 'Sn');
 * new RecurrenceOperator([0, 1, n.pow(2)], ring).toString(); // => (1)Sn + (n**2)Sn**2
 * ```
 */
export class RecurrenceOperator {
  /**
   * The polynomial coefficients in ascending powers of the shift operator.
   *
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.listofpoly`
   */
  readonly listofpoly: DMP[];
  /**
   * Builds a recurrence operator from coefficients in ascending shift order.
   *
   * @param listOfPoly - Polynomial coefficients, in increasing operator degree.
   * @param parent - Parent algebra or module.
   */
  constructor(
    listOfPoly: readonly (DMP | ExprLike)[],
    /**
     * The algebra or domain containing this element.
     *
     * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.parent`
     */
    readonly parent: RecurrenceOperatorAlgebra,
  ) {
    this.listofpoly = listOfPoly.map((j) => (j instanceof DMP ? j : parent.base.fromSympy(j)));
  }
  /**
   * The highest power of `Sn`.
   *
   * @returns The highest generator degree.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.order`
   */
  get order(): number {
    return this.listofpoly.length - 1;
  }
  private poly(o: DMP | ExprLike): DMP {
    return o instanceof DMP ? o : this.parent.base.fromSympy(sympify(o));
  }
  /**
   * Multiplies operators by shifting each coefficient past the appropriate power of the shift
   * operator.
   *
   * @param other - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__mul__`
   */
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
  /**
   * Multiplies this value by the factor on its left.
   *
   * @param other - Factor on the left.
   * @returns The product in operand order.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__rmul__`
   */
  rmul(other: DMP | ExprLike): RecurrenceOperator {
    const o = this.poly(other);
    return new RecurrenceOperator(
      this.listofpoly.map((j) => o.mul(j)),
      this.parent,
    );
  }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__add__`
   */
  add(other: RecurrenceOperand): RecurrenceOperator {
    if (other instanceof RecurrenceOperator) return new RecurrenceOperator(addLists(this.listofpoly, other.listofpoly), this.parent);
    return new RecurrenceOperator([first(this.listofpoly).add(this.poly(other)), ...this.listofpoly.slice(1)], this.parent);
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__sub__`
   */
  sub(other: RecurrenceOperand): RecurrenceOperator {
    return this.add(other instanceof RecurrenceOperator ? other.rmul(-1) : this.poly(other).neg());
  }
  /**
   * Subtracts this operator from the left operand.
   *
   * @param other - Left operand of the subtraction.
   * @returns The difference in operand order.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__rsub__`
   */
  rsub(other: DMP | ExprLike): RecurrenceOperator {
    return this.rmul(-1).add(other);
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   */
  neg(): RecurrenceOperator {
    return this.rmul(-1);
  }
  /**
   * Raises the value to the specified power.
   *
   * @param nIn - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__pow__`
   */
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
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__str__`
   */
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
   * Compares recurrence operators by their algebra and coefficients. A scalar is equal to an operator
   * with the same constant coefficient and all higher coefficients zero.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.holonomic.recurrence.RecurrenceOperator.__eq__`
   */
  equals(other: RecurrenceOperand): boolean {
    if (other instanceof RecurrenceOperator) return listsEqual(this.listofpoly, other.listofpoly) && this.parent.equals(other.parent);
    return first(this.listofpoly).equals(other instanceof DMP ? other : sympify(other)) && this.listofpoly.slice(1).every((p) => p.isZero);
  }
}

/**
 * Represents a sequence satisfying a linear homogeneous recurrence with polynomial coefficients and
 * optional initial terms.
 *
 * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence`
 */
export class HolonomicSequence {
  /**
   * The initial values.
   *
   * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence.u0`
   */
  readonly u0: Expr[];
  /**
   * The variable of the recurrence.
   *
   * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence.n`
   */
  readonly n: Sym;
  /**
   * Specifies a sequence by a recurrence and optional initial terms.
   *
   * @param recurrence - Operator defining the recurrence.
   * @param u0 - Initial terms of the sequence.
   */
  constructor(
    /**
     * The linear recurrence operator annihilating the sequence.
     *
     * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence.recurrence`
     */
    readonly recurrence: RecurrenceOperator,
    u0: readonly ExprLike[] | ExprLike = [],
  ) {
    this.u0 = isList(u0) ? u0.map((u) => sympify(u)) : [sympify(u0)];
    this.n = recurrence.parent.base.gen;
  }
  /**
   * Checks whether initial sequence values were supplied.
   *
   * @returns Whether initial values are specified.
   * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence._have_init_cond`
   */
  get haveInitCond(): boolean {
    return this.u0.length > 0;
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence.__str__`
   */
  toString(): string {
    const s = `HolonomicSequence(${this.recurrence.toString()}, ${str(this.n)})`;
    return s + this.u0.map((u, i) => `, u(${i}) = ${str(u)}`).join('');
  }
  /**
   * Compares the two operands for equality.
   *
   * @param o - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.holonomic.recurrence.HolonomicSequence.__eq__`
   */
  equals(o: HolonomicSequence): boolean {
    if (!this.recurrence.equals(o.recurrence) || this.n.key !== o.n.key) return false;
    if (this.haveInitCond && o.haveInitCond) return this.u0.length === o.u0.length && this.u0.every((u, i) => u.key === at(o.u0, i).key);
    return true;
  }
}
