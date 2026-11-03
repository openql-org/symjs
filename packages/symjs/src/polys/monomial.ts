// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.polys.monomials.Monomial: an exponent vector with
 * optional generators.
 */

import { at } from '../core/guard';
import type { Expr } from '../core/nodes';
import { mul, pow } from '../core/ops';
import { str } from '../printing/str';

/** Pairs of a and b up to the shorter length (Python zip, as SymPy's monomial operations use). */
function zip<A, B>(a: readonly A[], b: readonly B[]): [A, B][] {
  return a.slice(0, b.length).map((v, i) => [v, at(b, i)]);
}

/** A monomial as exponents over generators (SymPy Monomial). */
export class Monomial {
  constructor(
    readonly exponents: readonly number[],
    readonly gens: readonly Expr[] = [],
  ) {}

  /** The monomial as an expression (SymPy as_expr). */
  asExpr(...gens: Expr[]): Expr {
    const g = gens.length ? gens : this.gens;
    if (!g.length) throw new TypeError(`Cannot convert ${this.toString()} to an expression without generators`);
    return mul(...zip(g, this.exponents).map(([x, k]) => pow(x, k)));
  }
  /** Product of monomials (exponents added). */
  mul(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(zip(this.exponents, e).map(([k, l]) => k + l), this.gens);
  }
  /** Greatest common divisor (minimum exponents). */
  gcd(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(zip(this.exponents, e).map(([k, l]) => Math.min(k, l)), this.gens);
  }
  /** Least common multiple (maximum exponents). */
  lcm(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(zip(this.exponents, e).map(([k, l]) => Math.max(k, l)), this.gens);
  }
  /** SymPy str: x**2*y**0, or Monomial((2, 0)) without generators. */
  toString(): string {
    if (this.gens.length) return zip(this.gens, this.exponents).map(([g, k]) => `${str(g)}**${k}`).join('*');
    return `Monomial((${this.exponents.join(', ')}${this.exponents.length === 1 ? ',' : ''}))`;
  }
}
