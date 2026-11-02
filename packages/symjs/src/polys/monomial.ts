// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.polys.monomials.Monomial: an exponent vector with
 * optional generators.
 */

import { Expr } from '../core/nodes';
import { mul, pow } from '../core/ops';
import { str } from '../printing/str';

/** A monomial as exponents over generators (SymPy Monomial). */
export class Monomial {
  constructor(
    readonly exponents: readonly number[],
    readonly gens: readonly Expr[] = [],
  ) {}

  /** The monomial as an expression (SymPy as_expr). */
  asExpr(...gens: Expr[]): Expr {
    const g = gens.length ? gens : this.gens;
    if (!g.length) throw new Error(`Cannot convert ${this.toString()} to an expression without generators`);
    return mul(...g.map((x, i) => pow(x, this.exponents[i] ?? 0)));
  }
  /** Product of monomials (exponents added). */
  mul(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(this.exponents.map((k, i) => k + (e[i] ?? 0)), this.gens);
  }
  /** Greatest common divisor (minimum exponents). */
  gcd(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(this.exponents.map((k, i) => Math.min(k, e[i] ?? 0)), this.gens);
  }
  /** Least common multiple (maximum exponents). */
  lcm(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(this.exponents.map((k, i) => Math.max(k, e[i] ?? 0)), this.gens);
  }
  /** SymPy str: x**2*y**0, or Monomial((2, 0)) without generators. */
  toString(): string {
    if (this.gens.length) return this.gens.map((g, i) => `${str(g)}**${this.exponents[i]}`).join('*');
    return `Monomial((${this.exponents.join(', ')}${this.exponents.length === 1 ? ',' : ''}))`;
  }
}
