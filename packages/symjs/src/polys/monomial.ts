// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.polys.monomials: the Monomial class (an exponent vector
 * with optional generators), operations on exponent tuples and
 * itermonomials.
 */

import { at } from '../core/guard';
import { Rational, S, type Expr } from '../core/nodes';
import { mul, pow } from '../core/ops';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { asInt, type IntLike } from '../ntheory/intutil';
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

// ---------------------------------------------------------------------------
// operations on exponent tuples (SymPy sympy.polys.monomials)
// ---------------------------------------------------------------------------

/** An exponent tuple. */
export type ExponentVector = readonly number[];

/** The product of monomials, exponents added (SymPy monomial_mul). */
export function monomialMul(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => a + b);
}

/** The quotient A / B, or NoMatch when B does not divide A (SymPy monomial_div, None). */
export function monomialDiv(A: ExponentVector, B: ExponentVector): number[] | NoMatchResult {
  const C = monomialLdiv(A, B);
  return C.every((c) => c >= 0) ? C : NoMatch;
}

/** The quotient A / B with possibly negative exponents (SymPy monomial_ldiv). */
export function monomialLdiv(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => a - b);
}

/** The power A**n (SymPy monomial_pow). */
export function monomialPow(A: ExponentVector, n: number): number[] {
  return A.map((a) => a * n);
}

/** The greatest common divisor, minimum exponents (SymPy monomial_gcd). */
export function monomialGcd(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => Math.min(a, b));
}

/** The least common multiple, maximum exponents (SymPy monomial_lcm). */
export function monomialLcm(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => Math.max(a, b));
}

/** Whether A divides B (SymPy monomial_divides). */
export function monomialDivides(A: ExponentVector, B: ExponentVector): boolean {
  return zip(A, B).every(([a, b]) => a <= b);
}

/** The exponentwise maximum of monomials (SymPy monomial_max). */
export function monomialMax(...monoms: ExponentVector[]): number[] {
  const [first = [], ...rest] = monoms;
  return rest.reduce<number[]>((M, N) => monomialLcm(M, N), [...first]);
}

/** The exponentwise minimum of monomials (SymPy monomial_min). */
export function monomialMin(...monoms: ExponentVector[]): number[] {
  const [first = [], ...rest] = monoms;
  return rest.reduce<number[]>((M, N) => monomialGcd(M, N), [...first]);
}

/** The total degree (SymPy monomial_deg). */
export function monomialDeg(M: ExponentVector): number {
  return M.reduce((s, m) => s + m, 0);
}

/** The number of monomials of total degree at most N in V variables, binomial(V + N, N) (SymPy monomial_count). */
export function monomialCount(V: IntLike, N: IntLike): Rational {
  const [v, n] = [asInt(V, 'V'), asInt(N, 'N')];
  let c = 1n;
  for (let i = 1n; i <= n; i++) c = (c * (v + i)) / i;
  return Rational.of(c);
}

/** The cartesian product of lists (itertools.product). */
function product<T>(lists: readonly (readonly T[])[]): T[][] {
  return lists.reduce<T[][]>((acc, l) => acc.flatMap((xs) => l.map((y) => [...xs, y])), [[]]);
}

/**
 * The monomials in the variables (SymPy itermonomials): with a total degree
 * between minDegrees and maxDegrees, or, given lists of degrees, with the
 * degree of each variable between its bounds. SymPy yields them in no
 * particular order; they are returned in the order generated, without
 * duplicates.
 */
export function itermonomials(variables: readonly Expr[], maxDegrees: number | readonly number[], minDegrees?: number | readonly number[]): Expr[] {
  if (typeof maxDegrees !== 'number') {
    const n = variables.length;
    if (maxDegrees.length !== n) throw new RangeError('Argument sizes do not match');
    if (typeof minDegrees === 'number') throw new TypeError('min_degrees is not a list');
    const mins = minDegrees ?? Array.from({ length: n }, () => 0);
    if (mins.length !== n) throw new RangeError('Argument sizes do not match');
    if (mins.some((d) => d < 0)) throw new RangeError('min_degrees cannot contain negative numbers');
    if (mins.some((d, i) => d > at(maxDegrees, i))) throw new RangeError('min_degrees[i] must be <= max_degrees[i] for all i');
    const powers = variables.map((v, i) => Array.from({ length: at(maxDegrees, i) - at(mins, i) + 1 }, (_, k) => pow(v, at(mins, i) + k)));
    return product(powers).map((ps) => mul(...ps));
  }
  if (maxDegrees < 0) throw new RangeError('max_degrees cannot be negative');
  if (typeof minDegrees !== 'number' && minDegrees !== undefined) throw new TypeError('min_degrees must be an integer when max_degrees is');
  const minDegree = minDegrees ?? 0;
  if (minDegree < 0) throw new RangeError('min_degrees cannot be negative');
  if (minDegree > maxDegrees) return [];
  if (!variables.length || maxDegrees === 0) return [S.One];
  const vs = [...variables, S.One];
  const d = maxDegrees - minDegree;
  // combinations with replacement of the variables and 1 (products of the variables in any order when noncommutative)
  const items: Expr[][] = variables.every((v) => v.isCommutative) ? combinationsWithReplacement(vs, maxDegrees) : product(Array.from({ length: maxDegrees }, () => vs));
  const out = new Map<string, Expr>();
  for (const item of items) {
    if (item.filter((v) => v === S.One).length > d) continue;
    const m = mul(...item);
    out.set(str(m), m);
  }
  return [...out.values()];
}

/** itertools.combinations_with_replacement. */
function combinationsWithReplacement<T>(xs: readonly T[], k: number): T[][] {
  if (k === 0) return [[]];
  return xs.flatMap((x, i) => combinationsWithReplacement(xs.slice(i), k - 1).map((c) => [x, ...c]));
}
