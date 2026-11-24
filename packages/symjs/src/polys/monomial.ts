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

/**
 * A monomial as exponents over generators.
 *
 * @see SymPy `sympy.polys.monomials.Monomial`
 */
export class Monomial {
  /**
   * Construct a `Monomial` instance.
   *
   * @param exponents - Powers of the generators in order.
   * @param gens - Polynomial generators in the desired order.
   */
  constructor(
    /** The exponent of each generator in order. @see SymPy `sympy.polys.monomials.Monomial.exponents` */
    readonly exponents: readonly number[],
    /** The ordered generators. @see SymPy `sympy.polys.monomials.Monomial.gens` */
    readonly gens: readonly Expr[] = [],
  ) {}

  /**
   * Expresses the monomial as a product of generator powers.
   *
   * @param gens - Polynomial generators in the desired order.
   * @returns The symbolic expression.
   * @throws TypeError when no generators are supplied.
   * @see SymPy `sympy.polys.monomials.Monomial.as_expr`
   */
  asExpr(...gens: Expr[]): Expr {
    const g = gens.length ? gens : this.gens;
    if (!g.length) throw new TypeError(`Cannot convert ${this.toString()} to an expression without generators`);
    return mul(...zip(g, this.exponents).map(([x, k]) => pow(x, k)));
  }
  /**
   * Multiplies monomials by adding their exponent vectors.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The product of the operands.
   * @see SymPy `sympy.polys.monomials.Monomial.__mul__`
   */
  mul(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(zip(this.exponents, e).map(([k, l]) => k + l), this.gens);
  }
  /**
   * Computes the monomial GCD by taking componentwise minimum exponents.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The greatest common divisor.
   * @see SymPy `sympy.polys.monomials.Monomial.gcd`
   */
  gcd(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(zip(this.exponents, e).map(([k, l]) => Math.min(k, l)), this.gens);
  }
  /**
   * Computes the monomial LCM by taking componentwise maximum exponents.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The least common multiple.
   * @see SymPy `sympy.polys.monomials.Monomial.lcm`
   */
  lcm(o: Monomial | readonly number[]): Monomial {
    const e = o instanceof Monomial ? o.exponents : o;
    return new Monomial(zip(this.exponents, e).map(([k, l]) => Math.max(k, l)), this.gens);
  }
  /**
   * Prints the monomial with explicit powers when generators are given or as an exponent tuple otherwise.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.polys.monomials.Monomial.__str__`
   */
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

/**
 * Multiplies monomials by adding corresponding exponents.
 *
 * @param A - First exponent vector.
 * @param B - Second exponent vector.
 * @returns The product exponent vector.
 * @see SymPy `sympy.polys.monomials.monomial_mul`
 * @remarks SymPy returns `(4, 6, 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { monomialMul } from '@symjs/symjs';
 *
 * monomialMul([3, 4, 1], [1, 2, 0]); // => [4, 6, 1]
 * ```
 */
export function monomialMul(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => a + b);
}

/**
 * Subtracts corresponding exponents if the divisor monomial divides the dividend.
 *
 * @param A - First exponent vector.
 * @param B - Second exponent vector.
 * @returns The quotient exponent vector or `NoMatch`.
 * @see SymPy `sympy.polys.monomials.monomial_div`
 * @remarks SymPy returns `(2, 2, 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { monomialDiv } from '@symjs/symjs';
 *
 * monomialDiv([3, 4, 1], [1, 2, 0]); // => [2, 2, 1]
 * ```
 */
export function monomialDiv(A: ExponentVector, B: ExponentVector): number[] | NoMatchResult {
  const C = monomialLdiv(A, B);
  return C.every((c) => c >= 0) ? C : NoMatch;
}

/**
 * Subtracts exponent vectors to divide monomials, allowing negative powers.
 *
 * @param A - First exponent vector.
 * @param B - Second exponent vector.
 * @returns The signed quotient exponents.
 * @see SymPy `sympy.polys.monomials.monomial_ldiv`
 * @remarks SymPy returns `(2, 2, 1)` with tuples for the fixed-length groups. The second result is `(2, 2, -1)` in SymPy.
 * @example
 * ```ts
 * import { monomialLdiv } from '@symjs/symjs';
 *
 * monomialLdiv([3, 4, 1], [1, 2, 0]); // => [2, 2, 1]
 * monomialLdiv([3, 4, 1], [1, 2, 2]); // => [2, 2, -1]
 * ```
 */
export function monomialLdiv(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => a - b);
}

/**
 * Raises the monomial to the given power by scaling its exponents.
 *
 * @param A - First exponent vector.
 * @param n - Nonnegative power of the monomial.
 * @returns The resulting exponent vector.
 * @see SymPy `sympy.polys.monomials.monomial_pow`
 */
export function monomialPow(A: ExponentVector, n: number): number[] {
  return A.map((a) => a * n);
}

/**
 * Takes the componentwise minimum of the exponents.
 *
 * @param A - First exponent vector.
 * @param B - Second exponent vector.
 * @returns The monomial GCD.
 * @see SymPy `sympy.polys.monomials.monomial_gcd`
 * @remarks SymPy returns `(1, 2, 0)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { monomialGcd } from '@symjs/symjs';
 *
 * monomialGcd([1, 4, 1], [3, 2, 0]); // => [1, 2, 0]
 * ```
 */
export function monomialGcd(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => Math.min(a, b));
}

/**
 * Takes the componentwise maximum of the exponents.
 *
 * @param A - First exponent vector.
 * @param B - Second exponent vector.
 * @returns The monomial LCM.
 * @see SymPy `sympy.polys.monomials.monomial_lcm`
 * @remarks SymPy returns `(3, 4, 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { monomialLcm } from '@symjs/symjs';
 *
 * monomialLcm([1, 4, 1], [3, 2, 0]); // => [3, 4, 1]
 * ```
 */
export function monomialLcm(A: ExponentVector, B: ExponentVector): number[] {
  return zip(A, B).map(([a, b]) => Math.max(a, b));
}

/**
 * Tests whether each exponent of the divisor is at most the corresponding dividend exponent.
 *
 * @param A - First exponent vector.
 * @param B - Second exponent vector.
 * @returns True if the first monomial divides the second.
 * @see SymPy `sympy.polys.monomials.monomial_divides`
 * @example
 * ```ts
 * import { monomialDivides } from '@symjs/symjs';
 *
 * monomialDivides([1, 2], [3, 4]); // => True
 * monomialDivides([1, 2], [0, 2]); // => False
 * ```
 */
export function monomialDivides(A: ExponentVector, B: ExponentVector): boolean {
  return zip(A, B).every(([a, b]) => a <= b);
}

/**
 * Finds the largest exponent of each variable among the monomials.
 *
 * @param monoms - Exponent vectors of the monomials.
 * @returns The maximum exponent vector.
 * @see SymPy `sympy.polys.monomials.monomial_max`
 * @remarks SymPy returns `(6, 5, 9)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { monomialMax } from '@symjs/symjs';
 *
 * monomialMax([3, 4, 5], [0, 5, 1], [6, 3, 9]); // => [6, 5, 9]
 * ```
 */
export function monomialMax(...monoms: ExponentVector[]): number[] {
  const [first = [], ...rest] = monoms;
  return rest.reduce<number[]>((M, N) => monomialLcm(M, N), [...first]);
}

/**
 * Finds the smallest exponent of each variable among the monomials.
 *
 * @param monoms - Exponent vectors of the monomials.
 * @returns The minimum exponent vector.
 * @see SymPy `sympy.polys.monomials.monomial_min`
 * @remarks SymPy returns `(0, 3, 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { monomialMin } from '@symjs/symjs';
 *
 * monomialMin([3, 4, 5], [0, 5, 1], [6, 3, 9]); // => [0, 3, 1]
 * ```
 */
export function monomialMin(...monoms: ExponentVector[]): number[] {
  const [first = [], ...rest] = monoms;
  return rest.reduce<number[]>((M, N) => monomialGcd(M, N), [...first]);
}

/**
 * Adds the exponents of the monomial.
 *
 * @param M - Exponent vector.
 * @returns The total degree.
 * @see SymPy `sympy.polys.monomials.monomial_deg`
 * @example
 * ```ts
 * import { monomialDeg } from '@symjs/symjs';
 *
 * monomialDeg([1, 2]); // => 3
 * ```
 */
export function monomialDeg(M: ExponentVector): number {
  return M.reduce((s, m) => s + m, 0);
}

/**
 * Counts monomials in `V` variables of degree at most `N`.
 *
 * @param V - Number of variables.
 * @param N - Maximum total degree to count.
 * @returns The binomial coefficient `binomial(V + N, N)`.
 * @see SymPy `sympy.polys.monomials.monomial_count`
 * @example
 * ```ts
 * import { monomialCount } from '@symjs/symjs';
 *
 * monomialCount(2, 2); // => 6
 * ```
 */
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
 * The monomials in the variables: with a total degree
 * between minDegrees and maxDegrees, or, given lists of degrees, with the
 * degree of each variable between its bounds. SymPy yields them in no
 * particular order; they are returned in the order generated, without
 * duplicates.
 *
 * @param variables - Generators from which to build the monomials.
 * @param maxDegrees - Upper total degree or componentwise upper degree bounds.
 * @param minDegrees - Lower total degree or componentwise lower degree bounds.
 * @returns The monomials satisfying the degree bounds.
 * @throws RangeError when the exponent vectors have different lengths or a degree bound is negative or a minimum degree exceeds the corresponding maximum.
 * @throws TypeError when the lower and upper degree bounds have incompatible shapes.
 * @see SymPy `sympy.polys.monomials.itermonomials`
 * @example
 * ```ts
 * import { ex, itermonomials } from '@symjs/symjs';
 *
 * itermonomials([ex`x`, ex`y`], 2).length; // => 6
 * ```
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
