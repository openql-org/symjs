// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/utilities.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { ExprLike } from '../../core/nodes';
import { Dummy, Rational } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { isReal } from '../../core/assumptions';
import { at, getOrThrow } from '../../core/guard';
import { NotImplementedError } from '../../core/errors';
import { factorint } from '../../ntheory/factor';
import { asInt, pmod, type IntLike } from '../../ntheory/intutil';
import { algebraicEnclosure } from './interval';
import { minimalPolynomial } from '../numberfields';
import type { Poly } from '../sympoly';
import { PythonMPQ } from '../domains/pythonrational';
import { DomainMatrix } from '../matrices/domainmatrix';
import { DMRankError } from '../matrices/exceptions';
import { rat } from '../matrices/domainops';

/** A rational number as the number-field modules take it: an integer, a Rational or a QQ element. */
export type RationalLike = number | bigint | Rational | PythonMPQ;

/**
 * Tests whether the input is an exact rational value accepted by the number-field operations.
 *
 * @param c - Value to classify.
 * @returns Whether the input represents an exact rational number.
 * @see SymPy `sympy.polys.numberfields.utilities.is_rat`
 */
export function isRat(c: unknown): c is RationalLike {
  return (typeof c === 'number' && Number.isInteger(c)) || typeof c === 'bigint' || c instanceof Rational || c instanceof PythonMPQ;
}

/**
 * Tests whether the input represents an integer exactly.
 *
 * @param c - Value to classify.
 * @returns Whether the value represents an integer.
 * @see SymPy `sympy.polys.numberfields.utilities.is_int`
 */
export function isInt(c: unknown): boolean {
  return (typeof c === 'number' && Number.isInteger(c)) || typeof c === 'bigint' || (c instanceof Rational && c.q === 1n);
}

/**
 * The numerator and the (positive) denominator of a rational number.
 *
 * @param c - Rational value to decompose.
 * @returns The reduced numerator and positive denominator.
 * @throws TypeError when the value is not rational.
 * @see SymPy `sympy.polys.numberfields.utilities.get_num_denom`
 */
export function getNumDenom(c: RationalLike): [bigint, bigint] {
  if (c instanceof Rational) return [c.p, c.q];
  if (c instanceof PythonMPQ) return [c.numerator, c.denominator];
  if (typeof c === 'number' && !Number.isInteger(c)) throw new TypeError(`${c} is not a rational number`);
  return [BigInt(c), 1n];
}

/**
 * Separates a discriminant into a fundamental discriminant and a square factor.
 *
 * @remarks SymPy prints the pair as `({3: 1, -1: 1}, {2: 2, 3: 1})`.
 * @param aIn - Integer discriminant to decompose.
 * @returns Prime factorizations of the fundamental part and square factor.
 * @throws RangeError when the integer is neither zero nor one modulo four.
 * @see SymPy `sympy.polys.numberfields.utilities.extract_fundamental_discriminant`
 * @example
 * ```ts
 * import { extractFundamentalDiscriminant } from '@symjs/symjs';
 *
 * extractFundamentalDiscriminant(-432); // => [{3: 1, -1: 1}, {2: 2, 3: 1}]
 * ```
 */
export function extractFundamentalDiscriminant(aIn: IntLike): [Map<bigint, number>, Map<bigint, number>] {
  const a = asInt(aIn), residue = pmod(a, 4n);
  if (residue !== 0n && residue !== 1n) throw new RangeError('discriminant must be 0 or 1 mod 4');
  const D = new Map<bigint, number>(), F = new Map<bigint, number>();
  if (a === 0n) return [D, new Map([[0n, 1]])];
  let threes = 0;
  for (const [p, e] of factorint(a)) {
    if (e % 2n) {
      D.set(p, 1);
      if (pmod(p, 4n) === 3n) threes++;
      if (e >= 3n) F.set(p, Number((e - 1n) / 2n));
    } else F.set(p, Number(e / 2n));
  }
  const even = D.has(2n);
  if (even || threes % 2) {
    const e = getOrThrow(F, 2n);
    if (e === 1) F.delete(2n);
    else F.set(2n, e - 1);
    D.set(2n, even ? 3 : 2);
  }
  return [D, F];
}

/**
 * Bounds a real algebraic number between two rational endpoints.
 *
 * @remarks SymPy returns the intervals as tuples, `(1, 2)` and `(24/17, 17/12)`.
 * @param algIn - Real algebraic value.
 * @param eps - Maximum interval width.
 * @returns The rational interval enclosing the real algebraic number.
 * @throws NotImplementedError when the algebraic number is nonreal.
 * @see SymPy `sympy.polys.numberfields.utilities.isolate`
 * @example
 * ```ts
 * import { Rational, ex, isolate } from '@symjs/symjs';
 *
 * isolate(ex`sqrt(2)`); // => [1, 2]
 * isolate(ex`sqrt(2)`, Rational.of(1n, 100n)); // => [24/17, 17/12]
 * ```
 */
export function isolate(algIn: ExprLike, eps?: Rational): [Rational, Rational] {
  const alg = sympify(algIn);
  if (alg instanceof Rational) return [alg, alg];
  if (isReal(alg) !== true) throw new NotImplementedError('complex algebraic numbers are not supported');
  const p = minimalPolynomial(alg, new Dummy('x'), { polys: true });
  const intervals = p.intervals().map(([ab]) => ab);
  let bounds = intervals.length === 1 ? at(intervals, 0) : undefined;
  const le = (a: Rational, b: Rational): boolean => a.p * b.q <= b.p * a.q;
  for (let bits = 32; bounds === undefined; bits *= 2) {
    try {
      const [real] = algebraicEnclosure(alg,bits);
      bounds = intervals.find(([a,b]) => le(a,real[0]) && le(real[1],b));
    } catch (error) {
      if (!(error instanceof RangeError)) throw error;
    }
  }
  return eps === undefined ? bounds : p.refineRoot(bounds[0], bounds[1], eps);
}

/**
 * The powers of the root theta of a monic polynomial T, each written in the power basis 1,
 * theta,..., theta**(n-1) as a list of n integers, lowest power first, optionally reduced modulo an
 * integer. Powers from theta**n on are computed by the recurrence of T and cached.
 *
 * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers`
 * @example
 * ```ts
 * import { AlgIntPowers, Poly, ex } from '@symjs/symjs';
 *
 * const powers = new AlgIntPowers(Poly.from(ex`x**4 + x**3 + x**2 + x + 1`));
 * powers.get(1); // => [0, 1, 0, 0]
 * powers.get(4); // => [-1, -1, -1, -1]
 * ```
 */
export class AlgIntPowers {
  /**
   * The defining polynomial of the algebraic generator.
   *
   * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers.T`
   */
  readonly T: Poly;
  /**
   * The optional modulus for reducing the power-basis coefficients.
   *
   * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers.modulus`
   */
  readonly modulus: bigint | undefined;
  /**
   * The number of basis coordinates.
   *
   * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers.n`
   */
  readonly n: number;
  private readonly powersNAndUp: bigint[][];
  private maxSoFar: number;
  /**
   * Prepares to evaluate powers of an algebraic integer in the power basis, optionally modulo an
   * integer.
   *
   * @param T - Polynomial defining the algebraic roots.
   * @param modulus - Modulus used for the arithmetic.
   */
  constructor(T: Poly, modulus?: IntLike) {
    this.T = T;
    this.modulus = modulus === undefined ? undefined : asInt(modulus, 'modulus');
    this.n = T.degree();
    // theta**n = -(c[0] + c[1]*theta + ... + c[n-1]*theta**(n-1)) for T = theta**n + c[n-1]*theta**(n-1) + ... + c[0]
    const coeffs = T.allCoeffs().map((c) => rat(c).p).reverse();
    this.powersNAndUp = [coeffs.slice(0, -1).map((c) => this.red(-c))];
    this.maxSoFar = this.n;
  }
  /**
   * The integer reduced modulo the modulus, if any.
   *
   * @param exp - Integer coefficient to reduce.
   * @returns The coefficient reduced modulo the optional modulus.
   * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers.red`
   */
  red(exp: bigint): bigint {
    return this.modulus === undefined ? exp : pmod(exp, this.modulus);
  }
  /**
   * Compute the powers up to theta**e.
   *
   * @param e - Exponent of the power.
   * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers.compute_up_through`
   */
  computeUpThrough(e: number): void {
    const m = this.maxSoFar;
    if (e <= m) return;
    const n = this.n;
    const r = this.powersNAndUp;
    const c = at(r, 0);
    for (let k = m + 1; k <= e; k++) {
      const prev = at(r, k - 1 - n);
      const b = at(prev, n - 1);
      r.push([this.red(at(c, 0) * b), ...Array.from({ length: n - 1 }, (_, j) => this.red(at(prev, j) + at(c, j + 1) * b))]);
    }
    this.maxSoFar = e;
  }
  /**
   * Theta**e as its n coefficients, lowest power first.
   *
   * @param e - Nonnegative exponent of the algebraic generator.
   * @returns The power-basis coefficients of the requested power.
   * @throws RangeError when the exponent is negative.
   * @see SymPy `sympy.polys.numberfields.utilities.AlgIntPowers.get`
   */
  get(e: number): bigint[] {
    const n = this.n;
    if (e < 0) throw new RangeError('Exponent must be non-negative.');
    if (e < n) return Array.from({ length: n }, (_, i) => (i === e ? 1n : 0n));
    this.computeUpThrough(e);
    return [...at(this.powersNAndUp, e - n)];
  }
}

/**
 * The coefficient vectors of length m with entries in [-R, R], then [-R-1, R+1], and so on: each
 * vector of the next "shell" contains an entry of absolute value R, and the zero vector is skipped.
 * An infinite generator.
 *
 * @param m - Number of coordinates.
 * @param RIn - Initial coefficient bound.
 * @returns An iterator of coefficient vectors in successive shells.
 * @see SymPy `sympy.polys.numberfields.utilities.coeff_search`
 * @example
 * ```ts
 * import { coeffSearch } from '@symjs/symjs';
 *
 * const vectors = coeffSearch(2, 1);
 * vectors.next().value; // => [1, 1]
 * vectors.next().value; // => [1, 0]
 * ```
 */
export function* coeffSearch(m: number, RIn: number): Generator<number[], never, unknown> {
  let R = RIn;
  const R0 = R;
  let c = Array.from({ length: m }, () => R);
  for (;;) {
    if (R === R0 || c.includes(R) || c.includes(-R)) yield [...c];
    let j = m - 1;
    while (at(c, j) === -R) j--;
    c[j] = at(c, j) - 1;
    for (let i = j + 1; i < m; i++) c[i] = R;
    if (c.every((ci) => ci === 0)) {
      R += 1;
      c = Array.from({ length: m }, () => R);
    }
  }
}

/**
 * Extends linearly independent columns over a field to a basis of the whole space.
 *
 * @param M - Matrix of independent basis columns.
 * @returns An invertible matrix extending the given columns.
 * @throws DMRankError when the supplied columns are linearly dependent.
 * @see SymPy `sympy.polys.numberfields.utilities.supplement_a_subspace`
 * @example
 * ```ts
 * import { DM, QQ, supplementASubspace } from '@symjs/symjs';
 *
 * const A = DM([[1, 7, 0], [2, 3, 4]], QQ).transpose();
 * supplementASubspace(A).transpose().toList(); // => [[1, 7, 0], [2, 3, 4], [1, 0, 0]]
 * ```
 */
export function supplementASubspace(M: DomainMatrix): DomainMatrix {
  const [n, r] = M.shape;
  const Maug = M.hstack(DomainMatrix.eye(n, M.domain));
  const [R, pivots] = Maug.rref();
  if (pivots.length < r || pivots.slice(0, r).some((p, i) => p !== i)) throw new DMRankError('M was not of maximal rank');
  const A = R.extractSlice([0, n], [r, r + n]);
  return A.inv();
}
