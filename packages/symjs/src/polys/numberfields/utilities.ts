// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/numberfields/utilities.py, Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { ExprLike } from '../../core/nodes';
import { Dummy, Float, Rational } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { isReal } from '../../core/assumptions';
import { at, expectType, getOrThrow } from '../../core/guard';
import { NotImplementedError } from '../../core/errors';
import { factorint } from '../../ntheory/factor';
import { asInt, pmod, type IntLike } from '../../ntheory/intutil';
import { mag, toRational } from '../../numeric/mpf';
import { minimalPolynomial } from '../numberfields';
import type { Poly } from '../sympoly';
import { PythonMPQ } from '../domains/pythonrational';
import { DomainMatrix } from '../matrices/domainmatrix';
import { DMRankError } from '../matrices/exceptions';
import { rat } from '../matrices/domainops';

/** A rational number as the number-field modules take it: an integer, a Rational or a QQ element (SymPy is_rat). */
export type RationalLike = number | bigint | Rational | PythonMPQ;

/** An integer or a rational number (SymPy is_rat): a JavaScript integer, a bigint, a Rational or a QQ element. */
export function isRat(c: unknown): c is RationalLike {
  return (typeof c === 'number' && Number.isInteger(c)) || typeof c === 'bigint' || c instanceof Rational || c instanceof PythonMPQ;
}

/** An integer (SymPy is_int): a JavaScript integer, a bigint or an integer Rational. */
export function isInt(c: unknown): boolean {
  return (typeof c === 'number' && Number.isInteger(c)) || typeof c === 'bigint' || (c instanceof Rational && c.q === 1n);
}

/** The numerator and the (positive) denominator of a rational number (SymPy get_num_denom). */
export function getNumDenom(c: RationalLike): [bigint, bigint] {
  if (c instanceof Rational) return [c.p, c.q];
  if (c instanceof PythonMPQ) return [c.numerator, c.denominator];
  if (typeof c === 'number' && !Number.isInteger(c)) throw new TypeError(`${c} is not a rational number`);
  return [BigInt(c), 1n];
}

/** Factorizations of d and f with a=d*f**2 and d a fundamental discriminant or 1. */
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

/** Rational isolating interval of a real algebraic number, optionally narrowed to eps. */
export function isolate(algIn: ExprLike, eps?: Rational): [Rational, Rational] {
  const alg = sympify(algIn);
  if (alg instanceof Rational) return [alg, alg];
  if (isReal(alg) !== true) throw new NotImplementedError('complex algebraic numbers are not supported');
  const p = minimalPolynomial(alg, new Dummy('x'), { polys: true });
  const intervals = p.intervals().map(([ab]) => ab);
  let bounds = intervals.length === 1 ? at(intervals, 0) : undefined;
  // Root isolation proves each interval contains exactly one root. Refine
  // the value used to choose that interval until rounding cannot put it on
  // the wrong side of an endpoint; compare rationals without double conversion.
  const le = (a: Rational, b: Rational): boolean => a.p * b.q <= b.p * a.q;
  for (let digits = 15; bounds === undefined; digits *= 2) {
    const v = expectType(alg.evalf(digits), (e): e is Float => e instanceof Float, 'numeric algebraic value');
    const [n, d] = toRational(v.mpf), exponent = mag(v.mpf) - v.prec + 4;
    const error = exponent < 0 ? Rational.of(1n, 2n ** BigInt(-exponent)) : Rational.of(2n ** BigInt(exponent));
    const lo = Rational.of(n * error.q - error.p * d, d * error.q);
    const hi = Rational.of(n * error.q + error.p * d, d * error.q);
    bounds = intervals.find(([a, b]) => le(a, lo) && le(hi, b));
  }
  return eps === undefined ? bounds : p.refineRoot(bounds[0], bounds[1], eps);
}

/**
 * The powers of the root theta of a monic polynomial T, each written in the
 * power basis 1, theta, ..., theta**(n-1) as a list of n integers, lowest
 * power first, optionally reduced modulo an integer (SymPy AlgIntPowers).
 * Powers from theta**n on are computed by the recurrence of T and cached.
 */
export class AlgIntPowers {
  readonly T: Poly;
  readonly modulus: bigint | undefined;
  readonly n: number;
  private readonly powersNAndUp: bigint[][];
  private maxSoFar: number;
  constructor(T: Poly, modulus?: IntLike) {
    this.T = T;
    this.modulus = modulus === undefined ? undefined : asInt(modulus, 'modulus');
    this.n = T.degree();
    // theta**n = -(c[0] + c[1]*theta + ... + c[n-1]*theta**(n-1)) for T = theta**n + c[n-1]*theta**(n-1) + ... + c[0]
    const coeffs = T.allCoeffs().map((c) => rat(c).p).reverse();
    this.powersNAndUp = [coeffs.slice(0, -1).map((c) => this.red(-c))];
    this.maxSoFar = this.n;
  }
  /** The integer reduced modulo the modulus, if any. */
  red(exp: bigint): bigint {
    return this.modulus === undefined ? exp : pmod(exp, this.modulus);
  }
  /** Compute the powers up to theta**e. */
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
  /** theta**e as its n coefficients, lowest power first (SymPy get and __getitem__). */
  get(e: number): bigint[] {
    const n = this.n;
    if (e < 0) throw new RangeError('Exponent must be non-negative.');
    if (e < n) return Array.from({ length: n }, (_, i) => (i === e ? 1n : 0n));
    this.computeUpThrough(e);
    return [...at(this.powersNAndUp, e - n)];
  }
}

/**
 * The coefficient vectors of length m with entries in [-R, R], then [-R-1,
 * R+1], and so on: each vector of the next "shell" contains an entry of
 * absolute value R, and the zero vector is skipped (SymPy coeff_search).
 * An infinite generator.
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
 * For an n x r matrix M of rank r over a field, an invertible n x n matrix B
 * whose first r columns are those of M (SymPy supplement_a_subspace).
 * Throws DMRankError when M is not of maximal rank.
 */
export function supplementASubspace(M: DomainMatrix): DomainMatrix {
  const [n, r] = M.shape;
  const Maug = M.hstack(DomainMatrix.eye(n, M.domain));
  const [R, pivots] = Maug.rref();
  if (pivots.length < r || pivots.slice(0, r).some((p, i) => p !== i)) throw new DMRankError('M was not of maximal rank');
  const A = R.extractSlice([0, n], [r, r + n]);
  return A.inv();
}
