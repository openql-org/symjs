// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/densetools.py, BSD-3-Clause; see LICENSE.

/** Advanced tools for dense recursive polynomials in K[x] or K[X], with leading coefficients first. */
import { isNegative as isNegativeExpr } from '../core/assumptions';
import { DomainError } from '../core/errors';
import { at, first } from '../core/guard';
import { asNumerDenom } from '../core/methods';
import { Dummy } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import {
  dmpAdd, dmpAddTerm, dmpExquoGround, dmpMul, dmpMulGround, dmpQuoGround, dmpRem, dmpSub, dupAdd, dupAddTerm,
  dupDiv, dupExquoGround, dupLshift, dupMul, dupMulGround, dupQuoGround, dupRem, dupSqr, dupSub,
} from './densearith';
import {
  dmpConvert, dmpDegree, dmpFromDict, dmpGround, dmpGroundLC, dmpInclude, dmpStrip, dmpToDict, dmpZero, dmpZeroP,
  dmpZeros, dupConvert, dupDegree, dupFromRawDict, dupStrip, groundEquals, groundIsZero, polyLC, polyTC,
} from './densebasic';
import type { DensePoly } from './densebasic';
import { domainArith, domainNeg, ExpressionDomain, FractionField, groundRational, IntegerRing, PolynomialRing, QQ, RationalField, RealField } from './domains';
import type { Domain } from './domains';
import { AlgebraicField } from './domains/algebraicfield';
import { FiniteField } from './domains/finitefield';
import { GaussianDomain, GaussianRationalField } from './domains/gaussiandomains';
import { MultivariatePolynomialError, NotReversible } from './polyerrors';
import { lcmList, Poly, resultant } from './sympoly';

function list(f: unknown): DensePoly {
  if (!Array.isArray(f)) throw new TypeError('a dense polynomial level must be a list');
  return f;
}

function integer(n: unknown): number {
  const r = groundRational(n);
  if (r === undefined || r[1] !== 1n || !Number.isSafeInteger(Number(r[0]))) throw new RangeError('expected a safe integer');
  return Number(r[0]);
}

const mulInt = (K: Domain, c: unknown, n: number): unknown => domainArith(K, 'mul', BigInt(n), c);

/** The quotient a // b of ground elements of K (SymPy K.quo). */
function groundQuo(a: unknown, b: unknown, K: Domain): unknown {
  return first(dupQuoGround([a], b, K));
}

/** The exact quotient a / b of ground elements of K (SymPy K.exquo). */
function groundExquo(a: unknown, b: unknown, K: Domain): unknown {
  return first(dupExquoGround([a], b, K));
}

/** The falling factorial n*(n-1)*...*(n-m+1). */
function falling(n: number, m: number): number {
  let k = n;
  for (let i = n - 1; i > n - m; i--) k *= i;
  return k;
}

/** The rising product (i+1)*(i+2)*...*(i+m). */
function rising(i: number, m: number): number {
  let n = i + 1;
  for (let j = 1; j < m; j++) n *= i + j + 1;
  return n;
}

/**
 * Integrates `m` times in the principal generator.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of integrations.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The antiderivative in `x_0`.
 * @see SymPy `sympy.polys.densetools.dup_integrate`
 * @example
 * ```ts
 * import { QQ, dupIntegrate } from '@symjs/symjs';
 *
 * dupIntegrate([1, 2, 0], 1, QQ).map(c => QQ.toSympy(c)); // => [1/3, 1, 0, 0]
 * ```
 */
export function dupIntegrate(f: DensePoly, m: number, K: Domain): unknown[] {
  const n = integer(m);
  if (n <= 0 || !f.length) return [...f];
  const g: unknown[] = Array.from({ length: n }, () => K.zero);
  [...f].reverse().forEach((c, i) => g.unshift(groundExquo(c, BigInt(rising(i, n)), K)));
  return g;
}

/**
 * Integrates `m` times in the principal generator.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of integrations.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The antiderivative in `x_0`.
 * @see SymPy `sympy.polys.densetools.dmp_integrate`
 * @example
 * ```ts
 * import { QQ, dmpIntegrate } from '@symjs/symjs';
 *
 * (dmpIntegrate([[1], [2, 0]], 1, 1, QQ)[0] as unknown[]).map(c => QQ.toSympy(c)); // => [1/2]
 * ```
 */
export function dmpIntegrate(f: DensePoly, m: number, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupIntegrate(f, m, K);
  const n = integer(m);
  if (n <= 0 || dmpZeroP(f, v)) return [...f];
  const g = dmpZeros(n, v - 1, K);
  [...f].reverse().forEach((c, i) => g.unshift(dmpQuoGround(list(c), BigInt(rising(i, n)), v - 1, K)));
  return g;
}

function checkIndex(j: number, u: number): void {
  if (j < 0 || j > u) throw new RangeError(`0 <= j <= ${u} expected, got ${j}`);
}

/** Apply op to the coefficients in x_j through the outer levels; `drop` is 1 when op removes x_j (SymPy _rec_*_in). */
function recIn(g: DensePoly, v: number, i: number, j: number, op: (h: DensePoly, w: number) => unknown, drop = 0): unknown {
  if (i === j) return op(g, v);
  return dmpStrip(g.map((c) => recIn(list(c), v - 1, i + 1, j, op, drop)), v - drop);
}

/**
 * Integrates `m` times with respect to the selected generator.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of integrations.
 * @param j - Index of the polynomial variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The antiderivative in `x_j`.
 * @see SymPy `sympy.polys.densetools.dmp_integrate_in`
 * @example
 * ```ts
 * import { QQ, dmpIntegrateIn } from '@symjs/symjs';
 *
 * (dmpIntegrateIn([[1], [2, 0]], 1, 0, 1, QQ)[0] as unknown[]).map(c => QQ.toSympy(c)); // => [1/2]
 * ```
 */
export function dmpIntegrateIn(f: DensePoly, m: number, j: number, u: number, K: Domain): unknown[] {
  const [jj, uu] = [integer(j), integer(u)];
  checkIndex(jj, uu);
  return [...list(recIn(f, uu, 0, jj, (h, w) => dmpIntegrate(h, m, w, K)))];
}

/**
 * Differentiates the polynomial `m` times in its principal variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of differentiations.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The derivative polynomial.
 * @see SymPy `sympy.polys.densetools.dup_diff`
 * @example
 * ```ts
 * import { ZZ, dupDiff } from '@symjs/symjs';
 *
 * dupDiff([1, 2, 3, 4], 1, ZZ); // => [3, 4, 3]
 * dupDiff([1, 2, 3, 4], 2, ZZ); // => [6, 4]
 * ```
 */
export function dupDiff(f: DensePoly, m: number, K: Domain): unknown[] {
  const k = integer(m);
  if (k <= 0) return [...f];
  let n = dupDegree(f);
  if (n < k) return [];
  const deriv: unknown[] = [];
  for (const coeff of f.slice(0, -k)) {
    deriv.push(mulInt(K, coeff, falling(n, k)));
    n--;
  }
  return dupStrip(deriv);
}

/**
 * Differentiates the polynomial `m` times in its principal variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of differentiations.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The derivative polynomial.
 * @see SymPy `sympy.polys.densetools.dmp_diff`
 * @example
 * ```ts
 * import { ZZ, dmpDiff } from '@symjs/symjs';
 *
 * dmpDiff([[1, 2, 3], [2, 3, 1]], 1, 1, ZZ); // => [[1, 2, 3]]
 * dmpDiff([[1, 2, 3], [2, 3, 1]], 2, 1, ZZ); // => [[]]
 * ```
 */
export function dmpDiff(f: DensePoly, m: number, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupDiff(f, m, K);
  const k = integer(m);
  if (k <= 0) return [...f];
  let n = dmpDegree(f, v);
  if (n < k) return dmpZero(v);
  const deriv: unknown[] = [];
  for (const coeff of f.slice(0, -k)) {
    deriv.push(dmpMulGround(list(coeff), BigInt(falling(n, k)), v - 1, K));
    n--;
  }
  return dmpStrip(deriv, v);
}

/**
 * Differentiates the polynomial `m` times in the specified variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of differentiations.
 * @param j - Index of the polynomial variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The partial derivative.
 * @see SymPy `sympy.polys.densetools.dmp_diff_in`
 * @example
 * ```ts
 * import { ZZ, dmpDiffIn } from '@symjs/symjs';
 *
 * dmpDiffIn([[1, 2, 3], [2, 3, 1]], 1, 0, 1, ZZ); // => [[1, 2, 3]]
 * dmpDiffIn([[1, 2, 3], [2, 3, 1]], 1, 1, 1, ZZ); // => [[2, 2], [4, 3]]
 * ```
 */
export function dmpDiffIn(f: DensePoly, m: number, j: number, u: number, K: Domain): unknown[] {
  const [jj, uu] = [integer(j), integer(u)];
  checkIndex(jj, uu);
  return [...list(recIn(f, uu, 0, jj, (h, w) => dmpDiff(h, m, w, K)))];
}

/**
 * Evaluate f at x = a with Horner's scheme.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param a - Value substituted for the generator.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The value at the evaluation point.
 * @see SymPy `sympy.polys.densetools.dup_eval`
 * @example
 * ```ts
 * import { ZZ, dupEval } from '@symjs/symjs';
 *
 * dupEval([1, 2, 3], 2, ZZ); // => 11
 * ```
 */
export function dupEval(f: DensePoly, a: unknown, K: Domain): unknown {
  if (groundIsZero(a)) return K.convert(polyTC(f, K));
  let result: unknown = K.zero;
  for (const c of f) result = domainArith(K, 'add', domainArith(K, 'mul', result, a), c);
  return result;
}

/**
 * Uses Horner's rule to substitute the given value for the principal variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param a - Value substituted for the generator.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The specialized polynomial or ground value.
 * @see SymPy `sympy.polys.densetools.dmp_eval`
 * @example
 * ```ts
 * import { ZZ, dmpEval } from '@symjs/symjs';
 *
 * dmpEval([[2, 3], [1, 2]], 2, 1, ZZ); // => [5, 8]
 * ```
 */
export function dmpEval(f: DensePoly, a: unknown, u: number, K: Domain): unknown {
  const v = integer(u);
  if (!v) return dupEval(f, a, K);
  if (groundIsZero(a)) return polyTC(f, K);
  let result = list(polyLC(f, K));
  for (const coeff of f.slice(1)) result = dmpAdd(dmpMulGround(result, a, v - 1, K), list(coeff), v - 1, K);
  return result;
}

/**
 * Substitutes the supplied value for the selected generator.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param a - Value substituted for the generator.
 * @param j - Index of the polynomial variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The specialized polynomial or ground value.
 * @see SymPy `sympy.polys.densetools.dmp_eval_in`
 * @example
 * ```ts
 * import { ZZ, dmpEvalIn } from '@symjs/symjs';
 *
 * dmpEvalIn([[2, 3], [1, 2]], 2, 0, 1, ZZ); // => [5, 8]
 * dmpEvalIn([[2, 3], [1, 2]], 2, 1, 1, ZZ); // => [7, 4]
 * ```
 */
export function dmpEvalIn(f: DensePoly, a: unknown, j: number, u: number, K: Domain): unknown {
  const [jj, uu] = [integer(j), integer(u)];
  checkIndex(jj, uu);
  return recIn(f, uu, 0, jj, (h, w) => dmpEval(h, a, w, K), 1);
}

function recEvalTail(g: DensePoly, i: number, A: readonly unknown[], u: number, K: Domain): unknown {
  if (i === u) return dupEval(g, at(A, A.length - 1), K);
  const h = g.map((c) => recEvalTail(list(c), i + 1, A, u, K));
  return i < u - A.length + 1 ? h : dupEval(h, at(A, A.length - u + i - 1), K);
}

/**
 * Substitutes the supplied values for successive trailing generators.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param A - Values for successive trailing variables.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The specialized polynomial or ground value.
 * @see SymPy `sympy.polys.densetools.dmp_eval_tail`
 * @example
 * ```ts
 * import { ZZ, dmpEvalTail } from '@symjs/symjs';
 *
 * dmpEvalTail([[2, 3], [1, 2]], [2], 1, ZZ); // => [7, 4]
 * dmpEvalTail([[2, 3], [1, 2]], [2, 2], 1, ZZ); // => 18
 * ```
 */
export function dmpEvalTail(f: DensePoly, A: readonly unknown[], u: number, K: Domain): unknown {
  const v = integer(u);
  if (!A.length) return [...f];
  if (dmpZeroP(f, v)) return dmpZero(v - A.length);
  const e = recEvalTail(f, 0, A, v, K);
  return v === A.length - 1 ? e : dmpStrip(list(e), v - A.length);
}

/**
 * Evaluates the mth partial derivative at the supplied generator value.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Number of differentiations.
 * @param a - Value substituted for the generator.
 * @param j - Index of the polynomial variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The specialized derivative.
 * @throws RangeError when the variable index is outside the polynomial levels.
 * @see SymPy `sympy.polys.densetools.dmp_diff_eval_in`
 * @example
 * ```ts
 * import { ZZ, dmpDiffEvalIn } from '@symjs/symjs';
 *
 * dmpDiffEvalIn([[1, 2, 3], [2, 3, 1]], 1, 2, 0, 1, ZZ); // => [1, 2, 3]
 * dmpDiffEvalIn([[1, 2, 3], [2, 3, 1]], 1, 2, 1, 1, ZZ); // => [6, 11]
 * ```
 */
export function dmpDiffEvalIn(f: DensePoly, m: number, a: unknown, j: number, u: number, K: Domain): unknown {
  const [jj, uu] = [integer(j), integer(u)];
  if (jj > uu) throw new RangeError(`-${uu} <= j < ${uu} expected, got ${jj}`);
  if (!jj) return dmpEval(dmpDiff(f, m, uu, K), a, uu, K);
  return recIn(f, uu, 0, jj, (h, w) => dmpEval(dmpDiff(h, m, w, K), a, w, K), 1);
}

/**
 * Reduce the coefficients of f modulo p, symmetrically over ZZ.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param p - Modulus for reducing coefficients.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densetools.dup_trunc`
 * @example
 * ```ts
 * import { ZZ, dupTrunc } from '@symjs/symjs';
 *
 * dupTrunc([2, 3, 5, 7], 3, ZZ); // => [-1, 0, -1, 1]
 * ```
 */
export function dupTrunc(f: DensePoly, p: unknown, K: Domain): unknown[] {
  if (K instanceof IntegerRing) {
    const q = K.convert(p);
    return dupStrip(f.map((c) => {
      const r = K.rem(c, q);
      return r > q / 2n ? r - q : r;
    }));
  }
  if (K instanceof FiniteField) {
    const q = K.convert(p).val;
    return dupStrip(f.map((c) => K.convert(K.convert(c).val % q)));
  }
  return dupStrip(f.map((c) => K.rem(c, p)));
}

/**
 * Reduce f modulo a polynomial p in K[Y].
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param p - Modulus for reducing coefficients.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densetools.dmp_trunc`
 * @example
 * ```ts
 * import { ZZ, dmpTrunc } from '@symjs/symjs';
 *
 * dmpTrunc([[3, 8], [5, 6], [2, 3]], [1, -1], 1, ZZ); // => [[11], [11], [5]]
 * ```
 */
export function dmpTrunc(f: DensePoly, p: DensePoly, u: number, K: Domain): unknown[] {
  const v = integer(u);
  return dmpStrip(f.map((c) => dmpRem(list(c), p, v - 1, K)), v);
}

/**
 * Reduce the ground coefficients of f modulo p.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param p - Modulus for reducing coefficients.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densetools.dmp_ground_trunc`
 * @example
 * ```ts
 * import { ZZ, dmpGroundTrunc } from '@symjs/symjs';
 *
 * dmpGroundTrunc([[3, 8], [5, 6], [2, 3]], 3, 1, ZZ); // => [[-1], [-1, 0], [-1, 0]]
 * ```
 */
export function dmpGroundTrunc(f: DensePoly, p: unknown, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupTrunc(f, p, K);
  return dmpStrip(f.map((c) => dmpGroundTrunc(list(c), p, v - 1, K)), v);
}

/**
 * Divide all coefficients by the leading coefficient.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial divided by its leading coefficient.
 * @see SymPy `sympy.polys.densetools.dup_monic`
 * @example
 * ```ts
 * import { ZZ, dupMonic } from '@symjs/symjs';
 *
 * dupMonic([3, 6, 9], ZZ); // => [1, 2, 3]
 * ```
 */
export function dupMonic(f: DensePoly, K: Domain): unknown[] {
  if (!f.length) return [...f];
  const lc = polyLC(f, K);
  return K.isOne(lc) ? [...f] : dupExquoGround(f, lc, K);
}

/**
 * Divide all coefficients by the ground leading coefficient.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial normalized by its ground leading coefficient.
 * @see SymPy `sympy.polys.densetools.dmp_ground_monic`
 * @example
 * ```ts
 * import { ZZ, dmpGroundMonic } from '@symjs/symjs';
 *
 * dmpGroundMonic([[3, 6], [3, 0], [9, 3]], 1, ZZ); // => [[1, 2], [1, 0], [3, 1]]
 * ```
 */
export function dmpGroundMonic(f: DensePoly, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupMonic(f, K);
  if (dmpZeroP(f, v)) return [...f];
  const lc = dmpGroundLC(f, v, K);
  return K.isOne(lc) ? [...f] : dmpExquoGround(f, lc, v, K);
}

/**
 * Computes the content of a univariate polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The coefficient GCD.
 * @see SymPy `sympy.polys.densetools.dup_content`
 * @example
 * ```ts
 * import { ZZ, dupContent } from '@symjs/symjs';
 *
 * dupContent([6, 8, 12], ZZ); // => 2
 * ```
 */
export function dupContent(f: DensePoly, K: Domain): unknown {
  return groundContent(f, 0, K);
}

function groundContent(f: DensePoly, u: number, K: Domain): unknown {
  if (dmpZeroP(f, u)) return K.zero;
  let cont: unknown = K.zero;
  for (const c of f) {
    cont = K.gcd(cont, u ? groundContent(list(c), u - 1, K) : c);
    if (K !== QQ && K.isOne(cont)) break;
  }
  return cont;
}

/**
 * Computes the content in the ground domain.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The ground coefficient GCD.
 * @see SymPy `sympy.polys.densetools.dmp_ground_content`
 * @example
 * ```ts
 * import { ZZ, dmpGroundContent } from '@symjs/symjs';
 *
 * dmpGroundContent([[2, 6], [4, 12]], 1, ZZ); // => 2
 * ```
 */
export function dmpGroundContent(f: DensePoly, u: number, K: Domain): unknown {
  return groundContent(f, integer(u), K);
}

/**
 * Factors the coefficient GCD out of the polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The content and primitive part.
 * @see SymPy `sympy.polys.densetools.dup_primitive`
 * @remarks SymPy returns `(2, [3, 4, 6])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupPrimitive } from '@symjs/symjs';
 *
 * dupPrimitive([6, 8, 12], ZZ); // => [2, [3, 4, 6]]
 * ```
 */
export function dupPrimitive(f: DensePoly, K: Domain): [unknown, unknown[]] {
  return dmpGroundPrimitive(f, 0, K);
}

/**
 * Separates the multivariate polynomial from its ground content.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The content and primitive part.
 * @see SymPy `sympy.polys.densetools.dmp_ground_primitive`
 * @remarks SymPy returns `(2, [[1, 3], [2, 6]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpGroundPrimitive } from '@symjs/symjs';
 *
 * dmpGroundPrimitive([[2, 6], [4, 12]], 1, ZZ); // => [2, [[1, 3], [2, 6]]]
 * ```
 */
export function dmpGroundPrimitive(f: DensePoly, u: number, K: Domain): [unknown, unknown[]] {
  const v = integer(u);
  if (dmpZeroP(f, v)) return [K.zero, [...f]];
  const cont = groundContent(f, v, K);
  return K.isOne(cont) ? [cont, [...f]] : [cont, dmpQuoGround(f, cont, v, K)];
}

/**
 * Divides both inputs by their common content.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The common content and both quotients.
 * @see SymPy `sympy.polys.densetools.dup_extract`
 * @remarks SymPy returns `(2, [3, 6, 9], [2, 4, 6])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupExtract } from '@symjs/symjs';
 *
 * dupExtract([6, 12, 18], [4, 8, 12], ZZ); // => [2, [3, 6, 9], [2, 4, 6]]
 * ```
 */
export function dupExtract(f: DensePoly, g: DensePoly, K: Domain): [unknown, unknown[], unknown[]] {
  return dmpGroundExtract(f, g, 0, K);
}

/**
 * Divides both inputs by their common ground content.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The common ground content and both quotients.
 * @see SymPy `sympy.polys.densetools.dmp_ground_extract`
 * @remarks SymPy returns `(2, [[3, 6], [9]], [[2, 4], [6]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpGroundExtract } from '@symjs/symjs';
 *
 * dmpGroundExtract([[6, 12], [18]], [[4, 8], [12]], 1, ZZ); // => [2, [[3, 6], [9]], [[2, 4], [6]]]
 * ```
 */
export function dmpGroundExtract(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown, unknown[], unknown[]] {
  const v = integer(u);
  const gcd = K.gcd(groundContent(f, v, K), groundContent(g, v, K));
  if (K.isOne(gcd)) return [gcd, [...f], [...g]];
  return [gcd, dmpQuoGround(f, gcd, v, K), dmpQuoGround(g, gcd, v, K)];
}

/**
 * Substitutes `x + I*y` and separates the real and imaginary parts.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Two polynomials in `x` and `y`.
 * @throws DomainError when the coefficients are outside the supported real domains.
 * @see SymPy `sympy.polys.densetools.dup_real_imag`
 * @remarks SymPy returns `([[1], [1], [-3, 0, 1], [-1, 0, 1]], [[3, 0], [2, 0], [-1, 0, 1, 0]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupRealImag } from '@symjs/symjs';
 *
 * dupRealImag([1, 1, 1, 1], ZZ); // => [[[1], [1], [-3, 0, 1], [-1, 0, 1]], [[3, 0], [2, 0], [-1, 0, 1, 0]]]
 * ```
 */
export function dupRealImag(f: DensePoly, K: Domain): [unknown[], unknown[]] {
  if (!(K instanceof IntegerRing || K instanceof RationalField)) throw new DomainError(`computing real and imaginary parts is not supported over ${K.toString()}`);
  let [f1, f2] = [dmpZero(1), dmpZero(1)];
  if (!f.length) return [f1, f2];
  const g = [[[K.one, K.zero]], [[K.one], []]];
  let h = list(dmpGround(first(f), 2));
  for (const c of f.slice(1)) h = dmpAddTerm(dmpMul(h, g, 2, K), dmpGround(c, 1), 0, 2, K);
  const n = h.length - 1;
  h.forEach((c, i) => {
    const part = list(c);
    const k = (n - i) % 4;
    if (k === 0) f1 = dmpAdd(f1, part, 1, K);
    else if (k === 1) f2 = dmpAdd(f2, part, 1, K);
    else if (k === 2) f1 = dmpSub(f1, part, 1, K);
    else f2 = dmpSub(f2, part, 1, K);
  });
  return [f1, f2];
}

/**
 * Negates the indeterminate of the polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial evaluated at the negated generator.
 * @see SymPy `sympy.polys.densetools.dup_mirror`
 * @example
 * ```ts
 * import { ZZ, dupMirror } from '@symjs/symjs';
 *
 * dupMirror([1, 2, -4, 2], ZZ); // => [-1, 2, 4, 2]
 * ```
 */
export function dupMirror(f: DensePoly, K: Domain): unknown[] {
  const g = [...f];
  for (let i = g.length - 2; i >= 0; i -= 2) g[i] = domainNeg(K, g[i]);
  return g;
}

/**
 * Scales the polynomial's argument by a ground factor.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param a - Factor multiplying the generator.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial evaluated at the scaled generator.
 * @see SymPy `sympy.polys.densetools.dup_scale`
 * @example
 * ```ts
 * import { ZZ, dupScale } from '@symjs/symjs';
 *
 * dupScale([1, -2, 1], 2, ZZ); // => [4, -4, 1]
 * ```
 */
export function dupScale(f: DensePoly, a: unknown, K: Domain): unknown[] {
  const g = [...f];
  let b = a;
  for (let i = g.length - 2; i >= 0; i--) {
    g[i] = domainArith(K, 'mul', b, g[i]);
    b = domainArith(K, 'mul', b, a);
  }
  return g;
}

/**
 * Translates the polynomial's argument by the supplied value.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param a - Translation added to the generator or generators.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The translated polynomial.
 * @see SymPy `sympy.polys.densetools.dup_shift`
 * @example
 * ```ts
 * import { ZZ, dupShift } from '@symjs/symjs';
 *
 * dupShift([1, -2, 1], 2, ZZ); // => [1, 2, 1]
 * ```
 */
export function dupShift(f: DensePoly, a: unknown, K: Domain): unknown[] {
  const g = [...f];
  for (let i = g.length - 1; i > 0; i--) {
    for (let j = 0; j < i; j++) g[j + 1] = domainArith(K, 'add', g[j + 1], domainArith(K, 'mul', a, g[j]));
  }
  return g;
}

/**
 * Translates each generator by the corresponding supplied shift.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param a - Translation added to the generator or generators.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial after translating each generator.
 * @see SymPy `sympy.polys.densetools.dmp_shift`
 * @example
 * ```ts
 * import { ZZ, dmpShift } from '@symjs/symjs';
 *
 * dmpShift([[1, 0], [2, 3], [4, 5]], [1, 2], 1, ZZ); // => [[1, 2], [4, 11], [7, 22]]
 * ```
 */
export function dmpShift(f: DensePoly, a: readonly unknown[], u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupShift(f, first(a), K);
  if (dmpZeroP(f, v)) return [...f];
  const [a0, a1] = [first(a), a.slice(1)];
  const g = a1.some((c) => !groundIsZero(c)) ? f.map((c) => dmpShift(list(c), a1, v - 1, K)) : [...f];
  if (!groundIsZero(a0)) {
    for (let i = g.length - 1; i > 0; i--) {
      for (let j = 0; j < i; j++) g[j + 1] = dmpAdd(list(g[j + 1]), dmpMulGround(list(g[j]), a0, v - 1, K), v - 1, K);
    }
  }
  return dmpStrip(g, v);
}

/**
 * Substitutes the ratio of two polynomials and clears the denominator to the input degree.
 *
 * @param f - Polynomial in the original generator.
 * @param p - Numerator of the rational substitution.
 * @param q - Denominator of the rational substitution.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial after the rational substitution and denominator clearing.
 * @see SymPy `sympy.polys.densetools.dup_transform`
 * @example
 * ```ts
 * import { ZZ, dupTransform } from '@symjs/symjs';
 *
 * dupTransform([1, -2, 1], [1, 0, 1], [1, -1], ZZ); // => [1, -2, 5, -4, 4]
 * ```
 */
export function dupTransform(f: DensePoly, p: DensePoly, q: DensePoly, K: Domain): unknown[] {
  if (!f.length) return [];
  const Q: unknown[][] = [[K.one]];
  for (let i = 1; i < f.length; i++) Q.push(dupMul(at(Q, i - 1), q, K));
  let h: unknown[] = [first(f)];
  f.slice(1).forEach((c, i) => {
    h = dupAdd(dupMul(h, p, K), dupMulGround(at(Q, i + 1), c, K), K);
  });
  return h;
}

/**
 * Substitutes the second polynomial into the first.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The composition of the input polynomials.
 * @see SymPy `sympy.polys.densetools.dup_compose`
 * @example
 * ```ts
 * import { ZZ, dupCompose } from '@symjs/symjs';
 *
 * dupCompose([1, 1, 0], [1, -1], ZZ); // => [1, -1, 0]
 * ```
 */
export function dupCompose(f: DensePoly, g: DensePoly, K: Domain): unknown[] {
  if (g.length <= 1) return dupStrip([dupEval(f, polyLC(g, K), K)]);
  if (!f.length) return [];
  let h: unknown[] = [first(f)];
  for (const c of f.slice(1)) h = dupAddTerm(dupMul(h, g, K), c, 0, K);
  return h;
}

/**
 * Composes univariate polynomials over the coefficient domain.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The composition in the main variable.
 * @see SymPy `sympy.polys.densetools.dmp_compose`
 * @example
 * ```ts
 * import { ZZ, dmpCompose } from '@symjs/symjs';
 *
 * dmpCompose([[1, 2], [1, 0]], [[1, 0]], 1, ZZ); // => [[1, 3, 0]]
 * ```
 */
export function dmpCompose(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] {
  const v = integer(u);
  if (!v) return dupCompose(f, g, K);
  if (dmpZeroP(f, v)) return [...f];
  let h: unknown[] = [first(f)];
  for (const c of f.slice(1)) h = dmpAddTerm(dmpMul(h, g, v, K), c, 0, v, K);
  return h;
}

function rawDict(f: DensePoly): Map<number, unknown> {
  const n = f.length - 1;
  return new Map(f.flatMap((c, k) => groundIsZero(c) ? [] : [[n - k, c] as [number, unknown]]));
}

function rightDecompose(fIn: DensePoly, s: number, K: Domain): unknown[] {
  const n = fIn.length - 1;
  const lc = polyLC(fIn, K);
  const f = rawDict(fIn);
  const g = new Map<number, unknown>([[s, K.one]]);
  const r = Math.floor(n / s);
  for (let i = 1; i < s; i++) {
    let coeff: unknown = K.zero;
    for (let j = 0; j < i; j++) {
      const [fc, gc] = [f.get(n + j - i), g.get(s - j)];
      if (fc === undefined || gc === undefined) continue;
      coeff = domainArith(K, 'add', coeff, mulInt(K, domainArith(K, 'mul', fc, gc), i - r * j));
    }
    g.set(s - i, groundQuo(coeff, mulInt(K, lc, i * r), K));
  }
  return dupFromRawDict(g, K);
}

function leftDecompose(fIn: DensePoly, h: DensePoly, K: Domain): unknown[] | undefined {
  const g = new Map<number, unknown>();
  let f = [...fIn];
  for (let i = 0; f.length; i++) {
    const [q, r] = dupDiv(f, h, K);
    if (dupDegree(r) > 0) return undefined;
    g.set(i, polyLC(r, K));
    f = q;
  }
  return dupFromRawDict(g, K);
}

function decomposeOnce(f: DensePoly, K: Domain): [unknown[], unknown[]] | undefined {
  const df = f.length - 1;
  for (let s = 2; s < df; s++) {
    if (df % s !== 0) continue;
    const h = rightDecompose(f, s, K);
    const g = leftDecompose(f, h, K);
    if (g !== undefined) return [g, h];
  }
  return undefined;
}

/**
 * Writes a univariate polynomial as a composition of polynomial functions.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The components in composition order.
 * @see SymPy `sympy.polys.densetools.dup_decompose`
 * @example
 * ```ts
 * import { ZZ, dupDecompose } from '@symjs/symjs';
 *
 * dupDecompose([1, -2, 1, 0, 0], ZZ); // => [[1, 0, 0], [1, -1, 0]]
 * ```
 */
export function dupDecompose(fIn: DensePoly, K: Domain): unknown[][] {
  const F: unknown[][] = [];
  let f = [...fIn];
  for (let result = decomposeOnce(f, K); result !== undefined; result = decomposeOnce(f, K)) {
    [f] = result;
    F.unshift(result[1]);
  }
  return [f, ...F];
}

/**
 * Convert an algebraic coefficient generator into the first polynomial variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense polynomial with the algebraic generator adjoined, its level and its ground domain.
 * @throws DomainError when the coefficient domain is not algebraic.
 * @see SymPy `sympy.polys.densetools.dmp_alg_inject`
 * @example
 * ```ts
 * import { QQ, dmpAlgInject, ex } from '@symjs/symjs';
 *
 * const K = QQ.algebraicField(ex`sqrt(2)`);
 * dmpAlgInject([1, ex`sqrt(2)`], 0, K)[1]; // => 1
 * ```
 */
export function dmpAlgInject(f: DensePoly, u: number, K: Domain): [unknown[], number, Domain] {
  if (!(K instanceof AlgebraicField || K instanceof GaussianDomain)) throw new DomainError('computation can be done only in an algebraic domain');
  const v = integer(u);
  const terms = new Map<number[], unknown>();
  for (const [powers, c] of dmpToDict(f, v)) {
    if (K instanceof AlgebraicField) {
      const coefficients = K.convert(c).rep;
      coefficients.forEach((coefficient, i) => {
        if (!coefficient.isZero) terms.set([coefficients.length - i - 1, ...powers], coefficient);
      });
    } else {
      const coefficient = K.convert(c);
      if (!coefficient.re.isZero) terms.set([0, ...powers], K.dom.convert(coefficient.re));
      if (!coefficient.im.isZero) terms.set([1, ...powers], K.dom.convert(coefficient.im));
    }
  }
  return [dmpFromDict(terms, v + 1, K.dom), v + 1, K.dom];
}

/**
 * Lifts the polynomial from an algebraic extension to its ground domain while retaining its roots.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The lifted polynomial.
 * @see SymPy `sympy.polys.densetools.dmp_lift`
 * @example
 * ```ts
 * import { QQ, dmpLift, ex } from '@symjs/symjs';
 *
 * const K = QQ.algebraicField(ex`sqrt(2)`);
 * dmpLift([1, ex`sqrt(2)`], 0, K).map(c => QQ.toSympy(c)); // => [1, 0, -2]
 * ```
 */
export function dmpLift(f: DensePoly, u: number, K: Domain): unknown[] {
  const [F, v, K2] = dmpAlgInject(f, u, K);
  const mod = K instanceof AlgebraicField ? K.mod : [1n, 0n, 1n];
  const P = dmpInclude(mod, Array.from({ length: v }, (_, i) => i + 1), 0, K2);
  const variables = Array.from({ length: v + 1 }, (_, i) => new Dummy(`x${i}`));
  const expr = (g: DensePoly): Expr => add(...[...dmpToDict(g, v)].map(([m, c]) => mul(K2.toSympy(c), ...variables.map((x, i) => pow(x, at(m, i))))));
  const rest = variables.slice(1);
  const r = Poly.from(resultant(expr(F), expr(P), first(variables)), rest, { domain: K2.toString() });
  return dmpFromDict(new Map(r.terms().map(([m, c]) => [m, K2.convert(c)])), v - 1, K2);
}

/**
 * Counts the changes of sign in the sequence of nonzero coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sign variation count.
 * @throws DomainError when the coefficients do not admit sign comparisons.
 * @see SymPy `sympy.polys.densetools.dup_sign_variations`
 * @example
 * ```ts
 * import { ZZ, dupSignVariations } from '@symjs/symjs';
 *
 * dupSignVariations([1, 0, -1, -1, 1], ZZ); // => 2
 * ```
 */
export function dupSignVariations(f: DensePoly, K: Domain): number {
  let isNegative: (a: unknown) => boolean;
  if (K instanceof IntegerRing || K instanceof RationalField || K instanceof RealField) isNegative = (a) => K.isNegative(a);
  else if (K instanceof AlgebraicField && K.ext.asExpr().isComparable) {
    isNegative = (a) => !groundIsZero(a) && isNegativeExpr(K.toSympy(a)) === true;
  } else throw new DomainError(`sign variation counting not supported over ${K.toString()}`);
  let [prev, k]: [unknown, number] = [K.zero, 0];
  for (const coeff of f) {
    if (isNegative(domainArith(K, 'mul', coeff, prev))) k++;
    if (!groundIsZero(coeff)) prev = coeff;
  }
  return k;
}

/** Whether the elements of K have denominators other than one (SymPy K.denom). */
function fractional(K: Domain): boolean {
  return K instanceof RationalField || K instanceof GaussianRationalField || K instanceof ExpressionDomain || K instanceof FractionField;
}

function denominator(c: unknown, K: Domain): unknown {
  if (K instanceof RationalField) return K.convert(c).denominator;
  if (K instanceof GaussianRationalField) return K.denom(c);
  return K.convert(asNumerDenom(K.toSympy(c))[1]);
}

function numerator(c: unknown, K: Domain): unknown {
  if (K instanceof RationalField) return K.convert(c).numerator;
  if (K instanceof GaussianRationalField) return K.numer(c);
  return K.convert(asNumerDenom(K.toSympy(c))[0]);
}

function groundLcm(a: unknown, b: unknown, K: Domain): unknown {
  if (K instanceof PolynomialRing) {
    // SymPy PolyElement.lcm: monic when the coefficients are a field
    const domain = { domain: K.ground };
    const [f, g] = [Poly.from(K.toSympy(a), K.symbols, domain), Poly.from(K.toSympy(b), K.symbols, domain)];
    const l = K.ground === 'EX' ? Poly.from(lcmList([f.asExpr(), g.asExpr()]), K.symbols, domain).monic() : f.lcm(g);
    return K.convert(l.asExpr());
  }
  if (K instanceof ExpressionDomain) return K.convert(lcmList([K.toSympy(a), K.toSympy(b)]));
  return K.lcm(a, b);
}

function commonDenominator(g: DensePoly, v: number, K0: Domain, K1: Domain): unknown {
  let common = K1.convert(K1.one);
  if (!fractional(K0)) return common;
  for (const c of g) common = groundLcm(common, v ? commonDenominator(list(c), v - 1, K0, K1) : K1.convert(denominator(c, K0)), K1);
  return common;
}

/**
 * Clears denominators using their least common multiple.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K0 - Source coefficient domain.
 * @param K1 - Target coefficient domain.
 * @param convert - Convert the resulting coefficients to the associated ring.
 * @returns The common denominator and scaled polynomial.
 * @see SymPy `sympy.polys.densetools.dup_clear_denoms`
 * @example
 * ```ts
 * import { QQ, dupClearDenoms, ex } from '@symjs/symjs';
 *
 * dupClearDenoms([QQ.convert(ex`1/2`), QQ.convert(ex`1/3`)], QQ)[0]; // => 6
 * ```
 */
export function dupClearDenoms(f: DensePoly, K0: Domain, K1?: Domain, convert = false): [unknown, unknown[]] {
  const R = K1 ?? K0.getRing();
  const common = commonDenominator(f, 0, K0, R);
  if (groundEquals(common, 1n)) return [common, convert ? dupConvert(f, K0, R) : [...f]];
  const g = f.map((c) => domainArith(R, 'mul', R.convert(numerator(c, K0)), groundQuo(common, R.convert(denominator(c, K0)), R)));
  return [common, convert ? g : dupConvert(g, R, K0)];
}

/**
 * Clears denominators of the ground coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K0 - Source coefficient domain.
 * @param K1 - Target coefficient domain.
 * @param convert - Convert the resulting coefficients to the associated ring.
 * @returns The common denominator and scaled polynomial.
 * @see SymPy `sympy.polys.densetools.dmp_clear_denoms`
 * @example
 * ```ts
 * import { QQ, dmpClearDenoms, ex } from '@symjs/symjs';
 *
 * dmpClearDenoms([[QQ.convert(ex`1/2`)], [QQ.convert(ex`1/3`), 1]], 1, QQ)[0]; // => 6
 * ```
 */
export function dmpClearDenoms(f: DensePoly, u: number, K0: Domain, K1?: Domain, convert = false): [unknown, unknown[]] {
  const v = integer(u);
  if (!v) return dupClearDenoms(f, K0, K1, convert);
  const R = K1 ?? K0.getRing();
  const common = commonDenominator(f, v, K0, R);
  const g = groundEquals(common, 1n) ? [...f] : dmpMulGround(f, common, v, K0);
  return [common, convert ? dmpConvert(g, v, K0, R) : g];
}

/**
 * Uses Newton iteration to invert the polynomial modulo `x**n`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param n - Truncation order of the inverse series.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The truncated reciprocal.
 * @throws NotReversible when the constant coefficient is not a unit.
 * @see SymPy `sympy.polys.densetools.dup_revert`
 * @example
 * ```ts
 * import { QQ, dupRevert, ex } from '@symjs/symjs';
 *
 * dupRevert([QQ.convert(ex`-1/720`), 0, QQ.convert(ex`1/24`), 0, QQ.convert(ex`-1/2`), 0, 1], 8, QQ).map(c => QQ.toSympy(c)); // => [61/720, 0, 5/24, 0, 1/2, 0, 1]
 * ```
 */
export function dupRevert(f: DensePoly, n: number, K: Domain): unknown[] {
  const c = polyTC(f, K);
  if (groundIsZero(c) || !(K.isField || K.isOne(c) || K.isOne(domainNeg(K, c)))) throw new NotReversible('only units are reversible in a ring');
  let g: unknown[] = [domainArith(K, 'quo', K.one, c)];
  let h: unknown[] = [K.one, K.zero, K.zero];
  const N = Math.ceil(Math.log2(integer(n)));
  for (let i = 1; i <= N; i++) {
    const a = dupMulGround(g, 2n, K);
    const b = dupMul(f, dupSqr(g, K), K);
    g = dupRem(dupSub(a, b, K), h, K);
    h = dupLshift(h, dupDegree(h), K);
  }
  return g;
}

/**
 * Finds the multiplicative inverse of a univariate polynomial modulo `x**n`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Truncation order of the inverse series.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The truncated reciprocal.
 * @throws MultivariatePolynomialError when the operation requires a univariate polynomial.
 * @see SymPy `sympy.polys.densetools.dmp_revert`
 * @example
 * ```ts
 * import { ZZ, dmpRevert } from '@symjs/symjs';
 *
 * dmpRevert([1, 1], 3, 0, ZZ); // => [-1, 1, -1, 1]
 * ```
 */
export function dmpRevert(f: DensePoly, g: number, u: number, K: Domain): unknown[] {
  if (!integer(u)) return dupRevert(f, g, K);
  throw new MultivariatePolynomialError(`${String(f)}, ${String(g)}`);
}


import { dmpTools } from './polyclasses';
Object.assign(dmpTools, { dmpDiffIn, dmpEvalIn, dmpGroundMonic, dmpGroundContent, dmpGroundPrimitive, dmpGroundTrunc, dmpCompose, dupDecompose, dmpClearDenoms });
