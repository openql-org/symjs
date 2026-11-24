// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 polys/densearith.py, BSD-3-Clause; see LICENSE.

/** Arithmetic of dense recursive polynomials, with leading coefficients first. */
import { ExactQuotientFailed } from '../core/errors';
import { at, first } from '../core/guard';
import { abs } from '../functions/elementary/elementary';
import { dmpDegree, dmpFromDict, dmpGround, dmpStrip, dmpToDict, dmpZero, dmpZeroP, groundIsZero } from './densebasic';
import type { DensePoly } from './densebasic';
import { domainArith, domainNeg, groundRational, PolynomialRing } from './domains';
import type { Domain } from './domains';
import { PolynomialDivisionFailed } from './polyerrors';

function list(f: unknown): DensePoly {
  if (!Array.isArray(f)) throw new TypeError('a dense polynomial level must be a list');
  return f;
}

function integer(n: number): number {
  const r = groundRational(n);
  if (r === undefined || r[1] !== 1n || !Number.isSafeInteger(Number(r[0]))) throw new RangeError('expected a safe integer');
  return Number(r[0]);
}

function zero(u: number, K: Domain): unknown {
  return u < 0 ? K.zero : dmpZero(u);
}

function isZero(f: unknown, u: number): boolean {
  return u < 0 ? groundIsZero(f) : dmpZeroP(list(f), u);
}

function sum(f: unknown, g: unknown, u: number, K: Domain, subtract = false): unknown {
  if (u < 0) return domainArith(K, subtract ? 'sub' : 'add', f, g);
  const [a, b] = [list(f), list(g)];
  const n = Math.max(a.length, b.length);
  const h = Array.from({ length: n }, (_, i) => sum(
    i < n - a.length ? zero(u - 1, K) : at(a, i - n + a.length),
    i < n - b.length ? zero(u - 1, K) : at(b, i - n + b.length), u - 1, K, subtract));
  return dmpStrip(h, u);
}

function product(f: unknown, g: unknown, u: number, K: Domain): unknown {
  if (u < 0) return domainArith(K, 'mul', f, g);
  if (isZero(f, u) || isZero(g, u)) return dmpZero(u);
  const [a, b] = [list(f), list(g)];
  const h = Array.from({ length: a.length + b.length - 1 }, () => zero(u - 1, K));
  for (let i = 0; i < a.length; i++) for (let j = 0; j < b.length; j++) {
    h[i + j] = sum(at(h, i + j), product(at(a, i), at(b, j), u - 1, K), u - 1, K);
  }
  return dmpStrip(h, u);
}

function power(f: unknown, n: number, u: number, K: Domain): unknown {
  if (n < 0) throw new RangeError('Cannot raise polynomial to a negative power');
  let [b, e, h] = [f, n, u < 0 ? K.one : dmpGround(K.one, u)];
  while (e > 0) {
    if (e % 2) h = product(h, b, u, K);
    e = Math.floor(e / 2);
    if (e) b = product(b, b, u, K);
  }
  return h;
}

function term(f: DensePoly, c: unknown, i: number, u: number, K: Domain, subtract = false): unknown[] {
  if (isZero(c, u - 1)) return [...f];
  const h = [c, ...Array.from({ length: i }, () => zero(u - 1, K))];
  return [...list(sum(f, h, u, K, subtract))];
}

function mulTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] {
  if (isZero(f, u) || isZero(c, u - 1)) return dmpZero(u);
  return [...f.map((a) => product(a, c, u - 1, K)), ...Array.from({ length: i }, () => zero(u - 1, K))];
}

function mapGround(f: DensePoly, u: number, fn: (c: unknown) => unknown): unknown[] {
  return f.map((c) => u === 0 ? fn(c) : mapGround(list(c), u - 1, fn));
}

function mulGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] {
  if (u === 0 && groundIsZero(c)) return [];
  return f.map((a) => u === 0 ? domainArith(K, 'mul', a, c) : mulGround(list(a), c, u - 1, K));
}

function quoGround(f: DensePoly, c: unknown, u: number, K: Domain, exact: boolean): unknown[] {
  if (groundIsZero(c)) throw new RangeError('polynomial division by zero');
  return mapGround(f, u, (a) => {
    const [q, r] = groundDivide(a, c, K);
    if (exact && !groundIsZero(r)) throw new ExactQuotientFailed('ground coefficient does not divide exactly');
    return q;
  });
}

function groundDivide(a: unknown, b: unknown, K: Domain): [unknown, unknown] {
  if (K.isField) return [domainArith(K, 'quo', a, b), K.zero];
  if (K instanceof PolynomialRing) {
    const u = K.ngens - 1;
    const [q, r] = divide(dmpFromDict(K.toDict(a), u, K.dom), dmpFromDict(K.toDict(b), u, K.dom), u, K.dom, K.dom.isField);
    return [K.toSympy(dmpToDict(q, u)), K.toSympy(dmpToDict(r, u))];
  }
  return K.div(a, b);
}

/** Long division in the first variable; coefficient division is recursive. */
function divide(f: DensePoly, g: DensePoly, u: number, K: Domain, field: boolean, pseudo = false): [unknown[], unknown[]] {
  const roundoff = field && K.ground === 'RR' && u === 0;
  const dg = dmpDegree(g, u);
  if (dg < 0) throw new RangeError('polynomial division by zero');
  let q = dmpZero(u);
  let r = [...f];
  let dr = dmpDegree(r, u);
  if (dr < dg) return [q, r];
  const lc = first(g);
  let remaining = dr - dg + 1;
  while (dr >= dg) {
    const lead = first(r);
    let c: unknown;
    if (pseudo) {
      c = lead;
      q = mulTerm(q, lc, 0, u, K);
      r = mulTerm(r, lc, 0, u, K);
      remaining--;
    } else if (u > 0) {
      const [cq, cr] = divide(list(lead), list(lc), u - 1, K, field);
      if (!dmpZeroP(cr, u - 1)) break;
      c = cq;
    } else {
      const [cq, cr] = groundDivide(lead, lc, K);
      if (!groundIsZero(cr)) {
        if (field) throw new ExactQuotientFailed('leading coefficient does not divide exactly');
        break;
      }
      c = cq;
    }
    q = term(q, c, dr - dg, u, K);
    r = [...list(sum(r, mulTerm(g, c, dr - dg, u, K), u, K, true))];
    const previous = dr;
    dr = dmpDegree(r, u);
    if (dr >= dg && dr >= previous) {
      // Floating division can leave a rounded leading residue. Its degree
      // must still decrease, as in SymPy's dup_ff_div over inexact fields.
      if (roundoff) {
        r = dmpStrip(r.slice(1), 0);
        dr = dmpDegree(r, 0);
      } else throw new PolynomialDivisionFailed('polynomial division did not decrease the degree');
    }
  }
  if (pseudo) {
    const c = power(lc, remaining, u - 1, K);
    q = mulTerm(q, c, 0, u, K);
    r = mulTerm(r, c, 0, u, K);
  }
  return [q, r];
}

function exactQuotient(result: [unknown[], unknown[]], u: number): unknown[] {
  if (!dmpZeroP(result[1], u)) throw new ExactQuotientFailed('polynomial does not divide exactly');
  return result[0];
}

function absolute(c: unknown, K: Domain): unknown {
  return K.convert(abs(K.toSympy(c)));
}

function norm(f: DensePoly, u: number, K: Domain, kind: 'max' | 'l1' | 'l2'): unknown {
  let h: unknown = K.zero;
  for (const c of f) {
    const a = u > 0 ? norm(list(c), u - 1, K, kind) : kind === 'l2' ? domainArith(K, 'mul', c, c) : absolute(c, K);
    h = kind === 'max' ? K.isPositive(domainArith(K, 'sub', a, h)) ? a : h : domainArith(K, 'add', h, a);
  }
  return h;
}

/**
 * Multiply a sequence of dense polynomials.
 *
 * @param polys - Input polynomials.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densearith.dmp_expand`
 * @example
 * ```ts
 * import { ZZ, dmpExpand } from '@symjs/symjs';
 *
 * dmpExpand([[[1], [], [1, 0, 0]], [[1], [1]]], 1, ZZ); // => [[1], [1], [1, 0, 0], [1, 0, 0]]
 * ```
 */
export function dmpExpand(polys: readonly DensePoly[], u: number, K: Domain): unknown[] {
  return polys.reduce<unknown[]>((h, f) => [...list(product(h, f, integer(u), K))], [...list(dmpGround(K.one, integer(u)))]);
}

/**
 * Multiply a sequence of univariate polynomials.
 *
 * @param polys - Input polynomials.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densearith.dup_expand`
 * @example
 * ```ts
 * import { ZZ, dupExpand } from '@symjs/symjs';
 *
 * dupExpand([[1, 0, -1], [1, 0], [2]], ZZ); // => [2, 0, -2, 0]
 * ```
 */
export function dupExpand(polys: readonly DensePoly[], K: Domain): unknown[] { return dmpExpand(polys, 0, K); }

/**
 * Multiply by x**n.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param n - Number of powers to shift.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial multiplied by the specified power of the generator.
 * @see SymPy `sympy.polys.densearith.dup_lshift`
 * @example
 * ```ts
 * import { ZZ, dupLshift } from '@symjs/symjs';
 *
 * dupLshift([1, 0, 1], 2, ZZ); // => [1, 0, 1, 0, 0]
 * ```
 */
export function dupLshift(f: DensePoly, n: number, K: Domain): unknown[] {
  return f.length === 0 ? [] : [...f, ...Array.from({ length: integer(n) }, () => K.zero)];
}

/**
 * Remove the n trailing coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param n - Number of powers to shift.
 * @param _K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial after discarding the specified number of trailing coefficients.
 * @see SymPy `sympy.polys.densearith.dup_rshift`
 * @example
 * ```ts
 * import { ZZ, dupRshift } from '@symjs/symjs';
 *
 * dupRshift([1, 0, 1, 0, 0], 2, ZZ); // => [1, 0, 1]
 * dupRshift([1, 0, 1, 0, 2], 2, ZZ); // => [1, 0, 1]
 * ```
 */
export function dupRshift(f: DensePoly, n: number, _K: Domain): unknown[] {
  const k = integer(n);
  // Dividing by x**0 is the identity. SymPy's f[:-0] incorrectly gives [].
  return k === 0 ? [...f] : f.slice(0, -k);
}

/**
 * The sum of the polynomial and the term `c*x**i`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the monomial to add, subtract or multiply.
 * @param i - Exponent of the term in the main variable.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the polynomial and the term `c*x**i`.
 * @see SymPy `sympy.polys.densearith.dup_add_term`
 * @example
 * ```ts
 * import { ZZ, dupAddTerm } from '@symjs/symjs';
 *
 * dupAddTerm([1, 0, -1], 2, 4, ZZ); // => [2, 0, 1, 0, -1]
 * ```
 */
export function dupAddTerm(f: DensePoly, c: unknown, i: number, K: Domain): unknown[] { return term(f, c, integer(i), 0, K); }

/**
 * The difference between the polynomial and the term `c*x**i`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the monomial to add, subtract or multiply.
 * @param i - Exponent of the term in the main variable.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The difference between the polynomial and the term `c*x**i`.
 * @see SymPy `sympy.polys.densearith.dup_sub_term`
 * @example
 * ```ts
 * import { ZZ, dupSubTerm } from '@symjs/symjs';
 *
 * dupSubTerm([2, 0, 1, 0, -1], 2, 4, ZZ); // => [1, 0, -1]
 * ```
 */
export function dupSubTerm(f: DensePoly, c: unknown, i: number, K: Domain): unknown[] { return term(f, c, integer(i), 0, K, true); }

/**
 * The product of the polynomial and the term `c*x**i`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the monomial to add, subtract or multiply.
 * @param i - Exponent of the term in the main variable.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The product of the polynomial and the term `c*x**i`.
 * @see SymPy `sympy.polys.densearith.dup_mul_term`
 * @example
 * ```ts
 * import { ZZ, dupMulTerm } from '@symjs/symjs';
 *
 * dupMulTerm([1, 0, -1], 3, 2, ZZ); // => [3, 0, -3, 0, 0]
 * ```
 */
export function dupMulTerm(f: DensePoly, c: unknown, i: number, K: Domain): unknown[] { return mulTerm(f, c, integer(i), 0, K); }

/**
 * The polynomial with the ground coefficient added to its constant term.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial with the ground coefficient added to its constant term.
 * @see SymPy `sympy.polys.densearith.dup_add_ground`
 * @example
 * ```ts
 * import { ZZ, dupAddGround } from '@symjs/symjs';
 *
 * dupAddGround([1, 2, 3, 4], 4, ZZ); // => [1, 2, 3, 8]
 * ```
 */
export function dupAddGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return term(f, dmpGround(c, 0 - 1), 0, 0, K); }

/**
 * The polynomial with the ground coefficient subtracted from its constant term.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial with the ground coefficient subtracted from its constant term.
 * @see SymPy `sympy.polys.densearith.dup_sub_ground`
 * @example
 * ```ts
 * import { ZZ, dupSubGround } from '@symjs/symjs';
 *
 * dupSubGround([1, 2, 3, 4], 4, ZZ); // => [1, 2, 3, 0]
 * ```
 */
export function dupSubGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return term(f, dmpGround(c, 0 - 1), 0, 0, K, true); }

/**
 * The polynomial scaled by a ground coefficient.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial scaled by a ground coefficient.
 * @see SymPy `sympy.polys.densearith.dup_mul_ground`
 * @example
 * ```ts
 * import { ZZ, dupMulGround } from '@symjs/symjs';
 *
 * dupMulGround([1, 2, -1], 3, ZZ); // => [3, 6, -3]
 * ```
 */
export function dupMulGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return mulGround(f, c, 0, K); }

/**
 * The polynomial obtained by dividing each coefficient by the ground divisor.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial obtained by dividing each coefficient by the ground divisor.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dup_quo_ground`
 * @example
 * ```ts
 * import { ZZ, dupQuoGround } from '@symjs/symjs';
 *
 * dupQuoGround([3, 0, 2], 2, ZZ); // => [1, 0, 1]
 * ```
 */
export function dupQuoGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return quoGround(f, c, 0, K, false); }

/**
 * The polynomial obtained by exact division of every coefficient by the ground divisor.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial obtained by exact division of every coefficient by the ground divisor.
 * @throws RangeError when the divisor is zero.
 * @throws ExactQuotientFailed when the division leaves a nonzero remainder.
 * @see SymPy `sympy.polys.densearith.dup_exquo_ground`
 * @example
 * ```ts
 * import { QQ, dupExquoGround } from '@symjs/symjs';
 *
 * dupExquoGround([1, 0, 2], 2, QQ).map(c => QQ.toSympy(c)); // => [1/2, 0, 1]
 * ```
 */
export function dupExquoGround(f: DensePoly, c: unknown, K: Domain): unknown[] { return quoGround(f, c, 0, K, true); }

/**
 * The polynomial formed from the absolute values of its coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial formed from the absolute values of its coefficients.
 * @see SymPy `sympy.polys.densearith.dup_abs`
 * @example
 * ```ts
 * import { ZZ, dupAbs } from '@symjs/symjs';
 *
 * dupAbs([1, 0, -1], ZZ); // => [1, 0, 1]
 * ```
 */
export function dupAbs(f: DensePoly, K: Domain): unknown[] { return mapGround(f, 0, (c) => absolute(c, K)); }

/**
 * The additive inverse of the polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The additive inverse of the polynomial.
 * @see SymPy `sympy.polys.densearith.dup_neg`
 * @example
 * ```ts
 * import { ZZ, dupNeg } from '@symjs/symjs';
 *
 * dupNeg([1, 0, -1], ZZ); // => [-1, 0, 1]
 * ```
 */
export function dupNeg(f: DensePoly, K: Domain): unknown[] { return mapGround(f, 0, (c) => domainNeg(K, c)); }

/**
 * The sum of the polynomials.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the polynomials.
 * @see SymPy `sympy.polys.densearith.dup_add`
 * @example
 * ```ts
 * import { ZZ, dupAdd } from '@symjs/symjs';
 *
 * dupAdd([1, 0, -1], [1, -2], ZZ); // => [1, 1, -3]
 * ```
 */
export function dupAdd(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return [...list(sum(f, g, 0, K))]; }

/**
 * The difference of the polynomials.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The difference of the polynomials.
 * @see SymPy `sympy.polys.densearith.dup_sub`
 * @example
 * ```ts
 * import { ZZ, dupSub } from '@symjs/symjs';
 *
 * dupSub([1, 0, -1], [1, -2], ZZ); // => [1, -1, 1]
 * ```
 */
export function dupSub(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return [...list(sum(f, g, 0, K, true))]; }

/**
 * The product of the polynomials.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The product of the polynomials.
 * @see SymPy `sympy.polys.densearith.dup_mul`
 * @example
 * ```ts
 * import { ZZ, dupMul } from '@symjs/symjs';
 *
 * dupMul([1, -2], [1, 2], ZZ); // => [1, 0, -4]
 * ```
 */
export function dupMul(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return [...list(product(f, g, 0, K))]; }

/**
 * The polynomial `f + g*h`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param h - Third polynomial operand.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial `f + g*h`.
 * @see SymPy `sympy.polys.densearith.dup_add_mul`
 * @example
 * ```ts
 * import { ZZ, dupAddMul } from '@symjs/symjs';
 *
 * dupAddMul([1, 0, -1], [1, -2], [1, 2], ZZ); // => [2, 0, -5]
 * ```
 */
export function dupAddMul(f: DensePoly, g: DensePoly, h: DensePoly, K: Domain): unknown[] { return [...list(sum(f, product(g, h, 0, K), 0, K))]; }

/**
 * The polynomial `f - g*h`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param h - Third polynomial operand.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial `f - g*h`.
 * @see SymPy `sympy.polys.densearith.dup_sub_mul`
 * @example
 * ```ts
 * import { ZZ, dupSubMul } from '@symjs/symjs';
 *
 * dupSubMul([1, 0, -1], [1, -2], [1, 2], ZZ); // => [3]
 * ```
 */
export function dupSubMul(f: DensePoly, g: DensePoly, h: DensePoly, K: Domain): unknown[] { return [...list(sum(f, product(g, h, 0, K), 0, K, true))]; }

/**
 * The square of the polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The square of the polynomial.
 * @see SymPy `sympy.polys.densearith.dup_sqr`
 * @example
 * ```ts
 * import { ZZ, dupSqr } from '@symjs/symjs';
 *
 * dupSqr([1, 0, 1], ZZ); // => [1, 0, 2, 0, 1]
 * ```
 */
export function dupSqr(f: DensePoly, K: Domain): unknown[] { return [...list(product(f, f, 0, K))]; }

/**
 * The polynomial raised to the nonnegative integer power `n`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param n - Exponent or degree.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial raised to the nonnegative integer power `n`.
 * @throws RangeError when the exponent is negative.
 * @see SymPy `sympy.polys.densearith.dup_pow`
 * @example
 * ```ts
 * import { ZZ, dupPow } from '@symjs/symjs';
 *
 * dupPow([1, -2], 3, ZZ); // => [1, -6, 12, -8]
 * ```
 */
export function dupPow(f: DensePoly, n: number, K: Domain): unknown[] { return [...list(power(f, integer(n), 0, K))]; }

/**
 * The pseudo-quotient and pseudo-remainder in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dup_pdiv`
 * @remarks SymPy returns `([2, 4], [20])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupPdiv } from '@symjs/symjs';
 *
 * dupPdiv([1, 0, 1], [2, -4], ZZ); // => [[2, 4], [20]]
 * ```
 */
export function dupPdiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, false, true); }

/**
 * The pseudo-remainder in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The pseudo-remainder in the main variable.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dup_prem`
 * @example
 * ```ts
 * import { ZZ, dupPrem } from '@symjs/symjs';
 *
 * dupPrem([1, 0, 1], [2, -4], ZZ); // => [20]
 * ```
 */
export function dupPrem(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, false, true)[1]; }

/**
 * The pseudo-quotient in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The pseudo-quotient in the main variable.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dup_pquo`
 * @example
 * ```ts
 * import { ZZ, dupPquo } from '@symjs/symjs';
 *
 * dupPquo([1, 0, -1], [2, -2], ZZ); // => [2, 2]
 * dupPquo([1, 0, 1], [2, -4], ZZ); // => [2, 4]
 * ```
 */
export function dupPquo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, false, true)[0]; }

/**
 * The exact pseudo-quotient in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The exact pseudo-quotient in the main variable.
 * @throws RangeError when the divisor is zero.
 * @throws ExactQuotientFailed when the division leaves a nonzero remainder.
 * @see SymPy `sympy.polys.densearith.dup_pexquo`
 * @example
 * ```ts
 * import { ZZ, dupPexquo } from '@symjs/symjs';
 *
 * dupPexquo([1, 0, -1], [2, -2], ZZ); // => [2, 2]
 * ```
 */
export function dupPexquo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return exactQuotient(divide(f, g, 0, K, false, true), 0); }

/**
 * The quotient and remainder using division in the coefficient ring.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder using division in the coefficient ring.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dup_rr_div`
 * @remarks SymPy returns `([], [1, 0, 1])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupRrDiv } from '@symjs/symjs';
 *
 * dupRrDiv([1, 0, 1], [2, -4], ZZ); // => [[], [1, 0, 1]]
 * ```
 */
export function dupRrDiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, false); }

/**
 * The quotient and remainder using division in the coefficient field.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder using division in the coefficient field.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dup_ff_div`
 * @example
 * ```ts
 * import { QQ, dupFfDiv } from '@symjs/symjs';
 *
 * dupFfDiv([1, 0, 1], [2, -4], QQ)[0].map(c => QQ.toSympy(c)); // => [1/2, 1]
 * ```
 */
export function dupFfDiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, true); }

/**
 * The quotient and remainder of polynomial division.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder of polynomial division.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dup_div`
 * @remarks SymPy returns `([], [1, 0, 1])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupDiv } from '@symjs/symjs';
 *
 * dupDiv([1, 0, 1], [2, -4], ZZ); // => [[], [1, 0, 1]]
 * ```
 */
export function dupDiv(f: DensePoly, g: DensePoly, K: Domain): [unknown[], unknown[]] { return divide(f, g, 0, K, K.isField); }

/**
 * The remainder after dividing `f` by `g`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The remainder after dividing `f` by `g`.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dup_rem`
 * @example
 * ```ts
 * import { ZZ, dupRem } from '@symjs/symjs';
 *
 * dupRem([1, 0, 1], [2, -4], ZZ); // => [1, 0, 1]
 * ```
 */
export function dupRem(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, K.isField)[1]; }

/**
 * The quotient of polynomial division.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient of polynomial division.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dup_quo`
 * @example
 * ```ts
 * import { ZZ, dupQuo } from '@symjs/symjs';
 *
 * dupQuo([1, 0, 1], [2, -4], ZZ); // => []
 * ```
 */
export function dupQuo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return divide(f, g, 0, K, K.isField)[0]; }

/**
 * The exact polynomial quotient.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The exact polynomial quotient.
 * @throws RangeError when the divisor is zero.
 * @throws ExactQuotientFailed when the division leaves a nonzero remainder.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dup_exquo`
 * @example
 * ```ts
 * import { ZZ, dupExquo } from '@symjs/symjs';
 *
 * dupExquo([1, 0, -1], [1, -1], ZZ); // => [1, 1]
 * ```
 */
export function dupExquo(f: DensePoly, g: DensePoly, K: Domain): unknown[] { return exactQuotient(divide(f, g, 0, K, K.isField), 0); }

/**
 * The largest absolute value of the coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The largest absolute value of the coefficients.
 * @see SymPy `sympy.polys.densearith.dup_max_norm`
 * @example
 * ```ts
 * import { ZZ, dupMaxNorm } from '@symjs/symjs';
 *
 * dupMaxNorm([-1, 2, -3], ZZ); // => 3
 * ```
 */
export function dupMaxNorm(f: DensePoly, K: Domain): unknown { return norm(f, 0, K, 'max'); }

/**
 * The sum of the absolute values of the coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the absolute values of the coefficients.
 * @see SymPy `sympy.polys.densearith.dup_l1_norm`
 * @example
 * ```ts
 * import { ZZ, dupL1Norm } from '@symjs/symjs';
 *
 * dupL1Norm([2, -3, 0, 1], ZZ); // => 6
 * ```
 */
export function dupL1Norm(f: DensePoly, K: Domain): unknown { return norm(f, 0, K, 'l1'); }

/**
 * The sum of the squares of the coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the squares of the coefficients.
 * @see SymPy `sympy.polys.densearith.dup_l2_norm_squared`
 * @example
 * ```ts
 * import { ZZ, dupL2NormSquared } from '@symjs/symjs';
 *
 * dupL2NormSquared([2, -3, 0, 1], ZZ); // => 14
 * ```
 */
export function dupL2NormSquared(f: DensePoly, K: Domain): unknown { return norm(f, 0, K, 'l2'); }

/**
 * The sum of the polynomial and the term `c*x**i`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the monomial to add, subtract or multiply.
 * @param i - Exponent of the term in the main variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the polynomial and the term `c*x**i`.
 * @see SymPy `sympy.polys.densearith.dmp_add_term`
 * @example
 * ```ts
 * import { ZZ, dmpAddTerm } from '@symjs/symjs';
 *
 * dmpAddTerm([[1, 0], [1]], [2], 2, 1, ZZ); // => [[2], [1, 0], [1]]
 * ```
 */
export function dmpAddTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] { return term(f, c, integer(i), integer(u), K); }

/**
 * The difference between the polynomial and the term `c*x**i`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the monomial to add, subtract or multiply.
 * @param i - Exponent of the term in the main variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The difference between the polynomial and the term `c*x**i`.
 * @see SymPy `sympy.polys.densearith.dmp_sub_term`
 * @example
 * ```ts
 * import { ZZ, dmpSubTerm } from '@symjs/symjs';
 *
 * dmpSubTerm([[2], [1, 0], [1]], [2], 2, 1, ZZ); // => [[1, 0], [1]]
 * ```
 */
export function dmpSubTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] { return term(f, c, integer(i), integer(u), K, true); }

/**
 * The product of the polynomial and the term `c*x**i`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the monomial to add, subtract or multiply.
 * @param i - Exponent of the term in the main variable.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The product of the polynomial and the term `c*x**i`.
 * @see SymPy `sympy.polys.densearith.dmp_mul_term`
 * @example
 * ```ts
 * import { ZZ, dmpMulTerm } from '@symjs/symjs';
 *
 * dmpMulTerm([[1, 0], [1], []], [3, 0], 2, 1, ZZ); // => [[3, 0, 0], [3, 0], [], [], []]
 * ```
 */
export function dmpMulTerm(f: DensePoly, c: unknown, i: number, u: number, K: Domain): unknown[] { return mulTerm(f, c, integer(i), integer(u), K); }

/**
 * The polynomial with the ground coefficient added to its constant term.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial with the ground coefficient added to its constant term.
 * @see SymPy `sympy.polys.densearith.dmp_add_ground`
 * @example
 * ```ts
 * import { ZZ, dmpAddGround } from '@symjs/symjs';
 *
 * dmpAddGround([[1], [2], [3], [4]], 4, 1, ZZ); // => [[1], [2], [3], [8]]
 * ```
 */
export function dmpAddGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return term(f, dmpGround(c, integer(u) - 1), 0, integer(u), K); }

/**
 * The polynomial with the ground coefficient subtracted from its constant term.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial with the ground coefficient subtracted from its constant term.
 * @see SymPy `sympy.polys.densearith.dmp_sub_ground`
 * @example
 * ```ts
 * import { ZZ, dmpSubGround } from '@symjs/symjs';
 *
 * dmpSubGround([[1], [2], [3], [4]], 4, 1, ZZ); // => [[1], [2], [3], []]
 * ```
 */
export function dmpSubGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return term(f, dmpGround(c, integer(u) - 1), 0, integer(u), K, true); }

/**
 * The polynomial scaled by a ground coefficient.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial scaled by a ground coefficient.
 * @see SymPy `sympy.polys.densearith.dmp_mul_ground`
 * @example
 * ```ts
 * import { ZZ, dmpMulGround } from '@symjs/symjs';
 *
 * dmpMulGround([[2], [2, 0]], 3, 1, ZZ); // => [[6], [6, 0]]
 * ```
 */
export function dmpMulGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return mulGround(f, c, integer(u), K); }

/**
 * The polynomial obtained by dividing each coefficient by the ground divisor.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial obtained by dividing each coefficient by the ground divisor.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dmp_quo_ground`
 * @example
 * ```ts
 * import { ZZ, dmpQuoGround } from '@symjs/symjs';
 *
 * dmpQuoGround([[2, 0], [3], []], 2, 1, ZZ); // => [[1, 0], [1], []]
 * ```
 */
export function dmpQuoGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return quoGround(f, c, integer(u), K, false); }

/**
 * The polynomial obtained by exact division of every coefficient by the ground divisor.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial obtained by exact division of every coefficient by the ground divisor.
 * @throws RangeError when the divisor is zero.
 * @throws ExactQuotientFailed when the division leaves a nonzero remainder.
 * @see SymPy `sympy.polys.densearith.dmp_exquo_ground`
 * @example
 * ```ts
 * import { QQ, dmpExquoGround } from '@symjs/symjs';
 *
 * (dmpExquoGround([[1, 0], [2], []], 2, 1, QQ)[0] as unknown[]).map(c => QQ.toSympy(c)); // => [1/2, 0]
 * ```
 */
export function dmpExquoGround(f: DensePoly, c: unknown, u: number, K: Domain): unknown[] { return quoGround(f, c, integer(u), K, true); }

/**
 * The polynomial formed from the absolute values of its coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial formed from the absolute values of its coefficients.
 * @see SymPy `sympy.polys.densearith.dmp_abs`
 * @example
 * ```ts
 * import { ZZ, dmpAbs } from '@symjs/symjs';
 *
 * dmpAbs([[1, 0], [-1], []], 1, ZZ); // => [[1, 0], [1], []]
 * ```
 */
export function dmpAbs(f: DensePoly, u: number, K: Domain): unknown[] { return mapGround(f, integer(u), (c) => absolute(c, K)); }

/**
 * The additive inverse of the polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The additive inverse of the polynomial.
 * @see SymPy `sympy.polys.densearith.dmp_neg`
 * @example
 * ```ts
 * import { ZZ, dmpNeg } from '@symjs/symjs';
 *
 * dmpNeg([[1, 0], [-1], []], 1, ZZ); // => [[-1, 0], [1], []]
 * ```
 */
export function dmpNeg(f: DensePoly, u: number, K: Domain): unknown[] { return mapGround(f, integer(u), (c) => domainNeg(K, c)); }

/**
 * The sum of the polynomials.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the polynomials.
 * @see SymPy `sympy.polys.densearith.dmp_add`
 * @example
 * ```ts
 * import { ZZ, dmpAdd } from '@symjs/symjs';
 *
 * dmpAdd([[1], [], [1, 0]], [[1, 0], [1], []], 1, ZZ); // => [[1, 1], [1], [1, 0]]
 * ```
 */
export function dmpAdd(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, g, integer(u), K))]; }

/**
 * The difference of the polynomials.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The difference of the polynomials.
 * @see SymPy `sympy.polys.densearith.dmp_sub`
 * @example
 * ```ts
 * import { ZZ, dmpSub } from '@symjs/symjs';
 *
 * dmpSub([[1], [], [1, 0]], [[1, 0], [1], []], 1, ZZ); // => [[-1, 1], [-1], [1, 0]]
 * ```
 */
export function dmpSub(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, g, integer(u), K, true))]; }

/**
 * The product of the polynomials.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The product of the polynomials.
 * @see SymPy `sympy.polys.densearith.dmp_mul`
 * @example
 * ```ts
 * import { ZZ, dmpMul } from '@symjs/symjs';
 *
 * dmpMul([[1, 0], [1]], [[1], []], 1, ZZ); // => [[1, 0], [1], []]
 * ```
 */
export function dmpMul(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return [...list(product(f, g, integer(u), K))]; }

/**
 * The polynomial `f + g*h`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param h - Third polynomial operand.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial `f + g*h`.
 * @see SymPy `sympy.polys.densearith.dmp_add_mul`
 * @example
 * ```ts
 * import { ZZ, dmpAddMul } from '@symjs/symjs';
 *
 * dmpAddMul([[1], [], [1, 0]], [[1], []], [[1], [2]], 1, ZZ); // => [[2], [2], [1, 0]]
 * ```
 */
export function dmpAddMul(f: DensePoly, g: DensePoly, h: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, product(g, h, integer(u), K), integer(u), K))]; }

/**
 * The polynomial `f - g*h`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param h - Third polynomial operand.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial `f - g*h`.
 * @see SymPy `sympy.polys.densearith.dmp_sub_mul`
 * @example
 * ```ts
 * import { ZZ, dmpSubMul } from '@symjs/symjs';
 *
 * dmpSubMul([[1], [], [1, 0]], [[1], []], [[1], [2]], 1, ZZ); // => [[-2], [1, 0]]
 * ```
 */
export function dmpSubMul(f: DensePoly, g: DensePoly, h: DensePoly, u: number, K: Domain): unknown[] { return [...list(sum(f, product(g, h, integer(u), K), integer(u), K, true))]; }

/**
 * The square of the polynomial.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The square of the polynomial.
 * @see SymPy `sympy.polys.densearith.dmp_sqr`
 * @example
 * ```ts
 * import { ZZ, dmpSqr } from '@symjs/symjs';
 *
 * dmpSqr([[1], [1, 0], [1, 0, 0]], 1, ZZ); // => [[1], [2, 0], [3, 0, 0], [2, 0, 0, 0], [1, 0, 0, 0, 0]]
 * ```
 */
export function dmpSqr(f: DensePoly, u: number, K: Domain): unknown[] { return [...list(product(f, f, integer(u), K))]; }

/**
 * The polynomial raised to the nonnegative integer power `n`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param n - Exponent or degree.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The polynomial raised to the nonnegative integer power `n`.
 * @throws RangeError when the exponent is negative.
 * @see SymPy `sympy.polys.densearith.dmp_pow`
 * @example
 * ```ts
 * import { ZZ, dmpPow } from '@symjs/symjs';
 *
 * dmpPow([[1, 0], [1]], 3, 1, ZZ); // => [[1, 0, 0, 0], [3, 0, 0], [3, 0], [1]]
 * ```
 */
export function dmpPow(f: DensePoly, n: number, u: number, K: Domain): unknown[] { return [...list(power(f, integer(n), integer(u), K))]; }

/**
 * The pseudo-quotient and pseudo-remainder in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dmp_pdiv`
 * @remarks SymPy returns `([[2], [2, -2]], [[-4, 4]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpPdiv } from '@symjs/symjs';
 *
 * dmpPdiv([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[[2], [2, -2]], [[-4, 4]]]
 * ```
 */
export function dmpPdiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, false, true); }

/**
 * The pseudo-remainder in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The pseudo-remainder in the main variable.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dmp_prem`
 * @example
 * ```ts
 * import { ZZ, dmpPrem } from '@symjs/symjs';
 *
 * dmpPrem([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[-4, 4]]
 * ```
 */
export function dmpPrem(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, false, true)[1]; }

/**
 * The pseudo-quotient in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The pseudo-quotient in the main variable.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.densearith.dmp_pquo`
 * @example
 * ```ts
 * import { ZZ, dmpPquo } from '@symjs/symjs';
 *
 * dmpPquo([[1], [1, 0], []], [[2], [2, 0]], 1, ZZ); // => [[2], []]
 * dmpPquo([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[2], [2, -2]]
 * ```
 */
export function dmpPquo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, false, true)[0]; }

/**
 * The exact pseudo-quotient in the main variable.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The exact pseudo-quotient in the main variable.
 * @throws RangeError when the divisor is zero.
 * @throws ExactQuotientFailed when the division leaves a nonzero remainder.
 * @see SymPy `sympy.polys.densearith.dmp_pexquo`
 * @example
 * ```ts
 * import { ZZ, dmpPexquo } from '@symjs/symjs';
 *
 * dmpPexquo([[1], [1, 0], []], [[2], [2, 0]], 1, ZZ); // => [[2], []]
 * ```
 */
export function dmpPexquo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return exactQuotient(divide(f, g, integer(u), K, false, true), integer(u)); }

/**
 * The quotient and remainder using division in the coefficient ring.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder using division in the coefficient ring.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dmp_rr_div`
 * @remarks SymPy returns `([[]], [[1], [1, 0], []])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpRrDiv } from '@symjs/symjs';
 *
 * dmpRrDiv([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[[]], [[1], [1, 0], []]]
 * ```
 */
export function dmpRrDiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, false); }

/**
 * The quotient and remainder using division in the coefficient field.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder using division in the coefficient field.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dmp_ff_div`
 * @example
 * ```ts
 * import { QQ, dmpFfDiv } from '@symjs/symjs';
 *
 * (dmpFfDiv([[1], [1, 0], []], [[2], [2]], 1, QQ)[0][0] as unknown[]).map(c => QQ.toSympy(c)); // => [1/2]
 * ```
 */
export function dmpFfDiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, true); }

/**
 * The quotient and remainder of polynomial division.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient and remainder of polynomial division.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dmp_div`
 * @remarks SymPy returns `([[]], [[1], [1, 0], []])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpDiv } from '@symjs/symjs';
 *
 * dmpDiv([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[[]], [[1], [1, 0], []]]
 * ```
 */
export function dmpDiv(f: DensePoly, g: DensePoly, u: number, K: Domain): [unknown[], unknown[]] { return divide(f, g, integer(u), K, K.isField); }

/**
 * The remainder after dividing `f` by `g`.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The remainder after dividing `f` by `g`.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dmp_rem`
 * @example
 * ```ts
 * import { ZZ, dmpRem } from '@symjs/symjs';
 *
 * dmpRem([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[1], [1, 0], []]
 * ```
 */
export function dmpRem(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, K.isField)[1]; }

/**
 * The quotient of polynomial division.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The quotient of polynomial division.
 * @throws RangeError when the divisor is zero.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dmp_quo`
 * @example
 * ```ts
 * import { ZZ, dmpQuo } from '@symjs/symjs';
 *
 * dmpQuo([[1], [1, 0], []], [[2], [2]], 1, ZZ); // => [[]]
 * ```
 */
export function dmpQuo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return divide(f, g, integer(u), K, K.isField)[0]; }

/**
 * The exact polynomial quotient.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param g - Second polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The exact polynomial quotient.
 * @throws RangeError when the divisor is zero.
 * @throws ExactQuotientFailed when the division leaves a nonzero remainder.
 * @throws PolynomialDivisionFailed when inexact coefficient arithmetic prevents a reduction in degree.
 * @see SymPy `sympy.polys.densearith.dmp_exquo`
 * @example
 * ```ts
 * import { ZZ, dmpExquo } from '@symjs/symjs';
 *
 * dmpExquo([[1], [1, 0], []], [[1], [1, 0]], 1, ZZ); // => [[1], []]
 * ```
 */
export function dmpExquo(f: DensePoly, g: DensePoly, u: number, K: Domain): unknown[] { return exactQuotient(divide(f, g, integer(u), K, K.isField), integer(u)); }

/**
 * The largest absolute value of the coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The largest absolute value of the coefficients.
 * @see SymPy `sympy.polys.densearith.dmp_max_norm`
 * @example
 * ```ts
 * import { ZZ, dmpMaxNorm } from '@symjs/symjs';
 *
 * dmpMaxNorm([[2, -1], [-3]], 1, ZZ); // => 3
 * ```
 */
export function dmpMaxNorm(f: DensePoly, u: number, K: Domain): unknown { return norm(f, integer(u), K, 'max'); }

/**
 * The sum of the absolute values of the coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the absolute values of the coefficients.
 * @see SymPy `sympy.polys.densearith.dmp_l1_norm`
 * @example
 * ```ts
 * import { ZZ, dmpL1Norm } from '@symjs/symjs';
 *
 * dmpL1Norm([[2, -1], [-3]], 1, ZZ); // => 6
 * ```
 */
export function dmpL1Norm(f: DensePoly, u: number, K: Domain): unknown { return norm(f, integer(u), K, 'l1'); }

/**
 * The sum of the squares of the coefficients.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The sum of the squares of the coefficients.
 * @see SymPy `sympy.polys.densearith.dmp_l2_norm_squared`
 * @example
 * ```ts
 * import { ZZ, dmpL2NormSquared } from '@symjs/symjs';
 *
 * dmpL2NormSquared([[2, -1], [-3]], 1, ZZ); // => 14
 * ```
 */
export function dmpL2NormSquared(f: DensePoly, u: number, K: Domain): unknown { return norm(f, integer(u), K, 'l2'); }
