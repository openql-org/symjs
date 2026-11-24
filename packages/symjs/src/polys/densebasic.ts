// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/densebasic.py), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Basic tools for dense recursive polynomials in K[x] or K[X] (SymPy
 * sympy.polys.densebasic). A univariate polynomial (dup) is the list of its
 * coefficients, leading first; a polynomial in u + 1 variables (dmp) is the
 * list of its coefficients in the first variable, each a dmp in u variables.
 * The zero polynomial in u + 1 variables is u nested empty lists.
 *
 * The functions keep SymPy's names (camelCase) and arguments. Coefficients
 * are domain elements of any type (bigints, numbers, PythonMPQ, rational
 * expressions, ...); their zero test and comparison follow Python's truth
 * value and equality.
 */

import { InvariantError } from '../core/errors';
import { at, first } from '../core/guard';
import { Expr, Float, Rational } from '../core/nodes';
import { gcd as igcd } from '../core/numbers';
import { type Domain, domainArith, groundRational, isDomainElement } from './domains';
import { monomialKey, compareMonomialKeys, type MonomialOrdering } from './orderings';

/** A dense recursive polynomial: nested coefficient lists. */
export type DensePoly = readonly unknown[];
/** A monomial (exponent tuple). */
export type Monom = readonly number[];
/** A dict of terms: monomial (or a plain exponent for univariate raw dicts) to coefficient. */
export type TermDict = ReadonlyMap<Monom | number, unknown>;

/** SymPy's -inf degree of the zero polynomial. */
const ninf = -Infinity;

// ---------------------------------------------------------------------------
// coefficients (Python truth value and equality)
// ---------------------------------------------------------------------------

/**
 * Test a ground coefficient for zero or a nested coefficient list for emptiness.
 *
 * @param c - Coefficient of the term.
 * @returns Whether the coefficient is zero or the list is empty.
 */
export function groundIsZero(c: unknown): boolean {
  if (Array.isArray(c)) return c.length === 0;
  if (typeof c === 'number') return c === 0;
  if (typeof c === 'bigint') return c === 0n;
  if (c instanceof Rational || c instanceof Float) return c.isZero;
  if (c === null || c === undefined || c === false) return true;
  // domain elements (PythonMPQ, ModularInteger, Gaussian elements, ANP, Expression) have an isZero getter
  return typeof c === 'object' && !(c instanceof Expr) && 'isZero' in c && c.isZero === true;
}

/**
 * Compare ground coefficients by value, including across numeric representations.
 *
 * @param a - First operand.
 * @param b - Second operand.
 * @returns Whether the two coefficients are equal.
 */
export function groundEquals(a: unknown, b: unknown): boolean {
  const [ra, rb] = [groundRational(a), groundRational(b)];
  if (ra !== undefined && rb !== undefined) return ra[0] * rb[1] === rb[0] * ra[1];
  if (a instanceof Expr && b instanceof Expr) return a.key === b.key;
  if (isDomainElement(a)) return a.equals(b);
  return a === b;
}

const nz = (c: unknown): boolean => !groundIsZero(c);

/** A nested list of a dense polynomial. */
function asList(f: unknown): DensePoly {
  if (!Array.isArray(f)) throw new InvariantError('a dense polynomial level is not a list');
  return f as DensePoly;
}

const int = (n: unknown): number => {
  const r = groundRational(n);
  if (r === undefined || r[1] !== 1n) throw new TypeError(`expected an integer, got ${String(n)}`);
  return Number(r[0]);
};

const monomKey = (m: Monom): string => m.join(',');

/** The entries of a term dict with monomial tuples (a plain exponent k is the monomial (k,)). */
const monomEntries = (f: TermDict): [Monom, unknown][] => [...f].map(([m, c]) => [typeof m === 'number' ? [m] : m.map(int), c]);

// ---------------------------------------------------------------------------
// leading and trailing coefficients, degrees
// ---------------------------------------------------------------------------

/**
 * The leading coefficient of f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The leading coefficient of f.
 * @see SymPy `sympy.polys.densebasic.poly_LC`
 * @see SymPy `sympy.polys.densebasic.dup_LC`
 * @see SymPy `sympy.polys.densebasic.dmp_LC`
 * @example
 * ```ts
 * import { ZZ, dmpLC } from '@symjs/symjs';
 *
 * dmpLC([], ZZ); // => 0
 * dmpLC([1, 2, 3], ZZ); // => 1
 * ```
 */
export function polyLC(f: DensePoly, K: Domain): unknown {
  return f.length ? f[0] : K.zero;
}

/**
 * The trailing coefficient of f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The trailing coefficient of f.
 * @see SymPy `sympy.polys.densebasic.poly_TC`
 * @see SymPy `sympy.polys.densebasic.dup_TC`
 * @see SymPy `sympy.polys.densebasic.dmp_TC`
 * @example
 * ```ts
 * import { ZZ, dmpTC } from '@symjs/symjs';
 *
 * dmpTC([], ZZ); // => 0
 * dmpTC([1, 2, 3], ZZ); // => 3
 * ```
 */
export function polyTC(f: DensePoly, K: Domain): unknown {
  return f.length ? f[f.length - 1] : K.zero;
}

export { polyLC as dupLC, polyLC as dmpLC, polyTC as dupTC, polyTC as dmpTC };

/**
 * The ground leading coefficient.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The ground leading coefficient.
 * @see SymPy `sympy.polys.densebasic.dmp_ground_LC`
 * @example
 * ```ts
 * import { ZZ, dmpGroundLC } from '@symjs/symjs';
 *
 * dmpGroundLC([[[1], [2, 3]]], 2, ZZ); // => 1
 * ```
 */
export function dmpGroundLC(fIn: DensePoly, uIn: number, K: Domain): unknown {
  let [f, u] = [fIn, int(uIn)];
  for (; u; u--) f = asList(polyLC(f, K));
  return polyLC(f, K);
}

/**
 * The ground trailing coefficient.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The ground trailing coefficient.
 * @see SymPy `sympy.polys.densebasic.dmp_ground_TC`
 * @example
 * ```ts
 * import { ZZ, dmpGroundTC } from '@symjs/symjs';
 *
 * dmpGroundTC([[[1], [2, 3]]], 2, ZZ); // => 3
 * ```
 */
export function dmpGroundTC(fIn: DensePoly, uIn: number, K: Domain): unknown {
  let [f, u] = [fIn, int(uIn)];
  for (; u; u--) f = asList(polyTC(f, K));
  return polyTC(f, K);
}

/**
 * The leading term [monomial, coefficient].
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The leading term [monomial, coefficient].
 * @see SymPy `sympy.polys.densebasic.dmp_true_LT`
 * @remarks SymPy returns `((2, 0), 4)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpTrueLT } from '@symjs/symjs';
 *
 * dmpTrueLT([[4], [2, 0], [3, 0, 0]], 1, ZZ); // => [[2, 0], 4]
 * ```
 */
export function dmpTrueLT(fIn: DensePoly, uIn: number, K: Domain): [number[], unknown] {
  const monom: number[] = [];
  let [f, u] = [fIn, int(uIn)];
  for (; u; u--) {
    monom.push(f.length - 1);
    f = asList(f[0]);
  }
  monom.push(f.length ? f.length - 1 : 0);
  return [monom, polyLC(f, K)];
}

/**
 * The degree of f (-Infinity for zero; SymPy dup_degree).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @returns The degree of f (-Infinity for zero.
 * @see SymPy `sympy.polys.densebasic.dup_degree`
 * @example
 * ```ts
 * import { dupDegree } from '@symjs/symjs';
 *
 * dupDegree([1, 2, 0, 3]); // => 3
 * ```
 */
export function dupDegree(f: DensePoly): number {
  return f.length ? f.length - 1 : ninf;
}

/**
 * The degree of f in x_0 (-Infinity for zero; SymPy dmp_degree).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @returns The degree of f in x_0 (-Infinity for zero.
 * @see SymPy `sympy.polys.densebasic.dmp_degree`
 * @remarks SymPy prints the degree of zero as `-inf`.
 * @example
 * ```ts
 * import { dmpDegree } from '@symjs/symjs';
 *
 * dmpDegree([[[]]], 2); // => -Infinity
 * dmpDegree([[2], [1, 2, 3]], 1); // => 1
 * ```
 */
export function dmpDegree(f: DensePoly, u: number): number {
  return dmpZeroP(f, u) ? ninf : f.length - 1;
}

function recDegreeIn(g: DensePoly, v: number, i: number, j: number): number {
  if (i === j) return dmpDegree(g, v);
  return Math.max(...g.map((c) => recDegreeIn(asList(c), v - 1, i + 1, j)));
}

/**
 * The degree of f in x_j.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param jIn - Index of the polynomial variable.
 * @param uIn - Number of variables minus one.
 * @returns The degree of f in x_j.
 * @throws RangeError when a generator index is outside the allowed range.
 * @see SymPy `sympy.polys.densebasic.dmp_degree_in`
 * @example
 * ```ts
 * import { dmpDegreeIn } from '@symjs/symjs';
 *
 * dmpDegreeIn([[2], [1, 2, 3]], 0, 1); // => 1
 * dmpDegreeIn([[2], [1, 2, 3]], 1, 1); // => 2
 * ```
 */
export function dmpDegreeIn(f: DensePoly, jIn: number, uIn: number): number {
  const [j, u] = [int(jIn), int(uIn)];
  if (!j) return dmpDegree(f, u);
  if (j < 0 || j > u) throw new RangeError(`0 <= j <= ${u} expected, got ${j}`);
  return recDegreeIn(f, u, 0, j);
}

function recDegreeList(g: DensePoly, v: number, i: number, degs: number[]): void {
  degs[i] = Math.max(at(degs, i), dmpDegree(g, v));
  if (v > 0) for (const c of g) recDegreeList(asList(c), v - 1, i + 1, degs);
}

/**
 * The degrees in x_0, ..., x_u.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @returns The degrees in x_0, ..., x_u.
 * @see SymPy `sympy.polys.densebasic.dmp_degree_list`
 * @remarks SymPy returns `(1, 2)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { dmpDegreeList } from '@symjs/symjs';
 *
 * dmpDegreeList([[1], [1, 2, 3]], 1); // => [1, 2]
 * ```
 */
export function dmpDegreeList(f: DensePoly, uIn: number): number[] {
  const u = int(uIn);
  const degs = Array.from({ length: u + 1 }, () => ninf);
  recDegreeList(f, u, 0, degs);
  return degs;
}

// ---------------------------------------------------------------------------
// stripping, validation, copies
// ---------------------------------------------------------------------------

/**
 * Remove leading zeros.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dup_strip`
 * @example
 * ```ts
 * import { dupStrip } from '@symjs/symjs';
 *
 * dupStrip([0, 0, 1, 2, 3, 0]); // => [1, 2, 3, 0]
 * ```
 */
export function dupStrip(f: DensePoly): unknown[] {
  let i = 0;
  while (i < f.length && !nz(f[i])) i++;
  return f.slice(i);
}

/**
 * Remove leading zeros.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_strip`
 * @example
 * ```ts
 * import { dmpStrip } from '@symjs/symjs';
 *
 * dmpStrip([[], [0, 1, 2], [1]], 1); // => [[0, 1, 2], [1]]
 * ```
 */
export function dmpStrip(f: DensePoly, uIn: number): unknown[] {
  const u = int(uIn);
  if (!u) return dupStrip(f);
  if (dmpZeroP(f, u)) return [...f];
  let i = 0;
  while (i < f.length && dmpZeroP(asList(f[i]), u - 1)) i++;
  return i === f.length ? dmpZero(u) : f.slice(i);
}

function recValidate(g: unknown, i: number, K: Domain | null): Set<number> {
  if (!Array.isArray(g)) {
    if (K !== null && !K.ofType(g)) throw new TypeError(`${String(g)} is not of type ${K.toString()}`);
    return new Set([i - 1]);
  }
  if (!g.length) return new Set([i]);
  const levels = new Set<number>();
  for (const c of g) for (const l of recValidate(c, i + 1, K)) levels.add(l);
  return levels;
}

function recStrip(g: DensePoly, v: number): unknown[] {
  if (!v) return dupStrip(g);
  return dmpStrip(
    g.map((c) => recStrip(asList(c), v - 1)),
    v,
  );
}

/**
 * Check the structure of a dense polynomial and return [stripped f, u].
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Check the structure of a dense polynomial and return [stripped f, u].
 * @throws RangeError when the coefficient lists have inconsistent nesting.
 * @see SymPy `sympy.polys.densebasic.dmp_validate`
 * @remarks SymPy returns `([[1, 2], [1]], 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { dmpValidate } from '@symjs/symjs';
 *
 * dmpValidate([[], [0, 1, 2], [1]]); // => [[[1, 2], [1]], 1]
 * ```
 */
export function dmpValidate(f: DensePoly, K: Domain | null = null): [unknown[], number] {
  const levels = [...recValidate(f, 0, K)];
  if (levels.length !== 1) throw new RangeError('invalid data structure for a multivariate polynomial');
  const u = first(levels);
  return [recStrip(f, u), u];
}

/**
 * The coefficients in reverse order, stripped.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @returns The coefficients in reverse order, stripped.
 * @see SymPy `sympy.polys.densebasic.dup_reverse`
 * @example
 * ```ts
 * import { dupReverse } from '@symjs/symjs';
 *
 * dupReverse([1, 2, 3, 0]); // => [3, 2, 1]
 * ```
 */
export function dupReverse(f: DensePoly): unknown[] {
  return dupStrip([...f].reverse());
}

/**
 * A copy of f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @returns A copy of f.
 * @see SymPy `sympy.polys.densebasic.dup_copy`
 * @example
 * ```ts
 * import { dupCopy } from '@symjs/symjs';
 *
 * dupCopy([1, 2, 3, 0]); // => [1, 2, 3, 0]
 * ```
 */
export function dupCopy(f: DensePoly): unknown[] {
  return [...f];
}

/**
 * A deep copy of f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @returns A deep copy of f.
 * @see SymPy `sympy.polys.densebasic.dmp_copy`
 * @example
 * ```ts
 * import { dmpCopy } from '@symjs/symjs';
 *
 * dmpCopy([[1], [1, 2]], 1); // => [[1], [1, 2]]
 * ```
 */
export function dmpCopy(f: DensePoly, uIn: number): unknown[] {
  const u = int(uIn);
  if (!u) return [...f];
  return f.map((c) => dmpCopy(asList(c), u - 1));
}

/**
 * f as nested tuples.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dup_to_tuple`
 * @remarks SymPy returns `(1, 2, 3)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { dupToTuple } from '@symjs/symjs';
 *
 * dupToTuple([1, 2, 3]); // => [1, 2, 3]
 * ```
 */
export function dupToTuple(f: DensePoly): unknown[] {
  return [...f];
}

/**
 * f as nested tuples.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_to_tuple`
 * @remarks SymPy returns `((1,), (1, 2))` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { dmpToTuple } from '@symjs/symjs';
 *
 * dmpToTuple([[1], [1, 2]], 1); // => [[1], [1, 2]]
 * ```
 */
export function dmpToTuple(f: DensePoly, u: number): unknown[] {
  return dmpCopy(f, u);
}

/**
 * The coefficients normalized in K.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The coefficients normalized in K.
 * @see SymPy `sympy.polys.densebasic.dup_normal`
 * @example
 * ```ts
 * import { ZZ, dupNormal } from '@symjs/symjs';
 *
 * dupNormal([0, 1, 2, 3], ZZ); // => [1, 2, 3]
 * ```
 */
export function dupNormal(f: DensePoly, K: Domain): unknown[] {
  return dupStrip(f.map((c) => K.new(c)));
}

/**
 * The coefficients normalized in K.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The coefficients normalized in K.
 * @see SymPy `sympy.polys.densebasic.dmp_normal`
 * @example
 * ```ts
 * import { ZZ, dmpNormal } from '@symjs/symjs';
 *
 * dmpNormal([[], [0, 1, 2]], 1, ZZ); // => [[1, 2]]
 * ```
 */
export function dmpNormal(f: DensePoly, uIn: number, K: Domain): unknown[] {
  const u = int(uIn);
  if (!u) return dupNormal(f, K);
  return dmpStrip(
    f.map((c) => dmpNormal(asList(c), u - 1, K)),
    u,
  );
}

/**
 * Convert the coefficients from K0 to K1.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K0 - Source coefficient domain.
 * @param K1 - Target coefficient domain.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dup_convert`
 * @example
 * ```ts
 * import { QQ, ZZ, dupConvert } from '@symjs/symjs';
 *
 * dupConvert([1, 2], ZZ, QQ).map(c => QQ.toSympy(c)); // => [1, 2]
 * ```
 */
export function dupConvert(f: DensePoly, K0: Domain | null, K1: Domain): unknown[] {
  if (K0?.equals(K1) === true) return [...f];
  return dupStrip(f.map((c) => K1.convert(c, K0 ?? undefined)));
}

/**
 * Convert the coefficients from K0 to K1.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K0 - Source coefficient domain.
 * @param K1 - Target coefficient domain.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_convert`
 * @example
 * ```ts
 * import { QQ, ZZ, dmpConvert } from '@symjs/symjs';
 *
 * dmpConvert([1, 2], 0, ZZ, QQ).map(c => QQ.toSympy(c)); // => [1, 2]
 * ```
 */
export function dmpConvert(f: DensePoly, uIn: number, K0: Domain | null, K1: Domain): unknown[] {
  const u = int(uIn);
  if (!u) return dupConvert(f, K0, K1);
  if (K0?.equals(K1) === true) return [...f];
  return dmpStrip(
    f.map((c) => dmpConvert(asList(c), u - 1, K0, K1)),
    u,
  );
}

/**
 * Convert expression coefficients to K.
 *
 * @param f - Polynomial to operate on.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dup_from_sympy`
 * @example
 * ```ts
 * import { ZZ, dupFromSympy, ex } from '@symjs/symjs';
 *
 * dupFromSympy([ex`1`, ex`2`], ZZ); // => [1, 2]
 * ```
 */
export function dupFromSympy(f: readonly Expr[], K: Domain): unknown[] {
  return dupStrip(f.map((c) => K.convert(c)));
}

/**
 * Convert expression coefficients to K.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_from_sympy`
 * @example
 * ```ts
 * import { ZZ, dmpFromSympy } from '@symjs/symjs';
 *
 * dmpFromSympy([[1], [2]], 1, ZZ); // => [[1], [2]]
 * ```
 */
export function dmpFromSympy(f: DensePoly, uIn: number, K: Domain): unknown[] {
  const u = int(uIn);
  if (!u) return dupStrip(f.map((c) => K.convert(c)));
  return dmpStrip(
    f.map((c) => dmpFromSympy(asList(c), u - 1, K)),
    u,
  );
}

// ---------------------------------------------------------------------------
// coefficients by degree, zero, one and ground polynomials
// ---------------------------------------------------------------------------

/**
 * The coefficient of x**n.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param nIn - Requested exponent.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The coefficient of x**n.
 * @throws RangeError when the exponent is negative.
 * @see SymPy `sympy.polys.densebasic.dup_nth`
 * @example
 * ```ts
 * import { ZZ, dupNth } from '@symjs/symjs';
 *
 * dupNth([1, 2, 3], 0, ZZ); // => 3
 * dupNth([1, 2, 3], 4, ZZ); // => 0
 * ```
 */
export function dupNth(f: DensePoly, nIn: number, K: Domain): unknown {
  const n = int(nIn);
  if (n < 0) throw new RangeError(`'n' must be non-negative, got ${n}`);
  return n >= f.length ? K.zero : f[f.length - 1 - n];
}

/**
 * The coefficient of x_0**n, a dmp in u - 1 variables.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param nIn - Requested exponent.
 * @param uIn - Number of variables minus one.
 * @param _K - Coefficient domain for the polynomial arithmetic.
 * @returns The coefficient of x_0**n, a dmp in u - 1 variables.
 * @throws RangeError when the exponent is negative.
 * @see SymPy `sympy.polys.densebasic.dmp_nth`
 * @example
 * ```ts
 * import { ZZ, dmpNth } from '@symjs/symjs';
 *
 * dmpNth([[1], [2], [3]], 0, 1, ZZ); // => [3]
 * dmpNth([[1], [2], [3]], 4, 1, ZZ); // => []
 * ```
 */
export function dmpNth(f: DensePoly, nIn: number, uIn: number, _K: Domain): unknown {
  const [n, u] = [int(nIn), int(uIn)];
  if (n < 0) throw new RangeError(`'n' must be non-negative, got ${n}`);
  return n >= f.length ? dmpZero(u - 1) : f[dmpDegree(f, u) - n];
}

/**
 * The ground coefficient of x_0**N[0] ... x_u**N[u].
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param N - Exponent vector of the requested coefficient.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The ground coefficient of x_0**N[0] ... x_u**N[u].
 * @throws RangeError when the exponent is negative.
 * @see SymPy `sympy.polys.densebasic.dmp_ground_nth`
 * @example
 * ```ts
 * import { ZZ, dmpGroundNth } from '@symjs/symjs';
 *
 * dmpGroundNth([[1], [2, 3]], [0, 1], 1, ZZ); // => 2
 * ```
 */
export function dmpGroundNth(fIn: DensePoly, N: readonly number[], uIn: number, K: Domain): unknown {
  let f: unknown = fIn;
  let v = int(uIn);
  for (const nIn of N) {
    const n = int(nIn);
    const g = asList(f);
    if (n < 0) throw new RangeError(`'n' must be non-negative, got ${n}`);
    if (n >= g.length) return K.zero;
    const d = dmpDegree(g, v);
    f = at(g, (d === ninf ? -1 : d) - n);
    v -= 1;
  }
  return f;
}

/**
 * Test whether a dense polynomial is zero at the given nesting level.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @returns Whether the polynomial is zero.
 * @see SymPy `sympy.polys.densebasic.dmp_zero_p`
 * @example
 * ```ts
 * import { dmpZeroP } from '@symjs/symjs';
 *
 * dmpZeroP([[[[[]]]]], 4); // => True
 * dmpZeroP([[[[[1]]]]], 4); // => False
 * ```
 */
export function dmpZeroP(fIn: DensePoly, uIn: number): boolean {
  let [f, u] = [fIn, int(uIn)];
  for (; u; u--) {
    if (f.length !== 1) return false;
    f = asList(f[0]);
  }
  return f.length === 0;
}

/**
 * The zero polynomial in u + 1 variables.
 *
 * @param uIn - Number of variables minus one.
 * @returns The zero polynomial in u + 1 variables.
 * @see SymPy `sympy.polys.densebasic.dmp_zero`
 * @example
 * ```ts
 * import { dmpZero } from '@symjs/symjs';
 *
 * dmpZero(4); // => [[[[[]]]]]
 * ```
 */
export function dmpZero(uIn: number): unknown[] {
  let r: unknown[] = [];
  for (let i = 0; i < int(uIn); i++) r = [r];
  return r;
}

/**
 * Test whether a dense polynomial represents one.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Whether the polynomial is one.
 * @see SymPy `sympy.polys.densebasic.dmp_one_p`
 * @example
 * ```ts
 * import { ZZ, dmpOneP } from '@symjs/symjs';
 *
 * dmpOneP([[[1]]], 2, ZZ); // => True
 * ```
 */
export function dmpOneP(f: DensePoly, u: number, K: Domain): boolean {
  return dmpGroundP(f, K.one, u);
}

/**
 * The one polynomial.
 *
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The one polynomial.
 * @see SymPy `sympy.polys.densebasic.dmp_one`
 * @example
 * ```ts
 * import { ZZ, dmpOne } from '@symjs/symjs';
 *
 * dmpOne(2, ZZ); // => [[[1]]]
 * ```
 */
export function dmpOne(u: number, K: Domain): unknown {
  return dmpGround(K.one, u);
}

/**
 * Test whether a dense polynomial equals the given constant. Use `null` to accept any constant.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param c - Coefficient of the term.
 * @param uIn - Number of variables minus one.
 * @returns Whether the polynomial meets the constant test.
 * @see SymPy `sympy.polys.densebasic.dmp_ground_p`
 * @example
 * ```ts
 * import { dmpGroundP } from '@symjs/symjs';
 *
 * dmpGroundP([[[3]]], 3, 2); // => True
 * dmpGroundP([[[4]]], null, 2); // => True
 * ```
 */
export function dmpGroundP(fIn: DensePoly, c: unknown, uIn: number): boolean {
  const none = c === null || c === undefined;
  if (!none && !nz(c)) return dmpZeroP(fIn, uIn);
  let [f, u] = [fIn, int(uIn)];
  for (; u; u--) {
    if (f.length !== 1) return false;
    f = asList(f[0]);
  }
  return none ? f.length <= 1 : f.length === 1 && groundEquals(f[0], c);
}

/**
 * The constant c as a polynomial in u + 1 variables (c itself for u = -1; SymPy dmp_ground).
 *
 * @param cIn - Coefficient of the term.
 * @param uIn - Number of variables minus one.
 * @returns The constant c as a polynomial in u + 1 variables (c itself for u = -1.
 * @see SymPy `sympy.polys.densebasic.dmp_ground`
 * @example
 * ```ts
 * import { dmpGround } from '@symjs/symjs';
 *
 * dmpGround(3, 5); // => [[[[[[3]]]]]]
 * dmpGround(1, -1); // => 1
 * ```
 */
export function dmpGround(cIn: unknown, uIn: number): unknown {
  const u = int(uIn);
  if (!nz(cIn)) return dmpZero(u);
  let c: unknown = cIn;
  for (let i = 0; i < u + 1; i++) c = [c];
  return c;
}

/**
 * n zero polynomials (n zeros of K for u < 0; SymPy dmp_zeros).
 *
 * @param nIn - Number of entries to produce.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_zeros`
 * @example
 * ```ts
 * import { ZZ, dmpZeros } from '@symjs/symjs';
 *
 * dmpZeros(3, 2, ZZ); // => [[[[]]], [[[]]], [[[]]]]
 * dmpZeros(3, -1, ZZ); // => [0, 0, 0]
 * ```
 */
export function dmpZeros(nIn: number, uIn: number, K: Domain): unknown[] {
  const [n, u] = [int(nIn), int(uIn)];
  return Array.from({ length: n }, () => (u < 0 ? K.zero : dmpZero(u)));
}

/**
 * n copies of the constant c.
 *
 * @param c - Coefficient of the term.
 * @param nIn - Number of entries to produce.
 * @param uIn - Number of variables minus one.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_grounds`
 * @example
 * ```ts
 * import { dmpGrounds } from '@symjs/symjs';
 *
 * dmpGrounds(4, 3, 2); // => [[[[4]]], [[[4]]], [[[4]]]]
 * dmpGrounds(4, 3, -1); // => [4, 4, 4]
 * ```
 */
export function dmpGrounds(c: unknown, nIn: number, uIn: number): unknown[] {
  const [n, u] = [int(nIn), int(uIn)];
  return Array.from({ length: n }, () => (u < 0 ? c : dmpGround(c, u)));
}

/**
 * Is the ground leading coefficient negative?
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Whether the ground leading coefficient negative.
 * @see SymPy `sympy.polys.densebasic.dmp_negative_p`
 * @example
 * ```ts
 * import { ZZ, dmpNegativeP } from '@symjs/symjs';
 *
 * dmpNegativeP([[1], [-1]], 1, ZZ); // => False
 * dmpNegativeP([[-1], [1]], 1, ZZ); // => True
 * ```
 */
export function dmpNegativeP(f: DensePoly, u: number, K: Domain): boolean {
  return K.isNegative(dmpGroundLC(f, u, K));
}

/**
 * Is the ground leading coefficient positive?
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Whether the ground leading coefficient positive.
 * @see SymPy `sympy.polys.densebasic.dmp_positive_p`
 * @example
 * ```ts
 * import { ZZ, dmpPositiveP } from '@symjs/symjs';
 *
 * dmpPositiveP([[1], [-1]], 1, ZZ); // => True
 * dmpPositiveP([[-1], [1]], 1, ZZ); // => False
 * ```
 */
export function dmpPositiveP(f: DensePoly, u: number, K: Domain): boolean {
  return K.isPositive(dmpGroundLC(f, u, K));
}

// ---------------------------------------------------------------------------
// dicts
// ---------------------------------------------------------------------------

/**
 * A univariate polynomial from {(k,): c} or {k: c}.
 *
 * @param f - Map from monomials to their nonzero coefficients.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns A univariate polynomial from {(k,): c} or {k: c}.
 * @see SymPy `sympy.polys.densebasic.dup_from_dict`
 * @example
 * ```ts
 * import { ZZ, dupFromDict } from '@symjs/symjs';
 *
 * dupFromDict(new Map([[[0], 7], [[2], 5], [[4], 1]]), ZZ); // => [1, 0, 5, 0, 7]
 * dupFromDict(new Map([]), ZZ); // => []
 * ```
 */
export function dupFromDict(f: TermDict, K: Domain): unknown[] {
  if (!f.size) return [];
  const h = new Map(monomEntries(f).map(([m, c]) => [first(m), c]));
  return dupFromRawDict(h, K);
}

/**
 * A univariate polynomial from {k: c}.
 *
 * @param f - Polynomial to operate on.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns A univariate polynomial from {k: c}.
 * @see SymPy `sympy.polys.densebasic.dup_from_raw_dict`
 * @example
 * ```ts
 * import { ZZ, dupFromRawDict } from '@symjs/symjs';
 *
 * dupFromRawDict(new Map([[0, 7], [2, 5], [4, 1]]), ZZ); // => [1, 0, 5, 0, 7]
 * ```
 */
export function dupFromRawDict(f: ReadonlyMap<number, unknown>, K: Domain): unknown[] {
  if (!f.size) return [];
  const g = new Map([...f].map(([k, c]) => [int(k), c]));
  const n = Math.max(...g.keys());
  const h: unknown[] = [];
  for (let k = n; k >= 0; k--) h.push(g.has(k) ? g.get(k) : K.zero);
  return dupStrip(h);
}

function fromMonoms(entries: readonly [Monom, unknown][], u: number, K: Domain): unknown[] {
  if (!u) return dupFromRawDict(new Map(entries.map(([m, c]) => [first(m), c])), K);
  if (!entries.length) return dmpZero(u);
  const coeffs = new Map<number, [Monom, unknown][]>();
  for (const [m, c] of entries) {
    const head = first(m);
    const list = coeffs.get(head) ?? [];
    list.push([m.slice(1), c]);
    coeffs.set(head, list);
  }
  const n = Math.max(...coeffs.keys());
  const h: unknown[] = [];
  for (let k = n; k >= 0; k--) {
    const sub = coeffs.get(k);
    h.push(sub === undefined ? dmpZero(u - 1) : fromMonoms(sub, u - 1, K));
  }
  return dmpStrip(h, u);
}

/**
 * A polynomial in u + 1 variables from {monomial: c}.
 *
 * @param f - Map from monomials to their nonzero coefficients.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns A polynomial in u + 1 variables from {monomial: c}.
 * @see SymPy `sympy.polys.densebasic.dmp_from_dict`
 * @example
 * ```ts
 * import { ZZ, dmpFromDict } from '@symjs/symjs';
 *
 * dmpFromDict(new Map([[[0, 0], 3], [[0, 1], 2], [[2, 1], 1]]), 1, ZZ); // => [[1, 0], [], [2, 3]]
 * dmpFromDict(new Map([]), 0, ZZ); // => []
 * ```
 */
export function dmpFromDict(f: TermDict, u: number, K: Domain): unknown[] {
  return fromMonoms(monomEntries(f), int(u), K);
}

/**
 * {(k,): c} of the nonzero terms ({(0,): 0} for zero with zero=true; SymPy dup_to_dict).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param zero - Include an explicit constant zero term for the zero polynomial.
 * @returns {(k,): c} of the nonzero terms ({(0,): 0} for zero with zero=true; SymPy dup_to_dict).
 * @see SymPy `sympy.polys.densebasic.dup_to_dict`
 * @remarks SymPy returns `{(0,): 7, (2,): 5, (4,): 1}` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { dupToDict } from '@symjs/symjs';
 *
 * dupToDict([1, 0, 5, 0, 7]); // => {[0]: 7, [2]: 5, [4]: 1}
 * dupToDict([]); // => {}
 * ```
 */
export function dupToDict(f: DensePoly, K: Domain | null = null, zero = false): Map<number[], unknown> {
  if (!f.length && zero && K !== null) return new Map([[[0], K.zero]]);
  const n = f.length - 1;
  const result = new Map<number[], unknown>();
  for (let k = 0; k <= n; k++) if (nz(f[n - k])) result.set([k], f[n - k]);
  return result;
}

/**
 * {k: c} of the nonzero terms.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param zero - Include an explicit constant zero term for the zero polynomial.
 * @returns {k: c} of the nonzero terms.
 * @see SymPy `sympy.polys.densebasic.dup_to_raw_dict`
 * @example
 * ```ts
 * import { dupToRawDict } from '@symjs/symjs';
 *
 * dupToRawDict([1, 0, 5, 0, 7]); // => {0: 7, 2: 5, 4: 1}
 * ```
 */
export function dupToRawDict(f: DensePoly, K: Domain | null = null, zero = false): Map<number, unknown> {
  if (!f.length && zero && K !== null) return new Map([[0, K.zero]]);
  const n = f.length - 1;
  const result = new Map<number, unknown>();
  for (let k = 0; k <= n; k++) if (nz(f[n - k])) result.set(k, f[n - k]);
  return result;
}

/**
 * {monomial: c} of the nonzero terms.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param zero - Include an explicit constant zero term for the zero polynomial.
 * @returns {monomial: c} of the nonzero terms.
 * @see SymPy `sympy.polys.densebasic.dmp_to_dict`
 * @remarks SymPy returns `{(0, 0): 3, (0, 1): 2, (2, 1): 1}` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { dmpToDict } from '@symjs/symjs';
 *
 * dmpToDict([[1, 0], [], [2, 3]], 1); // => {[0, 0]: 3, [0, 1]: 2, [2, 1]: 1}
 * dmpToDict([], 0); // => {}
 * ```
 */
export function dmpToDict(f: DensePoly, uIn: number, K: Domain | null = null, zero = false): Map<number[], unknown> {
  const u = int(uIn);
  if (!u) return dupToDict(f, K, zero);
  if (dmpZeroP(f, u) && zero && K !== null) return new Map([[Array.from({ length: u + 1 }, () => 0), K.zero]]);
  const d = dmpDegree(f, u);
  const n = d === ninf ? -1 : d;
  const result = new Map<number[], unknown>();
  for (let k = 0; k <= n; k++) {
    for (const [exp, coeff] of dmpToDict(asList(f[n - k]), u - 1)) result.set([k, ...exp], coeff);
  }
  return result;
}

// ---------------------------------------------------------------------------
// variables: swap, permute, nest, raise, deflate, inflate, exclude, include
// ---------------------------------------------------------------------------

/**
 * Exchange x_i and x_j.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param iIn - Zero-based index.
 * @param jIn - Index of the polynomial variable.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @throws RangeError when the indices do not satisfy `0 <= i < j <= u`.
 * @see SymPy `sympy.polys.densebasic.dmp_swap`
 * @example
 * ```ts
 * import { ZZ, dmpSwap } from '@symjs/symjs';
 *
 * dmpSwap([[[2], [1, 0]], []], 0, 1, 2, ZZ); // => [[[2], []], [[1, 0], []]]
 * dmpSwap([[[2], [1, 0]], []], 1, 2, 2, ZZ); // => [[[1], [2, 0]], [[]]]
 * ```
 */
export function dmpSwap(f: DensePoly, iIn: number, jIn: number, uIn: number, K: Domain): unknown[] {
  const [i, j, u] = [int(iIn), int(jIn), int(uIn)];
  if (i < 0 || j < 0 || i > u || j > u) throw new RangeError(`0 <= i < j <= ${u} expected`);
  if (i === j) return [...f];
  const H: [Monom, unknown][] = [];
  for (const [exp, coeff] of dmpToDict(f, u)) {
    const e = [...exp];
    [e[i], e[j]] = [at(exp, j), at(exp, i)];
    H.push([e, coeff]);
  }
  return fromMonoms(H, u, K);
}

/**
 * Permute the variables: x_i becomes x_P[i].
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param P - Permutation of the variable indices.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_permute`
 * @example
 * ```ts
 * import { ZZ, dmpPermute } from '@symjs/symjs';
 *
 * dmpPermute([[[2], [1, 0]], []], [1, 0, 2], 2, ZZ); // => [[[2], []], [[1, 0], []]]
 * dmpPermute([[[2], [1, 0]], []], [1, 2, 0], 2, ZZ); // => [[[1], []], [[2, 0], []]]
 * ```
 */
export function dmpPermute(f: DensePoly, P: readonly number[], uIn: number, K: Domain): unknown[] {
  const u = int(uIn);
  const H: [Monom, unknown][] = [];
  for (const [exp, coeff] of dmpToDict(f, u)) {
    const e = exp.map(() => 0);
    exp.forEach((x, k) => {
      if (k < P.length) e[int(P[k])] = x;
    });
    H.push([e, coeff]);
  }
  return fromMonoms(H, u, K);
}

/**
 * Wrap f in l more levels (a ground c becomes a polynomial; SymPy dmp_nest).
 *
 * @param f - Polynomial to operate on.
 * @param lIn - Number of additional levels.
 * @param _K - Coefficient domain for the polynomial arithmetic.
 * @returns Wrap f in l more levels (a ground c becomes a polynomial; SymPy dmp_nest).
 * @see SymPy `sympy.polys.densebasic.dmp_nest`
 * @example
 * ```ts
 * import { ZZ, dmpNest } from '@symjs/symjs';
 *
 * dmpNest([[1]], 2, ZZ); // => [[[[1]]]]
 * ```
 */
export function dmpNest(f: unknown, lIn: number, _K: Domain): unknown {
  const l = int(lIn);
  if (!Array.isArray(f)) return dmpGround(f, l);
  let g: unknown = f;
  for (let i = 0; i < l; i++) g = [g];
  return g;
}

/**
 * Add l levels at the bottom of f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param lIn - Number of additional levels.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_raise`
 * @example
 * ```ts
 * import { ZZ, dmpRaise } from '@symjs/symjs';
 *
 * dmpRaise([[], [1, 2]], 2, 1, ZZ); // => [[[[]]], [[[1]], [[2]]]]
 * ```
 */
export function dmpRaise(f: DensePoly, lIn: number, uIn: number, K: Domain): unknown[] {
  const [l, u] = [int(lIn), int(uIn)];
  if (!l) return [...f];
  if (!u) return f.length ? f.map((c) => dmpGround(c, l - 1)) : dmpZero(l);
  return f.map((c) => dmpRaise(asList(c), l, u - 1, K));
}

/**
 * [g, h] with f(x) = h(x**g).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param _K - Coefficient domain for the polynomial arithmetic.
 * @returns [g, h] with f(x) = h(x**g).
 * @see SymPy `sympy.polys.densebasic.dup_deflate`
 * @remarks SymPy returns `(3, [1, 1, 1])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupDeflate } from '@symjs/symjs';
 *
 * dupDeflate([1, 0, 0, 1, 0, 0, 1], ZZ); // => [3, [1, 1, 1]]
 * ```
 */
export function dupDeflate(f: DensePoly, _K: Domain): [number, unknown[]] {
  if (dupDegree(f) <= 0) return [1, [...f]];
  let g = 0n;
  for (let i = 0; i < f.length; i++) {
    if (!nz(f[f.length - 1 - i])) continue;
    g = igcd(g, BigInt(i));
    if (g === 1n) return [1, [...f]];
  }
  const G = Number(g);
  return [G, f.filter((_c, k) => k % G === 0)];
}

/** Exponent gcds of the monomials of dicts (SymPy's B of dmp_deflate). */
function exponentGcds(dicts: readonly Map<number[], unknown>[], u: number): number[] {
  const B = Array.from({ length: u + 1 }, () => 0n);
  for (const F of dicts) for (const M of F.keys()) M.forEach((m, i) => (B[i] = igcd(at(B, i), BigInt(m))));
  return B.map((b) => (b ? Number(b) : 1));
}

const deflateDict = (F: Map<number[], unknown>, B: readonly number[]): [Monom, unknown][] => [...F].map(([A, c]) => [A.map((a, i) => Math.floor(a / at(B, i))), c]);

/**
 * [B, h] with f(x_0, ...) = h(x_0**B[0], ...).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns [B, h] with f(x_0, ...) = h(x_0**B[0], ...).
 * @see SymPy `sympy.polys.densebasic.dmp_deflate`
 * @remarks SymPy returns `((2, 3), [[1, 2], [3, 4]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpDeflate } from '@symjs/symjs';
 *
 * dmpDeflate([[1, 0, 0, 2], [], [3, 0, 0, 4]], 1, ZZ); // => [[2, 3], [[1, 2], [3, 4]]]
 * ```
 */
export function dmpDeflate(f: DensePoly, uIn: number, K: Domain): [number[], unknown[]] {
  const u = int(uIn);
  if (dmpZeroP(f, u)) return [Array.from({ length: u + 1 }, () => 1), [...f]];
  const F = dmpToDict(f, u);
  const B = exponentGcds([F], u);
  if (B.every((b) => b === 1)) return [B, [...f]];
  return [B, fromMonoms(deflateDict(F, B), u, K)];
}

/**
 * [G, hs] with a common deflation of univariate polynomials.
 *
 * @param polys - Input polynomials.
 * @param _K - Coefficient domain for the polynomial arithmetic.
 * @returns [G, hs] with a common deflation of univariate polynomials.
 * @see SymPy `sympy.polys.densebasic.dup_multi_deflate`
 * @remarks SymPy returns `(2, ([1, 2, 3], [4, 0]))` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupMultiDeflate } from '@symjs/symjs';
 *
 * dupMultiDeflate([[1, 0, 2, 0, 3], [4, 0, 0]], ZZ); // => [2, [[1, 2, 3], [4, 0]]]
 * ```
 */
export function dupMultiDeflate(polys: readonly DensePoly[], _K: Domain): [number, unknown[][]] {
  let G = 0n;
  const same = (): [number, unknown[][]] => [1, polys.map((p) => [...p])];
  for (const p of polys) {
    if (dupDegree(p) <= 0) return same();
    let g = 0n;
    for (let i = 0; i < p.length; i++) {
      if (!nz(p[p.length - 1 - i])) continue;
      g = igcd(g, BigInt(i));
      if (g === 1n) return same();
    }
    G = igcd(G, g);
  }
  const n = Number(G);
  return [n, polys.map((p) => p.filter((_c, k) => k % n === 0))];
}

/**
 * [B, hs] with a common deflation of polynomials in u + 1 variables.
 *
 * @param polys - Input polynomials.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns [B, hs] with a common deflation of polynomials in u + 1 variables.
 * @see SymPy `sympy.polys.densebasic.dmp_multi_deflate`
 * @remarks SymPy returns `((2, 1), ([[1, 0, 0, 2], [3, 0, 0, 4]], [[1, 0, 2], [3, 0, 4]]))` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpMultiDeflate } from '@symjs/symjs';
 *
 * dmpMultiDeflate([[[1, 0, 0, 2], [], [3, 0, 0, 4]], [[1, 0, 2], [], [3, 0, 4]]], 1, ZZ); // => [[2, 1], [[[1, 0, 0, 2], [3, 0, 0, 4]], [[1, 0, 2], [3, 0, 4]]]]
 * ```
 */
export function dmpMultiDeflate(polys: readonly DensePoly[], uIn: number, K: Domain): [number[], unknown[][]] {
  const u = int(uIn);
  if (!u) {
    const [M, H] = dupMultiDeflate(polys, K);
    return [[M], H];
  }
  const F = polys.map((p) => dmpToDict(p, u));
  const B = exponentGcds(
    F.filter((_d, i) => !dmpZeroP(at(polys, i), u)),
    u,
  );
  if (B.every((b) => b === 1)) return [B, polys.map((p) => [...p])];
  return [B, F.map((d) => fromMonoms(deflateDict(d, B), u, K))];
}

/**
 * f(x**m).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param mIn - Multiplier for the exponents.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @throws RangeError when the inflation factor is not positive.
 * @see SymPy `sympy.polys.densebasic.dup_inflate`
 * @example
 * ```ts
 * import { ZZ, dupInflate } from '@symjs/symjs';
 *
 * dupInflate([1, 1, 1], 3, ZZ); // => [1, 0, 0, 1, 0, 0, 1]
 * ```
 */
export function dupInflate(f: DensePoly, mIn: number, K: Domain): unknown[] {
  const m = int(mIn);
  if (m <= 0) throw new RangeError(`'m' must be positive, got ${m}`);
  if (m === 1 || !f.length) return [...f];
  const result: unknown[] = [f[0]];
  for (const coeff of f.slice(1)) result.push(...Array.from({ length: m - 1 }, () => K.zero), coeff);
  return result;
}

function recInflate(g: DensePoly, M: readonly number[], v: number, i: number, K: Domain): unknown[] {
  if (!v) return dupInflate(g, at(M, i), K);
  if (at(M, i) <= 0) throw new RangeError(`all M[i] must be positive, got ${at(M, i)}`);
  const h = g.map((c) => recInflate(asList(c), M, v - 1, i + 1, K));
  const result: unknown[] = [h[0]];
  for (const coeff of h.slice(1)) {
    for (let k = 1; k < at(M, i); k++) result.push(dmpZero(v - 1));
    result.push(coeff);
  }
  return result;
}

/**
 * f(x_0**M[0], ..., x_u**M[u]).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param MIn - Exponent vector.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_inflate`
 * @example
 * ```ts
 * import { ZZ, dmpInflate } from '@symjs/symjs';
 *
 * dmpInflate([[1, 2], [3, 4]], [2, 3], 1, ZZ); // => [[1, 0, 0, 2], [], [3, 0, 0, 4]]
 * ```
 */
export function dmpInflate(f: DensePoly, MIn: readonly number[], uIn: number, K: Domain): unknown[] {
  const [M, u] = [MIn.map(int), int(uIn)];
  if (!u) return dupInflate(f, first(M), K);
  if (M.every((m) => m === 1)) return [...f];
  return recInflate(f, M, u, 0, K);
}

/**
 * [J, g, u'] removing the variables x_j (j in J) that f does not depend on.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns [J, g, u'] removing the variables x_j (j in J) that f does not depend on.
 * @see SymPy `sympy.polys.densebasic.dmp_exclude`
 * @remarks SymPy returns `([2], [[1], [1, 2]], 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpExclude } from '@symjs/symjs';
 *
 * dmpExclude([[[1]], [[1], [2]]], 2, ZZ); // => [[2], [[1], [1, 2]], 1]
 * ```
 */
export function dmpExclude(f: DensePoly, uIn: number, K: Domain): [number[], unknown[], number] {
  const u = int(uIn);
  if (!u || dmpGroundP(f, null, u)) return [[], [...f], u];
  const F = dmpToDict(f, u);
  const J: number[] = [];
  for (let j = 0; j <= u; j++) if ([...F.keys()].every((m) => !at(m, j))) J.push(j);
  if (!J.length) return [[], [...f], u];
  const g: [Monom, unknown][] = [...F].map(([m, c]) => [m.filter((_e, k) => !J.includes(k)), c]);
  const v = u - J.length;
  return [J, fromMonoms(g, v, K), v];
}

/**
 * Add the variables x_j (j in J) that f does not depend on.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param J - Indices of the generators.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_include`
 * @example
 * ```ts
 * import { ZZ, dmpInclude } from '@symjs/symjs';
 *
 * dmpInclude([[1], [1, 2]], [2], 1, ZZ); // => [[[1]], [[1], [2]]]
 * ```
 */
export function dmpInclude(f: DensePoly, J: readonly number[], uIn: number, K: Domain): unknown[] {
  const u = int(uIn);
  if (!J.length) return [...f];
  const g: [Monom, unknown][] = [...dmpToDict(f, u)].map(([m, c]) => {
    const monom = [...m];
    for (const j of J) monom.splice(int(j), 0, 0);
    return [monom, c];
  });
  return fromMonoms(g, u + J.length, K);
}


/**
 * Move the generators of a polynomial-ring coefficient domain K[y] into f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param front - Place the coefficient-domain generators first.
 * @returns Move the generators of a polynomial-ring coefficient domain K[y] into f.
 * @see SymPy `sympy.polys.densebasic.dmp_inject`
 * @remarks SymPy returns `([[1, 0], [1]], 1)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpInject, ex, symbols } from '@symjs/symjs';
 *
 * const [y] = symbols('y');
 * dmpInject([ex`y`, 1], 0, ZZ.polyRing(y)); // => [[[1, 0], [1]], 1]
 * ```
 */
export function dmpInject(f: DensePoly, uIn: number, K: Domain, front = false): [unknown[], number] {
  const u = int(uIn);
  const h: [Monom, unknown][] = [];
  for (const [fMonom, g] of dmpToDict(f, u)) {
    for (const [gMonom, c] of K.toDict(g)) h.push([front ? [...gMonom, ...fMonom] : [...fMonom, ...gMonom], c]);
  }
  const w = u + K.ngens;
  return [fromMonoms(h, w, K.dom), w];
}

/**
 * Move the last (or first) K.ngens variables of f into the coefficient domain K.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param front - Place the coefficient-domain generators first.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_eject`
 * @example
 * ```ts
 * import { ZZ, dmpEject, symbols } from '@symjs/symjs';
 *
 * const [y] = symbols('y');
 * const K = ZZ.polyRing(y);
 * dmpEject([[1, 0], [1]], 1, K).map(c => K.toSympy(c)); // => [y, 1]
 * ```
 */
export function dmpEject(f: DensePoly, uIn: number, K: Domain, front = false): unknown[] {
  const u = int(uIn);
  const n = K.ngens;
  const v = u - n + 1;
  const h = new Map<string, [Monom, [Monom, unknown][]]>();
  for (const [monom, c] of dmpToDict(f, u)) {
    const [gMonom, fMonom] = front ? [monom.slice(0, n), monom.slice(n)] : [monom.slice(monom.length - n), monom.slice(0, monom.length - n)];
    const k = monomKey(fMonom);
    const entry = h.get(k) ?? [fMonom, []];
    entry[1].push([gMonom, c]);
    h.set(k, entry);
  }
  const terms: [Monom, unknown][] = [...h.values()].map(([m, cs]) => [m, K.new(new Map(cs))]);
  return fromMonoms(terms, v - 1, K);
}

/**
 * [i, g] with f = x**i * g.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns [i, g] with f = x**i * g.
 * @see SymPy `sympy.polys.densebasic.dup_terms_gcd`
 * @remarks SymPy returns `(2, [1, 0, 1])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dupTermsGcd } from '@symjs/symjs';
 *
 * dupTermsGcd([1, 0, 1, 0, 0], ZZ); // => [2, [1, 0, 1]]
 * ```
 */
export function dupTermsGcd(f: DensePoly, K: Domain): [number, unknown[]] {
  if (nz(polyTC(f, K)) || !f.length) return [0, [...f]];
  let i = 0;
  while (!nz(f[f.length - 1 - i])) i++;
  return [i, f.slice(0, f.length - i)];
}

/**
 * [G, g] with f = x**G * g.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns [G, g] with f = x**G * g.
 * @see SymPy `sympy.polys.densebasic.dmp_terms_gcd`
 * @remarks SymPy returns `((2, 1), [[1], [1, 0]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, dmpTermsGcd } from '@symjs/symjs';
 *
 * dmpTermsGcd([[1, 0], [1, 0, 0], [], []], 1, ZZ); // => [[2, 1], [[1], [1, 0]]]
 * ```
 */
export function dmpTermsGcd(f: DensePoly, uIn: number, K: Domain): [number[], unknown[]] {
  const u = int(uIn);
  if (nz(dmpGroundTC(f, u, K)) || dmpZeroP(f, u)) return [Array.from({ length: u + 1 }, () => 0), [...f]];
  const F = dmpToDict(f, u);
  const G = [...F.keys()].reduce((a, m) => a.map((x, i) => Math.min(x, at(m, i))));
  if (G.every((g) => g === 0)) return [G, [...f]];
  return [G, fromMonoms([...F].map(([m, c]) => [m.map((x, i) => x - at(G, i)), c]), u, K)];
}

function recListTerms(g: DensePoly, v: number, monom: Monom): [number[], unknown][] {
  const d = dmpDegree(g, v);
  const terms: [number[], unknown][] = [];
  g.forEach((c, i) => {
    if (!v) {
      if (nz(c)) terms.push([[...monom, d - i], c]);
    } else terms.push(...recListTerms(asList(c), v - 1, [...monom, d - i]));
  });
  return terms;
}

/**
 * The nonzero terms [monomial, c], in the given order (lex by default; SymPy dmp_list_terms).
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param order - Monomial order used to compare terms.
 * @returns The nonzero terms [monomial, c], in the given order (lex by default.
 * @see SymPy `sympy.polys.densebasic.dmp_list_terms`
 * @remarks SymPy returns `[((1, 1), 1), ((1, 0), 1), ((0, 1), 2), ((0, 0), 3)]` with tuples for the fixed-length groups. The second result is `[((1, 1), 1), ((1, 0), 1), ((0, 1), 2), ((0, 0), 3)]` in SymPy.
 * @example
 * ```ts
 * import { ZZ, dmpListTerms } from '@symjs/symjs';
 *
 * dmpListTerms([[1, 1], [2, 3]], 1, ZZ); // => [[[1, 1], 1], [[1, 0], 1], [[0, 1], 2], [[0, 0], 3]]
 * dmpListTerms([[1, 1], [2, 3]], 1, ZZ, 'grevlex'); // => [[[1, 1], 1], [[1, 0], 1], [[0, 1], 2], [[0, 0], 3]]
 * ```
 */
export function dmpListTerms(f: DensePoly, uIn: number, K: Domain, order?: string | MonomialOrdering): [number[], unknown][] {
  const u = int(uIn);
  const terms = recListTerms(f, u, []);
  if (!terms.length) return [[Array.from({ length: u + 1 }, () => 0), K.zero]];
  if (order === undefined) return terms;
  const key = monomialKey(order);
  return [...terms].sort((a, b) => compareMonomialKeys(key(b[0]), key(a[0])));
}

/**
 * h(a, b, ...args) over the coefficient pairs, padded with zeros.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param gIn - Second polynomial in dense, leading-coefficient-first representation.
 * @param h - Function applied to each pair of coefficients.
 * @param args - Additional arguments to the coefficient function.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dup_apply_pairs`
 * @example
 * ```ts
 * import { ZZ, dupApplyPairs } from '@symjs/symjs';
 *
 * dupApplyPairs([1, 2, 3], [1, 2], (a, b) => Number(a) + Number(b), [], ZZ); // => [1, 3, 5]
 * ```
 */
export function dupApplyPairs(fIn: DensePoly, gIn: DensePoly, h: (a: unknown, b: unknown, ...args: unknown[]) => unknown, args: readonly unknown[], K: Domain): unknown[] {
  const [n, m] = [fIn.length, gIn.length];
  const pad = (p: DensePoly, k: number): unknown[] => [...Array.from({ length: k }, () => K.zero), ...p];
  const [f, g] = [pad(fIn, m - n), pad(gIn, n - m)];
  return dupStrip(f.map((a, i) => h(a, g[i], ...args)));
}

/**
 * h(a, b, ...args) over the ground coefficient pairs, padded with zeros.
 *
 * @param fIn - Polynomial in dense, leading-coefficient-first representation.
 * @param gIn - Second polynomial in dense, leading-coefficient-first representation.
 * @param h - Function applied to each pair of coefficients.
 * @param args - Additional arguments to the coefficient function.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.densebasic.dmp_apply_pairs`
 * @example
 * ```ts
 * import { ZZ, dmpApplyPairs } from '@symjs/symjs';
 *
 * dmpApplyPairs([[1], [2]], [[3]], (a, b) => Number(a) + Number(b), [], 1, ZZ); // => [[1], [5]]
 * ```
 */
export function dmpApplyPairs(fIn: DensePoly, gIn: DensePoly, h: (a: unknown, b: unknown, ...args: unknown[]) => unknown, args: readonly unknown[], uIn: number, K: Domain): unknown[] {
  const u = int(uIn);
  if (!u) return dupApplyPairs(fIn, gIn, h, args, K);
  const [n, m] = [fIn.length, gIn.length];
  const f = [...dmpZeros(m - n, u - 1, K), ...fIn];
  const g = [...dmpZeros(n - m, u - 1, K), ...gIn];
  return dmpStrip(
    f.map((a, i) => dmpApplyPairs(asList(a), asList(g[i]), h, args, u - 1, K)),
    u,
  );
}

/**
 * The terms of degree m <= k < n of f.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param mIn - Inclusive lower degree bound.
 * @param nIn - Exclusive upper degree bound.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The terms of degree m <= k < n of f.
 * @see SymPy `sympy.polys.densebasic.dup_slice`
 */
export function dupSlice(f: DensePoly, mIn: number, nIn: number, K: Domain): unknown[] {
  const [m, n, k] = [int(mIn), int(nIn), f.length];
  const M = k >= m ? k - m : 0;
  const N = k >= n ? k - n : 0;
  const g = dupStrip(f.slice(N, M));
  return g.length ? [...g, ...Array.from({ length: m }, () => K.zero)] : [];
}

/**
 * The terms of degree m <= k < n in x_j of f, the others with x_j**0.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param mIn - Inclusive lower degree bound.
 * @param nIn - Exclusive upper degree bound.
 * @param jIn - Index of the polynomial variable.
 * @param uIn - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The terms of degree m <= k < n in x_j of f, the others with x_j**0.
 * @throws RangeError when the variable index is outside the polynomial levels.
 * @see SymPy `sympy.polys.densebasic.dmp_slice_in`
 */
export function dmpSliceIn(f: DensePoly, mIn: number, nIn: number, jIn: number, uIn: number, K: Domain): unknown[] {
  const [m, n, j, u] = [int(mIn), int(nIn), int(jIn), int(uIn)];
  if (j < 0 || j > u) throw new RangeError(`-${u} <= j < ${u} expected, got ${j}`);
  if (!u) return dupSlice(f, m, n, K);
  const g = new Map<string, [Monom, unknown]>();
  for (const [monomIn, coeff] of dmpToDict(f, u)) {
    const k = at(monomIn, j);
    const monom = k < m || k >= n ? monomIn.map((e, i) => (i === j ? 0 : e)) : monomIn;
    const key = monomKey(monom);
    const old = g.get(key);
    g.set(key, [monom, old === undefined ? coeff : domainArith(K, 'add', old[1], coeff)]);
  }
  return fromMonoms([...g.values()], u, K);
}

/**
 * The terms of degree m <= k < n in x_0.
 *
 * @param f - Polynomial in dense, leading-coefficient-first representation.
 * @param m - Inclusive lower degree bound.
 * @param n - Exclusive upper degree bound.
 * @param u - Number of variables minus one.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The terms of degree m <= k < n in x_0.
 * @see SymPy `sympy.polys.densebasic.dmp_slice`
 */
export function dmpSlice(f: DensePoly, m: number, n: number, u: number, K: Domain): unknown[] {
  return dmpSliceIn(f, m, n, 0, u, K);
}

/**
 * A random polynomial of degree n with coefficients in [a, b] and a nonzero leading coefficient.
 *
 * @param nIn - Exponent or degree.
 * @param aIn - Inclusive lower bound on the coefficients.
 * @param bIn - Inclusive upper bound on the coefficients.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @param random - Sampler returning a number in the half-open interval from zero to one.
 * @returns A random polynomial of degree n with coefficients in [a, b] and a nonzero leading coefficient.
 * @see SymPy `sympy.polys.densebasic.dup_random`
 * @example
 * ```ts
 * import { ZZ, dupRandom } from '@symjs/symjs';
 *
 * dupRandom(3, -10, 10, ZZ).length; // => 4
 * ```
 */
export function dupRandom(nIn: number, aIn: number, bIn: number, K: Domain, random: () => number = Math.random): unknown[] {
  const [n, a, b] = [int(nIn), int(aIn), int(bIn)];
  const draw = (): unknown => K.convert(a + Math.floor(random() * (b - a + 1)));
  const f = Array.from({ length: n + 1 }, draw);
  while (!nz(f[0])) f[0] = draw();
  return f;
}
