// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/specialpolys.py and dup_zz_cyclotomic_poly
// of polys/factortools.py), Copyright (c) 2006-2023 SymPy Development Team,
// BSD 3-Clause License (see LICENSE).

/**
 * @file Special polynomials (SymPy polys/specialpolys.py):
 * swinnerton_dyer_poly, cyclotomic_poly, symmetric_poly, random_poly and
 * interpolating_poly.
 */

import { at } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Dummy, Expr, Rational, Sym } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { nextprime } from '../ntheory/generate';
import type { NamedPolyOptions, NamedPolyResult } from './orthopolys';
import { cyclotomicCoeffs, minimalPolynomial } from './numberfields';
import { Poly } from './sympoly';

/** The polynomial in x (a dummy variable for a PurePoly when x is not given) as an expression or a Poly. */
function finish(e: (v: Expr) => Expr, x: ExprLike | undefined, opts: NamedPolyOptions): Expr | Poly {
  const v = x === undefined ? new Dummy('x') : sympify(x);
  const p = e(v);
  return opts.polys ? Poly.from(p, [v], { pure: x === undefined }) : p;
}

/**
 * Constructs the minimal polynomial of the sum of the square roots of the first `n` primes.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the order is not a positive integer.
 * @see SymPy `sympy.polys.specialpolys.swinnerton_dyer_poly`
 */
export function swinnertonDyerPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function swinnertonDyerPoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  if (!Number.isInteger(n) || n <= 0) throw new RangeError(`Cannot generate Swinnerton-Dyer polynomial of order ${n}`);
  return finish(
    (v) => {
      if (n === 1) return add(pow(v, 2), -2);
      if (n === 2) return add(pow(v, 4), mul(-10, pow(v, 2)), 1);
      if (n === 3) return add(pow(v, 8), mul(-40, pow(v, 6)), mul(352, pow(v, 4)), mul(-960, pow(v, 2)), 576);
      const roots: Expr[] = [sqrt(2)];
      let p = 2n;
      for (let i = 2; i <= n; i++) {
        p = nextprime(p);
        roots.push(sqrt(Rational.of(p)));
      }
      const t = new Dummy('x');
      return minimalPolynomial(add(...roots), t).subs(t, v);
    },
    x,
    opts,
  );
}

/**
 * Constructs the polynomial whose roots are the primitive nth roots of unity.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the order is not a positive integer.
 * @see SymPy `sympy.polys.specialpolys.cyclotomic_poly`
 */
export function cyclotomicPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function cyclotomicPoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  if (!Number.isInteger(n) || n <= 0) throw new RangeError(`Cannot generate cyclotomic polynomial of order ${n}`);
  const cs = cyclotomicCoeffs(n);
  return finish((v) => add(...cs.map((c, i) => mul(Rational.of(c), pow(v, cs.length - 1 - i)))), x, opts);
}

const isExprLike = (a: unknown): a is ExprLike => a instanceof Expr || typeof a === 'number' || typeof a === 'bigint' || typeof a === 'string';

/** The trailing options object of symmetricPoly (the other arguments are generators or one list of them). */
const isOptions = (a: unknown): a is NamedPolyOptions => !isExprLike(a) && !Array.isArray(a);

/**
 * Sums products of `n` distinct generators to form the elementary symmetric polynomial.
 *
 * @param n - Order of the elementary symmetric polynomial.
 * @param args - Variables and an optional polynomial-output setting.
 * @returns The degree-`n` symmetric polynomial.
 * @throws RangeError when the requested order is outside the range allowed by the number of generators.
 * @see SymPy `sympy.polys.specialpolys.symmetric_poly`
 */
export function symmetricPoly(n: number, ...args: (ExprLike | readonly ExprLike[] | NamedPolyOptions)[]): Expr | Poly {
  const last = args[args.length - 1];
  const opts = isOptions(last) ? last : {};
  const rest = isOptions(last) ? args.slice(0, -1) : args;
  // SymPy _analyze_gens: a single sequence of generators
  const first = rest[0];
  const list: readonly unknown[] = rest.length === 1 && Array.isArray(first) ? first : rest;
  const gens = list.filter(isExprLike).map((g) => sympify(g));
  if (!Number.isInteger(n) || n < 0 || n > gens.length || !gens.length) {
    throw new RangeError(`Cannot generate symmetric polynomial of order ${n} for (${gens.map((g) => g.toString()).join(', ')})`);
  }
  const terms: Expr[] = [];
  const rec = (start: number, chosen: Expr[]): void => {
    if (chosen.length === n) {
      terms.push(mul(...chosen));
      return;
    }
    for (let i = start; i < gens.length; i++) rec(i + 1, [...chosen, at(gens, i)]);
  };
  rec(0, []);
  const p = add(...terms);
  return opts.polys ? Poly.from(p, gens) : p;
}

/** Options of randomPoly. */
export interface RandomPolyOptions extends NamedPolyOptions {
  /** The random number generator (uniform in [0, 1)); Math.random by default. */
  random?: () => number;
}

/**
 * Generates a degree-`n` polynomial with integer coefficients in the supplied inclusive interval.
 *
 * @param x - Variable or evaluation point of the polynomial.
 * @param n - Nonnegative index of the polynomial family.
 * @param inf - Inclusive lower bound on the coefficients.
 * @param sup - Inclusive upper bound on the coefficients.
 * @param opts - Set `random` to supply a sampler and `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the degree is not a nonnegative integer or the bounds admit no nonzero integer coefficient.
 * @see SymPy `sympy.polys.specialpolys.random_poly`
 */
export function randomPoly<O extends RandomPolyOptions = Record<never, never>>(x: ExprLike, n: number, inf: number, sup: number, opts?: O): NamedPolyResult<O>;
export function randomPoly(x: ExprLike, n: number, inf: number, sup: number, opts: RandomPolyOptions = {}): Expr | Poly {
  if (!Number.isInteger(n) || n < 0) throw new RangeError(`random_poly: the degree must be a nonnegative integer (got ${n})`);
  if (!(Number.isInteger(inf) && Number.isInteger(sup) && inf <= sup) || (inf === 0 && sup === 0)) {
    throw new RangeError(`random_poly: no nonzero integer coefficient in [${inf}, ${sup}]`);
  }
  const rand = opts.random ?? Math.random;
  const draw = (): number => inf + Math.floor(rand() * (sup - inf + 1));
  // SymPy dup_random: the leading coefficient is drawn again until it is nonzero
  let lead = draw();
  while (lead === 0) lead = draw();
  const cs = [lead, ...Array.from({ length: n }, draw)];
  return finish((v) => add(...cs.map((c, i) => mul(c, pow(v, n - i)))), x, { polys: opts.polys });
}

/**
 * Interpolates the points with a polynomial of degree below their count, generating indexed coordinate
 * symbols for string inputs.
 *
 * @param n - Number of interpolation nodes.
 * @param xIn - Variable or evaluation point of the polynomial.
 * @param XIn - Interpolation nodes.
 * @param YIn - Values at the interpolation nodes.
 * @returns The Lagrange polynomial of degree n - 1 through the points (X[i], Y[i]).
 * @throws RangeError when the interpolation variable occurs in the input data or is not a symbol.
 * @see SymPy `sympy.polys.specialpolys.interpolating_poly`
 */
export function interpolatingPoly(n: number, xIn: ExprLike, XIn: string | readonly ExprLike[] = 'x', YIn: string | readonly ExprLike[] = 'y'): Expr {
  const x = sympify(xIn);
  const pts = (v: string | readonly ExprLike[]): Expr[] =>
    typeof v === 'string' ? Array.from({ length: n }, (_, i) => new Sym(`${v}${i}`)) : v.map(sympify);
  const X = pts(XIn);
  const Y = pts(YIn);
  const xs = new Set([...freeSymbols(x)].map(s => s.key));
  const clash = (vs: readonly Expr[]) => vs.some((v) => [...freeSymbols(v)].some((s) => xs.has(s.key)));
  if (!xs.size || clash(X) || clash(Y)) {
    throw new RangeError('Expecting symbol for x that does not appear in X or Y. Use `interpolate(list(zip(X, Y)), x)` instead.');
  }
  const numert = mul(...X.slice(0, n).map((xi) => add(x, mul(-1, xi))));
  const terms = Array.from({ length: n }, (_, i) => {
    const numer = mul(numert, pow(add(x, mul(-1, at(X, i))), -1));
    const denom = mul(...X.slice(0, n).flatMap((xj, j) => (j === i ? [] : [add(at(X, i), mul(-1, xj))])));
    return mul(numer, pow(denom, -1), at(Y, i));
  });
  return add(...terms);
}
