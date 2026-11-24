// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/ring_series.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/** Truncated arithmetic in a specified series variable; all other generators remain parameters. */
import { NotImplementedError } from '../core/errors';
import { at, first } from '../core/guard';
import { removeO } from '../core/methods';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Float, Mul, Pow, Rational } from '../core/nodes';
import { lcm } from '../core/numbers';
import { exp, pow, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { fn } from '../functions/elementary/elementary';
import { series } from '../series/series';
import { expand } from '../simplify/expand';
import type { IntLike } from '../ntheory/intutil';
import { groundIsZero, intArg } from './compatibility';
import { CoercionFailed, QQ } from './domains';
import type { PolyElement } from './rings';
import { PolyRing } from './rings';
import type { PuiseuxTerm } from './puiseux';
import { PuiseuxPoly, PuiseuxRing, addExponents as plus, multiplyExponents as times, compareExponents as cmp, rationalExponent as rat } from './puiseux';

/** An ordinary or Puiseux polynomial used in truncated series arithmetic. */
export type SeriesPoly = PolyElement | PuiseuxPoly;
/**
 * An operation on a polynomial series truncated in a specified generator.
 *
 * @param p - Input polynomial series.
 * @param x - Expansion variable.
 * @param prec - Exclusive exponent bound.
 * @returns The series truncated to the requested order.
 */
export type SeriesFunction = (p: SeriesPoly, x: SeriesPoly, prec: ExprLike) => SeriesPoly;
const zero = Rational.of(0), one = Rational.of(1), minusOne = Rational.of(-1);
const minus = (a: Rational, b: Rational): Rational => plus(a, times(minusOne, b));

function lift(p: SeriesPoly): PuiseuxPoly {
  return p instanceof PuiseuxPoly ? p : new PuiseuxRing(p.ring.symbols, p.ring.domain).fromPoly(p);
}
function index(p: SeriesPoly, x: SeriesPoly): number {
  return lift(p).ring.index(lift(x));
}
function restore(p: SeriesPoly, q: PuiseuxPoly): SeriesPoly {
  // Fractional exponents are promoted instead of being rounded to JS numbers.
  if (p instanceof PuiseuxPoly || q.monoms().some((m) => m.some((e) => !e.isInteger))) return q;
  return p.ring.fromTerms(q.terms().map(([m, c]) => [m.map((e) => {
    const n = Number(e.p);
    if (!Number.isSafeInteger(n)) throw new RangeError('polynomial exponent exceeds the safe integer range');
    return n;
  }), c]));
}
function trunc(p: PuiseuxPoly, i: number, prec: Rational): PuiseuxPoly {
  return p.ring.fromDict(p.terms().filter(([m]) => cmp(at(m, i), prec) < 0));
}
function valuation(p: PuiseuxPoly, i: number): Rational {
  if (p.isZero) throw new RangeError('the zero series has no finite valuation');
  return p.monoms().map((m) => at(m, i)).reduce((a, b) => cmp(a, b) < 0 ? a : b);
}
function shift(p: PuiseuxPoly, i: number, amount: Rational): PuiseuxPoly {
  return p.ring.fromDict(p.terms().map(([m, c]) => [m.map((e, j) => j === i ? plus(e, amount) : e), c]));
}
function product(p: PuiseuxPoly, q: PuiseuxPoly, i: number, prec: Rational): PuiseuxPoly {
  p.ring.ringNew(q); // Require the same generators and coefficient domain.
  const terms: PuiseuxTerm[] = [];
  for (const [m, c] of p.terms()) for (const [n, d] of q.terms()) {
    if (cmp(plus(at(m, i), at(n, i)), prec) < 0) terms.push([m.map((e, j) => plus(e, at(n, j))), p.ring.domain.mul(c, d)]);
  }
  return p.ring.fromDict(terms);
}
function integral(p: PuiseuxPoly, i: number): PuiseuxPoly {
  return p.ring.fromDict(p.terms().map(([m, c]) => {
    const e = plus(at(m, i), one);
    if (e.isZero) throw new NotImplementedError('the integral contains a logarithm');
    return [m.map((a, j) => j === i ? e : a), p.ring.domainNew(c.div(e))];
  }));
}
function factorial(n: number): bigint {
  let r = 1n;
  for (let k = 2; k <= n; k++) r *= BigInt(k);
  return r;
}

/**
 * Remove all terms of degree at least prec in x.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_trunc`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsTrunc } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsTrunc(R.fromExpr(ex`x**10 + x**5 + x + 1`), x, 12); // => x**10 + x**5 + x + 1
 * rsTrunc(R.fromExpr(ex`x**10 + x**5 + x + 1`), x, 10); // => x**5 + x + 1
 * ```
 */
export function rsTrunc(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return restore(p, trunc(lift(p), index(p, x), rat(prec))); }
/**
 * Multiply with truncation before accumulating terms.
 *
 * @param p - Input series.
 * @param q - Second input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_mul`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsMul } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsMul(R.fromExpr(ex`x**2 + 2*x + 1`), R.fromExpr(ex`x + 1`), x, 3); // => 3*x**2 + 3*x + 1
 * ```
 */
export function rsMul(p: SeriesPoly, q: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return restore(p, product(lift(p), lift(q), index(p, x), rat(prec))); }
/**
 * Square modulo O(x**prec).
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_square`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsSquare } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsSquare(R.fromExpr(ex`x**2 + 2*x + 1`), x, 3); // => 6*x**2 + 4*x + 1
 * ```
 */
export function rsSquare(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return rsMul(p, p, x, prec); }
/**
 * Differentiate a finite series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_diff`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsDiff } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsDiff(R.fromExpr(ex`x**2*y**3 + x`), x); // => 2*x*y**3 + 1
 * ```
 */
export function rsDiff(p: SeriesPoly, x: SeriesPoly): SeriesPoly { const q = lift(p); return restore(p, q.diff(at(q.ring.gens, index(p, x)))); }
/**
 * Integrate a finite series when no logarithmic term is needed.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_integrate`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsIntegrate } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsIntegrate(R.fromExpr(ex`x**2*y**3 + x`), x); // => 1/3*x**3*y**3 + 1/2*x**2
 * ```
 */
export function rsIntegrate(p: SeriesPoly, x: SeriesPoly): SeriesPoly { return restore(p, integral(lift(p), index(p, x))); }

/**
 * Substitute x_i -> x_i**n in the exponent lattice.
 *
 * @param p - Input series.
 * @param iIn - Index of the generator whose exponents change.
 * @param n - Exponent.
 * @returns The resulting truncated series.
 * @throws RangeError when a generator index is outside the allowed range.
 * @see SymPy `sympy.polys.ring_series.pow_xin`
 * @example
 * ```ts
 * import { QQ, ex, powXin, puiseuxRing } from '@symjs/symjs';
 *
 * const [R] = puiseuxRing('x, y', QQ);
 * powXin(R.fromExpr(ex`x**(2/5) + x**(2/3) + x`), 0, 15); // => x**6 + x**10 + x**15
 * ```
 */
export function powXin(p: SeriesPoly, iIn: IntLike, n: ExprLike): SeriesPoly {
  const i = intArg(iIn);
  if (!Number.isInteger(i) || i < 0 || i >= p.ring.ngens) throw new RangeError('invalid generator index');
  const q = lift(p), exponent = rat(n);
  return restore(p, q.ring.fromDict(q.terms().map(([m, c]) => [m.map((e, j) => j === i ? times(e, exponent) : e), c])));
}
/**
 * A nonintegral exponent in x; negative integer powers are not regular.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @returns A nonintegral exponent in x.
 * @throws RangeError when the series is not regular in the expansion variable.
 * @see SymPy `sympy.polys.ring_series.rs_is_puiseux`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing, rsIsPuiseux } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x', QQ);
 * rsIsPuiseux(R.fromExpr(ex`x**(2/5) + x**(2/3) + x`), x); // => True
 * ```
 */
export function rsIsPuiseux(p: SeriesPoly, x: SeriesPoly): boolean {
  const i = index(p, x);
  for (const m of lift(p).monoms()) {
    const e = at(m, i);
    if (!e.isInteger) return true;
    if (e.isNegative) throw new RangeError('the series is not regular');
  }
  return false;
}

/** Compose coefficients with a series of positive valuation. */
function composePositive(p: PuiseuxPoly, i: number, prec: Rational, coefficient: (n: number) => ExprLike): PuiseuxPoly {
  const constant = p.ring.groundNew(coefficient(0));
  if (p.isZero) return trunc(constant, i, prec);
  const v = valuation(p, i);
  if (cmp(v, zero) <= 0) throw new NotImplementedError('a positive series valuation is required');
  let result = trunc(constant, i, prec), power = p.ring.one;
  for (let k = 1; cmp(times(v, Rational.of(k)), prec) < 0; k++) {
    power = product(power, p, i, prec);
    result = result.add(power.mul(coefficient(k)));
  }
  return result;
}
/** Factor c*x**v from p, with a scalar nonzero leading coefficient. */
function normalize(p: PuiseuxPoly, i: number): [Rational, Expr, PuiseuxPoly] {
  const v = valuation(p, i), q = shift(p, i, times(minusOne, v));
  const c = q.get(q.ring.zeroMonom);
  if (groundIsZero(q.ring.domain, c) || q.terms().some(([m]) => at(m, i).isZero && m.some((e) => !e.isZero))) {
    throw new NotImplementedError('the leading coefficient must be a ground-domain unit');
  }
  return [v, c, q.truediv(c).sub(1)];
}
function rationalPower(p: PuiseuxPoly, exponent: Rational, i: number, prec: Rational): PuiseuxPoly {
  if (p.isZero) {
    if (exponent.isNegative) throw new RangeError('division by the zero series');
    // Zero exponents are handled by integerPower before this function is called.
    return p;
  }
  const [v, c, tail] = normalize(p, i);
  const offset = times(v, exponent);
  let binomial = one;
  const result = composePositive(tail, i, minus(prec, offset), (k) => {
    if (k) binomial = times(binomial, times(plus(exponent, Rational.of(1 - k)), Rational.of(1, k)));
    return binomial;
  });
  return shift(result.mul(p.ring.domainNew(pow(c, exponent))), i, offset);
}
function integerPower(p: PuiseuxPoly, n: bigint, i: number, prec: Rational): PuiseuxPoly {
  if (!n) return trunc(p.ring.one, i, prec);
  if (p.isZero) return p;
  const v = valuation(p, i), offset = times(v, Rational.of(n));
  const work = minus(prec, offset);
  let factor = trunc(shift(p, i, times(minusOne, v)), i, work), result = p.ring.one, k = n;
  while (k) {
    if (k & 1n) result = product(result, factor, i, work);
    k >>= 1n;
    if (k) factor = product(factor, factor, i, work);
  }
  return shift(result, i, offset);
}
/**
 * Integer or rational power, retaining the requested final precision.
 *
 * @param p - Input series.
 * @param n - Exponent.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_pow`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsPow } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsPow(R.fromExpr(ex`x + 1`), 4, x, 3); // => 6*x**2 + 4*x + 1
 * ```
 */
export function rsPow(p: SeriesPoly, n: ExprLike, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const e = rat(n), q = lift(p), i = index(p, x), order = rat(prec);
  return restore(p, e.isInteger && !e.isNegative ? integerPower(q, e.p, i, order) : rationalPower(q, e, i, order));
}
/**
 * Laurent/Puiseux reciprocal with a scalar leading coefficient.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_series_inversion`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsSeriesInversion } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsSeriesInversion(R.fromExpr(ex`x*y**2 + 1`), x, 4); // => -x**3*y**6 + x**2*y**4 - x*y**2 + 1
 * rsSeriesInversion(R.fromExpr(ex`x*y**2 + 1`), R.fromExpr(ex`y`), 4); // => -x*y**2 + 1
 * ```
 */
export function rsSeriesInversion(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return rsPow(p, -1, x, prec); }
/**
 * Expand the nth root, or its reciprocal for negative n.
 *
 * @param p - Input series.
 * @param nIn - Integer root index.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @throws RangeError when the requested root index is not an integer or both base and exponent are zero.
 * @see SymPy `sympy.polys.ring_series.rs_nth_root`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsNthRoot } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsNthRoot(R.fromExpr(ex`x*y + x + 1`), -3, x, 3); // => 2/9*x**2*y**2 + 4/9*x**2*y + 2/9*x**2 - 1/3*x*y - 1/3*x + 1
 * ```
 */
export function rsNthRoot(p: SeriesPoly, nIn: IntLike, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const n = intArg(nIn);
  if (!Number.isSafeInteger(n)) throw new RangeError('root order must be an integer');
  if (!n) {
    if (lift(p).isZero) throw new RangeError('0**0 expression');
    return p.ring.one;
  }
  return rsPow(p, Rational.of(1, n), x, prec);
}

type AnalyticName = 'exp' | 'sin' | 'cos' | 'sinh' | 'cosh' | 'atan' | 'atanh' | 'asin' | 'asinh' | 'LambertW';
function analyticCoefficient(name: AnalyticName, n: number): Rational {
  if (name === 'exp') return Rational.of(1, factorial(n));
  if (name === 'sin' || name === 'sinh') return n % 2 ? Rational.of(name === 'sin' && n % 4 === 3 ? -1 : 1, factorial(n)) : zero;
  if (name === 'cos' || name === 'cosh') return n % 2 ? zero : Rational.of(name === 'cos' && n % 4 === 2 ? -1 : 1, factorial(n));
  if (name === 'LambertW') return n ? Rational.of((-BigInt(n)) ** BigInt(n - 1), factorial(n)) : zero;
  if (n % 2 === 0) return zero;
  if (name === 'atan' || name === 'atanh') return Rational.of(name === 'atan' && n % 4 === 3 ? -1 : 1, n);
  const k = (n - 1) / 2;
  return Rational.of((name === 'asinh' && k % 2 ? -1n : 1n) * factorial(2 * k), 4n ** BigInt(k) * factorial(k) ** 2n * BigInt(n));
}
function analytic(p: SeriesPoly, x: SeriesPoly, prec: ExprLike, name: AnalyticName): SeriesPoly {
  // SymPy's exp/cos algorithms require a positive truncation order.
  if ((name === 'exp' || name === 'cos') && !rat(prec).isPositive) throw new RangeError('the series order must be positive');
  const q = lift(p), i = index(p, x), c = q.get(q.ring.zeroMonom), tail = q.sub(c);
  if (groundIsZero(q.ring.domain, c)) return restore(p, composePositive(tail, i, rat(prec), (k) => analyticCoefficient(name, k)));
  // Taylor coefficients at a nonzero ground constant, kept in the original domain.
  const t = new Dummy('t');
  let derivative = name === 'exp' ? exp(t) : fn(name, [t]);
  return restore(p, composePositive(tail, i, rat(prec), (k) => {
    if (k) derivative = diff(derivative, t);
    return q.ring.domainNew(derivative.subs([[t, q.ring.domain.toSympy(c)]]).div(Rational.of(factorial(k))));
  }));
}
/**
 * Exponential series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_exp`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsExp } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsExp(R.fromExpr(ex`x**2`), x, 7); // => 1/6*x**6 + 1/2*x**4 + x**2 + 1
 * ```
 */
export function rsExp(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'exp'); }
/**
 * Sine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_sin`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing, rsSin } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x, y', QQ);
 * rsSin(R.fromExpr(ex`x*y + x`), x, 4); // => x + x*y + -1/6*x**3 + -1/2*x**3*y + -1/2*x**3*y**2 + -1/6*x**3*y**3
 * rsSin(R.fromExpr(ex`x**(3/2) + x*y**(7/5)`), x, 4); // => x*y**(7/5) + x**(3/2) + -1/6*x**3*y**(21/5) + -1/2*x**(7/2)*y**(14/5)
 * ```
 */
export function rsSin(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'sin'); }
/**
 * Cosine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_cos`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing, rsCos } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x, y', QQ);
 * rsCos(R.fromExpr(ex`x*y + x`), x, 4); // => 1 + -1/2*x**2 + -1*x**2*y + -1/2*x**2*y**2
 * ```
 */
export function rsCos(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'cos'); }
/**
 * Hyperbolic sine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_sinh`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsSinh } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsSinh(R.fromExpr(ex`x*y + x`), x, 4); // => 1/6*x**3*y**3 + 1/2*x**3*y**2 + 1/2*x**3*y + 1/6*x**3 + x*y + x
 * ```
 */
export function rsSinh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'sinh'); }
/**
 * Hyperbolic cosine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_cosh`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsCosh } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsCosh(R.fromExpr(ex`x*y + x`), x, 4); // => 1/2*x**2*y**2 + x**2*y + 1/2*x**2 + 1
 * ```
 */
export function rsCosh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'cosh'); }
/**
 * Arcsine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_asin`
 * @example
 * ```ts
 * import { QQ, ring, rsAsin } from '@symjs/symjs';
 *
 * const [, x] = ring('x, y', QQ);
 * rsAsin(x, x, 8); // => 5/112*x**7 + 3/40*x**5 + 1/6*x**3 + x
 * ```
 */
export function rsAsin(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'asin'); }
/**
 * Inverse hyperbolic sine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_asinh`
 * @example
 * ```ts
 * import { QQ, ring, rsAsinh } from '@symjs/symjs';
 *
 * const [, x] = ring('x', QQ);
 * rsAsinh(x, x, 9); // => -5/112*x**7 + 3/40*x**5 - 1/6*x**3 + x
 * ```
 */
export function rsAsinh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'asinh'); }
/**
 * Arctangent series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_atan`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsAtan } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsAtan(R.fromExpr(ex`x*y + x`), x, 4); // => -1/3*x**3*y**3 - x**3*y**2 - x**3*y - 1/3*x**3 + x*y + x
 * ```
 */
export function rsAtan(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'atan'); }
/**
 * Inverse hyperbolic tangent series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_atanh`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsAtanh } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsAtanh(R.fromExpr(ex`x*y + x`), x, 4); // => 1/3*x**3*y**3 + x**3*y**2 + x**3*y + 1/3*x**3 + x*y + x
 * ```
 */
export function rsAtanh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'atanh'); }
/**
 * Principal Lambert W series at zero.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_LambertW`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsLambertW } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsLambertW(R.fromExpr(ex`x*y + x`), x, 3); // => -x**2*y**2 - 2*x**2*y - x**2 + x*y + x
 * ```
 */
export function rsLambertW(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return analytic(p, x, prec, 'LambertW'); }
/**
 * Tangent series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_tan`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsTan } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsTan(R.fromExpr(ex`x*y + x`), x, 4); // => 1/3*x**3*y**3 + x**3*y**2 + x**3*y + 1/3*x**3 + x*y + x
 * ```
 */
export function rsTan(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return tangent(p, x, prec, false); }
/**
 * Hyperbolic tangent series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_tanh`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsTanh } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsTanh(R.fromExpr(ex`x*y + x`), x, 4); // => -1/3*x**3*y**3 - x**3*y**2 - x**3*y - 1/3*x**3 + x*y + x
 * ```
 */
export function rsTanh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly { return tangent(p, x, prec, true); }

/** Split off all terms independent of the series generator. */
function constantPart(p: PuiseuxPoly, i: number): PuiseuxPoly {
  return p.ring.fromDict(p.terms().filter(([m]) => at(m, i).isZero));
}

/** Coerce function values of the constant term, adjoining formal generators if needed. */
function adjoinValues(p: SeriesPoly, tail: PuiseuxPoly, values: readonly Expr[]): [SeriesPoly, PuiseuxPoly, PuiseuxPoly[]] {
  const missing = values.filter((value) => {
    try { tail.ring.fromExpr(value); return false; }
    catch (error) {
      if (!(error instanceof CoercionFailed || error instanceof RangeError)) throw error;
      return true;
    }
  });
  if (missing.length === 0) return [p, tail, values.map((value) => tail.ring.fromExpr(value))];
  const template = p instanceof PuiseuxPoly
    ? new PuiseuxRing([...p.ring.symbols, ...missing], p.ring.domain).one
    : p.ring.addGens(missing).one;
  const ring = lift(template).ring;
  return [template, ring.fromExpr(tail.asExpr()), values.map((value) => ring.fromExpr(value))];
}

function tangent(p: SeriesPoly, x: SeriesPoly, prec: ExprLike, hyperbolic: boolean): SeriesPoly {
  const q = lift(p), i = index(p, x), order = rat(prec);
  const constant = constantPart(q, i);
  const [template, tail, values] = constant.isZero
    ? [p, q, [q.ring.zero]] as const
    : adjoinValues(p, q.sub(constant), [fn(hyperbolic ? 'tanh' : 'tan', [constant.asExpr()])]);
  const sine = composePositive(tail, i, order, (k) => analyticCoefficient(hyperbolic ? 'sinh' : 'sin', k));
  const cosine = composePositive(tail, i, order, (k) => analyticCoefficient(hyperbolic ? 'cosh' : 'cos', k));
  const t = product(sine, rationalPower(cosine, minusOne, i, order), i, order);
  if (constant.isZero) return restore(template, t);
  const c = first(values), ct = c.mul(t);
  const denominator = hyperbolic ? tail.ring.one.add(ct) : tail.ring.one.sub(ct);
  return restore(template, product(c.add(t), rationalPower(denominator, minusOne, i, order), i, order));
}
/**
 * Cotangent Laurent series, computing enough terms before inversion.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_cot`
 * @example
 * ```ts
 * import { QQ, ring, rsCot } from '@symjs/symjs';
 *
 * const [, x] = ring('x, y', QQ);
 * rsCot(x, x, 6); // => -2/945*x**5 - 1/45*x**3 - 1/3*x + x**(-1)
 * ```
 */
export function rsCot(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const v = valuation(lift(p), index(p, x));
  const order = plus(rat(prec), times(Rational.of(2), v));
  return rsSeriesInversion(rsTan(p, x, order), x, prec);
}
/**
 * Logarithmic series for a nonzero ground constant.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @throws NotImplementedError when the expansion would contain a logarithmic term.
 * @see SymPy `sympy.polys.ring_series.rs_log`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing, rsLog } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x', QQ);
 * rsLog(R.fromExpr(ex`x + 1`), x, 8); // => x + -1/2*x**2 + 1/3*x**3 + -1/4*x**4 + 1/5*x**5 + -1/6*x**6 + 1/7*x**7
 * rsLog(R.fromExpr(ex`x**(3/2) + 1`), x, 5); // => x**(3/2) + -1/2*x**3 + 1/3*x**(9/2)
 * ```
 */
export function rsLog(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), [v, c, tail] = normalize(q, i);
  if (!v.isZero) throw new NotImplementedError('the logarithm contains log(x)');
  const result = composePositive(tail, i, rat(prec), (k) => k ? Rational.of(k % 2 ? 1 : -1, k) : q.ring.domainNew(fn('log', [q.ring.domain.toSympy(c)])));
  return restore(p, result);
}

/**
 * Finite composition sum(c[k]*p**k) with truncation.
 *
 * @param p - Input series.
 * @param c - Coefficients in ascending powers of the input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_series_from_list`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsSeriesFromList } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsSeriesFromList(R.fromExpr(ex`x**2 + x + 1`), [1, 2, 3], x, 4); // => 6*x**3 + 11*x**2 + 8*x + 6
 * ```
 */
export function rsSeriesFromList(p: SeriesPoly, c: readonly ExprLike[], x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), order = rat(prec);
  let result = q.ring.zero;
  c.forEach((coefficient, k) => { result = result.add(integerPower(q, BigInt(k), i, order).mul(coefficient)); });
  return restore(p, result);
}
/**
 * Simultaneous substitution; replacements are not substituted into one another.
 *
 * @param p - Input series.
 * @param rules - Generator and replacement series pairs.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @throws RangeError when a substitution divides by the zero series.
 * @see SymPy `sympy.polys.ring_series.rs_subs`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsSubs } from '@symjs/symjs';
 *
 * const [R, x, y] = ring('x, y', QQ);
 * rsSubs(R.fromExpr(ex`x**2 + y**2`), new Map([[x, R.fromExpr(ex`x + y`)], [y, R.fromExpr(ex`x + 2*y`)]]), x, 3); // => 2*x**2 + 6*x*y + 5*y**2
 * rsSubs(R.fromExpr(ex`x**2 + y**2`), new Map([[x, R.fromExpr(ex`x + y`)]]), x, 3); // => x**2 + 2*x*y + 2*y**2
 * ```
 */
export function rsSubs(p: SeriesPoly, rules: ReadonlyMap<SeriesPoly, SeriesPoly>, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), order = rat(prec), replacements = new Map<number, PuiseuxPoly>();
  for (const [a, b] of rules) replacements.set(index(p, a), q.ring.ringNew(lift(b)));
  let result = q.ring.zero;
  for (const [m, c] of q.terms()) {
    const factors = m.map((exponent, j) => ({ exponent, base: replacements.get(j) ?? at(q.ring.gens, j) })).filter(({ exponent }) => !exponent.isZero);
    if (factors.some(({ base, exponent }) => base.isZero && exponent.isNegative)) throw new RangeError('substitution divides by the zero series');
    if (factors.some(({ base, exponent }) => base.isZero && exponent.isPositive)) continue;
    const valuations = factors.map(({ base, exponent }) => times(valuation(base, i), exponent));
    let remaining = valuations.reduce(plus, zero), term = q.ring.groundNew(c);
    factors.forEach(({ base, exponent }, j) => {
      const precision = plus(minus(order, valuations.reduce(plus, zero)), at(valuations, j));
      let power: PuiseuxPoly;
      if (base.isTerm) {
        // Unchanged parameter generators can carry fractional powers too;
        // they do not need inversion in the selected series variable.
        const [monom, coefficient] = first(base.terms());
        power = q.ring.fromDict([[monom.map((e) => times(e, exponent)), q.ring.domainNew(pow(coefficient, exponent))]]);
      } else power = exponent.isInteger && exponent.isPositive ? integerPower(base, exponent.p, i, precision) : rationalPower(base, exponent, i, precision);
      remaining = minus(remaining, at(valuations, j));
      term = product(term, power, i, minus(order, remaining));
    });
    result = result.add(trunc(term, i, order));
  }
  return restore(p, result);
}
/**
 * Revert p(x)=y with a scalar nonzero coefficient of x.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param nIn - Truncation order of the inverse series.
 * @param y - Generator in which to express the inverse.
 * @returns The resulting truncated series.
 * @throws RangeError when the requested series order is not positive or the constant term is nonzero.
 * @throws NotImplementedError when the exponents for reversion are not integers or the linear coefficient is zero or is not a scalar.
 * @see SymPy `sympy.polys.ring_series.rs_series_reversion`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsSeriesReversion } from '@symjs/symjs';
 *
 * const [R, x, y] = ring('x, y, a, b', QQ);
 * rsSeriesReversion(R.fromExpr(ex`2*a*b*x**2 - 2*b*x**2 - x**2 + x`), x, 3, y); // => -2*y**2*a*b + 2*y**2*b + y**2 + y
 * ```
 */
export function rsSeriesReversion(p: SeriesPoly, x: SeriesPoly, nIn: IntLike, y: SeriesPoly): SeriesPoly {
  const n = intArg(nIn);
  const q = lift(p), i = index(p, x), j = index(p, y);
  if (!Number.isSafeInteger(n) || n < 1) throw new RangeError('the series order must be positive');
  if (rsIsPuiseux(p, x)) throw new NotImplementedError('reversion requires integer exponents');
  if (q.terms().some(([m]) => at(m, i).isZero)) throw new RangeError('the series must have no constant term');
  const leading = q.ring.fromDict(q.terms().filter(([m]) => at(m, i).isOne));
  const a = leading.get(q.ring.zeroMonom.map((e, k) => k === i ? one : e));
  if (leading.length !== 1 || groundIsZero(q.ring.domain, a)) throw new NotImplementedError('reversion requires a nonzero scalar linear coefficient');
  let result = lift(y).truediv(a);
  for (let k = 2; k < n; k++) {
    const composed = lift(rsSubs(q, new Map([[lift(x), result]]), lift(y), k + 1));
    result = result.sub(q.ring.fromDict(composed.terms().filter(([m]) => at(m, j).key === Rational.of(k).key)).truediv(a));
  }
  return restore(p, trunc(result, j, Rational.of(n)));
}
/**
 * Transfer an ordinary-series algorithm to a fractional exponent lattice.
 *
 * @param f - Series function to apply.
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @see SymPy `sympy.polys.ring_series.rs_puiseux`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing, rsExp, rsPuiseux } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x', QQ);
 * rsPuiseux(rsExp, R.fromExpr(ex`x**(2/5) + x**(2/3) + x`), x, 1); // => 1 + x**(2/5) + x**(2/3) + 1/2*x**(4/5)
 * ```
 */
export function rsPuiseux(f: SeriesFunction, p: SeriesPoly, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const i = index(p, x), denominator = lift(p).monoms().reduce((n, m) => lcm(n, at(m, i).q), 1n);
  const scaled = powXin(p, i, Rational.of(denominator));
  return powXin(f(scaled, x, times(rat(prec), Rational.of(denominator))), i, Rational.of(1, denominator));
}
/**
 * Compose a univariate series algorithm with a multivariate input.
 *
 * @param p - Input series.
 * @param f - Function whose univariate series is to be composed with the input.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @throws NotImplementedError when the substituted tail has nonpositive valuation.
 * @see SymPy `sympy.polys.ring_series.rs_fun`
 * @example
 * ```ts
 * import { QQ, ring, rsFun, rsTan } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsFun(x, rsTan, x, 4).asExpr(); // => x**3/3 + x
 * ```
 */
export function rsFun(p: SeriesPoly, f: SeriesFunction, x: SeriesPoly, prec: ExprLike): SeriesPoly {
  const q = lift(p), i = index(p, x), constant = q.get(q.ring.zeroMonom), tail = q.sub(constant);
  const r = new PuiseuxRing([new Dummy('t')], q.ring.domain), t = first(r.gens);
  const order = rat(prec);
  const v = tail.isZero ? one : valuation(tail, i);
  if (!v.isPositive) throw new NotImplementedError('composition requires positive valuation');
  const count = Number((order.p * v.q + order.q * v.p - 1n) / (order.q * v.p));
  const expansion = lift(f(t.add(constant), t, Math.max(1, count)));
  return restore(p, lift(rsSeriesFromList(tail, Array.from({ length: Math.max(1, count) }, (_, k) => expansion.get([k])), at(q.ring.gens, i), prec)));
}
/**
 * Coefficientwise division/multiplication by factorials.
 *
 * @param p - Input series.
 * @param inverse - Multiply by factorials instead of dividing by them.
 * @returns The resulting truncated series.
 * @throws NotImplementedError when the coefficient domain is not the rational field.
 * @throws RangeError when an exponent is negative or nonintegral.
 * @see SymPy `sympy.polys.ring_series.rs_hadamard_exp`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsHadamardExp } from '@symjs/symjs';
 *
 * const [R] = ring('x', QQ);
 * rsHadamardExp(R.fromExpr(ex`x**3 + x**2 + x + 1`)); // => 1/6*x**3 + 1/2*x**2 + x + 1
 * ```
 */
export function rsHadamardExp(p: SeriesPoly, inverse = false): SeriesPoly {
  const q = lift(p);
  if (q.ring.domain !== QQ) throw new NotImplementedError('Hadamard exponential requires QQ');
  return restore(p, q.ring.fromDict(q.terms().map(([m, c]) => {
    const e = first(m);
    if (!e.isInteger || e.isNegative) throw new RangeError('factorial weights require nonnegative integer exponents');
    const f = factorial(Number(e.p));
    return [m, inverse ? c.mul(Rational.of(f)) : c.div(Rational.of(f))];
  })));
}
/**
 * Newton power-sum generating series of a univariate polynomial.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @throws RangeError when the polynomial is zero or multivariate.
 * @see SymPy `sympy.polys.ring_series.rs_newton`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsNewton } from '@symjs/symjs';
 *
 * const [R, x] = ring('x', QQ);
 * rsNewton(R.fromExpr(ex`x**2 - 2`), x, 5); // => 8*x**4 + 4*x**2 + 2
 * ```
 */
export function rsNewton(p: PolyElement, x: PolyElement, prec: ExprLike): SeriesPoly {
  if (p.ring.ngens !== 1 || p.isZero) throw new RangeError('Newton sums require a nonzero univariate polynomial');
  const degree = p.degree(), reversed = p.ring.fromTerms(p.listterms().map(([m, c]) => [[degree - first(m)], c]));
  const q = lift(p);
  return restore(p, q.ring.groundNew(degree).sub(lift(rsMul(rsDiff(reversed, x), rsSeriesInversion(reversed, x, prec), x, prec)).mul(lift(x))));
}
/**
 * Polynomial whose roots are all pairwise sums of roots.
 *
 * @param p - Input series.
 * @param q - Second input series.
 * @returns The resulting ring element.
 * @throws RangeError when the polynomials are zero or are not in the same univariate ring.
 * @see SymPy `sympy.polys.ring_series.rs_compose_add`
 * @example
 * ```ts
 * import { QQ, ex, ring, rsComposeAdd } from '@symjs/symjs';
 *
 * const [R] = ring('x', QQ);
 * rsComposeAdd(R.fromExpr(ex`x**2 - 2`), R.fromExpr(ex`x**2 - 3`)); // => x**4 - 10*x**2 + 1
 * ```
 */
export function rsComposeAdd(p: PolyElement, q: PolyElement): PolyElement {
  if (!p.ring.equals(q.ring) || p.ring.ngens !== 1 || p.isZero || q.isZero) throw new RangeError('expected nonzero polynomials in the same univariate ring');
  const x = first(p.ring.gens), degree = p.degree() * q.degree(), prec = degree + 1;
  const sums = lift(rsHadamardExp(rsMul(rsHadamardExp(rsNewton(p, x, prec)), rsHadamardExp(rsNewton(q, x, prec)), x, prec), true));
  const integrand = shift(sums.ring.groundNew(sums.get([0])).sub(sums), 0, minusOne);
  const exponential = lift(rsExp(restore(p, integral(integrand, 0)), x, prec));
  return p.ring.fromTerms(exponential.terms().map(([m, c]) => [[degree - Number(first(m).p)], c])).primitive()[1];
}
/**
 * Expand an expression at zero and return its finite polynomial/Puiseux part.
 *
 * @param expr - Expression to convert.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns The resulting truncated series.
 * @throws NotImplementedError when the expansion does not give a finite Puiseux series.
 * @see SymPy `sympy.polys.ring_series.rs_series`
 * @example
 * ```ts
 * import { ex, rsSeries, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * rsSeries(ex`sin(x) + exp(x)`, x, 5).asExpr(); // => x**4/24 + x**2/2 + 2*x + 1
 * ```
 */
export function rsSeries(expr: ExprLike, x: Sym, prec: IntLike): SeriesPoly {
  const expanded = expand(removeO(series(sympify(expr), x, 0, intArg(prec))));
  const generators = new Map<string, Expr>([[x.key, x]]);
  const collect = (e: Expr): void => {
    if (e instanceof Rational || e instanceof Float || e.key === x.key) return;
    if (e instanceof Add || e instanceof Mul) { e.args.forEach(collect); return; }
    if (e instanceof Pow && e.exp instanceof Rational && (e.has(x) || e.exp.isInteger)) { collect(e.base); return; }
    if (e.has(x)) throw new NotImplementedError('the expression did not expand into a finite Puiseux series');
    generators.set(e.key, e);
  };
  collect(expanded);
  const symbols = [...generators.values()], p = new PuiseuxRing(symbols, QQ).fromExpr(expanded);
  return restore(new PolyRing(symbols, QQ).zero, p);
}

/**
 * Cosine and sine series to the same precision.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns Cosine and sine series to the same precision.
 * @see SymPy `sympy.polys.ring_series.rs_cos_sin`
 * @remarks SymPy returns `(-1/2*x**2*y**2 - x**2*y - 1/2*x**2 + 1, -1/6*x**3*y**3 - 1/2*x**3*y**2 - 1/2*x**3*y - 1/6*x**3 + x*y + x)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { QQ, ex, ring, rsCosSin } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsCosSin(R.fromExpr(ex`x*y + x`), x, 4); // => [-1/2*x**2*y**2 - x**2*y - 1/2*x**2 + 1, -1/6*x**3*y**3 - 1/2*x**3*y**2 - 1/2*x**3*y - 1/6*x**3 + x*y + x]
 * ```
 */
export function rsCosSin(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): [SeriesPoly, SeriesPoly] {
  return cosineSine(p, x, prec, false);
}
/**
 * Hyperbolic cosine and sine series.
 *
 * @param p - Input series.
 * @param x - Generator with respect to which the series is expanded.
 * @param prec - Truncation order in the series variable.
 * @returns Hyperbolic cosine and sine series.
 * @see SymPy `sympy.polys.ring_series.rs_cosh_sinh`
 * @remarks SymPy returns `(1/2*x**2*y**2 + x**2*y + 1/2*x**2 + 1, 1/6*x**3*y**3 + 1/2*x**3*y**2 + 1/2*x**3*y + 1/6*x**3 + x*y + x)` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { QQ, ex, ring, rsCoshSinh } from '@symjs/symjs';
 *
 * const [R, x] = ring('x, y', QQ);
 * rsCoshSinh(R.fromExpr(ex`x*y + x`), x, 4); // => [1/2*x**2*y**2 + x**2*y + 1/2*x**2 + 1, 1/6*x**3*y**3 + 1/2*x**3*y**2 + 1/2*x**3*y + 1/6*x**3 + x*y + x]
 * ```
 */
export function rsCoshSinh(p: SeriesPoly, x: SeriesPoly, prec: ExprLike): [SeriesPoly, SeriesPoly] {
  return cosineSine(p, x, prec, true);
}

function cosineSine(p: SeriesPoly, x: SeriesPoly, prec: ExprLike, hyperbolic: boolean): [SeriesPoly, SeriesPoly] {
  const q = lift(p), i = index(p, x), order = rat(prec);
  const constant = constantPart(q, i);
  const sinName = hyperbolic ? 'sinh' : 'sin', cosName = hyperbolic ? 'cosh' : 'cos';
  if (constant.isZero) return hyperbolic ? [rsCosh(p, x, prec), rsSinh(p, x, prec)] : [rsCos(p, x, prec), rsSin(p, x, prec)];
  const value = constant.asExpr();
  const [template, tail, coefficients] = adjoinValues(p, q.sub(constant), [fn(sinName, [value]), fn(cosName, [value])]);
  const [s, c] = [at(coefficients, 0), at(coefficients, 1)];
  const sinTail = composePositive(tail, i, order, (k) => analyticCoefficient(sinName, k));
  const cosTail = composePositive(tail, i, order, (k) => analyticCoefficient(cosName, k));
  const cin = cosTail.mul(c), sin = sinTail.mul(s);
  return [
    restore(template, hyperbolic ? cin.add(sin) : cin.sub(sin)),
    restore(template, cosTail.mul(s).add(sinTail.mul(c))),
  ];
}
