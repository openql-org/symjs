// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sympy/discrete/convolutions.py, Copyright (c) SymPy Development Team, BSD-3-Clause (see LICENSE).

/**
 * @file Convolutions (SymPy sympy.discrete.convolutions): linear and cyclic
 * convolution by FFT, NTT and FWHT, subset convolution, covering product
 * and intersecting product.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { at } from '../core/guard';
import { add, mul } from '../core/ops';
import { lcm } from '../core/numbers';
import type { IntLike } from '../ntheory/intutil';
import { asInt, pmod } from '../ntheory/intutil';
import { expandMul } from '../simplify/expand';
import { iterable } from '../utilities/iterables';
import { asIntValue, fft, fwht, ifft, ifwht, intt, inverseMobiusTransform, mobiusTransform, ntt, padLength, sympifySeq } from './transforms';

/** Options of {@link convolution}: at most one of `dps`, `prime`, `dyadic` and `subset` selects the kind. */
export interface ConvolutionOptions {
  /** The length of a cyclic convolution (0, the default, for a linear one). */
  cycle?: IntLike;
  /** The number of decimal digits of precision of the FFT (exact when omitted). */
  dps?: number;
  /** A prime modulus of the form m*2**k + 1: convolution modulo it by NTT. */
  prime?: IntLike;
  /** Dyadic (bitwise-XOR) convolution by FWHT. */
  dyadic?: boolean;
  /** Subset convolution. */
  subset?: boolean;
}

const SEQ_MESSAGE = 'Expected a sequence of coefficients for convolution';

/** The elements of a sequence as an array; a TypeError when it is not iterable. */
function toArray<T>(seq: Iterable<T>): T[] {
  if (!iterable(seq)) throw new TypeError(SEQ_MESSAGE);
  return Array.from(seq);
}

/**
 * The integers of a sequence of JavaScript integers, bigints and non-integer
 * Rationals scaled by the lcm of the denominators, with that lcm (SymPy's
 * `loop` in convolution); undefined when another element (a Float, an
 * Integer expression, a symbol, ...) sends the sequence to the FFT.
 */
function scaledIntegers(a: readonly ExprLike[]): [bigint[], bigint] | undefined {
  let den = 1n;
  const fractions: [bigint, bigint][] = [];
  for (const x of a) {
    if (x instanceof Rational && x.q !== 1n) {
      den = lcm(den, x.q);
      fractions.push([x.p, x.q]);
    } else if (typeof x === 'bigint' || (typeof x === 'number' && Number.isInteger(x))) fractions.push([BigInt(x), 1n]);
    else return undefined;
  }
  return [fractions.map(([num, q]) => num * (den / q)), den];
}

/**
 * Computes the linear convolution of two integer sequences.
 * @param aIn - The first coefficient sequence.
 * @param bIn - The second coefficient sequence.
 * @returns The exact integer convolution coefficients.
 * @throws RangeError when the collection is empty.
 * @see SymPy `sympy.discrete.convolutions.convolution_int`
 * @example
 * ```ts
 * import { convolutionInt } from '@symjs/symjs';
 * convolutionInt([2, 3], [4, 5]); // => [8, 22, 15]
 * ```
 */
export function convolutionInt(aIn: readonly IntLike[], bIn: readonly IntLike[]): bigint[] {
  const a = aIn.map((v) => asInt(v)), b = bIn.map((v) => asInt(v));
  if (a.length === 0 || b.length === 0) throw new RangeError('max() iterable argument is empty');
  const out: bigint[] = [];
  for (let k = 0; k < a.length + b.length - 1; k++) out.push(0n);
  a.forEach((u, i) => {
    b.forEach((v, j) => {
      out[i + j] = at(out, i + j) + u * v;
    });
  });
  while (out.length > 1 && at(out, out.length - 1) === 0n) out.pop();
  return out;
}

/** The sums of the entries of ls whose indices are congruent modulo c (SymPy [sum(ls[i::c]) for i in range(c)]). */
function cyclic<T>(ls: readonly T[], c: number, zero: T, plus: (u: T, v: T) => T): T[] {
  const out: T[] = [];
  for (let i = 0; i < c; i++) out.push(zero);
  ls.forEach((x, i) => {
    out[i % c] = plus(at(out, i % c), x);
  });
  return out;
}

/**
 * Convolves two coefficient sequences using the selected transform and optionally folds the result to a cycle length.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @param opts - The cycle length and transform selection in {@link ConvolutionOptions}.
 * @returns The coefficients of the resulting product.
 * @throws RangeError when the cycle length is negative.
 * @throws TypeError when multiple convolution types are selected.
 * @see SymPy `sympy.discrete.convolutions.convolution`
 * @example
 * ```ts
 * import { convolution } from '@symjs/symjs';
 * convolution([1, 2, 3], [4, 5, 6], { cycle: 3 }); // => [31, 31, 28]
 * ```
 */
export function convolution(a: Iterable<IntLike>, b: Iterable<IntLike>, opts: ConvolutionOptions & { prime: IntLike }): bigint[];
export function convolution(a: Iterable<ExprLike>, b: Iterable<ExprLike>, opts?: ConvolutionOptions & { prime?: undefined }): Expr[];
export function convolution(a: Iterable<ExprLike>, b: Iterable<ExprLike>, opts: ConvolutionOptions = {}): Expr[] | bigint[] {
  const c = Number(asIntValue(opts.cycle ?? 0));
  if (c < 0) throw new RangeError('The length for cyclic convolution must be non-negative');
  const dyadic = opts.dyadic === true;
  const subset = opts.subset === true;
  if ([opts.prime !== undefined, opts.dps !== undefined, dyadic, subset].filter(Boolean).length > 1) {
    throw new TypeError('Ambiguity in determining the type of convolution');
  }

  if (opts.prime !== undefined) {
    const p = asIntValue(opts.prime);
    const ls = convolutionNtt(a, b, p);
    return c === 0 ? ls : cyclic(ls, c, 0n, (u, v) => u + v).map((x) => pmod(x, p));
  }

  let ls: Expr[];
  if (dyadic) ls = convolutionFwht(a, b);
  else if (subset) ls = convolutionSubset(a, b);
  else {
    const aa = toArray(a);
    const bb = toArray(b);
    const da = scaledIntegers(aa);
    const db = da && scaledIntegers(bb);
    if (da && db) {
      const den = da[1] * db[1];
      ls = convolutionInt(da[0], db[0]).map((x) => Rational.of(x, den));
    } else ls = convolutionFft(aa, bb, { dps: opts.dps });
  }
  return c === 0 ? ls : cyclic(ls, c, S.Zero, add);
}

/** The products of corresponding entries, expanded (SymPy [expand_mul(x*y) for x, y in zip(a, b)]). */
function pointwise(a: readonly Expr[], b: readonly Expr[]): Expr[] {
  return a.map((x, i) => expandMul(mul(x, at(b, i))));
}

/**
 * Computes the linear convolution of two sequences using the Fourier transform.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @param opts - Set `dps` for a numerical transform at the given decimal precision.
 * @returns The coefficients of the resulting product.
 * @see SymPy `sympy.discrete.convolutions.convolution_fft`
 * @example
 * ```ts
 * import { convolutionFft } from '@symjs/symjs';
 * convolutionFft([2, 3], [4, 5]); // => [8, 22, 15]
 * ```
 */
export function convolutionFft(a: Iterable<ExprLike>, b: Iterable<ExprLike>, opts: { dps?: number } = {}): Expr[] {
  const aa = sympifySeq(a, SEQ_MESSAGE);
  const bb = sympifySeq(b, SEQ_MESSAGE);
  const m = aa.length + bb.length - 1;
  const n = m > 0 ? padLength(m) : m;
  while (aa.length < n) aa.push(S.Zero);
  while (bb.length < n) bb.push(S.Zero);
  const fa = fft(aa, opts);
  const fb = fft(bb, opts);
  return ifft(pointwise(fa, fb), opts).slice(0, Math.max(m, 0));
}

/**
 * Computes the linear convolution modulo a prime using the number theoretic transform.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @param prime - The prime modulus, with the padded transform length dividing its predecessor.
 * @returns The coefficients of the resulting product.
 * @see SymPy `sympy.discrete.convolutions.convolution_ntt`
 * @example
 * ```ts
 * import { convolutionNtt } from '@symjs/symjs';
 * convolutionNtt([2, 3], [4, 5], 19457); // => [8, 22, 15]
 * ```
 */
export function convolutionNtt(a: Iterable<IntLike>, b: Iterable<IntLike>, prime: IntLike): bigint[] {
  const aa: IntLike[] = toArray(a);
  const bb: IntLike[] = toArray(b);
  const p = asIntValue(prime);
  const m = aa.length + bb.length - 1;
  const n = m > 0 ? padLength(m) : m;
  while (aa.length < n) aa.push(0n);
  while (bb.length < n) bb.push(0n);
  const fa = ntt(aa, p);
  const fb = ntt(bb, p);
  return intt(
    fa.map((x, i) => (x * at(fb, i)) % p),
    p,
  ).slice(0, Math.max(m, 0));
}

/** The sympified sequences a and b padded with zeros to a common power-of-2 length; undefined when one is empty. */
function padPair(a: Iterable<ExprLike>, b: Iterable<ExprLike>): [Expr[], Expr[]] | undefined {
  const aa = sympifySeq(a, SEQ_MESSAGE);
  const bb = sympifySeq(b, SEQ_MESSAGE);
  if (aa.length === 0 || bb.length === 0) return undefined;
  const n = padLength(Math.max(aa.length, bb.length));
  while (aa.length < n) aa.push(S.Zero);
  while (bb.length < n) bb.push(S.Zero);
  return [aa, bb];
}

/**
 * Convolves two sequences by grouping products according to the bitwise XOR of their indices.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @returns The coefficients of the resulting product.
 * @see SymPy `sympy.discrete.convolutions.convolution_fwht`
 * @example
 * ```ts
 * import { convolutionFwht } from '@symjs/symjs';
 * convolutionFwht([2, 3], [4, 5]); // => [23, 22]
 * ```
 */
export function convolutionFwht(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  return ifwht(pointwise(fwht(ab[0]), fwht(ab[1])));
}

/**
 * Convolves sequences indexed by subsets, summing products for disjoint pairs with the specified union.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @returns The coefficients of the resulting product.
 * @see SymPy `sympy.discrete.convolutions.convolution_subset`
 * @example
 * ```ts
 * import { convolutionSubset } from '@symjs/symjs';
 * convolutionSubset([2, 3], [4, 5]); // => [8, 22]
 * ```
 */
export function convolutionSubset(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  const [aa, bb] = ab;
  return aa.map((_, mask) => {
    let c: Expr = S.Zero;
    let smask = mask;
    while (smask > 0) {
      c = add(c, expandMul(mul(at(aa, smask), at(bb, mask ^ smask))));
      smask = (smask - 1) & mask;
    }
    return add(c, expandMul(mul(at(aa, 0), at(bb, mask))));
  });
}

/**
 * Sums products of coefficients whose index bitmasks have the specified union.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @returns The coefficients of the resulting product.
 * @see SymPy `sympy.discrete.convolutions.covering_product`
 * @example
 * ```ts
 * import { coveringProduct } from '@symjs/symjs';
 * coveringProduct([2, 3], [4, 5]); // => [8, 37]
 * ```
 */
export function coveringProduct(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  return inverseMobiusTransform(pointwise(mobiusTransform(ab[0]), mobiusTransform(ab[1])));
}

/**
 * Sums products of coefficients whose index bitmasks have the specified intersection.
 * @param a - The first coefficient sequence.
 * @param b - The second coefficient sequence.
 * @returns The coefficients of the resulting product.
 * @see SymPy `sympy.discrete.convolutions.intersecting_product`
 * @example
 * ```ts
 * import { intersectingProduct } from '@symjs/symjs';
 * intersectingProduct([2, 3], [4, 5]); // => [30, 15]
 * ```
 */
export function intersectingProduct(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  const sup = { subset: false };
  return inverseMobiusTransform(pointwise(mobiusTransform(ab[0], sup), mobiusTransform(ab[1], sup)), sup);
}
