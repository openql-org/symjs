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
import { pmod } from '../ntheory/intutil';
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
 * The linear convolution of two integer sequences (SymPy convolution_int).
 * Like SymPy's packing into one integer, the result ends at the last nonzero
 * term ([0] when every term is 0), and an empty sequence raises SymPy's error.
 */
function convolutionInt(a: readonly bigint[], b: readonly bigint[]): bigint[] {
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
 * Convolution of two sequences, of the kind the options select (SymPy
 * convolution): linear convolution by FFT by default (exact, or numeric
 * with `dps`), modulo a prime by NTT with `prime`, dyadic with
 * `{ dyadic: true }` and subset convolution with `{ subset: true }`; at
 * most one of them may be given. `cycle` gives the length of a cyclic
 * convolution. The results modulo a prime are bigints.
 *
 * `convolution([1, 2, 3], [4, 5, 6], { cycle: 3 })` is `[31, 31, 28]`.
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
 * Linear convolution by the Fast Fourier Transform (SymPy convolution_fft);
 * exact by default, numeric with `{ dps }` decimal digits.
 *
 * `convolutionFft([2, 5], [6, 7, 3])` is `[12, 44, 41, 15]`.
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
 * Linear convolution modulo a prime of the form m*2**k + 1 by the Number
 * Theoretic Transform (SymPy convolution_ntt); the results are bigints.
 *
 * `convolutionNtt([2, 5], [6, 7, 3], 19*2**10 + 1)` is `[12n, 44n, 41n, 15n]`.
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
 * Dyadic (bitwise-XOR) convolution by the Fast Walsh Hadamard Transform
 * (SymPy convolution_fwht); padded to the right with zeros to a power of 2.
 *
 * `convolutionFwht([u, v], [x, y])` is `[u*x + v*y, u*y + v*x]`.
 */
export function convolutionFwht(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  return ifwht(pointwise(fwht(ab[0]), fwht(ab[1])));
}

/**
 * Subset convolution, with the indices as bitmasks of subsets of a finite
 * set (SymPy convolution_subset): entry `mask` of the result is the sum of
 * a[s]*b[mask^s] over the subsets s of mask. Padded to the right with zeros
 * to a power of 2.
 *
 * `convolutionSubset([u, v], [x, y])` is `[u*x, u*y + v*x]`.
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
 * The covering product (SymPy covering_product): the sums of the products
 * of the entries grouped by the bitwise OR of their indices. Padded to the
 * right with zeros to a power of 2.
 *
 * `coveringProduct([u, v], [x, y])` is `[u*x, u*y + v*x + v*y]`.
 */
export function coveringProduct(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  return inverseMobiusTransform(pointwise(mobiusTransform(ab[0]), mobiusTransform(ab[1])));
}

/**
 * The intersecting product (SymPy intersecting_product): the sums of the
 * products of the entries grouped by the bitwise AND of their indices.
 * Padded to the right with zeros to a power of 2.
 *
 * `intersectingProduct([u, v], [x, y])` is `[u*x + u*y + v*x, v*y]`.
 */
export function intersectingProduct(a: Iterable<ExprLike>, b: Iterable<ExprLike>): Expr[] {
  const ab = padPair(a, b);
  if (!ab) return [];
  const sup = { subset: false };
  return inverseMobiusTransform(pointwise(mobiusTransform(ab[0], sup), mobiusTransform(ab[1], sup)), sup);
}
