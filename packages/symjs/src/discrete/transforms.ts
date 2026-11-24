// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sympy/discrete/transforms.py, Copyright (c) SymPy Development Team, BSD-3-Clause (see LICENSE).

/**
 * @file Discrete transforms (SymPy sympy.discrete.transforms): the Discrete
 * Fourier Transform (fft, ifft), the Number Theoretic Transform (ntt, intt),
 * the Walsh Hadamard Transform (fwht, ifwht) and the Mobius Transform for
 * the subset lattice (mobiusTransform, inverseMobiusTransform).
 *
 * Sequences are padded to the right with zeros to a power of 2. Symbolic
 * results are arrays of expressions; the results of the Number Theoretic
 * Transform are arrays of bigints (Python ints in SymPy).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { I, Rational, S, Sym, pi } from '../core/nodes';
import { at, expectType } from '../core/guard';
import { atoms } from '../core/methods';
import { add, div, mul, sub, sympify } from '../core/ops';
import { cos, sin } from '../functions/elementary/elementary';
import { evalf } from '../numeric/evalf';
import type { IntLike } from '../ntheory/intutil';
import { pmod, powmod } from '../ntheory/intutil';
import { isprime } from '../ntheory/primetest';
import { primitiveRoot } from '../ntheory/residue';
import { expandMul } from '../simplify/expand';
import { iterable } from '../utilities/iterables';

/** The smallest power of 2 that is at least n (n itself when it is one), as SymPy pads. */
export function padLength(n: number): number {
  let m = 1;
  while (m < n) m *= 2;
  return m;
}

/**
 * The integer value of an input like SymPy's as_int, which raises
 * ValueError (a RangeError here) with SymPy's message for a non-integer.
 */
export function asIntValue(n: IntLike): bigint {
  if (typeof n === 'bigint') return n;
  if (typeof n === 'number') {
    if (Number.isInteger(n)) return BigInt(n);
    throw new RangeError(`${n} is not an integer`);
  }
  const e = sympify(n);
  if (e instanceof Rational && e.q === 1n) return e.p;
  throw new RangeError(`${e.toString()} is not an integer`);
}

/** The bit reversal of i on b bits (SymPy int(ibin(i, b, str=True)[::-1], 2)). */
function bitReverse(i: number, b: number): number {
  let r = 0;
  for (let k = 0; k < b; k++) r = (r << 1) | ((i >> k) & 1);
  return r;
}

/** Swap the entries of a into bit-reversed order (a has a power-of-2 length n = 2**b). */
function bitReversePermute<T>(a: T[], b: number): void {
  for (let i = 1; i < a.length; i++) {
    const j = bitReverse(i, b);
    if (i < j) {
      const t = at(a, i);
      a[i] = at(a, j);
      a[j] = t;
    }
  }
}

/** The sympified elements of a sequence; a TypeError with `message` when it is not iterable. */
export function sympifySeq(seq: Iterable<ExprLike>, message: string): Expr[] {
  if (!iterable(seq)) throw new TypeError(message);
  return Array.from(seq, (x) => sympify(x));
}

/** Pad a with zeros to length n. */
function padZeros(a: Expr[], n: number): void {
  while (a.length < n) a.push(S.Zero);
}

/** Utility function for the Discrete Fourier Transform (SymPy _fourier_transform). */
function fourierTransform(seq: Iterable<ExprLike>, dps: number | undefined, inverse: boolean): Expr[] {
  const a = sympifySeq(seq, 'Expected a sequence of numeric coefficients for Fourier Transform');
  if (a.some((x) => atoms(x, (t) => t instanceof Sym).length > 0)) throw new RangeError('Expected non-symbolic coefficients');
  if (a.length < 2) return a;
  const n = padLength(a.length);
  const b = Math.log2(n);
  padZeros(a, n);
  bitReversePermute(a, b);

  let ang = div(mul(inverse ? -2 : 2, pi), n);
  if (dps !== undefined) ang = evalf(ang, dps + 2);
  const w: Expr[] = [];
  for (let i = 0; i < n / 2; i++) w.push(add(cos(mul(ang, i)), mul(I, sin(mul(ang, i)))));

  for (let h = 2; h <= n; h *= 2) {
    const hf = h / 2;
    const ut = n / h;
    for (let i = 0; i < n; i += h) {
      for (let j = 0; j < hf; j++) {
        const u = at(a, i + j);
        const v = expandMul(mul(at(a, i + j + hf), at(w, ut * j)));
        a[i + j] = add(u, v);
        a[i + j + hf] = sub(u, v);
      }
    }
  }

  if (!inverse) return a;
  return dps !== undefined ? a.map((x) => evalf(div(x, n), dps)) : a.map((x) => div(x, n));
}

/** Options of {@link fft} and {@link ifft}. */
export interface FftOptions {
  /** The number of decimal digits of precision (numeric transform); exact when omitted. */
  dps?: number;
}

/**
 * Computes the discrete Fourier transform, padding with zeros to a power of two.
 * @param seq - The sequence of input coefficients.
 * @param opts - The settings described by {@link FftOptions}.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @throws RangeError when an input coefficient contains a free symbol.
 * @see SymPy `sympy.discrete.transforms.fft`
 * @example
 * ```ts
 * import { fft } from '@symjs/symjs';
 * fft([1, 2, 3, 4]); // => [10, -2 - 2*I, -2, -2 + 2*I]
 * ```
 */
export function fft(seq: Iterable<ExprLike>, opts: FftOptions = {}): Expr[] {
  return fourierTransform(seq, opts.dps, false);
}

/**
 * Computes the inverse discrete Fourier transform, padding with zeros to a power of two.
 * @param seq - The sequence of input coefficients.
 * @param opts - The settings described by {@link FftOptions}.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @throws RangeError when an input coefficient contains a free symbol.
 * @see SymPy `sympy.discrete.transforms.ifft`
 * @example
 * ```ts
 * import { ifft } from '@symjs/symjs';
 * ifft([1, 2, 3, 4]); // => [5/2, -1/2 + I/2, -1/2, -1/2 - I/2]
 * ```
 */
export function ifft(seq: Iterable<ExprLike>, opts: FftOptions = {}): Expr[] {
  return fourierTransform(seq, opts.dps, true);
}

/** Utility function for the Number Theoretic Transform (SymPy _number_theoretic_transform). */
function numberTheoreticTransform(seq: Iterable<IntLike>, prime: IntLike, inverse: boolean): bigint[] {
  if (!iterable(seq)) throw new TypeError('Expected a sequence of integer coefficients for Number Theoretic Transform');
  const p = asIntValue(prime);
  if (!isprime(p)) throw new RangeError('Expected prime modulus for Number Theoretic Transform');
  const a = Array.from(seq, (x) => pmod(asIntValue(x), p));
  if (a.length < 1) return a;
  const n = padLength(a.length);
  const bn = BigInt(n);
  if ((p - 1n) % bn !== 0n) throw new RangeError('Expected prime modulus of the form (m*2**k + 1)');
  while (a.length < n) a.push(0n);
  bitReversePermute(a, Math.log2(n));

  const pr = expectType(primitiveRoot(p), (v): v is bigint => typeof v === 'bigint', 'primitive root');
  let rt = powmod(pr, (p - 1n) / bn, p);
  if (inverse) rt = powmod(rt, p - 2n, p);
  const w: bigint[] = [1n];
  for (let i = 1; i < n / 2; i++) w.push((at(w, i - 1) * rt) % p);

  for (let h = 2; h <= n; h *= 2) {
    const hf = h / 2;
    const ut = n / h;
    for (let i = 0; i < n; i += h) {
      for (let j = 0; j < hf; j++) {
        const u = at(a, i + j);
        const v = at(a, i + j + hf) * at(w, ut * j);
        a[i + j] = pmod(u + v, p);
        a[i + j + hf] = pmod(u - v, p);
      }
    }
  }

  if (!inverse) return a;
  const rv = powmod(bn, p - 2n, p);
  return a.map((x) => (x * rv) % p);
}

/**
 * Computes the discrete Fourier transform modulo a prime, padding to a power of two.
 * @param seq - The sequence of input coefficients.
 * @param prime - The prime modulus, with the padded transform length dividing its predecessor.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @throws RangeError when the coefficients are nonintegral or the prime modulus does not admit the padded transform length.
 * @see SymPy `sympy.discrete.transforms.ntt`
 * @example
 * ```ts
 * import { ntt } from '@symjs/symjs';
 * ntt([1, 2, 3, 4], 769); // => [10, 643, 767, 122]
 * ```
 */
export function ntt(seq: Iterable<IntLike>, prime: IntLike): bigint[] {
  return numberTheoreticTransform(seq, prime, false);
}

/**
 * Computes the inverse discrete Fourier transform modulo a prime.
 * @param seq - The sequence of input coefficients.
 * @param prime - The prime modulus, with the padded transform length dividing its predecessor.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @throws RangeError when the coefficients are nonintegral or the prime modulus does not admit the padded transform length.
 * @see SymPy `sympy.discrete.transforms.intt`
 * @example
 * ```ts
 * import { intt } from '@symjs/symjs';
 * intt([1, 2, 3, 4], 769); // => [387, 415, 384, 353]
 * ```
 */
export function intt(seq: Iterable<IntLike>, prime: IntLike): bigint[] {
  return numberTheoreticTransform(seq, prime, true);
}

/** Utility function for the Walsh Hadamard Transform (SymPy _walsh_hadamard_transform). */
function walshHadamardTransform(seq: Iterable<ExprLike>, inverse: boolean): Expr[] {
  const a = sympifySeq(seq, 'Expected a sequence of coefficients for Walsh Hadamard Transform');
  if (a.length < 2) return a;
  const n = padLength(a.length);
  padZeros(a, n);
  for (let h = 2; h <= n; h *= 2) {
    const hf = h / 2;
    for (let i = 0; i < n; i += h) {
      for (let j = 0; j < hf; j++) {
        const u = at(a, i + j);
        const v = at(a, i + j + hf);
        a[i + j] = add(u, v);
        a[i + j + hf] = sub(u, v);
      }
    }
  }
  return inverse ? a.map((x) => div(x, n)) : a;
}

/**
 * Computes the Walsh–Hadamard transform in Hadamard order.
 * @param seq - The sequence of input coefficients.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @see SymPy `sympy.discrete.transforms.fwht`
 * @example
 * ```ts
 * import { fwht } from '@symjs/symjs';
 * fwht([4, 2, 2, 0, 0, 2, -2, 0]); // => [8, 0, 8, 0, 8, 8, 0, 0]
 * ```
 */
export function fwht(seq: Iterable<ExprLike>): Expr[] {
  return walshHadamardTransform(seq, false);
}

/**
 * Computes the inverse Walsh–Hadamard transform in Hadamard order.
 * @param seq - The sequence of input coefficients.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @see SymPy `sympy.discrete.transforms.ifwht`
 * @example
 * ```ts
 * import { ifwht } from '@symjs/symjs';
 * ifwht([8, 0, 8, 0, 8, 8, 0, 0]); // => [4, 2, 2, 0, 0, 2, -2, 0]
 * ```
 */
export function ifwht(seq: Iterable<ExprLike>): Expr[] {
  return walshHadamardTransform(seq, true);
}

/** Utility function for the Mobius Transform by Yates's dynamic programming method (SymPy _mobius_transform). */
function mobiusTransformImpl(seq: Iterable<ExprLike>, sgn: 1 | -1, subset: boolean): Expr[] {
  const a = sympifySeq(seq, 'Expected a sequence of coefficients');
  if (a.length < 2) return a;
  const n = padLength(a.length);
  padZeros(a, n);
  for (let i = 1; i < n; i *= 2) {
    for (let j = 0; j < n; j++) {
      // subsets: add the entry without bit i to the one with it; supersets: the other way round
      if (((j & i) !== 0) === subset) a[j] = add(at(a, j), mul(sgn, at(a, j ^ i)));
    }
  }
  return a;
}

/** Options of {@link mobiusTransform} and {@link inverseMobiusTransform}. */
export interface MobiusTransformOptions {
  /** Enumerate the subsets (default true) or the supersets (false) of each index. */
  subset?: boolean;
}

/**
 * The Mobius Transform for the subset lattice, with the indices of the
 * sequence as bitmasks: entry i of the result is
 * the sum of the entries whose index is a subset of i (with
 * `{ subset: false }`, a superset of i). The sequence is padded to the
 * right with zeros to a power of 2.
 * @param seq - The sequence of input coefficients.
 * @param opts - The settings described by {@link MobiusTransformOptions}.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @see SymPy `sympy.discrete.transforms.mobius_transform`
 * @example
 * ```ts
 * import { mobiusTransform } from '@symjs/symjs';
 * mobiusTransform([1, 2, 3, 4]); // => [1, 3, 4, 10]
 * ```
 */
export function mobiusTransform(seq: Iterable<ExprLike>, opts: MobiusTransformOptions = {}): Expr[] {
  return mobiusTransformImpl(seq, 1, opts.subset ?? true);
}

/**
 * The inverse Mobius Transform for the subset lattice; see {@link mobiusTransform}.
 * @param seq - The sequence of input coefficients.
 * @param opts - The settings described by {@link MobiusTransformOptions}.
 * @returns The transformed coefficients in index order.
 * @throws TypeError when the coefficients are not iterable.
 * @see SymPy `sympy.discrete.transforms.inverse_mobius_transform`
 * @example
 * ```ts
 * import { inverseMobiusTransform } from '@symjs/symjs';
 * inverseMobiusTransform([1, 3, 4, 10]); // => [1, 2, 3, 4]
 * ```
 */
export function inverseMobiusTransform(seq: Iterable<ExprLike>, opts: MobiusTransformOptions = {}): Expr[] {
  return mobiusTransformImpl(seq, -1, opts.subset ?? true);
}
