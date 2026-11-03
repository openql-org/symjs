// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
//
// Parts ported from mpmath 1.3.0 (libmp/libelefun.py: bsp_acot, acot_fixed,
// machin, ln2_fixed, ln10_fixed, bs_chudnovsky, pi_fixed, bspe, e_fixed,
// phi_fixed; libmp/gammazeta.py: catalan_fixed, apery_fixed, euler_fixed),
// Copyright (c) 2005-2023 Fredrik Johansson and mpmath contributors,
// BSD-3-Clause; see the LICENSE file of this package.

/**
 * @file Mathematical constants as fixed-point integers floor(c * 2**prec)
 * (up to a few units in the last place), computed by binary splitting.
 *
 * Every series below is summed as a hypergeometric-type series
 *
 *     S = sum_{k=a}^{b-1} t_k * (p_a ... p_{k-1}) / (q_a ... q_k)
 *
 * by binary splitting: the range [a, b) is split at its midpoint and the
 * halves are combined exactly as integers (P, Q, T) with
 *
 *     P = P1 P2,  Q = Q1 Q2,  T = T1 Q2 + P1 T2,
 *
 * so that S = T / Q is formed with one final division. Splitting by the
 * index midpoint keeps the operands of each multiplication balanced, which
 * lets the subquadratic BigInt multiplication of the engine (Karatsuba,
 * Toom-Cook, FFT) do the work. Ranges of at most `leaf` terms are
 * accumulated term by term instead of recursing (identical integers, less
 * call overhead on small numbers). P of the rightmost subranges is never
 * needed and is not formed.
 *
 * Each constant has a table "max precision (bits) -> method, leaf size",
 * chosen from benchmarks with V8 BigInt (Node 22, see below). The tables
 * can be replaced through the internal API (setConstantMethodTable) for
 * tests and tuning, and computeConstantFixed runs one method directly.
 *
 * Methods (the series and their convergence in bits per term):
 *
 * - pi
 *   - chudnovsky: Chudnovsky's series, 47.1 bits/term, with the square root
 *     of 640320 from the integer square root (mpmath pi_fixed /
 *     bs_chudnovsky; recurrences of gmp-chudnovsky.c).
 *   - machin: 16 acot(5) - 4 acot(239), each acot by binary splitting
 *     (mpmath bsp_acot / acot_fixed / machin).
 * - e
 *   - taylor: sum 1/k! (mpmath bspe / e_fixed).
 * - ln2
 *   - machin: 18 acoth(26) - 2 acoth(4801) + 8 acoth(8749) (mpmath ln2_fixed).
 *   - series: ln 2 = 3/4 sum (-1)^k k!^2 / (2^k (2k+1)!), 3 bits/term.
 * - ln10
 *   - machin: 46 acoth(31) + 34 acoth(49) + 20 acoth(161) (mpmath ln10_fixed).
 *   - ln2: ln 10 = 3 ln 2 + 2 acoth(9), reusing the cached ln 2.
 * - euler (Euler-Mascheroni gamma), Brent-McMillan, where
 *   A = sum (n^k/k!)^2 H_k and B = sum (n^k/k!)^2 are split together with
 *   the harmonic numbers H_k (five integers per range, after Gourdon & Sebah,
 *   "The Euler constant: gamma", and Brent & McMillan 1980). n = c 2**j with
 *   c in {1, 3, 5, 7}, the smallest such n above the size the error bound
 *   needs (mpmath takes a power of two, up to twice too large), so the
 *   powers of n^2 are shifts times powers of c^2 and ln n = j ln 2 + ln c
 *   with ln 3, ln 5, ln 7 from ln 2 and acoth(5), acoth(9), acoth(15):
 *   - bm1: gamma = A/B - ln n, error O(e^(-4n)) (the algorithm of mpmath
 *     euler_fixed, which sums term by term).
 *   - bm3: gamma = A/B - C/B^2 - ln n with
 *     C = 1/(4n) sum_{k=0}^{2n} (2k)!^3 / (k!^4 (16n)^(2k)), error
 *     O(e^(-8n)), so n is half as large.
 * - catalan
 *   - lupas: Lupas' series, 2 bits/term (the series of mpmath catalan_fixed,
 *     which sums term by term).
 *   - guillera: G = 1/2 sum (-8)^k (3k+2) / ((2k+1)^3 binomial(2k,k)^3),
 *     3 bits/term with smaller factors (J. Guillera).
 * - apery (zeta(3))
 *   - amdeberhan: Amdeberhan-Zeilberger,
 *     zeta(3) = 1/64 sum (-1)^k k!^10 (205k^2+250k+77) / (2k+1)!^5,
 *     10 bits/term (the series of mpmath apery_fixed, which sums term by
 *     term).
 *   - wedeniwski: zeta(3) = 1/24 sum (-1)^k (2k+1)!^3 (2k)!^3 k!^3
 *     (126392k^5 + 412708k^4 + 531578k^3 + 336367k^2 + 104000k + 12463)
 *     / ((3k+2)! (4k+3)!^3), 16.7 bits/term (S. Wedeniwski).
 *
 * - ln3, ln5, ln7
 *   - machin: four-term hyperbolic Machin-like formulas over acoth(251),
 *     acoth(449), acoth(4801), acoth(8749) (J. Arndt, Matters Computational,
 *     32.1; also used by y-cruncher).
 *   - ln2: ln 3 = ln 2 + 2 acoth 5, ln 5 = 2 ln 2 + 2 acoth 9,
 *     ln 7 = 3 ln 2 - 2 acoth 15 from the cached ln 2.
 *   ln n of other integers (lnIntFixed) adds the logarithms of the prime
 *   factors; a prime p > 7 is ln(p - 1) + 2 acoth(2p - 1), cached per p.
 * - zeta5 (zeta(5)), with a cumulative rational factor (hsplit, the scheme
 *   of the Euler constant with general increments):
 *   - koecher: Koecher's formula 2 sum (-1)^(k+1)/(k^5 C(2k,k))
 *     - 5/2 sum (-1)^(k+1) H2_(k-1)/(k^3 C(2k,k)), 2 bits/term.
 *   - borwein: P. Borwein's algorithm 2 for eta(5) with its double sum
 *     exchanged into one split with increments (-1)^k/(k+1)^5, 2.54 bits/term.
 * - lemniscate (varpi = Gamma(1/4)^2 / (2 sqrt(2 pi)))
 *   - gauss: Gauss's varpi/2 = 2 arcsl(1/2) + arcsl(7/23).
 *   - hyper: varpi = 2 pi F / 33^(1/4) with F = 2F1(1/12, 5/12; 1; 8/1331)
 *     (the CM point tau = 2i, j = 66^3), 7.4 bits/term.
 *   Gamma(1/4) = sqrt(2 varpi sqrt(2 pi)) and Gauss's constant varpi/pi
 *   are derived from it.
 * - gamma13 (Gamma(1/3)), Gamma(1/3)^3 = F pi^2 c with F = 2F1(1/12, 5/12; 1; x):
 *   - j27: x = -9/64000 (tau = (1 + 3 sqrt(-3))/2), c = (72/5)^(1/4),
 *     12.8 bits/term.
 *   - j12: x = 4/125 (tau = sqrt(-3)), c = (2^28/(3^6 5^3))^(1/12),
 *     5 bits/term.
 *   2F1(1/12, 5/12; 1; 1728/j(tau))^4 = E4(tau), and the Chowla-Selberg
 *   formula gives E4 at these CM points by Gamma(1/4) or Gamma(1/3); the
 *   algebraic factors were found with PSLQ and are checked against mpmath
 *   to 16610 bits by the tests. The roots are exact integer roots
 *   (sqrtrem, and icbrt by Newton from above).
 *
 * The golden ratio (1 + sqrt 5)/2 is algebraic: it uses the integer square
 * root (mpf sqrtrem, divide and conquer) as mpmath phi_fixed does.
 *
 * Default tables (DEFAULT_TABLES; "<= bits: method/leaf", the last row
 * covers every larger precision). Each was chosen by timing every method
 * with leaf sizes 1..64 at precisions 64..63k bits in steps of 1.5x, and
 * every method at 166k and 332k bits:
 *
 *   pi       <= 2048: chudnovsky/16, above: chudnovsky/4. Machin is 3-5x
 *            slower at every precision; leaves of 16-64 terms save up to
 *            half of the time of the tiny low-precision sums, and are
 *            neutral above.
 *   e        taylor/16.
 *   ln2      <= 256: series/16, above: machin/8 (the crossover is between
 *            216 and 324 bits; machin is 1.7x faster at 10k+ bits).
 *   ln10     machin/8 (1.3-1.6x faster than 3 ln 2 + 2 acoth 9 from a
 *            cold ln 2 cache).
 *   euler    bm3/8 (1.2-1.6x faster than bm1 at every precision).
 *   catalan  guillera/8 (1.6x faster than lupas at 64 bits, 2.5-3x at
 *            1k+ bits).
 *   apery    wedeniwski/8 (1.1-1.5x faster than amdeberhan).
 *   ln3/5/7  machin/8 (1.0-2.3x faster than the ln 2 route from a cold
 *            ln 2 cache; with ln 2 already cached the ln 2 route is
 *            1.2-3x faster, but the table cannot know the cache state).
 *   zeta5    borwein/8 (1.3-1.6x faster than koecher).
 *   lemniscate <= 192: gauss/8 (up to 1.7x faster at 64 bits), above:
 *            hyper/8 (1.5-1.7x faster at 1k+ bits).
 *   gamma13  j27/8 (1.6-3.4x faster than j12).
 *
 * The leaf size changes the time by less than the run-to-run noise above
 * a few thousand bits. Fresh computation in ms (one process per value,
 * median of 3 runs; one run for the old code at 50000 and 100000 digits;
 * Node 22, Apple M1), the term-by-term code this module replaced (exp(1)
 * by its Taylor series for e; mpmath's apery_fixed for zeta(3), which was
 * Euler-Maclaurin in czeta before) vs binary splitting:
 *
 *   digits      1000          10000          50000            100000
 *   pi        3.3 / 1.2    165.6 / 4.7    1999 / 35       8201 / 100
 *   e         3.8 / 0.5    193.7 / 5.1    1978 / 25       7314 / 69
 *   ln2       2.2 / 1.4     99.6 / 20.7   1418 / 96       5358 / 203
 *   ln10      3.1 / 0.9    150.0 / 18.1   2015 / 124      8003 / 300
 *   euler    33.7 / 10.1  1867.5 / 159   22386 / 1060   127533 / 2641
 *   catalan   7.7 / 5.6    375.1 / 55.2   7140 / 342     33676 / 898
 *   apery     1.2 / 0.8     77.9 / 17.0   1095 / 142      4529 / 327
 *
 * The evaluation paths these replace (one run each, ms; the old paths are
 * the term-by-term log series, Euler-Maclaurin czeta and Stirling cgamma,
 * which remain for other arguments) vs binary splitting:
 *
 *   digits             1000           10000         50000
 *   log(3)          8.1 / 0.8     883.5 / 5.8    29920 / 43
 *   log(7)          6.3 / 0.8     638.2 / 6.1
 *   zeta(5)       239.7 / 4.6      7285 / 109        - / 959
 *   gamma(1/4)    707.8 / 1.4      4240 / 13.4       - / 105
 *   gamma(1/3)    718.7 / 1.0      4996 / 8.5        - / 70
 */

import { at } from '../core/guard';
import * as F from './mpf';

/** Names of the constants computed here. */
export type ConstantName =
  | 'pi'
  | 'e'
  | 'ln2'
  | 'ln3'
  | 'ln5'
  | 'ln7'
  | 'ln10'
  | 'euler'
  | 'catalan'
  | 'apery'
  | 'zeta5'
  | 'lemniscate'
  | 'gamma13';

const NAMES: readonly ConstantName[] = ['pi', 'e', 'ln2', 'ln3', 'ln5', 'ln7', 'ln10', 'euler', 'catalan', 'apery', 'zeta5', 'lemniscate', 'gamma13'];

/** One row of a method table: the method used up to maxPrec bits (inclusive). */
export interface MethodEntry {
  readonly maxPrec: number;
  readonly method: string;
  readonly leaf: number;
}

// ---------------------------------------------------------------------------
// Binary splitting engine
// ---------------------------------------------------------------------------

/** [p_k, q_k, t_k] of a series term (see the file comment). */
type Term = (k: number) => [bigint, bigint, bigint];

/** [P, Q, T] of a range. */
type PQT = [bigint, bigint, bigint];

/** Range [a, b) term by term. */
function bsLeaf(term: Term, a: number, b: number): PQT {
  let [P, Q, T] = term(a);
  for (let k = a + 1; k < b; k++) {
    const [p, q, t] = term(k);
    T = T * q + P * t;
    P *= p;
    Q *= q;
  }
  return [P, Q, T];
}

/**
 * [P, Q, T] of the range [a, b) (a < b) by binary splitting; P is 0 when
 * needP is false.
 */
export function bsplit(term: Term, a: number, b: number, leaf: number, needP = false): PQT {
  if (b - a <= leaf) return bsLeaf(term, a, b);
  const m = a + ((b - a) >> 1);
  const [P1, Q1, T1] = bsplit(term, a, m, leaf, true);
  const [P2, Q2, T2] = bsplit(term, m, b, leaf, needP);
  return [needP ? P1 * P2 : 0n, Q1 * Q2, T1 * Q2 + P1 * T2];
}

// ---------------------------------------------------------------------------
// Integer arctangents (mpmath bsp_acot, acot_fixed, machin)
// ---------------------------------------------------------------------------

/**
 * acot(x) (or acoth(x)) as fixed point: 1/x + sum_k (-1)^(k+1) / ((2k+3) x^(2k+3))
 * with mpmath's splitting p_k = 2k+3, q_k = (2k+3) x^2, t_k = -/+1.
 */
function acotFixed(x: bigint, prec: number, hyperbolic: boolean, leaf: number): bigint {
  const N = Math.floor((0.35 * prec) / Math.log(Number(x)) + 20);
  const x2 = x * x;
  const term: Term = (k) => {
    const a1 = BigInt(2 * k + 3);
    return [a1, a1 * x2, hyperbolic || k & 1 ? 1n : -1n];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((T + Q) << BigInt(prec)) / (Q * x);
}

/** sum c * acot[h](x) over [c, x] pairs, fixed point. */
function machin(coefs: readonly (readonly [bigint, bigint])[], prec: number, hyperbolic: boolean, leaf: number): bigint {
  const extra = 10;
  let s = 0n;
  for (const [c, x] of coefs) s += c * acotFixed(x, prec + extra, hyperbolic, leaf);
  return s >> BigInt(extra);
}

// ---------------------------------------------------------------------------
// The methods
// ---------------------------------------------------------------------------

type Method = (prec: number, leaf: number) => bigint;

// Chudnovsky's series (mpmath bs_chudnovsky, pi_fixed)
const CHUD_A = 13591409n;
const CHUD_B = 545140134n;
const CHUD_C = 640320n;
const CHUD_C3_24 = CHUD_C ** 3n / 24n;
const CHUD_D = 12n;

function piChudnovsky(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  // 14.18 digits per term
  const N = Math.floor(wp / 3.3219280948 / 14.181647462 + 2);
  // mpmath's term b = k + 1
  const term: Term = (k) => {
    const b = BigInt(k + 1);
    const g = (6n * b - 5n) * (2n * b - 1n) * (6n * b - 1n);
    const t = g * (CHUD_A + CHUD_B * b);
    return [g, b * b * b * CHUD_C3_24, k & 1 ? t : -t];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  const sqrtC = F.isqrt(CHUD_C << BigInt(2 * wp));
  return ((Q * CHUD_C * sqrtC) / ((T + CHUD_A * Q) * CHUD_D)) >> 10n;
}

const piMachin: Method = (prec, leaf) => machin([[16n, 5n], [-4n, 239n]], prec, false, leaf);

/** e = sum 1/k! (mpmath bspe, e_fixed). */
function eTaylor(prec: number, leaf: number): bigint {
  // slight overestimate of N with 1/N! < 2**-prec
  const N = Math.floor((1.1 * prec) / Math.log(Math.max(prec, 16)) + 20);
  const term: Term = (k) => [1n, BigInt(k + 1), 1n];
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((T + Q) << BigInt(prec)) / Q;
}

const ln2Machin: Method = (prec, leaf) => machin([[18n, 26n], [-2n, 4801n], [8n, 8749n]], prec, true, leaf);

/** ln 2 = 3/4 sum_k (-1)^k k!^2 / (2^k (2k+1)!): p_k = -(k+1), q_k = 4(2k+1) (q_0 = 1). */
function ln2Series(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  const N = Math.floor(wp / 3) + 4;
  const term: Term = (k) => [BigInt(-(k + 1)), k ? BigInt(8 * k + 4) : 1n, 1n];
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return (((3n * T) << BigInt(wp - 2)) / Q) >> 10n;
}

const ln10Machin: Method = (prec, leaf) => machin([[46n, 31n], [34n, 49n], [20n, 161n]], prec, true, leaf);

/** ln 10 = 3 ln 2 + ln(5/4) = 3 ln 2 + 2 acoth(9). */
function ln10FromLn2(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  return (3n * ln2Fixed(wp) + 2n * acotFixed(9n, wp, true, leaf)) >> 10n;
}

/** Catalan's constant by Lupas' series (mpmath catalan_fixed), k = index + 1. */
function catalanLupas(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  const N = Math.floor(wp / 2) + 4;
  const term: Term = (i) => {
    const k = BigInt(i + 1);
    const d = 16n * k * k - 16n * k + 3n;
    return [-32n * k * k * k * (2n * k - 1n), d * d, 32n * (40n * k * k - 24n * k + 3n)];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((T << BigInt(wp - 6)) / Q) >> 10n;
}

/** Catalan's constant by Guillera's series: p_k = -(k+1)^3, q_k = (2k+1)^3, t_k = 3k+2. */
function catalanGuillera(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  const N = Math.floor(wp / 3) + 4;
  const term: Term = (i) => {
    const k = BigInt(i);
    const k1 = k + 1n;
    const o = 2n * k + 1n;
    return [-k1 * k1 * k1, o * o * o, 3n * k + 2n];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((T << BigInt(wp - 1)) / Q) >> 10n;
}

/** zeta(3) by Amdeberhan-Zeilberger (mpmath apery_fixed): p_k = -(k+1)^5, q_k = 32 (2k+1)^5 (q_0 = 1). */
function aperyAmdeberhan(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  const N = Math.floor(wp / 10) + 4;
  const term: Term = (i) => {
    const k = BigInt(i);
    const o = 2n * k + 1n;
    return [-((k + 1n) ** 5n), i ? 32n * o ** 5n : 1n, 205n * k * k + 250n * k + 77n];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((T << BigInt(wp - 6)) / Q) >> 10n;
}

/**
 * zeta(3) by Wedeniwski's series: the term ratio is
 * -k^5 (2k-1)^3 / (24 (3k+1)(3k+2)(4k+1)^3 (4k+3)^3) and the first term
 * 1/432, so p_k = -(k+1)^5 (2k+1)^3, q_k = 24 (3k+1)(3k+2)(4k+1)^3 (4k+3)^3
 * (q_0 = 1) and zeta(3) = T / (10368 Q).
 */
function aperyWedeniwski(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  const N = Math.floor(wp / 16.7) + 4;
  const term: Term = (i) => {
    const k = BigInt(i);
    const k1 = k + 1n;
    const o = 2n * k + 1n;
    const f1 = 4n * k + 1n;
    const f3 = 4n * k + 3n;
    const t = ((((126392n * k + 412708n) * k + 531578n) * k + 336367n) * k + 104000n) * k + 12463n;
    return [-(k1 ** 5n) * o * o * o, i ? 24n * (3n * k + 1n) * (3n * k + 2n) * (f1 * f3) ** 3n : 1n, t];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((T << BigInt(wp)) / (10368n * Q)) >> 10n;
}

// ---------------------------------------------------------------------------
// Euler's constant (Brent-McMillan with binary splitting)
// ---------------------------------------------------------------------------

/** [T, D, C, V, R] of a range of the Brent-McMillan sums (see bmSplit). */
type BM = [bigint, bigint, bigint, bigint, bigint];

/**
 * Combine adjacent ranges L = [a, m) and R = [m, b), where P of L is
 * R1 * 2**s1 and Q of R is D2^2.
 */
function bmMerge(L: BM, R: BM, s1: bigint, needR: boolean): BM {
  const [T1, D1, C1, V1, R1] = L;
  const [T2, D2, C2, V2, R2] = R;
  const Q2 = D2 * D2;
  const PT = (R1 * T2) << s1;
  return [T1 * Q2 + PT, D1 * D2, C1 * D2 + C2 * D1, D2 * (V1 * Q2 + C1 * PT) + D1 * ((R1 * V2) << s1), needR ? R1 * R2 : 0n];
}

/**
 * Over a range [a, b) of k >= 1, with w_k = prod_{j=a}^{k} n^2 / j^2 and
 * h_k = sum_{j=a}^{k} 1/j: T/Q = sum w_k, C/D = h_{b-1} and
 * V/(Q D) = sum w_k h_k, where D = (b-1)!/(a-1)!, Q = D^2 and
 * P = n^(2(b-a)). With n = c 2**j, n^2 = c2 2**n2s, P = R 2**(n2s (b-a))
 * with R = c2^(b-a), and Q is not stored. The leaf of k is
 * [n^2, k, 1, n^2, c2]; merging is
 *
 *     T = T1 Q2 + P1 T2,  D = D1 D2,  C = C1 D2 + C2 D1,
 *     V = D2 (V1 Q2 + C1 P1 T2) + D1 P1 V2.
 */
function bmSplit(c2: bigint, n2s: number, a: number, b: number, leaf: number, needR: boolean): BM {
  const n2 = c2 << BigInt(n2s);
  if (b - a <= leaf) {
    let acc: BM = [n2, BigInt(a), 1n, n2, c2];
    for (let k = a + 1; k < b; k++) acc = bmMerge(acc, [n2, BigInt(k), 1n, n2, c2], BigInt(n2s * (k - a)), true);
    return acc;
  }
  const m = a + ((b - a) >> 1);
  return bmMerge(bmSplit(c2, n2s, a, m, leaf, true), bmSplit(c2, n2s, m, b, leaf, needR), BigInt(n2s * (m - a)), needR);
}

/**
 * The smallest n = c 2**j >= target with c in {1, 3, 5, 7}, as [c, j]: the
 * candidates are 4, 5, 6, 7, 8 times a power of two apart, so n exceeds the
 * needed size by at most 25% (a power of two alone wastes up to 100%).
 */
function bmParameter(target: number): [number, number] {
  let best: [number, number] = [1, Math.max(0, Math.ceil(Math.log2(target)))];
  for (const c of [3, 5, 7]) {
    const j = Math.max(0, Math.ceil(Math.log2(target / c)));
    if (c * 2 ** j < best[0] * 2 ** best[1]) best = [c, j];
  }
  return best;
}

/**
 * The number of terms K so that the tail (n^k/k!)^2, k >= K, of the
 * Brent-McMillan sums is below 2**-wp relative to B ~ e^(2n): the smallest
 * K >= n with 2K (1 + ln n - ln K) - 2n < -wp ln 2 (Stirling, which
 * overestimates the terms), plus a margin.
 */
function bmTerms(n: number, wp: number): number {
  const target = -wp * Math.LN2 - 8;
  const f = (k: number): number => 2 * k * (1 + Math.log(n) - Math.log(k)) - 2 * n;
  let lo = n;
  let hi = 6 * n;
  while (hi - lo > 1) {
    const mid = (lo + hi) >> 1;
    if (f(mid) < target) hi = mid;
    else lo = mid;
  }
  return hi + 4;
}

/**
 * Euler's constant by Brent-McMillan, gamma = A/B - ln n (refined = false,
 * error < pi e^(-4n)) or A/B - C/B^2 - ln n (refined = true, error below
 * e^(-8n)), with n = c 2**j from bmParameter.
 */
function eulerBM(prec: number, leaf: number, refined: boolean): bigint {
  const extra = 30;
  const wp = prec + extra;
  // n with e^(-4n) (or e^(-8n)) < 2**-wp
  const [c, j] = bmParameter((wp * Math.LN2) / (refined ? 8 : 4));
  const n = c * 2 ** j;
  const K = bmTerms(n, wp);
  const c2 = BigInt(c * c);
  const [T, D, , V] = bmSplit(c2, 2 * j, 1, K, leaf, false);
  const Q = D * D;
  // B = 1 + T/Q (the k = 0 term), A = V/(Q D) (H_0 = 0), ln n = j ln 2 + ln c
  const QT = Q + T;
  let g = (V << BigInt(wp)) / (D * QT) - BigInt(j) * ln2Fixed(wp) - lnIntFixed(BigInt(c), wp);
  if (refined) {
    // C = T_c / (4n Q_c) with c_k / c_{k-1} = 8 (2k-1)^3 / (k (16n)^2) = (2k-1)^3 / (k c^2 2^(5+2j))
    const sh = BigInt(5 + 2 * j);
    const term: Term = (k) => [BigInt(2 * k + 1) ** 3n, k ? (BigInt(k) * c2) << sh : 1n, 1n];
    const [, Qc, Tc] = bsplit(term, 0, 2 * n + 1, leaf);
    // C/B^2 = T_c Q^2 / (4n Q_c (Q+T)^2)
    const Bf = (QT << BigInt(wp)) / Q;
    const Cf = (Tc << BigInt(wp)) / ((Qc * BigInt(c)) << BigInt(j + 2));
    g -= (Cf << BigInt(2 * wp)) / (Bf * Bf);
  }
  return g >> BigInt(extra);
}

// ---------------------------------------------------------------------------
// Logarithms of small integers
// ---------------------------------------------------------------------------

// Hyperbolic Machin-like formulas over acoth(251), acoth(449), acoth(4801)
// and acoth(8749) (126/125, 225/224, 2401/2400 and 4375/4374 are 7-smooth),
// as listed by J. Arndt, "Matters Computational", section 32.1, and used by
// y-cruncher; ln 2 = 144, 54, -38, 62 in the same basis.
const LOG_X = [251n, 449n, 4801n, 8749n] as const;
const LOG_C: Record<'ln3' | 'ln5' | 'ln7', readonly bigint[]> = {
  ln3: [228n, 86n, -60n, 98n],
  ln5: [334n, 126n, -88n, 144n],
  ln7: [404n, 152n, -106n, 174n],
};

const lnMachin =
  (name: 'ln3' | 'ln5' | 'ln7'): Method =>
  (prec, leaf) =>
    machin(
      LOG_C[name].map((c, i) => [c, at(LOG_X, i)] as const),
      prec,
      true,
      leaf,
    );

/**
 * From the cached ln 2 and one fast series: ln 3 = ln 2 + 2 acoth 5,
 * ln 5 = 2 ln 2 + 2 acoth 9, ln 7 = 3 ln 2 - 2 acoth 15.
 */
const lnFromLn2 =
  (k: bigint, x: bigint, sgn: bigint): Method =>
  (prec, leaf) => {
    const wp = prec + 10;
    return (k * ln2Fixed(wp) + sgn * 2n * acotFixed(x, wp, true, leaf)) >> 10n;
  };

// ---------------------------------------------------------------------------
// zeta(5): sums with a cumulative rational factor
// ---------------------------------------------------------------------------

/** [p_k, q_k, t_k, u_k, v_k]: a series term as for Term and the increment u_k / v_k of a cumulative sum. */
type HTerm = (k: number) => [bigint, bigint, bigint, bigint, bigint];

/** [P, Q, T, D, C, V] of a range (see hsplit). */
type PQTDCV = [bigint, bigint, bigint, bigint, bigint, bigint];

function hMerge(L: PQTDCV, R: PQTDCV, needP: boolean): PQTDCV {
  const [P1, Q1, T1, D1, C1, V1] = L;
  const [P2, Q2, T2, D2, C2, V2] = R;
  const PT = P1 * T2;
  return [needP ? P1 * P2 : 0n, Q1 * Q2, T1 * Q2 + PT, D1 * D2, C1 * D2 + C2 * D1, D2 * (V1 * Q2 + C1 * PT) + D1 * (P1 * V2)];
}

/**
 * Binary splitting of S = sum_k w_k and S' = sum_k w_k h_k over [a, b),
 * with w_k = t_k (p_a ... p_{k-1}) / (q_a ... q_k) as for bsplit and the
 * cumulative sum h_k = sum_{j=a}^{k-1} u_j / v_j (exclusive): T/Q = S,
 * C/D = h_b and V/(Q D) = S'. Merging is
 *
 *     T = T1 Q2 + P1 T2,  D = D1 D2,  C = C1 D2 + C2 D1,
 *     V = D2 (V1 Q2 + C1 P1 T2) + D1 P1 V2,
 *
 * the scheme of the Euler constant sums with general harmonic increments.
 */
export function hsplit(term: HTerm, a: number, b: number, leaf: number, needP = false): PQTDCV {
  if (b - a <= leaf) {
    const leafOf = (k: number): PQTDCV => {
      const [p, q, t, u, v] = term(k);
      return [p, q, t, v, u, 0n];
    };
    let acc = leafOf(a);
    for (let k = a + 1; k < b; k++) acc = hMerge(acc, leafOf(k), true);
    return acc;
  }
  const m = a + ((b - a) >> 1);
  return hMerge(hsplit(term, a, m, leaf, true), hsplit(term, m, b, leaf, needP), needP);
}

/**
 * zeta(5) by Koecher's formula
 *
 *     zeta(5) = 2 sum_k (-1)^(k+1) / (k^5 C(2k,k))
 *               - 5/2 sum_k (-1)^(k+1) H2_(k-1) / (k^3 C(2k,k)),
 *
 * H2_m = sum_{j<=m} 1/j^2, 2 bits/term (M. Koecher, Math. Intelligencer 2,
 * 1980). With k = i + 1 the first sum has p_i = -k^5, q_i = 2(2k-1) k^4,
 * the second p_i = -k^3, q_i = 2(2k-1) k^2 and the increments 1/k^2.
 */
function zeta5Koecher(prec: number, leaf: number): bigint {
  const wp = prec + 20;
  const N = Math.floor(wp / 2) + 8;
  const t1: Term = (i) => {
    const k = BigInt(i + 1);
    const k4 = k ** 4n;
    return [-k4 * k, 2n * (2n * k - 1n) * k4, 1n];
  };
  const [, Q1, T1] = bsplit(t1, 0, N, leaf);
  const t2: HTerm = (i) => {
    const k = BigInt(i + 1);
    const k2 = k * k;
    return [-k2 * k, 2n * (2n * k - 1n) * k2, 1n, 1n, k2];
  };
  const [, Q, , D, , V] = hsplit(t2, 0, N, leaf);
  return (((2n * T1) << BigInt(wp)) / Q1 - ((5n * V) << BigInt(wp - 1)) / (Q * D)) >> 20n;
}

/**
 * zeta(5) = 16/15 eta(5) by P. Borwein's algorithm 2 ("An efficient algorithm
 * for the Riemann zeta function", 2000): with
 * e_i = n (n+i-1)! 4^i / ((n-i)! (2i)!) and d_n = sum_{i<=n} e_i,
 * eta(s) ~ 1/d_n sum_{i=0}^{n} e_i sum_{k<i} (-1)^k / (k+1)^s (the sums
 * exchanged), error below 3 (3 + sqrt 8)^-n, 2.54 bits/term:
 * p_i = 2(n+i)(n-i), q_i = i (2i-1) (q_0 = 1), increments
 * (-1)^i / (i+1)^5, and eta(5) = V / (D T).
 */
function zeta5Borwein(prec: number, leaf: number): bigint {
  const wp = prec + 20;
  const n = Math.ceil(wp / 2.54) + 4;
  const nb = BigInt(n);
  const term: HTerm = (i) => {
    const k = BigInt(i);
    return [2n * (nb + k) * (nb - k), i ? k * (2n * k - 1n) : 1n, 1n, i & 1 ? -1n : 1n, (k + 1n) ** 5n];
  };
  const [, , T, D, , V] = hsplit(term, 0, n + 1, leaf);
  return ((16n * V) << BigInt(wp)) / (15n * D * T) >> 20n;
}

// ---------------------------------------------------------------------------
// The lemniscate constant and Gamma(1/3)
// ---------------------------------------------------------------------------

/**
 * floor(n^(1/3)) for n >= 1 by Newton's iteration from above, started from
 * the root of the top bits (so that only a few full-size steps remain).
 */
function icbrt(n: bigint): bigint {
  const bl = F.bitLength(n);
  let x: bigint;
  if (bl <= 150) x = BigInt(Math.ceil(Math.cbrt(Number(n)) * (1 + 1e-12))) + 1n;
  else {
    const s = Math.floor(bl / 6);
    x = (icbrt(n >> BigInt(3 * s)) + 1n) << BigInt(s);
  }
  for (;;) {
    const y = (2n * x + n / (x * x)) / 3n;
    if (y >= x) return x;
    x = y;
  }
}

/**
 * 2F1(1/12, 5/12; 1; a/b) as fixed point: the term ratio is
 * (12k-11)(12k-7) / (144 k^2) * a/b. At x = 1728/j(tau) for a CM point
 * tau, 2F1(1/12, 5/12; 1; x)^4 = E4(tau), which the Chowla-Selberg formula
 * expresses by Gamma values; the algebraic factors used below were
 * identified with PSLQ and are checked to thousands of digits by the tests.
 */
function hyp1125(a: bigint, b: bigint, prec: number, leaf: number): bigint {
  const N = Math.ceil(prec / Math.log2(Number(b) / Math.abs(Number(a)))) + 6;
  const term: Term = (i) => {
    const k = BigInt(i + 1);
    return [(12n * k - 11n) * (12n * k - 7n) * a, i ? 144n * BigInt(i * i) * b : 1n, 1n];
  };
  // index i carries the step to term i + 1: P(0,i)/Q(0,i+1) = c_i, q_0 = 1
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return (T << BigInt(prec)) / Q;
}

/**
 * arcsl(a/b) = sum_k C(2k,k)/4^k (a/b)^(4k+1) / (4k+1) (the lemniscate arc
 * sine) as fixed point: p_k = (2k+1)(4k+1) a^4, q_k = 2k (4k+1) b^4 (q_0 = 1).
 */
function arcslFixed(a: bigint, b: bigint, prec: number, leaf: number): bigint {
  const N = Math.ceil(prec / (4 * Math.log2(Number(b) / Number(a)))) + 6;
  const a4 = a ** 4n;
  const b4 = b ** 4n;
  const term: Term = (i) => {
    const k = BigInt(i);
    return [(2n * k + 1n) * (4n * k + 1n) * a4, i ? 2n * k * (4n * k + 1n) * b4 : 1n, 1n];
  };
  const [, Q, T] = bsplit(term, 0, N, leaf);
  return ((a * T) << BigInt(prec)) / (b * Q);
}

/** The lemniscate constant by Gauss's formula varpi/2 = 2 arcsl(1/2) + arcsl(7/23). */
function lemniscateGauss(prec: number, leaf: number): bigint {
  const wp = prec + 10;
  return (4n * arcslFixed(1n, 2n, wp, leaf) + 2n * arcslFixed(7n, 23n, wp, leaf)) >> 10n;
}

/** varpi = 2 pi F / 33^(1/4) with F = 2F1(1/12, 5/12; 1; 8/1331) (tau = 2i, j = 66^3). */
function lemniscateHyper(prec: number, leaf: number): bigint {
  const wp = prec + 20;
  const f = hyp1125(8n, 1331n, wp, leaf);
  const r = F.isqrt(F.isqrt(33n << BigInt(4 * wp)));
  return ((2n * piFixed(wp) * f) / r) >> 20n;
}

/**
 * Gamma(1/3) from Gamma(1/3)^3 = F pi^2 (72/5)^(1/4), F = 2F1(1/12, 5/12; 1; -9/64000)
 * (tau = (1 + 3 sqrt(-3))/2, j = -12288000), 12.8 bits/term.
 */
function gamma13J27(prec: number, leaf: number): bigint {
  const wp = prec + 20;
  const f = hyp1125(-9n, 64000n, wp, leaf);
  const pi = piFixed(wp);
  const r = F.isqrt(F.isqrt((72n << BigInt(4 * wp)) / 5n));
  return icbrt((f * pi * pi * r) >> BigInt(wp)) >> 20n;
}

/**
 * Gamma(1/3) from Gamma(1/3)^3 = F pi^2 (2^28 / (3^6 5^3))^(1/12), F = 2F1(1/12, 5/12; 1; 4/125)
 * (tau = sqrt(-3), j = 54000), 5 bits/term.
 */
function gamma13J12(prec: number, leaf: number): bigint {
  const wp = prec + 20;
  const f = hyp1125(4n, 125n, wp, leaf);
  const pi = piFixed(wp);
  const r = icbrt(F.isqrt(F.isqrt((1n << BigInt(28 + 12 * wp)) / 91125n)));
  return icbrt((f * pi * pi * r) >> BigInt(wp)) >> 20n;
}

// ---------------------------------------------------------------------------
// Method tables and the cached constants
// ---------------------------------------------------------------------------

/** A fixed-point value computed at the largest precision requested so far and shifted down. */
class Memo {
  prec = -1;
  value = 0n;
  constructor(private readonly compute: (prec: number) => bigint) {}
  get(prec: number): bigint {
    if (prec > this.prec) {
      const p = Math.max(prec, Math.ceil(this.prec * 1.5), 128) + 20;
      this.value = this.compute(p);
      this.prec = p;
    }
    return this.value >> BigInt(this.prec - prec);
  }
  clear(): void {
    this.prec = -1;
    this.value = 0n;
  }
}

const METHODS: Record<ConstantName, Record<string, Method>> = {
  pi: { chudnovsky: piChudnovsky, machin: piMachin },
  e: { taylor: eTaylor },
  ln2: { machin: ln2Machin, series: ln2Series },
  ln3: { machin: lnMachin('ln3'), ln2: lnFromLn2(1n, 5n, 1n) },
  ln5: { machin: lnMachin('ln5'), ln2: lnFromLn2(2n, 9n, 1n) },
  ln7: { machin: lnMachin('ln7'), ln2: lnFromLn2(3n, 15n, -1n) },
  ln10: { machin: ln10Machin, ln2: ln10FromLn2 },
  euler: { bm1: (p, l) => eulerBM(p, l, false), bm3: (p, l) => eulerBM(p, l, true) },
  catalan: { lupas: catalanLupas, guillera: catalanGuillera },
  apery: { amdeberhan: aperyAmdeberhan, wedeniwski: aperyWedeniwski },
  zeta5: { koecher: zeta5Koecher, borwein: zeta5Borwein },
  lemniscate: { gauss: lemniscateGauss, hyper: lemniscateHyper },
  gamma13: { j27: gamma13J27, j12: gamma13J12 },
};

const row = (maxPrec: number, method: string, leaf: number): MethodEntry => ({ maxPrec, method, leaf });

/** The default tables (see the file comment for the benchmark behind them). */
const DEFAULT_TABLES: Record<ConstantName, readonly MethodEntry[]> = {
  pi: [row(2048, 'chudnovsky', 16), row(Infinity, 'chudnovsky', 4)],
  e: [row(Infinity, 'taylor', 16)],
  ln2: [row(256, 'series', 16), row(Infinity, 'machin', 8)],
  ln3: [row(Infinity, 'machin', 8)],
  ln5: [row(Infinity, 'machin', 8)],
  ln7: [row(Infinity, 'machin', 8)],
  ln10: [row(Infinity, 'machin', 8)],
  euler: [row(Infinity, 'bm3', 8)],
  catalan: [row(Infinity, 'guillera', 8)],
  apery: [row(Infinity, 'wedeniwski', 8)],
  zeta5: [row(Infinity, 'borwein', 8)],
  lemniscate: [row(192, 'gauss', 8), row(Infinity, 'hyper', 8)],
  gamma13: [row(Infinity, 'j27', 8)],
};

const tables: Record<ConstantName, readonly MethodEntry[]> = { ...DEFAULT_TABLES };

/** The method row of a table for prec bits: the first row with prec <= maxPrec, the last row otherwise. */
function pick(table: readonly MethodEntry[], prec: number): MethodEntry {
  for (let i = 0; i < table.length - 1; i++) {
    const r = at(table, i);
    if (prec <= r.maxPrec) return r;
  }
  return at(table, -1);
}

/** The method of a constant by name; throws RangeError for an unknown name. */
function method(name: ConstantName, m: string): Method {
  const f = Object.hasOwn(METHODS[name], m) ? METHODS[name][m] : undefined;
  if (f === undefined) throw new RangeError(`unknown method ${m} for the constant ${name}`);
  return f;
}

/** Throws RangeError unless leaf is a positive integer. */
function checkLeaf(leaf: number): void {
  if (!Number.isInteger(leaf) || leaf < 1) throw new RangeError(`leaf size must be a positive integer, got ${leaf}`);
}

/** Run one method of a constant at prec bits, uncached. */
function run(name: ConstantName, m: string, prec: number, leaf: number): bigint {
  const f = method(name, m);
  checkLeaf(leaf);
  return f(prec, leaf);
}

const memoOf = (name: ConstantName): Memo =>
  new Memo((p) => {
    const r = pick(tables[name], p);
    return run(name, r.method, p, r.leaf);
  });

const caches: Record<ConstantName, Memo> = {
  pi: memoOf('pi'),
  e: memoOf('e'),
  ln2: memoOf('ln2'),
  ln3: memoOf('ln3'),
  ln5: memoOf('ln5'),
  ln7: memoOf('ln7'),
  ln10: memoOf('ln10'),
  euler: memoOf('euler'),
  catalan: memoOf('catalan'),
  apery: memoOf('apery'),
  zeta5: memoOf('zeta5'),
  lemniscate: memoOf('lemniscate'),
  gamma13: memoOf('gamma13'),
};

const cachedConstant =
  (name: ConstantName): ((prec: number) => bigint) =>
  (prec) =>
    caches[name].get(prec);

/** floor(pi * 2**prec), up to a few ulp (likewise below). */
export const piFixed = cachedConstant('pi');
/** e. */
export const eFixed = cachedConstant('e');
/** ln 2. */
export const ln2Fixed = cachedConstant('ln2');
/** ln 3. */
export const ln3Fixed = cachedConstant('ln3');
/** ln 5. */
export const ln5Fixed = cachedConstant('ln5');
/** ln 7. */
export const ln7Fixed = cachedConstant('ln7');
/** ln 10. */
export const ln10Fixed = cachedConstant('ln10');
/** Euler's constant gamma. */
export const eulerFixed = cachedConstant('euler');
/** Catalan's constant G. */
export const catalanFixed = cachedConstant('catalan');
/** Apery's constant zeta(3). */
export const aperyFixed = cachedConstant('apery');
/** zeta(5). */
export const zeta5Fixed = cachedConstant('zeta5');
/** The lemniscate constant varpi = Gamma(1/4)^2 / (2 sqrt(2 pi)). */
export const lemniscateFixed = cachedConstant('lemniscate');
/** Gamma(1/3). */
export const gamma13Fixed = cachedConstant('gamma13');

/** Constants derived from the others (and phi), cached the same way. */
const derived = {
  // mpmath phi_fixed
  phi: new Memo((p) => {
    const wp = p + 10;
    return (F.isqrt(5n << BigInt(2 * wp)) + (1n << BigInt(wp))) >> 11n;
  }),
  // Gamma(1/4) = sqrt(2 varpi sqrt(2 pi))
  gamma14: new Memo((p) => {
    const wp = p + 10;
    const s = F.isqrt(piFixed(wp) << BigInt(wp + 1));
    return F.isqrt(2n * lemniscateFixed(wp) * s) >> 10n;
  }),
  // Gauss's constant varpi / pi = 1 / agm(1, sqrt 2)
  gauss: new Memo((p) => {
    const wp = p + 10;
    return ((lemniscateFixed(wp) << BigInt(wp)) / piFixed(wp)) >> 10n;
  }),
};

/** floor(phi * 2**prec) with phi = (1 + sqrt 5)/2. */
export const phiFixed = (prec: number): bigint => derived.phi.get(prec);
/** Gamma(1/4). */
export const gamma14Fixed = (prec: number): bigint => derived.gamma14.get(prec);
/** Gauss's constant 1 / agm(1, sqrt 2). */
export const gaussFixed = (prec: number): bigint => derived.gauss.get(prec);

/** ln p for primes p > 7: ln(p - 1) + 2 acoth(2p - 1), cached per p. */
const lnPrimes = new Map<bigint, Memo>();

function lnPrimeFixed(p: bigint, prec: number): bigint {
  if (p === 2n) return ln2Fixed(prec);
  if (p === 3n) return ln3Fixed(prec);
  if (p === 5n) return ln5Fixed(prec);
  if (p === 7n) return ln7Fixed(prec);
  let m = lnPrimes.get(p);
  if (m === undefined) {
    m = new Memo((wp) => lnIntFixed(p - 1n, wp) + 2n * acotFixed(2n * p - 1n, wp, true, 8));
    lnPrimes.set(p, m);
  }
  return m.get(prec);
}

/**
 * ln n for an integer n >= 1 as fixed point, from the logarithms of its
 * prime factors (found by trial division, so meant for small n).
 */
export function lnIntFixed(nIn: bigint, prec: number): bigint {
  const wp = prec + 10;
  let n = nIn;
  let s = 0n;
  for (let p = 2n; p * p <= n; p += p === 2n ? 1n : 2n) {
    while (n % p === 0n) {
      s += lnPrimeFixed(p, wp);
      n /= p;
    }
  }
  if (n > 1n) s += lnPrimeFixed(n, wp);
  return s >> 10n;
}

// ---------------------------------------------------------------------------
// Internal API (tests and tuning)
// ---------------------------------------------------------------------------

/**
 * The method names of a constant.
 * @internal
 */
export function constantMethods(name: ConstantName): readonly string[] {
  return Object.keys(METHODS[name]);
}

/**
 * The current method table of a constant.
 * @internal
 */
export function getConstantMethodTable(name: ConstantName): readonly MethodEntry[] {
  return tables[name];
}

/**
 * Replace the method table of a constant (the default one when table is
 * omitted) and clear the cached values. The rows must have increasing
 * maxPrec, known methods and positive integer leaf sizes; precisions above
 * the last maxPrec use the last row.
 * @internal
 */
export function setConstantMethodTable(name: ConstantName, table?: readonly MethodEntry[]): void {
  const t = table ?? DEFAULT_TABLES[name];
  if (t.length === 0) throw new RangeError('empty method table');
  let prev = -Infinity;
  for (const r of t) {
    if (!(r.maxPrec > prev)) throw new RangeError('method table rows must have increasing maxPrec');
    method(name, r.method);
    checkLeaf(r.leaf);
    prev = r.maxPrec;
  }
  tables[name] = t.map((r) => row(r.maxPrec, r.method, r.leaf));
  clearConstantCache();
}

/**
 * Forget the cached value of a constant, or of all constants and the values
 * derived from them when name is omitted.
 * @internal
 */
export function clearConstantCache(name?: ConstantName): void {
  if (name !== undefined) {
    caches[name].clear();
    return;
  }
  for (const k of NAMES) caches[k].clear();
  for (const m of Object.values(derived)) m.clear();
  lnPrimes.clear();
}

/**
 * The constant at prec bits by the given method and leaf size (by the
 * method table when method is omitted), bypassing the cache.
 * @internal
 */
export function computeConstantFixed(name: ConstantName, prec: number, method?: string, leaf?: number): bigint {
  const r = pick(tables[name], prec);
  return run(name, method ?? r.method, prec, leaf ?? r.leaf);
}
