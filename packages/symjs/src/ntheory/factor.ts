// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Integer factorization and divisors (SymPy sympy.ntheory.factor_):
 * factorint with trial division, Fermat's method, Pollard's rho and p-1
 * and the elliptic curve method (the curve stage of sympy.ntheory.ecm),
 * factorrat, primefactors, divisors, divisor counts, multiplicity,
 * perfect_power, perfect/abundant/deficient/amicable numbers and digital
 * roots. Integers are returned as bigints and dicts as Maps in SymPy's
 * insertion order.
 */

import type { Expr } from '../core/nodes';
import { Mul, Pow, Rational, S } from '../core/nodes';
import { at, defined, expectType, first, getOrThrow, last } from '../core/guard';
import { sympify } from '../core/ops';
import { gcd } from '../core/numbers';
import type { UnsolvedResult } from '../core/truth';
import { Unsolved, isNoMatch } from '../core/truth';
import { digits } from './digits';
import type { IntLike } from './intutil';
import { asInt, babs, bitLength, bitScan1, divmod, fdiv, gcdN, invert, iroot, isFactorial, isqrt, pmod, powmod, pyLog2, pyLogBase, remove, sqrtrem, truncInt } from './intutil';
import { MERSENNE_PRIME_EXPONENTS, factorCache, isMersennePrime, isprime } from './primetest';
import { primerange, nextprime } from './generate';
import { randintFrom } from './random';
import { sieve } from './sieve';

const cmpBig = (a: bigint, b: bigint): number => (a < b ? -1 : a > b ? 1 : 0);
const sortedKeys = (m: ReadonlyMap<bigint, bigint>): bigint[] => [...m.keys()].sort(cmpBig);

// ---------------------------------------------------------------------------
// multiplicity
// ---------------------------------------------------------------------------

/**
 * The exponent of p in n!.
 *
 * @param pIn - Integer factor greater than one.
 * @param nIn - Nonnegative argument of the factorial.
 * @returns The highest exponent dividing the factorial.
 * @throws RangeError when the factor is at most one or the factorial argument is negative.
 * @see SymPy `sympy.ntheory.factor_.multiplicity_in_factorial`
 * @example
 * ```ts
 * import { multiplicityInFactorial } from '@symjs/symjs';
 *
 * multiplicityInFactorial(2, 3); // => 1
 * multiplicityInFactorial(10, 25); // => 6
 * ```
 */
export function multiplicityInFactorial(pIn: IntLike, nIn: IntLike): bigint {
  const p = asInt(pIn);
  const n = asInt(nIn);
  if (p <= 0n) throw new RangeError(`expecting positive integer got ${p}`);
  if (n < 0n) throw new RangeError(`expecting non-negative integer got ${n}`);
  // every power of 1 divides n! (SymPy raises ValueError: min() of an empty sequence)
  if (p === 1n) throw new RangeError('the multiplicity of 1 in n! is not defined');
  const f = new Map<bigint, bigint>();
  for (const [k, v] of factorintInt(p, {})) {
    const prev = f.get(v);
    f.set(v, prev !== undefined && prev > k ? prev : k);
  }
  return [...f]
    .map(([v, k]) => fdiv(fdiv(n + k - digits(n, k).reduce((a, b) => a + b, 0n), k - 1n), v))
    .reduce((a, b) => (a < b ? a : b));
}

/**
 * The greatest integer m such that p**m divides n; also for Rationals (possibly negative) and for
 * an unevaluated factorial(k) as n.
 *
 * @param pIn - Factor whose multiplicity to measure.
 * @param nIn - Number or unevaluated factorial to examine.
 * @returns The exponent with which the factor divides the value.
 * @throws RangeError when the multiplicity is undefined for the supplied values.
 * @throws TypeError when the values cannot be interpreted as integers or rationals.
 * @see SymPy `sympy.ntheory.factor_.multiplicity`
 * @example
 * ```ts
 * import { ex, multiplicity } from '@symjs/symjs';
 *
 * multiplicity(3, ex`1/9`); // => -2
 * ```
 */
export function multiplicity(pIn: IntLike, nIn: IntLike): bigint {
  const pe = typeof pIn === 'bigint' || typeof pIn === 'number' ? Rational.of(asInt(pIn)) : sympify(pIn);
  const ne = typeof nIn === 'bigint' || typeof nIn === 'number' ? Rational.of(asInt(nIn)) : sympify(nIn);
  if (pe instanceof Rational && ne instanceof Rational) {
    if (pe.q !== 1n || ne.q !== 1n) {
      if (pe.q === 1n) {
        if (ne.p === 1n) return -multiplicity(pe.p, ne.q);
        return multiplicity(pe.p, ne.p) - multiplicity(pe.p, ne.q);
      }
      if (pe.p === 1n) return multiplicity(pe.q, ne.q);
      const like = [multiplicity(pe.p, ne.p), multiplicity(pe.q, ne.q)].reduce((a, b) => (a < b ? a : b));
      const cross = [multiplicity(pe.q, ne.p), multiplicity(pe.p, ne.q)].reduce((a, b) => (a < b ? a : b));
      return like - cross;
    }
    if (ne.p === 0n) throw new RangeError(`no such integer exists: multiplicity of ${ne.p} is not-defined`);
    return remove(ne.p, pe.p)[1];
  }
  if (pe instanceof Rational && pe.q === 1n && isFactorial(ne)) {
    const k = first(ne.args);
    if (k instanceof Rational && k.q === 1n && k.p >= 0n) return multiplicityInFactorial(pe.p, k.p);
  }
  throw new TypeError(`expecting ints or fractions, got ${pe.toString()} and ${ne.toString()}`);
}

// ---------------------------------------------------------------------------
// perfect powers
// ---------------------------------------------------------------------------

function ppDone(n: bigint, factors: Map<bigint, bigint>, gIn: bigint, multi: bigint): [bigint, bigint] | false {
  const g = gcd(gIn, multi);
  if (g === 1n) return false;
  factors.set(n, multi);
  let r = 1n;
  for (const [p, e] of factors) r *= p ** (e / g);
  return [r, g];
}

/** @internal SymPy _perfect_power(n, next_p): (b, e) with b**e == n and e maximal, or false. */
export function perfectPowerInt(nIn: bigint, nextPIn: bigint = 2n): [bigint, bigint] | false {
  let n = nIn;
  let nextP = nextPIn;
  if (n <= 3n) return false;
  const factors = new Map<bigint, bigint>();
  let g = 0n;
  let multi = 1n;
  if (n <= 1000000n) {
    n = factorintSmall(factors, n, 1000n, 1000, nextP)[0];
    if (n > 1n) return false;
    g = gcdN(...factors.values());
    if (g === 1n) return false;
    let r = 1n;
    for (const [p, e] of factors) r *= p ** (e / g);
    return [r, g];
  }
  if (nextP < 3n) {
    g = BigInt(bitScan1(n));
    if (g !== 0n) {
      if (g === 1n) return false;
      n >>= g;
      factors.set(2n, g);
      if (n === 1n) return [2n, g];
      const [m, exact] = iroot(n, g);
      if (exact) return [2n * m, g];
      if (isprime(g)) return false;
    }
    nextP = 3n;
  }
  while ((n & 7n) === 1n) {
    const [m, exact] = iroot(n, 2n);
    if (!exact) break;
    n = m;
    multi <<= 1n;
  }
  if (n < nextP ** 3n) return ppDone(n, factors, g, multi);
  const tfMax = BigInt(Math.floor(bitLength(n) / 27) + 24);
  if (nextP < tfMax) {
    for (const p of primerange(nextP, tfMax)) {
      const [m, t0] = remove(n, p);
      if (t0 === 0n) continue;
      n = m;
      const t = t0 * multi;
      const g2 = gcd(g, t);
      if (g2 === 1n) return false;
      factors.set(p, t);
      if (n === 1n) {
        let r = 1n;
        for (const [q, e] of factors) r *= q ** (e / g2);
        return [r, g2];
      } else if (g === 0n || g2 < g) {
        g = g2;
        const [mm, exact] = iroot(n ** multi, g);
        if (exact) {
          let r = mm;
          for (const [q, e] of factors) r *= q ** (e / g);
          return [r, g];
        } else if (isprime(g)) return false;
      }
    }
    nextP = tfMax;
  }
  if (n < nextP ** 3n) return ppDone(n, factors, g, multi);
  let primeIter: Iterable<bigint>;
  if (g !== 0n) primeIter = sortedKeys(factorintInt(g >> BigInt(bitScan1(g)), {}));
  else primeIter = primerange(3n, BigInt(Math.floor(pyLogBase(n, nextP))) + 2n);
  let logn = pyLog2(n);
  const threshold = logn / 40;
  for (const p of primeIter) {
    if (threshold < Number(p)) {
      for (;;) {
        const b = Math.pow(2, logn / Number(p));
        const rb = BigInt(Math.floor(b + 0.5));
        if (Math.abs(Number(rb) - b) < 0.01 && rb ** p === n) {
          n = rb;
          multi *= p;
          logn = pyLog2(n);
        } else break;
      }
    } else {
      for (;;) {
        const [m, exact] = iroot(n, p);
        if (!exact) break;
        n = m;
        multi *= p;
        logn = pyLog2(n);
      }
    }
    if (n < nextP ** (p + 2n)) break;
  }
  return ppDone(n, factors, g, multi);
}

/** Options of perfectPower. */
export interface PerfectPowerOptions {
  /** Return the largest exponent (default true); false: the smallest prime exponent. */
  big?: boolean;
  /** Use trial division by small factors (default true). */
  factor?: boolean;
}

function perfectPowerBig(nIn: bigint, candidatesIn: readonly bigint[] | undefined, big: boolean, factor: boolean): [bigint, bigint] | false {
  const n = nIn;
  if (n < 0n) {
    if (candidatesIn === undefined) {
      const pp = perfectPowerBig(-n, undefined, true, factor);
      if (pp === false) return false;
      let [b, e] = pp;
      const e2 = e & -e;
      b = b ** e2;
      e = e / e2;
      if (e <= 1n) return false;
      if (big) return [-b, e];
      // the smallest prime factor of the odd e > 1
      const p = first(primefactors(e));
      return [-(b ** (e / p)), p];
    }
    const odd = [...new Set(candidatesIn.filter((i) => i % 2n !== 0n))];
    if (odd.length === 0) return false;
    const pp = perfectPowerBig(-n, odd, big, factor);
    if (pp !== false) return [-pp[0], pp[1]];
    return false;
  }
  if (candidatesIn === undefined && big) return perfectPowerInt(n);
  if (n <= 3n) return false;
  const logn = pyLog2(n);
  const maxPossible = BigInt(Math.floor(logn)) + 2n;
  const notSquare = [2n, 3n, 7n, 8n].includes(n % 10n);
  const minPossible = 2n + (notSquare ? 1n : 0n);
  let candidates: Iterable<bigint>;
  if (candidatesIn === undefined || candidatesIn.length === 0) candidates = primerange(minPossible, maxPossible);
  else {
    let cs = [...new Set(candidatesIn)].filter((i) => minPossible <= i && i < maxPossible).sort(cmpBig);
    if (n % 2n === 0n) {
      const e = BigInt(bitScan1(n));
      cs = cs.filter((i) => e % i === 0n);
    }
    if (big) cs.reverse();
    for (const e of cs) {
      const [r, ok] = iroot(n, e);
      if (ok) return [r, e];
    }
    return false;
  }
  let fac = 2n + (n % 2n);
  for (const e0 of candidates) {
    let e = e0;
    const f = fac;
    fac = nextprime(fac);
    if (factor && n % f === 0n) {
      e = remove(n, f)[1];
      if (e === 1n) return false;
      let [r, exact] = iroot(n, e);
      if (!exact) {
        const m = n / f ** e;
        const rE = perfectPowerBig(m, [...divisorsGen(e, false)], true, true);
        if (rE === false) return false;
        const [r2, E] = rE;
        r = f ** (e / E) * r2;
        e = E;
      }
      if (!big) {
        const e0s = primefactors(e);
        if (e0s[0] !== e) {
          const e0 = first(e0s);
          r = r ** (e / e0);
          e = e0;
        }
      }
      return [r, e];
    }
    if (logn / Number(e) < 40) {
      const b = 2.0 ** (logn / Number(e));
      if (Math.abs(Math.floor(b + 0.5) - b) > 0.01) continue;
    }
    const [r, exact] = iroot(n, e);
    if (exact) {
      let rr = r;
      let ee = e;
      if (big) {
        const m = perfectPowerBig(r, undefined, big, factor);
        if (m !== false) {
          rr = m[0];
          ee = e * m[1];
        }
      }
      return [rr, ee];
    }
  }
  return false;
}

/**
 * Determines whether a number is an exact power with an integer exponent greater than one.
 *
 * @remarks SymPy prints the base and exponent as tuples, `(2, 4)` and `(-2, 3)`.
 * @param n - Number to decompose.
 * @param candidates - Exponents to consider.
 * @param opts - Exponent selection and trial-division settings.
 * @returns The base and exponent, or `false` if no power qualifies.
 * @throws TypeError when the expression cannot be interpreted as an integer or rational.
 * @see SymPy `sympy.ntheory.factor_.perfect_power`
 * @example
 * ```ts
 * import { perfectPower } from '@symjs/symjs';
 *
 * perfectPower(16); // => [2, 4]
 * perfectPower(-8); // => [-2, 3]
 * ```
 */
export function perfectPower(n: bigint | number, candidates?: readonly (bigint | number)[], opts?: PerfectPowerOptions): [bigint, bigint] | false;
/**
 * Determines whether a number is an exact power with an integer exponent greater than one.
 *
 * @remarks SymPy prints the base and exponent as tuples, `(2, 4)` and `(-2, 3)`.
 * @param n - Number to decompose.
 * @param candidates - Exponents to consider.
 * @param opts - Exponent selection and trial-division settings.
 * @returns The base and exponent, or `false` if no power qualifies.
 * @throws TypeError when the expression cannot be interpreted as an integer or rational.
 * @see SymPy `sympy.ntheory.factor_.perfect_power`
 */
export function perfectPower(n: IntLike, candidates?: readonly (bigint | number)[], opts?: PerfectPowerOptions): [bigint | Rational, bigint] | false;
export function perfectPower(nIn: IntLike, candidatesIn?: readonly (bigint | number)[], opts: PerfectPowerOptions = {}): [bigint | Rational, bigint] | false {
  const big = opts.big ?? true;
  const factor = opts.factor ?? true;
  const candidates = candidatesIn?.map((c) => BigInt(c));
  const e = typeof nIn === 'bigint' || typeof nIn === 'number' ? Rational.of(asInt(nIn)) : sympify(nIn);
  if (!(e instanceof Rational)) throw new TypeError(`${e.toString()} is not an integer`);
  if (e.q === 1n) return perfectPowerBig(e.p, candidates, big, factor);
  if (e.p < 0n) {
    const pos = Rational.of(-e.p, e.q);
    if (candidates === undefined) {
      const pp = perfectPower(pos, undefined, { big: true, factor });
      if (pp === false) return false;
      const b = expectType(pp[0], isRational, 'base of a rational perfect power');
      const e2 = pp[1] & -pp[1];
      const bb = Rational.of(b.p ** e2, b.q ** e2);
      const ee = pp[1] / e2;
      if (ee <= 1n) return false;
      if (big) return [Rational.of(-bb.p, bb.q), ee];
      // the smallest prime factor of the odd ee > 1
      const pr = first(primefactors(ee));
      return [Rational.of(-(bb.p ** (ee / pr)), bb.q ** (ee / pr)), pr];
    }
    const odd = candidates.filter((i) => i % 2n !== 0n);
    if (odd.length === 0) return false;
    const pp = perfectPower(pos, odd, { big, factor });
    if (pp === false) return false;
    const b = expectType(pp[0], isRational, 'base of a rational perfect power');
    return [Rational.of(-b.p, b.q), pp[1]];
  }
  const p = e.p;
  const q = e.q;
  if (p === 1n) {
    const qq = perfectPowerBig(q, candidates, big, factor);
    return qq === false ? false : [Rational.of(1n, qq[0]), qq[1]];
  }
  const pp = perfectPowerBig(p, undefined, true, factor);
  if (pp === false) return false;
  const qq = perfectPowerBig(q, undefined, true, factor);
  if (qq === false) return false;
  const [numBase, numExp] = pp;
  const [denBase, denExp] = qq;
  const tuple = (x: bigint): [Rational, bigint] => [Rational.of(numBase ** (numExp / x), denBase ** (denExp / x)), x];
  if (candidates !== undefined && candidates.length > 0) {
    const valid = candidates.filter((i) => numExp % i === 0n && denExp % i === 0n);
    if (valid.length === 0) return false;
    return tuple(valid.reduce((a, b) => (big ? (a > b ? a : b) : a < b ? a : b)));
  }
  const g = gcd(numExp, denExp);
  if (g === 1n) return false;
  return tuple(big ? g : first(primefactors(g)));
}

// ---------------------------------------------------------------------------
// Pollard's rho and p-1
// ---------------------------------------------------------------------------

/** Configures the iteration and restarts used in Pollard’s rho factor search. */
export interface PollardRhoOptions {
  /** The initial value (default 2). */
  s?: bigint | number;
  /** The constant of the default F(x) = x**2 + a (default 1). */
  a?: bigint | number;
  /** The number of retries with random s and a (default 5). */
  retries?: number;
  /** The seed of the random retries (default 1234). */
  seed?: bigint | number;
  /** The maximum number of steps per try (default unbounded). */
  maxSteps?: number;
  /** The iteration function (default x**2 + a mod n). */
  F?: (x: bigint) => bigint;
}

/**
 * Searches for a nontrivial factor by Pollard’s rho method.
 *
 * @param nIn - Composite integer to split.
 * @param opts - Parameters and retry limits for the factor search.
 * @returns A nontrivial divisor, or `Unsolved` if the attempts fail.
 * @throws RangeError when the integer is less than five.
 * @see SymPy `sympy.ntheory.factor_.pollard_rho`
 * @example
 * ```ts
 * import { pollardRho } from '@symjs/symjs';
 *
 * pollardRho(16843009, { a: 16843007, retries: 1 }); // => 257
 * ```
 */
export function pollardRho(nIn: IntLike, opts: PollardRhoOptions = {}): bigint | UnsolvedResult {
  const n = truncInt(nIn);
  if (n < 5n) throw new RangeError('pollard_rho should receive n > 4');
  const retries = opts.retries ?? 5;
  let a = BigInt(opts.a ?? 1);
  const maxSteps = opts.maxSteps ?? 0;
  const randint = randintFrom(BigInt(opts.seed ?? 1234) + BigInt(retries));
  let V = BigInt(opts.s ?? 2);
  let F: ((x: bigint) => bigint) | undefined = opts.F;
  for (let i = 0; i < retries + 1; i++) {
    let U = V;
    if (F === undefined) {
      const aa = a;
      F = (x: bigint) => pmod(powmod(x, 2n, n) + aa, n);
    }
    const f = F;
    let j = 0;
    for (;;) {
      if (maxSteps && j > maxSteps) break;
      j++;
      U = f(U);
      V = f(f(V));
      const g = gcd(U - V, n);
      if (g === 1n) continue;
      if (g === n) break;
      return g;
    }
    V = randint(0n, n - 1n);
    a = randint(1n, n - 3n);
    F = undefined;
  }
  return Unsolved;
}

/** Configures the smoothness bound, starting base and restarts for Pollard’s p − 1 method. */
export interface PollardPm1Options {
  /** The smoothness bound (default 10). */
  B?: bigint | number;
  /** The base (default 2). */
  a?: bigint | number;
  /** The number of retries with random bases (default 0). */
  retries?: number;
  /** The seed of the random retries (default 1234). */
  seed?: bigint | number;
}

/**
 * A nontrivial factor of n by Pollard's p-1 method with smoothness bound B, or Unsolved when the
 * method fails.
 *
 * @param nIn - Composite integer to split.
 * @param opts - Parameters and retry limits for the factor search.
 * @returns A nontrivial divisor, or `Unsolved` if the attempts fail.
 * @throws RangeError when the integer is less than four or the smoothness bound is less than three.
 * @see SymPy `sympy.ntheory.factor_.pollard_pm1`
 * @example
 * ```ts
 * import { pollardPm1 } from '@symjs/symjs';
 *
 * pollardPm1(257 * 1009, { B: 16, a: 3 }); // => 1009
 * ```
 */
export function pollardPm1(nIn: IntLike, opts: PollardPm1Options = {}): bigint | UnsolvedResult {
  const n = truncInt(nIn);
  const B = BigInt(opts.B ?? 10);
  let a = BigInt(opts.a ?? 2);
  const retries = opts.retries ?? 0;
  if (n < 4n || B < 3n) throw new RangeError('pollard_pm1 should receive n > 3 and B > 2');
  const randint = randintFrom(BigInt(opts.seed ?? 1234) + B);
  for (let i = 0; i < retries + 1; i++) {
    let aM = a;
    for (const p of sieve.primerange(2n, B + 1n)) {
      const e = BigInt(Math.floor(pyLogBase(B, p)));
      aM = powmod(aM, p ** e, n);
    }
    const g = gcd(aM - 1n, n);
    if (1n < g && g < n) return g;
    a = randint(2n, n - 2n);
  }
  return Unsolved;
}

// ---------------------------------------------------------------------------
// elliptic curve method (SymPy sympy.ntheory.ecm._ecm_one_factor)
// ---------------------------------------------------------------------------

/**
 * A projective Montgomery-curve point.
 *
 * @see SymPy `sympy.ntheory.ecm.Point`
 */
export class ECMPoint {
  /**
   * Creates a projective Montgomery point modulo the integer being factored.
   *
   * @param x - Projective x-coordinate.
   * @param z - Projective z-coordinate.
   * @param a24 - Montgomery coefficient used for doubling.
   * @param mod - Modulus used for the arithmetic.
   */
  constructor(
    /** The projective X-coordinate. */
    readonly x: bigint,
    /** The projective Z-coordinate. */
    readonly z: bigint,
    /**
     * The Montgomery doubling coefficient.
     *
     * @see SymPy `sympy.ntheory.ecm.Point.a_24`
     */
    readonly a24: bigint,
    /**
     * Computes the remainder on division by the supplied divisor.
     *
     * @see SymPy `sympy.ntheory.ecm.Point.mod`
     */
    readonly mod: bigint,
  ) {}

  /**
   * The projective X coordinate.
   *
   * @returns The projective X-coordinate.
   * @see SymPy `sympy.ntheory.ecm.Point.x_cord`
   */
  get xCord(): bigint {
    return this.x;
  }
  /**
   * The projective Z coordinate.
   *
   * @returns The projective Z-coordinate.
   * @see SymPy `sympy.ntheory.ecm.Point.z_cord`
   */
  get zCord(): bigint {
    return this.z;
  }

  /**
   * Adds the other operand to this value.
   *
   * @param Q - Addend.
   * @param diff - Difference of the two points.
   * @returns The sum of the operands.
   * @see SymPy `sympy.ntheory.ecm.Point.add`
   */
  add(Q: ECMPoint, diff: ECMPoint): ECMPoint {
    const u = (this.x - this.z) * (Q.x + Q.z);
    const v = (this.x + this.z) * (Q.x - Q.z);
    const ad = u + v;
    const sb = u - v;
    return new ECMPoint(pmod(diff.z * ad * ad, this.mod), pmod(diff.x * sb * sb, this.mod), this.a24, this.mod);
  }

  /**
   * Uses Montgomery doubling to compute the sum of the point with itself.
   *
   * @returns Twice the point under the curve group law.
   * @see SymPy `sympy.ntheory.ecm.Point.double`
   */
  double(): ECMPoint {
    const u = powmod(this.x + this.z, 2n, this.mod);
    const v = powmod(this.x - this.z, 2n, this.mod);
    const diff = u - v;
    return new ECMPoint(pmod(u * v, this.mod), pmod(diff * (v + this.a24 * diff), this.mod), this.a24, this.mod);
  }

  /**
   * Multiplies a Montgomery point by a positive integer using differential addition and doubling.
   *
   * @param k - Positive scalar multiplier.
   * @returns The scalar multiple of the point.
   * @throws RangeError when the multiplier is not positive.
   * @see SymPy `sympy.ntheory.ecm.Point.mont_ladder`
   */
  montLadder(k: bigint): ECMPoint {
    if (k < 1n) throw new RangeError('Multiplier must be a positive integer');
    let Q: ECMPoint = this;
    let R = this.double();
    for (const bit of k.toString(2).slice(1)) {
      if (bit === '1') {
        Q = R.add(Q, this);
        R = R.double();
      } else {
        R = Q.add(R, this);
        Q = Q.double();
      }
    }
    return Q;
  }
}

/** @internal One factor of n by Lenstra's elliptic curve method, or undefined (SymPy _ecm_one_factor). */
export function ecmOneFactor(n: bigint, B1 = 10000n, B2 = 100000n, maxCurve = 200, seed?: bigint | number): bigint | undefined {
  const randint = randintFrom(seed);
  const D0 = isqrt(B2);
  const D = D0 < B1 / 2n - 1n ? D0 : B1 / 2n - 1n;
  sieve.extend(D);
  const Dn = Number(D);
  const beta: bigint[] = new Array<bigint>(Dn).fill(0n);
  const Sx: ECMPoint[] = new Array<ECMPoint>(Dn);
  let k = 1n;
  for (const p of primerange(2n, B1 + 1n)) k *= p ** BigInt(Math.floor(pyLogBase(B1, p)));
  const deltasList: bigint[][] = [];
  for (let r = B1 + 2n * D; r < B2 + 2n * D; r += 4n * D) {
    const deltas = new Set<bigint>();
    for (const q of primerange(r - 2n * D, r + 2n * D)) deltas.add(babs(q - r) >> 1n);
    deltasList.push([...deltas]);
  }
  for (let c = 0; c < maxCurve; c++) {
    const sigma = randint(6n, n - 1n);
    const u = pmod(sigma * sigma - 5n, n);
    const v = pmod(4n * sigma, n);
    const u3 = powmod(u, 3n, n);
    let inv: bigint;
    try {
      inv = invert(16n * u3 * v, n);
    } catch {
      const g = gcd(2n * u3 * v, n);
      if (g === n) continue;
      return g;
    }
    const a24 = pmod(powmod(v - u, 3n, n) * (3n * u + v) * inv, n);
    let Q = new ECMPoint(u3, powmod(v, 3n, n), a24, n);
    Q = Q.montLadder(k);
    let g = gcd(Q.z, n);
    if (g !== 1n && g !== n) return g;
    else if (g === n) continue;
    Sx[0] = Q;
    const Q2 = Q.double();
    Sx[1] = Q2.add(Q, Q);
    beta[0] = pmod(Sx[0].x * Sx[0].z, n);
    beta[1] = pmod(Sx[1].x * Sx[1].z, n);
    for (let d = 2; d < Dn; d++) {
      const sd = at(Sx, d - 1).add(Q2, at(Sx, d - 2));
      Sx[d] = sd;
      beta[d] = pmod(sd.x * sd.z, n);
    }
    g = 1n;
    const W = Q.montLadder(4n * D);
    let T = Q.montLadder(B1 - 2n * D);
    let R = Q.montLadder(B1 + 2n * D);
    for (const deltas of deltasList) {
      const alpha = pmod(R.x * R.z, n);
      for (const delta of deltas) {
        const s = at(Sx, Number(delta));
        const f = (R.x - s.x) * (R.z + s.z) - alpha + at(beta, Number(delta));
        g = pmod(g * f, n);
      }
      [T, R] = [R, R.add(W, T)];
    }
    g = gcd(n, g);
    if (g !== 1n && g !== n) return g;
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// factorint
// ---------------------------------------------------------------------------

/** @internal SymPy _factorint_small: trial division; returns [n, next_p] (next_p 0 when done). */
export function factorintSmall(factors: Map<bigint, bigint>, nIn: bigint, limit: bigint, failMax: number, nextPIn: bigint = 2n): [bigint, bigint] {
  let n = nIn;
  let nextP = nextPIn;
  const done = (m: bigint, d: bigint): [bigint, bigint] => (d * d <= m ? [m, d] : [m, 0n]);
  const limit2 = limit * limit;
  let threshold2 = n < limit2 ? n : limit2;
  if (nextP < 3n) {
    if ((n & 1n) === 0n) {
      const m = BigInt(bitScan1(n));
      factors.set(2n, m);
      n >>= m;
      threshold2 = n < limit2 ? n : limit2;
    }
    nextP = 3n;
    if (threshold2 < 9n) return done(n, nextP);
  }
  if (nextP < 5n) {
    if (n % 3n === 0n) {
      n /= 3n;
      let m = 1n;
      while (n % 3n === 0n) {
        n /= 3n;
        m++;
        if (m === 20n) {
          const [nn, mm] = remove(n, 3n);
          n = nn;
          m += mm;
          break;
        }
      }
      factors.set(3n, m);
      threshold2 = n < limit2 ? n : limit2;
    }
    nextP = 5n;
    if (threshold2 < 25n) return done(n, nextP);
  }
  const p6 = nextP % 6n;
  nextP += (p6 < 2n ? -1n : 5n) - p6;
  let fails = 0;
  const step = (): void => {
    if (n % nextP !== 0n) fails++;
    else {
      n /= nextP;
      let m = 1n;
      while (n % nextP === 0n) {
        n /= nextP;
        m++;
        if (m === 20n) {
          const [nn, mm] = remove(n, nextP);
          n = nn;
          m += mm;
          break;
        }
      }
      factors.set(nextP, m);
      fails = 0;
      threshold2 = n < limit2 ? n : limit2;
    }
  };
  while (fails < failMax) {
    step();
    nextP += 2n;
    if (threshold2 < nextP * nextP) return done(n, nextP);
    step();
    nextP += 4n;
    if (threshold2 < nextP * nextP) return done(n, nextP);
  }
  return done(n, nextP);
}

/** Selects factorization methods, search limits and the form of the result. */
export interface FactorintOptions {
  /** Trial division only up to this bound (composite factors may remain). */
  limit?: bigint | number;
  /** Use trial division (default true). */
  useTrial?: boolean;
  /** Use Pollard's rho (default true). */
  useRho?: boolean;
  /** Use Pollard's p-1 (default true). */
  usePm1?: boolean;
  /** Use the elliptic curve method (default true). */
  useEcm?: boolean;
  /** Return the factorization as an unevaluated product (true), or as a Map (false). */
  visual?: boolean;
  /** Return the list of prime factors with multiplicity. */
  multiple?: boolean;
}

interface Opts {
  limit?: bigint;
  useTrial?: boolean;
  useRho?: boolean;
  usePm1?: boolean;
  useEcm?: boolean;
  /** The first ECM bound B1 (10000; a test sets a small one to see it widen). */
  ecmB1?: bigint;
}

function trial(factors: Map<bigint, bigint>, nIn: bigint, candidates: Iterable<bigint>): [bigint, boolean] {
  let n = nIn;
  const nf = factors.size;
  for (const d of candidates) {
    if (n % d === 0n) {
      if (n !== d) factorCache.set(n, d);
      const [m, e] = remove(n / d, d);
      n = m;
      factors.set(d, e + 1n);
    }
  }
  return [n, factors.size !== nf];
}

function checkTermination(factors: Map<bigint, bigint>, n: bigint, limit: bigint | undefined, useTrial: boolean, useRho: boolean, usePm1: boolean, nextP: bigint): boolean {
  if (n === 1n) return true;
  if (n < nextP * nextP || isprime(n)) {
    factorCache.set(n, n);
    factors.set(n, 1n);
    return true;
  }
  const p = perfectPowerInt(n, nextP);
  if (p === false) return false;
  const [base, exp] = p;
  if (base < nextP * nextP || isprime(base)) {
    factorCache.set(n, base);
    factors.set(base, exp);
  } else {
    const facs = factorintInt(base, { limit, useTrial, useRho, usePm1 });
    for (const [b, e] of facs) factors.set(b, exp * e);
  }
  return true;
}

const SMALL: Record<number, [bigint, bigint][]> = {
  0: [[0n, 1n]],
  1: [],
  2: [[2n, 1n]],
  3: [[3n, 1n]],
  4: [[2n, 2n]],
  5: [[5n, 1n]],
  6: [
    [2n, 1n],
    [3n, 1n],
  ],
  7: [[7n, 1n]],
  8: [[2n, 3n]],
  9: [[3n, 2n]],
};

/** @internal factorint of an integer: the Map prime -> exponent. */
export function factorintInt(nIn: bigint, o: Opts): Map<bigint, bigint> {
  let n = nIn;
  const useTrial = o.useTrial ?? true;
  const useRho = o.useRho ?? true;
  const usePm1 = o.usePm1 ?? true;
  let useEcm = o.useEcm ?? true;
  let limit = o.limit;
  if (limit === 0n) limit = undefined;
  if (limit !== undefined) useEcm = false;
  if (n < 0n) {
    const f = factorintInt(-n, { limit, useTrial, useRho, usePm1 });
    f.set(-1n, 1n);
    return f;
  }
  if (limit !== undefined && limit < 2n) return n === 1n ? new Map() : new Map([[n, 1n]]);
  if (n < 10n) return new Map(SMALL[Number(n)]);
  const factors = new Map<bigint, bigint>();
  let small = 1n << 15n;
  const failMax = 600;
  if (limit !== undefined && limit < small) small = limit;
  let nextP: bigint;
  [n, nextP] = factorintSmall(factors, n, small, failMax);
  if (nextP === 0n) {
    if (n > 1n) factors.set(n, 1n);
    return factors;
  }
  for (;;) {
    const p = factorCache.get(n);
    if (isNoMatch(p)) break;
    const [m, e] = remove(n, p);
    n = m;
    factors.set(p, e);
  }
  if (limit !== undefined && nextP > limit) {
    // n > 1 when checkTermination fails
    if (!checkTermination(factors, n, limit, useTrial, useRho, usePm1, nextP)) factors.set(n, 1n);
    return factors;
  }
  if (checkTermination(factors, n, limit, useTrial, useRho, usePm1, nextP)) return factors;
  const sqrtN = isqrt(n);
  let a = sqrtN + 1n;
  if ((n % 4n === 1n) !== ((a & 1n) === 1n)) a += 1n;
  let b2 = a * a - n;
  for (let i = 0; i < 3; i++) {
    const [b, fermat] = sqrtrem(b2);
    if (fermat === 0n) {
      for (const r of [a - b, a + b]) {
        const facs = factorintInt(r, { limit, useTrial, useRho, usePm1 });
        for (const [k, v] of facs) factors.set(k, (factors.get(k) ?? 0n) + v);
        factorCache.add(n, [...facs.keys()]);
      }
      return factors;
    }
    b2 += (a + 1n) << 2n;
    a += 2n;
  }
  let low = nextP;
  let high = 2n * nextP;
  const limitP1 = (limit ?? sqrtN) + 1n;
  let iteration = 0;
  const sub = (c: bigint): bigint[] => (c < nextP * nextP || isprime(c) ? [c] : [...factorintInt(c, { limit, useTrial, useRho, usePm1, useEcm }).keys()]);
  for (;;) {
    const highL = high < limitP1 ? high : limitP1;
    let foundTrial: boolean;
    if (useTrial) {
      [n, foundTrial] = trial(factors, n, sieve.primerange(low, highL));
      nextP = highL;
      if (foundTrial && checkTermination(factors, n, limit, useTrial, useRho, usePm1, nextP)) return factors;
    } else foundTrial = false;
    if (high > limitP1) {
      // n > 1: a factorization that ends returns through checkTermination
      factors.set(n, 1n);
      return factors;
    }
    if (!foundTrial) {
      if (usePm1) {
        const c = pollardPm1(n, { B: low, seed: highL });
        if (typeof c === 'bigint') {
          n = trial(factors, n, sub(c))[0];
          if (checkTermination(factors, n, limit, useTrial, useRho, usePm1, nextP)) return factors;
        }
      }
      if (useRho) {
        const c = pollardRho(n, { retries: 1, maxSteps: Number(low), seed: highL });
        if (typeof c === 'bigint') {
          n = trial(factors, n, sub(c))[0];
          if (checkTermination(factors, n, limit, useTrial, useRho, usePm1, nextP)) return factors;
        }
      }
    }
    iteration++;
    if (useEcm && iteration >= 3 && n.toString().length >= 24) break;
    [low, high] = [high, high * 2n];
  }
  let B1 = o.ecmB1 ?? 10000n;
  let B2 = 100n * B1;
  let numCurves = 50;
  for (;;) {
    const factor = ecmOneFactor(n, B1, B2, numCurves, B1);
    if (factor !== undefined) {
      n = trial(factors, n, sub(factor))[0];
      if (checkTermination(factors, n, limit, useTrial, useRho, usePm1, nextP)) return factors;
    }
    B1 *= 5n;
    B2 = 100n * B1;
    numCurves *= 4;
  }
}

/** factorial(x) as a Map, by Legendre's formula for x >= 20. */
function factorintFactorial(x: bigint): Map<bigint, bigint> {
  const factors = new Map<bigint, bigint>();
  let m = 2n;
  for (const p of sieve.primerange(2n, x + 1n)) {
    if (m > 1n) {
      m = 0n;
      let q = x / p;
      while (q !== 0n) {
        m += q;
        q /= p;
      }
    }
    factors.set(p, m);
  }
  return factors;
}

/** The unevaluated product of p**e (SymPy factorint(..., visual=True)). */
function visualOf(fd: Map<bigint, bigint>): Expr {
  if (fd.size === 0) return S.One;
  const args: Expr[] = [];
  const d = new Map(fd);
  if (d.has(-1n)) {
    d.delete(-1n);
    args.push(S.NegOne);
  }
  for (const k of sortedKeys(d)) args.push(new Pow(Rational.of(k), Rational.of(getOrThrow(d, k))));
  return args.length === 1 ? first(args) : new Mul(args);
}

function listOf(fac: Map<bigint, bigint>): (bigint | Rational)[] {
  const out: (bigint | Rational)[] = [];
  for (const p of sortedKeys(fac)) {
    const e = getOrThrow(fac, p);
    for (let i = 0n; i < (e > 0n ? e : -e); i++) out.push(e > 0n ? p : Rational.of(1n, p));
  }
  return out;
}

const isRational = (x: unknown): x is Rational => x instanceof Rational;

/** Whether the factorint argument is a map of factors. */
const isFactorMap = (n: IntLike | ReadonlyMap<bigint | number, bigint | number>): n is ReadonlyMap<bigint | number, bigint | number> => n instanceof Map;

const optsOf = (o: FactorintOptions): Opts => ({
  limit: o.limit === undefined ? undefined : truncInt(o.limit),
  useTrial: o.useTrial,
  useRho: o.useRho,
  usePm1: o.usePm1,
  useEcm: o.useEcm,
});

/** The factors of an unevaluated Mul as SymPy's as_powers_dict with int keys. */
function mulPowers(m: Mul): Map<bigint, bigint> {
  const d = new Map<bigint, bigint>();
  for (const a of m.args) {
    let b: Expr = a;
    let e = 1n;
    if (a instanceof Pow && a.exp instanceof Rational && a.exp.q === 1n) {
      b = a.base;
      e = a.exp.p;
    }
    const k = truncInt(b);
    d.set(k, (d.get(k) ?? 0n) + e);
  }
  return d;
}

/**
 * The prime factorization of an integer as a `Map` from each prime to its
 * exponent, in SymPy's order. A negative number includes the factor `-1`, and
 * `factorint(0)` is `{0: 1}`. The argument may also be a `Map` of factors, an
 * unevaluated product or an unevaluated `factorial(k)`, which are factored
 * further.
 *
 * @param n - The integer to factor.
 * @param opts - `limit` bounds the trial division (the result may then hold
 *   composite factors); `useTrial`, `useRho`, `usePm1` and `useEcm` select the
 *   methods; `multiple` gives the list of the factors; `visual` gives an
 *   unevaluated product.
 * @returns The factorization.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 * @example
 * ```ts
 * import { factorint } from '@symjs/symjs';
 *
 * factorint(2000); // => {2: 4, 5: 3}
 * factorint(65537); // => {65537: 1}
 * factorint(-12); // => {2: 2, 3: 1, -1: 1}
 * factorint(3n * 101n ** 7n, { limit: 5 }); // => {3: 1, 101: 7}
 * factorint(24, { multiple: true }); // => [2, 2, 2, 3]
 * factorint(4200, { visual: true }); // => 2**3*3**1*5**2*7**1
 * ```
 */
export function factorint(n: bigint | number, opts: FactorintOptions & { multiple: true }): bigint[];
/**
 * Factors the integer or factor map using the requested output format.
 *
 * @param n - Integer, rational or factor map to factor.
 * @param opts - Factorization methods and output format.
 * @returns A list of factors with multiplicity.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 */
export function factorint(n: IntLike | ReadonlyMap<bigint | number, bigint | number>, opts: FactorintOptions & { multiple: true }): (bigint | Rational)[];
/**
 * Factors the integer or factor map using the requested output format.
 *
 * @param n - Integer, rational or factor map to factor.
 * @param opts - Factorization methods and output format.
 * @returns An unevaluated product.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 */
export function factorint(n: IntLike | ReadonlyMap<bigint | number, bigint | number>, opts: FactorintOptions & { visual: true }): Expr;
/**
 * Factors the integer or factor map using the requested output format.
 *
 * @param n - Integer, rational or factor map to factor.
 * @param opts - Factorization methods and output format.
 * @returns A map from prime factors to exponents.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 */
export function factorint(n: ReadonlyMap<bigint | number, bigint | number>, opts: FactorintOptions & { visual: false }): Map<bigint, bigint>;
/**
 * Factors the integer or factor map using the requested output format.
 *
 * @param n - Integer, rational or factor map to factor.
 * @param opts - Factorization methods and output format.
 * @returns An unevaluated product.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 */
export function factorint(n: ReadonlyMap<bigint | number, bigint | number>, opts?: FactorintOptions): Expr;
/**
 * Factors the integer or factor map using the requested output format.
 *
 * @param n - Integer, rational or factor map to factor.
 * @param opts - Factorization methods and output format.
 * @returns A map from prime factors to exponents.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 */
export function factorint(n: IntLike, opts?: FactorintOptions): Map<bigint, bigint>;
export function factorint(nIn: IntLike | ReadonlyMap<bigint | number, bigint | number>, opts: FactorintOptions = {}): Map<bigint, bigint> | Expr | (bigint | Rational)[] {
  const o = optsOf(opts);
  if (opts.multiple === true) {
    const plain: FactorintOptions & { visual: false } = { ...opts, visual: false, multiple: false };
    const fac = isFactorMap(nIn) ? factorint(nIn, plain) : factorint(nIn, plain);
    return listOf(fac);
  }
  const visual = opts.visual;
  const mapIn = isFactorMap(nIn) ? nIn : undefined;
  const intIn = isFactorMap(nIn) ? undefined : nIn;
  const isMap = mapIn !== undefined;
  let mulIn: Mul | undefined;
  let e: Expr | undefined;
  if (intIn !== undefined && typeof intIn !== 'bigint' && typeof intIn !== 'number') {
    e = sympify(intIn);
    if (e instanceof Mul) mulIn = e;
  }
  let fd = new Map<bigint, bigint>();
  if (visual === true && intIn !== undefined && mulIn === undefined) fd = factorint(intIn, { ...opts, visual: false });
  else if (mulIn !== undefined) fd = mulPowers(mulIn);
  else if (mapIn !== undefined) for (const [k, v] of mapIn) fd.set(BigInt(k), BigInt(v));
  if (fd.size > 0 && (isMap || mulIn !== undefined)) {
    for (const key of [...fd.keys()]) {
      if (isprime(key)) continue;
      const ex = getOrThrow(fd, key);
      fd.delete(key);
      for (const [k, v] of factorintInt(key, o)) fd.set(k, (fd.get(k) ?? 0n) + v * ex);
    }
  }
  if (visual === true || (isMap && visual === undefined)) return visualOf(fd);
  if (isMap || mulIn !== undefined) return fd;
  if (e !== undefined && isFactorial(e)) {
    const x = asInt(first(e.args));
    if (x >= 20n) return factorintFactorial(x);
    let f = 1n;
    for (let i = 2n; i <= x; i++) f *= i;
    return factorintInt(f, o);
  }
  return factorintInt(asInt(e ?? defined(intIn, 'integer argument')), o);
}

/**
 * The factorization of a Rational as a Map prime -> exponent (negative for the denominator);
 * `visual` and `multiple` as in factorint.
 *
 * @param rat - Rational number to factor.
 * @param opts - Factorization methods and output format.
 * @returns A list of prime factors and reciprocals with multiplicity.
 * @throws TypeError when the value is not rational.
 * @see SymPy `sympy.ntheory.factor_.factorrat`
 * @example
 * ```ts
 * import { ex, factorrat } from '@symjs/symjs';
 *
 * factorrat(ex`8/9`); // => {2: 3, 3: -2}
 * factorrat(ex`-1/987`); // => {-1: 1, 3: -1, 7: -1, 47: -1}
 * ```
 */
export function factorrat(rat: IntLike, opts: FactorintOptions & { multiple: true }): (bigint | Rational)[];
/**
 * The factorization of a Rational as a Map prime -> exponent (negative for the denominator);
 * `visual` and `multiple` as in factorint.
 *
 * @param rat - Rational number to factor.
 * @param opts - Factorization methods and output format.
 * @returns An unevaluated product of prime powers.
 * @throws TypeError when the value is not rational.
 * @see SymPy `sympy.ntheory.factor_.factorrat`
 */
export function factorrat(rat: IntLike, opts: FactorintOptions & { visual: true }): Expr;
/**
 * The factorization of a Rational as a Map prime -> exponent (negative for the denominator);
 * `visual` and `multiple` as in factorint.
 *
 * @param rat - Rational number to factor.
 * @param opts - Factorization methods and output format.
 * @returns A map from primes to signed exponents.
 * @throws TypeError when the value is not rational.
 * @see SymPy `sympy.ntheory.factor_.factorrat`
 */
export function factorrat(rat: IntLike, opts?: FactorintOptions): Map<bigint, bigint>;
export function factorrat(ratIn: IntLike, opts: FactorintOptions = {}): Map<bigint, bigint> | Expr | (bigint | Rational)[] {
  const r = typeof ratIn === 'bigint' || typeof ratIn === 'number' ? Rational.of(asInt(ratIn)) : sympify(ratIn);
  if (!(r instanceof Rational)) throw new TypeError(`${r.toString()} is not a Rational`);
  const o = optsOf(opts);
  const f = new Map(factorintInt(r.p, o));
  for (const [p, e] of factorintInt(r.q, o)) f.set(p, (f.get(p) ?? 0n) - e);
  if (opts.multiple === true) {
    const key = (p: bigint): number => (getOrThrow(f, p) > 0n ? Number(p) : 1 / Number(p));
    const out: (bigint | Rational)[] = [];
    for (const p of [...f.keys()].sort((x, y) => key(x) - key(y))) {
      const e = getOrThrow(f, p);
      for (let i = 0n; i < (e > 0n ? e : -e); i++) out.push(e > 0n ? p : Rational.of(1n, p));
    }
    return out;
  }
  if (opts.visual !== true) return f;
  return visualOf(f);
}

/**
 * Lists distinct prime factors in ascending order.
 *
 * @param nIn - Integer to factor.
 * @param opts - Use `limit` to bound the factor search.
 * @returns The distinct known prime divisors in ascending order.
 * @see SymPy `sympy.ntheory.factor_.primefactors`
 * @example
 * ```ts
 * import { primefactors } from '@symjs/symjs';
 *
 * primefactors(6); // => [2, 3]
 * primefactors(-5); // => [5]
 * ```
 */
export function primefactors(nIn: IntLike, opts: { limit?: bigint | number } = {}): bigint[] {
  const n = truncInt(nIn);
  const factors = sortedKeys(factorintInt(n, { limit: opts.limit === undefined ? undefined : truncInt(opts.limit) }));
  const s = factors.slice(0, -1).filter((f) => f !== -1n && f !== 0n && f !== 1n);
  const lastFactor = factors.at(-1);
  if (lastFactor !== undefined && isprime(lastFactor)) s.push(lastFactor);
  return s;
}

// ---------------------------------------------------------------------------
// divisors
// ---------------------------------------------------------------------------

function* divisorsGen(n: bigint, proper: boolean): Generator<bigint, void, undefined> {
  if (n <= 1n) {
    if (!proper && n !== 0n) yield 1n;
    return;
  }
  const fd = factorintInt(n, {});
  const ps = sortedKeys(fd);
  function* rec(i: number): Generator<bigint, void, undefined> {
    if (i === ps.length) {
      yield 1n;
      return;
    }
    const pows = [1n];
    const p = at(ps, i);
    const e = getOrThrow(fd, p);
    for (let k = 0n; k < e; k++) pows.push(last(pows) * p);
    for (const q of rec(i + 1)) for (const p of pows) yield p * q;
  }
  for (const d of rec(0)) if (!proper || d !== n) yield d;
}

/**
 * Enumerates positive divisors in ascending order, or in factorization order as an iterator.
 *
 * @param n - Integer whose divisors to enumerate.
 * @param opts - Set `generator` to iterate and `proper` to exclude the number itself.
 * @returns An iterator over the divisors.
 * @see SymPy `sympy.ntheory.factor_.divisors`
 * @example
 * ```ts
 * import { divisors } from '@symjs/symjs';
 *
 * divisors(24); // => [1, 2, 3, 4, 6, 8, 12, 24]
 * [...divisors(120, { generator: true })]; // => [1, 2, 4, 8, 3, 6, 12, 24, 5, 10, 20, 40, 15, 30, 60, 120]
 * ```
 */
export function divisors(n: IntLike, opts: { generator: true; proper?: boolean }): Generator<bigint, void, undefined>;
/**
 * Enumerates positive divisors in ascending order, or in factorization order as an iterator.
 *
 * @param n - Integer whose divisors to enumerate.
 * @param opts - Set `generator` to iterate and `proper` to exclude the number itself.
 * @returns The divisors in ascending order.
 * @see SymPy `sympy.ntheory.factor_.divisors`
 */
export function divisors(n: IntLike, opts?: { generator?: false; proper?: boolean }): bigint[];
export function divisors(nIn: IntLike, opts: { generator?: boolean; proper?: boolean } = {}): bigint[] | Generator<bigint, void, undefined> {
  const rv = divisorsGen(babs(asInt(nIn)), opts.proper ?? false);
  return opts.generator === true ? rv : [...rv].sort(cmpBig);
}

/**
 * The divisors of n other than n.
 *
 * @param n - Integer whose divisors to examine.
 * @param opts - Set `generator` to iterate over the results.
 * @returns An iterator over the proper divisors.
 * @see SymPy `sympy.ntheory.factor_.proper_divisors`
 * @example
 * ```ts
 * import { properDivisors } from '@symjs/symjs';
 *
 * properDivisors(24); // => [1, 2, 3, 4, 6, 8, 12]
 * [...properDivisors(120, { generator: true })]; // => [1, 2, 4, 8, 3, 6, 12, 24, 5, 10, 20, 40, 15, 30, 60]
 * ```
 */
export function properDivisors(n: IntLike, opts: { generator: true }): Generator<bigint, void, undefined>;
/**
 * The divisors of n other than n.
 *
 * @param n - Integer whose divisors to examine.
 * @param opts - Set `generator` to iterate over the results.
 * @returns The proper divisors in ascending order.
 * @see SymPy `sympy.ntheory.factor_.proper_divisors`
 */
export function properDivisors(n: IntLike, opts?: { generator?: false }): bigint[];
export function properDivisors(n: IntLike, opts: { generator?: boolean } = {}): bigint[] | Generator<bigint, void, undefined> {
  return opts.generator === true ? divisors(n, { generator: true, proper: true }) : divisors(n, { proper: true });
}

/**
 * The number of divisors of n that are multiples of `modulus`; `proper` excludes n.
 *
 * @param nIn - Integer whose divisors to count.
 * @param modulus - Only count multiples of this number.
 * @param opts - Set `proper` to exclude the number itself.
 * @returns The number of qualifying divisors.
 * @see SymPy `sympy.ntheory.factor_.divisor_count`
 * @example
 * ```ts
 * import { divisorCount } from '@symjs/symjs';
 *
 * divisorCount(6); // => 4
 * divisorCount(6, 2); // => 2
 * ```
 */
export function divisorCount(nIn: IntLike, modulus: IntLike = 1, opts: { proper?: boolean } = {}): bigint {
  let n = asInt(nIn);
  const m = asInt(modulus);
  if (m === 0n) return 0n;
  if (m !== 1n) {
    const [q, r] = divmod(n, m);
    if (r !== 0n) return 0n;
    n = q;
  }
  if (n === 0n) return 0n;
  let c = 1n;
  for (const [k, v] of factorintInt(n, {})) if (k > 1n) c *= v + 1n;
  if (c !== 0n && opts.proper === true) c -= 1n;
  return c;
}

/**
 * The number of proper divisors of n that are multiples of `modulus`.
 *
 * @param n - Integer whose proper divisors to count.
 * @param modulus - Only count multiples of this number.
 * @returns The number of qualifying proper divisors.
 * @see SymPy `sympy.ntheory.factor_.proper_divisor_count`
 * @example
 * ```ts
 * import { properDivisorCount } from '@symjs/symjs';
 *
 * properDivisorCount(6); // => 3
 * properDivisorCount(6, 2); // => 1
 * ```
 */
export function properDivisorCount(n: IntLike, modulus: IntLike = 1): bigint {
  return divisorCount(n, modulus, { proper: true });
}

/**
 * The t-th-power-free part of a positive integer.
 *
 * @param nIn - Positive integer to decompose.
 * @param tIn - Degree of the powers to remove.
 * @returns The factor left after removing all complete powers of the given degree.
 * @throws RangeError when the integer is not positive or the degree is less than two.
 * @see SymPy `sympy.ntheory.factor_.core`
 * @example
 * ```ts
 * import { core } from '@symjs/symjs';
 *
 * core(24, 2); // => 6
 * core(9424, 3); // => 1178
 * ```
 */
export function core(nIn: IntLike, tIn: IntLike = 2): bigint {
  const n = asInt(nIn), t = asInt(tIn);
  if (n <= 0n || t < 2n) throw new RangeError('core requires n > 0 and t >= 2');
  let result = 1n;
  for (const [p, e] of factorintInt(n, {})) result *= p ** (e % t);
  return result;
}

function* unitaryDivisors(n: bigint): Generator<bigint, void, undefined> {
  if (n === 0n) return;
  let values = [1n];
  for (const [p, e] of factorintInt(n, {})) values = [...values, ...values.map((d) => d * p ** e)];
  yield* values;
}

/**
 * Enumerates divisors that are coprime to their complementary divisors.
 *
 * @param n - Integer whose divisors to examine.
 * @param opts - Set `generator` to iterate over the results.
 * @returns An iterator over the unitary divisors.
 * @see SymPy `sympy.ntheory.factor_.udivisors`
 * @example
 * ```ts
 * import { udivisors } from '@symjs/symjs';
 *
 * udivisors(15); // => [1, 3, 5, 15]
 * ```
 */
export function udivisors(n: IntLike, opts: { generator: true }): Generator<bigint, void, undefined>;
/**
 * Enumerates divisors that are coprime to their complementary divisors.
 *
 * @param n - Integer whose divisors to examine.
 * @param opts - Set `generator` to iterate over the results.
 * @returns The unitary divisors in ascending order.
 * @see SymPy `sympy.ntheory.factor_.udivisors`
 */
export function udivisors(n: IntLike, opts?: { generator?: false }): bigint[];
export function udivisors(n: IntLike, opts: { generator?: boolean } = {}): bigint[] | Generator<bigint, void, undefined> {
  const result = unitaryDivisors(babs(asInt(n)));
  return opts.generator === true ? result : [...result].sort(cmpBig);
}

/**
 * Counts divisors that are coprime to their complementary divisors.
 *
 * @param nIn - Integer whose unitary divisors to count.
 * @returns The number of unitary divisors.
 * @see SymPy `sympy.ntheory.factor_.udivisor_count`
 * @example
 * ```ts
 * import { udivisorCount } from '@symjs/symjs';
 *
 * udivisorCount(120); // => 8
 * ```
 */
export function udivisorCount(nIn: IntLike): bigint {
  const n = babs(asInt(nIn));
  return n === 0n ? 0n : 2n ** BigInt(factorintInt(n, {}).size);
}

function* antidivisorsGen(n: bigint): Generator<bigint, void, undefined> {
  if (n <= 2n) return;
  for (const d of divisorsGen(n, false)) {
    const y = 2n * d;
    if (y < n && n % y !== 0n) yield y;
  }
  for (const m of [2n * n - 1n, 2n * n + 1n]) {
    for (const d of divisorsGen(m, false)) if (d >= 2n && d < n) yield d;
  }
}

/**
 * Enumerates the integers that miss dividing the given number by the largest possible margin.
 *
 * @param n - Integer whose divisors to examine.
 * @param opts - Set `generator` to iterate over the results.
 * @returns An iterator over the antidivisors.
 * @see SymPy `sympy.ntheory.factor_.antidivisors`
 * @example
 * ```ts
 * import { antidivisors } from '@symjs/symjs';
 *
 * antidivisors(24); // => [7, 16]
 * ```
 */
export function antidivisors(n: IntLike, opts: { generator: true }): Generator<bigint, void, undefined>;
/**
 * Enumerates the integers that miss dividing the given number by the largest possible margin.
 *
 * @param n - Integer whose divisors to examine.
 * @param opts - Set `generator` to iterate over the results.
 * @returns The antidivisors in ascending order.
 * @see SymPy `sympy.ntheory.factor_.antidivisors`
 */
export function antidivisors(n: IntLike, opts?: { generator?: false }): bigint[];
export function antidivisors(n: IntLike, opts: { generator?: boolean } = {}): bigint[] | Generator<bigint, void, undefined> {
  const result = antidivisorsGen(babs(asInt(n)));
  return opts.generator === true ? result : [...result].sort(cmpBig);
}

/**
 * Counts the antidivisors of an integer.
 *
 * @param nIn - Integer whose antidivisors to count.
 * @returns The number of antidivisors.
 * @see SymPy `sympy.ntheory.factor_.antidivisor_count`
 * @example
 * ```ts
 * import { antidivisorCount } from '@symjs/symjs';
 *
 * antidivisorCount(13); // => 4
 * antidivisorCount(27); // => 5
 * ```
 */
export function antidivisorCount(nIn: IntLike): bigint {
  const n = babs(asInt(nIn));
  return n <= 2n ? 0n : divisorCount(2n * n - 1n) + divisorCount(2n * n + 1n) + divisorCount(n) - divisorCount(n, 2) - 5n;
}

/** @internal sigma(n), the sum of the divisors of an integer (SymPy _divisor_sigma with k = 1). */
export function divisorSigmaInt(n: bigint): bigint {
  let r = 1n;
  for (const [p, e] of factorintInt(n, {})) r *= fdiv(p ** (e + 1n) - 1n, p - 1n);
  return r;
}

/**
 * Finds the largest prime and largest prime power dividing an integer.
 *
 * @remarks SymPy prints the two bounds as tuples, `(3, 128)` and `(13, 16)`.
 * @param nIn - Integer to factor.
 * @returns The largest prime factor and largest prime-power factor.
 * @see SymPy `sympy.ntheory.factor_.smoothness`
 * @example
 * ```ts
 * import { smoothness } from '@symjs/symjs';
 *
 * smoothness(1152); // => [3, 128]
 * smoothness(208); // => [13, 16]
 * ```
 */
export function smoothness(nIn: IntLike): [bigint, bigint] {
  const n = asInt(nIn);
  if (n === 1n) return [1n, 1n];
  const facs = factorintInt(n, {});
  let a = 0n;
  let b = 0n;
  for (const [p, e] of facs) {
    if (p > a) a = p;
    if (p ** e > b) b = p ** e;
  }
  return [a, b];
}

type SmoothnessResult = [bigint, [bigint, [bigint, bigint, bigint]][]];
type SmoothnessInput = IntLike | string | ReadonlyMap<bigint | number, bigint | number> | SmoothnessResult;
type SmoothnessOptions = { m?: bigint | number; power?: boolean; visual?: boolean };
/**
 * Computes the smoothness and power smoothness of each shifted prime factor.
 *
 * @remarks SymPy prints the example as `(-1, [(3, (2, 2, 2)), (19, (1, 3, 9)), (61, (1, 5, 5))])`.
 * @param n - Integer, factorization or smoothness description.
 * @param opts - Set `m` for the shift, `power` to sort by prime-power smoothness and `visual` to
 *   select text output.
 * @returns Smoothness data for the shifted prime factors in the requested format.
 * @throws RangeError when the text is not a smoothness description.
 * @see SymPy `sympy.ntheory.factor_.smoothness_p`
 * @example
 * ```ts
 * import { smoothnessP } from '@symjs/symjs';
 *
 * smoothnessP(10431); // => [-1, [[3, [2, 2, 2]], [19, [1, 3, 9]], [61, [1, 5, 5]]]]
 * ```
 */
export function smoothnessP(n: SmoothnessInput, opts: SmoothnessOptions & { visual: false }): SmoothnessResult;
/**
 * Computes the smoothness and power smoothness of each shifted prime factor.
 *
 * @remarks SymPy prints the example as `(-1, [(3, (2, 2, 2)), (19, (1, 3, 9)), (61, (1, 5, 5))])`.
 * @param n - Integer, factorization or smoothness description.
 * @param opts - Set `m` for the shift, `power` to sort by prime-power smoothness and `visual` to
 *   select text output.
 * @returns Smoothness data for the shifted prime factors in the requested format.
 * @throws RangeError when the text is not a smoothness description.
 * @see SymPy `sympy.ntheory.factor_.smoothness_p`
 */
export function smoothnessP(n: SmoothnessInput, opts: SmoothnessOptions & { visual: true }): string;
/**
 * Computes the smoothness and power smoothness of each shifted prime factor.
 *
 * @remarks SymPy prints the example as `(-1, [(3, (2, 2, 2)), (19, (1, 3, 9)), (61, (1, 5, 5))])`.
 * @param n - Integer, factorization or smoothness description.
 * @param opts - Set `m` for the shift, `power` to sort by prime-power smoothness and `visual` to
 *   select text output.
 * @returns Smoothness data for the shifted prime factors in the requested format.
 * @throws RangeError when the text is not a smoothness description.
 * @see SymPy `sympy.ntheory.factor_.smoothness_p`
 */
export function smoothnessP(n: ReadonlyMap<bigint | number, bigint | number> | SmoothnessResult, opts?: SmoothnessOptions & { visual?: undefined }): string;
/**
 * Computes the smoothness and power smoothness of each shifted prime factor.
 *
 * @remarks SymPy prints the example as `(-1, [(3, (2, 2, 2)), (19, (1, 3, 9)), (61, (1, 5, 5))])`.
 * @param n - Integer, factorization or smoothness description.
 * @param opts - Set `m` for the shift, `power` to sort by prime-power smoothness and `visual` to
 *   select text output.
 * @returns Smoothness data for the shifted prime factors in the requested format.
 * @throws RangeError when the text is not a smoothness description.
 * @see SymPy `sympy.ntheory.factor_.smoothness_p`
 */
export function smoothnessP(n: string, opts?: SmoothnessOptions & { visual?: undefined }): Map<bigint, bigint>;
/**
 * Computes the smoothness and power smoothness of each shifted prime factor.
 *
 * @remarks SymPy prints the example as `(-1, [(3, (2, 2, 2)), (19, (1, 3, 9)), (61, (1, 5, 5))])`.
 * @param n - Integer, factorization or smoothness description.
 * @param opts - Set `m` for the shift, `power` to sort by prime-power smoothness and `visual` to
 *   select text output.
 * @returns Smoothness data for the shifted prime factors in the requested format.
 * @throws RangeError when the text is not a smoothness description.
 * @see SymPy `sympy.ntheory.factor_.smoothness_p`
 */
export function smoothnessP(n: IntLike, opts?: SmoothnessOptions & { visual?: false }): SmoothnessResult;
/**
 * Computes the smoothness and power smoothness of each shifted prime factor.
 *
 * @remarks SymPy prints the example as `(-1, [(3, (2, 2, 2)), (19, (1, 3, 9)), (61, (1, 5, 5))])`.
 * @param n - Integer, factorization or smoothness description.
 * @param opts - Set `m` for the shift, `power` to sort by prime-power smoothness and `visual` to
 *   select text output.
 * @returns Smoothness data for the shifted prime factors in the requested format.
 * @throws RangeError when the text is not a smoothness description.
 * @see SymPy `sympy.ntheory.factor_.smoothness_p`
 */
export function smoothnessP(n: SmoothnessInput, opts: SmoothnessOptions): SmoothnessResult | string | Map<bigint, bigint>;
export function smoothnessP(nIn: SmoothnessInput, opts: SmoothnessOptions = {}): SmoothnessResult | string | Map<bigint, bigint> {
  const m = BigInt(opts.m ?? -1);
  const k = opts.power === true ? 2 : 1;
  let input = nIn;
  if (typeof input === 'string') {
    if (opts.visual === true) return input;
    const factors = new Map<bigint, bigint>();
    for (const line of input.split('\n')) {
      const match = /^p\*\*i=(-?\d+)\*\*(-?\d+) has /.exec(line);
      if (match === null) throw new RangeError('invalid smoothness description');
      factors.set(BigInt(at(match, 1)), BigInt(at(match, 2)));
    }
    if (opts.visual === undefined) return factors;
    input = factors;
  }
  const isTuple = (v: Exclude<SmoothnessInput, string>): v is SmoothnessResult => Array.isArray(v);
  let result: SmoothnessResult;
  if (isTuple(input)) result = input;
  else {
    const facs = isFactorMap(input) ? factorint(input, { visual: false }) : factorint(input, { visual: false });
    const rows: SmoothnessResult[1] = [...facs].map(([f, M]) => {
      const [a, b] = smoothness(f + m);
      return [f, [M, a, b]];
    });
    rows.sort((x, y) => cmpBig(x[1][k], y[1][k]) || cmpBig(x[0], y[0]));
    result = [m, rows];
  }
  if (opts.visual === false || opts.visual === undefined && !(nIn instanceof Map) && !isTuple(input)) return result;
  const rows = result[1];
  return rows.map(([p, [i, B, Bp]]) => `p**i=${p}**${i} has p${m < 0n ? '' : '+'}${m} B=${B}, B-pow=${Bp}`).join('\n');
}

// ---------------------------------------------------------------------------
// perfect, abundant, deficient, amicable numbers; digital roots
// ---------------------------------------------------------------------------

/**
 * The nth Mersenne prime exponent.
 *
 * @param nth - One-based index among known Mersenne primes.
 * @returns The exponent of the indexed Mersenne prime.
 * @throws RangeError when the index is outside the supported table.
 * @see SymPy `sympy.ntheory.factor_.mersenne_prime_exponent`
 * @example
 * ```ts
 * import { mersennePrimeExponent } from '@symjs/symjs';
 *
 * mersennePrimeExponent(1); // => 2
 * mersennePrimeExponent(20); // => 4423
 * ```
 */
export function mersennePrimeExponent(nth: IntLike): bigint {
  const n = asInt(nth);
  if (n < 1n) throw new RangeError('nth must be a positive integer; mersenne_prime_exponent(1) == 2');
  if (n > 51n) throw new RangeError('There are only 51 perfect numbers; nth must be less than or equal to 51');
  return BigInt(at(MERSENNE_PRIME_EXPONENTS, Number(n) - 1));
}

/**
 * Computes the excess of the sum of proper divisors over the integer.
 *
 * @param nIn - Integer whose divisors to sum.
 * @returns The sum of the proper divisors minus the number itself.
 * @see SymPy `sympy.ntheory.factor_.abundance`
 * @example
 * ```ts
 * import { abundance } from '@symjs/symjs';
 *
 * abundance(6); // => 0
 * abundance(10); // => -2
 * ```
 */
export function abundance(nIn: IntLike): bigint {
  const n = asInt(nIn);
  return divisorSigmaInt(n) - 2n * n;
}

/**
 * Tests whether an integer equals the sum of its proper divisors.
 *
 * @param nIn - Integer to classify.
 * @returns Whether the proper divisors sum to the integer.
 * @see SymPy `sympy.ntheory.factor_.is_perfect`
 * @example
 * ```ts
 * import { isPerfect } from '@symjs/symjs';
 *
 * isPerfect(20); // => False
 * isPerfect(6); // => True
 * ```
 */
export function isPerfect(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (n < 1n) return false;
  if (n % 2n === 0n) {
    const m = BigInt((bitLength(n) + 1) >> 1);
    if ((1n << (m - 1n)) * ((1n << m) - 1n) !== n) return false;
    return MERSENNE_PRIME_EXPONENTS.includes(Number(m)) || isMersennePrime(2n ** m - 1n);
  }
  if (n < 10n ** 2000n) return false;
  if (n % 105n === 0n) return false;
  const conds: [bigint, bigint][] = [
    [12n, 1n],
    [468n, 117n],
    [324n, 81n],
  ];
  if (conds.every(([m, r]) => n % m !== r)) return false;
  // SymPy raises ValueError on an odd perfect number (none is known, and the
  // conditions above make one impossible to meet in practice); it is perfect,
  // so the answer is true
  return abundance(n) === 0n;
}

/**
 * Tests whether the sum of the proper divisors exceeds the integer.
 *
 * @param nIn - Integer to classify.
 * @returns Whether the proper divisors sum to more than the integer.
 * @see SymPy `sympy.ntheory.factor_.is_abundant`
 * @example
 * ```ts
 * import { isAbundant } from '@symjs/symjs';
 *
 * isAbundant(20); // => True
 * isAbundant(15); // => False
 * ```
 */
export function isAbundant(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (isPerfect(n)) return false;
  return n % 6n === 0n || abundance(n) > 0n;
}

/**
 * Tests whether the sum of the proper divisors falls short of the integer.
 *
 * @param nIn - Integer to classify.
 * @returns Whether the proper divisors sum to less than the integer.
 * @see SymPy `sympy.ntheory.factor_.is_deficient`
 * @example
 * ```ts
 * import { isDeficient } from '@symjs/symjs';
 *
 * isDeficient(20); // => False
 * isDeficient(15); // => True
 * ```
 */
export function isDeficient(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (isPerfect(n)) return false;
  return abundance(n) < 0n;
}

/**
 * Tests whether two numbers form an amicable pair.
 *
 * @param mIn - First integer of the pair.
 * @param nIn - Second integer of the pair.
 * @returns Whether each integer is the sum of the other’s proper divisors.
 * @see SymPy `sympy.ntheory.factor_.is_amicable`
 * @example
 * ```ts
 * import { isAmicable } from '@symjs/symjs';
 *
 * isAmicable(220, 284); // => True
 * ```
 */
export function isAmicable(mIn: IntLike, nIn: IntLike): boolean {
  const m = asInt(mIn);
  const n = asInt(nIn);
  if (m === n) return false;
  const sm = divisorSigmaInt(m);
  return m + n === sm && sm === divisorSigmaInt(n);
}

/**
 * The digital root of n in base b.
 *
 * @param nIn - Integer whose digits to reduce.
 * @param bIn - Radix in which to take the digits.
 * @returns The final single digit in the specified base.
 * @throws RangeError when the radix is less than two.
 * @see SymPy `sympy.ntheory.factor_.dra`
 * @example
 * ```ts
 * import { dra } from '@symjs/symjs';
 *
 * dra(3110, 12); // => 8
 * ```
 */
export function dra(nIn: IntLike, bIn: IntLike): bigint {
  const num = babs(asInt(nIn));
  const b = asInt(bIn);
  if (b <= 1n) throw new RangeError('Base should be an integer greater than 1');
  if (num === 0n) return 0n;
  return 1n + ((num - 1n) % (b - 1n));
}

/**
 * The multiplicative digital root of n in base b.
 *
 * @param nIn - Integer whose digits to reduce.
 * @param bIn - Radix in which to take the digits.
 * @returns The final single digit in the specified base.
 * @throws RangeError when the radix is less than two.
 * @see SymPy `sympy.ntheory.factor_.drm`
 * @example
 * ```ts
 * import { drm } from '@symjs/symjs';
 *
 * drm(9876, 10); // => 0
 * drm(49, 10); // => 8
 * ```
 */
export function drm(nIn: IntLike, bIn: IntLike): bigint {
  let n = babs(asInt(nIn));
  const b = asInt(bIn);
  if (b <= 1n) throw new RangeError('Base should be an integer greater than 1');
  while (n > b) {
    let m = 1n;
    while (n > 1n) {
      const r = n % b;
      n /= b;
      if (r === 0n) return 0n;
      m *= r;
    }
    n = m;
  }
  return n;
}
