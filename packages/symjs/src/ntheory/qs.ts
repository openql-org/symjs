// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The self-initializing quadratic sieve (SymPy sympy.ntheory.qs: qs
 * and qs_factor) with SymPy's seeded polynomial choice.
 */

import { at, defined, first, last } from '../core/guard';
import { gcd } from '../core/numbers';
import { perfectPowerInt } from './factor';
import type { IntLike } from './intutil';
import { asInt, bitScan1, invert, isqrt, pmod, powmod, pyLog, pyRound } from './intutil';
import { isprime } from './primetest';
import type { RandInt } from './random';
import { randintFrom } from './random';
import { sqrtModPrimePower } from './residue';
import { sieve } from './sieve';

interface FactorBaseElem {
  prime: bigint;
  p: number;
  tmemP: bigint;
  logP: number;
  soln1: number | undefined;
  soln2: number;
  bAinv: number[];
}

class SievePolynomial {
  readonly a2: bigint;
  readonly ab: bigint;
  readonly b2: bigint;
  constructor(
    readonly a: bigint,
    readonly b: bigint,
    N: bigint,
  ) {
    this.a2 = a * a;
    this.ab = 2n * a * b;
    this.b2 = b * b - N;
  }
  evalU(x: bigint): bigint {
    return this.a * x + this.b;
  }
  evalV(x: bigint): bigint {
    return (this.a2 * x + this.ab) * x + this.b2;
  }
}

function generateFactorBase(primeBound: bigint, n: bigint): [number | undefined, number | undefined, FactorBaseElem[]] {
  const fb: FactorBaseElem[] = [];
  let idx1000: number | undefined;
  let idx5000: number | undefined;
  for (const prime of sieve.primerange(1n, primeBound)) {
    if (powmod(n, (prime - 1n) / 2n, prime) === 1n) {
      if (prime > 1000n && idx1000 === undefined) idx1000 = fb.length - 1;
      if (prime > 5000n && idx5000 === undefined) idx5000 = fb.length - 1;
      const residue = first(defined(sqrtModPrimePower(n, prime, 1n), 'square root of n modulo a factor base prime'));
      const logP = pyRound(Math.log(Number(prime)) * 2 ** 10);
      fb.push({ prime, p: Number(prime), tmemP: residue, logP, soln1: undefined, soln2: 0, bAinv: [] });
    }
  }
  return [idx1000, idx5000, fb];
}

function* generatePolynomial(N: bigint, M: number, fb: FactorBaseElem[], idx1000: number | undefined, idx5000: number | undefined, randint: RandInt): Generator<SievePolynomial, void, undefined> {
  const approxVal = pyLog(2n * N) / 2 - Math.log(M);
  const start = idx1000 ?? 0;
  const end = idx5000 === undefined || idx5000 === 0 ? fb.length - 1 : idx5000;
  for (;;) {
    let bestA = 0n;
    let bestQ: number[] = [];
    let bestRatio: number | undefined;
    for (let it = 0; it < 50; it++) {
      let a = 1n;
      const q: number[] = [];
      while (pyLog(a) < approxVal) {
        let randP = 0;
        while (randP === 0 || q.includes(randP)) randP = Number(randint(BigInt(start), BigInt(end)));
        a *= at(fb, randP).prime;
        q.push(randP);
      }
      const ratio = Math.exp(pyLog(a) - approxVal);
      if (bestRatio === undefined || Math.abs(ratio - 1) < Math.abs(bestRatio - 1)) {
        bestQ = q;
        bestA = a;
        bestRatio = ratio;
      }
    }
    const a = bestA;
    const B: bigint[] = [];
    for (const val of bestQ) {
      const ql = at(fb, val).prime;
      let gamma = pmod(at(fb, val).tmemP * invert(a / ql, ql), ql);
      if (2n * gamma > ql) gamma = ql - gamma;
      B.push((a / ql) * gamma);
    }
    const b = B.reduce((x, y) => x + y, 0n);
    let g = new SievePolynomial(a, b, N);
    for (const f of fb) {
      if (a % f.prime === 0n) {
        f.soln1 = undefined;
        continue;
      }
      const aInv = invert(a, f.prime);
      f.bAinv = B.map((be) => Number(pmod(2n * be * aInv, f.prime)));
      f.soln1 = Number(pmod(aInv * (f.tmemP - b), f.prime));
      f.soln2 = Number(pmod(aInv * (-f.tmemP - b), f.prime));
    }
    yield g;
    for (let i = 1; i < 2 ** (B.length - 1); i++) {
      const v = bitScan1(BigInt(i));
      const negPow = 2 * ((i >> (v + 1)) % 2) - 1;
      const nb = g.b + 2n * BigInt(negPow) * at(B, v);
      g = new SievePolynomial(g.a, nb, N);
      for (const f of fb) {
        if (f.soln1 === undefined) continue;
        f.soln1 = (((f.soln1 - negPow * at(f.bAinv, v)) % f.p) + f.p) % f.p;
        f.soln2 = (((f.soln2 - negPow * at(f.bAinv, v)) % f.p) + f.p) % f.p;
      }
      yield g;
    }
  }
}

function genSieveArray(M: number, fb: readonly FactorBaseElem[]): Float64Array {
  const arr = new Float64Array(2 * M + 1);
  for (const f of fb) {
    if (f.soln1 === undefined) continue;
    // idx < 2M < arr.length, so the elements exist (`?? 0` only satisfies the index type)
    for (let idx = (M + f.soln1) % f.p; idx < 2 * M; idx += f.p) arr[idx] = (arr[idx] ?? 0) + f.logP;
    if (f.p === 2) continue;
    for (let idx = (M + f.soln2) % f.p; idx < 2 * M; idx += f.p) arr[idx] = (arr[idx] ?? 0) + f.logP;
  }
  return arr;
}

function checkSmoothness(numIn: bigint, fb: readonly FactorBaseElem[]): [bigint, bigint] {
  let num = numIn;
  let vec = 0n;
  if (num < 0n) {
    num = -num;
    vec = 1n;
  }
  fb.forEach((f, i0) => {
    if (num % f.prime !== 0n) return;
    let e = 1;
    num /= f.prime;
    while (num % f.prime === 0n) {
      e++;
      num /= f.prime;
    }
    if (e % 2) vec += 1n << BigInt(i0 + 1);
  });
  return [vec, num];
}

type Relation = [bigint, bigint, bigint];

function trialDivisionStage(N: bigint, M: number, fb: readonly FactorBaseElem[], sieveArray: Float64Array, poly: SievePolynomial, partial: Map<bigint, Relation>, errorTerm: number): [Relation[], bigint[]] {
  const accumulated = (Math.log(M) + pyLog(N) / 2 - errorTerm) * 2 ** 10;
  const smooth: Relation[] = [];
  const proper: bigint[] = [];
  const upper = 128n * last(fb).prime;
  for (const [k, s] of sieveArray.entries()) {
    if (s < accumulated) continue;
    const x = BigInt(k - M);
    let v = poly.evalV(x);
    let [vec, num] = checkSmoothness(v, fb);
    if (num === 1n) smooth.push([poly.evalU(x), v, vec]);
    else if (num < upper && isprime(num)) {
      if (N % num === 0n) {
        if (!proper.includes(num)) proper.push(num);
        continue;
      }
      let u = poly.evalU(x);
      const prev = partial.get(num);
      if (prev !== undefined) {
        partial.delete(num);
        const [uPrev, vPrev, vecPrev] = prev;
        u = pmod(u * uPrev * invert(num, N), N);
        v = (v * vPrev) / (num * num);
        vec ^= vecPrev;
        smooth.push([u, v, vec]);
      } else partial.set(num, [u, v, vec]);
    }
  }
  return [smooth, proper];
}

function* findFactor(N: bigint, smooth: readonly Relation[], col: number): Generator<bigint, void, undefined> {
  const matrix = smooth.map((r) => r[2]);
  const row = matrix.length;
  const mark = new Array<boolean>(row).fill(false);
  for (let pos = 0; pos < col; pos++) {
    const m = 1n << BigInt(pos);
    for (let i = 0; i < row; i++) {
      const p = at(matrix, i) & m;
      if (p) {
        const addCol = p ^ at(matrix, i);
        matrix[i] = m;
        mark[i] = true;
        for (let j = i + 1; j < row; j++) if (at(matrix, j) & m) matrix[j] = at(matrix, j) ^ addCol;
        break;
      }
    }
  }
  for (let i = 0; i < row; i++) {
    if (mark[i]) continue;
    let u = at(smooth, i)[0];
    let v = at(smooth, i)[1];
    for (let j = 0; j < row; j++) {
      if (mark[j] && at(matrix, i) & at(matrix, j)) {
        u *= at(smooth, j)[0];
        v *= at(smooth, j)[1];
      }
    }
    v = isqrt(v);
    const g = gcd(u - v, N);
    if (1n < g && g < N) yield g;
  }
}

/** Options of qs and qsFactor. */
export interface QsOptions {
  /** The error term of the sieve threshold (default 25). */
  ERROR_TERM?: number;
  /** The seed of the polynomial choice (default 1234). */
  seed?: bigint | number;
}

/**
 * The factorization of N found by the self-initializing quadratic sieve
 * with the given prime bound and sieve interval [-M, M], as a Map factor
 * -> exponent (SymPy qs_factor); factors may be composite.
 */
export function qsFactor(NIn: IntLike, primeBoundIn: IntLike, MIn: IntLike, opts: QsOptions = {}): Map<bigint, bigint> {
  let N = asInt(NIn);
  const primeBound = asInt(primeBoundIn);
  const M = Number(asInt(MIn));
  const errorTerm = opts.ERROR_TERM ?? 25;
  if (N < 2n) throw new RangeError('N should be greater than 1');
  const factors = new Map<bigint, bigint>();
  const smooth: Relation[] = [];
  const partial = new Map<bigint, Relation>();
  if (N % 2n === 0n) {
    let e = 1n;
    N /= 2n;
    while (N % 2n === 0n) {
      N /= 2n;
      e++;
    }
    factors.set(2n, e);
  }
  if (isprime(N)) {
    factors.set(N, 1n);
    return factors;
  }
  const result = perfectPowerInt(N, 3n);
  if (result !== false) {
    factors.set(result[0], result[1]);
    return factors;
  }
  let Ncopy = N;
  const randint = randintFrom(opts.seed ?? 1234);
  const [idx1000, idx5000, fb] = generateFactorBase(primeBound, N);
  const threshold = Math.floor((fb.length * 105) / 100);
  const takeOut = (p: bigint): void => {
    let e = 1n;
    Ncopy /= p;
    while (Ncopy % p === 0n) {
      Ncopy /= p;
      e++;
    }
    factors.set(p, e);
  };
  for (const g of generatePolynomial(N, M, fb, idx1000, idx5000, randint)) {
    const sieveArray = genSieveArray(M, fb);
    const [sRel, pF] = trialDivisionStage(N, M, fb, sieveArray, g, partial, errorTerm);
    smooth.push(...sRel);
    for (const p of pF) if (Ncopy % p === 0n) takeOut(p);
    if (threshold <= smooth.length) break;
  }
  for (const factor of findFactor(N, smooth, fb.length + 1)) {
    if (Ncopy % factor === 0n) {
      takeOut(factor);
      if (Ncopy === 1n || isprime(Ncopy)) break;
    }
  }
  if (Ncopy !== 1n) factors.set(Ncopy, 1n);
  return factors;
}

/**
 * The set of factors of N found by the quadratic sieve (SymPy qs), filled
 * in increasing order.
 */
export function qs(N: IntLike, primeBound: IntLike, M: IntLike, opts: QsOptions = {}): Set<bigint> {
  return new Set([...qsFactor(N, primeBound, M, opts).keys()].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0)));
}
