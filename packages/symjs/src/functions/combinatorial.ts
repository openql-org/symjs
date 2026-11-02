// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Combinatorial numbers and polynomials and number-theoretic
 * functions (SymPy functions.combinatorial.numbers and ntheory):
 * Bernoulli, Euler, Genocchi, Bell, Fibonacci, Lucas, Tribonacci,
 * partitions, totients, Mobius, divisor sigma, prime counting, Jacobi
 * and Kronecker symbols, and the multivariate gamma function.
 */

import { isIntegerQ, isNegative, isPositive, isReal as isRealQ } from '../core/assumptions';
import { Dummy, Expr, ExprLike, Fn, FnName, Rational, S } from '../core/nodes';
import { Product } from '../concrete/summations';
import { add, mul, pow, sympify } from '../core/ops';
import { factorInt } from '../core/numbers';
import { expandMul } from '../simplify/expand';
import { evaluators, fn } from './elementary';
import { bernoulliNumber, floor as floorFn, gamma } from './special';

const R = (p: bigint | number, q: bigint | number = 1n) => Rational.of(BigInt(p), BigInt(q));
const asInt = (e: Expr): bigint | undefined => (e instanceof Rational && e.isInteger ? e.p : undefined);

function binom(n: number, k: number): bigint {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return r;
}

/** Bernoulli number with SymPy's convention B_1 = +1/2. */
function bernoulliPlus(n: number): Rational {
  return n === 1 ? R(1, 2) : (bernoulliNumber(n) as Rational);
}

/** Bernoulli polynomial B_n(x) = sum C(n,k) B_k x^(n-k) with B_1 = -1/2. */
function bernoulliPoly(n: number, x: Expr): Expr {
  const terms: Expr[] = [];
  for (let k = 0; k <= n; k++) {
    const b = k === 1 ? R(-1, 2) : (bernoulliNumber(k) as Rational);
    if (b.isZero) continue;
    terms.push(mul(R(binom(n, k)), b, pow(x, n - k)));
  }
  return expandMul(add(...terms));
}

const eulerCache: bigint[] = [1n];
/** Euler (secant) numbers E_n. */
function eulerNumber(n: number): bigint {
  if (n % 2 === 1) return 0n;
  while (eulerCache.length <= n) {
    const m = eulerCache.length;
    if (m % 2 === 1) {
      eulerCache.push(0n);
      continue;
    }
    // sum_{k=0}^{m} C(m,k) E_k = 0 for even m > 0 (over even k)
    let s = 0n;
    for (let k = 0; k < m; k += 2) s += binom(m, k) * eulerCache[k]!;
    eulerCache.push(-s);
  }
  return eulerCache[n]!;
}

/** Euler polynomial E_n(x) = sum C(n,k) E_k/2^k (x - 1/2)^(n-k). */
function eulerPoly(n: number, x: Expr): Expr {
  const terms: Expr[] = [];
  for (let k = 0; k <= n; k++) {
    const e = eulerNumber(k);
    if (e === 0n) continue;
    terms.push(mul(R(binom(n, k)), R(e, 2n ** BigInt(k)), pow(add(x, R(-1, 2)), n - k)));
  }
  return expandMul(add(...terms));
}

/** Bell numbers via the Bell triangle. */
function bellNumber(n: number): bigint {
  let row: bigint[] = [1n];
  const bells: bigint[] = [1n];
  for (let i = 1; i <= n; i++) {
    const next = [row[row.length - 1]!];
    for (const v of row) next.push(next[next.length - 1]! + v);
    row = next;
    bells.push(row[0]!);
  }
  return bells[n]!;
}

/** Stirling numbers of the second kind S(n, k). */
function stirling2(n: number, k: number): bigint {
  const t: bigint[][] = [[1n]];
  for (let i = 1; i <= n; i++) {
    t[i] = [0n];
    for (let j = 1; j <= i; j++) t[i]![j] = BigInt(j) * (t[i - 1]![j] ?? 0n) + (t[i - 1]![j - 1] ?? 0n);
  }
  return t[n]![k] ?? 0n;
}

/** Incomplete Bell polynomial B_{n,k}(x_1, ..., x_{n-k+1}). */
function incompleteBell(n: number, k: number, xs: readonly Expr[]): Expr {
  if (n === 0 && k === 0) return S.One;
  if (n === 0 || k === 0) return S.Zero;
  const terms: Expr[] = [];
  for (let m = 1; m <= n - k + 1; m++) {
    terms.push(mul(R(binom(n - 1, m - 1)), xs[m - 1] ?? S.Zero, incompleteBell(n - m, k - 1, xs)));
  }
  return expandMul(add(...terms));
}

function fibPoly(n: number, x: Expr): Expr {
  let [a, b]: [Expr, Expr] = [S.Zero, S.One];
  for (let i = 1; i < n; i++) [a, b] = [b, expandMul(add(mul(x, b), a))];
  return n === 0 ? S.Zero : b;
}

function fibNumber(n: bigint): bigint {
  if (n < 0n) {
    const f = fibNumber(-n);
    return (-n) % 2n === 0n ? -f : f;
  }
  let [a, b] = [0n, 1n];
  for (let i = 0n; i < n; i++) [a, b] = [b, a + b];
  return a;
}

function tribPoly(n: number, x: Expr): Expr {
  const t: Expr[] = [S.Zero, S.One, pow(x, 2)];
  for (let i = 3; i <= n; i++) t[i] = expandMul(add(mul(pow(x, 2), t[i - 1]!), mul(x, t[i - 2]!), t[i - 3]!));
  return t[n]!;
}

function partitionNumber(n: number): bigint {
  const p: bigint[] = [1n];
  for (let i = 1; i <= n; i++) {
    let s = 0n;
    for (let k = 1; ; k++) {
      const g1 = (k * (3 * k - 1)) / 2;
      const g2 = (k * (3 * k + 1)) / 2;
      if (g1 > i) break;
      const sign = k % 2 === 1 ? 1n : -1n;
      s += sign * p[i - g1]!;
      if (g2 <= i) s += sign * p[i - g2]!;
    }
    p.push(s);
  }
  return p[n]!;
}

/** Primality test (deterministic Miller-Rabin for 64-bit, trial division otherwise). */
export function isprime(nIn: ExprLike | bigint): boolean {
  const n = typeof nIn === 'bigint' ? nIn : asInt(sympify(nIn));
  if (n === undefined || n < 2n) return false;
  for (const p of [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]) {
    if (n === p) return true;
    if (n % p === 0n) return false;
  }
  let d = n - 1n;
  let s = 0;
  while (d % 2n === 0n) {
    d /= 2n;
    s++;
  }
  const powmod = (b: bigint, e: bigint, m: bigint) => {
    let r = 1n;
    b %= m;
    while (e > 0n) {
      if (e & 1n) r = (r * b) % m;
      b = (b * b) % m;
      e >>= 1n;
    }
    return r;
  };
  for (const a of [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]) {
    let x = powmod(a, d, n);
    if (x === 1n || x === n - 1n) continue;
    let ok = false;
    for (let r = 1; r < s; r++) {
      x = (x * x) % n;
      if (x === n - 1n) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

/** Jacobi symbol (m/n) for odd positive n. */
export function jacobiSymbol(mIn: bigint, n: bigint): number {
  if (n <= 0n || n % 2n === 0n) throw new RangeError('jacobi_symbol: n must be an odd positive integer');
  let m = ((mIn % n) + n) % n;
  let t = 1;
  while (m !== 0n) {
    while (m % 2n === 0n) {
      m /= 2n;
      const r = n % 8n;
      if (r === 3n || r === 5n) t = -t;
    }
    [m, n] = [n, m];
    if (m % 4n === 3n && n % 4n === 3n) t = -t;
    m %= n;
  }
  return n === 1n ? t : 0;
}

/** Kronecker symbol (a/n). */
export function kroneckerSymbol(a: bigint, n: bigint): number {
  if (n === 0n) return a === 1n || a === -1n ? 1 : 0;
  let t = 1;
  if (n < 0n) {
    n = -n;
    if (a < 0n) t = -t;
  }
  let v = 0;
  while (n % 2n === 0n) {
    n /= 2n;
    v++;
  }
  if (v > 0) {
    if (a % 2n === 0n) return 0;
    const r = ((a % 8n) + 8n) % 8n;
    if (v % 2 === 1 && (r === 3n || r === 5n)) t = -t;
  }
  if (n === 1n) return t;
  return t * jacobiSymbol(a, n);
}

function totient(n: bigint): bigint {
  let r = n;
  for (const p of factorInt(n).keys()) r = (r / p) * (p - 1n);
  return r;
}

function carmichael(n: bigint): bigint {
  const g = (a: bigint, b: bigint): bigint => (b === 0n ? a : g(b, a % b));
  let l = 1n;
  for (const [p, e] of factorInt(n)) {
    let lam = (p - 1n) * p ** (e - 1n);
    if (p === 2n && e >= 3n) lam /= 2n;
    l = (l / g(l, lam)) * lam;
  }
  return l;
}

function primepi(n: bigint): bigint {
  let c = 0n;
  for (let i = 2n; i <= n; i++) if (isprime(i)) c++;
  return c;
}

// ---------------------------------------------------------------------------
// evaluators
// ---------------------------------------------------------------------------

const small = (n: bigint) => n >= 0n && n <= 5000n;

const EVAL: Partial<Record<FnName, (...a: Expr[]) => Expr | undefined>> = {
  bernoulli: (n, x) => {
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return small(k) ? bernoulliPoly(Number(k), x) : undefined;
    if (k > 1n && k % 2n === 1n) return S.Zero;
    return small(k) ? bernoulliPlus(Number(k)) : undefined;
  },
  euler: (n, x) => {
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return small(k) ? eulerPoly(Number(k), x) : undefined;
    return small(k) ? R(eulerNumber(Number(k))) : undefined;
  },
  genocchi: (n, x) => {
    const k = asInt(n);
    if (k === undefined) {
      // genocchi(n) = 0 for odd n > 1
      if (x === undefined && isIntegerQ(mul(add(n, -1), R(1, 2))) === true && isPositive(add(n, -1)) === true) return S.Zero;
      return undefined;
    }
    if (k < 0n) return undefined;
    const kk = Number(k);
    if (x !== undefined) {
      const half = mul(R(1, 2), add(x, 1));
      return expandMul(mul(2, add(bernoulliPoly(kk, x), mul(-1, R(2n ** k), bernoulliPoly(kk, half)))));
    }
    return mul(2, add(1, mul(-1, R(2n ** k))), bernoulliPlus(kk));
  },
  bell: (n, a, ...rest) => {
    const b = rest.length ? rest[0] : undefined;
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (a === undefined) return R(bellNumber(Number(k)));
    if (b === undefined) {
      const terms: Expr[] = [];
      for (let j = 0; j <= Number(k); j++) terms.push(mul(R(stirling2(Number(k), j)), pow(a, j)));
      return add(...terms);
    }
    const kk = asInt(a);
    if (kk === undefined) return undefined;
    return incompleteBell(Number(k), Number(kk), rest);
  },
  fibonacci: (n, x) => {
    const k = asInt(n);
    if (k === undefined) return undefined;
    if (x !== undefined) return k >= 0n ? fibPoly(Number(k), x) : undefined;
    return R(fibNumber(k));
  },
  lucas: (n) => {
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    return R(fibNumber(k + 1n) + fibNumber(k - 1n));
  },
  tribonacci: (n, x) => {
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return tribPoly(Number(k), x);
    const t = [0n, 1n, 1n];
    for (let i = 3; i <= Number(k); i++) t[i] = t[i - 1]! + t[i - 2]! + t[i - 3]!;
    return R(t[Number(k)]!);
  },
  partition: (n) => {
    const k = asInt(n);
    if (k === undefined) return isIntegerQ(n) === true && isNegative(n) === true ? S.Zero : undefined;
    if (k < 0n) return S.Zero;
    return R(partitionNumber(Number(k)));
  },
  totient: (n) => {
    const k = asInt(n);
    return k !== undefined && k > 0n ? R(totient(k)) : undefined;
  },
  reduced_totient: (n) => {
    const k = asInt(n);
    return k !== undefined && k > 0n ? R(carmichael(k)) : undefined;
  },
  mobius: (n) => {
    const k = asInt(n);
    if (k === undefined) {
      // a square factor makes mobius vanish (mobius(4*n) = mobius(n**2) = 0) for positive integers
      if (isIntegerQ(n) !== true) return undefined;
      const fs = n.kind === 'Mul' ? n.args : [n];
      for (const f of fs) {
        if (f instanceof Rational && f.isInteger && [...factorInt(f.p < 0n ? -f.p : f.p).values()].some((e) => e > 1n)) return S.Zero;
        if (f.kind === 'Pow' && f.args[1] instanceof Rational && (f.args[1] as Rational).isInteger && (f.args[1] as Rational).p > 1n) return S.Zero;
      }
      return undefined;
    }
    if (k <= 0n) return undefined;
    let r = 1n;
    for (const e of factorInt(k).values()) {
      if (e > 1n) return S.Zero;
      r = -r;
    }
    return R(r);
  },
  divisor_sigma: (n, kIn) => {
    const m = asInt(n);
    const k = kIn === undefined ? 1n : asInt(kIn);
    if (m === undefined || k === undefined || m <= 0n) return undefined;
    let r = 1n;
    for (const [p, e] of factorInt(m)) {
      if (k === 0n) r *= e + 1n;
      else {
        let s = 0n;
        for (let i = 0n; i <= e; i++) s += p ** (k * i);
        r *= s;
      }
    }
    return R(r);
  },
  primenu: (n) => {
    const k = asInt(n);
    return k !== undefined && k > 0n ? R(k === 1n ? 0 : factorInt(k).size) : undefined;
  },
  primeomega: (n) => {
    const k = asInt(n);
    if (k === undefined || k <= 0n) return undefined;
    let c = 0n;
    if (k > 1n) for (const e of factorInt(k).values()) c += e;
    return R(c);
  },
  primepi: (n) => {
    const k = asInt(n);
    return k !== undefined ? R(k < 2n ? 0n : primepi(k)) : undefined;
  },
  multigamma: (x, p) => {
    const k = asInt(p);
    if (k === undefined && isIntegerQ(p) === true && isPositive(p) === true) {
      // pi**(p*(p - 1)/4)*Product(gamma(x + (1 - k)/2), (k, 1, p)) like SymPy
      const d = new Dummy('k');
      return mul(pow(S.Pi, mul(p, add(p, -1), R(1, 4))), Product(gamma(add(x, mul(add(1, mul(-1, d)), R(1, 2)))), [d, 1, p]));
    }
    if (k === undefined || k < 1n) return undefined;
    const kk = Number(k);
    const factors: Expr[] = [pow(S.Pi, R(kk * (kk - 1), 4))];
    for (let j = 1; j <= kk; j++) factors.push(gamma(add(x, R(1 - j, 2))));
    return mul(...factors);
  },
};

/** SymPy frac: fractional part, split into real and imaginary parts. */
function evalFrac(x: Expr): Expr | undefined {
  const one = (a: Expr): Expr => {
    if (a instanceof Rational && a.isZero) return S.Zero;
    if (isIntegerQ(a) === true) return S.Zero;
    if (a instanceof Rational) return add(a, mul(-1, floorFn(a)));
    if (a.freeSymbols().size === 0 && !(a.kind === 'Special')) return add(a, mul(-1, floorFn(a)));
    return new Fn('frac', [a]);
  };
  let real: Expr = S.Zero;
  let imag: Expr = S.Zero;
  for (const t of x.kind === 'Add' ? x.args : [x]) {
    if (isRealQ(mul(S.I, t)) === true && !(t instanceof Rational && t.isZero)) {
      const i = mul(-1, S.I, t);
      if (!i.has(S.I)) imag = add(imag, i);
      else real = add(real, t);
    } else real = add(real, t);
  }
  const r = one(real);
  const i = one(imag);
  const out = add(r, mul(S.I, i));
  if (out instanceof Fn && out.name === 'frac' && out.args[0]!.key === x.key) return undefined;
  return out;
}
EVAL.frac = evalFrac;

for (const [name, f] of Object.entries(EVAL) as [FnName, (...a: Expr[]) => Expr | undefined][]) {
  evaluators[name] = (...a: Expr[]) => f(...a);
}

export const bernoulli = (n: ExprLike, x?: ExprLike): Expr => fn('bernoulli', x === undefined ? [n] : [n, x]);
export const euler = (n: ExprLike, x?: ExprLike): Expr => fn('euler', x === undefined ? [n] : [n, x]);
export const genocchi = (n: ExprLike, x?: ExprLike): Expr => fn('genocchi', x === undefined ? [n] : [n, x]);
export const bell = (n: ExprLike, a?: ExprLike, xs?: readonly ExprLike[]): Expr => fn('bell', [n, ...(a === undefined ? [] : [a]), ...(xs ?? [])]);
export const fibonacci = (n: ExprLike, x?: ExprLike): Expr => fn('fibonacci', x === undefined ? [n] : [n, x]);
export const lucas = (n: ExprLike): Expr => fn('lucas', [n]);
export const tribonacci = (n: ExprLike, x?: ExprLike): Expr => fn('tribonacci', x === undefined ? [n] : [n, x]);
export const partition = (n: ExprLike): Expr => fn('partition', [n]);
export const totientFn = (n: ExprLike): Expr => fn('totient', [n]);
export const reducedTotient = (n: ExprLike): Expr => fn('reduced_totient', [n]);
export const mobius = (n: ExprLike): Expr => fn('mobius', [n]);
export const divisorSigma = (n: ExprLike, k?: ExprLike): Expr => fn('divisor_sigma', k === undefined ? [n] : [n, k]);
export const primenu = (n: ExprLike): Expr => fn('primenu', [n]);
export const primeomega = (n: ExprLike): Expr => fn('primeomega', [n]);
export const primepiFn = (n: ExprLike): Expr => fn('primepi', [n]);
export const multigamma = (x: ExprLike, p: ExprLike): Expr => fn('multigamma', [x, p]);


export const frac = (x: ExprLike): Expr => fn('frac', [x]);

/**
 * Motzkin numbers M(0), ..., M(n-1) (SymPy motzkin.find_first_n_motzkins).
 *
 * @experimental May change in a minor release.
 */
export function firstMotzkins(n: number): bigint[] {
  const m: bigint[] = [];
  for (let k = 0; k < n; k++) {
    if (k < 2) m.push(1n);
    else m.push(((2n * BigInt(k) + 1n) * m[k - 1]! + (3n * BigInt(k) - 3n) * m[k - 2]!) / (BigInt(k) + 2n));
  }
  return m;
}

/**
 * Motzkin numbers in [x, y] (SymPy motzkin.find_motzkin_numbers_in_range).
 *
 * @experimental May change in a minor release.
 */
export function motzkinNumbersInRange(x: bigint, y: bigint): bigint[] {
  const out: bigint[] = [];
  let a = 1n;
  let b = 1n;
  if (x <= 1n && 1n <= y) out.push(1n);
  for (let k = 2n; ; k++) {
    const c = ((2n * k + 1n) * b + (3n * k - 3n) * a) / (k + 2n);
    if (c > y) break;
    if (c >= x) out.push(c);
    a = b;
    b = c;
  }
  return out;
}

/**
 * Is n a Motzkin number (SymPy motzkin.is_motzkin)?
 *
 * @experimental May change in a minor release.
 */
export function isMotzkin(n: bigint): boolean {
  if (n < 1n) return false;
  return motzkinNumbersInRange(n, n).length > 0;
}
