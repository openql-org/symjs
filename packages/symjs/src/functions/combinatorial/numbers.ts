// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Combinatorial numbers and polynomials and number-theoretic
 * functions (SymPy functions.combinatorial.numbers and ntheory):
 * Bernoulli, Euler, Genocchi, Bell, Fibonacci, Lucas, Tribonacci,
 * partitions, totients, Mobius, divisor sigma, prime counting, Jacobi
 * and Kronecker symbols, and the multivariate gamma function.
 */

import { at, first, last } from '../../core/guard';
import { isIntegerQ, isNegative, isPositive, isReal as isRealQ } from '../../core/assumptions';
import type { Expr, ExprLike, FnName } from '../../core/nodes';
import { Dummy, Fn, Pow, Rational, S, Special } from '../../core/nodes';
import { AccumBounds } from '../../core/accumbounds';
import { Product } from '../../core/concrete';
import { add, mul, pow, sympify } from '../../core/ops';
import { factorInt } from '../../core/numbers';
import { expandMul } from '../../simplify/expand';
import { evaluators, fn, forEachEntry } from '../elementary/elementary';
import { bernoulliNumber, floor as floorFn, gamma } from '../special/special';
import { isprime as ntheoryIsprime } from '../../ntheory/primetest';
import { invert } from '../../ntheory/intutil';

const R = (p: bigint | number, q: bigint | number = 1n) => Rational.of(BigInt(p), BigInt(q));
const asInt = (e: Expr): bigint | undefined => (e instanceof Rational && e.isInteger ? e.p : undefined);

function binom(n: number, k: number): bigint {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return r;
}

/** Bernoulli number with SymPy's convention B_1 = +1/2. */
function bernoulliPlus(n: number): Rational {
  return n === 1 ? R(1, 2) : (bernoulliNumber(n));
}

/** Bernoulli polynomial B_n(x) = sum C(n,k) B_k x^(n-k) with B_1 = -1/2. */
function bernoulliPoly(n: number, x: Expr): Expr {
  const terms: Expr[] = [];
  for (let k = 0; k <= n; k++) {
    const b = k === 1 ? R(-1, 2) : (bernoulliNumber(k));
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
    for (const [k, e] of eulerCache.entries()) if (k % 2 === 0) s += binom(m, k) * e;
    eulerCache.push(-s);
  }
  return at(eulerCache, n);
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
    let acc = last(row);
    const next = [acc];
    for (const v of row) {
      acc += v;
      next.push(acc);
    }
    row = next;
    bells.push(first(row));
  }
  return at(bells, n);
}

/** Stirling numbers of the second kind S(n, k). */
function stirling2(n: number, k: number): bigint {
  let prev: bigint[] = [1n];
  for (let i = 1; i <= n; i++) {
    const row: bigint[] = [0n];
    for (let j = 1; j <= i; j++) row[j] = BigInt(j) * (prev[j] ?? 0n) + at(prev, j - 1);
    prev = row;
  }
  return at(prev, k);
}

/** Incomplete Bell polynomial B_{n,k}(x_1, ..., x_{n-k+1}). */
function incompleteBell(n: number, k: number, xs: readonly Expr[]): Expr {
  if (n === 0 && k === 0) return S.One;
  if (n === 0 || k === 0) return S.Zero;
  const terms: Expr[] = [];
  for (let m = 1; m <= n - k + 1; m++) {
    terms.push(mul(R(binom(n - 1, m - 1)), at(xs, m - 1), incompleteBell(n - m, k - 1, xs)));
  }
  return expandMul(add(...terms));
}

function fibPoly(n: number, x: Expr): Expr {
  let [a, b]: [Expr, Expr] = [S.Zero, S.One];
  for (let i = 1; i < n; i++) [a, b] = [b, expandMul(add(mul(x, b), a))];
  return b;
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
  let [a, b, c]: [Expr, Expr, Expr] = [S.Zero, S.One, pow(x, 2)];
  if (n < 3) return at([a, b, c], n);
  for (let i = 3; i <= n; i++) [a, b, c] = [b, c, expandMul(add(mul(pow(x, 2), c), mul(x, b), a))];
  return c;
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
      s += sign * at(p, i - g1);
      if (g2 <= i) s += sign * at(p, i - g2);
    }
    p.push(s);
  }
  return at(p, n);
}

/** Primality test (deterministic Miller-Rabin for 64-bit, trial division otherwise). */
export function isprime(nIn: ExprLike | bigint): boolean {
  // SymPy's test (trial division, Miller-Rabin with fixed bases, then BPSW): no strong pseudoprimes pass
  return ntheoryIsprime(nIn);
}

/** Jacobi symbol (m/n) for odd positive n. */
export function jacobiSymbol(mIn: bigint, nIn: bigint): number {
  let n = nIn;
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
export function kroneckerSymbol(a: bigint, nIn: bigint): number {
  let n = nIn;
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

function carmichaelLambda(n: bigint): bigint {
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
  bernoulli: (n, x?: Expr) => {
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return small(k) ? bernoulliPoly(Number(k), x) : undefined;
    if (k > 1n && k % 2n === 1n) return S.Zero;
    return small(k) ? bernoulliPlus(Number(k)) : undefined;
  },
  euler: (n, x?: Expr) => {
    // SymPy euler.eval: euler(-1) = pi/2 and euler(-1, x) = digamma((x + 1)/2) - digamma(x/2)
    if (n instanceof Rational && n.p === -1n && n.q === 1n) {
      return x === undefined ? mul(R(1, 2), S.Pi) : add(fn('polygamma', [0, mul(add(x, 1), R(1, 2))]), mul(-1, fn('polygamma', [0, mul(x, R(1, 2))])));
    }
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return small(k) ? eulerPoly(Number(k), x) : undefined;
    return small(k) ? R(eulerNumber(Number(k))) : undefined;
  },
  genocchi: (n, x?: Expr) => {
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
  bell: (n, a?: Expr, ...rest: Expr[]) => {
    const b = rest.length ? rest[0] : undefined;
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (a === undefined) return R(bellNumber(Number(k)));
    if (b === undefined) {
      const terms: Expr[] = [];
      for (let j = 0; j <= Number(k); j++) terms.push(mul(R(stirling2(Number(k), j)), pow(a, j)));
      return add(...terms);
    }
    // SymPy raises TypeError for a symbolic k and IndexError when the symbols run out
    const kk = asInt(a);
    if (kk === undefined) throw new TypeError('bell: k must be an integer');
    if (k >= 1n && kk >= 1n && k - kk + 1n > BigInt(rest.length)) throw new RangeError('bell: too few symbols');
    return incompleteBell(Number(k), Number(kk), rest);
  },
  fibonacci: (n, x?: Expr) => {
    const k = asInt(n);
    if (k === undefined) return undefined;
    if (x !== undefined) {
      // SymPy raises ValueError for indices below 1 (fibonacci(0) = 0 is the number)
      if (k < 1n) throw new RangeError('Fibonacci polynomials are defined only for positive integer indices.');
      return fibPoly(Number(k), x);
    }
    return R(fibNumber(k));
  },
  lucas: (n) => {
    const k = asInt(n);
    if (k === undefined) return undefined;
    return R(fibNumber(k + 1n) + fibNumber(k - 1n));
  },
  tribonacci: (n, x?: Expr) => {
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return tribPoly(Number(k), x);
    let [a, b, c] = [0n, 1n, 1n];
    for (let i = 3; i <= Number(k); i++) [a, b, c] = [b, c, a + b + c];
    return R(k === 0n ? a : k === 1n ? b : c);
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
    return k !== undefined && k > 0n ? R(carmichaelLambda(k)) : undefined;
  },
  mobius: (n) => {
    const k = asInt(n);
    if (k === undefined) {
      // a square factor makes mobius of a positive integer vanish: mobius(4*n) = 0, and
      // mobius(b**2) = 0 for an integer b > 1 (SymPy also returns 0 when b may be 1)
      // (SymPy mobius.eval: every factor b**e is a positive integer b to a positive integer power e,
      // otherwise mobius(-4*n) stays unevaluated)
      if (isIntegerQ(n) !== true || isPositive(n) !== true) return undefined;
      const fs = n.kind === 'Mul' ? n.args : [n];
      let zero = false;
      for (const f of fs) {
        const [b, e]: [Expr, Expr] = f instanceof Pow ? [f.base, f.exp] : [f, S.One];
        if (isIntegerQ(b) !== true || isPositive(b) !== true || !(e instanceof Rational && e.isInteger && e.p > 0n)) return undefined;
        if (b instanceof Rational && [...factorInt(b.p).values()].some((m) => m > 1n)) zero = true;
        if (e.p > 1n && isPositive(add(b, -1)) === true) zero = true;
      }
      return zero ? S.Zero : undefined;
    }
    if (k <= 0n) throw new RangeError('mobius: n should be a positive integer');
    let r = 1n;
    for (const e of factorInt(k).values()) {
      if (e > 1n) return S.Zero;
      r = -r;
    }
    return R(r);
  },
  divisor_sigma: (n, kIn?: Expr) => {
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
    if (k === undefined && isIntegerQ(p) !== false && isPositive(p) !== false) {
      // pi**(p*(p - 1)/4)*Product(gamma(x + (1 - k)/2), (k, 1, p)) like SymPy
      const d = new Dummy('k');
      return mul(pow(S.Pi, mul(p, add(p, -1), R(1, 4))), Product(gamma(add(x, mul(add(1, mul(-1, d)), R(1, 2)))), [d, 1, p]));
    }
    if (k === undefined || k < 1n) throw new RangeError('multigamma: Order parameter p must be positive integer.');
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
    if (a instanceof Special) return a.name === 'oo' || a.name === '-oo' ? AccumBounds(0, 1) : S.NaN;
    if (isIntegerQ(a) === true) return S.Zero;
    if (a.freeSymbols().size === 0) return add(a, mul(-1, floorFn(a)));
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
  if (out instanceof Fn && out.name === 'frac' && first(out.args).key === x.key) return undefined;
  return out;
}
EVAL.frac = evalFrac;

forEachEntry(EVAL, (name, f) => {
  evaluators[name] = (...a: Expr[]) => f(...a);
});

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
  let a = 1n; // M(k - 2)
  let b = 1n; // M(k - 1)
  for (let k = 0; k < n; k++) {
    if (k < 2) m.push(1n);
    else {
      const c = ((2n * BigInt(k) + 1n) * b + (3n * BigInt(k) - 3n) * a) / (BigInt(k) + 2n);
      m.push(c);
      a = b;
      b = c;
    }
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

/** SymPy legendre_symbol(a, p) for an odd prime p: 0, 1 or -1. */
export function legendreSymbol(a: bigint | number, p: bigint | number): number {
  const P = BigInt(p);
  if (P < 3n || !isprime(P)) throw new RangeError('legendre_symbol: p should be an odd prime');
  return jacobiSymbol(BigInt(a), P);
}

/** SymPy motzkin(n) (motzkin.find_first_n_motzkins(n)[n - 1]). */
export function motzkin(n: number): bigint {
  if (!Number.isInteger(n) || n < 1) throw new RangeError('motzkin: n must be a positive integer');
  return at(firstMotzkins(n), n - 1);
}

/** SymPy andre(n): Euler zigzag (up/down) numbers 1, 1, 1, 2, 5, 16, 61, ... */
export function andre(n: number): bigint {
  if (!Number.isInteger(n) || n < 0) throw new RangeError('andre: n must be a nonnegative integer');
  // Seidel-Entringer triangle
  let row: bigint[] = [1n];
  for (let i = 1; i <= n; i++) {
    const next: bigint[] = [0n];
    let acc = 0n;
    for (let j = 1; j <= i; j++) {
      acc += at(row, i - j);
      next.push(acc);
    }
    row = next;
  }
  return at(row, n);
}

// ---- binomial coefficients modulo m ------------------------------------------------

const bmod = (a: bigint, m: bigint) => ((a % m) + m) % m;
function bpow(b: bigint, e: bigint, m: bigint): bigint {
  let r = 1n;
  let x = bmod(b, m);
  for (let k = e; k > 0n; k >>= 1n) {
    if (k & 1n) r = (r * x) % m;
    x = (x * x) % m;
  }
  return r;
}

/** G(r) = product of the integers in [1, r] prime to p, modulo p**e, for r < p**e. */
function pFreeProductFactory(p: bigint, e: number): (r: bigint) => bigint {
  const pe = p ** BigInt(e);
  if (pe <= 4_000_000n) {
    const n = Number(pe);
    const table = new Array<bigint>(n);
    let acc = 1n;
    table[0] = 1n;
    for (let i = 1; i < n; i++) {
      if (BigInt(i) % p !== 0n) acc = (acc * BigInt(i)) % pe;
      table[i] = acc;
    }
    return (r) => at(table, Number(r));
  }
  if (e === 1 && p <= 20_000_000n) {
    const n = Number(p);
    const fact = new Array<bigint>(n);
    fact[0] = 1n;
    let f = 1n;
    for (let i = 1; i < n; i++) {
      f = (f * BigInt(i)) % p;
      fact[i] = f;
    }
    return (r) => at(fact, Number(r));
  }
  if (e === 2 && p >= 3n && p <= 20_000_000n) {
    // r = a*p + b: ((p - 1)!)**a * b! * (1 + a*p*H_b) mod p**2 (each full block is (p - 1)! since H_{p-1} = 0 mod p)
    const n = Number(p);
    const fact = new Array<bigint>(n);
    const harm = new Array<bigint>(n);
    fact[0] = 1n;
    harm[0] = 0n;
    let f = 1n;
    let h = 0n;
    for (let i = 1; i < n; i++) {
      f = (f * BigInt(i)) % pe;
      h = (h + invert(BigInt(i), p)) % p;
      fact[i] = f;
      harm[i] = h;
    }
    const block = f;
    return (r) => {
      const a = r / p;
      const b = Number(r % p);
      return (bpow(block, a, pe) * at(fact, b) % pe) * bmod(1n + a * p * at(harm, b), pe) % pe;
    };
  }
  throw new RangeError('binomial_mod: modulus too large');
}

/** (n!)_p = n! without its factors p, modulo p**e. */
function pFreeFactorial(n: bigint, p: bigint, e: number, G: (r: bigint) => bigint): bigint {
  const pe = p ** BigInt(e);
  // the product over a full period of p**e is -1 (1 for 2**e, e >= 3)
  const period = p === 2n && e >= 3 ? 1n : pe - 1n;
  let r = 1n;
  for (let m = n; m > 0n; m /= p) r = (r * bpow(period, m / pe, pe) % pe) * G(m % pe) % pe;
  return r;
}

const digitSum = (n: bigint, p: bigint) => {
  let s = 0n;
  for (let m = n; m > 0n; m /= p) s += m % p;
  return s;
};

/** binomial(n, k) modulo m for nonnegative integers (prime-power moduli of moderate size). */
export function binomialMod(n: bigint, k: bigint, m: bigint): bigint {
  if (k < 0n || k > n) return 0n;
  if (m === 1n) return 0n;
  // prime-power parts of m, combined by the Chinese remainder theorem
  let result = 0n;
  let mod = 1n;
  let rest = m;
  for (let p = 2n; p * p <= rest || rest > 1n; p++) {
    if (p * p > rest) p = rest;
    if (rest % p !== 0n) continue;
    let e = 0;
    while (rest % p === 0n) {
      rest /= p;
      e++;
    }
    const pe = p ** BigInt(e);
    // Kummer: the exponent of p in binomial(n, k)
    const v = (digitSum(k, p) + digitSum(n - k, p) - digitSum(n, p)) / (p - 1n);
    let r: bigint;
    if (v >= BigInt(e)) r = 0n;
    else {
      const G = pFreeProductFactory(p, e);
      const u = pFreeFactorial(n, p, e, G) * invert(pFreeFactorial(k, p, e, G) * pFreeFactorial(n - k, p, e, G), pe);
      r = (p ** v * u) % pe;
    }
    // combine x = result (mod mod) and x = r (mod pe)
    const t = bmod((r - result) * invert(mod, pe), pe);
    result += mod * t;
    mod *= pe;
    if (rest === 1n) break;
  }
  return bmod(result, mod);
}

// ---- Carmichael numbers (SymPy carmichael / sympy.ntheory.factor_) ----------------

function toBig(n: ExprLike | bigint | number): bigint {
  if (typeof n === 'bigint') return n;
  if (typeof n === 'number') return BigInt(n);
  const v = sympify(n);
  if (!(v instanceof Rational && v.isInteger)) throw new TypeError(`expected an integer, got ${v.toString()}`);
  return v.p;
}

/** SymPy is_carmichael: n is composite, squarefree and p - 1 | n - 1 for each prime p | n (Korselt). */
export function isCarmichael(nIn: ExprLike | bigint | number): boolean {
  const n = toBig(nIn);
  if (n < 561n || n % 2n === 0n || isprime(n)) return false;
  for (const [p, e] of factorInt(n)) if (e > 1n || (n - 1n) % (p - 1n) !== 0n) return false;
  return true;
}

/** SymPy find_carmichael_numbers_in_range(x, y): the Carmichael numbers in [x, y). */
export function findCarmichaelNumbersInRange(x: ExprLike | bigint | number, y: ExprLike | bigint | number): bigint[] {
  const lo = toBig(x);
  const hi = toBig(y);
  if (lo < 0n || hi < 0n || lo > hi) throw new RangeError('The provided range is not valid. x and y must be non-negative integers and x <= y');
  const out: bigint[] = [];
  for (let k = lo % 2n === 0n ? lo + 1n : lo; k < hi; k += 2n) if (isCarmichael(k)) out.push(k);
  return out;
}

/** SymPy find_first_n_carmichaels(n): the first n Carmichael numbers. */
export function findFirstNCarmichaels(n: number): bigint[] {
  const out: bigint[] = [];
  for (let k = 561n; out.length < n; k += 2n) if (isCarmichael(k)) out.push(k);
  return out;
}

/** SymPy carmichael (the deprecated class): its static methods. */
export const carmichael = { isCarmichael, findCarmichaelNumbersInRange, findFirstNCarmichaels } as const;
