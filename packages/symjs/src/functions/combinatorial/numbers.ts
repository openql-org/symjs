// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Parts ported from SymPy (sympy/functions/combinatorial/numbers.py),
// Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Combinatorial numbers and polynomials and number-theoretic
 * functions (SymPy functions.combinatorial.numbers and ntheory):
 * Bernoulli, Euler, Genocchi, Bell, Fibonacci, Lucas, Tribonacci,
 * partitions, totients, Mobius, divisor sigma, prime counting, Jacobi
 * and Kronecker symbols, and the multivariate gamma function.
 */

import { at, defined, first, last } from '../../core/guard';
import { isIntegerQ, isNegative, isPositive, isReal as isRealQ, isZero } from '../../core/assumptions';
import type { ExprLike, FnName } from '../../core/nodes';
import { Dummy, Expr, Float, Fn, Pow, Rational, S, Special, Sym, functionFactHandlers, impl, registerFunctionHeads, registerRewrite } from '../../core/nodes';
import { AccumBounds } from '../../core/accumbounds';
import { Product } from '../../core/concrete';
import { add, mul, pow, sqrt, sympify } from '../../core/ops';
import { factorInt } from '../../core/numbers';
import { expandMul } from '../../simplify/expand';
import { cos, evaluators, fn, forEachEntry, log } from '../elementary/elementary';
import { bernoulliNumber, ceiling as ceilingFn, floor as floorFn, gamma } from '../special/special';
import { Eq, piecewise, rel } from '../../core/logic';
import { fnPartials } from '../../calculus/diff';
import { Mod } from '../mod';
import { mpExprFns, mpFns } from '../../numeric/mpeval';
import * as F from '../../numeric/mpf';
import * as M from '../../numeric/mpfun';
import type { Mpc } from '../../numeric/mpfun';
import { cloggamma, cpolygamma, czeta } from '../../numeric/mpspecial';
import type { RelOp } from '../../core/nodes';
import { isprime as ntheoryIsprime } from '../../ntheory/primetest';
import type { IntLike } from '../../ntheory/intutil';
import { primepiInt } from '../../ntheory/generate';
import { asInt as intOf, invert } from '../../ntheory/intutil';
import { multisetPartitionsTaocp } from '../../utilities/enumerative';
import { valueKey } from '../../utilities/values';

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
export function jacobiSymbol(m: bigint, n: bigint): number;
export function jacobiSymbol(m: ExprLike, n: ExprLike): Expr;
export function jacobiSymbol(m: ExprLike, n: ExprLike): number | Expr {
  return typeof m === 'bigint' && typeof n === 'bigint' ? jacobiInt(m, n) : fn('jacobi_symbol', [m, n]);
}

function jacobiInt(mIn: bigint, nIn: bigint): number {
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
export function kroneckerSymbol(a: bigint, n: bigint): number;
export function kroneckerSymbol(a: ExprLike, n: ExprLike): Expr;
export function kroneckerSymbol(a: ExprLike, n: ExprLike): number | Expr {
  return typeof a === 'bigint' && typeof n === 'bigint' ? kroneckerInt(a, n) : fn('kronecker_symbol', [a, n]);
}

function kroneckerInt(a: bigint, nIn: bigint): number {
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
  return t * jacobiInt(a, n);
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

/** Validate the domain shared by multiplicative arithmetic functions. */
function positiveInteger(n: Expr): void {
  if (isIntegerQ(n) === false) throw new TypeError('argument must be an integer');
  if (isPositive(n) === false || (n instanceof Sym && n.assumptions.positive === false)) throw new RangeError('argument must be positive');
}

const oddArgument = (n: Expr): boolean => (n instanceof Sym && n.assumptions.odd === true) || isIntegerQ(mul(add(n, -1), R(1, 2))) === true;

const primeArgument = (n: Expr): boolean => n instanceof Sym && n.assumptions.prime === true;

type ResidueSymbol = 'legendre_symbol' | 'jacobi_symbol' | 'kronecker_symbol';
function evalResidueSymbol(name: ResidueSymbol, a: Expr, n: Expr): Expr | undefined {
  const noninteger = (e: Expr): boolean => e !== S.NaN && isIntegerQ(e) === false;
  if (noninteger(a) || noninteger(n)) throw new TypeError('residue symbol arguments must be integers');
  const m = asInt(a);
  const k = asInt(n);
  const symbolFacts = n instanceof Sym ? n.assumptions0 : undefined;
  const notOdd = (): boolean => symbolFacts?.get('odd') === false || Mod(n, 2).equals(S.Zero);
  if (name === 'legendre_symbol') {
    const notPrime = k === undefined ? symbolFacts?.get('prime') === false : k < 3n || !isprime(k);
    if (notPrime || notOdd()) throw new RangeError('legendreSymbol requires an odd prime denominator');
    if (m !== undefined && k !== undefined) return R(jacobiInt(m, k));
  } else if (name === 'jacobi_symbol') {
    if ((symbolFacts?.get('positive') ?? isPositive(n)) === false || notOdd()) throw new RangeError('jacobiSymbol requires an odd positive denominator');
    if (m !== undefined && k !== undefined) return R(jacobiInt(m, k));
  } else if (m !== undefined && k !== undefined) return R(kroneckerInt(m, k));
  if (m === 1n || (name !== 'legendre_symbol' && k === 1n)) return S.One;
  if (name !== 'kronecker_symbol' && isIntegerQ(a) === true && Mod(a, n).equals(S.Zero)) return S.Zero;
  return undefined;
}

// ---------------------------------------------------------------------------
// evaluators
// ---------------------------------------------------------------------------

const small = (n: bigint) => n >= 0n && n <= 5000n;

const EVAL: Partial<Record<FnName, (...a: Expr[]) => Expr | undefined>> = {
  bernoulli: (n, x?: Expr) => {
    if (x instanceof Rational && x.isOne) return fn('bernoulli', [n]);
    if (x === undefined && oddArgument(n) && isPositive(add(n, -1)) === true) return S.Zero;
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return small(k) ? bernoulliPoly(Number(k), x) : undefined;
    return small(k) ? bernoulliPlus(Number(k)) : undefined;
  },
  euler: (n, x?: Expr) => {
    if (x === undefined && oddArgument(n) && isPositive(n) === true) return S.Zero;
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
      if (x === undefined && oddArgument(n) && isPositive(add(n, -1)) === true) return S.Zero;
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
  andre: (n) => {
    if (n === S.NaN || n === S.Infinity) return n;
    if (isZero(n) === true) return S.One;
    const k = asInt(n);
    if (k === undefined) return undefined;
    if (k >= 0n) return R(andreInteger(Number(k)));
    if (k === -1n) return mul(-1, log(2));
    if (k === -2n) return mul(-2, S.Catalan);
    if (k % 2n === 0n) return undefined;
    const j = -k - 1n;
    return mul(R((j % 4n === 0n ? 1n : -1n) * (1n - 2n ** j), 4n ** j), fn('zeta', [R(-k)]));
  },
  legendre_symbol: (a, n) => evalResidueSymbol('legendre_symbol', a, n),
  jacobi_symbol: (a, n) => evalResidueSymbol('jacobi_symbol', a, n),
  kronecker_symbol: (a, n) => evalResidueSymbol('kronecker_symbol', a, n),
  bell: (n, a?: Expr, ...rest: Expr[]) => {
    if (n === S.Infinity) {
      if (a !== undefined) throw new RangeError('Bell polynomial requires a finite index');
      return S.Infinity;
    }
    if (isIntegerQ(n) === false || isNegative(n) === true) throw new RangeError('bell requires a nonnegative integer');
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
    if (n === S.Infinity) return S.Infinity;
    if (isNegative(n) === true && isIntegerQ(n) === true) throw new RangeError('tribonacci requires a nonnegative integer');
    const k = asInt(n);
    if (k === undefined || k < 0n) return undefined;
    if (x !== undefined) return tribPoly(Number(k), x);
    let [a, b, c] = [0n, 1n, 1n];
    for (let i = 3; i <= Number(k); i++) [a, b, c] = [b, c, a + b + c];
    return R(k === 0n ? a : k === 1n ? b : c);
  },
  partition: (n) => {
    if (isIntegerQ(n) === false) throw new TypeError('partition requires an integer');
    const k = asInt(n);
    if (k === undefined) return isIntegerQ(n) === true && isNegative(n) === true ? S.Zero : undefined;
    if (k < 0n) return S.Zero;
    return R(partitionNumber(Number(k)));
  },
  totient: (n) => {
    positiveInteger(n);
    if (primeArgument(n)) return add(n, -1);
    const k = asInt(n);
    return k !== undefined && k > 0n ? R(totient(k)) : undefined;
  },
  reduced_totient: (n) => {
    positiveInteger(n);
    if (primeArgument(n)) return add(n, -1);
    const k = asInt(n);
    return k !== undefined && k > 0n ? R(carmichaelLambda(k)) : undefined;
  },
  mobius: (n) => {
    positiveInteger(n);
    if (primeArgument(n)) return R(-1);
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
        if (isIntegerQ(b) !== true || isPositive(b) !== true || isIntegerQ(e) !== true || isPositive(e) !== true) return undefined;
        if (b instanceof Rational && [...factorInt(b.p).values()].some((m) => m > 1n)) zero = true;
        if (isPositive(add(e, -1)) === true && isPositive(add(b, -1)) === true) zero = true;
      }
      return zero ? S.Zero : undefined;
    }
    let r = 1n;
    for (const e of factorInt(k).values()) {
      if (e > 1n) return S.Zero;
      r = -r;
    }
    return R(r);
  },
  divisor_sigma: (n, kIn?: Expr) => {
    positiveInteger(n);
    const order = kIn ?? S.One;
    if (isIntegerQ(order) === false) throw new TypeError('order must be an integer');
    if (isNegative(order) === true) throw new RangeError('order must be nonnegative');
    if (primeArgument(n)) return add(1, pow(n, order));
    const m = asInt(n);
    const k = asInt(order);
    if (m === 1n) return S.One;
    if (m !== undefined && k === undefined) return mul(...[...factorInt(m)].map(([p, e]) => add(...Array.from({ length: Number(e + 1n) }, (_, i) => pow(R(p), mul(order, i))))));
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
  udivisor_sigma: (n, kIn?: Expr) => {
    positiveInteger(n);
    const k = kIn ?? S.One;
    if (isIntegerQ(n) === false || isIntegerQ(k) === false) throw new TypeError('udivisor_sigma requires integer arguments');
    if (isPositive(n) === false || isNegative(k) === true) throw new RangeError('udivisor_sigma requires n > 0 and k >= 0');
    if (primeArgument(n)) return add(1, pow(n, k));
    const m = asInt(n);
    if (m === undefined) return undefined;
    return mul(...[...factorInt(m)].map(([p, e]) => add(1, pow(R(p), mul(k, R(e))))));
  },
  primenu: (n) => {
    positiveInteger(n);
    if (primeArgument(n)) return S.One;
    const k = asInt(n);
    return k !== undefined && k > 0n ? R(k === 1n ? 0 : factorInt(k).size) : undefined;
  },
  primeomega: (n) => {
    positiveInteger(n);
    if (primeArgument(n)) return S.One;
    const k = asInt(n);
    if (k === undefined || k <= 0n) return undefined;
    let c = 0n;
    if (k > 1n) for (const e of factorInt(k).values()) c += e;
    return R(c);
  },
  primepi: (n) => {
    if (n === S.Infinity) return S.Infinity;
    if (n === S.NegativeInfinity) return S.Zero;
    if (isRealQ(n) === false) throw new TypeError('primepi requires a real argument');
    if (rel('Lt', n, 2) === S.true) return S.Zero;
    const value = n instanceof Rational ? n.p / n.q : n instanceof Float ? BigInt(Math.trunc(n.value)) : undefined;
    return value === undefined ? undefined : R(primepiInt(value));
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

/** The facts the comparison rules need, from the assumptions of the expressions (an extended real includes oo and -oo). */
const FACTS = {
  extended_real: (e: Expr) => isRealQ(e) === true,
  real: (e: Expr) => isRealQ(e) === true && !(e instanceof Special),
  finite: (e: Expr) => isRealQ(e) === true && !e.has(S.Infinity) && !e.has(S.NegativeInfinity),
  integer: (e: Expr) => isIntegerQ(e) === true,
  noninteger: (e: Expr) => isIntegerQ(e) === false && isRealQ(e) === true,
  positive: (e: Expr) => isPositive(e) === true && !(e instanceof Special),
  extended_negative: (e: Expr) => isNegative(e) === true,
  extended_nonpositive: (e: Expr) => isPositive(e) === false && isRealQ(e) === true,
} as const;
const holds = (p: keyof typeof FACTS, e: Expr): boolean => FACTS[p](e);
const isRoundFn = (e: Expr): e is Fn => e instanceof Fn && (e.name === 'floor' || e.name === 'ceiling' || e.name === 'frac');

/** SymPy frac._value_one_or_more: other is known to be at least 1. */
const oneOrMore = (other: Expr): boolean =>
  holds('extended_real', other) && ((other.freeSymbols().size === 0 && rel('Ge', other, 1) === S.true) || (holds('integer', other) && holds('positive', other)));

/**
 * SymPy floor and ceiling comparisons (their __lt__, __le__, __gt__ and
 * __ge__): against an integer or a real number the comparison is one of the
 * argument. The bound of a number is taken through its floor and ceiling,
 * which is also exact for an integer-valued Float.
 */
function floorCeilingRelation(op: Exclude<RelOp, 'Eq' | 'Ne'>, f: Fn, other: Expr): Expr | undefined {
  const a = first(f.args);
  const isFloor = f.name === 'floor';
  if (holds('real', a) && (holds('integer', other) || (other.freeSymbols().size === 0 && holds('real', other)))) {
    const lo = floorFn(other);
    const hi = ceilingFn(other);
    if (isFloor) return { Le: () => rel('Lt', a, add(lo, 1)), Gt: () => rel('Ge', a, add(lo, 1)), Ge: () => rel('Ge', a, hi), Lt: () => rel('Lt', a, hi) }[op]();
    return { Lt: () => rel('Le', a, add(hi, -1)), Ge: () => rel('Gt', a, add(hi, -1)), Gt: () => rel('Gt', a, lo), Le: () => rel('Le', a, lo) }[op]();
  }
  if (a.key === other.key && holds('real', other)) {
    // floor(x) <= x <= ceiling(x), strictly when x is not an integer
    const weak = isFloor ? op === 'Le' : op === 'Ge';
    const strict = isFloor ? op === 'Lt' : op === 'Gt';
    if (weak) return S.true;
    if (strict) return holds('noninteger', other) ? S.true : undefined;
    return op === 'Le' || op === 'Ge' ? (holds('noninteger', other) ? S.false : undefined) : S.false;
  }
  if (holds('finite', a) && ((other === S.Infinity && (op === 'Lt' || op === 'Le')) || (other === S.NegativeInfinity && (op === 'Gt' || op === 'Ge')))) return S.true;
  return undefined;
}

/** SymPy frac comparisons: 0 <= frac(x) < 1 for an extended real x. */
function fracRelation(op: Exclude<RelOp, 'Eq' | 'Ne'>, f: Fn, other: Expr): Expr | undefined {
  if (!holds('extended_real', first(f.args))) return undefined;
  const large = oneOrMore(other);
  switch (op) {
    case 'Ge':
      return holds('extended_nonpositive', other) ? S.true : large ? S.false : undefined;
    case 'Gt':
      return large ? S.false : holds('extended_negative', other) ? S.true : undefined;
    case 'Le':
      return holds('extended_negative', other) ? S.false : large ? S.true : undefined;
    default:
      return holds('extended_nonpositive', other) ? S.false : large ? S.true : undefined;
  }
}

/** SymPy _eval_is_eq of floor, ceiling and frac: true, false or undefined. */
function roundEquality(f: Fn, other: Expr): boolean | undefined {
  const a = first(f.args);
  const forms =
    f.name === 'floor' ? [mul(-1, ceilingFn(mul(-1, a))), add(a, mul(-1, frac(a)))]
    : f.name === 'ceiling' ? [mul(-1, floorFn(mul(-1, a))), add(a, frac(mul(-1, a)))]
    : [add(a, mul(-1, floorFn(a))), add(a, ceilingFn(mul(-1, a)))];
  if (f.name === 'frac') {
    if (forms.some((g) => g.key === other.key)) return true;
    return holds('extended_negative', other) || oneOrMore(other) ? false : undefined;
  }
  let result: boolean | undefined;
  for (const g of forms) {
    const r = rel('Eq', g, other);
    if (r === S.true) return true;
    if (r === S.false) result = false;
  }
  return result;
}

impl.relational = (op, lhs, rhs) => {
  if (op === 'Eq' || op === 'Ne') {
    const r = isRoundFn(lhs) ? roundEquality(lhs, rhs) : undefined;
    const v = r ?? (isRoundFn(rhs) ? roundEquality(rhs, lhs) : undefined);
    return v === undefined ? undefined : v === (op === 'Eq') ? S.true : S.false;
  }
  if (!isRoundFn(lhs)) return undefined;
  return lhs.name === 'frac' ? fracRelation(op, lhs, rhs) : floorCeilingRelation(op, lhs, rhs);
};

forEachEntry(EVAL, (name, f) => {
  evaluators[name] = (...a: Expr[]) => f(...a);
});

const minus = (x: Expr): Expr => mul(-1, x);
const zeta = (...args: ExprLike[]): Expr => fn('zeta', args);
const bernoulliRewrite = (n: Expr, x: Expr): Expr => mul(minus(n), zeta(add(1, minus(n)), x));

registerRewrite('bernoulli', 'zeta', (args) => {
  const n = first(args);
  return piecewise([1, Eq(n, 0)], [bernoulliRewrite(n, args[1] ?? S.One), true]);
});
registerRewrite('genocchi', 'dirichlet_eta', (args) => {
  const n = first(args);
  return mul(-2, n, fn('dirichlet_eta', [add(1, minus(n)), args[1] ?? S.One]));
});
registerRewrite('andre', 'polylog', (args) => {
  const s = first(args);
  const k = add(s, 1);
  return add(mul(pow(minus(S.I), k), fn('polylog', [minus(s), S.I])),
    mul(pow(S.I, k), fn('polylog', [minus(s), minus(S.I)])));
});
registerRewrite('andre', 'zeta', (args) => {
  const s = first(args);
  const k = add(s, 1);
  return mul(2, gamma(k), pow(mul(2, S.Pi), minus(k)),
    add(zeta(k, R(1, 4)), mul(-1, cos(mul(S.Pi, s)), zeta(k, R(3, 4)))));
});

const binetTerms = (n: Expr): readonly [Expr, Expr] => {
  const root = sqrt(5);
  return [pow(add(1, root), n), pow(add(1, minus(root)), n)];
};
registerRewrite('fibonacci', 'sqrt', (args) => {
  if (args.length !== 1) return undefined;
  const n = first(args);
  const [a, b] = binetTerms(n);
  return mul(R(1, 5), sqrt(5), pow(2, minus(n)), add(a, minus(b)));
});
registerRewrite('lucas', 'sqrt', (args) => {
  const n = first(args);
  return mul(pow(2, minus(n)), add(...binetTerms(n)));
});
registerRewrite('tribonacci', 'sqrt', (args) => {
  if (args.length !== 1) return undefined;
  const n = first(args);
  const w = add(S.NegHalf, mul(S.Half, S.I, sqrt(3)));
  const root = mul(3, sqrt(33));
  const a = pow(add(19, root), R(1, 3));
  const b = pow(add(19, minus(root)), R(1, 3));
  const roots = [add(a, b), add(mul(w, a), mul(pow(w, 2), b)), add(mul(pow(w, 2), a), mul(w, b))]
    .map((t) => mul(R(1, 3), add(1, t)));
  return add(...roots.map((r, i) => mul(pow(r, add(n, 1)),
    ...roots.flatMap((other, j) => i === j ? [] : [pow(expandMul(add(r, minus(other))), -1)]))));
});
registerRewrite('tribonacci', 'TribonacciConstant', (args) => {
  if (args.length !== 1) return undefined;
  const n = first(args);
  const b = pow(add(586, mul(102, sqrt(33))), R(1, 3));
  return floorFn(add(mul(3, b, pow(S.TribonacciConstant, n), pow(add(pow(b, 2), mul(-2, b), 4), -1)), S.Half));
});

fnPartials['harmonic'] = (args, i) => {
  if (i !== 0) return undefined;
  const m = args[1] ?? S.One;
  return mul(m, zeta(add(m, 1), add(first(args), 1)));
};

for (const name of [
  'legendre_symbol', 'jacobi_symbol', 'kronecker_symbol', 'mobius',
  'primepi', 'primenu', 'primeomega', 'partition', 'divisor_sigma', 'udivisor_sigma',
  'totient', 'reduced_totient', 'andre', 'catalan', 'genocchi',
] as const) {
  functionFactHandlers[name] = (fact, args, query) => {
    switch (name) {
      case 'legendre_symbol':
      case 'jacobi_symbol':
      case 'kronecker_symbol':
      case 'mobius':
        return fact === 'integer' ? true : fact === 'prime' ? false : undefined;
      case 'primepi':
      case 'primenu':
      case 'primeomega':
      case 'partition':
        if (fact === 'integer' || fact === 'nonnegative') return true;
        return name === 'partition' && fact === 'positive' && query('nonnegative', first(args)) === true ? true : undefined;
      case 'divisor_sigma':
      case 'udivisor_sigma':
      case 'totient':
      case 'reduced_totient':
        return fact === 'integer' || fact === 'positive' ? true : undefined;
      case 'andre':
      case 'catalan':
      case 'genocchi':
        break;
    }
    const n = first(args);
    if (name === 'catalan' && fact === 'composite') {
      return query('integer', n) === true && query('positive', add(n, -3)) === true ? true : undefined;
    }
    if (name !== 'genocchi' && fact === 'positive') return query('nonnegative', n) === true ? true : undefined;
    if (args.length > 1 && !args[1]?.equals(S.One)) return undefined;
    if (name === 'genocchi' && fact === 'prime') return query('zero', add(n, -8));
    if (query('integer', n) !== true) return undefined;
    const even = query('even', n);
    // An even integer strictly above -2 is nonnegative.
    if (query('nonnegative', n) !== true && !(even === true && query('positive', add(n, 2)) === true)) return undefined;
    if (fact === 'integer') return true;
    if (name !== 'genocchi') return undefined;
    const zero = query('zero', n);
    if (fact === 'positive') return zero === true || even === false ? false : query('even', mul(S.Half, n));
    if (fact === 'negative' && even !== false) return query('odd', mul(S.Half, n));
    const parity = even === true ? zero : query('positive', add(n, -1));
    if (fact === 'even') return parity;
    if (fact === 'odd' || fact === 'negative') return parity === undefined ? parity : !parity;
    return undefined;
  };
}

const mpInt = (n: bigint): Mpc => [F.fromInt(n), F.ZERO];
const mpHalf: Mpc = [{ man: 1n, exp: -1n }, F.ZERO];
const mpTwo = mpInt(2n);
const mpFour = mpInt(4n);
const mpQuarter: Mpc = [{ man: 1n, exp: -2n }, F.ZERO];
const mpThreeQuarters: Mpc = [{ man: 3n, exp: -2n }, F.ZERO];
const mpEqualInt = (n: Mpc, k: bigint): boolean => M.isReal(n) && F.cmp(n[0], F.fromInt(k)) === 0;

// The functional equation gives B_n without constructing its exact rational numerator.
mpExprFns['bernoulli'] = (e, _evaluate, prec) => {
  const n = first(e.args);
  if (e.args.length !== 1 || !(n instanceof Rational) || !n.isInteger || n.p <= 5000n) return undefined;
  if (n.p % 2n === 1n) return M.C0;
  const wp = prec + 20 + n.p.toString(2).length;
  const a = F.fromInt(n.p);
  const logFactorial = cloggamma(mpInt(n.p + 1n), wp)[0];
  const logTwoPi = M.log(F.ldexp(M.mpPi(wp), 1), wp);
  const magnitude = M.exp(F.sub(logFactorial, F.mul(a, logTwoPi, wp), wp), prec + 10);
  let z = F.ONE;
  for (let k = 2n; ; k++) {
    const term = F.powInt(F.fromInt(k), -n.p, wp);
    // The integral test bounds the entire omitted tail by (k + 1)*k**(-n).
    if (F.mag(term) + k.toString(2).length + 1 <= -wp) break;
    z = F.add(z, term, wp);
  }
  return [F.mulInt(F.mul(magnitude, z, prec), n.p % 4n === 0n ? -2n : 2n), F.ZERO];
};

function mpBernoulli(n: Mpc, x: Mpc, p: number): Mpc {
  if (mpEqualInt(n, 0n)) return M.C1;
  if (mpEqualInt(n, 1n)) return M.csub(x, mpHalf, p);
  return M.cmul(M.cneg(n), czeta(M.csub(M.C1, n, p), p, x), p);
}
mpFns['bernoulli'] = (args, prec) => mpBernoulli(first(args), args[1] ?? M.C1, prec + 20);
mpFns['genocchi'] = (args, prec) => {
  const n = first(args);
  const x = args[1] ?? M.C1;
  const p = prec + 30;
  const a = mpBernoulli(n, x, p);
  const b = mpBernoulli(n, M.cmul(M.cadd(x, M.C1, p), mpHalf, p), p);
  return M.cmul(mpTwo, M.csub(a, M.cmul(M.cpow(mpTwo, n, p), b, p), p), p);
};
mpFns['euler'] = (args, prec) => {
  const n = first(args);
  const x = args[1] ?? mpHalf;
  const p = prec + 30;
  const halfShift = M.cmul(mpHalf, M.cadd(x, M.C1, p), p);
  if (mpEqualInt(n, -1n)) {
    if (args.length === 1) return [F.ldexp(M.mpPi(p), -1), F.ZERO];
    return M.csub(cpolygamma(0, halfShift, p), cpolygamma(0, M.cmul(x, mpHalf, p), p), p);
  }
  const s = M.cneg(n);
  const b = M.cmul(M.cpow(mpTwo, M.cadd(n, M.C1, p), p), czeta(s, p, halfShift), p);
  const result = M.cmul(mpTwo, M.csub(czeta(s, p, x), b, p), p);
  return args.length === 1 ? M.cmul(result, M.cpow(mpTwo, n, p), p) : result;
};
mpExprFns['andre'] = (e, evaluate) => {
  const exact = EVAL.andre?.(first(e.args));
  return exact === undefined ? undefined : evaluate(exact);
};
mpFns['andre'] = (args, prec) => {
  // Split the Dirichlet series into residue classes modulo 4.
  const n = first(args);
  const p = prec + 30;
  const s = M.cneg(n);
  const angle = M.cmul(n, [F.ldexp(M.mpPi(p), -1), F.ZERO], p);
  const odd = M.csub(czeta(s, p, mpQuarter), czeta(s, p, mpThreeQuarters), p);
  const even = M.csub(czeta(s, p, mpHalf), czeta(s, p), p);
  return M.cmul(M.cmul(mpTwo, M.cpow(mpFour, n, p), p),
    M.cadd(M.cmul(M.ccos(angle, p), odd, p), M.cmul(M.csin(angle, p), even, p), p), p);
};

export const bernoulli = (n: ExprLike, x?: ExprLike): Expr => fn('bernoulli', x === undefined ? [n] : [n, x]);
export const euler = (n: ExprLike, x?: ExprLike): Expr => fn('euler', x === undefined ? [n] : [n, x]);
export const genocchi = (n: ExprLike, x?: ExprLike): Expr => fn('genocchi', x === undefined ? [n] : [n, x]);
export const bell = (n: ExprLike, a?: ExprLike, xs?: readonly ExprLike[]): Expr => fn('bell', [n, ...(a === undefined ? [] : [a]), ...(xs ?? [])]);
export const fibonacci = (n: ExprLike, x?: ExprLike): Expr => fn('fibonacci', x === undefined ? [n] : [n, x]);
export const lucas = (n: ExprLike): Expr => fn('lucas', [n]);
export const tribonacci = (n: ExprLike, x?: ExprLike): Expr => fn('tribonacci', x === undefined ? [n] : [n, x]);
export const partition = (n: ExprLike): Expr => fn('partition', [n]);
/** An integer supplied directly or by its prime factorization. */
type FactoredInteger = ExprLike | ReadonlyMap<ExprLike, ExprLike>;
function factoredExpr(n: FactoredInteger): Expr {
  if (typeof n === 'object' && !(n instanceof Expr)) return mul(...[...n].map(([p, k]) => pow(p, k)));
  return sympify(n);
}
export const totientFn = (n: FactoredInteger): Expr => fn('totient', [factoredExpr(n)]);
export const reducedTotient = (n: FactoredInteger): Expr => fn('reduced_totient', [factoredExpr(n)]);
export const mobius = (n: ExprLike): Expr => fn('mobius', [n]);
export const divisorSigma = (n: ExprLike, k?: ExprLike): Expr => fn('divisor_sigma', k === undefined ? [n] : [n, k]);
/** Sum of k-th powers of the unitary divisors of n. */
export const udivisorSigma = (n: ExprLike, k?: ExprLike): Expr => fn('udivisor_sigma', k === undefined ? [n] : [n, k]);
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
  if (!Number.isInteger(n) || n < 0) throw new RangeError('count must be a nonnegative integer');
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
  if (x < 0n || y < x) throw new RangeError('invalid Motzkin range');
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
export function legendreSymbol(a: bigint | number, p: bigint | number): number;
export function legendreSymbol(a: ExprLike, p: ExprLike): Expr;
export function legendreSymbol(a: ExprLike, p: ExprLike): number | Expr {
  if ((typeof a !== 'bigint' && typeof a !== 'number') || (typeof p !== 'bigint' && typeof p !== 'number')) return fn('legendre_symbol', [a, p]);
  const P = BigInt(p);
  if (P < 3n || !isprime(P)) throw new RangeError('legendre_symbol: p should be an odd prime');
  return jacobiInt(BigInt(a), P);
}

/** SymPy motzkin(n) (motzkin.find_first_n_motzkins(n)[n - 1]). */
export function motzkin(n: number): bigint {
  if (!Number.isInteger(n) || n < 1) throw new RangeError('motzkin: n must be a positive integer');
  return at(firstMotzkins(n), n - 1);
}

/** Euler zigzag numbers and their analytic continuation for symbolic inputs. */
export function andre(n: Expr | bigint): Expr;
export function andre(n: number): bigint;
export function andre(n: ExprLike): bigint | Expr {
  return typeof n === 'number' ? andreInteger(n) : fn('andre', [n]);
}

function andreInteger(n: number): bigint {
  if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('andre requires a nonnegative safe integer index');
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
export function binomialMod(nIn: IntLike, kIn: IntLike, mIn: IntLike): bigint {
  const [n, k, m] = [intOf(nIn), intOf(kIn), intOf(mIn)];
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

/** Input to the multiset counting functions: a size, a sequence, or item multiplicities. */
export type CountingInput = IntLike | Iterable<unknown> | Map<unknown, IntLike>;

function countSize(n: IntLike): number {
  const size = Number(intOf(n));
  if (!Number.isSafeInteger(size) || size < 0) throw new RangeError('count must be a nonnegative safe integer');
  return size;
}

function histogram(n: CountingInput, identical = false): number[] {
  if (typeof n === 'number' || typeof n === 'bigint' || n instanceof Expr) {
    const size = countSize(n);
    return identical ? [size] : Array<number>(size).fill(1);
  }
  if (n instanceof Map) return [...n.values()].map((v: IntLike) => countSize(v)).filter((v) => v > 0);
  const counts = new Map<string, number>();
  for (const item of n) {
    const key = valueKey(item);
    counts.set(key, (counts.get(key) ?? 0) + 1);
  }
  return [...counts.values()];
}

function selections(n: CountingInput, k: IntLike | undefined, replacement: boolean, ordered: boolean): bigint {
  const counts = histogram(n), total = counts.reduce((a, b) => a + b, 0);
  const degree = k === undefined ? total : countSize(k);
  let row = Array<bigint>(degree + 1).fill(0n);
  row[0] = 1n;
  for (const count of counts) {
    const next = Array<bigint>(degree + 1).fill(0n);
    for (let i = 0; i <= degree; i++) {
      for (let j = 0; j <= Math.min(replacement ? degree : count, degree - i); j++) {
        next[i + j] = at(next, i + j) + at(row, i) * (ordered ? binom(i + j, j) : 1n);
      }
    }
    row = next;
  }
  return k === undefined ? row.reduce((a, b) => a + b, 0n) : at(row, degree);
}

/** Number of combinations of a multiset, optionally allowing replacement. */
export function nC(n: CountingInput, k?: IntLike, opts: { replacement?: boolean } = {}): bigint {
  return selections(n, k, opts.replacement ?? false, false);
}

/** Number of distinct ordered selections of a multiset. */
export function nP(n: CountingInput, k?: IntLike, opts: { replacement?: boolean } = {}): bigint {
  return selections(n, k, opts.replacement ?? false, true);
}

/** Number of derangements; brute is accepted as an algorithm hint. */
export function nD(i?: CountingInput, opts: { brute?: boolean; n?: IntLike; m?: Iterable<IntLike> | Map<IntLike, IntLike> } = {}): bigint {
  if ([i, opts.n, opts.m].filter((v) => v !== undefined).length !== 1) throw new TypeError('supply exactly one of i, n, or m');
  if (i !== undefined && (typeof i === 'number' || typeof i === 'bigint' || i instanceof Expr)) throw new TypeError('items must be a sequence or multiset');
  let counts: number[];
  if (opts.m !== undefined) {
    if (!(Symbol.iterator in Object(opts.m))) throw new TypeError('multiplicities must be iterable');
    counts = opts.m instanceof Map
      ? [...opts.m].flatMap(([m, repeat]: [IntLike, IntLike]) => Array<number>(countSize(repeat)).fill(countSize(m)))
      : Array.from(opts.m, (v) => countSize(v));
  } else counts = histogram(defined(i ?? opts.n));
  if (counts.length > 0 && counts.every((c) => c === 1)) {
    let a = 1n, b = 0n;
    for (let j = 2; j <= counts.length; j++) [a, b] = [b, BigInt(j - 1) * (a + b)];
    return b;
  }
  const original = counts.flatMap((count, index) => Array<number>(count).fill(index));
  if (original.length === 0) return 0n;
  const memo = new Map<string, bigint>();
  function count(position: number): bigint {
    if (position === original.length) return 1n;
    const key = counts.join(',');
    const cached = memo.get(key);
    if (cached !== undefined) return cached;
    let result = 0n;
    for (let j = 0; j < counts.length; j++) {
      const available = at(counts, j);
      if (available === 0 || j === at(original, position)) continue;
      counts[j] = available - 1;
      result += count(position + 1);
      counts[j] = available;
    }
    memo.set(key, result);
    return result;
  }
  return count(0);
}

/** Number of partitions of a multiset; an integer denotes identical items. */
export function nT(n: CountingInput, k?: IntLike): bigint {
  const counts = histogram(n, true).filter((v) => v > 0);
  if (k !== undefined && intOf(k) < 0n) return 0n;
  const parts = k === undefined ? undefined : countSize(k);
  if (counts.length === 0) return parts === undefined || parts === 0 ? 1n : 0n;
  let result = 0n;
  for (const [, lastPart] of multisetPartitionsTaocp(counts)) if (parts === undefined || lastPart + 1 === parts) result++;
  return result;
}

/** Stirling numbers of either kind, including signed and reduced variants. */
export function stirling(nIn: IntLike, kIn: IntLike, d?: IntLike, opts: { kind?: number; signed?: boolean } = {}): bigint {
  const n = countSize(nIn), k = countSize(kIn);
  if (k > n) return 0n;
  if (d !== undefined && intOf(d) !== 0n) {
    const shift = countSize(d) - 1;
    // Singleton blocks satisfy every separation, including the empty partition.
    return k === n ? 1n : k <= shift ? 0n : stirling2(n - shift, k - shift);
  }
  if (opts.signed !== true && opts.kind !== undefined && opts.kind !== 1 && opts.kind !== 2) throw new RangeError('kind must be 1 or 2');
  if (opts.signed !== true && opts.kind !== 1) return stirling2(n, k);
  let row = Array<bigint>(k + 1).fill(0n);
  row[0] = 1n;
  for (let i = 1; i <= n; i++) {
    const next = Array<bigint>(k + 1).fill(0n);
    for (let j = 1; j <= k; j++) next[j] = at(row, j - 1) + BigInt(i - 1) * at(row, j);
    row = next;
  }
  return at(row, k) * (opts.signed === true && (n - k) % 2 === 1 ? -1n : 1n);
}

registerFunctionHeads([
  ['bernoulli', bernoulli],
  ['euler', euler],
  ['genocchi', genocchi],
  ['andre', (n) => fn('andre', [n])],
  ['legendre_symbol', (a, p) => fn('legendre_symbol', [a, p])],
  ['jacobi_symbol', (a, n) => fn('jacobi_symbol', [a, n])],
  ['kronecker_symbol', (a, n) => fn('kronecker_symbol', [a, n])],
  ['fibonacci', fibonacci],
  ['lucas', lucas],
  ['tribonacci', tribonacci],
  ['partition', partition],
  ['totient', totientFn],
  ['reduced_totient', reducedTotient],
  ['mobius', mobius],
  ['divisor_sigma', divisorSigma],
  ['udivisor_sigma', udivisorSigma],
  ['primenu', primenu],
  ['primeomega', primeomega],
  ['primepi', primepiFn],
  ['multigamma', multigamma],
  ['frac', frac],
]);
