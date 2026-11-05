// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Residues modulo n (SymPy sympy.ntheory.residue_ntheory): orders,
 * primitive roots, square and nth roots modulo n, quadratic and nth power
 * residues, discrete logarithms and polynomial congruences (with the
 * solvers of sympy.polys.galoistools it uses: linear_congruence,
 * gf_csolve).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Mul, Pow, Rational, Sym } from '../core/nodes';
import { at, defined, first } from '../core/guard';
import { sympify } from '../core/ops';
import { gcd, lcm } from '../core/numbers';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { factorintInt, perfectPowerInt } from './factor';
import { primerange } from './generate';
import type { IntLike } from './intutil';
import { asInt, babs, bitLength, bitScan1, divmod, fdiv, gcdext, invert, isqrt, jacobi, pmod, powmod, product, pyLog, remove } from './intutil';
import { gfCrt, gfCrt1, gfCrt2 } from './modular';
import { isprime } from './primetest';
import type { RandInt } from './random';
import { randintFrom, rng } from './random';

// the sign of a - b (a huge difference becomes an infinity of the same sign)
const cmpBig = (a: bigint, b: bigint): number => Number(a - b);
const sortBig = (xs: Iterable<bigint>): bigint[] => [...xs].sort(cmpBig);
const factorint = (n: bigint): Map<bigint, bigint> => factorintInt(n, {});

/** The order of a modulo n (SymPy n_order). */
export function nOrder(aIn: IntLike, nIn: IntLike): bigint {
  const n = asInt(nIn);
  if (n <= 1n) throw new RangeError('n should be an integer greater than 1');
  const a = pmod(asInt(aIn), n);
  if (a === 1n) return 1n;
  if (gcd(a, n) !== 1n) throw new RangeError('The two numbers should be relatively prime');
  let aOrder = 1n;
  for (const [p, e] of factorint(n)) {
    const pe = p ** e;
    const peOrder = (p - 1n) * p ** (e - 1n);
    const factors = factorint(p - 1n);
    if (e > 1n) factors.set(p, e - 1n);
    let order = 1n;
    for (const [px, ex] of factors) {
      let x = powmod(a, peOrder / px ** ex, pe);
      while (x !== 1n) {
        x = powmod(x, px, pe);
        order *= px;
      }
    }
    aOrder = lcm(aOrder, order);
  }
  return aOrder;
}

/**
 * The first primitive root of the prime p that SymPy's
 * _primitive_root_prime_iter yields (the smallest one; only the first value
 * of SymPy's generators is ever used).
 */
function primitiveRootPrime(p: bigint): bigint {
  if (p === 3n) return 2n;
  const gMin = p % 8n === 1n || p % 8n === 7n ? 3n : 2n;
  if (p < 41n) return p === 23n ? 5n : gMin;
  const v = [...factorint(p - 1n).keys()].map((i) => (p - 1n) / i);
  let g = gMin;
  while (!v.every((pw) => powmod(g, pw, p) !== 1n)) g++;
  return g;
}

/** The first primitive root of p**e that SymPy's _primitive_root_prime_power_iter yields. */
function primitiveRootPrimePower(p: bigint, e: bigint): bigint {
  const g = primitiveRootPrime(p);
  if (e === 1n) return g;
  const p2 = p * p;
  // the first k in 0, p, 2p, ... other than t
  const t = pmod(g - powmod(g, 2n - p, p2), p2);
  return t === 0n ? g + p : g;
}

/** The first primitive root of 2*p**e that SymPy's _primitive_root_prime_power2_iter yields. */
function primitiveRootPrimePower2(p: bigint, e: bigint): bigint {
  const g = primitiveRootPrimePower(p, e);
  return g % 2n === 1n ? g : g + p ** e;
}

/**
 * The smallest primitive root of p, or with `{ smallest: false }` one
 * found more quickly (SymPy primitive_root); NoMatch when none exists.
 */
export function primitiveRoot(pIn: IntLike, opts: { smallest?: boolean } = {}): bigint | NoMatchResult {
  const smallest = opts.smallest ?? true;
  const p = asInt(pIn);
  if (p <= 1n) throw new RangeError('p should be an integer greater than 1');
  if (p <= 4n) return p - 1n;
  const pEven = p % 2n === 0n;
  let q: bigint;
  if (!pEven) q = p;
  else if (p % 4n !== 0n) q = p / 2n;
  else return NoMatch;
  let e = 1n;
  if (!isprime(q)) {
    const m = perfectPowerInt(q, 3n);
    if (m === false) return NoMatch;
    [q, e] = m;
    if (!isprime(q)) return NoMatch;
  }
  if (!smallest) {
    return pEven ? primitiveRootPrimePower2(q, e) : primitiveRootPrimePower(q, e);
  }
  if (pEven) return smallestPrimitiveRoot(3n, 2n, p, q);
  const g = primitiveRootPrime(q);
  if (e === 1n || powmod(g, q - 1n, q * q) !== 1n) return g;
  return smallestPrimitiveRoot(g + 1n, 1n, p, q);
}

/** The first i = start, start + step, ... prime to q that is a primitive root of p (one exists below p). */
function smallestPrimitiveRoot(start: bigint, step: bigint, p: bigint, q: bigint): bigint {
  for (let i = start; ; i += step) if (i % q !== 0n && isPrimitiveRoot(i, p)) return i;
}

/** a is a primitive root of p (SymPy is_primitive_root). */
export function isPrimitiveRoot(aIn: IntLike, pIn: IntLike): boolean {
  const p = asInt(pIn);
  if (p <= 1n) throw new RangeError('p should be an integer greater than 1');
  const a = pmod(asInt(aIn), p);
  if (gcd(a, p) !== 1n) throw new RangeError('The two numbers should be relatively prime');
  if (p <= 4n) return a === p - 1n;
  let q: bigint;
  if (p % 2n !== 0n) q = p;
  else if (p % 4n !== 0n) q = p / 2n;
  else return false;
  let groupOrder: bigint;
  let factors: bigint[];
  if (isprime(q)) {
    groupOrder = q - 1n;
    factors = [...factorint(q - 1n).keys()];
  } else {
    const m = perfectPowerInt(q, 3n);
    if (m === false) return false;
    const [q2, e] = m;
    if (!isprime(q2)) return false;
    groupOrder = q2 ** (e - 1n) * (q2 - 1n);
    factors = [...new Set([...factorint(q2 - 1n).keys(), q2])];
  }
  return factors.every((pr) => powmod(a, groupOrder / pr, p) !== 1n);
}

// ---------------------------------------------------------------------------
// square roots
// ---------------------------------------------------------------------------

function sqrtModTonelliShanks(a: bigint, p: bigint): bigint {
  const s = bitScan1(p - 1n);
  const t = p >> BigInt(s);
  let d: bigint;
  if (p % 12n === 5n) d = 3n;
  else if (p % 5n === 2n || p % 5n === 3n) d = 5n;
  else {
    for (;;) {
      d = rng.randint(6n, p - 1n);
      if (jacobi(d, p) === -1) break;
    }
  }
  const A = powmod(a, t, p);
  const D = powmod(d, t, p);
  let m = 0n;
  for (let i = 0; i < s; i++) {
    let adm = (A * powmod(D, m, p)) % p;
    adm = powmod(adm, 2n ** BigInt(s - 1 - i), p);
    if (adm % p === p - 1n) m += 2n ** BigInt(i);
  }
  return (powmod(a, (t + 1n) / 2n, p) * powmod(D, m / 2n, p)) % p;
}

/** @internal The square roots of a modulo p**k for gcd(a, p) = 1, sorted, or undefined (SymPy _sqrt_mod_prime_power). */
export function sqrtModPrimePower(aIn: bigint, p: bigint, k: bigint): bigint[] | undefined {
  const pk = p ** k;
  const a = pmod(aIn, pk);
  if (p === 2n) {
    if (a % 8n !== 1n) return undefined;
    if (k <= 3n) {
      const out: bigint[] = [];
      for (let i = 1n; i < pk; i += 2n) out.push(i);
      return out;
    }
    let r = 1n;
    for (let nx = 3n; nx < k; nx++) if (((r * r - a) >> nx) & 1n) r += 1n << (nx - 1n);
    const h = 1n << (k - 1n);
    return sortBig([r, pk - r, pmod(r + h, pk), pmod(-(r + h), pk)]);
  }
  if (jacobi(a, p) !== 1) return undefined;
  let res: bigint;
  if (p % 4n === 3n) res = powmod(a, (p + 1n) / 4n, p);
  else if (p % 8n === 5n) {
    res = powmod(a, (p + 3n) / 8n, p);
    if (powmod(res, 2n, p) !== a % p) res = (res * powmod(2n, (p - 1n) / 4n, p)) % p;
  } else res = sqrtModTonelliShanks(a, p);
  if (k > 1n) {
    let px = p;
    for (let i = 0; i < bitLength(k) - 1; i++) {
      px = px * px;
      const frinv = invert(2n * res, px);
      res = pmod(res - (res * res - a) * frinv, px);
    }
    if ((k & (k - 1n)) !== 0n) {
      const frinv = invert(2n * res, pk);
      res = pmod(res - (res * res - a) * frinv, pk);
    }
  }
  return sortBig([res, pk - res]);
}

function sqrtMod1(aIn: bigint, p: bigint, n: bigint): bigint[] | undefined {
  const pn = p ** n;
  let a = pmod(aIn, pn);
  if (a === 0n) {
    const out: bigint[] = [];
    const st = p ** ((n + 1n) / 2n);
    for (let i = 0n; i < pn; i += st) out.push(i);
    return out;
  }
  let r: bigint;
  [a, r] = remove(a, p);
  if (r % 2n === 1n) return undefined;
  const res = sqrtModPrimePower(a, p, n - r);
  if (res === undefined) return undefined;
  const m = r / 2n;
  const out: bigint[] = [];
  for (const rx of res) for (let x = rx * p ** m; x < pn; x += p ** (n - m)) out.push(x);
  return out;
}

function* iproduct2<A, B>(it1: Iterator<A>, it2: Iterator<B>): Generator<[A, B], void, undefined> {
  const e1: A[] = [];
  const e2: B[] = [];
  const append = <T>(it: Iterator<T>, elems: T[]): void => {
    const r = it.next();
    if (r.done !== true) elems.push(r.value);
  };
  let n = 0;
  append(it1, e1);
  append(it2, e2);
  while (n <= e1.length + e2.length) {
    for (let m = n - e1.length + 1; m < e2.length; m++) yield [at(e1, n - m), at(e2, m)];
    n++;
    append(it1, e1);
    append(it2, e2);
  }
}

/** The singletons [e] of the elements of xs. */
function* singletons<T>(xs: readonly T[]): Generator<T[], void, undefined> {
  for (const e of xs) yield [e];
}

/** SymPy iproduct for two or more lists: the Cartesian product in diagonal order. */
function* iproduct<T>(lists: readonly (readonly T[])[]): Generator<T[], void, undefined> {
  const tail = lists.length === 2 ? singletons(at(lists, 1)) : iproduct(lists.slice(1));
  for (const [ef, eo] of iproduct2(first(lists)[Symbol.iterator](), tail)) yield [ef, ...eo];
}

/** The square roots of a modulo p, in SymPy's order (SymPy sqrt_mod_iter). */
export function* sqrtModIter(aIn: IntLike, pIn: IntLike): Generator<bigint, void, undefined> {
  const a = asInt(aIn);
  const p = babs(asInt(pIn));
  const v: bigint[][] = [];
  const pv: bigint[] = [];
  let diag = false;
  for (const [px, ex] of factorint(p)) {
    let rx: bigint[] | undefined;
    if (a % px !== 0n) rx = sqrtModPrimePower(a, px, ex);
    else {
      rx = sqrtMod1(a, px, ex);
      diag = true;
    }
    if (rx === undefined || rx.length === 0) return;
    v.push(rx);
    pv.push(px ** ex);
  }
  if (v.length === 1) {
    yield* first(v);
    return;
  }
  const [mm, e, s] = gfCrt1(pv);
  for (const vx of diag ? iproduct(v) : product(v)) yield gfCrt2(vx, pv, mm, e, s);
}

/**
 * A square root of a modulo p, the smallest one not above p/2, or NoMatch
 * (SymPy sqrt_mod); with `allRoots`, the sorted list of all roots.
 */
export function sqrtMod(a: IntLike, p: IntLike, allRoots: true): bigint[];
export function sqrtMod(a: IntLike, p: IntLike, allRoots?: false): bigint | NoMatchResult;
export function sqrtMod(a: IntLike, pIn: IntLike, allRoots = false): bigint | NoMatchResult | bigint[] {
  if (allRoots) return sortBig(sqrtModIter(a, pIn));
  const p = babs(asInt(pIn));
  const halfp = p / 2n;
  let x: bigint | NoMatchResult = NoMatch;
  for (const r of sqrtModIter(a, p)) {
    if (r < halfp) return r;
    if (r > halfp) return p - r;
    x = r;
  }
  return x;
}

/** a is a quadratic residue modulo p (SymPy is_quad_residue). */
export function isQuadResidue(aIn: IntLike, pIn: IntLike): boolean {
  let p = asInt(pIn);
  if (p < 1n) throw new RangeError('p must be > 0');
  let a = pmod(asInt(aIn), p);
  if (a < 2n || p < 3n) return true;
  const t = bitScan1(p);
  if (t) {
    const a2 = a % (1n << BigInt(t));
    if (a2) {
      const r = bitScan1(a2);
      if (r % 2 || (a2 >> BigInt(r)) & 6n) return false;
    }
    p >>= BigInt(t);
    a %= p;
    if (a < 2n || p < 3n) return true;
  }
  const j = jacobi(a, p);
  if (j === -1 || isprime(p)) return j === 1;
  for (const [px, ex] of factorint(p)) {
    if (a % px) {
      if (jacobi(a, px) !== 1) return false;
    } else {
      let a2 = a % px ** ex;
      if (a2 === 0n) continue;
      let r: bigint;
      [a2, r] = remove(a2, px);
      if (r % 2n || jacobi(a2, px) !== 1) return false;
    }
  }
  return true;
}

function isNthpowResidueBignPrimePower(aIn: bigint, n: bigint, p: bigint, kIn: bigint): boolean {
  let a = aIn;
  let k = kIn;
  while (a % p === 0n) {
    a %= p ** k;
    if (!a) return true;
    let mu: bigint;
    [a, mu] = remove(a, p);
    if (mu % n) return false;
    k -= mu;
  }
  if (p !== 2n) {
    const f = p ** (k - 1n) * (p - 1n);
    return powmod(a, f / gcd(f, n), p ** k) === 1n;
  }
  if (n & 1n) return true;
  const c0 = BigInt(bitScan1(n) + 2);
  const c = c0 < k ? c0 : k;
  return pmod(a, 2n ** c) === 1n;
}

/** a is an nth power residue modulo m (SymPy is_nthpow_residue). */
export function isNthpowResidue(aIn: IntLike, nIn: IntLike, mIn: IntLike): boolean {
  const m = asInt(mIn);
  const n = asInt(nIn);
  if (m <= 0n) throw new RangeError('m must be > 0');
  if (n < 0n) throw new RangeError('n must be >= 0');
  const a = pmod(asInt(aIn), m);
  if (n === 0n) return m === 1n ? false : a === 1n;
  if (a === 0n) return true;
  if (n === 1n) return true;
  if (n === 2n) return isQuadResidue(a, m);
  for (const [p, e] of factorint(m)) if (!isNthpowResidueBignPrimePower(a, n, p, e)) return false;
  return true;
}

function nthrootMod1(s: bigint, q: bigint, p: bigint): bigint[] {
  const g = primitiveRootPrime(p);
  let r = s;
  for (const [qx, ex] of factorint(q)) {
    let f = (p - 1n) / qx ** ex;
    while (f % qx === 0n) f /= qx;
    const z = f * invert(-f, qx);
    const x = (1n + z) / qx;
    let t = discreteLog(p, powmod(r, f, p), powmod(g, f * qx, p));
    for (let i = 0n; i < ex; i++) {
      r = (powmod(r, x, p) * powmod(g, pmod(-z * t, p - 1n), p)) % p;
      t /= qx;
    }
  }
  const res = [r];
  const h = powmod(g, (p - 1n) / q, p);
  let hx = r;
  for (let i = 0n; i < q - 1n; i++) {
    hx = (hx * h) % p;
    res.push(hx);
  }
  return sortBig(res);
}

function nthrootModPrimePower(aIn: bigint, n: bigint, p: bigint, k: bigint): bigint[] {
  let a = aIn;
  if (!isNthpowResidueBignPrimePower(a, n, p, k)) return [];
  let aModP = a % p;
  let baseRoots: bigint[];
  if (aModP === 0n) baseRoots = [0n];
  else if ((p - 1n) % n === 0n) baseRoots = nthrootMod1(aModP, n, p);
  else {
    let pa = n;
    let pb = p - 1n;
    let b = 1n;
    if (pa < pb) [aModP, pa, b, pb] = [b, pb, aModP, pa];
    while (pb) {
      const [q, pc] = divmod(pa, pb);
      const c = (powmod(b, -q, p) * aModP) % p;
      [pa, pb] = [pb, pc];
      [aModP, b] = [b, c];
    }
    if (pa === 1n) baseRoots = [aModP];
    else if (pa === 2n) baseRoots = sqrtMod(aModP, p, true);
    else baseRoots = nthrootMod1(aModP, pa, p);
  }
  if (k === 1n) return baseRoots;
  a %= p ** k;
  const tot = new Set<bigint>();
  for (const root0 of baseRoots) {
    let root = root0;
    const diff = (powmod(root, n - 1n, p) * n) % p;
    let newBase = p;
    if (diff !== 0n) {
      const mInv = invert(diff, p);
      for (let i = 1n; i < k; i++) {
        newBase *= p;
        const tmp = (powmod(root, n, newBase) - a) * mInv;
        root = pmod(root - tmp, newBase);
      }
      tot.add(root);
    } else {
      let rootsInBase = new Set<bigint>([root]);
      for (let i = 1n; i < k; i++) {
        newBase *= p;
        const newRoots = new Set<bigint>();
        for (const k0 of rootsInBase) {
          let kk = k0;
          if (powmod(kk, n, newBase) !== a % newBase) continue;
          while (!newRoots.has(kk)) {
            newRoots.add(kk);
            kk = (kk + newBase / p) % newBase;
          }
        }
        rootsInBase = newRoots;
      }
      for (const r of rootsInBase) tot.add(r);
    }
  }
  return sortBig(tot);
}

/**
 * The smallest solution x of x**n = a (mod p), or NoMatch (SymPy
 * nthroot_mod); with `allRoots`, the sorted list of all solutions.
 */
export function nthrootMod(a: IntLike, n: IntLike, p: IntLike, allRoots: true): bigint[];
export function nthrootMod(a: IntLike, n: IntLike, p: IntLike, allRoots?: false): bigint | NoMatchResult;
export function nthrootMod(aIn: IntLike, nIn: IntLike, pIn: IntLike, allRoots = false): bigint | NoMatchResult | bigint[] {
  const p = asInt(pIn);
  const n = asInt(nIn);
  if (n < 1n) throw new RangeError('n should be positive');
  if (p < 1n) throw new RangeError('p should be positive');
  const a = pmod(asInt(aIn), p);
  if (n === 1n) return allRoots ? [a] : a;
  if (n === 2n) return allRoots ? sqrtMod(a, p, true) : sqrtMod(a, p);
  const base: bigint[][] = [];
  const primePower: bigint[] = [];
  for (const [q, e] of factorint(p)) {
    const roots = nthrootModPrimePower(a, n, q, e);
    if (roots.length === 0) return allRoots ? [] : NoMatch;
    primePower.push(q ** e);
    base.push(sortBig(roots));
  }
  const [P, E, S] = gfCrt1(primePower);
  const ret = sortBig(new Set([...product(base)].map((c) => gfCrt2(c, primePower, P, E, S))));
  if (allRoots) return ret;
  // every prime power has a root, so the product is not empty
  return first(ret);
}

/** The sorted list of quadratic residues modulo p (SymPy quadratic_residues). */
export function quadraticResidues(pIn: IntLike): bigint[] {
  const p = asInt(pIn);
  const r = new Set<bigint>();
  for (let i = 0n; i <= p / 2n; i++) r.add(powmod(i, 2n, p));
  return sortBig(r);
}

// ---------------------------------------------------------------------------
// discrete logarithms
// ---------------------------------------------------------------------------

const noLog = (): never => {
  throw new RangeError('Log does not exist');
};

function dlogTrialMul(n: bigint, aIn: bigint, bIn: bigint, order: bigint): bigint {
  const a = pmod(aIn, n);
  const b = pmod(bIn, n);
  let x = 1n;
  for (let i = 0n; i < order; i++) {
    if (x === a) return i;
    x = (x * b) % n;
  }
  return noLog();
}

function dlogShanks(n: bigint, aIn: bigint, bIn: bigint, order: bigint): bigint {
  const a = pmod(aIn, n);
  const b = pmod(bIn, n);
  const m = isqrt(order) + 1n;
  const T = new Map<bigint, bigint>();
  let x = 1n;
  for (let i = 0n; i < m; i++) {
    T.set(x, i);
    x = (x * b) % n;
  }
  const z = powmod(b, -m, n);
  x = a;
  for (let i = 0n; i < m; i++) {
    const t = T.get(x);
    if (t !== undefined) return i * m + t;
    x = (x * z) % n;
  }
  return noLog();
}

/** @internal Pollard's rho discrete logarithm (SymPy _discrete_log_pollard_rho). */
export function dlogPollardRho(n: bigint, aIn: bigint, bIn: bigint, order: bigint, retries = 10, rseed?: bigint): bigint {
  const a = pmod(aIn, n);
  const b = pmod(bIn, n);
  const randint: RandInt = randintFrom(rseed);
  for (let i = 0; i < retries; i++) {
    let aa = randint(1n, order - 1n);
    let ba = randint(1n, order - 1n);
    let xa = (powmod(b, aa, n) * powmod(a, ba, n)) % n;
    let xb: bigint;
    let ab: bigint;
    let bb: bigint;
    const c0 = xa % 3n;
    if (c0 === 0n) {
      xb = (a * xa) % n;
      ab = aa;
      bb = (ba + 1n) % order;
    } else if (c0 === 1n) {
      xb = (xa * xa) % n;
      ab = (aa + aa) % order;
      bb = (ba + ba) % order;
    } else {
      xb = (b * xa) % n;
      ab = (aa + 1n) % order;
      bb = ba;
    }
    for (let j = 0n; j < order; j++) {
      let c = xa % 3n;
      if (c === 0n) {
        xa = (a * xa) % n;
        ba = (ba + 1n) % order;
      } else if (c === 1n) {
        xa = (xa * xa) % n;
        aa = (aa + aa) % order;
        ba = (ba + ba) % order;
      } else {
        xa = (b * xa) % n;
        aa = (aa + 1n) % order;
      }
      for (let rep = 0; rep < 2; rep++) {
        c = xb % 3n;
        if (c === 0n) {
          xb = (a * xb) % n;
          bb = (bb + 1n) % order;
        } else if (c === 1n) {
          xb = (xb * xb) % n;
          ab = (ab + ab) % order;
          bb = (bb + bb) % order;
        } else {
          xb = (b * xb) % n;
          ab = (ab + 1n) % order;
        }
      }
      if (xa === xb) {
        const r = pmod(ba - bb, order);
        try {
          const e = pmod(invert(r, order) * (ab - aa), order);
          if (pmod(powmod(b, e, n) - a, n) === 0n) return e;
        } catch {
          // no inverse: retry
        }
        break;
      }
    }
  }
  throw new RangeError("Pollard's Rho failed to find logarithm");
}

function dlogIsSmooth(nIn: bigint, factorbase: readonly bigint[]): bigint[] | undefined {
  let n = nIn;
  const factors = factorbase.map(() => 0n);
  factorbase.forEach((p, i) => {
    while (n % p === 0n) {
      factors[i] = at(factors, i) + 1n;
      n /= p;
    }
  });
  return n === 1n ? factors : undefined;
}

/** @internal The index calculus discrete logarithm (SymPy _discrete_log_index_calculus). */
export function dlogIndexCalculus(n: bigint, aIn: bigint, bIn: bigint, order: bigint, rseed?: bigint): bigint {
  const randint = randintFrom(rseed);
  const a = pmod(aIn, n);
  const b = pmod(bIn, n);
  const ln = pyLog(n);
  const B = BigInt(Math.floor(Math.exp(0.5 * Math.sqrt(ln * Math.log(ln)) * (1 + 1 / Math.log(ln)))));
  const max = 5n * B * B;
  const factorbase = [...primerange(B)];
  const lf = factorbase.length;
  const ordermo = order - 1n;
  let abx = a;
  let relationa: bigint[] | undefined;
  for (let x = 0n; x < order; x++) {
    if (abx === 1n) return pmod(order - x, order);
    const ra = dlogIsSmooth(abx, factorbase);
    if (ra !== undefined) {
      relationa = [...ra.map((r) => pmod(r, order)), x];
      break;
    }
    abx = (abx * b) % n;
  }
  if (relationa === undefined) throw new RangeError('Index Calculus failed');
  const relations: (bigint[] | undefined)[] = new Array<bigint[] | undefined>(lf).fill(undefined);
  let k = 1;
  let kk = 0n;
  while (k < 3 * lf && kk < max) {
    const x = randint(1n, ordermo);
    const rel0 = dlogIsSmooth(powmod(b, x, n), factorbase);
    if (rel0 === undefined) {
      kk++;
      continue;
    }
    k++;
    kk = 0n;
    const relation = [...rel0, x];
    let index = lf;
    for (let i = 0; i < lf; i++) {
      const ri = pmod(at(relation, i), order);
      const reli = relations[i];
      if (ri > 0n && reli !== undefined) for (let j = 0; j <= lf; j++) relation[j] = pmod(at(relation, j) - ri * at(reli, j), order);
      else relation[i] = ri;
      if (at(relation, i) > 0n && index === lf) index = i;
    }
    if (index === lf || relations[index] !== undefined) continue;
    const rinv = invert(at(relation, index), order);
    for (let j = index; j <= lf; j++) relation[j] = (rinv * at(relation, j)) % order;
    relations[index] = relation;
    let broke = false;
    for (let i = 0; i < lf; i++) {
      const reli = relations[i];
      if (at(relationa, i) > 0n && reli !== undefined) {
        const rbi = at(relationa, i);
        for (let j = 0; j <= lf; j++) relationa[j] = pmod(at(relationa, j) - rbi * at(reli, j), order);
      }
      if (at(relationa, i) > 0n) {
        broke = true;
        break;
      }
    }
    if (!broke) {
      const x2 = pmod(order - at(relationa, lf), order);
      if (powmod(b, x2, n) === a) return x2;
      throw new RangeError('Index Calculus failed');
    }
  }
  throw new RangeError('Index Calculus failed');
}

function dlogPohligHellman(n: bigint, aIn: bigint, bIn: bigint, order: bigint, orderFactors?: Map<bigint, bigint>): bigint {
  const a = pmod(aIn, n);
  const b = pmod(bIn, n);
  const of = orderFactors ?? factorint(order);
  const l: bigint[] = [];
  for (const [pi, ri] of of) {
    let li = 0n;
    for (let j = 0n; j < ri; j++) {
      const aj = powmod(a * powmod(b, -li, n), order / pi ** (j + 1n), n);
      const bj = powmod(b, order / pi, n);
      const cj = discreteLog(n, aj, bj, pi, true);
      li += cj * pi ** j;
    }
    l.push(li);
  }
  // the moduli are coprime, so the remainders always combine
  return gfCrt(
    l,
    [...of].map(([pi, ri]) => pi ** ri),
  );
}

/**
 * The discrete logarithm x with b**x = a (mod n) (SymPy discrete_log):
 * trial multiplication, Shanks' baby-step giant-step, Pollard's rho, the
 * index calculus or Pohlig-Hellman depending on the order of b. Throws a
 * RangeError when the logarithm does not exist.
 */
export function discreteLog(nIn: IntLike, aIn: IntLike, bIn: IntLike, orderIn?: IntLike, primeOrderIn?: boolean): bigint {
  const n = asInt(nIn);
  const a = asInt(aIn);
  const b = asInt(bIn);
  if (n < 1n) throw new RangeError('n should be positive');
  if (n === 1n) return 0n;
  let order: bigint;
  let orderFactors: Map<bigint, bigint> | undefined;
  if (orderIn === undefined) {
    const factors = new Map<bigint, bigint>();
    for (const [px, kx] of factorint(n)) {
      if (kx > 1n) factors.set(px, (factors.get(px) ?? 0n) + kx - 1n);
      for (const [py, ky] of factorint(px - 1n)) factors.set(py, (factors.get(py) ?? 0n) + ky);
    }
    order = 1n;
    for (const [px, kx] of factors) order *= px ** kx;
    orderFactors = new Map();
    for (const [p, e] of factors) {
      let i = 0n;
      for (let t = 0n; t < e; t++) {
        if (powmod(b, order / p, n) === 1n) {
          order /= p;
          i++;
        } else break;
      }
      if (i < e) orderFactors.set(p, e - i);
    }
  } else order = asInt(orderIn);
  const primeOrder = primeOrderIn ?? isprime(order);
  if (order < 1000n) return dlogTrialMul(n, a, b, order);
  if (primeOrder) {
    const ln = pyLog(n);
    if (4 * Math.sqrt(ln * Math.log(ln)) < pyLog(order) - 10) return dlogIndexCalculus(n, a, b, order);
    if (order < 1000000000000n) return dlogShanks(n, a, b, order);
    return dlogPollardRho(n, a, b, order);
  }
  return dlogPohligHellman(n, a, b, order, orderFactors);
}

// ---------------------------------------------------------------------------
// congruences
// ---------------------------------------------------------------------------

/** The solutions of a*x = b (mod m) (SymPy galoistools linear_congruence). */
export function linearCongruence(aIn: IntLike, bIn: IntLike, mIn: IntLike): bigint[] {
  const a = asInt(aIn);
  const b = asInt(bIn);
  const m = asInt(mIn);
  if (pmod(a, m) === 0n) {
    if (pmod(b, m) === 0n) {
      const out: bigint[] = [];
      for (let i = 0n; i < m; i++) out.push(i);
      return out;
    }
    return [];
  }
  const [g, r] = gcdext(a, m);
  if (pmod(b, g) !== 0n) return [];
  const out: bigint[] = [];
  for (let t = 0n; t < g; t++) out.push(pmod(fdiv(r * b, g) + fdiv(t * m, g), m));
  return out;
}

/** The solutions of a*x**2 + b*x + c = 0 (mod n), sorted (SymPy quadratic_congruence). */
export function quadraticCongruence(aIn: IntLike, bIn: IntLike, cIn: IntLike, nIn: IntLike): bigint[] {
  const n = asInt(nIn);
  if (n <= 1n) throw new RangeError('n should be an integer greater than 1');
  const a = pmod(asInt(aIn), n);
  let b = pmod(asInt(bIn), n);
  let c = pmod(asInt(cIn), n);
  if (a === 0n) return linearCongruence(b, -c, n);
  if (n === 2n) {
    const roots: bigint[] = [];
    if (c === 0n) roots.push(0n);
    if ((b + c) % 2n) roots.push(1n);
    return roots;
  }
  if (gcd(2n * a, n) === 1n) {
    const invA = invert(a, n);
    b *= invA;
    c *= invA;
    if (b % 2n) b += n;
    b >>= 1n;
    return sortBig([...sqrtModIter(b * b - c, n)].map((i) => pmod(i - b, n)));
  }
  const res = new Set<bigint>();
  for (const i of sqrtModIter(b * b - 4n * a * c, 4n * a * n)) {
    const [q, rem] = divmod(i - b, 2n * a);
    if (rem === 0n) res.add(pmod(q, n));
  }
  return sortBig(res);
}

// dense polynomials over GF(p), coefficients from the leading one

const gfStrip = (f: bigint[]): bigint[] => {
  let i = 0;
  while (i < f.length && f[i] === 0n) i++;
  return f.slice(i);
};
const gfTrunc = (f: readonly bigint[], p: bigint): bigint[] => gfStrip(f.map((c) => pmod(c, p)));

function gfMul(f: readonly bigint[], g: readonly bigint[], p: bigint): bigint[] {
  if (f.length === 0 || g.length === 0) return [];
  const out = new Array<bigint>(f.length + g.length - 1).fill(0n);
  f.forEach((a, i) => g.forEach((b, j) => (out[i + j] = at(out, i + j) + a * b)));
  return gfTrunc(out, p);
}

function gfDiv(f: readonly bigint[], g: readonly bigint[], p: bigint): [bigint[], bigint[]] {
  if (f.length < g.length) return [[], [...f]];
  const inv = invert(at(g, 0), p);
  const r = [...f];
  const q: bigint[] = [];
  for (let i = 0; i <= f.length - g.length; i++) {
    const c = pmod(at(r, i) * inv, p);
    q.push(c);
    if (c !== 0n) for (let j = 0; j < g.length; j++) r[i + j] = pmod(at(r, i + j) - c * at(g, j), p);
  }
  return [gfStrip(q), gfStrip(r.slice(f.length - g.length + 1))];
}

function gfPowMod(f: readonly bigint[], nIn: bigint, g: readonly bigint[], p: bigint): bigint[] {
  let n = nIn;
  let h: bigint[] = [1n];
  let b = gfDiv(f, g, p)[1];
  while (n > 0n) {
    if (n & 1n) h = gfDiv(gfMul(h, b, p), g, p)[1];
    n >>= 1n;
    if (n > 0n) b = gfDiv(gfMul(b, b, p), g, p)[1];
  }
  return h;
}

function gfGcd(fIn: readonly bigint[], gIn: readonly bigint[], p: bigint): bigint[] {
  let f = [...fIn];
  let g = [...gIn];
  // f is not zero: the callers pass a nonzero first polynomial
  while (g.length > 0) [f, g] = [g, gfDiv(f, g, p)[1]];
  const inv = invert(at(f, 0), p);
  return f.map((c) => pmod(c * inv, p));
}

/** f - 1 over GF(p), p >= 2. */
function gfSubOne(f: readonly bigint[], p: bigint): bigint[] {
  if (f.length === 0) return [p - 1n];
  const r = pmod(at(f, f.length - 1) - 1n, p);
  if (f.length > 1) return [...f.slice(0, -1), r];
  return r ? [r] : [];
}

function gfEval(f: readonly bigint[], a: bigint, p: bigint): bigint {
  let r = 0n;
  for (const c of f) r = pmod(r * a + c, p);
  return r;
}

const gfValue = (f: readonly bigint[], a: bigint): bigint => f.reduce((r, c) => r * a + c, 0n);

function gfDiff(f: readonly bigint[], p: bigint): bigint[] {
  const df = f.length - 1;
  if (df <= 0) return [];
  const h = new Array<bigint>(df).fill(0n);
  let n = BigInt(df);
  for (const c0 of f.slice(0, -1)) {
    const c = pmod(c0 * n, p);
    if (c) h[df - Number(n)] = c;
    n--;
  }
  return gfStrip(h);
}

function csolvePrimeLasVegas(fIn: readonly bigint[], p: bigint): bigint[] {
  const root = new Set<bigint>();
  let g = gfPowMod([1n, 0n], p - 1n, fIn, p);
  g = gfSubOne(g, p);
  const factors = [gfGcd(fIn, g, p)];
  while (factors.length > 0) {
    const f = defined(factors.pop(), 'polynomial factor');
    if (f.length <= 1) continue;
    if (f.length === 2) {
      root.add(pmod(-invert(at(f, 0), p) * at(f, 1), p));
      continue;
    }
    if (f.length === 3) {
      const inv = invert(at(f, 0), p);
      let b = (at(f, 1) * inv) % p;
      b = (b + p * (b % 2n)) / 2n;
      for (const r of sqrtMod(b * b - at(f, 2) * inv, p, true)) root.add(pmod(r - b, p));
      continue;
    }
    for (;;) {
      const a = rng.randint(0n, p - 1n);
      let h = gfPowMod([1n, a], (p - 1n) / 2n, f, p);
      h = gfSubOne(h, p);
      h = gfGcd(f, h, p);
      if (1 < h.length && h.length < f.length) {
        factors.push(h);
        factors.push(gfDiv(f, h, p)[0]);
        break;
      }
    }
  }
  return sortBig(root);
}

function raiseModPower(x: bigint, s: bigint, p: bigint, f: readonly bigint[]): bigint[] {
  const alpha = gfValue(gfDiff(f, p), x);
  const beta = fdiv(-gfValue(f, x), p ** s);
  return linearCongruence(alpha, beta, p);
}

function csolvePrimeInt(f: readonly bigint[], p: bigint, e: bigint): bigint[] {
  const g0 = [...f];
  const pn = Number(p);
  for (let i = 0; i < g0.length - pn; i++) {
    g0[i + pn - 1] = at(g0, i + pn - 1) + at(g0, i);
    g0[i] = 0n;
  }
  let g = gfTrunc(g0, p);
  let k = 0;
  while (k < g.length && g[g.length - k - 1] === 0n) k++;
  const rootZero: bigint[] = [];
  if (k) {
    g = g.slice(0, -k);
    rootZero.push(0n);
  }
  let X1: bigint[];
  if (g.length === 0) {
    X1 = [];
    for (let i = 0n; i < p; i++) X1.push(i);
  } else if (BigInt(g.length * g.length) < p) X1 = [...rootZero, ...csolvePrimeLasVegas(g, p)];
  else {
    X1 = [...rootZero];
    for (let i = 0n; i < p; i++) if (gfEval(g, i, p) === 0n) X1.push(i);
  }
  if (e === 1n) return X1;
  const X: bigint[] = [];
  const S: [bigint, bigint][] = X1.map((x) => [x, 1n]);
  while (S.length > 0) {
    const [x, s] = defined(S.pop(), 'lifting stack entry');
    if (s === e) X.push(x);
    else {
      const ps = p ** s;
      for (const v of raiseModPower(x, s, p, f)) S.push([x + v * ps, s + 1n]);
    }
  }
  return sortBig(X);
}

/**
 * The roots of the polynomial with integer coefficients f (leading first)
 * modulo p**e for a prime p (SymPy csolve_prime of sympy.polys.galoistools;
 * kept here because gf_csolve, which ntheory uses, is built on it).
 */
export function csolvePrime(f: readonly IntLike[], p: IntLike, e: IntLike = 1n): bigint[] {
  return csolvePrimeInt(f.map((c) => asInt(c)), asInt(p), asInt(e));
}

/** The roots of the polynomial with coefficients f (leading first) modulo n (SymPy gf_csolve). */
export function gfCsolve(f: readonly IntLike[], nIn: IntLike): bigint[] {
  const n = asInt(nIn);
  const fs = f.map((c) => asInt(c));
  const P = factorint(n);
  const X = [...P].map(([p, e]) => csolvePrimeInt(fs, p, e));
  const dist = [...P].map(([p, e]) => p ** e);
  return sortBig([...product(X)].map((per) => gfCrt(per, dist)));
}

/** The integer coefficients of a univariate polynomial expression, leading first. */
function polyCoeffs(exprIn: ExprLike): bigint[] {
  const e = sympify(exprIn).expand();
  const terms = e instanceof Add ? e.args : [e];
  const coeffs = new Map<number, bigint>();
  let gen: string | undefined;
  const genOf = (x: Expr): void => {
    if (!(x instanceof Sym)) throw new RangeError('The expression should be a polynomial');
    if (gen !== undefined && gen !== x.key) throw new RangeError('The expression should be univariate');
    gen = x.key;
  };
  for (const t of terms) {
    let c = 1n;
    let deg = 0;
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Rational) {
        if (f.q !== 1n) throw new RangeError('The expression should should have integer coefficients');
        c *= f.p;
      } else if (f instanceof Pow && f.exp instanceof Rational && f.exp.q === 1n && f.exp.p > 0n) {
        genOf(f.base);
        deg += Number(f.exp.p);
      } else {
        genOf(f);
        deg += 1;
      }
    }
    coeffs.set(deg, (coeffs.get(deg) ?? 0n) + c);
  }
  if (gen === undefined) throw new RangeError('The expression should be univariate');
  const degs = [...coeffs.keys()].filter((d) => coeffs.get(d) !== 0n);
  const top = Math.max(0, ...degs);
  const out: bigint[] = [];
  for (let d = top; d >= 0; d--) out.push(coeffs.get(d) ?? 0n);
  return out;
}

/** The solutions of the polynomial congruence expr = 0 (mod m), sorted (SymPy polynomial_congruence). */
export function polynomialCongruence(expr: ExprLike, mIn: IntLike): bigint[] {
  const m = asInt(mIn);
  const coefficients = polyCoeffs(expr).map((c) => pmod(c, m));
  const rank = coefficients.length;
  if (rank === 3) return quadraticCongruence(at(coefficients, 0), at(coefficients, 1), at(coefficients, 2), m);
  if (rank === 2) return quadraticCongruence(0n, at(coefficients, 0), at(coefficients, 1), m);
  const last = at(coefficients, rank - 1);
  if (coefficients[0] === 1n && 1n + last === coefficients.reduce((s, c) => s + c, 0n)) return nthrootMod(-last, rank - 1, m, true);
  return gfCsolve(coefficients, m);
}
