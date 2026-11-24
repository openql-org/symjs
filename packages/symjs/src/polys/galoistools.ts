// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Dense polynomial arithmetic over the finite field GF(p) (SymPy
 * sympy.polys.galoistools): a polynomial is the list of its coefficients,
 * leading coefficient first, each in [0, p). Arithmetic, division, gcd,
 * composition, the Frobenius map, irreducibility tests (Ben-Or, Rabin),
 * square-free decomposition and factorization (Berlekamp, Cantor-Zassenhaus,
 * Shoup), and the Chinese remainder theorem.
 *
 * The functions keep SymPy's names (camelCase) and arguments; the ground
 * domain argument `K` is ZZ (coefficients are bigints).
 */

import { ExactQuotientFailed, NotInvertible } from '../core/errors';
import { at } from '../core/guard';
import { factorintInt } from '../ntheory/factor';
import { asInt, type IntLike } from '../ntheory/intutil';
import { ZZ, type Domain } from './domains';

/** A factorization [[factor, multiplicity], ...] of dense polynomials. */
export type GFFactorization = readonly (readonly [readonly IntLike[], IntLike])[];
const isSeq = (k: IntLike | readonly IntLike[]): k is readonly IntLike[] => Array.isArray(k);
const hasLc = (F: GFFactorization | readonly [IntLike, GFFactorization]): F is readonly [IntLike, GFFactorization] => F.length === 2 && !Array.isArray(F[0]);

/** A dense polynomial over GF(p): coefficients, leading first. */
export type GFPoly = bigint[];
type P = GFPoly;

const mod = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;
const ints = (f: readonly IntLike[]): P => f.map((c) => asInt(c));
const eq = (f: P, g: P): boolean => f.length === g.length && f.every((c, i) => c === at(g, i));
const isOne = (f: P): boolean => f.length === 1 && f[0] === 1n;

/** The inverse of a modulo m (K.invert). */
function invert(a: bigint, m: bigint): bigint {
  let [r0, r1] = [mod(a, m), m];
  let [s0, s1] = [1n, 0n];
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
  }
  if (r0 !== 1n) throw new NotInvertible(`inverse of ${a} (mod ${m}) does not exist`);
  return mod(s0, m);
}

/** The extended Euclidean algorithm on positive integers: [s, t, g] with s*a + t*b = g (K.gcdex). */
function igcdex(a: bigint, b: bigint): [bigint, bigint, bigint] {
  let [r0, r1, s0, s1, t0, t1] = [a, b, 1n, 0n, 0n, 1n];
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
    [t0, t1] = [t1, t0 - q * t1];
  }
  return [s0, t0, r0];
}

/** Lexicographic comparison of coefficient lists (Python list order). */
function cmpList(f: P, g: P): number {
  for (let i = 0; i < Math.min(f.length, g.length); i++) {
    const a = at(f, i);
    const b = at(g, i);
    if (a !== b) return a < b ? -1 : 1;
  }
  return f.length - g.length;
}
/** SymPy _sort_factors(factors, multiple=False): by degree, then coefficients. */
const sortPolys = (fs: P[]): P[] => [...fs].sort((f, g) => f.length - g.length || cmpList(f, g));
/** SymPy _sort_factors(factors): by degree, multiplicity, then coefficients. */
const sortFactors = (fs: [P, number][]): [P, number][] => [...fs].sort(([f, n], [g, m]) => f.length - g.length || n - m || cmpList(f, g));

// ---------------------------------------------------------------------------
// internal arithmetic on bigint lists
// ---------------------------------------------------------------------------

function strip(f: P): P {
  let k = 0;
  while (k < f.length && f[k] === 0n) k++;
  return k ? f.slice(k) : f;
}
const trunc = (f: P, p: bigint): P => strip(f.map((a) => mod(a, p)));
const neg = (f: P, p: bigint): P => f.map((c) => mod(-c, p));

function addGround(f: P, a: bigint, p: bigint): P {
  if (!f.length) {
    const c = mod(a, p);
    return c ? [c] : [];
  }
  const c = mod(at(f, -1) + a, p);
  if (f.length > 1) return [...f.slice(0, -1), c];
  return c ? [c] : [];
}
const subGround = (f: P, a: bigint, p: bigint): P => addGround(f, -a, p);
const mulGround = (f: P, a: bigint, p: bigint): P => (a === 0n ? [] : f.map((b) => mod(a * b, p)));
const quoGround = (f: P, a: bigint, p: bigint): P => mulGround(f, invert(a, p), p);

function add(fIn: P, gIn: P, p: bigint): P {
  if (!fIn.length) return gIn;
  if (!gIn.length) return fIn;
  let [f, g] = [fIn, gIn];
  if (f.length === g.length) return strip(f.map((a, i) => mod(a + at(g, i), p)));
  const k = Math.abs(f.length - g.length);
  let h: P;
  if (f.length > g.length) [h, f] = [f.slice(0, k), f.slice(k)];
  else [h, g] = [g.slice(0, k), g.slice(k)];
  return [...h, ...f.map((a, i) => mod(a + at(g, i), p))];
}

function sub(fIn: P, gIn: P, p: bigint): P {
  if (!gIn.length) return fIn;
  if (!fIn.length) return neg(gIn, p);
  let [f, g] = [fIn, gIn];
  if (f.length === g.length) return strip(f.map((a, i) => mod(a - at(g, i), p)));
  const k = Math.abs(f.length - g.length);
  let h: P;
  if (f.length > g.length) [h, f] = [f.slice(0, k), f.slice(k)];
  else [h, g] = [neg(g.slice(0, k), p), g.slice(k)];
  return [...h, ...f.map((a, i) => mod(a - at(g, i), p))];
}

function mul(f: P, g: P, p: bigint): P {
  if (!f.length || !g.length) return [];
  const df = f.length - 1;
  const dg = g.length - 1;
  const h: P = [];
  for (let i = 0; i <= df + dg; i++) {
    let c = 0n;
    for (let j = Math.max(0, i - dg); j <= Math.min(i, df); j++) c += at(f, j) * at(g, i - j);
    h.push(mod(c, p));
  }
  return strip(h);
}
const sqr = (f: P, p: bigint): P => mul(f, f, p);

function div(f: P, g: P, p: bigint): [P, P] {
  const df = f.length - 1;
  const dg = g.length - 1;
  if (!g.length) throw new RangeError('polynomial division');
  if (df < dg) return [[], f];
  const inv = invert(at(g, 0), p);
  const h = [...f];
  const dq = df - dg;
  const dr = dg - 1;
  for (let i = 0; i <= df; i++) {
    let c = at(h, i);
    for (let j = Math.max(0, dg - i); j <= Math.min(df - i, dr); j++) c -= at(h, i + j - dg) * at(g, dg - j);
    if (i <= dq) c *= inv;
    h[i] = mod(c, p);
  }
  return [h.slice(0, dq + 1), strip(h.slice(dq + 1))];
}
const rem = (f: P, g: P, p: bigint): P => div(f, g, p)[1];
const quo = (f: P, g: P, p: bigint): P => div(f, g, p)[0];

function pow(fIn: P, nIn: bigint, p: bigint): P {
  let [f, n, h] = [fIn, nIn, [1n]];
  for (;;) {
    if (n & 1n) h = mul(h, f, p);
    n >>= 1n;
    if (!n) return h;
    f = sqr(f, p);
  }
}

function powMod(fIn: P, nIn: bigint, g: P, p: bigint): P {
  let [f, n, h] = [fIn, nIn, [1n]];
  for (;;) {
    if (n & 1n) h = rem(mul(h, f, p), g, p);
    n >>= 1n;
    if (!n) return h;
    f = rem(sqr(f, p), g, p);
  }
}

function monic(f: P, p: bigint): [bigint, P] {
  if (!f.length) return [0n, []];
  const lc = at(f, 0);
  return lc === 1n ? [lc, [...f]] : [lc, quoGround(f, lc, p)];
}

function gcd(fIn: P, gIn: P, p: bigint): P {
  let [f, g] = [fIn, gIn];
  while (g.length) [f, g] = [g, rem(f, g, p)];
  return monic(f, p)[1];
}

function diff(f: P, p: bigint): P {
  const df = f.length - 1;
  const h: P = Array.from({ length: Math.max(df, 0) }, () => 0n);
  for (let i = 0; i < df; i++) h[i] = mod(at(f, i) * BigInt(df - i), p);
  return strip(h);
}

function evalAt(f: P, a: bigint, p: bigint): bigint {
  let r = 0n;
  for (const c of f) r = mod(r * a + c, p);
  return r;
}

function composeMod(g: P, h: P, f: P, p: bigint): P {
  if (!g.length) return [];
  let comp: P = [at(g, 0)];
  for (const a of g.slice(1)) comp = rem(addGround(mul(comp, h, p), a, p), f, p);
  return comp;
}

function frobeniusMonomialBase(g: P, p: bigint): P[] {
  const n = g.length - 1;
  if (n <= 0) return [];
  const b: P[] = [[1n]];
  if (p < BigInt(n)) {
    for (let i = 1; i < n; i++) b.push(rem([...at(b, i - 1), ...Array.from({ length: Number(p) }, () => 0n)], g, p));
  } else if (n > 1) {
    b.push(powMod([1n, 0n], p, g, p));
    for (let i = 2; i < n; i++) b.push(rem(mul(at(b, i - 1), at(b, 1), p), g, p));
  }
  return b;
}

function frobeniusMap(fIn: P, g: P, b: P[], p: bigint): P {
  const f = fIn.length - 1 >= g.length - 1 ? rem(fIn, g, p) : fIn;
  if (!f.length) return [];
  const n = f.length - 1;
  let sf: P = [at(f, -1)];
  for (let i = 1; i <= n; i++) sf = add(sf, mulGround(at(b, i), at(f, n - i), p), p);
  return sf;
}

function powPnm1d2(fIn: P, n: number, g: P, b: P[], p: bigint): P {
  const f = rem(fIn, g, p);
  let [h, r] = [f, f];
  for (let i = 1; i < n; i++) {
    h = frobeniusMap(h, g, b, p);
    r = rem(mul(r, h, p), g, p);
  }
  return powMod(r, (p - 1n) / 2n, g, p);
}

function traceMap(a: P, b: P, c: P, nIn: bigint, f: P, p: bigint): [P, P] {
  let n = nIn;
  let u = composeMod(a, b, f, p);
  let v = b;
  let [U, V] = n & 1n ? [add(a, u, p), b] : [a, c];
  n >>= 1n;
  while (n) {
    u = add(u, composeMod(u, v, f, p), p);
    v = composeMod(v, v, f, p);
    if (n & 1n) {
      U = add(U, composeMod(u, V, f, p), p);
      V = composeMod(v, V, f, p);
    }
    n >>= 1n;
  }
  return [composeMod(a, V, f, p), U];
}

function traceMapFrob(fIn: P, n: number, g: P, b: P[], p: bigint): P {
  const f = rem(fIn, g, p);
  let [h, r] = [f, f];
  for (let i = 1; i < n; i++) {
    h = frobeniusMap(h, g, b, p);
    r = rem(add(r, h, p), g, p);
  }
  return r;
}

/** A deterministic pseudo-random generator for the probabilistic algorithms (xorshift). */
function rng(seed = 0x2545f491n): (bound: bigint) => bigint {
  let s = seed;
  return (bound) => {
    s ^= (s << 13n) & 0xffffffffffffffffn;
    s ^= s >> 7n;
    s ^= (s << 17n) & 0xffffffffffffffffn;
    return s % bound;
  };
}
const randomPoly = (n: number, p: bigint, next: (b: bigint) => bigint): P => [1n, ...Array.from({ length: n }, () => next(p))];

function irredBenOr(fIn: P, p: bigint): boolean {
  const n = fIn.length - 1;
  if (n <= 1) return true;
  const f = monic(fIn, p)[1];
  const x = [1n, 0n];
  if (n < 5) {
    const H = powMod(x, p, f, p);
    let h = H;
    for (let i = 0; i < Math.floor(n / 2); i++) {
      if (!isOne(gcd(f, sub(h, x, p), p))) return false;
      h = composeMod(h, H, f, p);
    }
  } else {
    const b = frobeniusMonomialBase(f, p);
    let h = frobeniusMap(x, f, b, p);
    for (let i = 0; i < Math.floor(n / 2); i++) {
      if (!isOne(gcd(f, sub(h, x, p), p))) return false;
      h = frobeniusMap(h, f, b, p);
    }
  }
  return true;
}

function irredRabin(fIn: P, p: bigint): boolean {
  const n = fIn.length - 1;
  if (n <= 1) return true;
  const f = monic(fIn, p)[1];
  const x = [1n, 0n];
  const indices = new Set([...factorintInt(BigInt(n), {}).keys()].map((d) => n / Number(d)));
  const b = frobeniusMonomialBase(f, p);
  let h = at(b, 1);
  for (let i = 1; i < n; i++) {
    if (indices.has(i) && !isOne(gcd(f, sub(h, x, p), p))) return false;
    h = frobeniusMap(h, f, b, p);
  }
  return eq(h, x);
}

function sqfList(fIn: P, p: bigint): [bigint, [P, number][]] {
  const r = Number(p);
  const [lc, f0] = monic(fIn, p);
  if (f0.length - 1 < 1) return [lc, []];
  let f = f0;
  const factors: [P, number][] = [];
  let n = 1;
  for (;;) {
    const F = diff(f, p);
    let sqf = false;
    if (F.length) {
      let g = gcd(f, F, p);
      let h = quo(f, g, p);
      let i = 1;
      while (!isOne(h)) {
        const G = gcd(g, h, p);
        const H = quo(h, G, p);
        if (H.length > 1) factors.push([H, i * n]);
        [g, h, i] = [quo(g, G, p), G, i + 1];
      }
      if (isOne(g)) sqf = true;
      else f = g;
    }
    if (sqf) break;
    // f is a p-th power: f(x) = g(x**p)
    const d = Math.floor((f.length - 1) / r);
    f = Array.from({ length: d + 1 }, (_, i) => at(f, i * r));
    n *= r;
  }
  return [lc, factors];
}

function qMatrix(f: P, p: bigint): P[] {
  const n = f.length - 1;
  const r = Number(p);
  let q: P = [1n, ...Array.from({ length: n - 1 }, () => 0n)];
  const Q: P[] = [[...q]];
  for (let i = 1; i <= (n - 1) * r; i++) {
    const c = at(q, -1);
    const qq: P = [mod(-c * at(f, -1), p)];
    for (let j = 1; j < n; j++) qq.push(mod(at(q, j - 1) - c * at(f, -j - 1), p));
    if (i % r === 0) Q.push([...qq]);
    q = qq;
  }
  return Q;
}

function qBasis(Qin: readonly (readonly bigint[])[], p: bigint): P[] {
  const Q = Qin.map((q) => [...q]);
  const n = Q.length;
  const row = (k: number): P => at(Q, k);
  for (let k = 0; k < n; k++) row(k)[k] = mod(at(row(k), k) - 1n, p);
  for (let k = 0; k < n; k++) {
    let i = k;
    while (i < n && at(row(k), i) === 0n) i++;
    if (i === n) continue;
    const inv = invert(at(row(k), i), p);
    for (let j = 0; j < n; j++) row(j)[i] = mod(at(row(j), i) * inv, p);
    for (let j = 0; j < n; j++) [row(j)[k], row(j)[i]] = [at(row(j), i), at(row(j), k)];
    for (let ii = 0; ii < n; ii++) {
      if (ii === k) continue;
      const q = at(row(k), ii);
      for (let j = 0; j < n; j++) row(j)[ii] = mod(at(row(j), ii) - at(row(j), k) * q, p);
    }
  }
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) row(i)[j] = i === j ? mod(1n - at(row(i), j), p) : mod(-at(row(i), j), p);
  return Q.filter((q) => q.some((c) => c !== 0n));
}

function berlekamp(f: P, p: bigint): P[] {
  const V = qBasis(qMatrix(f, p), p).map((v) => strip([...v].reverse()));
  let factors: P[] = [f];
  split: for (let k = 1; k < V.length; k++) {
    for (const f0 of [...factors]) {
      let g0 = f0;
      for (let s = 0n; s < p; s++) {
        const h = gcd(g0, subGround(at(V, k), s, p), p);
        if (!isOne(h) && !eq(h, g0)) {
          factors = factors.filter((x) => x !== g0);
          g0 = quo(g0, h, p);
          factors.push(g0, h);
        }
        if (factors.length === V.length) break split;
      }
    }
  }
  return sortPolys(factors);
}

function ddfZassenhaus(fIn: P, p: bigint): [P, number][] {
  let f = fIn;
  let g: P = [1n, 0n];
  const factors: [P, number][] = [];
  let b = frobeniusMonomialBase(f, p);
  for (let i = 1; 2 * i <= f.length - 1; i++) {
    g = frobeniusMap(g, f, b, p);
    const h = gcd(f, sub(g, [1n, 0n], p), p);
    if (!isOne(h)) {
      factors.push([h, i]);
      f = quo(f, h, p);
      g = rem(g, f, p);
      b = frobeniusMonomialBase(f, p);
    }
  }
  return isOne(f) ? factors : [...factors, [f, f.length - 1]];
}

function edfZassenhaus(f: P, n: number, p: bigint, next: (b: bigint) => bigint): P[] {
  let factors: P[] = [f];
  if (f.length - 1 <= n) return factors;
  const N = Math.floor((f.length - 1) / n);
  const b = p === 2n ? [] : frobeniusMonomialBase(f, p);
  let t: P = [1n, 0n];
  while (factors.length < N) {
    let g: P;
    if (p === 2n) {
      let [h, r] = [t, t];
      for (let i = 0; i < n - 1; i++) {
        r = powMod(r, 2n, f, p);
        h = add(h, r, p);
      }
      g = gcd(f, h, p);
      t = [...t, 0n, 0n];
    } else {
      const h = powPnm1d2(randomPoly(2 * n - 1, p, next), n, f, b, p);
      g = gcd(f, subGround(h, 1n, p), p);
    }
    if (!isOne(g) && !eq(g, f)) factors = [...edfZassenhaus(g, n, p, next), ...edfZassenhaus(quo(f, g, p), n, p, next)];
  }
  return sortPolys(factors);
}

function ddfShoup(fIn: P, p: bigint): [P, number][] {
  let f = fIn;
  const n = f.length - 1;
  const k = Math.ceil(Math.sqrt(Math.floor(n / 2)));
  const b = frobeniusMonomialBase(f, p);
  const x: P = [1n, 0n];
  const U: P[] = [x, frobeniusMap(x, f, b, p)];
  for (let i = 2; i <= k; i++) U.push(frobeniusMap(at(U, i - 1), f, b, p));
  const h = at(U, k);
  U.length = k;
  const V: P[] = [h];
  for (let i = 1; i < k; i++) V.push(composeMod(at(V, i - 1), h, f, p));
  const factors: [P, number][] = [];
  V.forEach((v, i) => {
    let hh: P = [1n];
    for (const u of U) hh = rem(mul(hh, sub(v, u, p), p), f, p);
    let g = gcd(f, hh, p);
    f = quo(f, g, p);
    let j = k - 1;
    for (const u of [...U].reverse()) {
      const F = gcd(g, sub(v, u, p), p);
      if (!isOne(F)) factors.push([F, k * (i + 1) - j]);
      g = quo(g, F, p);
      j--;
    }
  });
  if (!isOne(f)) factors.push([f, f.length - 1]);
  return factors;
}

function edfShoup(f: P, n: number, p: bigint, next: (b: bigint) => bigint): P[] {
  const N = f.length - 1;
  if (N <= 0) return [];
  if (N <= n) return [f];
  const x: P = [1n, 0n];
  const r = randomPoly(N - 1, p, next);
  if (p === 2n) {
    const H = traceMap(r, powMod(x, p, f, p), x, BigInt(n - 1), f, p)[1];
    const h1 = gcd(f, H, p);
    return sortPolys([...edfShoup(h1, n, p, next), ...edfShoup(quo(f, h1, p), n, p, next)]);
  }
  const H = traceMapFrob(r, n, f, frobeniusMonomialBase(f, p), p);
  const h = powMod(H, (p - 1n) / 2n, f, p);
  const h1 = gcd(f, h, p);
  const h2 = gcd(f, subGround(h, 1n, p), p);
  const h3 = quo(f, mul(h1, h2, p), p);
  return sortPolys([...edfShoup(h1, n, p, next), ...edfShoup(h2, n, p, next), ...edfShoup(h3, n, p, next)]);
}

const zassenhaus = (f: P, p: bigint): P[] => {
  const next = rng();
  return sortPolys(ddfZassenhaus(f, p).flatMap(([g, n]) => edfZassenhaus(g, n, p, next)));
};
const shoup = (f: P, p: bigint): P[] => {
  const next = rng();
  return sortPolys(ddfShoup(f, p).flatMap(([g, n]) => edfShoup(g, n, p, next)));
};

/** The factorization methods of gfFactorSqf. */
export type GFFactorMethod = 'berlekamp' | 'zassenhaus' | 'shoup';
const FACTOR_METHODS: Readonly<Record<GFFactorMethod, (f: P, p: bigint) => P[]>> = { berlekamp, zassenhaus, shoup };

function factorSqf(fIn: P, p: bigint, method: string = 'zassenhaus'): [bigint, P[]] {
  const [lc, f] = monic(fIn, p);
  if (f.length - 1 < 1) return [lc, []];
  if (method !== 'berlekamp' && method !== 'zassenhaus' && method !== 'shoup') throw new RangeError(`unknown finite-field factorization method: ${method}`);
  return [lc, FACTOR_METHODS[method](f, p)];
}

// ---------------------------------------------------------------------------
// public API (SymPy names)
// ---------------------------------------------------------------------------

/**
 * Solves simultaneous congruences for the given residues and moduli.
 *
 * @param U - Residues to combine.
 * @param M - Pairwise coprime moduli.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The combined integer residue.
 * @see SymPy `sympy.polys.galoistools.gf_crt`
 * @example
 * ```ts
 * import { ZZ, gfCrt } from '@symjs/symjs';
 *
 * gfCrt([49, 76, 65], [99, 97, 95], ZZ); // => 639985
 * ```
 */
export function gfCrt(U: readonly IntLike[], M: readonly IntLike[], _K: Domain = ZZ): bigint {
  const ms = ints(M);
  const p = ms.reduce((a, b) => a * b, 1n);
  let v = 0n;
  ints(U).forEach((u, i) => {
    const m = at(ms, i);
    const e = p / m;
    v += e * mod(u * igcdex(e, m)[0], m);
  });
  return mod(v, p);
}

/**
 * Precomputes the modulus products and inverses used in Chinese remainder reconstruction.
 *
 * @param M - Pairwise coprime moduli.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The product, complementary products, and inverses.
 * @see SymPy `sympy.polys.galoistools.gf_crt1`
 * @remarks SymPy returns `(912285, [9215, 9405, 9603], [62, 24, 12])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfCrt1 } from '@symjs/symjs';
 *
 * gfCrt1([99, 97, 95], ZZ); // => [912285, [9215, 9405, 9603], [62, 24, 12]]
 * ```
 */
export function gfCrt1(M: readonly IntLike[], _K: Domain = ZZ): [bigint, bigint[], bigint[]] {
  const ms = ints(M);
  const p = ms.reduce((a, b) => a * b, 1n);
  const E = ms.map((m) => p / m);
  const S = ms.map((m, i) => mod(igcdex(at(E, i), m)[0], m));
  return [p, E, S];
}

/**
 * Combines residues using the precomputed Chinese remainder data.
 *
 * @param U - Residues to combine.
 * @param M - Pairwise coprime moduli.
 * @param p - Product of the pairwise coprime moduli.
 * @param E - Partial products of the moduli.
 * @param S - Modular inverses of the partial products.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The reconstructed residue.
 * @see SymPy `sympy.polys.galoistools.gf_crt2`
 * @example
 * ```ts
 * import { ZZ, gfCrt2 } from '@symjs/symjs';
 *
 * gfCrt2([49, 76, 65], [99, 97, 95], 912285, [9215, 9405, 9603], [62, 24, 12], ZZ); // => 639985
 * ```
 */
export function gfCrt2(U: readonly IntLike[], M: readonly IntLike[], p: IntLike, E: readonly IntLike[], S: readonly IntLike[], _K: Domain = ZZ): bigint {
  const [us, ms, es, ss] = [ints(U), ints(M), ints(E), ints(S)];
  let v = 0n;
  us.forEach((u, i) => (v += at(es, i) * mod(u * at(ss, i), at(ms, i))));
  return mod(v, asInt(p));
}

/**
 * Chooses the representative of the residue class in `(-p/2, p/2]`.
 *
 * @param a - Ground coefficient.
 * @param p - Prime modulus of the coefficient field.
 * @returns The symmetric integer residue.
 * @see SymPy `sympy.polys.galoistools.gf_int`
 * @example
 * ```ts
 * import { gfInt } from '@symjs/symjs';
 *
 * gfInt(2, 7); // => 2
 * gfInt(5, 7); // => -2
 * ```
 */
export function gfInt(a: IntLike, p: IntLike): bigint {
  const [x, m] = [asInt(a), asInt(p)];
  return x <= m / 2n ? x : x - m;
}

/**
 * Computes the polynomial degree, assigning minus one to the zero polynomial.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @returns The degree of f.
 * @see SymPy `sympy.polys.galoistools.gf_degree`
 * @example
 * ```ts
 * import { gfDegree } from '@symjs/symjs';
 *
 * gfDegree([1, 1, 2, 0]); // => 3
 * gfDegree([]); // => -1
 * ```
 */
export function gfDegree(f: readonly IntLike[]): number {
  return f.length - 1;
}

/**
 * Extracts the coefficient of the leading term.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The leading coefficient.
 * @see SymPy `sympy.polys.galoistools.gf_LC`
 * @example
 * ```ts
 * import { ZZ, gfLC } from '@symjs/symjs';
 *
 * gfLC([3, 0, 1], ZZ); // => 3
 * ```
 */
export function gfLC(f: readonly IntLike[], _K: Domain = ZZ): bigint {
  return f.length ? asInt(at(f, 0)) : 0n;
}

/**
 * Extracts the coefficient of degree zero.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The trailing coefficient.
 * @see SymPy `sympy.polys.galoistools.gf_TC`
 * @example
 * ```ts
 * import { ZZ, gfTC } from '@symjs/symjs';
 *
 * gfTC([3, 0, 1], ZZ); // => 1
 * ```
 */
export function gfTC(f: readonly IntLike[], _K: Domain = ZZ): bigint {
  return f.length ? asInt(at(f, -1)) : 0n;
}

/**
 * Strips leading zeros from the coefficient list.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_strip`
 * @example
 * ```ts
 * import { gfStrip } from '@symjs/symjs';
 *
 * gfStrip([0, 0, 0, 3, 0, 1]); // => [3, 0, 1]
 * ```
 */
export function gfStrip(f: readonly IntLike[]): bigint[] {
  return strip(ints(f));
}

/**
 * Reduces every polynomial coefficient modulo the prime.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_trunc`
 * @example
 * ```ts
 * import { gfTrunc } from '@symjs/symjs';
 *
 * gfTrunc([7, -2, 3], 5); // => [2, 3, 3]
 * ```
 */
export function gfTrunc(f: readonly IntLike[], p: IntLike): bigint[] {
  return trunc(ints(f), asInt(p));
}

/**
 * Converts coefficients to the domain and reduces them modulo the prime.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_normal`
 * @example
 * ```ts
 * import { ZZ, gfNormal } from '@symjs/symjs';
 *
 * gfNormal([5, 10, 21, -3], 5, ZZ); // => [1, 2]
 * ```
 */
export function gfNormal(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return trunc(ints(f), asInt(p));
}

/**
 * Converts degree-indexed integer coefficients to a dense polynomial modulo `p`.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The reduced coefficient list.
 * @see SymPy `sympy.polys.galoistools.gf_from_dict`
 * @example
 * ```ts
 * import { ZZ, gfFromDict } from '@symjs/symjs';
 *
 * gfFromDict(new Map([[10, 4], [4, 33], [0, -1]]), 5, ZZ); // => [4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4]
 * ```
 */
export function gfFromDict(f: ReadonlyMap<IntLike | readonly IntLike[], IntLike>, p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  // a key is a degree or a 1-tuple of it
  const terms = new Map([...f].map(([k, c]) => [Number(isSeq(k) ? asInt(at(k, 0)) : asInt(k)), asInt(c)]));
  const n = Math.max(...terms.keys());
  const h: P = [];
  for (let k = n; k >= 0; k--) h.push(mod(terms.get(k) ?? 0n, m));
  return trunc(h, m);
}

/**
 * Indexes the nonzero terms by degree using symmetric representatives by default.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param symmetric - Use signed representatives of residue classes.
 * @returns A degree-to-coefficient map.
 * @see SymPy `sympy.polys.galoistools.gf_to_dict`
 * @example
 * ```ts
 * import { gfToDict } from '@symjs/symjs';
 *
 * gfToDict([4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4], 5); // => {0: -1, 4: -2, 10: -1}
 * gfToDict([4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4], 5, false); // => {0: 4, 4: 3, 10: 4}
 * ```
 */
export function gfToDict(f: readonly IntLike[], p: IntLike, symmetric = true): Map<number, bigint> {
  const cs = ints(f);
  const n = cs.length - 1;
  const out = new Map<number, bigint>();
  for (let k = 0; k <= n; k++) {
    const a = symmetric ? gfInt(at(cs, n - k), p) : at(cs, n - k);
    if (a) out.set(k, a);
  }
  return out;
}

/**
 * Reduces an integer polynomial over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @returns The coefficient list modulo `p`.
 * @see SymPy `sympy.polys.galoistools.gf_from_int_poly`
 * @example
 * ```ts
 * import { gfFromIntPoly } from '@symjs/symjs';
 *
 * gfFromIntPoly([7, -2, 3], 5); // => [2, 3, 3]
 * ```
 */
export function gfFromIntPoly(f: readonly IntLike[], p: IntLike): bigint[] {
  return trunc(ints(f), asInt(p));
}

/**
 * Lifts finite-field coefficients to integers, using symmetric representatives by default.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param symmetric - Use signed representatives of residue classes.
 * @returns The integer polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_to_int_poly`
 * @example
 * ```ts
 * import { gfToIntPoly } from '@symjs/symjs';
 *
 * gfToIntPoly([2, 3, 3], 5); // => [2, -2, -2]
 * gfToIntPoly([2, 3, 3], 5, false); // => [2, 3, 3]
 * ```
 */
export function gfToIntPoly(f: readonly IntLike[], p: IntLike, symmetric = true): bigint[] {
  return symmetric ? f.map((c) => gfInt(c, p)) : ints(f);
}

/**
 * Negates every coefficient of the polynomial.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The additive inverse.
 * @see SymPy `sympy.polys.galoistools.gf_neg`
 * @example
 * ```ts
 * import { ZZ, gfNeg } from '@symjs/symjs';
 *
 * gfNeg([3, 2, 1, 0], 5, ZZ); // => [2, 3, 4, 0]
 * ```
 */
export function gfNeg(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return neg(ints(f), asInt(p));
}

/**
 * Adds a ground element to the polynomial's constant term.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param a - Ground coefficient.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_add_ground`
 * @example
 * ```ts
 * import { ZZ, gfAddGround } from '@symjs/symjs';
 *
 * gfAddGround([3, 2, 4], 2, 5, ZZ); // => [3, 2, 1]
 * ```
 */
export function gfAddGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return addGround(ints(f), asInt(a), asInt(p));
}

/**
 * Subtracts a ground element from the polynomial's constant term.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param a - Ground coefficient.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_sub_ground`
 * @example
 * ```ts
 * import { ZZ, gfSubGround } from '@symjs/symjs';
 *
 * gfSubGround([3, 2, 4], 2, 5, ZZ); // => [3, 2, 2]
 * ```
 */
export function gfSubGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return subGround(ints(f), asInt(a), asInt(p));
}

/**
 * Multiplies all coefficients by a ground element.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param a - Ground coefficient.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_mul_ground`
 * @example
 * ```ts
 * import { ZZ, gfMulGround } from '@symjs/symjs';
 *
 * gfMulGround([3, 2, 4], 2, 5, ZZ); // => [1, 4, 3]
 * ```
 */
export function gfMulGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return mulGround(ints(f), asInt(a), asInt(p));
}

/**
 * Divides all coefficients by a nonzero ground element.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param a - Ground coefficient.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @throws NotInvertible when the ground divisor is not invertible modulo the characteristic.
 * @see SymPy `sympy.polys.galoistools.gf_quo_ground`
 * @example
 * ```ts
 * import { ZZ, gfQuoGround } from '@symjs/symjs';
 *
 * gfQuoGround([3, 2, 4], 2, 5, ZZ); // => [4, 1, 2]
 * ```
 */
export function gfQuoGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return quoGround(ints(f), asInt(a), asInt(p));
}

/**
 * Adds the corresponding coefficients of two polynomials.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The sum polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_add`
 * @example
 * ```ts
 * import { ZZ, gfAdd } from '@symjs/symjs';
 *
 * gfAdd([3, 2, 4], [2, 2, 2], 5, ZZ); // => [4, 1]
 * ```
 */
export function gfAdd(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return add(ints(f), ints(g), asInt(p));
}

/**
 * Subtracts the second polynomial from the first.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The difference polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_sub`
 * @example
 * ```ts
 * import { ZZ, gfSub } from '@symjs/symjs';
 *
 * gfSub([3, 2, 4], [2, 2, 2], 5, ZZ); // => [1, 0, 2]
 * ```
 */
export function gfSub(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return sub(ints(f), ints(g), asInt(p));
}

/**
 * Multiplies polynomials over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_mul`
 * @example
 * ```ts
 * import { ZZ, gfMul } from '@symjs/symjs';
 *
 * gfMul([3, 2, 4], [2, 2, 2], 5, ZZ); // => [1, 0, 3, 2, 3]
 * ```
 */
export function gfMul(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return mul(ints(f), ints(g), asInt(p));
}

/**
 * Multiplies the polynomial by itself.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The squared polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_sqr`
 * @example
 * ```ts
 * import { ZZ, gfSqr } from '@symjs/symjs';
 *
 * gfSqr([3, 2, 4], 5, ZZ); // => [4, 2, 3, 1, 1]
 * ```
 */
export function gfSqr(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return sqr(ints(f), asInt(p));
}

/**
 * Adds the product of the last two polynomials to the first.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param h - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The polynomial `f + g*h`.
 * @see SymPy `sympy.polys.galoistools.gf_add_mul`
 * @example
 * ```ts
 * import { ZZ, gfAddMul } from '@symjs/symjs';
 *
 * gfAddMul([3, 2, 4], [2, 2, 2], [1, 4], 5, ZZ); // => [2, 3, 2, 2]
 * ```
 */
export function gfAddMul(f: readonly IntLike[], g: readonly IntLike[], h: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  return add(ints(f), mul(ints(g), ints(h), m), m);
}

/**
 * Subtracts the product of the last two polynomials from the first.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param h - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The polynomial `f - g*h`.
 * @see SymPy `sympy.polys.galoistools.gf_sub_mul`
 * @example
 * ```ts
 * import { ZZ, gfSubMul } from '@symjs/symjs';
 *
 * gfSubMul([3, 2, 4], [2, 2, 2], [1, 4], 5, ZZ); // => [3, 3, 2, 1]
 * ```
 */
export function gfSubMul(f: readonly IntLike[], g: readonly IntLike[], h: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  return sub(ints(f), mul(ints(g), ints(h), m), m);
}

/**
 * Multiplies the factors to their specified powers and applies the optional leading coefficient.
 *
 * @param F - Factor and multiplicity pairs, optionally preceded by a leading coefficient.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The expanded polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_expand`
 * @example
 * ```ts
 * import { ZZ, gfExpand } from '@symjs/symjs';
 *
 * gfExpand([[[3, 2, 4], 1], [[2, 2], 2], [[3, 1], 3]], 5, ZZ); // => [4, 3, 0, 3, 0, 1, 4, 1]
 * ```
 */
export function gfExpand(F: GFFactorization | readonly [IntLike, GFFactorization], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  const [lc, fs] = hasLc(F) ? [asInt(F[0]), F[1]] : [1n, F];
  let g: P = [lc];
  for (const [f, k] of fs) g = mul(g, pow(ints(f), asInt(k), m), m);
  return g;
}

/**
 * Divides polynomials over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The quotient and remainder.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.galoistools.gf_div`
 * @remarks SymPy returns `([1, 1], [1])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfDiv } from '@symjs/symjs';
 *
 * gfDiv([1, 0, 1, 1], [1, 1, 0], 2, ZZ); // => [[1, 1], [1]]
 * ```
 */
export function gfDiv(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[]] {
  return div(ints(f), ints(g), asInt(p));
}

/**
 * Computes what remains after dividing `f` by `g` over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The remainder polynomial.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.galoistools.gf_rem`
 * @example
 * ```ts
 * import { ZZ, gfRem } from '@symjs/symjs';
 *
 * gfRem([1, 0, 1, 1], [1, 1, 0], 2, ZZ); // => [1]
 * ```
 */
export function gfRem(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return rem(ints(f), ints(g), asInt(p));
}

/**
 * Retains the quotient when dividing `f` by `g` over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The quotient polynomial.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.galoistools.gf_quo`
 * @example
 * ```ts
 * import { ZZ, gfQuo } from '@symjs/symjs';
 *
 * gfQuo([1, 0, 1, 1], [1, 1, 0], 2, ZZ); // => [1, 1]
 * gfQuo([1, 0, 3, 2, 3], [2, 2, 2], 5, ZZ); // => [3, 2, 4]
 * ```
 */
export function gfQuo(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return quo(ints(f), ints(g), asInt(p));
}

/**
 * Divides exactly over the prime field, raising `ExactQuotientFailed` for a nonzero remainder.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The exact quotient f / g.
 * @throws ExactQuotientFailed when the divisor does not divide the dividend exactly.
 * @throws RangeError when the divisor is zero.
 * @see SymPy `sympy.polys.galoistools.gf_exquo`
 * @example
 * ```ts
 * import { ZZ, gfExquo } from '@symjs/symjs';
 *
 * gfExquo([1, 0, 3, 2, 3], [2, 2, 2], 5, ZZ); // => [3, 2, 4]
 * ```
 */
export function gfExquo(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [q, r] = div(ints(f), ints(g), asInt(p));
  if (r.length) throw new ExactQuotientFailed(`[${f.join(', ')}] does not divide [${g.join(', ')}]`);
  return q;
}

/**
 * Shifts the polynomial by multiplying by a power of its generator.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param n - Nonnegative integer exponent or shift.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_lshift`
 * @example
 * ```ts
 * import { ZZ, gfLshift } from '@symjs/symjs';
 *
 * gfLshift([3, 2, 4], 4, ZZ); // => [3, 2, 4, 0, 0, 0, 0]
 * ```
 */
export function gfLshift(f: readonly IntLike[], n: IntLike, _K: Domain = ZZ): bigint[] {
  const cs = ints(f);
  return cs.length ? [...cs, ...Array.from({ length: Number(asInt(n)) }, () => 0n)] : cs;
}

/**
 * Splits the polynomial into its quotient and remainder on division by `x**n`.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param n - Nonnegative integer exponent or shift.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The shifted polynomial and its low-degree tail.
 * @see SymPy `sympy.polys.galoistools.gf_rshift`
 * @remarks SymPy returns `([1, 2], [3, 4, 0])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfRshift } from '@symjs/symjs';
 *
 * gfRshift([1, 2, 3, 4, 0], 3, ZZ); // => [[1, 2], [3, 4, 0]]
 * ```
 */
export function gfRshift(f: readonly IntLike[], n: IntLike, _K: Domain = ZZ): [bigint[], bigint[]] {
  const cs = ints(f);
  const k = Number(asInt(n));
  return k ? [cs.slice(0, -k), cs.slice(-k)] : [cs, []];
}

/**
 * Raises the polynomial to an integer power by repeated squaring.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param n - Nonnegative integer exponent or shift.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_pow`
 * @example
 * ```ts
 * import { ZZ, gfPow } from '@symjs/symjs';
 *
 * gfPow([3, 2, 4], 3, 5, ZZ); // => [2, 4, 4, 2, 2, 1, 4]
 * ```
 */
export function gfPow(f: readonly IntLike[], n: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return pow(ints(f), asInt(n), asInt(p));
}

/**
 * Computes `x**(i*p)` modulo `g` for each basis degree below the degree of `g`.
 *
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The Frobenius images of the monomials.
 * @see SymPy `sympy.polys.galoistools.gf_frobenius_monomial_base`
 * @example
 * ```ts
 * import { ZZ, gfFrobeniusMonomialBase } from '@symjs/symjs';
 *
 * gfFrobeniusMonomialBase([1, 0, 2, 1], 5, ZZ); // => [[1], [4, 4, 2], [1, 2]]
 * ```
 */
export function gfFrobeniusMonomialBase(g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return frobeniusMonomialBase(ints(g), asInt(p));
}

/**
 * Applies the Frobenius map modulo the polynomial using the supplied monomial images.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param b - Precomputed Frobenius images of the monomial basis.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_frobenius_map`
 * @example
 * ```ts
 * import { ZZ, gfFrobeniusMap } from '@symjs/symjs';
 *
 * gfFrobeniusMap([2, 1, 0, 1], [1, 0, 2, 1], [[1], [4, 4, 2], [1, 2]], 5, ZZ); // => [4, 0, 3]
 * ```
 */
export function gfFrobeniusMap(f: readonly IntLike[], g: readonly IntLike[], b: readonly (readonly IntLike[])[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return frobeniusMap(ints(f), ints(g), b.map(ints), asInt(p));
}

/**
 * Raises the polynomial to the specified power modulo the divisor.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param n - Nonnegative integer exponent or shift.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_pow_mod`
 * @example
 * ```ts
 * import { ZZ, gfPowMod } from '@symjs/symjs';
 *
 * gfPowMod([3, 2, 4], 3, [1, 1], 5, ZZ); // => []
 * ```
 */
export function gfPowMod(f: readonly IntLike[], n: IntLike, g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  const k = asInt(n);
  return k === 0n ? [1n] : powMod(rem(ints(f), ints(g), m), k, ints(g), m);
}

/**
 * Computes the greatest common divisor over the prime field with leading coefficient one.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The monic GCD.
 * @see SymPy `sympy.polys.galoistools.gf_gcd`
 * @example
 * ```ts
 * import { ZZ, gfGcd } from '@symjs/symjs';
 *
 * gfGcd([3, 2, 4], [2, 2, 3], 5, ZZ); // => [1, 3]
 * ```
 */
export function gfGcd(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return gcd(ints(f), ints(g), asInt(p));
}

/**
 * Computes the least common multiple over the prime field with leading coefficient one.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The monic LCM.
 * @see SymPy `sympy.polys.galoistools.gf_lcm`
 * @example
 * ```ts
 * import { ZZ, gfLcm } from '@symjs/symjs';
 *
 * gfLcm([3, 2, 4], [2, 2, 3], 5, ZZ); // => [1, 2, 0, 4]
 * ```
 */
export function gfLcm(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (!a.length || !b.length) return [];
  return monic(quo(mul(a, b, m), gcd(a, b, m), m), m)[1];
}

/**
 * Factors out the monic GCD of the two inputs.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The GCD and both quotients.
 * @see SymPy `sympy.polys.galoistools.gf_cofactors`
 * @remarks SymPy returns `([1, 3], [3, 3], [2, 1])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfCofactors } from '@symjs/symjs';
 *
 * gfCofactors([3, 2, 4], [2, 2, 3], 5, ZZ); // => [[1, 3], [3, 3], [2, 1]]
 * ```
 */
export function gfCofactors(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[], bigint[]] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (!a.length && !b.length) return [[], [], []];
  const h = gcd(a, b, m);
  return [h, quo(a, h, m), quo(b, h, m)];
}

/**
 * Finds Bézout coefficients expressing the monic GCD as `s*f + t*g`.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The triple `[s, t, gcd]`.
 * @see SymPy `sympy.polys.galoistools.gf_gcdex`
 * @remarks SymPy returns `([5, 6], [6], [1, 7])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfGcdex } from '@symjs/symjs';
 *
 * gfGcdex([1, 8, 7], [1, 7, 1, 7], 11, ZZ); // => [[5, 6], [6], [1, 7]]
 * ```
 */
export function gfGcdex(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[], bigint[]] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (!a.length && !b.length) return [[1n], [], []];
  const [p0, r0In] = monic(a, m);
  const [p1, r1In] = monic(b, m);
  let [r0, r1] = [r0In, r1In];
  if (!a.length) return [[], [invert(p1, m)], r1];
  if (!b.length) return [[invert(p0, m)], [], r0];
  let [s0, s1]: [P, P] = [[invert(p0, m)], []];
  let [t0, t1]: [P, P] = [[], [invert(p1, m)]];
  for (;;) {
    const [Q, R] = div(r0, r1, m);
    if (!R.length) break;
    let lc: bigint;
    [[lc, r1], r0] = [monic(R, m), r1];
    const inv = invert(lc, m);
    const s = sub(s0, mul(s1, Q, m), m);
    const t = sub(t0, mul(t1, Q, m), m);
    [s1, s0] = [mulGround(s, inv, m), s1];
    [t1, t0] = [mulGround(t, inv, m), t1];
  }
  return [s1, t1, r1];
}

/**
 * Separates the leading coefficient from the monic polynomial.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The leading coefficient and monic part.
 * @see SymPy `sympy.polys.galoistools.gf_monic`
 * @remarks SymPy returns `(3, [1, 4, 3])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfMonic } from '@symjs/symjs';
 *
 * gfMonic([3, 2, 4], 5, ZZ); // => [3, [1, 4, 3]]
 * ```
 */
export function gfMonic(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint, bigint[]] {
  return monic(ints(f), asInt(p));
}

/**
 * Differentiates the element with respect to its polynomial variable.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The derivative.
 * @see SymPy `sympy.polys.galoistools.gf_diff`
 * @example
 * ```ts
 * import { ZZ, gfDiff } from '@symjs/symjs';
 *
 * gfDiff([3, 2, 4], 5, ZZ); // => [1, 2]
 * ```
 */
export function gfDiff(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return diff(ints(f), asInt(p));
}

/**
 * Evaluates the polynomial over the prime field using Horner's rule.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param a - Evaluation point.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The value modulo the prime.
 * @see SymPy `sympy.polys.galoistools.gf_eval`
 * @example
 * ```ts
 * import { ZZ, gfEval } from '@symjs/symjs';
 *
 * gfEval([3, 2, 4], 2, 5, ZZ); // => 0
 * ```
 */
export function gfEval(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint {
  return evalAt(ints(f), asInt(a), asInt(p));
}

/**
 * Evaluates the polynomial at every supplied point.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param A - Points at which to evaluate the polynomial.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.galoistools.gf_multi_eval`
 * @example
 * ```ts
 * import { ZZ, gfMultiEval } from '@symjs/symjs';
 *
 * gfMultiEval([3, 2, 4], [0, 1, 2, 3, 4], 5, ZZ); // => [4, 4, 0, 2, 0]
 * ```
 */
export function gfMultiEval(f: readonly IntLike[], A: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [cs, m] = [ints(f), asInt(p)];
  return A.map((a) => evalAt(cs, asInt(a), m));
}

/**
 * Substitutes the second polynomial into the first.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The composition `f(g)`.
 * @see SymPy `sympy.polys.galoistools.gf_compose`
 * @example
 * ```ts
 * import { ZZ, gfCompose } from '@symjs/symjs';
 *
 * gfCompose([3, 2, 4], [2, 2, 2], 5, ZZ); // => [2, 4, 0, 3, 0]
 * ```
 */
export function gfCompose(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (b.length <= 1) return strip([evalAt(a, b.length ? at(b, 0) : 0n, m)]);
  if (!a.length) return [];
  let h: P = [at(a, 0)];
  for (const c of a.slice(1)) h = addGround(mul(h, b, m), c, m);
  return h;
}

/**
 * Composes `g` with `h` and reduces the result modulo `f`.
 *
 * @param g - Polynomial operand as coefficients in descending degree.
 * @param h - Polynomial operand as coefficients in descending degree.
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The reduced composition.
 * @see SymPy `sympy.polys.galoistools.gf_compose_mod`
 * @example
 * ```ts
 * import { ZZ, gfComposeMod } from '@symjs/symjs';
 *
 * gfComposeMod([3, 2, 4], [2, 2, 2], [4, 3], 5, ZZ); // => [4]
 * ```
 */
export function gfComposeMod(g: readonly IntLike[], h: readonly IntLike[], f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return composeMod(ints(g), ints(h), ints(f), asInt(p));
}

/**
 * Computes the modular composition and accumulated trace used in Shoup's algorithm.
 *
 * @param a - Polynomial whose iterated Frobenius images are summed.
 * @param b - Image of the generator under the Frobenius map.
 * @param c - Initial polynomial to compose with the iterated map.
 * @param n - Number of Frobenius iterations.
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The iterated image and trace polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_trace_map`
 * @remarks SymPy returns `([1, 3], [1, 3])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfTraceMap } from '@symjs/symjs';
 *
 * gfTraceMap([1, 2], [4, 4], [1, 1], 4, [3, 2, 4], 5, ZZ); // => [[1, 3], [1, 3]]
 * ```
 */
export function gfTraceMap(a: readonly IntLike[], b: readonly IntLike[], c: readonly IntLike[], n: IntLike, f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[]] {
  return traceMap(ints(a), ints(b), ints(c), asInt(n), ints(f), asInt(p));
}

/**
 * Generates a random monic polynomial of the specified degree using the supplied bounded integer
 * sampler.
 *
 * @param n - Degree of the polynomial to generate.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @param random - Sampler returning an integer residue below the supplied bound.
 * @returns The sampled polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_random`
 * @example
 * ```ts
 * import { gfRandom } from '@symjs/symjs';
 *
 * gfRandom(10, 5).length; // => 11
 * ```
 */
export function gfRandom(n: IntLike, p: IntLike, _K: Domain = ZZ, random: (bound: bigint) => bigint = rng(BigInt(Date.now()) | 1n)): bigint[] {
  return randomPoly(Number(asInt(n)), asInt(p), random);
}

/**
 * Samples a monic irreducible polynomial of the requested degree.
 *
 * @param n - Degree of the polynomial to generate.
 * @param p - Prime modulus of the coefficient field.
 * @param K - Integer coefficient domain, normally `ZZ`.
 * @param random - Sampler returning an integer residue below the supplied bound.
 * @returns An irreducible polynomial over the prime field.
 * @see SymPy `sympy.polys.galoistools.gf_irreducible`
 * @example
 * ```ts
 * import { gfIrreducible, gfIrreducibleP } from '@symjs/symjs';
 *
 * gfIrreducibleP(gfIrreducible(5, 3), 3); // => True
 * ```
 */
export function gfIrreducible(n: IntLike, p: IntLike, K: Domain = ZZ, random?: (bound: bigint) => bigint): bigint[] {
  const m = asInt(p);
  for (;;) {
    const f = gfRandom(n, m, K, random);
    if (irredRabin(f, m)) return f;
  }
}

/**
 * Tests irreducibility using Ben-Or's criterion.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns Whether the polynomial is irreducible over the finite field.
 * @see SymPy `sympy.polys.galoistools.gf_irred_p_ben_or`
 * @example
 * ```ts
 * import { ZZ, gfIrredPBenOr } from '@symjs/symjs';
 *
 * gfIrredPBenOr([1, 4, 2, 2, 3, 2, 4, 1, 4, 0, 4], 5, ZZ); // => True
 * gfIrredPBenOr([3, 2, 4], 5, ZZ); // => False
 * ```
 */
export function gfIrredPBenOr(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  return irredBenOr(ints(f), asInt(p));
}

/**
 * Tests irreducibility using Rabin's criterion.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns Whether the polynomial is irreducible over the finite field.
 * @see SymPy `sympy.polys.galoistools.gf_irred_p_rabin`
 * @example
 * ```ts
 * import { ZZ, gfIrredPRabin } from '@symjs/symjs';
 *
 * gfIrredPRabin([1, 4, 2, 2, 3, 2, 4, 1, 4, 0, 4], 5, ZZ); // => True
 * gfIrredPRabin([3, 2, 4], 5, ZZ); // => False
 * ```
 */
export function gfIrredPRabin(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  return irredRabin(ints(f), asInt(p));
}

/**
 * Tests a polynomial for irreducibility over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @param method - Algorithm to use.
 * @returns True for an irreducible polynomial.
 * @throws RangeError when the algorithm name is unrecognized.
 * @see SymPy `sympy.polys.galoistools.gf_irreducible_p`
 * @example
 * ```ts
 * import { ZZ, gfIrreducibleP } from '@symjs/symjs';
 *
 * gfIrreducibleP([1, 4, 2, 2, 3, 2, 4, 1, 4, 0, 4], 5, ZZ); // => True
 * gfIrreducibleP([3, 2, 4], 5, ZZ); // => False
 * ```
 */
export function gfIrreducibleP(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ, method = 'rabin'): boolean {
  if (method === 'ben-or') return irredBenOr(ints(f), asInt(p));
  if (method === 'rabin') return irredRabin(ints(f), asInt(p));
  throw new RangeError(`unknown finite-field irreducibility method: ${method}`);
}

/**
 * Checks that the polynomial has no repeated irreducible factors.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns True for a square-free polynomial.
 * @see SymPy `sympy.polys.galoistools.gf_sqf_p`
 * @example
 * ```ts
 * import { ZZ, gfSqfP } from '@symjs/symjs';
 *
 * gfSqfP([3, 2, 4], 5, ZZ); // => True
 * gfSqfP([2, 4, 4, 2, 2, 1, 4], 5, ZZ); // => False
 * ```
 */
export function gfSqfP(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  const m = asInt(p);
  const g = monic(ints(f), m)[1];
  return !g.length || isOne(gcd(g, diff(g, m), m));
}

/**
 * Removes repeated irreducible factors from the polynomial.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The square-free part.
 * @see SymPy `sympy.polys.galoistools.gf_sqf_part`
 * @example
 * ```ts
 * import { ZZ, gfSqfPart } from '@symjs/symjs';
 *
 * gfSqfPart([1, 1, 3, 0, 1, 0, 2, 2, 1], 5, ZZ); // => [1, 4, 3]
 * ```
 */
export function gfSqfPart(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  return sqfList(ints(f), m)[1].reduce<P>((g, [h]) => mul(g, h, m), [1n]);
}

/**
 * Groups factors over the prime field by multiplicity.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @param opts - Controls `all` (inclusion of all multiplicities).
 * @returns The leading coefficient and square-free factor–multiplicity pairs.
 * @throws RangeError when the `all` option is true.
 * @see SymPy `sympy.polys.galoistools.gf_sqf_list`
 * @remarks SymPy returns `(1, [([1, 1], 11)])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfSqfList } from '@symjs/symjs';
 *
 * gfSqfList([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 11, ZZ); // => [1, [[[1, 1], 11]]]
 * ```
 */
export function gfSqfList(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ, opts: { all?: boolean } = {}): [bigint, [bigint[], number][]] {
  if (opts.all === true) throw new RangeError("'all=True' is not supported yet");
  return sqfList(ints(f), asInt(p));
}

/**
 * Constructs the matrix for the Frobenius action in Berlekamp's algorithm.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns Berlekamp's Q matrix.
 * @see SymPy `sympy.polys.galoistools.gf_Qmatrix`
 * @example
 * ```ts
 * import { ZZ, gfQmatrix } from '@symjs/symjs';
 *
 * gfQmatrix([3, 2, 4], 5, ZZ); // => [[1, 0], [3, 4]]
 * gfQmatrix([1, 0, 0, 0, 1], 5, ZZ); // => [[1, 0, 0, 0], [0, 4, 0, 0], [0, 0, 1, 0], [0, 0, 0, 4]]
 * ```
 */
export function gfQmatrix(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return qMatrix(ints(f), asInt(p));
}

/**
 * Finds the subspace fixed by Berlekamp's matrix.
 *
 * @param Q - Berlekamp matrix.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns Basis vectors for the kernel of `Q - I`.
 * @see SymPy `sympy.polys.galoistools.gf_Qbasis`
 * @example
 * ```ts
 * import { ZZ, gfQbasis } from '@symjs/symjs';
 *
 * gfQbasis([[1, 0, 0, 0], [0, 4, 0, 0], [0, 0, 1, 0], [0, 0, 0, 4]], 5, ZZ); // => [[1, 0, 0, 0], [0, 0, 1, 0]]
 * gfQbasis([[1, 0], [3, 4]], 5, ZZ); // => [[1, 0]]
 * ```
 */
export function gfQbasis(Q: readonly (readonly IntLike[])[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return qBasis(Q.map(ints), asInt(p));
}

/**
 * Uses Berlekamp's algorithm to split a square-free monic polynomial.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The irreducible factors.
 * @see SymPy `sympy.polys.galoistools.gf_berlekamp`
 * @example
 * ```ts
 * import { ZZ, gfBerlekamp } from '@symjs/symjs';
 *
 * gfBerlekamp([1, 0, 0, 0, 1], 5, ZZ); // => [[1, 0, 2], [1, 0, 3]]
 * ```
 */
export function gfBerlekamp(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return berlekamp(ints(f), asInt(p));
}

/**
 * Groups irreducible factors by degree using Cantor–Zassenhaus distinct-degree factorization.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The factor products and their degrees.
 * @see SymPy `sympy.polys.galoistools.gf_ddf_zassenhaus`
 * @remarks SymPy returns `[([1, 0, 0, 0, 0, 10], 1), ([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], 2)]` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfDdfZassenhaus } from '@symjs/symjs';
 *
 * gfDdfZassenhaus([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10], 11, ZZ); // => [[[1, 0, 0, 0, 0, 10], 1], [[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], 2]]
 * ```
 */
export function gfDdfZassenhaus(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], number][] {
  return ddfZassenhaus(ints(f), asInt(p));
}

/**
 * Splits a product of equal-degree irreducibles using Cantor–Zassenhaus factorization.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param n - Degree of the factors.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The irreducible factors.
 * @see SymPy `sympy.polys.galoistools.gf_edf_zassenhaus`
 * @example
 * ```ts
 * import { ZZ, gfEdfZassenhaus } from '@symjs/symjs';
 *
 * gfEdfZassenhaus([1, 1, 1, 1], 1, 5, ZZ); // => [[1, 1], [1, 2], [1, 3]]
 * ```
 */
export function gfEdfZassenhaus(f: readonly IntLike[], n: IntLike, p: IntLike, _K: Domain = ZZ): bigint[][] {
  return edfZassenhaus(ints(f), Number(asInt(n)), asInt(p), rng());
}

/**
 * Groups irreducible factors by degree using the Kaltofen–Shoup algorithm.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The factor products and their degrees.
 * @see SymPy `sympy.polys.galoistools.gf_ddf_shoup`
 * @remarks SymPy returns `[([1, 1, 0], 1), ([1, 1, 0, 1, 2], 2)]` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfDdfShoup } from '@symjs/symjs';
 *
 * gfDdfShoup([1, 2, 1, 1, 0, 2, 0], 3, ZZ); // => [[[1, 1, 0], 1], [[1, 1, 0, 1, 2], 2]]
 * ```
 */
export function gfDdfShoup(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], number][] {
  return ddfShoup(ints(f), asInt(p));
}

/**
 * Splits a product of equal-degree irreducibles using the Gathen–Shoup algorithm.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param n - Degree of the factors.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The irreducible factors.
 * @see SymPy `sympy.polys.galoistools.gf_edf_shoup`
 * @example
 * ```ts
 * import { ZZ, gfEdfShoup } from '@symjs/symjs';
 *
 * gfEdfShoup([1, 2837, 2277], 1, 2917, ZZ); // => [[1, 852], [1, 1985]]
 * ```
 */
export function gfEdfShoup(f: readonly IntLike[], n: IntLike, p: IntLike, _K: Domain = ZZ): bigint[][] {
  return edfShoup(ints(f), Number(asInt(n)), asInt(p), rng());
}

/**
 * Factors a square-free monic polynomial by the Cantor–Zassenhaus algorithm.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The irreducible factors.
 * @see SymPy `sympy.polys.galoistools.gf_zassenhaus`
 * @example
 * ```ts
 * import { ZZ, gfZassenhaus } from '@symjs/symjs';
 *
 * gfZassenhaus([1, 4, 3], 5, ZZ); // => [[1, 1], [1, 3]]
 * ```
 */
export function gfZassenhaus(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return zassenhaus(ints(f), asInt(p));
}

/**
 * Factors a square-free monic polynomial using Shoup's algorithm.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @returns The irreducible factors.
 * @see SymPy `sympy.polys.galoistools.gf_shoup`
 * @example
 * ```ts
 * import { ZZ, gfShoup } from '@symjs/symjs';
 *
 * gfShoup([1, 4, 3], 5, ZZ); // => [[1, 1], [1, 3]]
 * ```
 */
export function gfShoup(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return shoup(ints(f), asInt(p));
}

/**
 * Factors a square-free polynomial over the prime field.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @param method - Algorithm to use.
 * @returns The leading coefficient and monic factors.
 * @see SymPy `sympy.polys.galoistools.gf_factor_sqf`
 * @remarks SymPy returns `(3, [[1, 1], [1, 3]])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfFactorSqf } from '@symjs/symjs';
 *
 * gfFactorSqf([3, 2, 4], 5, ZZ); // => [3, [[1, 1], [1, 3]]]
 * ```
 */
export function gfFactorSqf(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ, method?: GFFactorMethod): [bigint, bigint[][]] {
  return factorSqf(ints(f), asInt(p), method);
}

/**
 * Finds the irreducible factors over the prime field and counts their multiplicities.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param p - Prime modulus of the coefficient field.
 * @param _K - Integer coefficient domain, normally `ZZ`.
 * @param method - Algorithm to use.
 * @returns The leading coefficient and factor–multiplicity pairs.
 * @see SymPy `sympy.polys.galoistools.gf_factor`
 * @remarks SymPy returns `(5, [([1, 2], 1), ([1, 8], 2)])` with tuples for the fixed-length groups.
 * @example
 * ```ts
 * import { ZZ, gfFactor } from '@symjs/symjs';
 *
 * gfFactor([5, 2, 7, 2], 11, ZZ); // => [5, [[[1, 2], 1], [[1, 8], 2]]]
 * ```
 */
export function gfFactor(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ, method?: string): [bigint, [bigint[], number][]] {
  const m = asInt(p);
  const [lc, g] = monic(ints(f), m);
  if (g.length - 1 < 1) return [lc, []];
  const factors: [P, number][] = [];
  for (const [h, n] of sqfList(g, m)[1]) for (const q of factorSqf(h, m, method)[1]) factors.push([q, n]);
  return [lc, sortFactors(factors)];
}

/**
 * Evaluates the polynomial at an integer using integer arithmetic.
 *
 * @param f - Polynomial as coefficients in descending degree.
 * @param a - Evaluation point.
 * @returns The integer value.
 * @see SymPy `sympy.polys.galoistools.gf_value`
 * @example
 * ```ts
 * import { gfValue } from '@symjs/symjs';
 *
 * gfValue([1, 7, 2, 4], 11); // => 2204
 * ```
 */
export function gfValue(f: readonly IntLike[], a: IntLike): bigint {
  const x = asInt(a);
  return ints(f).reduce((r, c) => r * x + c, 0n);
}
