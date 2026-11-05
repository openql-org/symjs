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

/** The factorization methods of gfFactorSqf (SymPy GF_FACTOR_METHOD). */
export type GFFactorMethod = 'berlekamp' | 'zassenhaus' | 'shoup';
const FACTOR_METHODS: Readonly<Record<GFFactorMethod, (f: P, p: bigint) => P[]>> = { berlekamp, zassenhaus, shoup };

function factorSqf(fIn: P, p: bigint, method: GFFactorMethod = 'zassenhaus'): [bigint, P[]] {
  const [lc, f] = monic(fIn, p);
  if (f.length - 1 < 1) return [lc, []];
  return [lc, FACTOR_METHODS[method](f, p)];
}

// ---------------------------------------------------------------------------
// public API (SymPy names)
// ---------------------------------------------------------------------------

/** Chinese remainder theorem: the integer congruent to U[i] modulo M[i] (SymPy gf_crt). */
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

/** The first part of the Chinese remainder theorem: [p, E, S] (SymPy gf_crt1). */
export function gfCrt1(M: readonly IntLike[], _K: Domain = ZZ): [bigint, bigint[], bigint[]] {
  const ms = ints(M);
  const p = ms.reduce((a, b) => a * b, 1n);
  const E = ms.map((m) => p / m);
  const S = ms.map((m, i) => mod(igcdex(at(E, i), m)[0], m));
  return [p, E, S];
}

/** The second part of the Chinese remainder theorem (SymPy gf_crt2). */
export function gfCrt2(U: readonly IntLike[], M: readonly IntLike[], p: IntLike, E: readonly IntLike[], S: readonly IntLike[], _K: Domain = ZZ): bigint {
  const [us, ms, es, ss] = [ints(U), ints(M), ints(E), ints(S)];
  let v = 0n;
  us.forEach((u, i) => (v += at(es, i) * mod(u * at(ss, i), at(ms, i))));
  return mod(v, asInt(p));
}

/** The symmetric representative of a modulo p, in (-p/2, p/2] (SymPy gf_int). */
export function gfInt(a: IntLike, p: IntLike): bigint {
  const [x, m] = [asInt(a), asInt(p)];
  return x <= m / 2n ? x : x - m;
}

/** The degree of f; -1 for the zero polynomial (SymPy gf_degree). */
export function gfDegree(f: readonly IntLike[]): number {
  return f.length - 1;
}

/** The leading coefficient (SymPy gf_LC). */
export function gfLC(f: readonly IntLike[], _K: Domain = ZZ): bigint {
  return f.length ? asInt(at(f, 0)) : 0n;
}

/** The trailing coefficient (SymPy gf_TC). */
export function gfTC(f: readonly IntLike[], _K: Domain = ZZ): bigint {
  return f.length ? asInt(at(f, -1)) : 0n;
}

/** f without leading zeros (SymPy gf_strip). */
export function gfStrip(f: readonly IntLike[]): bigint[] {
  return strip(ints(f));
}

/** f with its coefficients reduced modulo p (SymPy gf_trunc). */
export function gfTrunc(f: readonly IntLike[], p: IntLike): bigint[] {
  return trunc(ints(f), asInt(p));
}

/** f with its coefficients converted to K and reduced modulo p (SymPy gf_normal). */
export function gfNormal(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return trunc(ints(f), asInt(p));
}

/** The polynomial of a {degree: coefficient} map, reduced modulo p (SymPy gf_from_dict). */
export function gfFromDict(f: ReadonlyMap<IntLike | readonly IntLike[], IntLike>, p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  // a key is a degree or a 1-tuple of it
  const terms = new Map([...f].map(([k, c]) => [Number(isSeq(k) ? asInt(at(k, 0)) : asInt(k)), asInt(c)]));
  const n = Math.max(...terms.keys());
  const h: P = [];
  for (let k = n; k >= 0; k--) h.push(mod(terms.get(k) ?? 0n, m));
  return trunc(h, m);
}

/** The {degree: coefficient} map of f, with symmetric coefficients by default (SymPy gf_to_dict). */
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

/** An integer polynomial reduced modulo p (SymPy gf_from_int_poly). */
export function gfFromIntPoly(f: readonly IntLike[], p: IntLike): bigint[] {
  return trunc(ints(f), asInt(p));
}

/** The integer polynomial of f, with symmetric coefficients by default (SymPy gf_to_int_poly). */
export function gfToIntPoly(f: readonly IntLike[], p: IntLike, symmetric = true): bigint[] {
  return symmetric ? f.map((c) => gfInt(c, p)) : ints(f);
}

/** -f (SymPy gf_neg). */
export function gfNeg(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return neg(ints(f), asInt(p));
}

/** f + a for a ground element a (SymPy gf_add_ground). */
export function gfAddGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return addGround(ints(f), asInt(a), asInt(p));
}

/** f - a for a ground element a (SymPy gf_sub_ground). */
export function gfSubGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return subGround(ints(f), asInt(a), asInt(p));
}

/** f * a for a ground element a (SymPy gf_mul_ground). */
export function gfMulGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return mulGround(ints(f), asInt(a), asInt(p));
}

/** f / a for a ground element a (SymPy gf_quo_ground). */
export function gfQuoGround(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return quoGround(ints(f), asInt(a), asInt(p));
}

/** f + g (SymPy gf_add). */
export function gfAdd(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return add(ints(f), ints(g), asInt(p));
}

/** f - g (SymPy gf_sub). */
export function gfSub(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return sub(ints(f), ints(g), asInt(p));
}

/** f * g (SymPy gf_mul). */
export function gfMul(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return mul(ints(f), ints(g), asInt(p));
}

/** f**2 (SymPy gf_sqr). */
export function gfSqr(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return sqr(ints(f), asInt(p));
}

/** f + g*h (SymPy gf_add_mul). */
export function gfAddMul(f: readonly IntLike[], g: readonly IntLike[], h: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  return add(ints(f), mul(ints(g), ints(h), m), m);
}

/** f - g*h (SymPy gf_sub_mul). */
export function gfSubMul(f: readonly IntLike[], g: readonly IntLike[], h: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  return sub(ints(f), mul(ints(g), ints(h), m), m);
}

/** The product of a factorization [[f, k], ...] or [lc, [[f, k], ...]] (SymPy gf_expand). */
export function gfExpand(F: GFFactorization | readonly [IntLike, GFFactorization], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  const [lc, fs] = hasLc(F) ? [asInt(F[0]), F[1]] : [1n, F];
  let g: P = [lc];
  for (const [f, k] of fs) g = mul(g, pow(ints(f), asInt(k), m), m);
  return g;
}

/** Division with remainder: [quotient, remainder] (SymPy gf_div). */
export function gfDiv(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[]] {
  return div(ints(f), ints(g), asInt(p));
}

/** The remainder of f / g (SymPy gf_rem). */
export function gfRem(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return rem(ints(f), ints(g), asInt(p));
}

/** The quotient of f / g (SymPy gf_quo). */
export function gfQuo(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return quo(ints(f), ints(g), asInt(p));
}

/** The exact quotient f / g; throws ExactQuotientFailed when g does not divide f (SymPy gf_exquo). */
export function gfExquo(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [q, r] = div(ints(f), ints(g), asInt(p));
  if (r.length) throw new ExactQuotientFailed(`[${f.join(', ')}] does not divide [${g.join(', ')}]`);
  return q;
}

/** f * x**n (SymPy gf_lshift). */
export function gfLshift(f: readonly IntLike[], n: IntLike, _K: Domain = ZZ): bigint[] {
  const cs = ints(f);
  return cs.length ? [...cs, ...Array.from({ length: Number(asInt(n)) }, () => 0n)] : cs;
}

/** [f // x**n, f % x**n] (SymPy gf_rshift). */
export function gfRshift(f: readonly IntLike[], n: IntLike, _K: Domain = ZZ): [bigint[], bigint[]] {
  const cs = ints(f);
  const k = Number(asInt(n));
  return k ? [cs.slice(0, -k), cs.slice(-k)] : [cs, []];
}

/** f**n by repeated squaring (SymPy gf_pow). */
export function gfPow(f: readonly IntLike[], n: IntLike, p: IntLike, _K: Domain = ZZ): bigint[] {
  return pow(ints(f), asInt(n), asInt(p));
}

/** The powers x**(i*p) modulo g, i = 0 .. deg(g) - 1 (SymPy gf_frobenius_monomial_base). */
export function gfFrobeniusMonomialBase(g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return frobeniusMonomialBase(ints(g), asInt(p));
}

/** f**p modulo g from the Frobenius monomial base b (SymPy gf_frobenius_map). */
export function gfFrobeniusMap(f: readonly IntLike[], g: readonly IntLike[], b: readonly (readonly IntLike[])[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return frobeniusMap(ints(f), ints(g), b.map(ints), asInt(p));
}

/** f**n modulo g (SymPy gf_pow_mod). */
export function gfPowMod(f: readonly IntLike[], n: IntLike, g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  const k = asInt(n);
  return k === 0n ? [1n] : powMod(rem(ints(f), ints(g), m), k, ints(g), m);
}

/** The monic gcd (SymPy gf_gcd). */
export function gfGcd(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return gcd(ints(f), ints(g), asInt(p));
}

/** The monic lcm (SymPy gf_lcm). */
export function gfLcm(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (!a.length || !b.length) return [];
  return monic(quo(mul(a, b, m), gcd(a, b, m), m), m)[1];
}

/** [gcd, f / gcd, g / gcd] (SymPy gf_cofactors). */
export function gfCofactors(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[], bigint[]] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (!a.length && !b.length) return [[], [], []];
  const h = gcd(a, b, m);
  return [h, quo(a, h, m), quo(b, h, m)];
}

/** The extended Euclidean algorithm: [s, t, h] with s*f + t*g = h = gcd(f, g) (SymPy gf_gcdex). */
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

/** [lc, f / lc] (SymPy gf_monic). */
export function gfMonic(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint, bigint[]] {
  return monic(ints(f), asInt(p));
}

/** The derivative (SymPy gf_diff). */
export function gfDiff(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return diff(ints(f), asInt(p));
}

/** f(a) by Horner's scheme (SymPy gf_eval). */
export function gfEval(f: readonly IntLike[], a: IntLike, p: IntLike, _K: Domain = ZZ): bigint {
  return evalAt(ints(f), asInt(a), asInt(p));
}

/** f at every point of A (SymPy gf_multi_eval). */
export function gfMultiEval(f: readonly IntLike[], A: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [cs, m] = [ints(f), asInt(p)];
  return A.map((a) => evalAt(cs, asInt(a), m));
}

/** The composition f(g) (SymPy gf_compose). */
export function gfCompose(f: readonly IntLike[], g: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const [a, b, m] = [ints(f), ints(g), asInt(p)];
  if (b.length <= 1) return strip([evalAt(a, b.length ? at(b, 0) : 0n, m)]);
  if (!a.length) return [];
  let h: P = [at(a, 0)];
  for (const c of a.slice(1)) h = addGround(mul(h, b, m), c, m);
  return h;
}

/** The composition g(h) modulo f (SymPy gf_compose_mod). */
export function gfComposeMod(g: readonly IntLike[], h: readonly IntLike[], f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  return composeMod(ints(g), ints(h), ints(f), asInt(p));
}

/** The trace map [a(b**(p**n)) ... ] modulo f used by Shoup's algorithm (SymPy gf_trace_map). */
export function gfTraceMap(a: readonly IntLike[], b: readonly IntLike[], c: readonly IntLike[], n: IntLike, f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], bigint[]] {
  return traceMap(ints(a), ints(b), ints(c), asInt(n), ints(f), asInt(p));
}

/** A random monic polynomial of degree n (SymPy gf_random); `random` returns integers in [0, bound). */
export function gfRandom(n: IntLike, p: IntLike, _K: Domain = ZZ, random: (bound: bigint) => bigint = rng(BigInt(Date.now()) | 1n)): bigint[] {
  return randomPoly(Number(asInt(n)), asInt(p), random);
}

/** A random monic irreducible polynomial of degree n (SymPy gf_irreducible). */
export function gfIrreducible(n: IntLike, p: IntLike, K: Domain = ZZ, random?: (bound: bigint) => bigint): bigint[] {
  const m = asInt(p);
  for (;;) {
    const f = gfRandom(n, m, K, random);
    if (irredRabin(f, m)) return f;
  }
}

/** Ben-Or's irreducibility test (SymPy gf_irred_p_ben_or). */
export function gfIrredPBenOr(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  return irredBenOr(ints(f), asInt(p));
}

/** Rabin's irreducibility test (SymPy gf_irred_p_rabin). */
export function gfIrredPRabin(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  return irredRabin(ints(f), asInt(p));
}

/** Whether f is irreducible over GF(p) (SymPy gf_irreducible_p, Rabin's test). */
export function gfIrreducibleP(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  return irredRabin(ints(f), asInt(p));
}

/** Whether f is square-free (SymPy gf_sqf_p). */
export function gfSqfP(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): boolean {
  const m = asInt(p);
  const g = monic(ints(f), m)[1];
  return !g.length || isOne(gcd(g, diff(g, m), m));
}

/** The square-free part (SymPy gf_sqf_part). */
export function gfSqfPart(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[] {
  const m = asInt(p);
  return sqfList(ints(f), m)[1].reduce<P>((g, [h]) => mul(g, h, m), [1n]);
}

/** The square-free decomposition [lc, [[factor, multiplicity], ...]] (SymPy gf_sqf_list). */
export function gfSqfList(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ, opts: { all?: boolean } = {}): [bigint, [bigint[], number][]] {
  if (opts.all === true) throw new RangeError("'all=True' is not supported yet");
  return sqfList(ints(f), asInt(p));
}

/** Berlekamp's Q matrix (SymPy gf_Qmatrix). */
export function gfQmatrix(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return qMatrix(ints(f), asInt(p));
}

/** A basis of the kernel of Q - I (SymPy gf_Qbasis). */
export function gfQbasis(Q: readonly (readonly IntLike[])[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return qBasis(Q.map(ints), asInt(p));
}

/** Berlekamp's factorization of a square-free monic polynomial (SymPy gf_berlekamp). */
export function gfBerlekamp(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return berlekamp(ints(f), asInt(p));
}

/** Distinct-degree factorization, Cantor-Zassenhaus (SymPy gf_ddf_zassenhaus). */
export function gfDdfZassenhaus(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], number][] {
  return ddfZassenhaus(ints(f), asInt(p));
}

/** Equal-degree factorization, Cantor-Zassenhaus (SymPy gf_edf_zassenhaus). */
export function gfEdfZassenhaus(f: readonly IntLike[], n: IntLike, p: IntLike, _K: Domain = ZZ): bigint[][] {
  return edfZassenhaus(ints(f), Number(asInt(n)), asInt(p), rng());
}

/** Distinct-degree factorization, Kaltofen-Shoup (SymPy gf_ddf_shoup). */
export function gfDdfShoup(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint[], number][] {
  return ddfShoup(ints(f), asInt(p));
}

/** Equal-degree factorization, Gathen-Shoup (SymPy gf_edf_shoup). */
export function gfEdfShoup(f: readonly IntLike[], n: IntLike, p: IntLike, _K: Domain = ZZ): bigint[][] {
  return edfShoup(ints(f), Number(asInt(n)), asInt(p), rng());
}

/** Factorization of a square-free monic polynomial by Cantor-Zassenhaus (SymPy gf_zassenhaus). */
export function gfZassenhaus(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return zassenhaus(ints(f), asInt(p));
}

/** Factorization of a square-free monic polynomial by Shoup's method (SymPy gf_shoup). */
export function gfShoup(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): bigint[][] {
  return shoup(ints(f), asInt(p));
}

/** Factorization of a square-free polynomial: [lc, factors] (SymPy gf_factor_sqf). */
export function gfFactorSqf(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ, method?: GFFactorMethod): [bigint, bigint[][]] {
  return factorSqf(ints(f), asInt(p), method);
}

/** Factorization into irreducibles: [lc, [[factor, multiplicity], ...]] (SymPy gf_factor). */
export function gfFactor(f: readonly IntLike[], p: IntLike, _K: Domain = ZZ): [bigint, [bigint[], number][]] {
  const m = asInt(p);
  const [lc, g] = monic(ints(f), m);
  if (g.length - 1 < 1) return [lc, []];
  const factors: [P, number][] = [];
  for (const [h, n] of sqfList(g, m)[1]) for (const q of factorSqf(h, m)[1]) factors.push([q, n]);
  return [lc, sortFactors(factors)];
}

/** f(a) over the integers (SymPy gf_value). */
export function gfValue(f: readonly IntLike[], a: IntLike): bigint {
  const x = asInt(a);
  return ints(f).reduce((r, c) => r * x + c, 0n);
}
