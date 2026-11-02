// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Factorization of square-free univariate integer polynomials
 * (Berlekamp-Zassenhaus: factorization modulo a prime by distinct- and
 * equal-degree factorization, Hensel lifting and recombination), the
 * algorithm behind SymPy's dup_zz_zassenhaus.
 *
 * Polynomials are bigint coefficient arrays, lowest degree first.
 */

import { NotImplementedError, NotInvertible } from '../core/errors';
import { at } from '../core/guard';

type P = bigint[];

const babs = (a: bigint) => (a < 0n ? -a : a);
const mod = (a: bigint, m: bigint) => ((a % m) + m) % m;

function trim(f: P): P {
  let n = f.length;
  while (n > 0 && f[n - 1] === 0n) n--;
  return f.slice(0, n);
}
const deg = (f: P) => trim(f).length - 1;

function modInv(a: bigint, m: bigint): bigint {
  let [r0, r1] = [mod(a, m), m];
  let [s0, s1] = [1n, 0n];
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1] = [r1, r0 - q * r1];
    [s0, s1] = [s1, s0 - q * s1];
  }
  if (r0 !== 1n) throw new NotInvertible('zassenhaus: not invertible');
  return mod(s0, m);
}

// ---- arithmetic modulo m ----------------------------------------------------

const pmod = (f: P, m: bigint): P => trim(f.map((c) => mod(c, m)));

function padd(f: P, g: P, m: bigint): P {
  const n = Math.max(f.length, g.length);
  return pmod(Array.from({ length: n }, (_, i) => (f[i] ?? 0n) + (g[i] ?? 0n)), m);
}
function psub(f: P, g: P, m: bigint): P {
  const n = Math.max(f.length, g.length);
  return pmod(Array.from({ length: n }, (_, i) => (f[i] ?? 0n) - (g[i] ?? 0n)), m);
}
function pmul(f: P, g: P, m: bigint): P {
  if (!f.length || !g.length) return [];
  const r: bigint[] = Array(f.length + g.length - 1).fill(0n);
  for (let i = 0; i < f.length; i++) {
    const fi = f[i];
    if (fi === undefined || fi === 0n) continue;
    let k = i;
    for (const gj of g) {
      r[k] = (r[k] ?? 0n) + fi * gj;
      k++;
    }
  }
  return pmod(r, m);
}
/** Division modulo a prime power m with a monic-invertible divisor. */
function pdivmod(f: P, g: P, m: bigint): [P, P] {
  const gg = trim(g);
  let r = pmod(f, m);
  const dg = gg.length - 1;
  if (dg < 0) throw new RangeError('zassenhaus: division by zero');
  const inv = modInv(at(gg, dg), m);
  const q: bigint[] = Array(Math.max(0, r.length - dg)).fill(0n);
  while (r.length - 1 >= dg && r.length) {
    const k = r.length - 1 - dg;
    const c = mod(at(r, -1) * inv, m);
    q[k] = c;
    let i = k;
    for (const gj of gg) {
      r[i] = mod((r[i] ?? 0n) - c * gj, m);
      i++;
    }
    r = trim(r);
  }
  return [trim(q), r];
}
const prem = (f: P, g: P, m: bigint) => pdivmod(f, g, m)[1];

function monic(f: P, m: bigint): P {
  const t = trim(f);
  if (!t.length) return t;
  const inv = modInv(at(t, -1), m);
  return pmod(t.map((c) => c * inv), m);
}

function pgcd(a0: P, b0: P, p: bigint): P {
  let a = pmod(a0, p);
  let b = pmod(b0, p);
  while (b.length) [a, b] = [b, prem(a, b, p)];
  return monic(a, p);
}

/** s, t with s*a + t*b = 1 modulo p (a, b coprime). */
function pgcdex(a0: P, b0: P, p: bigint): [P, P] {
  let [r0, r1] = [pmod(a0, p), pmod(b0, p)];
  let [s0, s1]: [P, P] = [[1n], []];
  let [t0, t1]: [P, P] = [[], [1n]];
  while (r1.length) {
    const [q, r] = pdivmod(r0, r1, p);
    [r0, r1] = [r1, r];
    [s0, s1] = [s1, psub(s0, pmul(q, s1, p), p)];
    [t0, t1] = [t1, psub(t0, pmul(q, t1, p), p)];
  }
  const inv = modInv(at(r0, 0), p);
  return [pmod(s0.map((c) => c * inv), p), pmod(t0.map((c) => c * inv), p)];
}

function ppowmod(f: P, e: bigint, g: P, p: bigint): P {
  let result: P = [1n];
  let base = prem(f, g, p);
  let k = e;
  while (k > 0n) {
    if (k & 1n) result = prem(pmul(result, base, p), g, p);
    base = prem(pmul(base, base, p), g, p);
    k >>= 1n;
  }
  return result;
}

const derivative = (f: P): P => trim(f.slice(1).map((c, i) => c * BigInt(i + 1)));

// ---- factorization modulo p ------------------------------------------------------

/** Distinct-degree factorization of a monic square-free f modulo p. */
function ddf(f0: P, p: bigint): [P, number][] {
  let f = f0;
  const out: [P, number][] = [];
  let h: P = [0n, 1n];
  for (let d = 1; 2 * d <= deg(f); d++) {
    h = ppowmod(h, p, f, p);
    const g = pgcd(f, psub(h, [0n, 1n], p), p);
    if (deg(g) > 0) {
      out.push([g, d]);
      f = pdivmod(f, g, p)[0];
      h = prem(h, f, p);
    }
  }
  if (deg(f) > 0) out.push([f, deg(f)]);
  return out;
}

let seed = 12345;
const rand = (m: bigint): bigint => {
  seed = (seed * 1103515245 + 12345) & 0x7fffffff;
  return BigInt(seed) % m;
};

/** Equal-degree factorization (Cantor-Zassenhaus) of f, a product of factors of degree d, modulo an odd prime p. */
function edf(f: P, d: number, p: bigint): P[] {
  const n = deg(f);
  if (n === d) return [monic(f, p)];
  for (let tries = 0; tries < 200; tries++) {
    const a = trim(Array.from({ length: n }, () => rand(p)));
    if (deg(a) < 1) continue;
    const e = (p ** BigInt(d) - 1n) / 2n;
    const b = psub(ppowmod(a, e, f, p), [1n], p);
    const g = pgcd(f, b, p);
    if (deg(g) > 0 && deg(g) < n) return [...edf(g, d, p), ...edf(pdivmod(f, g, p)[0], d, p)];
  }
  throw new NotImplementedError('zassenhaus: equal-degree factorization failed');
}

// ---- Hensel lifting ----------------------------------------------------------------

/**
 * Lift f = lc * prod(fs) modulo p to modulo p**l (multifactor Hensel
 * lifting by splitting into two halves).
 */
function henselLift(f: P, fs: P[], p: bigint, l: number): P[] {
  const m = p ** BigInt(l);
  if (fs.length === 1) {
    // the single factor is f made monic modulo p**l
    return [monic(pmod(f, m), m)];
  }
  const k = Math.floor(fs.length / 2);
  const left = fs.slice(0, k);
  const right = fs.slice(k);
  const lc = at(trim(f), -1);
  let g = left.reduce((acc, q) => pmul(acc, q, p), [mod(lc, p)] as P);
  let h = right.reduce((acc, q) => pmul(acc, q, p), [1n] as P);
  let [s, t] = pgcdex(g, h, p);
  // quadratic lifting of f = g*h
  let cur = p;
  while (cur < m) {
    const next = cur * cur > m ? m : cur * cur;
    const e = psub(pmod(f, next), pmul(g, h, next), next);
    const [q, r] = pdivmod(pmul(s, e, next), h, next);
    const g1 = padd(g, padd(pmul(t, e, next), pmul(q, g, next), next), next);
    const h1 = padd(h, r, next);
    const b = psub(padd(pmul(s, g1, next), pmul(t, h1, next), next), [1n], next);
    const [c, d] = pdivmod(pmul(s, b, next), h1, next);
    s = psub(s, d, next);
    t = psub(t, padd(pmul(t, b, next), pmul(c, g1, next), next), next);
    g = g1;
    h = h1;
    cur = next;
  }
  // g = lc * prod(left), h = prod(right) (monic) modulo m
  return [...henselLift(g, left, p, l), ...henselLift(h, right, p, l)];
}

// ---- driver --------------------------------------------------------------------------

const SMALL_PRIMES = [3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n, 43n, 47n, 53n, 59n, 61n, 67n, 71n, 73n, 79n, 83n, 89n, 97n, 101n, 103n, 107n, 109n, 113n];

function isqrtCeil(n: bigint): bigint {
  if (n < 2n) return n;
  let x = BigInt(Math.ceil(Math.sqrt(Number(n))));
  while (x * x < n) x++;
  while ((x - 1n) * (x - 1n) >= n) x--;
  return x;
}

/** Exact division over ZZ, or undefined. */
function zzDivExact(f: P, g: P): P | undefined {
  let r = trim([...f]);
  const gg = trim(g);
  const dg = gg.length - 1;
  const lg = at(gg, dg);
  const q: bigint[] = Array(Math.max(0, r.length - dg)).fill(0n);
  while (r.length - 1 >= dg && r.length) {
    const lr = at(r, -1);
    if (lr % lg !== 0n) return undefined;
    const c = lr / lg;
    const k = r.length - 1 - dg;
    q[k] = c;
    let i = k;
    for (const gj of gg) {
      r[i] = (r[i] ?? 0n) - c * gj;
      i++;
    }
    r = trim(r);
  }
  return r.length ? undefined : trim(q);
}

function primitivePart(f: P): P {
  let g = 0n;
  for (const c of f) {
    let a = babs(c);
    let b = g;
    while (b) [a, b] = [b, a % b];
    g = a;
  }
  const t = trim(f);
  const sign = t.length && at(t, -1) < 0n ? -1n : 1n;
  return g ? t.map((c) => (sign * c) / g) : t;
}

/**
 * Irreducible factors over ZZ of a primitive square-free integer polynomial
 * of degree >= 1 (positive leading coefficient), lowest degree first.
 */
export function zassenhaus(f0: P): P[] {
  const f = primitivePart(f0);
  const n = deg(f);
  if (n <= 1) return [f];
  const lc = at(f, n);
  // a prime keeping the degree and square-freeness
  let p = 0n;
  for (const q of SMALL_PRIMES) {
    if (lc % q === 0n) continue;
    const fp = pmod(f, q);
    if (deg(fp) !== n) continue;
    if (deg(pgcd(fp, derivative(fp), q)) !== 0) continue;
    p = q;
    break;
  }
  if (!p) throw new NotImplementedError('zassenhaus: no suitable prime');
  const fpm = monic(pmod(f, p), p);
  const modFactors: P[] = [];
  for (const [g, d] of ddf(fpm, p)) modFactors.push(...edf(g, d, p));
  if (modFactors.length === 1) return [f];
  // Mignotte bound for the coefficients of a factor, times lc
  const norm = isqrtCeil(f.reduce((s, c) => s + c * c, 0n));
  const bound = 2n * babs(lc) * (1n << BigInt(n)) * norm;
  let l = 1;
  while (p ** BigInt(l) <= bound) l++;
  const m = p ** BigInt(l);
  const lifted = henselLift(f, modFactors, p, l);
  // recombination
  const sym = (c: bigint) => {
    const r = mod(c, m);
    return r > m / 2n ? r - m : r;
  };
  let rest = f;
  let remaining = lifted;
  const out: P[] = [];
  let size = 1;
  while (2 * size <= remaining.length) {
    let found = false;
    const idx = Array.from({ length: size }, (_, i) => i);
    for (;;) {
      const lcr = at(trim(rest), -1);
      const prod = idx.reduce((acc, i) => pmul(acc, at(remaining, i), m), [mod(lcr, m)] as P);
      const cand = primitivePart(prod.map(sym));
      const q = deg(cand) > 0 ? zzDivExact(rest, cand) : undefined;
      if (q) {
        out.push(cand);
        rest = q;
        remaining = remaining.filter((_, i) => !idx.includes(i));
        found = true;
        break;
      }
      // next combination
      let i = size - 1;
      while (i >= 0 && idx[i] === remaining.length - size + i) i--;
      if (i < 0) break;
      idx[i] = at(idx, i) + 1;
      for (let j = i + 1; j < size; j++) idx[j] = at(idx, j - 1) + 1;
    }
    if (!found) size++;
  }
  out.push(primitivePart(rest));
  return out;
}

// ---- factorization over GF(p) ------------------------------------------------------

/** Equal-degree factorization modulo 2 (trace map instead of the (p**d - 1)/2 power). */
function edf2(f: P, d: number): P[] {
  const n = deg(f);
  if (n === d) return [monic(f, 2n)];
  for (let tries = 0; tries < 400; tries++) {
    const a = trim(Array.from({ length: n }, () => rand(2n)));
    if (deg(a) < 1) continue;
    // b = a + a**2 + a**4 + ... + a**(2**(d - 1)) mod f
    let t = a;
    let b = a;
    for (let i = 1; i < d; i++) {
      t = prem(pmul(t, t, 2n), f, 2n);
      b = padd(b, t, 2n);
    }
    const g = pgcd(f, b, 2n);
    if (deg(g) > 0 && deg(g) < n) return [...edf2(g, d), ...edf2(pdivmod(f, g, 2n)[0], d)];
  }
  throw new NotImplementedError('factorModP: equal-degree factorization failed');
}

/** Square-free decomposition modulo p (SymPy gf_sqf_list): [factor, multiplicity] of a monic f. */
function sqfListModP(f0: P, p: bigint): [P, number][] {
  const out: [P, number][] = [];
  let f = monic(f0, p);
  let n = 1;
  if (deg(f) < 1) return out;
  for (;;) {
    let sqf = false;
    const F = pmod(derivative(f), p);
    if (F.length) {
      let g = pgcd(f, F, p);
      let h = pdivmod(f, g, p)[0];
      let i = 1;
      while (!(h.length === 1 && h[0] === 1n)) {
        const G = pgcd(g, h, p);
        const H = pdivmod(h, G, p)[0];
        if (deg(H) > 0) out.push([monic(H, p), i * n]);
        g = pdivmod(g, G, p)[0];
        h = G;
        i++;
      }
      if (g.length === 1 && g[0] === 1n) sqf = true;
      else f = g;
    }
    if (sqf) break;
    // f is a p-th power: take the p-th root (coefficients at multiples of p)
    const r = Number(p);
    const d = Math.floor(deg(f) / r);
    f = Array.from({ length: d + 1 }, (_, i) => f[i * r] ?? 0n);
    n *= r;
  }
  return out;
}

/**
 * Factorization of an integer polynomial over GF(p), p prime (coefficients
 * lowest degree first): the leading coefficient modulo p and the monic
 * irreducible factors with their multiplicities.
 */
export function factorModP(f0: P, p: bigint): [bigint, [P, number][]] {
  const f = pmod(f0, p);
  if (!f.length) return [0n, []];
  const lc = at(f, -1);
  const out: [P, number][] = [];
  for (const [g, m] of sqfListModP(f, p)) {
    for (const [h, d] of ddf(g, p)) {
      for (const irr of p === 2n ? edf2(h, d) : edf(h, d, p)) out.push([irr, m]);
    }
  }
  return [lc, out];
}
