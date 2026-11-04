// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (identification.py: pslq, findpoly, identify),
// Copyright (c) 2005-2023 Fredrik Johansson and mpmath contributors,
// BSD 3-Clause License (see LICENSE).

/**
 * @file Integer relations and closed forms of numbers: PSLQ, findpoly and
 * identify (mpmath), which SymPy's nsimplify uses. Values are Mpf numbers and
 * `prec` plays the role of mpmath's working precision `mp.prec`; identify
 * returns formulas as strings, like mpmath.
 */

import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE } from './mpf';
import * as M from './mpfun';
import { at, expectType } from '../core/guard';

const babs = (n: bigint): bigint => (n < 0n ? -n : n);
const nonzero = (v: unknown): v is bigint => typeof v === 'bigint' && v !== 0n;

/** Python floor division a // b. */
function fdiv(a: bigint, b: bigint): bigint {
  const q = a / b;
  return a % b !== 0n && a < 0n !== b < 0n ? q - 1n : q;
}

/** Python a % b (the sign of b). */
function pmod(a: bigint, b: bigint): bigint {
  const r = a % b;
  return r !== 0n && r < 0n !== b < 0n ? r + b : r;
}

const sqrtFixed = (x: bigint, prec: number): bigint => F.isqrt(x << BigInt(prec));
const roundFixed = (x: bigint, prec: number): bigint => ((x + (1n << BigInt(prec - 1))) >> BigInt(prec)) << BigInt(prec);

/**
 * An integer relation a_1 x_1 + ... + a_n x_n = 0 with |a_i| < maxcoeff found
 * by PSLQ at working precision prec (mpmath pslq), or undefined. `tol`
 * defaults to 2**(-3/4 prec).
 */
export function pslq(xs: readonly Mpf[], prec: number, tolIn?: Mpf, maxcoeff = 1000, maxsteps = 100): bigint[] | undefined {
  const n = xs.length;
  if (n < 2) throw new RangeError('n cannot be less than 2');
  if (prec < 53) throw new RangeError('prec cannot be less than 53');
  const target = Math.trunc(prec * 0.75);
  const tolMpf = tolIn ?? { man: 1n, exp: BigInt(-target) };
  const wp = prec + 60;
  const P = BigInt(wp);
  const tol = F.toFixed(tolMpf, wp);
  if (tol === 0n) throw new RangeError('pslq: tolerance too small');
  const x: bigint[] = [0n, ...xs.map((xk) => F.toFixed(F.round(xk, prec), wp))];
  const minx = x.slice(2).reduce((m, v) => (babs(v) < m ? babs(v) : m), babs(at(x, 1)));
  if (minx === 0n) throw new RangeError('PSLQ requires a vector of nonzero numbers');
  if (minx < fdiv(tol, 100n)) return undefined;
  const g = sqrtFixed(fdiv(4n << P, 3n), wp);
  const one = 1n << P;
  const mat = (): bigint[][] => Array.from({ length: n + 1 }, () => new Array<bigint>(n + 1).fill(0n));
  const A = mat();
  const B = mat();
  const H = mat();
  const get = (m: bigint[][], i: number, j: number): bigint => at(at(m, i), j);
  const set = (m: bigint[][], i: number, j: number, v: bigint): void => {
    at(m, i)[j] = v;
  };
  for (let i = 1; i <= n; i++) {
    set(A, i, i, one);
    set(B, i, i, one);
  }
  // s_k = |(x_k, ..., x_n)|, nonzero since every x_j is
  const s: bigint[] = new Array<bigint>(n + 1).fill(0n);
  for (let k = 1; k <= n; k++) {
    let t = 0n;
    for (let j = k; j <= n; j++) t += (at(x, j) ** 2n) >> P;
    s[k] = sqrtFixed(t, wp);
  }
  const t1 = at(s, 1);
  const y = [...x];
  for (let k = 1; k <= n; k++) {
    y[k] = fdiv(at(x, k) << P, t1);
    s[k] = fdiv(at(s, k) << P, t1);
  }
  const yk = (k: number): bigint => at(y, k);
  for (let i = 1; i <= n; i++) {
    if (i <= n - 1) set(H, i, i, fdiv(at(s, i + 1) << P, at(s, i)));
    for (let j = 1; j < i; j++) set(H, i, j, fdiv((-yk(i) * yk(j)) << P, at(s, j) * at(s, j + 1)));
  }
  /** Row i minus t times row j (H, A) and the matching column update of B and y. */
  const reduce = (i: number, j: number, t: bigint): void => {
    y[j] = yk(j) + ((t * yk(i)) >> P);
    for (let k = 1; k <= j; k++) set(H, i, k, get(H, i, k) - ((t * get(H, j, k)) >> P));
    for (let k = 1; k <= n; k++) {
      set(A, i, k, get(A, i, k) - ((t * get(A, j, k)) >> P));
      set(B, k, j, get(B, k, j) + ((t * get(B, k, i)) >> P));
    }
  };
  // H[j][j] = s_(j+1)/s_j is nonzero here
  for (let i = 2; i <= n; i++) for (let j = i - 1; j > 0; j--) reduce(i, j, roundFixed(fdiv(get(H, i, j) << P, get(H, j, j)), wp));
  for (let rep = 0; rep < maxsteps; rep++) {
    let m = -1;
    let szmax = -1n;
    for (let i = 1; i < n; i++) {
      const sz = (g ** BigInt(i) * babs(get(H, i, i))) >> (P * BigInt(i - 1));
      if (sz > szmax) {
        m = i;
        szmax = sz;
      }
    }
    [y[m], y[m + 1]] = [yk(m + 1), yk(m)];
    for (let i = 1; i <= n; i++) {
      const [h1, h2] = [get(H, m, i), get(H, m + 1, i)];
      set(H, m, i, h2);
      set(H, m + 1, i, h1);
      const [a1, a2] = [get(A, m, i), get(A, m + 1, i)];
      set(A, m, i, a2);
      set(A, m + 1, i, a1);
      const [b1, b2] = [get(B, i, m), get(B, i, m + 1)];
      set(B, i, m, b2);
      set(B, i, m + 1, b1);
    }
    if (m <= n - 2) {
      // PSLQ keeps H[j][j] != 0 for j < n - 1 (H has rank n - 1), so the rotated pair is nonzero
      const t0 = expectType(sqrtFixed((get(H, m, m) ** 2n + get(H, m, m + 1) ** 2n) >> P, wp), nonzero, 'PSLQ rotation norm');
      const c1 = fdiv(get(H, m, m) << P, t0);
      const c2 = fdiv(get(H, m, m + 1) << P, t0);
      for (let i = m; i <= n; i++) {
        const t3 = get(H, i, m);
        const t4 = get(H, i, m + 1);
        set(H, i, m, (c1 * t3 + c2 * t4) >> P);
        set(H, i, m + 1, (-c2 * t3 + c1 * t4) >> P);
      }
    }
    for (let i = m + 1; i <= n; i++) {
      for (let j = Math.min(i - 1, m + 1); j > 0; j--) {
        if (get(H, j, j) === 0n) break;
        reduce(i, j, roundFixed(fdiv(get(H, i, j) << P, get(H, j, j)), wp));
      }
    }
    for (let i = 1; i <= n; i++) {
      if (babs(yk(i)) < tol) {
        const vec = Array.from({ length: n }, (_, j) => roundFixed(get(B, j + 1, i), wp) >> P);
        if (vec.every((v) => babs(v) < BigInt(maxcoeff))) return vec;
      }
    }
    let recnorm = 0n;
    for (const r of H) for (const h of r) if (babs(h) > recnorm) recnorm = babs(h);
    // the norm bound (H has rank n - 1, so it does not vanish)
    if (fdiv(fdiv(1n << (2n * P), expectType(recnorm, nonzero, 'PSLQ norm')) >> P, 100n) >= BigInt(maxcoeff)) break;
  }
  return undefined;
}

/** Integer coefficients [c_n, ..., c_0] of a polynomial of degree <= n with root x (mpmath findpoly), or undefined. */
export function findpoly(x: Mpf, n: number, prec: number, maxcoeff = 1000): bigint[] | undefined {
  const xr = F.round(x, prec);
  if (F.isZero(xr)) return [1n, 0n];
  const xs: Mpf[] = [ONE];
  for (let i = 1; i <= n; i++) {
    xs.push(F.powInt(xr, BigInt(i), prec));
    const a = pslq(xs, prec, undefined, maxcoeff);
    if (a) return a.reverse();
  }
  return undefined;
}

/** p/q in lowest terms: an integer string or a [p, q] pair (mpmath fracgcd). */
function fracgcd(pIn: bigint, qIn: bigint): bigint | [bigint, bigint] {
  let [x, y] = [pIn, qIn];
  while (y !== 0n) [x, y] = [y, pmod(x, y)];
  let [p, q] = [pIn, qIn];
  if (x !== 1n) {
    p = fdiv(p, x);
    q = fdiv(q, x);
  }
  return q === 1n ? p : [p, q];
}

type Named = readonly [Mpf, string];

function pslqstring(r: readonly bigint[], constants: readonly Named[]): string {
  const q = at(r, 0);
  const terms: string[] = [];
  r.slice(1).forEach((p, i) => {
    if (p === 0n) return;
    const z = fracgcd(-p, q);
    const name = at(constants, i)[1];
    const cs = name === '1' ? '' : `*${name}`;
    if (typeof z === 'bigint') terms.push(z > 0n ? `${z}${cs}` : `(${z})${cs}`);
    else terms.push(`(${z[0]}/${z[1]})${cs}`);
  });
  const s = terms.join(' + ');
  // r[0] != 0 and t != 0, so some other coefficient is nonzero and s is not empty
  return s.includes('+') || s.includes('*') ? `(${s})` : s;
}

function prodstring(r: readonly bigint[], constants: readonly Named[]): string {
  const q = at(r, 0);
  const num: string[] = [];
  const den: string[] = [];
  r.slice(1).forEach((p, i) => {
    if (p === 0n) return;
    const z = fracgcd(-p, q);
    const cs = at(constants, i)[1];
    if (typeof z === 'bigint') (z < 0n ? den : num).push(babs(z) === 1n ? cs : `${cs}**${babs(z)}`);
    else (z[0] < 0n ? den : num).push(`${cs}**(${babs(z[0])}/${z[1]})`);
  });
  const ns = num.join('*');
  const ds = den.join('*');
  if (ns && ds) return `(${ns})/(${ds})`;
  return ns || `1/(${ds})`;
}

function quadraticstring(t: Mpf, aIn: bigint, bIn: bigint, cIn: bigint, prec: number): string {
  const [a, b, c] = cIn < 0n ? [-aIn, -bIn, -cIn] : [aIn, bIn, cIn];
  const disc = b * b - 4n * a * c;
  // the roots (-b +- sqrt(disc))/(2c) (disc >= 0: t is a real root)
  const sq = F.sqrt(F.fromInt(disc), prec);
  const mb = F.fromInt(-b);
  const c2 = F.fromInt(2n * c);
  const dist = (s: Mpf): Mpf => F.abs(F.sub(F.div(F.add(mb, s, prec), c2, prec), t, prec));
  if (F.cmp(dist(sq), dist(F.neg(sq))) < 0) return b !== 0n ? `((${-b}+sqrt(${disc}))/${2n * c})` : `(sqrt(${-4n * a * c})/${2n * c})`;
  return b !== 0n ? `((${-b}-sqrt(${disc}))/${2n * c})` : `(-sqrt(${-4n * a * c})/${2n * c})`;
}

type Transform = readonly [(x: Mpf, c: Mpf, p: number) => Mpf, string, boolean];

const sq = (v: Mpf, p: number): Mpf => F.mul(v, v, p);
const TRANSFORMS: readonly Transform[] = [
  [(x, c, p) => F.mul(x, c, p), '$y/$c', false],
  [(x, c, p) => F.div(x, c, p), '$c*$y', true],
  [(x, c, p) => F.div(c, x, p), '$c/$y', false],
  [(x, c, p) => sq(F.mul(x, c, p), p), 'sqrt($y)/$c', false],
  [(x, c, p) => sq(F.div(x, c, p), p), '$c*sqrt($y)', true],
  [(x, c, p) => sq(F.div(c, x, p), p), '$c/sqrt($y)', false],
  [(x, c, p) => F.mul(c, sq(x, p), p), 'sqrt($y)/sqrt($c)', true],
  [(x, c, p) => F.div(sq(x, p), c, p), 'sqrt($c)*sqrt($y)', true],
  [(x, c, p) => F.div(c, sq(x, p), p), 'sqrt($c)/sqrt($y)', true],
  [(x, c, p) => F.sqrt(F.mul(x, c, p), p), '$y**2/$c', false],
  [(x, c, p) => F.sqrt(F.div(x, c, p), p), '$c*$y**2', true],
  [(x, c, p) => F.sqrt(F.div(c, x, p), p), '$c/$y**2', false],
  [(x, c, p) => F.mul(c, F.sqrt(x, p), p), '$y**2/$c**2', true],
  [(x, c, p) => F.div(F.sqrt(x, p), c, p), '$c**2*$y**2', true],
  [(x, c, p) => F.div(c, F.sqrt(x, p), p), '$c**2/$y**2', true],
  [(x, c, p) => M.exp(F.mul(x, c, p), p), 'log($y)/$c', false],
  [(x, c, p) => M.exp(F.div(x, c, p), p), '$c*log($y)', true],
  [(x, c, p) => M.exp(F.div(c, x, p), p), '$c/log($y)', false],
  [(x, c, p) => F.mul(c, M.exp(x, p), p), 'log($y/$c)', true],
  [(x, c, p) => F.div(M.exp(x, p), c, p), 'log($c*$y)', true],
  [(x, c, p) => F.div(c, M.exp(x, p), p), 'log($c/$y)', false],
  [(x, c, p) => M.log(F.mul(x, c, p), p), 'exp($y)/$c', false],
  [(x, c, p) => M.log(F.div(x, c, p), p), '$c*exp($y)', true],
  [(x, c, p) => M.log(F.div(c, x, p), p), '$c/exp($y)', false],
  [(x, c, p) => F.mul(c, M.log(x, p), p), 'exp($y/$c)', true],
  [(x, c, p) => F.div(M.log(x, p), c, p), 'exp($c*$y)', true],
  [(x, c, p) => F.div(c, M.log(x, p), p), 'exp($c/$y)', false],
];

/** A transform value, or undefined where mpmath would leave the reals (log or sqrt of a negative, a zero divisor) or overflow. */
function applyTransform(f: Transform[0], x: Mpf, c: Mpf, prec: number): Mpf | undefined {
  try {
    return f(x, c, prec);
  } catch {
    return undefined;
  }
}

const maxAbs = (r: readonly bigint[]): bigint => r.reduce((m, v) => (babs(v) > m ? babs(v) : m), 0n);

/**
 * Closed-form formulas for x (mpmath identify): a rational linear combination
 * of the constants (named values), possibly after one of the transforms
 * x*c, x/c, x**2, sqrt(x), exp(x), log(x), ..., a quadratic irrational, or a
 * product of powers of 2, 3, 5, 7 and the constants. Returns the first
 * formula found, all of them (shortest first) with `full`, or undefined.
 */
export function identify(
  xIn: Mpf,
  constantsIn: readonly Named[],
  prec: number,
  opts: { tol?: Mpf; maxcoeff?: number; full?: boolean } = {},
): string[] | undefined {
  const x = F.round(xIn, prec);
  if (F.isZero(x)) return ['0'];
  if (x.man < 0n) return identify(F.neg(x), constantsIn, prec, opts)?.map((s) => `-(${s})`);
  const full = opts.full ?? false;
  // tol defaults to eps**0.7
  const tol = opts.tol !== undefined && !F.isZero(opts.tol) ? opts.tol : M.powReal({ man: 1n, exp: BigInt(1 - prec) }, F.fromRational(7n, 10n, prec), prec);
  const mc = opts.maxcoeff ?? 1000;
  const M2 = F.fromInt(BigInt(mc * mc));
  let constants = constantsIn.map(([v, name]) => [F.round(v, prec), name] as Named);
  if (!constants.some(([v]) => F.cmp(v, ONE) === 0)) constants = [[ONE, '1'], ...constants];
  const solutions: string[] = [];
  for (const [ft, ftn, red] of TRANSFORMS) {
    for (const [c, cn] of constants) {
      if (red && cn === '1') continue;
      const t = applyTransform(ft, x, c, prec);
      if (t === undefined || F.cmp(F.abs(t), M2) > 0 || F.cmp(F.abs(t), tol) < 0) continue;
      const r = pslq([t, ...constants.map(([v]) => v)], prec, tol, mc);
      let s: string | undefined;
      if (r && maxAbs(r) <= BigInt(mc) && r[0] !== 0n) s = pslqstring(r, constants);
      else {
        const q = pslq([ONE, t, F.mul(t, t, prec)], prec, tol, mc);
        if (q && at(q, 2) !== 0n && maxAbs(q) <= BigInt(mc)) s = quadraticstring(t, at(q, 0), at(q, 1), at(q, 2), prec);
      }
      if (s !== undefined) {
        const y = s;
        solutions.push(cn === '1' && ftn.includes('/$c') ? ftn.replaceAll('$y', y).replaceAll('/$c', '') : ftn.replaceAll('$y', y).replaceAll('$c', cn));
        if (!full) return solutions;
      }
    }
  }
  if (F.cmp(x, ONE) !== 0) {
    const ilogs = [2n, 3n, 5n, 7n];
    const logs: Named[] = ilogs.map((i) => [M.log(F.fromInt(i), prec), String(i)] as Named);
    for (const [a, s] of constants) {
      // a constant whose logarithm is a rational multiple of log 2, 3, 5 or 7 adds nothing
      if (a.man <= 0n) continue;
      const la = M.log(a, prec);
      if (!ilogs.some((i) => findpoly(F.div(la, M.log(F.fromInt(i), prec), prec), 1, prec) !== undefined)) logs.push([la, s]);
    }
    const r = pslq([M.log(x, prec), ...logs.map(([v]) => v)], prec, tol, mc);
    if (r && maxAbs(r) <= BigInt(mc) && r[0] !== 0n) {
      solutions.push(prodstring(r, logs));
      if (!full) return solutions;
    }
  }
  if (!full || solutions.length === 0) return undefined;
  return solutions.map((s, i) => [s, i] as const).sort((a, b) => a[0].length - b[0].length || a[1] - b[1]).map(([s]) => s);
}

