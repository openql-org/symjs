// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The heuristic GCD of multivariate integer polynomials: a port of
 * SymPy's dmp_zz_heu_gcd, dup_zz_heu_gcd, _dmp_zz_gcd_interpolate and
 * _dmp_rr_trivial_gcd / _dmp_simplify_gcd from sympy/polys/euclidtools.py
 * (SymPy, BSD 3-Clause license), on the sparse polynomials of wang.ts.
 *
 * The polynomials are evaluated at a large integer for the main variable, the
 * GCD of the images is computed recursively (down to integers), and the GCD is
 * interpolated back from its balanced digits in base x. The candidate and the
 * cofactors are verified by exact division; with SymPy's evaluation points (large
 * against the coefficients) a candidate that divides both is the GCD. When no
 * evaluation point works the heuristic gives up (undefined), and the
 * caller falls back to a subresultant or primitive remainder sequence, as SymPy
 * does on HeuristicGCDFailed.
 */

import { at, defined, first } from '../core/guard';
import { gcd as igcd, iroot } from '../core/numbers';
import type { ZPoly, ZTerm } from './wang';

/** SymPy HEU_GCD_MAX: the number of evaluation points tried. */
const HEU_GCD_MAX = 6;

const babs = (a: bigint): bigint => (a < 0n ? -a : a);
const bmin = (a: bigint, b: bigint): bigint => (a < b ? a : b);
const bmax = (a: bigint, b: bigint): bigint => (a > b ? a : b);
const keyOf = (e: readonly number[]): string => e.join(',');

function addTerm(f: ZPoly, e: readonly number[], c: bigint): void {
  if (c === 0n) return;
  const k = keyOf(e);
  const s = (f.get(k)?.c ?? 0n) + c;
  if (s === 0n) f.delete(k);
  else f.set(k, { e, c: s });
}

/** The constant polynomial c in n variables. */
function constant(c: bigint, n: number): ZPoly {
  const f: ZPoly = new Map();
  addTerm(f, Array<number>(n).fill(0), c);
  return f;
}

const mapCoeffs = (f: ZPoly, fn: (c: bigint) => bigint): ZPoly => {
  const out: ZPoly = new Map();
  for (const t of f.values()) addTerm(out, t.e, fn(t.c));
  return out;
};

/** Lexicographic comparison of distinct exponent tuples. */
function cmpLex(a: readonly number[], b: readonly number[]): number {
  const i = a.findIndex((k, j) => k !== at(b, j));
  return at(a, i) - at(b, i);
}

/** The lex-leading term of a nonzero polynomial. */
function leadTerm(f: ZPoly): ZTerm {
  let best: ZTerm | undefined;
  for (const t of f.values()) if (best === undefined || cmpLex(t.e, best.e) > 0) best = t;
  return defined(best, 'a term of a nonzero polynomial');
}

/** SymPy dmp_ground_LC: the coefficient of the lex-leading term. */
const groundLC = (f: ZPoly): bigint => leadTerm(f).c;

/** The degree in the variable i (-1 for zero). */
function degIn(f: ZPoly, i: number): number {
  let d = -1;
  for (const t of f.values()) d = Math.max(d, at(t.e, i));
  return d;
}

/** SymPy dmp_ground_content: the gcd of the coefficients (positive). */
function groundContent(f: ZPoly): bigint {
  let g = 0n;
  for (const t of f.values()) g = igcd(g, t.c);
  return babs(g);
}

/** SymPy dmp_max_norm. */
function maxNorm(f: ZPoly): bigint {
  let m = 0n;
  for (const t of f.values()) m = bmax(m, babs(t.c));
  return m;
}

/** SymPy dmp_ground_primitive (the primitive part only; zero stays zero). */
function primitive(f: ZPoly): ZPoly {
  const c = groundContent(f);
  return c <= 1n ? f : mapCoeffs(f, (k) => k / c);
}

/** f with a positive leading coefficient. */
const positive = (f: ZPoly): ZPoly => (f.size && groundLC(f) < 0n ? mapCoeffs(f, (k) => -k) : f);

/** f(a, x_1, ..., x_{n-1}): the main variable evaluated (SymPy dmp_eval). */
function evalMain(f: ZPoly, a: bigint): ZPoly {
  const out: ZPoly = new Map();
  for (const t of f.values()) addTerm(out, t.e.slice(1), t.c * a ** BigInt(at(t.e, 0)));
  return out;
}

/**
 * SymPy _dmp_zz_gcd_interpolate: the polynomial in n + 1 variables whose coefficients in the new
 * main variable are the balanced base-x digits of h, with a positive leading coefficient.
 */
function interpolate(hIn: ZPoly, x: bigint): ZPoly {
  const out: ZPoly = new Map();
  let h = hIn;
  const half = x / 2n;
  for (let i = 0; h.size; i++) {
    const next: ZPoly = new Map();
    for (const t of h.values()) {
      let r = ((t.c % x) + x) % x;
      if (r > half) r -= x;
      addTerm(out, [i, ...t.e], r);
      addTerm(next, t.e, (t.c - r) / x);
    }
    h = next;
  }
  return positive(out);
}

/**
 * The exact quotient f/g over the integers, or undefined when g does not divide f (SymPy dmp_div
 * with a zero remainder). The quotient's degree in each variable is at most deg f - deg g.
 */
export function zzExquo(f: ZPoly, g: ZPoly): ZPoly | undefined {
  const n = leadTerm(g).e.length;
  const bound = Array.from({ length: n }, (_, i) => degIn(f, i) - degIn(g, i));
  const lt = leadTerm(g);
  const r: ZPoly = new Map(f);
  const q: ZPoly = new Map();
  while (r.size) {
    const t = leadTerm(r);
    const m = t.e.map((k, i) => k - at(lt.e, i));
    if (m.some((k, i) => k < 0 || k > at(bound, i)) || t.c % lt.c !== 0n) return undefined;
    const c = t.c / lt.c;
    addTerm(q, m, c);
    for (const s of g.values()) addTerm(r, s.e.map((k, i) => k + at(m, i)), -c * s.c);
  }
  return q;
}

/** The coefficients of f in the main variable, as polynomials in the other n - 1 variables. */
function mainCoeffs(f: ZPoly): ZPoly[] {
  const out = new Map<number, ZPoly>();
  for (const t of f.values()) {
    const k = at(t.e, 0);
    const c = out.get(k) ?? new Map<string, ZTerm>();
    addTerm(c, t.e.slice(1), t.c);
    out.set(k, c);
  }
  return [...out.values()];
}

/** p(x_1, ..., x_{n-1}) as a polynomial in n variables (degree 0 in the main one). */
function lift(p: ZPoly): ZPoly {
  const out: ZPoly = new Map();
  for (const t of p.values()) addTerm(out, [0, ...t.e], t.c);
  return out;
}

type GcdResult = readonly [ZPoly, ZPoly, ZPoly];

/** h, f/h and g/h for a GCD h that divides both (undefined when the division fails). */
function cofactors(f: ZPoly, g: ZPoly, h: ZPoly): GcdResult | undefined {
  const cff = zzExquo(f, h);
  const cfg = cff && zzExquo(g, h);
  return cff && cfg ? [h, cff, cfg] : undefined;
}

/**
 * SymPy _dmp_rr_trivial_gcd and _dmp_simplify_gcd: the GCD when f or g is zero, or when one of
 * them does not involve the main variable (then it is the GCD with the content of the other).
 */
function trivialGcd(f: ZPoly, g: ZPoly, n: number, start?: bigint): GcdResult | 'fail' | undefined {
  if (!f.size && !g.size) return [f, f, g];
  if (!f.size) {
    const s = groundLC(g) < 0n ? -1n : 1n;
    return [mapCoeffs(g, (k) => s * k), f, constant(s, n)];
  }
  if (!g.size) {
    const s = groundLC(f) < 0n ? -1n : 1n;
    return [mapCoeffs(f, (k) => s * k), constant(s, n), g];
  }
  if (n === 0) {
    const a = groundLC(f);
    const b = groundLC(g);
    const h = igcd(a, b);
    return [constant(h, 0), constant(a / h, 0), constant(b / h, 0)];
  }
  if (degIn(f, 0) > 0 && degIn(g, 0) > 0) return undefined;
  // gcd(f, content(g)) for an f without the main variable (or the other way round)
  const cs = [...mainCoeffs(f), ...mainCoeffs(g)];
  let h = first(cs);
  for (const c of cs.slice(1)) {
    const r = heuGcd(h, c, n - 1, start);
    if (r === undefined) return 'fail';
    h = r[0];
  }
  return defined(cofactors(f, g, positive(lift(h))), 'the cofactors of a GCD');
}

/**
 * The GCD of two integer polynomials in n variables with its cofactors, [h, f/h, g/h], h with
 * a positive leading coefficient (SymPy dmp_zz_heu_gcd), or undefined when the heuristic fails.
 * `start` (at least 3) replaces SymPy's first evaluation point; it is for tests, which use small
 * points to reach the retries (a point below SymPy's bound can give a wrong GCD).
 */
export function heuGcd(fIn: ZPoly, gIn: ZPoly, n: number, start?: bigint): GcdResult | undefined {
  const trivial = trivialGcd(fIn, gIn, n, start);
  if (trivial === 'fail') return undefined;
  if (trivial !== undefined) return trivial;
  // dmp_ground_extract: the integer content comes out
  const gcd = igcd(groundContent(fIn), groundContent(gIn));
  const f = mapCoeffs(fIn, (k) => k / gcd);
  const g = mapCoeffs(gIn, (k) => k / gcd);
  const fNorm = maxNorm(f);
  const gNorm = maxNorm(g);
  const B = 2n * bmin(fNorm, gNorm) + 29n;
  let x = start ?? bmax(bmin(B, 99n * iroot(B, 2n)), 2n * bmin(fNorm / babs(groundLC(f)), gNorm / babs(groundLC(g))) + (n === 1 ? 2n : 4n));
  // (a candidate from a cofactor takes the sign of f or g; the GCD gets a positive leading coefficient)
  const withContent = ([h, cff, cfg]: GcdResult): GcdResult => {
    const s = groundLC(h) < 0n ? -1n : 1n;
    return [mapCoeffs(h, (k) => s * k * gcd), mapCoeffs(cff, (k) => s * k), mapCoeffs(cfg, (k) => s * k)];
  };
  for (let i = 0; i < HEU_GCD_MAX; i++) {
    const ff = evalMain(f, x);
    const gg = evalMain(g, x);
    if (ff.size && gg.size) {
      const r = heuGcd(ff, gg, n - 1, start);
      if (r === undefined) return undefined;
      const [h0, cff0, cfg0] = r;
      const h = primitive(interpolate(h0, x));
      const viaH = cofactors(f, g, h);
      if (viaH) return withContent(viaH);
      const cff = interpolate(cff0, x);
      const h1 = zzExquo(f, cff);
      const cfg1 = h1 && zzExquo(g, h1);
      if (h1 && cfg1) return withContent([h1, cff, cfg1]);
      const cfg = interpolate(cfg0, x);
      const h2 = zzExquo(g, cfg);
      const cff2 = h2 && zzExquo(f, h2);
      if (h2 && cff2) return withContent([h2, cff2, cfg]);
    }
    x = (73794n * x * iroot(iroot(x, 2n), 2n)) / 27011n;
  }
  return undefined;
}
