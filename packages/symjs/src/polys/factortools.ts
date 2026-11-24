// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/factortools.py, Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { PolynomialError } from '../core/errors';
import { Rational, type Expr } from '../core/nodes';
import { iroot } from '../core/numbers';
import { igcd, igcdex } from '../core/numberutils';
import { at } from '../core/guard';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { asInt } from '../ntheory/intutil';
import { dmpFromDict } from './densebasic';
import { AlgebraicField } from './domains/algebraicfield';
import type { GaussianIntegerRing, GaussianRationalField } from './domains/gaussiandomains';
import type { PythonMPQ } from './domains/pythonrational';
import { gfGcdex } from './galoistools';
import type { PolyElement } from './rings';
import { wangFactor, zpoly, type RandInt, type ZPoly } from './wang';

type ExtensionField = AlgebraicField | GaussianIntegerRing | GaussianRationalField;

/** Order factors by outer dense length, multiplicity, and the dense coefficient list. */
export function sortExtensionFactors<P extends { listterms(): [readonly number[], Expr][] }>(
  factors: readonly [P, number][], domain: ExtensionField, level: number,
): [P, number][] {
  const compareCoeffs = (a: unknown, b: unknown): number => {
    const coordinates = (value: unknown): readonly PythonMPQ[] => {
      if (domain instanceof AlgebraicField) return domain.convert(value).toList();
      const z = domain.convert(value);
      return [z.re, z.im];
    };
    const u = coordinates(a), v = coordinates(b);
    for (let i = 0; i < Math.min(u.length, v.length); i++) {
      const sign = at(u, i).compare(at(v, i));
      if (sign) return sign;
    }
    return u.length - v.length;
  };
  const compareDense = (a: unknown, b: unknown): number => {
    if (!Array.isArray(a) || !Array.isArray(b)) return compareCoeffs(a, b);
    for (let i = 0; i < Math.min(a.length, b.length); i++) {
      const sign = compareDense(a[i], b[i]);
      if (sign) return sign;
    }
    return a.length - b.length;
  };
  const dense = factors.map((factor) => ({ factor, terms: dmpFromDict(new Map(factor[0].listterms()), level, domain) }));
  dense.sort((a, b) => a.terms.length - b.terms.length || a.factor[1] - b.factor[1] || compareDense(a.terms, b.terms));
  return dense.map(({ factor }) => factor);
}

/**
 * Counts how often each candidate factor divides the polynomial exactly.
 *
 * @param fIn - Dividend polynomial.
 * @param factors - Polynomial factors.
 * @returns The factors paired with multiplicities.
 * @throws PolynomialError when the dividend is zero or a candidate factor is constant or a candidate factor does not divide the polynomial.
 * @see SymPy `sympy.polys.factortools.dup_trial_division`
 */
export function dupTrialDivision(fIn: PolyElement, factors: readonly PolyElement[]): [PolyElement, number][] {
  let f = fIn;
  const result: [PolyElement, number][] = [];
  for (const factor of factors) {
    if (factor.isGround || f.isZero) throw new PolynomialError('trial division requires a nonzero dividend and nonconstant factors');
    let k = 0;
    for (;;) {
      const [q, r] = f.div(factor);
      if (!r.isZero) break;
      f = q;
      k++;
    }
    if (k === 0) throw new PolynomialError('trial division failed');
    result.push([factor, k]);
  }
  return result.sort(([a, k], [b, l]) => a.degree() - b.degree() || k - l || a.toString().localeCompare(b.toString()));
}

/**
 * Uses Wang's algorithm to factor a primitive square-free integer polynomial.
 *
 * @param f - Polynomial to operate on.
 * @param modulus - Initial bound on the evaluation points.
 * @param seed - Seed for choosing evaluation points.
 * @returns The integer polynomial factors.
 * @throws RangeError when all supplied evaluation points have been exhausted.
 * @see SymPy `sympy.polys.factortools.dmp_zz_wang`
 */
export function dmpZzWang(f: PolyElement, modulus?: number, seed?: readonly number[]): PolyElement[] {
  const encode = (p: PolyElement): ZPoly => zpoly(p.terms().map(([m, c]) => [m, asInt(c)]));
  const decode = (p: ZPoly): PolyElement => f.ring.fromDict([...p.values()].map(({ e, c }) => [e, c]));
  const leadingFactors = (p: ZPoly): [bigint, ZPoly[]] => {
    const [content, factors] = decode(p).factorList();
    return [asInt(content), factors.map(([g]) => encode(g))];
  };
  let index = 0;
  const random: RandInt | undefined = seed === undefined ? undefined : (lo, hi) => {
    while (index < seed.length) {
      const value = at(seed, index++);
      if (value >= lo && value <= hi) return value;
    }
    throw new RangeError('Wang evaluation point sequence exhausted');
  };
  return wangFactor(encode(f), f.ring.ngens, leadingFactors, random, modulus).map(decode);
}

/**
 * Computes Mignotte's bound for coefficients of multivariate integer polynomial factors.
 *
 * @param f - Polynomial to operate on.
 * @returns An upper bound on the absolute coefficients of the integer factors.
 * @see SymPy `sympy.polys.factortools.dmp_zz_mignotte_bound`
 */
export function dmpZzMignotteBound(f: PolyElement): Expr {
  if (f.isZero) return Rational.of(0);
  const n = f.degrees().reduce((sum, degree) => sum + degree, 0);
  const coefficients = f.listterms().map(([, c]) => BigInt(String(c)));
  const a = coefficients.reduce((maximum, c) => { const abs = c < 0n ? -c : c; return abs > maximum ? abs : maximum; }, 0n);
  const b = BigInt(String(f.LC));
  return Rational.of(iroot(BigInt(n + 1), 2n) * 2n ** BigInt(n) * a * (b < 0n ? -b : b));
}

/**
 * Lifts both polynomial factors and their Bézout coefficients from modulus `m` to `m**2`.
 *
 * @param m - Current lifting modulus.
 * @param f - Polynomial to operate on.
 * @param g - First factor modulo the lifting modulus.
 * @param h - Complementary factor modulo the lifting modulus.
 * @param s - Bézout coefficient of the first factor.
 * @param t - Bézout coefficient of the complementary factor.
 * @returns Two lifted factors and two lifted coefficients.
 * @see SymPy `sympy.polys.factortools.dup_zz_hensel_step`
 */
export function dupZzHenselStep(m: bigint, f: PolyElement, g: PolyElement, h: PolyElement, s: PolyElement, t: PolyElement): [PolyElement, PolyElement, PolyElement, PolyElement] {
  const M = m * m;
  const e = f.sub(g.mul(h)).truncGround(M);
  const [q0, r0] = s.mul(e).div(h);
  const q = q0.truncGround(M), r = r0.truncGround(M);
  const G = g.add(t.mul(e).add(q.mul(g))).truncGround(M);
  const H = h.add(r).truncGround(M);
  const b = s.mul(G).add(t.mul(H)).sub(1).truncGround(M);
  const [c0, d0] = s.mul(b).div(H);
  const c = c0.truncGround(M), d = d0.truncGround(M);
  return [G, H, s.sub(d).truncGround(M), t.sub(t.mul(b).add(c.mul(G))).truncGround(M)];
}

/**
 * Lifts a modular factorization to the prime power `p**l`.
 *
 * @param p - Prime used for lifting.
 * @param f - Polynomial to operate on.
 * @param factors - Polynomial factors.
 * @param l - Target lifting exponent.
 * @returns The lifted polynomial factors.
 * @throws RangeError when the lifting precision is nonpositive or the factor list is empty.
 * @see SymPy `sympy.polys.factortools.dup_zz_hensel_lift`
 */
export function dupZzHenselLift(p: bigint, f: PolyElement, factors: readonly PolyElement[], l: number): PolyElement[] {
  if (factors.length === 0 || !Number.isSafeInteger(l) || l < 1) throw new RangeError('positive precision and at least one factor required');
  const R = f.ring, modulus = p ** BigInt(l);
  if (factors.length === 1) return [f.mulGround(igcdex(BigInt(String(f.LC)), modulus)[0]).truncGround(modulus)];
  const k = Math.floor(factors.length / 2);
  let g = factors.slice(0, k).reduce((a, b) => a.mul(b), R.groundNew(f.LC)).truncGround(p);
  let h = factors.slice(k).reduce((a, b) => a.mul(b), R.one).truncGround(p);
  const dense = (v: PolyElement): bigint[] => v.toDense().map((c) => BigInt(String(c)));
  const [s0, t0] = gfGcdex(dense(g), dense(h), p);
  let s = R.fromList(s0.map((c) => Rational.of(c))).truncGround(p), t = R.fromList(t0.map((c) => Rational.of(c))).truncGround(p);
  let m = p;
  for (let i = 0; i < Math.ceil(Math.log2(l)); i++) {
    [g, h, s, t] = dupZzHenselStep(m, f, g, h, s, t);
    m *= m;
  }
  return [...dupZzHenselLift(p, g, factors.slice(0, k), l), ...dupZzHenselLift(p, h, factors.slice(k), l)];
}

/**
 * Remove common divisors of successive evaluated leading-coefficient factors.
 *
 * @param E - Evaluations of the leading-coefficient factors.
 * @param cs - Content of the specialized polynomial.
 * @param ct - Content of the leading coefficient.
 * @returns The matching value, or `NoMatch` when the requested form is unavailable.
 * @see SymPy `sympy.polys.factortools.dmp_zz_wang_non_divisors`
 */
export function dmpZzWangNonDivisors(E: readonly bigint[], cs: bigint, ct: bigint): bigint[] | NoMatchResult {
  const result = [cs * ct];
  for (const value of E) {
    let q = value < 0n ? -value : value;
    if (q === 0n) return NoMatch;
    for (let i = result.length - 1; i >= 0; i--) {
      let r = at(result, i);
      while (r !== 1n) {
        r = igcd(r, q);
        q /= r;
      }
      if (q === 1n) return NoMatch;
    }
    result.push(q);
  }
  return result.slice(1);
}
