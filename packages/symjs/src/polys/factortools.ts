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
import { gfGcdex } from './galoistools';
import type { PolyElement } from './rings';

/** Determine factor multiplicities by repeated exact polynomial division. */
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

/** Mignotte's multivariate factor coefficient bound over the integers. */
export function dmpZzMignotteBound(f: PolyElement): Expr {
  if (f.isZero) return Rational.of(0);
  const n = f.degrees().reduce((sum, degree) => sum + degree, 0);
  const coefficients = f.listterms().map(([, c]) => BigInt(String(c)));
  const a = coefficients.reduce((maximum, c) => { const abs = c < 0n ? -c : c; return abs > maximum ? abs : maximum; }, 0n);
  const b = BigInt(String(f.LC));
  return Rational.of(iroot(BigInt(n + 1), 2n) * 2n ** BigInt(n) * a * (b < 0n ? -b : b));
}

/** Lift a factorization and its Bezout relation from modulus m to m squared. */
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

/** Multifactor Hensel lifting to the prime power p to the exponent l. */
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

/** Remove common divisors of successive evaluated leading-coefficient factors. */
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
