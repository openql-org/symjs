// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file symmetrize: rewrite a polynomial in elementary symmetric polynomials
 * (SymPy polys.polyfuncs.symmetrize).
 */

import { at, defined, first } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { expandMul } from '../simplify/expand';
import { Poly, sortGens } from './sympoly';
import { Matrix } from '../matrices/matrix';
import { nullspace } from '../matrices/linalg';

/** Elementary symmetric polynomial e_k of the generators. */
function elementary(gens: readonly Expr[], k: number): Expr {
  const terms: Expr[] = [];
  const rec = (start: number, chosen: Expr[]) => {
    if (chosen.length === k) {
      terms.push(mul(...chosen));
      return;
    }
    for (let i = start; i < gens.length; i++) rec(i + 1, [...chosen, at(gens, i)]);
  };
  rec(0, []);
  return add(...terms);
}

/**
 * Symmetric part in terms of s1, s2, ... and the non-symmetric remainder.
 * Returns [symmetric, remainder, [(s_k, e_k)]].
 */
export function symmetrize(fIn: ExprLike, gensIn: readonly Sym[] = []): [Expr, Expr, [Sym, Expr][]] {
  const fe = sympify(fIn);
  const gens = gensIn.length ? [...gensIn] : sortGens([...fe.freeSymbols()]);
  const n = gens.length;
  const polys = Array.from({ length: n }, (_, i) => elementary(gens, i + 1));
  const syms = Array.from({ length: n }, (_, i) => new Sym(`s${i + 1}`));
  const weights = Array.from({ length: n }, (_, i) => n - i);
  let f = Poly.from(fe, gens);
  const symmetric: Expr[] = [];
  for (let guard = 0; guard < 10000 && !f.isZero; guard++) {
    let best: [number[], Expr] | undefined;
    let bestH = -Infinity;
    for (const [m, c] of f.terms()) {
      if (m.every((v, i) => v >= (m[i + 1] ?? 0))) {
        // a constant (no generators) has weight -Infinity and is still taken
        const h = Math.max(...m.map((v, i) => v * at(weights, i)));
        if (best === undefined || h > bestH) {
          bestH = h;
          best = [m, c];
        }
      }
    }
    if (!best) break;
    const [monom, coeff] = best;
    const exps = monom.map((m1, i) => m1 - (monom[i + 1] ?? 0));
    symmetric.push(mul(coeff, ...exps.map((k, i) => pow(at(syms, i), k))));
    const product = expandMul(mul(coeff, ...exps.map((k, i) => pow(at(polys, i), k))));
    f = Poly.from(expandMul(add(f.asExpr(), mul(-1, product))), gens);
  }
  return [add(...symmetric), f.asExpr(), syms.map((s, i): [Sym, Expr] => [s, at(polys, i)])];
}

/** symmetrize with the elementary polynomials substituted back (formal=False). */
export function symmetrizeExpr(fIn: ExprLike, gens: readonly Sym[] = []): [Expr, Expr] {
  const [s, r, m] = symmetrize(fIn, gens);
  return [xreplace(s, m), r];
}

/**
 * Rational interpolation of (x, y) data with a numerator of degree
 * `degnum` (SymPy rational_interpolate).
 */
export function rationalInterpolate(data: readonly (readonly [ExprLike, ExprLike])[], degnum: number, X: Sym = new Sym('x')): Expr {
  const xs = data.map(([a]) => sympify(a));
  const ys = data.map(([, b]) => sympify(b));
  const k = xs.length - degnum - 1;
  if (k < 0) throw new RangeError('rational_interpolate: too few values for the required degree');
  const rows = degnum + k + 1;
  const c: Expr[][] = Array.from({ length: rows }, () => Array.from({ length: degnum + k + 2 }, () => sympify(1)));
  c.forEach((row, i) => {
    const xi = at(xs, i);
    const yi = at(ys, i);
    for (let j = 0; j < Math.max(degnum, k); j++) row[j + 1] = mul(at(row, j), xi);
    for (let j = 0; j <= k; j++) row[degnum + k + 1 - j] = mul(-1, at(row, k - j), yi);
  });
  const r = first(nullspace(Matrix.of(c)));
  const num = add(...Array.from({ length: degnum + 1 }, (_, i) => mul(r.get(i, 0), pow(X, i))));
  const den = add(...Array.from({ length: k + 1 }, (_, i) => mul(r.get(i + degnum + 1, 0), pow(X, i))));
  return mul(num, pow(den, -1));
}

/**
 * SymPy viete(f, roots=None, *gens): Viete's formulas for the roots of the
 * univariate polynomial f, as [elementary symmetric polynomial of the roots,
 * its value] pairs. Without roots the symbols r1, r2, ... are used.
 */
export function viete(fIn: Poly | ExprLike, roots?: readonly Expr[], ...gens: Expr[]): [Expr, Expr][] {
  const f = fIn instanceof Poly ? fIn : Poly.from(sympify(fIn), gens.length ? gens : undefined);
  if (f.gens.length > 1) throw new RangeError("multivariate polynomials are not allowed");
  const n = f.degree();
  if (n < 1) throw new RangeError("Cannot derive Viete's formulas for a constant polynomial");
  const rs = roots ?? Array.from({ length: n }, (_, i) => new Sym(`r${i + 1}`));
  if (rs.length !== n) throw new RangeError(`required ${n} roots, got ${rs.length}`);
  const [lc, ...coeffs] = f.allCoeffs();
  return coeffs.map((c, i): [Expr, Expr] => {
    const sigma = add(...combinations(rs, i + 1).map((ps) => mul(...ps)));
    return [sigma, mul(i % 2 === 0 ? -1 : 1, c, pow(defined(lc, 'leading coefficient'), -1))];
  });
}

/** The k-element combinations of xs in lexicographic order. */
function combinations<T>(xs: readonly T[], k: number): T[][] {
  if (k === 0) return [[]];
  return xs.flatMap((x, i) => combinations(xs.slice(i + 1), k - 1).map((c) => [x, ...c]));
}
