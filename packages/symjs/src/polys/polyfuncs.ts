// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file symmetrize: rewrite a polynomial in elementary symmetric polynomials
 * (SymPy polys.polyfuncs.symmetrize).
 */

import { Expr, ExprLike, Sym } from '../core/nodes';
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
    for (let i = start; i < gens.length; i++) rec(i + 1, [...chosen, gens[i]!]);
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
  const gens = gensIn.length ? [...gensIn] : (sortGens([...fe.freeSymbols()]) as Sym[]);
  const n = gens.length;
  const polys = Array.from({ length: n }, (_, i) => elementary(gens, i + 1));
  const syms = Array.from({ length: n }, (_, i) => new Sym(`s${i + 1}`));
  const weights = Array.from({ length: n }, (_, i) => n - i);
  let f = Poly.from(fe, gens);
  const symmetric: Expr[] = [];
  for (let guard = 0; guard < 10000 && !f.isZero; guard++) {
    let best: [number[], Expr] | undefined;
    let bestH = -1;
    for (const [m, c] of f.terms()) {
      if (m.every((v, i) => i === m.length - 1 || v >= m[i + 1]!)) {
        const h = Math.max(...m.map((v, i) => v * weights[i]!));
        if (h > bestH) {
          bestH = h;
          best = [m, c];
        }
      }
    }
    if (!best) break;
    const [monom, coeff] = best;
    const exps = monom.map((m1, i) => m1 - (monom[i + 1] ?? 0));
    symmetric.push(mul(coeff, ...exps.map((k, i) => pow(syms[i]!, k))));
    const product = expandMul(mul(coeff, ...exps.map((k, i) => pow(polys[i]!, k))));
    f = Poly.from(expandMul(add(f.asExpr(), mul(-1, product))), gens);
  }
  return [add(...symmetric), f.asExpr(), syms.map((s, i) => [s, polys[i]!] as [Sym, Expr])];
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
  if (k < 0) throw new Error('rational_interpolate: too few values for the required degree');
  const rows = degnum + k + 1;
  const c: Expr[][] = Array.from({ length: rows }, () => Array.from({ length: degnum + k + 2 }, () => sympify(1)));
  for (let j = 0; j < Math.max(degnum, k); j++) for (let i = 0; i < rows; i++) c[i]![j + 1] = mul(c[i]![j]!, xs[i]!);
  for (let j = 0; j <= k; j++) for (let i = 0; i < rows; i++) c[i]![degnum + k + 1 - j] = mul(-1, c[i]![k - j]!, ys[i]!);
  const r = nullspace(Matrix.of(c))[0]!;
  const num = add(...Array.from({ length: degnum + 1 }, (_, i) => mul(r.get(i, 0), pow(X, i))));
  const den = add(...Array.from({ length: k + 1 }, (_, i) => mul(r.get(i + degnum + 1, 0), pow(X, i))));
  return mul(num, pow(den, -1));
}
