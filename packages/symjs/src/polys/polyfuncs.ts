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
