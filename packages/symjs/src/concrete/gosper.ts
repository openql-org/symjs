// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Gosper's algorithm for hypergeometric summation (SymPy
 * sympy.concrete.gosper): the Gosper normal form of a rational function,
 * the Gosper term of a hypergeometric term and the closed form of its
 * (indefinite or definite) sum.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, Rational, S, Sym } from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { at } from '../core/guard';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import { subs, xreplace } from '../core/traverse';
import { Poly, factor } from '../polys/sympoly';
import { fraction } from '../simplify/rational';
import { hypersimp } from '../simplify/public';
import { limit } from '../series/limits';
import { linsolve } from '../solvers/public';

const field = (e: Expr, n: Sym): Poly => Poly.from(e, [n], { domain: 'QQ' });

/**
 * SymPy gosper_normal: polynomials A, B, C with f/g = Z*A/B*C(n + 1)/C(n),
 * gcd(A(n), B(n + h)) = 1 for all nonnegative integers h, gcd(A, C(n + 1)) =
 * gcd(B, C) = 1 (Z is folded into A). Poly objects, or expressions with
 * `polys: false`.
 */
export function gosperNormal(f: ExprLike, g: ExprLike, n: Sym, opts?: { polys?: true }): [Poly, Poly, Poly];
export function gosperNormal(f: ExprLike, g: ExprLike, n: Sym, opts: { polys: false }): [Expr, Expr, Expr];
export function gosperNormal(fIn: ExprLike, gIn: ExprLike, n: Sym, opts: { polys?: boolean } = {}): [Poly, Poly, Poly] | [Expr, Expr, Expr] {
  const p = field(sympify(fIn), n);
  const q = field(sympify(gIn), n);
  const Z = mul(p.LC(), pow(q.LC(), -1));
  let A = p.monic();
  let B = q.monic();
  let C = field(S.One, n);
  const h = new Dummy('h');
  const R = field(A.asExpr(), n).resultant(field(xreplace(B.asExpr(), [[n, add(n, h)]]), n));
  const roots = Poly.from(R, [h])
    .groundRoots()
    .map(([r]) => r)
    .filter((r): r is Rational => r instanceof Rational && r.isInteger && !r.isNegative)
    .map((r) => Number(r.p))
    .sort((a, b) => a - b);
  for (const i of new Set(roots)) {
    // (gcds over a field are monic)
    const d = A.gcd(B.shift(i)).monic();
    A = A.quo(d);
    B = B.quo(d.shift(-i));
    for (let j = 1; j <= i; j++) C = C.mul(d.shift(-j));
  }
  A = A.mulGround(Z);
  if (opts.polys === false) return [A.asExpr(), B.asExpr(), C.asExpr()];
  return [A, B, C];
}

/**
 * SymPy gosper_term: the rational function g such that f*g is an
 * antidifference of the hypergeometric term f (g(n + 1)*f(n + 1) - g(n)*f(n)
 * = f(n)); NoMatch (SymPy None) when f is not Gosper-summable.
 */
export function gosperTerm(fIn: ExprLike, n: Sym): Expr | NoMatchResult {
  const r = hypersimp(fIn, n);
  if (isNoMatch(r)) return NoMatch;
  const [p, q] = fraction(r);
  const [A, B0, C] = gosperNormal(p, q, n);
  const B = B0.shift(-1);
  const [N, M, K] = [A.degree(), B.degree(), C.degree()];
  let D: Expr[];
  if (N !== M || A.LC().key !== B.LC().key) D = [Rational.of(K - Math.max(N, M))];
  else if (N === 0) D = [Rational.of(K - N + 1), S.Zero];
  else D = [Rational.of(K - N + 1), mul(sub(B.nth(N - 1), A.nth(N - 1)), pow(A.LC(), -1))];
  const ds = D.filter((d): d is Rational => d instanceof Rational && d.isInteger && !d.isNegative).map((d) => Number(d.p));
  if (!ds.length) return NoMatch;
  const d = Math.max(...ds);
  const coeffs = Array.from({ length: d + 1 }, (_c, i) => new Dummy(`c${i}`));
  // x = c0*n**d + ... + cd
  const x = add(...coeffs.map((c, i) => mul(c, pow(n, d - i))));
  const H = sub(sub(mul(A.asExpr(), xreplace(x, [[n, add(n, 1)]])), mul(B.asExpr(), x)), C.asExpr());
  const eqs = Poly.from(H, [n]).coeffs();
  const sol = linsolve(eqs, coeffs);
  if (!Array.isArray(sol)) return NoMatch;
  // undetermined coefficients are 0 (x is not zero: C is not)
  const xs = xreplace(xreplace(x, coeffs.map((c, i) => [c, at(sol, i)] as const)), coeffs.map((c) => [c, S.Zero] as const));
  // (B*x first: a numeric x distributes over B, as in SymPy)
  return mul(mul(B.asExpr(), xs), pow(C.asExpr(), -1));
}

/**
 * SymPy gosper_sum: the indefinite sum of the hypergeometric term f in k
 * (k a symbol), or the sum from a to b (k given as [k, a, b]), by Gosper's
 * algorithm; NoMatch when f is not Gosper-summable.
 */
export function gosperSum(fIn: ExprLike, k: Sym | readonly [Sym, ExprLike, ExprLike]): Expr | NoMatchResult {
  const f = sympify(fIn);
  const v = k instanceof Sym ? k : k[0];
  const g = gosperTerm(f, v);
  if (isNoMatch(g)) return NoMatch;
  if (k instanceof Sym) return factor(mul(f, g));
  const [, a, b] = k;
  let result = sub(subs(mul(f, add(g, 1)), [[v, b]]), subs(mul(f, g), [[v, a]]));
  if (result === S.NaN) result = sub(limit(mul(f, add(g, 1)), v, b), limit(mul(f, g), v, a));
  return factor(result);
}
