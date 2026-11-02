// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy homogeneous_order (shared by dsolve and its hint solvers).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Derivative, Dummy, Fn, Pow, Rational, S, UndefFn } from '../core/nodes';
import { mul, pow, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { powsimp } from '../simplify/powsimp';
import { simplify } from '../simplify/simplify';

/**
 * SymPy homogeneous_order(eq, *symbols): n such that eq(t*x, t*y, ...) = t**n * eq(x, y, ...),
 * or undefined when eq is not homogeneous in the symbols.
 */
export function homogeneousOrder(eqIn: ExprLike, ...symbols: Expr[]): Expr | undefined {
  let eq = sympify(eqIn);
  const hasDeriv = (e: Expr): boolean => e instanceof Derivative || e.args.some(hasDeriv);
  if (hasDeriv(eq)) return undefined;
  if (freeSymbols(eq).size === 0) return S.Zero;
  // replace applied functions of the symbols by dummies
  const syms: Expr[] = [];
  for (const s of symbols) {
    if (s instanceof UndefFn) {
      if (s.args.some((a) => !symbols.some((t) => t.key === a.key))) return undefined;
      const d = new Dummy('d');
      eq = xreplace(eq, [[s, d]]);
      syms.push(d);
    } else syms.push(s);
  }
  if (![...freeSymbols(eq)].some((s) => syms.some((t) => t.key === s.key))) return undefined;
  if (eq instanceof Fn) return homogeneousOrder(eq.args[0]!, ...syms)?.key === S.Zero.key ? S.Zero : undefined;
  const t = new Dummy('t', { positive: true });
  const scaled = xreplace(eq, syms.map((s) => [s, mul(t, s)] as const));
  const ratio = simplify(powsimp(mul(scaled, pow(eq, -1)), { force: false }));
  if (ratio instanceof Rational && ratio.isOne) return S.Zero;
  if (ratio.key === t.key) return S.One;
  if (ratio instanceof Pow && ratio.base.key === t.key && !ratio.exp.has(t)) return ratio.exp;
  return undefined;
}
