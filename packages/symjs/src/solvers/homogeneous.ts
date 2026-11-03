// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy homogeneous_order (shared by dsolve and its hint solvers).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Derivative, Dummy, Fn, Mul, Rational, S, UndefFn } from '../core/nodes';
import { asBaseExp, mul, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { expectType, first, getOrThrow } from '../core/guard';
import { separatevars } from '../simplify/separatevars';

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
  if (eq instanceof Fn) return homogeneousOrder(first(eq.args), ...syms)?.key === S.Zero.key ? S.Zero : undefined;
  // replace x by t*x and see whether a power of t can be factored out
  const t = new Dummy('t', { positive: true });
  const scaled = xreplace(eq, syms.map((s) => [s, mul(t, s)] as const));
  const sep = separatevars(scaled, { symbols: [t], dict: true });
  // with the single symbol t the dict form always exists and has an entry for t
  const isDict = (v: unknown): v is Map<Sym | 'coeff', Expr> => v instanceof Map;
  const eqs = getOrThrow(expectType(sep, isDict, 'separatevars dict'), t);
  if (eqs instanceof Rational && eqs.isOne) return S.Zero;
  const [b, e] = asBaseExp(mul(...(eqs instanceof Mul ? eqs.args : [eqs]).filter((a) => a.has(t))));
  if (b.key === t.key) return e;
  return undefined;
}
