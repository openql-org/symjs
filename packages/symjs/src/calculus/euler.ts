// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/calculus/euler.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Euler-Lagrange equations of a Lagrangian (SymPy euler_equations).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Derivative, Fn, Rel, Sym, UndefFn } from '../core/nodes';
import { at, first } from '../core/guard';
import { rel } from '../core/logic';
import { add, mul, sympify } from '../core/ops';
import { derivative } from '../core/undef';
import { diff } from './diff';

const isFunction = (e: Expr): e is UndefFn | Fn => e instanceof UndefFn || e instanceof Fn;

/** The distinct subexpressions of e (e included) that satisfy pred (SymPy atoms(Function), atoms(Derivative)). */
function subexpressions<T extends Expr>(e: Expr, pred: (a: Expr) => a is T): T[] {
  const out = new Map<string, T>();
  const go = (a: Expr): void => {
    if (pred(a)) out.set(a.key, a);
    a.args.forEach(go);
  };
  go(e);
  return [...out.values()];
}

/** A value or an array of values as an array. */
function listOf<T>(v: T | readonly T[]): readonly T[] {
  const isList = (u: T | readonly T[]): u is readonly T[] => Array.isArray(u);
  return isList(v) ? v : [v];
}

/** The multisets of size k of the items, in the order of Python's combinations_with_replacement. */
function combinationsWithReplacement<T>(items: readonly T[], k: number): T[][] {
  const out: T[][] = [];
  const rec = (start: number, acc: T[]): void => {
    if (acc.length === k) {
      out.push(acc);
      return;
    }
    for (let i = start; i < items.length; i++) rec(i, [...acc, at(items, i)]);
  };
  rec(0, []);
  return out;
}

/**
 * SymPy euler_equations(L, funcs, vars): the Euler-Lagrange equations of the
 * Lagrangian L for the functions funcs (all the functions of L by default) of
 * the variables vars (the arguments of the first function by default).
 */
export function eulerEquations(lagrangian: ExprLike, funcs: Expr | readonly Expr[] = [], vars: ExprLike | readonly ExprLike[] = []): Expr[] {
  const L = sympify(lagrangian);
  let fs: Expr[] = [...listOf(funcs)];
  if (fs.length === 0) fs = subexpressions(L, isFunction);
  else for (const f of fs) if (!isFunction(f)) throw new TypeError(`Function expected, got: ${f.toString()}`);
  const vs0: Expr[] = listOf(vars).map(sympify);
  const vs: Expr[] = vs0.length === 0 ? [...first(fs).args] : vs0;
  if (!vs.every((v) => v instanceof Sym)) throw new TypeError(`Variables are not symbols, got ${vs.map(String).join(', ')}`);
  for (const f of fs) {
    if (f.args.length !== vs.length || f.args.some((a, i) => a.key !== vs[i]?.key)) throw new RangeError(`Variables (${vs.map(String).join(', ')}${vs.length === 1 ? ',' : ''}) do not match args: ${f.toString()}`);
  }
  const keys = new Set(fs.map((f) => f.key));
  const derivs = subexpressions(L, (a): a is Derivative => a instanceof Derivative && keys.has(a.expr.key));
  const order = Math.max(0, ...derivs.map((d) => d.variableCount.reduce((s, [, n]) => s + n, 0)));
  const eqns: Expr[] = [];
  for (const f of fs) {
    let eq = diff(L, f);
    for (let i = 1; i <= order; i++) {
      for (const p of combinationsWithReplacement(vs, i)) {
        const dfp = derivative(f, p.map((v): [Expr, number] => [v, 1]));
        let term = diff(L, dfp);
        for (const v of p) term = diff(term, v);
        eq = add(eq, mul(i % 2 === 0 ? 1 : -1, term));
      }
    }
    const neq = rel('Eq', eq, 0);
    if (neq instanceof Rel) eqns.push(neq);
  }
  return eqns;
}
