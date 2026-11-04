// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (solvers/solveset.py), BSD-3-Clause; see LICENSE.

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { S } from '../core/nodes';
import { at, defined } from '../core/guard';
import { sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { NotImplementedError } from '../core/errors';
import { EmptySet, FiniteSet, ImageSet, Reals, imageSet } from '../sets/sets';
import { expand } from '../simplify/expand';
import { asEquation, nonlinsolve as finiteNonlinsolve } from './solve';
import { solveset } from './inequalities';

/**
 * Solve a nonlinear system over the complex numbers. Infinite solution
 * components are ImageSets, rather than a list of principal logarithms.
 * The remaining algebraic systems use polynomial elimination.
 */
export function nonlinsolve(system: readonly ExprLike[], symbols: readonly Sym[]): Expr[][] {
  const eqs = system.map(asEquation);
  if (symbols.length === 2 && eqs.length === 2) {
    const one = eqs.findIndex((e) => symbols.filter((v) => e.has(v)).length === 1);
    if (one >= 0) {
      const equation = at(eqs, one);
      const v = defined(symbols.find((s) => equation.has(s)));
      const w = defined(symbols.find((s) => s !== v));
      const values = solveset(equation, v);
      if (values.equals(EmptySet)) return [];
      const other = at(eqs, 1 - one);
      const tuple = (a: Expr, b: Expr): Expr[] => symbols.map((s) => s === v ? a : b);
      if (values instanceof ImageSet) {
        const real = solveset(equation, v, Reals);
        const roots = (e: Expr): readonly Expr[] => {
          const r = solveset(e, w);
          if (r instanceof FiniteSet) return r.args;
          if (r.equals(EmptySet)) return [];
          throw new NotImplementedError('nonlinsolve: an independent infinite or unresolved solution component requires another parameter');
        };
        const out: Expr[][] = [];
        if (real instanceof FiniteSet) {
          for (const a of real.args) for (const b of roots(subs(other, [[v, a]]))) out.push(tuple(a, b));
        }
        for (const b of roots(subs(other, [[v, values.expr]]))) {
          out.push(tuple(values, imageSet(values.variable, b, values.base)));
        }
        return out;
      }
      if (values instanceof FiniteSet) {
        const out: Expr[][] = [];
        let complete = true;
        for (const a of values.args) {
          const rest = solveset(subs(other, [[v, a]]), w);
          if (rest instanceof FiniteSet) for (const b of rest.args) out.push(tuple(a, b));
          else if (rest instanceof ImageSet) out.push(tuple(a, rest));
          else if (!rest.equals(EmptySet)) complete = false;
        }
        if (out.some((t) => t.some((c) => c instanceof ImageSet))) {
          if (!complete) throw new NotImplementedError('nonlinsolve: some solution components remain unresolved');
          return out;
        }
        if (complete) return out;
      }
    }
  }
  return finiteNonlinsolve(eqs, symbols);
}

/** SymPy substitution: extend known assignments by solving the remaining system. */
export function substitution(
  system: readonly ExprLike[],
  symbols: readonly Sym[],
  result: readonly ReadonlyMap<Sym, ExprLike>[] = [new Map()],
  _knownSymbols: readonly Sym[] = [],
  exclude: readonly ExprLike[] = [],
  allSymbols: readonly Sym[] = symbols,
): Expr[][] {
  const out: Expr[][] = [];
  for (const known of result) {
    const entries = [...known].map(([k, v]): [Expr, Expr] => [k, sympify(v)]);
    const pending = system.map((e) => expand(subs(asEquation(e), entries))).filter((e) => !e.equals(S.Zero));
    const free = symbols.filter((v) => !entries.some(([k]) => k.equals(v)));
    const solutions = free.length ? nonlinsolve(pending, free) : pending.length ? [] : [[]];
    for (const solution of solutions) {
      const assignments: [Expr, Expr][] = [...entries, ...free.map((v, i): [Expr, Expr] => [v, at(solution, i)])];
      if (exclude.some((e) => expand(subs(sympify(e), assignments)).equals(S.Zero))) continue;
      out.push(allSymbols.map((v) => assignments.find(([k]) => k.equals(v))?.[1] ?? v));
    }
  }
  return out;
}
