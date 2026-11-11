// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (solvers/solveset.py), BSD-3-Clause; see LICENSE.

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Mul, S, Special } from '../core/nodes';
import { at, defined } from '../core/guard';
import { add, mul, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { NonlinearError, NotImplementedError } from '../core/errors';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { Complexes, ConditionSet, EmptySet, FiniteSet, ImageSet, Interval, Reals, SetOp, type SetExpr, imageSet, intersection, union } from '../sets/sets';
import { expand } from '../simplify/expand';
import { asEquation, nonlinsolve as finiteNonlinsolve } from './solve';
import { periodicity, solveset } from './inequalities';

/** Whether every subexpression is finite at the proposed solution. */
export function domainCheck(f: ExprLike, symbol: Sym, p: ExprLike): boolean {
  const point = sympify(p);
  if (point instanceof Special) return false;
  const check = (e: Expr): boolean => !(subs(e, [[symbol, point]]) instanceof Special) && e.args.every(check);
  return check(sympify(f));
}

/** Linear coefficients followed by the constant term; rejects nonlinear structure before expansion. */
export function linearCoeffs(eq: ExprLike, ...syms: Sym[]): Expr[] {
  if (new Set(syms.map((s) => s.key)).size !== syms.length) throw new RangeError('linearCoeffs: duplicate symbols');
  const zero = (): Expr[] => Array.from({ length: syms.length + 1 }, () => S.Zero);
  const visit = (e: Expr): Expr[] => {
    const i = syms.findIndex((s) => s.equals(e));
    if (i >= 0) { const out = zero(); out[i] = S.One; return out; }
    if (!syms.some((s) => e.has(s))) { const out = zero(); out[syms.length] = e; return out; }
    if (e instanceof Add) {
      const rows = e.args.map(visit);
      return zero().map((_, j) => add(...rows.map((r) => at(r, j))));
    }
    if (e instanceof Mul) {
      const dep = e.args.filter((a) => syms.some((s) => a.has(s)));
      if (dep.length !== 1) throw new NonlinearError('linearCoeffs: symbol-dependent cross-terms');
      const independent = mul(...e.args.filter((a) => !syms.some((s) => a.has(s))));
      return visit(at(dep, 0)).map((c) => mul(independent, c));
    }
    throw new NonlinearError('linearCoeffs: nonlinear in given generators');
  };
  return visit(sympify(eq));
}

/** Solve over the real domain. */
export function solvesetReal(f: ExprLike, symbol: Sym): SetExpr {
  return solveset(f, symbol, Reals);
}

function invert(f: ExprLike, y: ExprLike, x: Sym, domain: SetExpr): [Expr, SetExpr] {
  const expression = sympify(f), value = sympify(y);
  if (!expression.has(x) || value.has(x)) throw new RangeError('invert: f must depend on x and y must be independent of x');
  const solutions = solveset(add(expression, mul(-1, value)), x, domain);
  return solutions instanceof ConditionSet ? [expression, FiniteSet.of(value)] : [x, solutions];
}

/** Invert f(x) = y over the complex numbers, retaining unresolved equations. */
export function invertComplex(f: ExprLike, y: ExprLike, x: Sym): [Expr, SetExpr] {
  return invert(f, y, x, Complexes);
}

/** Invert f(x) = y over the real numbers, retaining unresolved equations. */
export function invertReal(f: ExprLike, y: ExprLike, x: Sym): [Expr, SetExpr] {
  return invert(f, y, x, Reals);
}

/** Finite solutions, or representatives in one period; NoMatch for other infinite sets. */
export function solvify(f: ExprLike, symbol: Sym, domain: SetExpr): Expr[] | NoMatchResult {
  const result = solveset(f, symbol, domain);
  if (result === EmptySet) return [];
  if (result instanceof ConditionSet) throw new NotImplementedError('solvify: solveset could not solve the equation');
  if (result instanceof FiniteSet) return [...result.args];
  const period = periodicity(f, symbol);
  const parts = result instanceof SetOp && result.op === 'Union' ? result.args : [result];
  if (period !== undefined && parts.every((s) => s instanceof ImageSet)) {
    const window = Interval.Ropen(0, period);
    const principal = union(...parts.map((s) => intersection(s, window)));
    if (principal instanceof FiniteSet) return [...principal.args];
  }
  return NoMatch;
}

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
