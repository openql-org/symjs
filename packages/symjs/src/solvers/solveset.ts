// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (solvers/solveset.py), BSD-3-Clause; see LICENSE.

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, Constant, Fn, Mul, Pow, S, Special, Sym } from '../core/nodes';
import { isNegative, isNonNegative, isPositive } from '../core/assumptions';
import { at, defined } from '../core/guard';
import { add, mul, pow, sympify } from '../core/ops';
import { fn, log } from '../functions/elementary/elementary';
import { some, subs, xreplace } from '../core/traverse';
import { NonlinearError, NotImplementedError } from '../core/errors';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { Complexes, ConditionSet, EmptySet, FiniteSet, ImageSet, Interval, Reals, SetOp, type SetExpr, complement, imageSet, intersection, union } from '../sets/sets';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { asEquation, denoms, nonlinsolve as finiteNonlinsolve } from './solve';
import { periodicity, solveset } from './inequalities';
import { decompogen } from './decompogen';
import { functionRange } from './calculusutil';
import { Eq } from '../core/logic';

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
  return visit(asEquation(eq));
}

/** Solve over the real domain. */
export function solvesetReal(f: ExprLike, symbol: ExprLike): SetExpr {
  return solveset(f, symbol, Reals);
}

/** Solve over the complex domain. */
export function solvesetComplex(f: ExprLike, symbol: ExprLike): SetExpr {
  return solveset(f, symbol, Complexes);
}

/** Solve successive outer functions in a functional decomposition. */
export function solveDecomposition(f: ExprLike, symbol: Sym, domain: SetExpr): SetExpr {
  const expression = sympify(f);
  let values: SetExpr = FiniteSet.of(S.Zero);
  for (const g of decompogen(expression, symbol)) {
    const range = domain === Reals && g instanceof Fn && (g.name === 'sin' || g.name === 'cos') ? Interval.of(-1, 1) : functionRange(g, symbol, domain);
    values = range === Reals ? values : intersection(values, range);
    if (values === EmptySet) return EmptySet;
    const parts = values instanceof SetOp && values.op === 'Union' ? values.args : [values];
    const results: SetExpr[] = [];
    for (const part of parts) {
      if (part instanceof FiniteSet) {
        for (const value of part.args) results.push(solveset(add(g, mul(-1, value)), symbol, domain));
      } else if (part instanceof ImageSet) {
        const solutions = solveset(add(g, mul(-1, part.expr)), symbol, domain);
        const finite = solutions instanceof FiniteSet ? solutions : solutions instanceof SetOp && solutions.op === 'Intersection' ? solutions.args.find((s) => s instanceof FiniteSet) : undefined;
        if (finite instanceof FiniteSet) for (const value of finite.args) results.push(imageSet(part.variable, value, part.base));
        else return new ConditionSet(symbol, Eq(expression, 0), domain);
      } else return new ConditionSet(symbol, Eq(expression, 0), domain);
    }
    values = union(...results);
  }
  return values;
}

function invert(f: ExprLike, y: ExprLike, x: Sym, domain: SetExpr): [Expr, SetExpr] {
  const expression = sympify(f), value = sympify(y);
  if (![...expression.freeSymbols()].some((s) => s.equals(x)) || [...value.freeSymbols()].some((s) => s.equals(x))) throw new RangeError('invert: f must depend on x and y must be independent of x');
  const solutions = solveset(add(expression, mul(-1, value)), x, domain);
  return solutions instanceof ConditionSet ? [expression, FiniteSet.of(value)] : [x, solutions];
}

/** Invert f(x) = y over the complex numbers, retaining unresolved equations. */
export function invertComplex(f: ExprLike, y: ExprLike, x: Sym): [Expr, SetExpr] {
  return invert(f, y, x, Complexes);
}

/** Invert f(x) = y over the real numbers, retaining unresolved equations. */
export function invertReal(f: ExprLike, y: ExprLike, x: Sym): [Expr, SetExpr] {
  const expression = sympify(f), value = sympify(y);
  if (![...expression.freeSymbols()].some((s) => s.equals(x)) || [...value.freeSymbols()].some((s) => s.equals(x))) throw new RangeError('invert: f must depend on x and y must be independent of x');
  const visit = (e: Expr, values: readonly Expr[]): [Expr, SetExpr] => {
    if (e.equals(x) || values.length === 0) {
      const known = values.filter((v) => v instanceof Fn && v.name === 'acsch' && (isPositive(at(v.args, 0)) === true || isNegative(at(v.args, 0)) === true));
      return [x, union(FiniteSet.of(...known), intersection(FiniteSet.of(...values.filter((v) => !known.includes(v))), Reals))];
    }
    if (e instanceof Add || e instanceof Mul) {
      const independent = e.args.filter((a) => !a.has(x));
      if (independent.length) {
        const dependent = e.args.filter((a) => a.has(x));
        const c = e instanceof Add ? add(...independent) : mul(...independent);
        return visit(e instanceof Add ? add(...dependent) : mul(...dependent), values.map((v) => e instanceof Add ? add(v, mul(-1, c)) : mul(v, pow(c, -1))));
      }
    }
    if (e instanceof Fn) {
      const arg = at(e.args, 0);
      if (e.name === 'log') return visit(arg, values.map((v) => pow(S.E, v)));
      if (e.name === 'abs' && values.every((v) => isNonNegative(v) === true)) return visit(arg, values.flatMap((v) => [v, mul(-1, v)]));
      const inverse: Readonly<Partial<Record<FnName, FnName>>> = { sinh: 'asinh', cosh: 'acosh', tanh: 'atanh', coth: 'acoth', sech: 'asech', csch: 'acsch' };
      const name = inverse[e.name];
      if (name !== undefined) {
        return visit(arg, values.flatMap((v) => {
          const root = fn(name, [v]);
          return e.name === 'cosh' || e.name === 'sech' ? [mul(-1, root), root] : [root];
        }));
      }
    }
    if (e instanceof Pow && !e.base.has(x) && isPositive(e.base) === true) return visit(e.exp, values.filter((v) => !v.equals(S.Zero)).map((v) => mul(log(v), pow(log(e.base), -1))));
    if (e instanceof Pow && e.exp instanceof Constant && (e.exp.name === 'pi' || e.exp.name === 'E') && values.every((v) => isNegative(v) === true)) return [x, EmptySet];
    const results = values.map((v) => invert(e, v, x, Reals));
    if (results.every(([lhs]) => lhs.equals(x))) return [x, union(...results.map(([, rhs]) => rhs))];
    return [e, FiniteSet.of(...values)];
  };
  return visit(expression, [value]);
}

/** Finite solutions, or representatives in one period; NoMatch for other infinite sets. */
export function solvify(f: ExprLike, symbol: Sym, domain: SetExpr): Expr[] | NoMatchResult {
  const result = solveset(f, symbol, domain);
  if (result === EmptySet) return [];
  if (result instanceof ConditionSet) throw new NotImplementedError('solvify: solveset could not solve the equation');
  if (result instanceof FiniteSet) return [...result.args];
  const period = periodicity(f, symbol);
  const parts = result instanceof SetOp && result.op === 'Union' ? result.args : [result];
  if (period === undefined) {
    const finite = parts.flatMap((part) => part instanceof FiniteSet ? part.args : []);
    return finite.length ? finite : NoMatch;
  }
  if (parts.every((s) => s instanceof ImageSet)) {
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
  if (eqs.length === 0) return [];
  if (symbols.length === 0) {
    if (eqs.some((e) => e.freeSymbols().size > 0)) throw new RangeError('nonlinsolve: at least one unknown is required');
    return eqs.some((e) => !e.equals(S.Zero)) ? [] : [[]];
  }
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
  try {
    // Solve over the complex domain even when an unknown has a real assumption.
    return finiteNonlinsolve(eqs, symbols, { check: false }).filter(isFiniteTuple);
  } catch (error) {
    if (!(error instanceof NotImplementedError)) throw error;
    return substituteFinite(eqs, symbols);
  }
}

function isFiniteTuple(values: readonly Expr[]): boolean {
  return !values.some((value) => some(value, (term) => term instanceof Special));
}

/** Eliminate one unknown at a time using the finite branches of solveset. */
function substituteFinite(system: readonly Expr[], symbols: readonly Sym[]): Expr[][] {
  const exclusions = system.flatMap((e) => [...denoms(e, ...symbols)]);
  const solveRemaining = (equations: readonly Expr[], remaining: readonly Sym[], values: readonly Expr[]): Expr[][] => {
    const pending = equations.filter((e) => !e.equals(S.Zero));
    if (!pending.length) return [[...values]];
    const withUnknowns = pending.map((e) => ({ e, vars: remaining.filter((s) => e.has(s)) }));
    if (withUnknowns.some(({ vars }) => !vars.length)) return [];
    withUnknowns.sort((a, b) => a.vars.length - b.vars.length);
    for (const { e, vars } of withUnknowns) {
      for (const symbol of vars) {
        const complex = solveset(e, symbol, Complexes);
        if (complex === EmptySet) return [];
        if (!(complex instanceof FiniteSet)) continue;
        const real = solveset(e, symbol, Reals);
        const candidates = new Map([...complex.args, ...(real instanceof FiniteSet ? real.args : [])].map((r) => [r.key, r]));
        return [...candidates.values()].flatMap((root) => {
          const replacement = [[symbol, root]] as const;
          const next = pending.filter((f) => f !== e).map((f) => cancel(xreplace(f, replacement)));
          return solveRemaining(next, remaining.filter((s) => !s.equals(symbol)), values.map((v) => xreplace(v, replacement)));
        });
      }
    }
    throw new NotImplementedError('nonlinsolve: nonlinear substitution has an unresolved solution set');
  };
  const solutions = solveRemaining(system, symbols, symbols).filter(isFiniteTuple);
  const withExclusions = solutions.map((values) => {
    const mapping = symbols.map((s, i): [Expr, Expr] => [s, at(values, i)]);
    const forbidden = [...exclusions, ...values.flatMap((v) => [...denoms(v, ...symbols)])].map((d) => cancel(xreplace(d, mapping)));
    return { values, forbidden };
  });
  const admissible = withExclusions.filter(({ forbidden }) => !forbidden.some((d) => d.equals(S.Zero)));
  const accepted = new Map<string, Expr[]>();
  for (const { values, forbidden } of admissible) {
    const row = values.map((v) => {
      if (!(v instanceof Sym) || !symbols.some((s) => s.equals(v))) return v;
      const excluded = forbidden.filter((d) => d.has(v) && symbols.every((s) => s.equals(v) || !d.has(s))).map((d) => solveset(d, v));
      return excluded.some((set) => set !== EmptySet) ? complement(FiniteSet.of(v), union(...excluded)) : v;
    });
    accepted.set(JSON.stringify(row.map((v) => v.key)), row);
  }
  return [...accepted.values()];
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
    if (system.length === 0) continue;
    const solutions = pending.length ? free.length ? nonlinsolve(pending, free) : [] : [free];
    for (const solution of solutions) {
      const assignments: [Expr, Expr][] = [...entries, ...free.map((v, i): [Expr, Expr] => [v, at(solution, i)])];
      if (exclude.some((e) => expand(subs(sympify(e), assignments)).equals(S.Zero))) continue;
      out.push(allSymbols.map((v) => assignments.find(([k]) => k.equals(v))?.[1] ?? v));
    }
  }
  return out;
}
