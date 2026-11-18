// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of the solvers whose implementations report "no
 * result" internally (docs/api-policy.md): no solution is EmptySet, a
 * missing form NoMatch, no closed form Unsolved, three-valued answers Truth,
 * a nonlinear system a NonlinearError.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { at, defined } from '../core/guard';
import { add, mul, sympify } from '../core/ops';
import { BoolAtom, Rel } from '../core/nodes';
import type { NoMatchResult, Truth, UnsolvedResult } from '../core/truth';
import { orNoMatch, orUnsolved, toTruth } from '../core/truth';
import { EmptySet, Reals, type SetExpr } from '../sets/sets';
import { Matrix } from '../matrices/matrix';
import { linearCoeffs } from './solveset';
import * as S from './solve';
import * as I from './inequalities';
import * as O from './ode';
import * as R from './recurr';
import { _linsolve } from '../polys/matrices/linsolve';

/** SymPy linear_eq_to_matrix: [A, b] with A x = b; throws NonlinearError for nonlinear equations. */
export function linearEqToMatrix(eqs: readonly ExprLike[], syms: readonly Sym[]): [Matrix, Matrix] {
  if (!syms.length) throw new RangeError('linearEqToMatrix: symbols are required');
  if (new Set(syms.map((s) => s.key)).size !== syms.length) throw new RangeError('linearEqToMatrix: duplicate symbols');
  const rows = eqs.map((eq) => {
    const e = sympify(eq);
    if (e instanceof BoolAtom || (e instanceof Rel && e.op !== 'Eq')) throw new TypeError('linearEqToMatrix: an expression or equality is required');
    if (e instanceof Rel) {
      const lhs = linearCoeffs(e.lhs, ...syms), rhs = linearCoeffs(e.rhs, ...syms);
      return lhs.map((c, i) => add(c, mul(-1, at(rhs, i))));
    }
    return linearCoeffs(e, ...syms);
  });
  return [Matrix.fromFunction(rows.length, syms.length, (i, j) => at(at(rows, i), j)), Matrix.fromFunction(rows.length, 1, (i) => mul(-1, at(at(rows, i), syms.length)))];
}

/**
 * SymPy linsolve: the solution of a linear system as values of the symbols
 * (free symbols stand for parameters), or EmptySet when it is inconsistent.
 */
export function linsolve(eqs: readonly ExprLike[], syms: readonly Expr[]): Expr[] | typeof EmptySet {
  if (eqs.length && !syms.length) throw new RangeError('linsolve: symbols are required');
  if (new Set(syms.map((s) => s.key)).size !== syms.length) throw new RangeError('linsolve: duplicate symbols');
  const result = _linsolve(eqs, syms);
  return result instanceof Map ? syms.map((s) => defined(result.get(s))) : result;
}

/** Solve an augmented linear system [A | b], preserving free parameters. */
export function linsolveAugmented(augmented: Matrix, syms: readonly Sym[]): Expr[] | typeof EmptySet {
  if (augmented.cols !== syms.length + 1) throw new RangeError('Augmented matrix must have one more column than the number of unknowns');
  return S.solveAugmented(augmented, syms) ?? EmptySet;
}

/** SymPy solve_linear_system: solved variables only, or EmptySet if inconsistent. */
export function solveLinearSystem(augmented: Matrix, syms: readonly Sym[]): Map<Sym, Expr> | typeof EmptySet {
  const result = linsolveAugmented(augmented, syms);
  return Array.isArray(result) ? new Map(syms.flatMap((s, i): [Sym, Expr][] => at(result, i).equals(s) ? [] : [[s, at(result, i)]])) : result;
}

/** SymPy homogeneous_order: the order of a homogeneous function, or NoMatch. */
export function homogeneousOrder(eq: ExprLike, ...symbols: Expr[]): Expr | NoMatchResult {
  return orNoMatch(O.homogeneousOrder(eq, ...symbols));
}

/** SymPy periodicity: the fundamental period of f in x, or NoMatch when none is found. */
export function periodicity(f: ExprLike, x: Sym): Expr | NoMatchResult {
  return orNoMatch(I.periodicity(f, x));
}

/** SymPy is_increasing (f nondecreasing on the interval). */
export const isIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isIncreasing(sympify(f), iv, x));
/** SymPy is_strictly_increasing. */
export const isStrictlyIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isStrictlyIncreasing(sympify(f), iv, x));
/** SymPy is_decreasing. */
export const isDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isDecreasing(sympify(f), iv, x));
/** SymPy is_strictly_decreasing. */
export const isStrictlyDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isStrictlyDecreasing(sympify(f), iv, x));
/** SymPy is_monotonic. */
export const isMonotonic = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isMonotonic(sympify(f), iv, x));

/** SymPy rsolve: the solution of a recurrence, or Unsolved. */
export function rsolve(f: ExprLike, y: Expr, init?: [ExprLike, ExprLike][]): Expr | UnsolvedResult {
  return orUnsolved(R.rsolve(f, y, init));
}
/** SymPy rsolve_poly: a polynomial solution and its constants, or Unsolved. */
export function rsolvePoly(coeffs: readonly ExprLike[], f: ExprLike, n: Sym, shift = 0): [Expr, Sym[]] | UnsolvedResult {
  return orUnsolved(R.rsolvePoly(coeffs, f, n, shift));
}
/** SymPy rsolve_ratio: a rational solution and its constants, or Unsolved. */
export function rsolveRatio(coeffs: readonly ExprLike[], f: ExprLike, n: Sym): [Expr, Sym[]] | UnsolvedResult {
  return orUnsolved(R.rsolveRatio(coeffs, f, n));
}
/** SymPy rsolve_hyper: a hypergeometric solution and its constants, or Unsolved. */
export function rsolveHyper(coeffs: readonly ExprLike[], f: ExprLike, n: Sym): [Expr, Sym[]] | UnsolvedResult {
  return orUnsolved(R.rsolveHyper(coeffs, f, n));
}
