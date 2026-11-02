// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of the solvers whose implementations report "no
 * result" internally (docs/api-policy.md): no solution is EmptySet, a
 * missing form NoMatch, no closed form Unsolved, three-valued answers Truth,
 * a nonlinear system a NonlinearError.
 */

import { Expr, ExprLike, Sym } from '../core/nodes';
import { sympify } from '../core/ops';
import { NonlinearError } from '../core/errors';
import { NoMatchResult, Truth, UnsolvedResult, orNoMatch, orUnsolved, toTruth } from '../core/truth';
import { EmptySet, Reals, type SetExpr } from '../sets/sets';
import type { Matrix } from '../matrices/matrix';
import * as S from './solve';
import * as I from './inequalities';
import * as O from './ode';
import * as R from './recurr';

/** SymPy linear_eq_to_matrix: [A, b] with A x = b; throws NonlinearError for nonlinear equations. */
export function linearEqToMatrix(eqs: readonly ExprLike[], syms: readonly Sym[]): [Matrix, Matrix] {
  const r = S.linearEqToMatrix(eqs, syms);
  if (!r) throw new NonlinearError('linear_eq_to_matrix: the equations are not linear in the symbols');
  return r;
}

/**
 * SymPy linsolve: the solution of a linear system as values of the symbols
 * (free symbols stand for parameters), or EmptySet when it is inconsistent.
 */
export function linsolve(eqs: readonly ExprLike[], syms: readonly Sym[]): Expr[] | typeof EmptySet {
  const [A, b] = linearEqToMatrix(eqs, syms);
  return S.solveAugmented(A.hstack(b), syms) ?? EmptySet;
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
