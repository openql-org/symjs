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

/**
 * Extracts the coefficient matrix and right-hand side of a linear system without changing the order of the unknowns.
 *
 * @remarks SymPy returns `Matrix([[c, 0, 1], [0, 1, 1], [1, -1, 0]])`.
 *
 * @param eqs - The equations to solve simultaneously.
 * @param syms - The unknowns in the desired order.
 * @returns The coefficient matrix and the right-hand-side column.
 * @throws NonlinearError when an equation is nonlinear in the unknowns.
 * @throws RangeError when the unknown list is empty or contains duplicates.
 * @throws TypeError when an equation is a Boolean value or an inequality.
 * @see SymPy `sympy.solvers.solveset.linear_eq_to_matrix`
 * @example
 * ```ts
 * import { ex, linearEqToMatrix, symbols } from '@symjs/symjs';
 *
 * const [x, y, z] = symbols('x y z');
 * linearEqToMatrix([ex`c*x - c + z - 1`, ex`y + z`, ex`x - y`], [x, y, z])[0]; // => Matrix([
 * //   [c,  0, 1],
 * //   [0,  1, 1],
 * //   [1, -1, 0]])
 * ```
 */
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
 * The solution of a linear system as values of the symbols
 * (free symbols stand for parameters), or EmptySet when it is inconsistent.
 *
 * @param eqs - The equations to solve simultaneously.
 * @param syms - The unknowns in the desired order.
 * @returns Solution values in variable order, or `EmptySet` for an inconsistent system.
 * @throws NonlinearError when an equation is nonlinear in the unknowns.
 * @see SymPy `sympy.solvers.solveset.linsolve`
 * @example
 * ```ts
 * import { ex, linsolve, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * linsolve([ex`x + y - 3`, ex`x - y - 1`], [x, y]); // => [2, 1]
 * ```
 */
export function linsolve(eqs: readonly ExprLike[], syms: readonly Expr[]): Expr[] | typeof EmptySet {
  if (eqs.length && !syms.length) throw new RangeError('linsolve: symbols are required');
  if (new Set(syms.map((s) => s.key)).size !== syms.length) throw new RangeError('linsolve: duplicate symbols');
  const result = _linsolve(eqs, syms);
  return result instanceof Map ? syms.map((s) => defined(result.get(s))) : result;
}

/**
 * Solves an augmented linear system [A | b], preserving free parameters.
 *
 * @param augmented - The matrix of coefficients followed by the right-hand side.
 * @param syms - The unknowns in the desired order.
 * @returns Solution values in variable order, or `EmptySet` for an inconsistent system.
 * @throws RangeError when the augmented matrix has the wrong number of columns.
 */
export function linsolveAugmented(augmented: Matrix, syms: readonly Sym[]): Expr[] | typeof EmptySet {
  if (augmented.cols !== syms.length + 1) throw new RangeError('Augmented matrix must have one more column than the number of unknowns');
  return S.solveAugmented(augmented, syms) ?? EmptySet;
}

/**
 * Solves an augmented linear system, retaining assignments for determined variables.
 *
 * @param augmented - The matrix of coefficients followed by the right-hand side.
 * @param syms - The unknowns in the desired order.
 * @returns A map assigning solved variables, or `EmptySet` for an inconsistent system.
 * @see SymPy `sympy.solvers.solvers.solve_linear_system`
 * @example
 * ```ts
 * import { Matrix, solveLinearSystem, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * solveLinearSystem(Matrix.of([[1, 4, 2], [-2, 1, 14]]), [x, y]); // => {x: -6, y: 2}
 * ```
 */
export function solveLinearSystem(augmented: Matrix, syms: readonly Sym[]): Map<Sym, Expr> | typeof EmptySet {
  const result = linsolveAugmented(augmented, syms);
  return Array.isArray(result) ? new Map(syms.flatMap((s, i): [Sym, Expr][] => at(result, i).equals(s) ? [] : [[s, at(result, i)]])) : result;
}

/**
 * The order of a homogeneous function, or NoMatch.
 *
 * @param eq - The equation, or an expression equal to zero.
 * @param symbols - The unknowns in the desired order.
 * @returns The scaling degree, or `NoMatch` if the expression is not homogeneous.
 * @see SymPy `sympy.solvers.ode.ode.homogeneous_order`
 * @example
 * ```ts
 * import { ex, homogeneousOrder } from '@symjs/symjs';
 * homogeneousOrder(ex`f(x)`, ex`f(x)`, ex`x`); // => 1
 * ```
 */
export function homogeneousOrder(eq: ExprLike, ...symbols: Expr[]): Expr | NoMatchResult {
  return orNoMatch(O.homogeneousOrder(eq, ...symbols));
}

/**
 * The fundamental period of f in x, or NoMatch when none is found.
 *
 * @param f - The function or expression to analyze.
 * @param x - The independent variable.
 * @returns A period, or `NoMatch` if none is found.
 * @see SymPy `sympy.calculus.util.periodicity`
 * @example
 * ```ts
 * import { ex, periodicity, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * periodicity(ex`sin(x)*cos(x)`, x); // => pi
 * ```
 */
export function periodicity(f: ExprLike, x: Sym): Expr | NoMatchResult {
  return orNoMatch(I.periodicity(f, x));
}

/**
 * Tests whether a function is nondecreasing on an interval.
 *
 * @param f - The function or expression to analyze.
 * @param iv - The interval on which to test monotonicity.
 * @param x - The independent variable.
 * @returns The monotonicity test, or `'unknown'` when undecidable.
 * @see SymPy `sympy.calculus.singularities.is_increasing`
 * @example
 * ```ts
 * import { Interval, ex, isIncreasing } from '@symjs/symjs';
 * isIncreasing(ex`-x**2`, Interval.Ropen(0, ex`oo`)); // => False
 * ```
 */
export const isIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isIncreasing(sympify(f), iv, x));
/**
 * Tests whether a function increases strictly on an interval.
 *
 * @param f - The function or expression to analyze.
 * @param iv - The interval on which to test monotonicity.
 * @param x - The independent variable.
 * @returns The monotonicity test, or `'unknown'` when undecidable.
 * @see SymPy `sympy.calculus.singularities.is_strictly_increasing`
 * @example
 * ```ts
 * import { Interval, ex, isStrictlyIncreasing } from '@symjs/symjs';
 * isStrictlyIncreasing(ex`-x**2`, Interval.Ropen(0, ex`oo`)); // => False
 * ```
 */
export const isStrictlyIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isStrictlyIncreasing(sympify(f), iv, x));
/**
 * Tests whether a function is nonincreasing on an interval.
 *
 * @param f - The function or expression to analyze.
 * @param iv - The interval on which to test monotonicity.
 * @param x - The independent variable.
 * @returns The monotonicity test, or `'unknown'` when undecidable.
 * @see SymPy `sympy.calculus.singularities.is_decreasing`
 * @example
 * ```ts
 * import { Interval, ex, isDecreasing } from '@symjs/symjs';
 * isDecreasing(ex`-x**2`, Interval.Lopen(ex`-oo`, 0)); // => False
 * ```
 */
export const isDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isDecreasing(sympify(f), iv, x));
/**
 * Tests whether a function decreases strictly on an interval.
 *
 * @param f - The function or expression to analyze.
 * @param iv - The interval on which to test monotonicity.
 * @param x - The independent variable.
 * @returns The monotonicity test, or `'unknown'` when undecidable.
 * @see SymPy `sympy.calculus.singularities.is_strictly_decreasing`
 * @example
 * ```ts
 * import { Interval, ex, isStrictlyDecreasing } from '@symjs/symjs';
 * isStrictlyDecreasing(ex`-x**2`, Interval.Lopen(ex`-oo`, 0)); // => False
 * ```
 */
export const isStrictlyDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isStrictlyDecreasing(sympify(f), iv, x));
/**
 * Tests whether a function is nondecreasing or nonincreasing on an interval.
 *
 * @param f - The function or expression to analyze.
 * @param iv - The interval on which to test monotonicity.
 * @param x - The independent variable.
 * @returns The monotonicity test, or `'unknown'` when undecidable.
 * @see SymPy `sympy.calculus.singularities.is_monotonic`
 * @example
 * ```ts
 * import { Interval, ex, isMonotonic } from '@symjs/symjs';
 * isMonotonic(ex`-x**2`, Interval.open(ex`-oo`, ex`oo`)); // => False
 * ```
 */
export const isMonotonic = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): Truth => toTruth(I.isMonotonic(sympify(f), iv, x));

/**
 * The solution of a recurrence, or Unsolved.
 *
 * @param f - The recurrence written with zero right-hand side.
 * @param y - The sequence evaluated at its index.
 * @param init - The initial conditions.
 * @returns The solution of the recurrence, or `Unsolved`.
 * @see SymPy `sympy.solvers.recurr.rsolve`
 * @example
 * ```ts
 * import { ex, rsolve } from '@symjs/symjs';
 * rsolve(ex`2*n*(n + 1)*y(n) + (n - 1)*y(n + 2) - (n**2 + 3*n - 2)*y(n + 1)`, ex`y(n)`); // => 2**n*C0 + C1*factorial(n)
 * ```
 */
export function rsolve(f: ExprLike, y: Expr, init?: [ExprLike, ExprLike][]): Expr | UnsolvedResult {
  return orUnsolved(R.rsolve(f, y, init));
}
/**
 * A polynomial solution and its constants, or Unsolved.
 *
 * @remarks SymPy returns `C0 + n**4 - 2*n**3 + n**2`.
 *
 * @param coeffs - Coefficients ordered by increasing shift of the unknown sequence.
 * @param f - The inhomogeneous term.
 * @param n - The recurrence index.
 * @param shift - The initial index shift for the polynomial ansatz.
 * @returns A solution and its arbitrary constants, or `Unsolved`.
 * @see SymPy `sympy.solvers.recurr.rsolve_poly`
 * @example
 * ```ts
 * import { ex, rsolvePoly, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n', { integer: true });
 * rsolvePoly([-1, 1], ex`4*${n}**3`, n); // => [C0 + n**4 - 2*n**3 + n**2, [C0]]
 * ```
 */
export function rsolvePoly(coeffs: readonly ExprLike[], f: ExprLike, n: Sym, shift = 0): [Expr, Sym[]] | UnsolvedResult {
  return orUnsolved(R.rsolvePoly(coeffs, f, n, shift));
}
/**
 * A rational solution and its constants, or Unsolved.
 *
 * @remarks SymPy returns `C0*(2*x - 3)/(2*(x**2 - 1))`.
 *
 * @param coeffs - Coefficients ordered by increasing shift of the unknown sequence.
 * @param f - The inhomogeneous term.
 * @param n - The recurrence index.
 * @returns A solution and its arbitrary constants, or `Unsolved`.
 * @see SymPy `sympy.solvers.recurr.rsolve_ratio`
 * @example
 * ```ts
 * import { ex, rsolveRatio, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * rsolveRatio([ex`-2*x**3 + x**2 + 2*x - 1`, ex`2*x**3 + x**2 - 6*x`, ex`-2*x**3 - 11*x**2 - 18*x - 9`, ex`2*x**3 + 13*x**2 + 22*x + 8`], 0, x); // => [C0*(2*x - 3)/(2*(x**2 - 1)), [C0]]
 * ```
 */
export function rsolveRatio(coeffs: readonly ExprLike[], f: ExprLike, n: Sym): [Expr, Sym[]] | UnsolvedResult {
  return orUnsolved(R.rsolveRatio(coeffs, f, n));
}
/**
 * A hypergeometric solution and its constants, or Unsolved.
 *
 * @remarks SymPy returns `C0*(1/2 - sqrt(5)/2)**x + C1*(1/2 + sqrt(5)/2)**x`.
 *
 * @param coeffs - Coefficients ordered by increasing shift of the unknown sequence.
 * @param f - The inhomogeneous term.
 * @param n - The recurrence index.
 * @returns A solution and its arbitrary constants, or `Unsolved`.
 * @see SymPy `sympy.solvers.recurr.rsolve_hyper`
 * @example
 * ```ts
 * import { rsolveHyper, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * rsolveHyper([-1, -1, 1], 0, x); // => [C0*(1/2 - sqrt(5)/2)**x + C1*(1/2 + sqrt(5)/2)**x, [C0, C1]]
 * ```
 */
export function rsolveHyper(coeffs: readonly ExprLike[], f: ExprLike, n: Sym): [Expr, Sym[]] | UnsolvedResult {
  return orUnsolved(R.rsolveHyper(coeffs, f, n));
}
