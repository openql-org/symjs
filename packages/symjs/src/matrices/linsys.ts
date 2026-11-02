// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Linear systems (SymPy linear_eq_to_matrix, linsolve and
 * solve_lin_sys): in the matrices layer so that polys and simplify can use
 * them without depending on the solvers layer.
 */

import { NonlinearError } from '../core/errors';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Mul, Pow, Rational, Rel, S, Sym } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { polyCoefficients } from '../polys/poly';
import { Poly, sortGens } from '../polys/sympoly';
import { expandMul } from '../simplify/expand';
import { cancel, fraction } from '../simplify/rational';
import { Matrix } from './matrix';
import { rref } from './linalg';

/** An equation Eq(a, b) as a - b. */
function asEquation(e: ExprLike): Expr {
  const x = sympify(e);
  if (x instanceof Rel && x.op === 'Eq') return add(x.lhs, mul(-1, x.rhs));
  return x;
}

/** Coefficient matrix and right-hand side of a linear system; undefined if nonlinear. */
export function linearEqToMatrix(eqs: readonly ExprLike[], syms: readonly Sym[]): [Matrix, Matrix] | undefined {
  const rows: Expr[][] = [];
  const rhs: Expr[] = [];
  for (const e0 of eqs) {
    const e = expandMul(asEquation(e0));
    const row: Expr[] = [];
    let rest = e;
    for (const s of syms) {
      const pc = polyCoefficients(e, s);
      if (!pc || [...pc.keys()].some((k) => k > 1)) return undefined;
      const c = pc.get(1) ?? S.Zero;
      if (syms.some((t) => t !== s && c.has(t))) return undefined;
      row.push(c);
      rest = add(rest, mul(-1, c, s));
    }
    rest = expandMul(rest);
    if (syms.some((s) => rest.has(s))) return undefined;
    rows.push(row);
    rhs.push(mul(-1, rest));
  }
  return [Matrix.of(rows), Matrix.col(...rhs)];
}

/**
 * Solve a linear system. Returns the solution tuple (free unknowns appear as
 * themselves), or undefined when inconsistent.
 */
export function linsolve(eqs: readonly ExprLike[], syms: readonly Sym[]): Expr[] | undefined {
  const lin = linearEqToMatrix(eqs, syms);
  if (!lin) throw new NonlinearError('linsolve: nonlinear system');
  const [A, b] = lin;
  return solveAugmented(A.hstack(b), syms);
}

/**
 * The coefficients of a linear system are rational functions with rational
 * coefficients of the parameters (SymPy's domain QQ(params) rather than EX).
 */
function rationalFunctionDomain(entries: readonly Expr[], syms: readonly Sym[]): boolean {
  const isRatPoly = (e: Expr): boolean => {
    if (e instanceof Rational) return true;
    if (e instanceof Sym) return !syms.some((s) => s.key === e.key);
    if (e instanceof Add || e instanceof Mul) return e.args.every(isRatPoly);
    if (e instanceof Pow) return e.exp instanceof Rational && e.exp.q === 1n && isRatPoly(e.base);
    return false;
  };
  return entries.every(isRatPoly);
}

/** An element of QQ(params) as SymPy prints it: numerator/denominator, expanded over a constant denominator. */
function fieldElement(v: Expr): Expr {
  const c = cancel(v);
  let [num, den] = fraction(c);
  if (den.isNumber) return expandMul(c);
  // the denominator with a positive leading coefficient in lex order (1 - y -> y - 1)
  try {
    const lc = Poly.from(den, sortGens([...freeSymbols(den)])).LC();
    if (lc.isNumber && lc.toNumber() < 0) [num, den] = [mul(-1, num), expandMul(mul(-1, den))];
  } catch {
    // not a polynomial: keep the sign
  }
  return mul(expandMul(num), pow(den, -1));
}

/** Solve [A | b] for syms. */
export function solveAugmented(aug: Matrix, syms: readonly Sym[]): Expr[] | undefined {
  const n = syms.length;
  const [R, pivots] = rref(aug);
  if (pivots.includes(n)) return undefined; // inconsistent
  // SymPy solve_lin_sys: over QQ(params) the solution is a polynomial in the free unknowns with
  // coefficients in the field; over EX each value is cancelled and its numerator distributed
  const field = rationalFunctionDomain(aug.data, syms);
  const sol: Expr[] = syms.map((s) => s);
  pivots.forEach((pc, i) => {
    const terms: Expr[] = [];
    let v: Expr = R.get(i, n);
    for (let j = 0; j < n; j++) {
      if (j === pc || pivots.includes(j)) continue;
      const c = mul(-1, R.get(i, j));
      v = add(v, mul(c, syms[j]!));
      if (field) terms.push(mul(fieldElement(c), syms[j]!));
    }
    if (field) sol[pc] = add(...terms, fieldElement(R.get(i, n)));
    else sol[pc] = expandMul(cancel(v));
  });
  return sol;
}

