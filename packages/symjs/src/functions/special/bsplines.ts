// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sympy/functions/special/bsplines.py,
// Copyright (c) SymPy Development Team, BSD-3-Clause (see LICENSE).

/** Piecewise polynomial B-spline bases and interpolating splines. */
import { at, first, last } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { S } from '../../core/nodes';
import { add, mul, pow, sympify } from '../../core/ops';
import { Ge, Le, piecewise } from '../../core/logic';
import { and } from '../../core/boolalg';
import { isPositive, isZero } from '../../core/assumptions';
import { expandMul } from '../../simplify/expand';
import type { IntLike } from '../../ntheory/intutil';
import { asInt } from '../../ntheory/intutil';

const sub = (a: ExprLike, b: ExprLike): Expr => add(a, mul(-1, b));
const quotient = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));
function degree(value: IntLike): number {
  const n = Number(asInt(value));
  if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('spline degree and index must be nonnegative integers');
  return n;
}

/** Cox-de Boor recurrence, retaining one polynomial per knot interval. */
function pieces(d: number, knots: readonly Expr[], n: number, x: Expr): Expr[] {
  if (n + d + 1 >= knots.length) throw new RangeError('n + d + 1 must be less than the number of knots');
  if (d === 0) return knots.slice(1).map((_, i) => i === n ? S.One : S.Zero);
  const left = sub(at(knots, n + d), at(knots, n));
  const right = sub(at(knots, n + d + 1), at(knots, n + 1));
  const a = isZero(left) === true ? knots.slice(1).map(() => S.Zero) : pieces(d - 1, knots, n, x).map((e) => mul(quotient(sub(x, at(knots, n)), left), e));
  const b = isZero(right) === true ? knots.slice(1).map(() => S.Zero) : pieces(d - 1, knots, n + 1, x).map((e) => mul(quotient(sub(at(knots, n + d + 1), x), right), e));
  return a.map((e, i) => expandMul(add(e, at(b, i))));
}
function asPiecewise(parts: readonly Expr[], knots: readonly Expr[], x: Expr, defaultZero: boolean): Expr {
  const pairs: [Expr, Expr][] = [];
  parts.forEach((e, i) => {
    if (isZero(e) !== true || (!defaultZero && !at(knots, i).equals(at(knots, i + 1)))) pairs.push([e, and(Ge(x, at(knots, i)), Le(x, at(knots, i + 1)))]);
  });
  if (defaultZero) pairs.push([S.Zero, S.true]);
  return piecewise(...pairs);
}

/** The n-th B-spline of degree d on the given knot vector. */
export function bsplineBasis(d: IntLike, knots: readonly ExprLike[], n: IntLike, x: Expr): Expr {
  const ks = knots.map(sympify);
  return asPiecewise(pieces(degree(d), ks, degree(n), x), ks, x, true);
}

/** All B-splines of degree d on the given knot vector. */
export function bsplineBasisSet(d: IntLike, knots: readonly ExprLike[], x: Expr): Expr[] {
  const order = degree(d);
  if (knots.length < order + 2) throw new RangeError('not enough knots for the spline degree');
  return Array.from({ length: knots.length - order - 1 }, (_, i) => bsplineBasis(order, knots, i, x));
}

/** Spline of degree d interpolating strictly increasing real abscissae. */
export function interpolatingSpline(d: IntLike, x: Expr, X: readonly ExprLike[], Y: readonly ExprLike[]): Expr {
  const order = degree(d), xs = X.map(sympify), ys = Y.map(sympify);
  if (order === 0 || xs.length <= order || xs.length !== ys.length) throw new RangeError('interpolation requires 0 < degree < number of matching X and Y values');
  if (xs.slice(1).some((v, i) => isPositive(sub(v, at(xs, i))) !== true)) throw new RangeError('X must be strictly increasing real coordinates');
  const j = Math.floor((order + 1) / 2);
  const interior = order % 2 ? xs.slice(j, -j) : xs.slice(j, -j - 1).map((v, i) => quotient(add(v, at(xs, j + i + 1)), 2));
  const knots = [...Array<Expr>(order + 1).fill(first(xs)), ...interior, ...Array<Expr>(order + 1).fill(last(xs))];
  const basis = bsplineBasisSet(order, knots, x);
  const rows = xs.map((v, i) => [...basis.map((b) => b.subs(x, v)), at(ys, i)]);
  // Solve the collocation system here so the L1 special functions do not
  // import the L2 matrix package. The Schoenberg-Whitney conditions give positive leading minors,
  // so elimination needs no row exchanges.
  for (let c = 0; c < xs.length; c++) {
    const pivot = at(rows, c);
    const normalized = pivot.map((e) => quotient(e, at(pivot, c)));
    rows[c] = normalized;
    rows.forEach((row, i) => {
      if (i !== c) rows[i] = row.map((e, k) => expandMul(sub(e, mul(at(row, c), at(normalized, k)))));
    });
  }
  const coefficients = rows.map((row) => last(row));
  const terms = basis.map((_, i) => pieces(order, knots, i, x));
  const result = knots.slice(1).map((_, i) => at(knots, i).equals(at(knots, i + 1)) ? S.Zero : expandMul(add(...terms.map((part, k) => mul(at(coefficients, k), at(part, i))))));
  return asPiecewise(result, knots, x, false);
}
