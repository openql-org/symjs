// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, assumptions/refine.py, BSD-3-Clause; see LICENSE.

/** Individual assumption refinement handlers. A missing refinement is NoMatch. */
import type { Expr, ExprLike } from '../core/nodes';
import { Add, ExtensionExpr, Pow, Rational, S } from '../core/nodes';
import type { Assumption } from '../core/refine';
import { Q, ask, refine } from '../core/refine';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { at, pair } from '../core/guard';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { atan, im } from '../functions/elementary/elementary';

/** SymPy refine_Pow: remove even parts of exponents of -1, and refine real powers. */
export function refinePow(expr: ExprLike, assumptions: Assumption = true): Expr | NoMatchResult {
  const e = sympify(expr);
  if (!(e instanceof Pow)) return NoMatch;
  if (e.base.equals(S.NegOne)) {
    if (ask(Q.even(e.exp), assumptions) === true) return S.One;
    if (ask(Q.odd(e.exp), assumptions) === true) return S.NegOne;
  }
  if (e.base.equals(S.NegOne) && e.exp instanceof Add) {
    let parity = 0;
    const terms: Expr[] = [];
    for (const t of e.exp.args) {
      if (ask(Q.even(t), assumptions) === true) continue;
      if (ask(Q.odd(t), assumptions) === true) parity++;
      else terms.push(t);
    }
    const result = pow(-1, add(...terms, parity % 2));
    if (!result.equals(e)) return result;
  }
  const result = refine(e, assumptions);
  return result.equals(e) ? NoMatch : result;
}

/** SymPy refine_abs: simplify an absolute value when its sign is known. */
export function refineAbs(expr: ExprLike, assumptions: Assumption = true): Expr | NoMatchResult {
  const e = sympify(expr);
  const result = refine(e, assumptions);
  return result.equals(e) ? NoMatch : result;
}

/** SymPy refine_arg: the argument of a positive or negative real value. */
export function refineArg(expr: ExprLike, assumptions: Assumption = true): Expr | NoMatchResult {
  const x = at(sympify(expr).args, 0);
  if (ask(Q.positive(x), assumptions) === true) return S.Zero;
  if (ask(Q.negative(x), assumptions) === true) return S.Pi;
  return NoMatch;
}

/** SymPy refine_atan2: select the quadrant under the given assumptions. */
export function refineAtan2(expr: ExprLike, assumptions: Assumption = true): Expr {
  const e = sympify(expr);
  const [y, x] = pair(e.args);
  const ratio = (): Expr => atan(mul(y, pow(x, -1)));
  if (ask(Q.positive(x), assumptions) === true && ask(Q.real(y), assumptions) === true) return ratio();
  if (ask(Q.negative(x), assumptions) === true) {
    if (ask(Q.negative(y), assumptions) === true) return add(ratio(), mul(-1, S.Pi));
    if (ask(Q.positive(y), assumptions) === true) return add(ratio(), S.Pi);
    if (ask(Q.zero(y), assumptions) === true) return S.Pi;
  }
  if (ask(Q.zero(x), assumptions) === true) {
    if (ask(Q.positive(y), assumptions) === true) return mul(S.Half, S.Pi);
    if (ask(Q.negative(y), assumptions) === true) return mul(Rational.of(-1, 2), S.Pi);
    if (ask(Q.zero(y), assumptions) === true) return S.NaN;
  }
  return e;
}

/** SymPy refine_re: real part under assumptions. */
export function refineRe(expr: ExprLike, assumptions: Assumption = true): Expr {
  const e = sympify(expr);
  const x = at(e.args, 0);
  if (ask(Q.real(x), assumptions) === true) return x;
  if (ask(Q.imaginary(x), assumptions) === true) return S.Zero;
  return refine(e, assumptions);
}

/** SymPy refine_im: imaginary part under assumptions. */
export function refineIm(expr: ExprLike, assumptions: Assumption = true): Expr {
  const e = sympify(expr);
  const x = at(e.args, 0);
  if (ask(Q.real(x), assumptions) === true) return S.Zero;
  if (ask(Q.imaginary(x), assumptions) === true) return mul(-1, S.I, x);
  return refine(e, assumptions);
}

/** SymPy refine_sign: sign on the real and imaginary axes. */
export function refineSign(expr: ExprLike, assumptions: Assumption = true): Expr {
  const e = sympify(expr);
  const x = at(e.args, 0);
  if (ask(Q.zero(x), assumptions) === true) return S.Zero;
  if (ask(Q.positive(x), assumptions) === true) return S.One;
  if (ask(Q.negative(x), assumptions) === true) return S.NegOne;
  // A real nonzero -I*x also proves x lies on the imaginary axis.
  const imaginaryPart = ask(Q.imaginary(x), assumptions) === true ? im(x) : mul(-1, S.I, x);
  if (ask(Q.positive(imaginaryPart), assumptions) === true) return S.I;
  if (ask(Q.negative(imaginaryPart), assumptions) === true) return mul(-1, S.I);
  return e;
}

/** SymPy refine_matrixelement: use the upper triangle of a symmetric matrix. */
export function refineMatrixelement(expr: ExprLike, assumptions: Assumption = true): Expr | NoMatchResult {
  const e = sympify(expr);
  if (!(e instanceof ExtensionExpr) || e.name !== 'MatrixElement') return NoMatch;
  const matrix = at(e.args, 0), i = at(e.args, 1), j = at(e.args, 2);
  if (ask(Q.symmetric(matrix), assumptions) !== true) return NoMatch;
  return couldExtractMinusSign(add(i, mul(-1, j))) ? e : e.withArgs([matrix, j, i]);
}
