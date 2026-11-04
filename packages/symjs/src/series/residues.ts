// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/series/residues.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file The residue of an expression at a point (SymPy residue).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Order, Pow, Rational, S } from '../core/nodes';
import { NotImplementedError } from '../core/errors';
import { asCoeffMul } from '../core/methods';
import { add, mul, pow, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { collect } from '../simplify/radsimp';
import { series } from './series';

/**
 * SymPy residue(expr, x, x0): the coefficient of 1/(x - x0) in the Laurent
 * series of expr about x = x0.
 */
export function residue(ex: ExprLike, x: Sym, x0: ExprLike = 0): Expr {
  const p = sympify(x0);
  const e = p instanceof Rational && p.isZero ? sympify(ex) : subs(sympify(ex), [[x, add(x, p)]]);
  // the series up to O(1) has every negative power (SymPy tries growing orders of nseries, whose
  // order counts from the leading term, until the Order term is O(1) or smaller)
  const s = series(e, x, 0, 0);
  const terms = (s instanceof Add ? s.args : [s]).filter((t) => !(t instanceof Order));
  const c0 = collect(add(...terms), x);
  const args = c0 instanceof Add ? c0.args : [c0];
  const inv = pow(x, -1);
  let res: Expr = S.Zero;
  for (const arg of args) {
    const [c, ms] = asCoeffMul(arg, [x]);
    const m = mul(...ms);
    const ok = m.key === S.One.key || m.key === x.key || (m instanceof Pow && m.base.key === x.key && m.exp instanceof Rational && m.exp.isInteger);
    if (!ok) throw new NotImplementedError(`term of unexpected form: ${m.toString()}`);
    if (m.key === inv.key) res = add(res, c);
  }
  return res;
}
