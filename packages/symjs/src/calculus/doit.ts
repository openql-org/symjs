// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Evaluation of unevaluated objects (SymPy doit): integrals, limits,
 * sums/products and derivatives, innermost first.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Derivative, ExtensionExpr, Integral, Limit, Sym } from '../core/nodes';
import { at, cast } from '../core/guard';
import { sympify } from '../core/ops';
import { rebuild, xreplace } from '../core/traverse';
import { Concrete, doitConcrete } from '../concrete/summations';
import { integrate } from '../integrals/integrate';
import { limit } from '../series/limits';
import { diff } from './diff';

/** Evaluate all unevaluated Integral, Limit, Sum, Product and Derivative objects. */
export function doit(ex: ExprLike): Expr {
  const go = (x: Expr): Expr => {
    const y = x.args.length ? rebuild(x, x.args.map(go)) : x;
    if (y instanceof Integral) {
      const [, , a, b] = y.args;
      const f = y.integrand;
      const v = cast(y.variable, Sym, 'integration variable');
      // (x, b): the antiderivative at b
      if (a && !b) return xreplace(integrate(f, v), [[v, a]]);
      return a && b ? integrate(f, v, [a, b]) : integrate(f, v);
    }
    if (y instanceof Limit) return limit(at(y.args, 0), cast(y.args[1], Sym, 'limit variable'), at(y.args, 2), y.dir);
    if (y instanceof Concrete) return doitConcrete(y);
    if (y instanceof ExtensionExpr) return y.doitSelf() ?? y;
    if (y instanceof Derivative) {
      let r = y.expr;
      for (const [v, n] of y.variableCount) r = diff(r, v, n);
      return r;
    }
    return y;
  };
  return go(sympify(ex));
}
