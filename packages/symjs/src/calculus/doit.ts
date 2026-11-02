// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Evaluation of unevaluated objects (SymPy doit): integrals, limits,
 * sums/products and derivatives, innermost first.
 */

import { Derivative, Expr, ExprLike, ExtensionExpr, Integral, Limit, Sym } from '../core/nodes';
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
      const [f, v, a, b] = y.args;
      // (x, b): the antiderivative at b
      if (a && !b) return xreplace(integrate(f!, v as Sym), [[v!, a]]);
      return a && b ? integrate(f!, v as Sym, [a, b]) : integrate(f!, v as Sym);
    }
    if (y instanceof Limit) return limit(y.args[0]!, y.args[1] as Sym, y.args[2]!, y.dir);
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
