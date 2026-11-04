// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/error_prop.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.error_prop: propagation of the variances of
 * independent (or, with covariances, correlated) variables through sums,
 * products, powers and exponentials, to first order.
 */

import { Add, Mul, Pow, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { at, first } from '../core/guard';
import { asOrderedFactors } from '../printing/sortkey';
import { simplify } from '../simplify/simplify';
import { RandomSymbol, isRandom } from './rv';
import { VarianceNode } from './symbolicprobability';
import { Covariance } from './symbolicprobability';

/** Options of variancePropagation. */
export interface VariancePropOptions {
  /** Symbols that are constants (their variance is 0). */
  readonly consts?: readonly Expr[];
  /** Include the covariance terms (SymPy include_covar). */
  readonly includeCovar?: boolean;
}

/** The argument of a Variance, or the value itself (SymPy _arg0_or_var; the first factor of a product in SymPy's order). */
const arg0OrVar = (v: Expr): Expr => (v instanceof Mul ? first(asOrderedFactors(v)) : v.args.length > 0 ? at(v.args, 0) : v);

/** An exponential exp(x) (SymPy isinstance(expr, exp)). */
const isExp = (e: Expr): e is Pow => e instanceof Pow && e.base === S.E;

/**
 * The variance of an expression of independent variables, to first order
 * (SymPy variance_prop). Symbols that are not random variables are given
 * a Variance of their own.
 */
export function varianceProp(exprIn: ExprLike, opts: VariancePropOptions = {}): Expr {
  const expr = sympify(exprIn);
  const consts = opts.consts ?? [];
  const includeCovar = opts.includeCovar ?? false;
  const args = expr.args;
  if (args.length === 0) {
    if (consts.some((c) => c.key === expr.key)) return S.Zero;
    if (isRandom(expr)) return new VarianceNode([expr]).doit();
    if (expr instanceof Sym) return new VarianceNode([new RandomSymbol(expr)]).doit();
    return S.Zero;
  }
  const varArgs = args.map((a) => varianceProp(a, opts));
  let varExpr: Expr;
  if (expr instanceof Add) {
    varExpr = add(...varArgs);
    if (includeCovar) {
      const terms: Expr[] = [];
      for (let i = 0; i < varArgs.length; i++) {
        for (let j = i + 1; j < varArgs.length; j++) terms.push(mul(2, Covariance(arg0OrVar(at(varArgs, i)), arg0OrVar(at(varArgs, j))).expand()));
      }
      varExpr = add(varExpr, ...terms);
    }
  } else if (expr instanceof Mul) {
    const terms = args.map((a, i) => mul(at(varArgs, i), pow(a, -2)));
    varExpr = simplify(mul(pow(expr, 2), add(...terms)));
    if (includeCovar) {
      const extra: Expr[] = [];
      for (let i = 0; i < args.length; i++) {
        for (let j = i + 1; j < args.length; j++) {
          const c = Covariance(arg0OrVar(at(varArgs, i)), arg0OrVar(at(varArgs, j))).expand();
          extra.push(mul(2, c, pow(mul(at(args, i), at(args, j)), -1)));
        }
      }
      varExpr = add(varExpr, ...extra);
    }
  } else if (isExp(expr)) {
    varExpr = simplify(mul(at(varArgs, 1), pow(expr, 2)));
  } else if (expr instanceof Pow) {
    const b = at(args, 1);
    const v = mul(at(varArgs, 0), pow(mul(expr, b, pow(at(args, 0), -1)), 2));
    varExpr = simplify(v);
  } else {
    varExpr = new VarianceNode([expr]);
  }
  return varExpr;
}
