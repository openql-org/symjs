// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/singularityfunctions.py), BSD
// 3-Clause License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Indefinite integration of singularity functions (SymPy
 * singularityintegrate).
 */

import type { ExprLike, Sym } from '../core/nodes';
import { Expr, Integral, Mul, Pow, Rational } from '../core/nodes';
import { some } from '../core/traverse';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { isPositive, isZero } from '../core/assumptions';
import { add, mul, pow, sympify } from '../core/ops';
import { at } from '../core/guard';
import { rewrite } from '../simplify/rewrite';
import { integrateDeltas } from './deltafunctions';
import { SingularityFunction, isSingularityFunction } from './transforms/delta';

const hasSingularity = (e: Expr): boolean => isSingularityFunction(e) || e.args.some(hasSingularity);

/**
 * SymPy singularityintegrate: the indefinite integral in x of a singularity
 * function, or of a product or power containing one, as singularity
 * functions; NoMatch (SymPy None) when the method does not apply.
 *
 * @example
 * singularityintegrate(SingularityFunction(x, a, 3), x)  // SingularityFunction(x, a, 4)/4
 */
export function singularityintegrate(f: ExprLike, x: Sym): Expr | NoMatchResult {
  const e = sympify(f);
  if (!hasSingularity(e)) return NoMatch;
  if (isSingularityFunction(e)) {
    const [v, a, n] = [at(e.args, 0), at(e.args, 1), at(e.args, 2)];
    if (isPositive(n) === true || isZero(n) === true) return mul(SingularityFunction(v, a, add(n, 1)), pow(add(n, 1), -1));
    if (n instanceof Rational && ['-1', '-2', '-3', '-4'].includes(String(n))) return SingularityFunction(v, a, add(n, 1));
  }
  if (e instanceof Mul || e instanceof Pow) return rewrite(integrateDeltas(rewrite(e, 'DiracDelta'), x), 'SingularityFunction');
  return NoMatch;
}

/**
 * singularityintegrate as integrate uses it: the integral of f, or undefined
 * when the method does not apply or leaves a part unevaluated.
 *
 * @internal
 */
export function singularityIntegral(f: Expr, x: Sym): Expr | undefined {
  // SymPy integrates SingularityFunction(g(x), a, n) as if g(x) were x: wrong unless g(x) = x
  if (some(f, (e) => isSingularityFunction(e) && at(e.args, 0).key !== x.key)) return undefined;
  const r = singularityintegrate(f, x);
  return r instanceof Expr && !some(r, (e) => e instanceof Integral) ? r : undefined;
}
