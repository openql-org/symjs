// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 concrete/expr_with_limits.py (BSD-3-Clause).

import { Concrete } from '../core/concrete';
import { Integral, type Expr } from '../core/nodes';
import { first } from '../core/guard';
import { sub } from '../core/ops';
import { ask, Q } from '../core/refine';
import type { Truth } from '../core/truth';
import { truthAnd, truthOr } from '../core/truth';

/** Limits in the order used by SymPy (innermost first). */
function limits(e: Concrete | Integral): (readonly Expr[])[] {
  if (e instanceof Concrete) return e.limits;
  return [...(e.integrand instanceof Integral ? limits(e.integrand) : []), e.args.slice(1)];
}

/** Variables of a sum, product or integral, including indefinite variables. */
export function variables(e: Concrete | Integral): Expr[] {
  return limits(e).flatMap((l) => l.slice(0, 1));
}

/** Whether every limit is finite, using assumptions on the bounds and variables. */
export function hasFiniteLimits(e: Concrete | Integral): Truth {
  return truthAnd(...limits(e).map((l): Truth => {
    const variableFinite = ask(Q.finite(first(l)));
    if (l.length !== 3) return variableFinite;
    const bounds = truthAnd(...l.slice(1).map((b) => ask(Q.finite(b))));
    return bounds === 'unknown' ? variableFinite : bounds;
  }));
}

/** Whether any definite limit runs from a larger lower bound to a smaller upper bound. */
export function hasReversedLimits(e: Concrete | Integral): Truth {
  return truthOr(...limits(e).map((l): Truth => {
    const a = l[1], b = l[2];
    if (a === undefined || b === undefined) return 'unknown';
    const d = sub(b, a);
    if (ask(Q.extended_negative(d)) === true) return true;
    return ask(Q.extended_nonnegative(d)) === true ? false : 'unknown';
  }));
}
