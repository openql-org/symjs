// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/functions/special/tensor_functions.py),
// BSD 3-Clause License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file The Levi-Civita symbol (SymPy LeviCivita and Eijk). KroneckerDelta is
 * in functions/special/hyper.ts.
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { Rational, S } from '../../core/nodes';
import { defineFunction } from '../../core/defun';
import { at } from '../../core/guard';

/** SymPy eval_levicivita: prod_{i<j} (a_j - a_i) / prod_i i!, for integer arguments. */
function evalLeviCivita(args: readonly bigint[]): Expr {
  let num = 1n;
  let den = 1n;
  let fact = 1n;
  for (let i = 0; i < args.length; i++) {
    if (i > 0) fact *= BigInt(i);
    den *= fact;
    for (let j = i + 1; j < args.length; j++) num *= at(args, j) - at(args, i);
  }
  return Rational.of(num, den);
}

const leviCivitaDef = defineFunction('LeviCivita', {
  eval: (...args: Expr[]) => {
    const ints = args.flatMap((a) => (a instanceof Rational && a.isInteger ? [a.p] : []));
    if (ints.length === args.length) return evalLeviCivita(ints);
    // a repeated index
    if (new Set(args.map((a) => a.key)).size < args.length) return S.Zero;
    return undefined;
  },
  latex: (args) => `\\varepsilon_{${args.join(' ')}}`,
});

/**
 * The Levi-Civita symbol (SymPy LeviCivita): the sign of the permutation of
 * integer arguments, 0 for a repeated index, unevaluated otherwise.
 */
export function LeviCivita(...args: ExprLike[]): Expr {
  return leviCivitaDef(...args);
}

/** SymPy Eijk: the Levi-Civita symbol, LeviCivita(*args). */
export function Eijk(...args: ExprLike[]): Expr {
  return LeviCivita(...args);
}
