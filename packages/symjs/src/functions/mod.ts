// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy Mod(p, q): the remainder p - q*floor(p/q), with the sign of
 * q. Numbers are evaluated; Mod(p, p), Mod(n, 1) for an integer n and
 * Mod(0, q) are 0; anything else stays unevaluated.
 */

import type { Expr } from '../core/nodes';
import { Float, Rational, S } from '../core/nodes';
import { add } from '../core/ops';
import { isIntegerQ } from '../core/assumptions';
import { defineFunction } from '../core/defun';
import type { DefinedFunction } from '../core/defun';
import { ratMod } from '../core/num';

function evalMod(p: Expr, q: Expr): Expr | undefined {
  if (q instanceof Rational && q.isZero) throw new RangeError('Modulo by zero');
  if (p instanceof Rational && q instanceof Rational) return ratMod(p, q);
  if ((p instanceof Float || p instanceof Rational) && (q instanceof Float || q instanceof Rational)) {
    const a = p.toNumber();
    const b = q.toNumber();
    return new Float(a - b * Math.floor(a / b));
  }
  if (p instanceof Rational && p.isZero) return S.Zero;
  if (p.key === q.key || add(p, q).key === S.Zero.key) return S.Zero;
  if (q instanceof Rational && q.equals(S.One) && isIntegerQ(p) === true) return S.Zero;
  return undefined;
}

/** SymPy Mod(p, q) (Python's p % q for expressions). */
export const Mod: DefinedFunction = /* @__PURE__ */ defineFunction('Mod', {
  nargs: 2,
  eval: (p, q) => evalMod(p, q),
  latex: ([p, q]) => `${p} \\bmod ${q}`,
});
