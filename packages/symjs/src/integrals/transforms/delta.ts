// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Heaviside step function and the Dirac delta distribution
 * (SymPy sympy.functions.special.delta_functions), used by the integral
 * transforms.
 */

import type { DefinedFunction } from '../../core/defun';
import type { Expr, ExprLike } from '../../core/nodes';
import { defineFunction } from '../../core/defun';
import { S, Rational } from '../../core/nodes';
import { isNegative, isNonZero, isPositive, isZero } from '../../core/assumptions';
import { mul, neg, splitCoeff } from '../../core/ops';
import { at } from '../../core/guard';

const isMinusOne = (c: Expr): boolean => c instanceof Rational && c.p === -1n && c.q === 1n;

const heavisideDef = defineFunction('Heaviside', {
  nargs: [1, 2],
  eval: (x: Expr, h0?: Expr) => {
    const H0 = h0 ?? S.Half;
    if (x.key === S.NaN.key) return S.NaN;
    if (isNegative(x) === true) return S.Zero;
    if (isPositive(x) === true) return S.One;
    if (isZero(x) === true) return H0;
    // SymPy stores Heaviside(x) with H0 = 1/2 and prints only the argument
    if (h0 !== undefined && h0.key === S.Half.key) return heavisideDef(x);
    return undefined;
  },
  fdiff: (args) => DiracDelta(at(args, 0)),
  latex: (args) => `\\theta\\left(${at(args, 0)}\\right)`,
});

const diracDef = defineFunction('DiracDelta', {
  nargs: [1, 2],
  eval: (x: Expr, k?: Expr) => {
    const kk = k ?? S.Zero;
    if (!(kk instanceof Rational) || !kk.isInteger || kk.isNegative) {
      throw new RangeError(`the second argument of DiracDelta must be a non-negative integer, ${String(kk)} given instead`);
    }
    if (x.key === S.NaN.key) return S.NaN;
    if (isNonZero(x) === true) return S.Zero;
    const [c, rest] = splitCoeff(x);
    if (isMinusOne(c)) {
      const odd = kk.p % 2n === 1n;
      const d = kk.isZero ? diracDef(rest) : diracDef(rest, kk);
      return odd ? neg(d) : d;
    }
    // DiracDelta(x, 0) is stored as DiracDelta(x)
    if (k !== undefined && kk.isZero) return diracDef(x);
    return undefined;
  },
  fdiff: (args) => {
    const k = args[1] ?? S.Zero;
    return diracDef(at(args, 0), mul(1, k).add(1));
  },
  latex: (args) => (args.length > 1 ? `\\delta^{\\left( ${at(args, 1)} \\right)}\\left( ${at(args, 0)} \\right)` : `\\delta\\left(${at(args, 0)}\\right)`),
});

/**
 * The Heaviside step function (SymPy Heaviside): 0 for negative, 1 for
 * positive arguments and `H0` (default 1/2) at 0.
 */
export function Heaviside(x: ExprLike, H0?: ExprLike): Expr {
  return H0 === undefined ? heavisideDef(x) : heavisideDef(x, H0);
}

/** The Dirac delta distribution and its k-th derivative (SymPy DiracDelta). */
export function DiracDelta(x: ExprLike, k?: ExprLike): Expr {
  return k === undefined ? diracDef(x) : diracDef(x, k);
}

/** True when e is an application of Heaviside. */
export const isHeaviside = (e: Expr): boolean => heavisideDef.isApplied(e);

/** True when e is an application of DiracDelta. */
export const isDiracDelta = (e: Expr): boolean => diracDef.isApplied(e);

/** The underlying defined functions (for code that needs the function objects). */
export const HeavisideFunction: DefinedFunction = heavisideDef;
/** The underlying defined function of DiracDelta. */
export const DiracDeltaFunction: DefinedFunction = diracDef;
