// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/manualintegrate.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file SymPy manualintegrate's sqrt_quadratic_rule for a polynomial times an
 * odd power of the square root of a quadratic with symbolic coefficients:
 * the recursion of SqrtQuadraticDenomRule, the logarithm of
 * ReciprocalSqrtQuadraticRule (with the perfect-square case of
 * NestedPowRule) and the degenerate cases of a vanishing leading coefficient
 * (sqrt_linear_rule).
 */

import { isReal } from '../core/assumptions';
import { at, defined, getOrThrow } from '../core/guard';
import { Ne, piecewise } from '../core/logic';
import { asIndependent } from '../core/methods';
import type { Expr, Sym } from '../core/nodes';
import { Dummy, Mul, Piecewise, Pow, Rational, S } from '../core/nodes';
import { add, mul, pow, sqrt } from '../core/ops';
import { xreplace } from '../core/traverse';
import { log } from '../functions/elementary/elementary';
import { polyCoefficients } from '../polys/poly';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';

const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;

/** The integral of a polynomial (coefficients cancelled) term by term. */
function polyIntegral(p: Expr, x: Sym): Expr {
  const pc = defined(polyCoefficients(expand(p), x), 'polynomial');
  return add(...[...pc].map(([k, c]) => mul(cancel(c), Rational.of(1, k + 1), pow(x, k + 1))));
}

/** The integral of 1/sqrt(a + b*x + c*x**2) with c != 0 (inverse_trig_rule with degenerate=False). */
function reciprocalSqrt(a: Expr, b: Expr, c: Expr, x: Sym): Expr {
  const h = mul(-1, b, pow(mul(2, c), -1));
  const k = add(a, mul(-1, pow(b, 2), pow(mul(4, c), -1)));
  const generic = mul(log(add(mul(2, sqrt(c), sqrt(add(a, mul(b, x), mul(c, pow(x, 2))))), b, mul(2, c, x))), pow(sqrt(c), -1));
  // a perfect square: (x - h)*log(x - h)/sqrt(c*(x - h)**2) (NestedPowRule)
  const xh = add(x, mul(-1, h));
  const square = mul(xh, pow(sqrt(mul(c, pow(xh, 2))), -1), log(xh));
  return piecewise([generic, Ne(k, 0)], [square, true]);
}

/** The integral of poly/sqrt(a + b*x + c*x**2) for coefficients coeffs of degree 2 or more (SqrtQuadraticDenomRule). */
function sqrtQuadraticDenom(a: Expr, b: Expr, c: Expr, coeffs0: readonly Expr[], x: Sym): Expr {
  const coeffs = [...coeffs0];
  const result: Expr[] = [];
  for (let i = 0; i < coeffs.length - 2; i++) {
    const n = coeffs.length - 1 - i;
    const coeff = mul(at(coeffs, i), pow(mul(c, n), -1));
    result.push(coeff);
    coeffs[i + 1] = add(at(coeffs, i + 1), mul(-1, 2 * n - 1, b, S.Half, coeff));
    coeffs[i + 2] = add(at(coeffs, i + 2), mul(-1, n - 1, a, coeff));
  }
  const d = at(coeffs, coeffs.length - 1);
  const e = at(coeffs, coeffs.length - 2);
  const s = sqrt(add(a, mul(b, x), mul(c, pow(x, 2))));
  const constant = add(d, mul(-1, b, e, pow(mul(2, c), -1)));
  const I0 = isZero(constant) ? S.Zero : mul(constant, reciprocalSqrt(a, b, c, x));
  return add(mul(add(...result.map((r, i) => mul(r, pow(x, coeffs.length - 2 - i))), mul(e, pow(c, -1))), s), I0);
}

/** The integral of f*sqrt(a + b*x)**n, b != 0 (sqrt_linear_rule: u = sqrt(a + b*x)), with its degenerate case b = 0. */
function sqrtLinear(f: Expr, a: Expr, b: Expr, n: number, x: Sym): Expr {
  const u = new Dummy('u');
  const sub = mul(xreplace(f, [[x, mul(add(pow(u, 2), mul(-1, a)), pow(b, -1))]]), pow(u, n + 1), 2, pow(b, -1));
  const [coeff, rest] = asIndependent(sub, [u]);
  const step = xreplace(mul(coeff, polyIntegral(rest, u)), [[u, sqrt(add(a, mul(b, x)))]]);
  return piecewise([step, Ne(b, 0)], [mul(pow(sqrt(a), n), polyIntegral(f, x)), true]);
}

/**
 * SymPy sqrt_quadratic_rule: the integral of f = p(x)*sqrt(a + b*x + c*x**2)**n
 * for a polynomial p, n = 1 or n = -1 (with p of degree 2 or more for n = -1)
 * and b != 0, when the coefficients are not known to be real (SymPy then
 * chooses asin and asinh by their signs). Undefined otherwise.
 *
 * @example
 * sqrtQuadraticRule(parse('x*sqrt(x**2 + a*x + b)'), x)
 */
export function sqrtQuadraticRule(f: Expr, x: Sym): Expr | undefined {
  const factors = f instanceof Mul ? f.args : [f];
  const root = factors.find((t) => t instanceof Pow && t.exp instanceof Rational && t.exp.q === 2n && t.base.has(x));
  if (!(root instanceof Pow) || !(root.exp instanceof Rational)) return undefined;
  const n = Number(root.exp.p);
  const pc = polyCoefficients(root.base, x);
  if (pc === undefined || Math.max(...pc.keys()) !== 2 || Math.abs(n) !== 1) return undefined;
  const [a, b, c] = [pc.get(0) ?? S.Zero, pc.get(1) ?? S.Zero, getOrThrow(pc, 2)];
  const p = mul(...factors.filter((t) => t !== root));
  const k = add(a, mul(-1, pow(b, 2), pow(mul(4, c), -1)));
  if (isZero(b) || polyCoefficients(p, x) === undefined || (isReal(k) === true && isReal(c) === true)) return undefined;
  const numer = defined(polyCoefficients(expand(mul(p, pow(root.base, (n + 1) / 2))), x), 'polynomial');
  const deg = Math.max(...numer.keys());
  if (deg < 2) return undefined;
  const coeffs = Array.from({ length: deg + 1 }, (_, i) => numer.get(deg - i) ?? S.Zero);
  const generic = sqrtQuadraticDenom(a, b, c, coeffs, x);
  const linear = sqrtLinear(p, a, b, n, x);
  return piecewise([generic, Ne(c, 0)], ...(linear instanceof Piecewise ? linear.pairs : [[linear, S.true] as const]));
}
