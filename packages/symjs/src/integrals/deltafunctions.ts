// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/deltafunctions.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Indefinite integration of expressions containing DiracDelta
 * (SymPy deltaintegrate).
 */

import type { Expr, Sym } from '../core/nodes';
import { Add, Integral, Mul, Pow, S, impl } from '../core/nodes';
import { isZero } from '../core/assumptions';
import { add, mul, neg, pow, sub } from '../core/ops';
import { at, defined } from '../core/guard';
import { ordered } from '../core/match';
import { asIndependent } from '../core/methods';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { expand } from '../simplify/expand';
import { polyCoefficients } from '../polys/poly';
import { DiracDelta, Heaviside, isDiracDelta, isSimple } from './transforms/delta';

const hasDelta = (e: Expr): boolean => isDiracDelta(e) || e.args.some(hasDelta);
const hasIntegral = (e: Expr): boolean => e instanceof Integral || e.args.some(hasIntegral);
const expandDelta = (e: Expr, x: Sym): Expr => expand(e, { diracdelta: true, wrt: x });
const isDeltaPow = (e: Expr): e is Pow => e instanceof Pow && isDiracDelta(e.base);

/** The coefficient c1 and root -c0/c1 of a simple (linear) DiracDelta argument c1*x + c0. */
function linearRoot(arg: Expr, x: Sym): [Expr, Expr] {
  const c = defined(polyCoefficients(arg, x), 'linear DiracDelta argument');
  const c1 = defined(c.get(1), 'coefficient of x');
  return [c1, neg(mul(c.get(0) ?? S.Zero, pow(c1, -1)))];
}

/**
 * SymPy change_mul: splits a product into a simple DiracDelta factor and the
 * rest, or (without one) expands its DiracDelta factors.
 */
function changeMul(node: Expr, x: Sym): [Expr | undefined, Expr | undefined] {
  const sorted = ordered(node instanceof Mul ? node.args : [node]);
  let dirac: Expr | undefined;
  const rest: Expr[] = [];
  for (const a0 of sorted) {
    let a = a0;
    if (isDeltaPow(a)) {
      rest.push(pow(a.base, sub(a.exp, 1)));
      a = a.base;
    }
    if (dirac === undefined && isDiracDelta(a) && isSimple(a, x)) dirac = a;
    else rest.push(a);
  }
  if (dirac !== undefined) return [dirac, mul(...rest)];
  const expanded = sorted.map((a) => (isDiracDelta(a) ? expandDelta(a, x) : isDeltaPow(a) ? pow(expandDelta(a.base, x), a.exp) : a));
  if (expanded.every((a, i) => a.key === at(sorted, i).key)) return [undefined, undefined];
  return [undefined, expand(mul(...expanded))];
}

/**
 * Integrates term by term, taking out constant factors, by deltaintegrate where
 * it applies and by integrate otherwise (the route SymPy integrate takes).
 *
 * @internal
 */
export function integrateDeltas(e: Expr, x: Sym): Expr {
  if (e instanceof Add) {
    // like SymPy integrate, a sum with a part left unevaluated is left unevaluated as a whole
    const parts = e.args.map((t) => integrateDeltas(t, x));
    return parts.some(hasIntegral) ? impl.integrate(e, x) : add(...parts);
  }
  const [c, g] = asIndependent(e, [x]);
  const h = deltaintegrate(g, x);
  return h === undefined ? impl.integrate(e, x) : mul(c, h);
}

/**
 * SymPy deltaintegrate: the indefinite integral in x of an expression
 * containing DiracDelta, or undefined when the method does not apply.
 *
 * Deliberate difference: after repeated integration by parts SymPy returns
 * r*DiracDelta(x, m - 1) for a delta at a point p, which is wrong unless p = 0;
 * the result here is r*DiracDelta(x - p, m - 1). The integral of
 * DiracDelta(c*x + d, k) divides by the coefficient c of x, where SymPy
 * divides by the leading coefficient of the polynomial in all its symbols.
 *
 * @internal
 */
export function deltaintegrate(f: Expr, x: Sym): Expr | undefined {
  if (!hasDelta(f)) return undefined;
  if (isDiracDelta(f)) {
    const h = expandDelta(f, x);
    if (h.key !== f.key) return integrateDeltas(h, x);
    if (!isSimple(f, x)) return undefined;
    const arg = at(f.args, 0);
    if (f.args.length === 1) return Heaviside(arg);
    return mul(DiracDelta(arg, sub(at(f.args, 1), 1)), pow(linearRoot(arg, x)[0], -1));
  }
  if (!(f instanceof Mul || f instanceof Pow)) return undefined;
  const g = expand(f);
  if (g.key !== f.key) {
    const fh = integrateDeltas(g, x);
    return fh instanceof Integral ? undefined : fh;
  }
  const [dirac, rest0] = changeMul(f, x);
  if (dirac === undefined) return rest0 === undefined ? undefined : integrateDeltas(rest0, x);
  let rest = defined(rest0, 'the rest of the product');
  let delta = expandDelta(dirac, x);
  if (delta instanceof Mul) {
    // take out the factors the expansion extracted
    const [d2, rest2] = changeMul(delta, x);
    delta = defined(d2, 'simple DiracDelta factor');
    rest = mul(rest, defined(rest2, 'the extracted factors'));
  }
  const point = linearRoot(at(delta.args, 0), x)[1];
  // the largest hyperreal term left after repeated integration by parts
  let n = delta.args.length === 1 ? 0 : Number(String(at(delta.args, 1)));
  let m = 0;
  while (n >= 0) {
    const r = mul(pow(-1, n), subs(diff(rest, x, n), [[x, point]]));
    if (isZero(r) !== true) return m === 0 ? mul(r, Heaviside(sub(x, point))) : mul(r, DiracDelta(sub(x, point), m - 1));
    n -= 1;
    m += 1;
  }
  return S.Zero;
}

/**
 * deltaintegrate as integrate uses it: the integral of f, or undefined when
 * a part is left unevaluated.
 *
 * @internal
 */
export function deltaIntegral(f: Expr, x: Sym): Expr | undefined {
  const r = integrateDeltas(f, x);
  return hasIntegral(r) ? undefined : r;
}
