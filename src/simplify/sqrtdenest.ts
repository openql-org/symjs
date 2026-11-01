// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file sqrtdenest: denest square roots of the form sqrt(a + b*sqrt(c))
 * (the basic case of SymPy simplify.sqrtdenest).
 */

import { Add, Expr, ExprLike, Mul, Pow, Rational, S } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { rebuild } from '../core/traverse';

const isHalf = (e: Expr) => e instanceof Rational && e.p === 1n && e.q === 2n;

/** a + b*sqrt(c) with rational a, b, c, or undefined. */
function splitSurd(e: Expr): [Rational, Rational, Rational] | undefined {
  if (!(e instanceof Add) || e.args.length !== 2) return undefined;
  const [a, t] = e.args as [Expr, Expr];
  if (!(a instanceof Rational)) return undefined;
  let b: Rational = S.One as Rational;
  let s: Expr = t;
  if (t instanceof Mul && t.args.length === 2 && t.args[0] instanceof Rational) {
    b = t.args[0];
    s = t.args[1]!;
  }
  if (!(s instanceof Pow && isHalf(s.exp) && s.base instanceof Rational)) return undefined;
  return [a, b, s.base];
}

function denestOne(e: Expr): Expr | undefined {
  if (!(e instanceof Pow && isHalf(e.exp))) return undefined;
  const parts = splitSurd(e.base);
  if (!parts) return undefined;
  const [a, b, c] = parts;
  const d2 = add(pow(a, 2), mul(-1, pow(b, 2), c));
  if (!(d2 instanceof Rational) || d2.isNegative) return undefined;
  const d = sqrt(d2);
  if (!(d instanceof Rational)) return undefined;
  const p = sqrt(mul(add(a, d), Rational.of(1n, 2n)));
  const q = sqrt(mul(add(a, mul(-1, d)), Rational.of(1n, 2n)));
  return add(p, mul(b.isNegative ? -1 : 1, q));
}

/** Denest square roots (bottom-up). */
export function sqrtdenest(exIn: ExprLike): Expr {
  const go = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const args = e.args.map(go);
    const y = args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
    return denestOne(y) ?? y;
  };
  return go(sympify(exIn));
}
