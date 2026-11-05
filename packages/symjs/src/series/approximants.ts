// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Consecutive Pade approximants of a series (SymPy
 * sympy.series.approximants).
 *
 * Ported from SymPy 1.14 (sympy/series/approximants.py, BSD-3-Clause,
 * Copyright (c) SymPy Development Team).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { S, Sym, impl } from '../core/nodes';
import { add, div, mul, pow, sub, sympify } from '../core/ops';
import { isZero } from '../core/assumptions';
import { at } from '../core/guard';
import { polyLcm } from '../polys/sympoly';
import { denom } from '../simplify/rational';
import { expand } from '../simplify/expand';

const isZeroValue = (e: Expr): boolean => isZero(e) === true;

/** SymPy lcm of two expressions, which is 0 when one of them is 0 (a denominator that cancels to 0). */
const lcm0 = (a: Expr, b: Expr): Expr => (isZeroValue(a) || isZeroValue(expand(b)) ? S.Zero : polyLcm(a, b));

const defaultX: Sym = /* @__PURE__ */ new Sym('x');

/** Options of approximants. */
export interface ApproximantsOptions {
  /** true: simplify every approximant (slower, useful when symbols are involved). */
  simplify?: boolean;
}

/** Removes the trailing zeros of a coefficient list. */
function trimZeros(p: Expr[]): void {
  while (isZeroValue(at(p, p.length - 1))) p.pop();
}

/**
 * The consecutive Pade approximants of the series with coefficients l, as
 * rational functions of X (SymPy approximants). The last one is the
 * rational generating function of the sequence, if it has one. The
 * coefficients may be symbolic.
 *
 * Example: for lucas(0..15) the approximants are 2, -4/(x - 2),
 * (5*x - 2)/(3*x - 1), (x - 2)/(x**2 + x - 1).
 */
export function* approximants(lIn: readonly ExprLike[], X: Expr = defaultX, opts: ApproximantsOptions = {}): Generator<Expr, void, undefined> {
  let l = lIn.map(sympify);
  let [p1, q1]: [Expr[], Expr[]] = [[S.One], [S.Zero]];
  let [p2, q2]: [Expr[], Expr[]] = [[S.Zero], [S.One]];
  while (l.length) {
    let b = 0;
    while (isZeroValue(at(l, b))) {
      b++;
      if (b === l.length) return;
    }
    const lb = at(l, b);
    const m: Expr[] = [div(S.One, lb)];
    for (let k = b + 1; k < l.length; k++) {
      // SymPy indexes m[b - j - 1] from the end of m
      let s: Expr = S.Zero;
      for (let j = b; j < k; j++) s = sub(s, mul(at(l, j + 1), at(m, k - j - 1)));
      m.push(div(s, lb));
    }
    l = m;
    const a = at(l, 0);
    l[0] = S.Zero;
    const p: Expr[] = Array.from({ length: Math.max(p2.length, b + p1.length) }, () => S.Zero);
    const q: Expr[] = Array.from({ length: Math.max(q2.length, b + q1.length) }, () => S.Zero);
    p2.forEach((e, k) => (p[k] = mul(a, e)));
    p1.forEach((e, k) => (p[k + b] = add(at(p, k + b), e)));
    q2.forEach((e, k) => (q[k] = mul(a, e)));
    q1.forEach((e, k) => (q[k + b] = add(at(q, k + b), e)));
    trimZeros(p);
    trimZeros(q);
    [p1, p2] = [p2, p];
    [q1, q2] = [q2, q];

    let c: Expr = S.One;
    for (const x of [...p, ...q]) c = lcm0(c, denom(x));
    const out = div(add(...p.map((e, k) => mul(c, e, pow(X, k)))), add(...q.map((e, k) => mul(c, e, pow(X, k)))));
    yield opts.simplify === true ? impl.simplify(out) : out;
  }
}
