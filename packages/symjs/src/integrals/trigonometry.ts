// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (sympy/integrals/trigonometry.py), BSD 3-Clause
// License, Copyright (c) 2006-2023 SymPy Development Team.

/**
 * @file Integration of sin(a*x)**n*cos(a*x)**m for integers n and m (SymPy
 * trigintegrate).
 */

import { Ne, piecewise } from '../core/logic';
import type { Expr, Sym } from '../core/nodes';
import { Dummy, Fn, Mul, Pow, Rational, S, impl } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { xreplace } from '../core/traverse';
import { at, defined } from '../core/guard';
import { cos, sin } from '../functions/elementary/elementary';
import { polyCoefficients } from '../polys/poly';

/** [a, n, m] with f = sin(a*x)**n*cos(a*x)**m, a free of x and n, m integers; undefined otherwise. */
function matchSinCos(f: Expr, x: Sym): [Expr, number, number] | undefined {
  let a: Expr | undefined;
  let n = 0;
  let m = 0;
  for (const t of f instanceof Mul ? f.args : [f]) {
    const [base, k] = t instanceof Pow && t.exp instanceof Rational && t.exp.isInteger ? [t.base, Number(t.exp.p)] : [t, 1];
    if (!(base instanceof Fn && (base.name === 'sin' || base.name === 'cos'))) return undefined;
    const pc = polyCoefficients(at(base.args, 0), x);
    const c = pc?.get(1);
    if (pc === undefined || c === undefined || pc.size !== 1) return undefined;
    if (a !== undefined && a.key !== c.key) return undefined;
    a = c;
    if (base.name === 'sin') n += k;
    else m += k;
  }
  // (a product has factors)
  return [defined(a, 'argument'), n, m];
}

const u = new Dummy('u');

/** The binomial coefficient C(n, k) for small integers. */
const binom = (n: number, k: number): Rational => {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return Rational.of(r);
};

/**
 * The integral of sin(a*x)**n*cos(a*x)**m in x for integers n and m (SymPy
 * trigintegrate), as Piecewise((F/a, Ne(a, 0)), (x or 0, True)); undefined
 * when f has another form.
 *
 * @example
 * trigintegrate(parse('1/sin(x)'), x)  // log(cos(x) - 1)/2 - log(cos(x) + 1)/2
 */
export function trigintegrate(f: Expr, x: Sym): Expr | undefined {
  const match = matchSinCos(f, x);
  if (match === undefined) return undefined;
  const [a, n, m] = match;
  const zz = n === 0 ? x : S.Zero;
  const odd = (k: number) => k % 2 !== 0;
  let res: Expr;
  if (odd(n) || odd(m)) {
    let nOdd = odd(n);
    if (nOdd && odd(m)) {
      // both odd: substitute the function of the smaller power
      if (n < 0 && m > 0) nOdd = false;
      else if (m < 0 && n > 0) nOdd = true;
      else if (n < 0 && m < 0) nOdd = n > m;
      else nOdd = n < m;
    }
    const [ff, uu] = nOdd
      ? [mul(-1, pow(add(1, mul(-1, pow(u, 2))), (n - 1) / 2), pow(u, m)), cos(mul(a, x))]
      : [mul(pow(u, n), pow(add(1, mul(-1, pow(u, 2))), (m - 1) / 2)), sin(mul(a, x))];
    const fx = xreplace(impl.integrate(ff, u), [[u, uu]]);
    return piecewise([mul(fx, pow(a, -1)), Ne(a, 0)], [zz, true]);
  }
  // n and m even
  if (Math.abs(n) > Math.abs(m)) {
    if (m > 0) res = add(...Array.from({ length: m / 2 + 1 }, (_, i) => mul((-1) ** i, binom(m / 2, i), sinPowIntegrate(n + 2 * i, x))));
    else if (m === 0) res = sinPowIntegrate(n, x);
    else res = add(mul(Rational.of(-1, m + 1), pow(cos(x), m + 1), pow(sin(x), n - 1)), mul(Rational.of(n - 1, m + 1), requireTrig(mul(pow(cos(x), m + 2), pow(sin(x), n - 2)), x)));
  } else if (Math.abs(m) > Math.abs(n)) {
    if (n > 0) res = add(...Array.from({ length: n / 2 + 1 }, (_, i) => mul((-1) ** i, binom(n / 2, i), cosPowIntegrate(m + 2 * i, x))));
    else if (n === 0) res = cosPowIntegrate(m, x);
    else res = add(mul(Rational.of(1, n + 1), pow(cos(x), m - 1), pow(sin(x), n + 1)), mul(Rational.of(m - 1, n + 1), requireTrig(mul(pow(cos(x), m - 2), pow(sin(x), n + 2)), x)));
  } else if (m === n) {
    res = impl.integrate(pow(mul(sin(mul(2, x)), S.Half), m), x);
  } else if (n < 0) {
    // m == -n
    res = add(mul(Rational.of(1, n + 1), pow(cos(x), m - 1), pow(sin(x), n + 1)), mul(Rational.of(m - 1, n + 1), impl.integrate(mul(pow(cos(x), m - 2), pow(sin(x), n + 2)), x)));
  } else {
    res = add(mul(Rational.of(-1, m + 1), pow(cos(x), m + 1), pow(sin(x), n - 1)), mul(Rational.of(n - 1, m + 1), impl.integrate(mul(pow(cos(x), m + 2), pow(sin(x), n - 2)), x)));
  }
  return piecewise([mul(xreplace(res, [[x, mul(a, x)]]), pow(a, -1)), Ne(a, 0)], [zz, true]);
}

/** trigintegrate of an expression of the matched form (the recursion of the reduction formulas). */
function requireTrig(f: Expr, x: Sym): Expr {
  return defined(trigintegrate(f, x), 'integral of sin**n*cos**m');
}

/** The integral of sin(x)**n for an even n (the reduction formulas of SymPy _sin_pow_integrate). */
function sinPowIntegrate(n: number, x: Sym): Expr {
  if (n > 0) {
    return add(mul(Rational.of(-1, n), cos(x), pow(sin(x), n - 1)), mul(Rational.of(n - 1, n), sinPowIntegrate(n - 2, x)));
  }
  if (n < 0) {
    return add(mul(Rational.of(1, n + 1), cos(x), pow(sin(x), n + 1)), mul(Rational.of(n + 2, n + 1), sinPowIntegrate(n + 2, x)));
  }
  return x;
}

/** The integral of cos(x)**n for an even n (SymPy _cos_pow_integrate). */
function cosPowIntegrate(n: number, x: Sym): Expr {
  if (n > 0) {
    return add(mul(Rational.of(1, n), sin(x), pow(cos(x), n - 1)), mul(Rational.of(n - 1, n), cosPowIntegrate(n - 2, x)));
  }
  if (n < 0) {
    return add(mul(Rational.of(-1, n + 1), sin(x), pow(cos(x), n + 1)), mul(Rational.of(n + 2, n + 1), cosPowIntegrate(n + 2, x)));
  }
  return x;
}
