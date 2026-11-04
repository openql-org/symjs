// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Simplification of Bessel functions (port of SymPy besselsimp):
 * polar factors of the argument, half-integer orders in terms of
 * elementary functions and integer orders reduced to orders 0 and 1.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Fn, Mul, Rational, S } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { mapBottomUp, xreplace } from '../core/traverse';
import { cos, cosh, fn, sin, sinh } from '../functions/elementary/elementary';
import { Poly, factor } from '../polys/sympoly';
import { expandMul as expand } from './expand';
import { fraction, together } from './rational';
import { factorTerms } from './exprtools';
import { first, pair } from '../core/guard';

type BName = 'besselj' | 'bessely' | 'besseli' | 'besselk';
const BESSEL: ReadonlySet<string> = new Set<BName>(['besselj', 'bessely', 'besseli', 'besselk']);
const isBName = (name: string): name is BName => BESSEL.has(name);
const isBessel = (e: Expr): e is Fn => e instanceof Fn && isBName(e.name);

/**
 * z = rest * exp_polar(I*pi*k): [rest, k] (polar_lift(-1), polar_lift(I) and
 * polar_lift(-I) evaluate to exp_polar(I*pi), exp_polar(I*pi/2) and exp_polar(-I*pi/2)).
 */
function polarFactor(z: Expr): [Expr, Rational] | undefined {
  const fs = z instanceof Mul ? z.args : [z];
  for (const f of fs) {
    if (!(f instanceof Fn && f.name === 'exp_polar')) continue;
    const k = mul(first(f.args), pow(mul(S.I, S.Pi), -1));
    if (k instanceof Rational) return [mul(...fs.filter((g) => g !== f)), k];
  }
  return undefined;
}

function polarRule(e: Fn): Expr | undefined {
  if (e.name !== 'besselj' && e.name !== 'besseli') return undefined;
  const [nu, z] = pair(e.args);
  const pf = polarFactor(z);
  if (!pf) return undefined;
  const [rest, k] = pf;
  const phase = exp(mul(S.I, S.Pi, nu, k));
  if (k.isOne) return mul(phase, fn(e.name, [nu, rest]));
  if (k.q === 2n && (k.p === 1n || k.p === -1n)) return mul(phase, fn(e.name === 'besselj' ? 'besseli' : 'besselj', [nu, rest]));
  return undefined;
}

/** Half-integer orders through the spherical forms and the recurrence. */
function halfInteger(name: BName, nu: Rational, z: Expr): Expr {
  // sqrt(2/(pi*z)) written like SymPy: sqrt(2)/(sqrt(pi)*sqrt(z))
  const s = mul(sqrt(2), pow(sqrt(S.Pi), -1), pow(z, S.NegHalf));
  const base: Record<BName, [Expr, Expr]> = {
    // [order -1/2, order 1/2]
    besselj: [mul(s, cos(z)), mul(s, sin(z))],
    bessely: [mul(s, sin(z)), mul(-1, s, cos(z))],
    besseli: [mul(s, cosh(z)), mul(s, sinh(z))],
    besselk: [mul(sqrt(2), sqrt(S.Pi), S.Half, pow(z, S.NegHalf), exp(mul(-1, z))), mul(sqrt(2), sqrt(S.Pi), S.Half, pow(z, S.NegHalf), exp(mul(-1, z)))],
  };
  const [m1, p1] = base[name];
  // nu = m + 1/2
  const m = Number((nu.p - 1n) / 2n);
  if (m >= 0) {
    let lo = m1;
    let hi = p1;
    for (let k = 0; k < m; k++) {
      const next = step(name, Rational.of(2 * k + 1, 2), z, hi, lo);
      lo = hi;
      hi = next;
    }
    return hi;
  }
  let cur = m1; // order -1/2
  let up = p1; // order 1/2
  for (let o = -1; o > m; o--) {
    // order of cur is o + 1/2; compute order o - 1/2
    const prev = backStep(name, Rational.of(2 * o + 1, 2), z, cur, up);
    up = cur;
    cur = prev;
  }
  return cur;
}

/** B_{nu+1} from B_nu (hi) and B_{nu-1} (lo). */
function step(name: BName, nu: Rational, z: Expr, hi: Expr, lo: Expr): Expr {
  const c = mul(2, nu, pow(z, -1));
  switch (name) {
    case 'besselj':
    case 'bessely':
      return add(mul(c, hi), mul(-1, lo));
    case 'besseli':
      return add(mul(-1, c, hi), lo);
    case 'besselk':
      return add(mul(c, hi), lo);
  }
}

/** B_{nu-1} from B_nu and B_{nu+1} (nu given as the order of cur). */
function backStep(name: BName, nuCur: Rational, z: Expr, cur: Expr, up: Expr): Expr {
  const c = mul(2, nuCur, pow(z, -1));
  switch (name) {
    case 'besselj':
    case 'bessely':
      return add(mul(c, cur), mul(-1, up));
    case 'besseli':
      return add(mul(c, cur), up);
    case 'besselk':
      return add(mul(-1, c, cur), up);
  }
}

/** expand_func for integer orders > 1: down to orders 0 and 1. */
function integerReduce(name: BName, n: number, z: Expr): Expr {
  const b = (k: number) => fn(name, [k, z]);
  let lo: Expr = b(0);
  let hi: Expr = b(1);
  for (let k = 1; k < n; k++) {
    const next = step(name, Rational.of(k), z, hi, lo);
    lo = hi;
    hi = next;
  }
  return hi;
}

/** SymPy besselsimp. */
export function besselsimp(ex: ExprLike): Expr {
  const orig = sympify(ex);
  let e = mapBottomUp(orig, (t) => (isBessel(t) ? (polarRule(t) ?? t) : t));
  e = mapBottomUp(e, (t) => {
    if (!(t instanceof Fn) || !isBName(t.name)) return t;
    const [nu, z] = pair(t.args);
    if (nu instanceof Rational && nu.q === 2n) return halfInteger(t.name, nu, z);
    if (nu instanceof Rational && nu.isInteger && nu.p > 1n) return integerReduce(t.name, Number(nu.p), z);
    return t;
  });
  if (e.key !== orig.key) {
    try {
      e = factor(together(expand(e)));
      // pull out common factors, and the sign of a sum whose leading coefficient (in SymPy's
      // generator order) is negative, from the numerator (SymPy factor)
      const [n, d] = fraction(e);
      let num = factorTerms(n);
      const inner = num instanceof Mul ? num.args.find((a) => a instanceof Add) : num;
      // (the sign goes into one product with the denominator: -1 times a lone sum would be distributed)
      const pull = inner instanceof Add && couldExtractMinusSign(Poly.from(inner).LC());
      if (pull) num = xreplace(num, [[inner, mul(-1, inner)]]);
      e = mul(pull ? -1 : 1, num, pow(d, -1));
    } catch {
      // keep e
    }
  }
  return e;
}
