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
import { cos, cosh, fn, sin, sinh } from '../functions/elementary';
import { factor } from '../polys/sympoly';
import { expandMul as expand } from './expand';
import { fraction, together } from './rational';
import { factorTerms } from './exprtools';

type BName = 'besselj' | 'bessely' | 'besseli' | 'besselk';
const BESSEL = new Set(['besselj', 'bessely', 'besseli', 'besselk']);
const isBessel = (e: Expr): e is Fn => e instanceof Fn && BESSEL.has(e.name);

/** z = rest * exp_polar(I*pi*k) (or polar_lift(-1), ...): [rest, k] with k in {1, 1/2, -1/2}. */
function polarFactor(z: Expr): [Expr, Rational] | undefined {
  const fs = z instanceof Mul ? z.args : [z];
  for (const f of fs) {
    if (!(f instanceof Fn)) continue;
    let k: Rational | undefined;
    if (f.name === 'exp_polar') {
      const q = mul(f.args[0]!, pow(mul(S.I, S.Pi), -1));
      if (q instanceof Rational) k = q;
    } else if (f.name === 'polar_lift') {
      const a = f.args[0]!;
      if (a instanceof Rational && a.p === -1n && a.q === 1n) k = S.One;
      else if (a.key === S.I.key) k = S.Half;
      else if (a.key === mul(-1, S.I).key) k = S.NegHalf;
    }
    if (k) return [mul(...fs.filter((g) => g !== f)), k];
  }
  return undefined;
}

function polarRule(e: Fn): Expr | undefined {
  if (e.name !== 'besselj' && e.name !== 'besseli') return undefined;
  const [nu, z] = e.args as [Expr, Expr];
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
    if (!isBessel(t)) return t;
    const [nu, z] = t.args as [Expr, Expr];
    if (nu instanceof Rational && nu.q === 2n) return halfInteger(t.name as BName, nu, z);
    if (nu instanceof Rational && nu.isInteger && nu.p > 1n) return integerReduce(t.name as BName, Number(nu.p), z);
    return t;
  });
  if (e.key !== orig.key) {
    try {
      e = factor(together(expand(e)));
      // pull out common factors and a leading minus sign of the numerator (SymPy factor)
      const [n, d] = fraction(e);
      let num = factorTerms(n);
      const inner = num instanceof Mul ? num.args.find((a) => a instanceof Add) : num instanceof Add ? num : undefined;
      const negs = inner instanceof Add ? inner.args.filter((a) => couldExtractMinusSign(a)).length : 0;
      const pull = inner instanceof Add && (2 * negs > inner.args.length || (2 * negs === inner.args.length && couldExtractMinusSign(inner)));
      if (inner && pull) num = mul(-1, xreplace(num, [[inner, mul(-1, inner)]]));
      e = mul(num, pow(d, -1));
    } catch {
      // keep e
    }
  }
  return e;
}
