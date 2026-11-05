// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Parts ported from SymPy (sympy/core/mod.py, Pow._eval_Mod and factorial._eval_Mod),
// Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file SymPy Mod(p, q): the remainder p - q*floor(p/q), with the sign of
 * q. Numbers are evaluated (also real constants such as pi, by the ratio
 * p/q); Mod(p, p), Mod(n, 1) for an integer n and Mod(0, q) are 0; an
 * unevaluated integer power or factorial is reduced without being computed
 * (modular exponentiation, Wilson's theorem and the prime factorization of
 * n!); anything else stays unevaluated.
 */

import type { Expr } from '../core/nodes';
import { Add, Fn, Float, Mul, Pow, Rational, S, impl } from '../core/nodes';
import { extractMultiplicatively } from '../core/methods';
import { add, mul, pow } from '../core/ops';
import { isqrt, powmod } from '../ntheory/intutil';
import { at } from '../core/guard';
import { isprime } from '../ntheory/primetest';
import { sieve } from '../ntheory/sieve';
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
  const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
  if (isInt(q)) {
    if (p instanceof Pow && isInt(p.base) && isInt(p.exp) && p.exp.p > 0n) return Rational.of(powmod(p.base.p, p.exp.p, q.p));
    if (p instanceof Fn && p.name === 'factorial' && p.args[0] instanceof Rational && p.args[0].isInteger && p.args[0].p >= 0n) return factorialMod(p.args[0].p, q.p);
  }
  // a rational ratio k = p/q: Mod(p, q) = q*Mod(k, 1) (SymPy extracts gcd(p, q))
  const k = mul(p, pow(q, -1));
  if (k instanceof Rational) return mul(q, ratMod(k, S.One));
  if (isIntegerQ(k) === true) return S.Zero;
  // Extract common symbolic factors before reducing the additive terms.
  // The quotient is structural, so no assumptions about floating signs enter.
  for (const g of q instanceof Mul ? q.args : [q]) {
    if (g instanceof Rational) continue;
    const quotient = extractMultiplicatively(p, g);
    if (quotient !== undefined) return mul(g, Mod(quotient, mul(q, pow(g, -1))));
  }
  return byRatio(p, q) ?? reduceTerms(p, q);
}

/**
 * SymPy Mod.eval for a sum: Mod terms with the same q are denested, and
 * ("simplify terms") each term of a sum whose remainder
 * evaluates is replaced by it, (x + y + 2) % x -> Mod(y + 2, x).
 */
function reduceTerms(p: Expr, q: Expr): Expr | undefined {
  if (!(p instanceof Add)) return undefined;
  // denest: Mod(Mod(x, q) + y, q) -> Mod(x + y, q)
  const inner = p.args.filter((t) => Mod.isApplied(t));
  if (inner.length && inner.every((t) => at(t.args, 1).key === q.key)) return Mod(add(...p.args.map((t) => (Mod.isApplied(t) ? at(t.args, 0) : t))), q);
  const terms = p.args.map((t) => evalMod(t, q) ?? t);
  const r = add(...terms);
  return r.key === p.key ? undefined : Mod(r, q);
}

/** Python's a % m (the sign of m). */
const pyMod = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;

/** A real number's value, or undefined (symbols, complex or not a number). */
function realNumber(e: Expr): number | undefined {
  if (e.freeSymbols().size) return undefined;
  try {
    const v = impl.toComplex(e);
    return v.im === 0 && Number.isFinite(v.re) ? v.re : undefined;
  } catch {
    return undefined;
  }
}

/**
 * SymPy Mod "by ratio" for real numbers: p - d*q with d = int(p/q), shifted
 * by q to the sign of q. A ratio within rounding of an integer is left
 * unevaluated rather than risk an off-by-one.
 */
function byRatio(p: Expr, q: Expr): Expr | undefined {
  const r = realNumber(p);
  const s = realNumber(q);
  if (r === undefined || s === undefined) return undefined;
  const ratio = r / s;
  if (Math.abs(ratio - Math.round(ratio)) < 1e-9 * Math.max(1, Math.abs(ratio)) || Math.abs(ratio) > 2 ** 52) return undefined;
  const d = Math.trunc(ratio);
  const rv = add(p, mul(-d, q));
  return (r - d * s) * s < 0 ? add(rv, q) : rv;
}

/** SymPy factorial._facmod: n! mod q from the exponents of the primes in n!. */
function facmod(n: bigint, q: bigint): bigint {
  let res = 1n;
  const N = Number(isqrt(n));
  const pw: bigint[] = Array.from({ length: N }, () => 1n);
  let m = 2n;
  for (const prime of sieve.primerange(2n, n + 1n)) {
    if (m > 1n) {
      m = 0n;
      for (let y = n / prime; y > 0n; y /= prime) m += y;
    }
    if (m < BigInt(N)) pw[Number(m)] = (at(pw, Number(m)) * prime) % q;
    else res = (res * powmod(prime, m, q)) % q;
  }
  for (let ex = 1; ex < N; ex++) {
    const bs = at(pw, ex);
    if (bs === 1n) continue;
    if (bs === 0n) return 0n;
    res = (res * powmod(bs, BigInt(ex), q)) % q;
  }
  return res;
}

/** SymPy factorial._eval_Mod: n! mod q, by Wilson's theorem when q is a prime just above n. */
function factorialMod(n: bigint, q: bigint): Expr | undefined {
  const aq = q < 0n ? -q : q;
  const d = aq - n;
  if (d <= 0n) return S.Zero;
  const prime = isprime(aq);
  if (d === 1n) {
    // (p - 1)! = -1 mod p for a prime, and (m - 1)! = 0 mod m for a composite m > 5
    if (prime) return Rational.of(pyMod(-1n, q));
    return aq >= 6n ? S.Zero : Rational.of(pyMod(facmod(n, aq), q));
  }
  let fc: bigint;
  if (prime && d - 1n < n) {
    // n! = (-1)**d / (d - 1)! mod p (from (p - 1)! = -1)
    fc = powmod(facmod(d - 1n, aq), aq - 2n, aq);
    if (d % 2n === 1n) fc = -fc;
  } else fc = facmod(n, aq);
  return Rational.of(pyMod(fc, q));
}

/** SymPy Mod(p, q) (Python's p % q for expressions). */
export const Mod: DefinedFunction = /* @__PURE__ */ defineFunction('Mod', {
  nargs: 2,
  eval: (p, q) => evalMod(p, q),
  latex: ([p, q]) => `${p} \\bmod ${q}`,
});
