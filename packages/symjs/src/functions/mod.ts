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
import { Add, Fn, Float, Mul, Pow, Rational, S, Sym, impl, isNum } from '../core/nodes';
import { extractMultiplicatively } from '../core/methods';
import { add, couldExtractMinusSign, mul, pow, splitCoeff } from '../core/ops';
import { isqrt, powmod } from '../ntheory/intutil';
import { at } from '../core/guard';
import { isprime } from '../ntheory/primetest';
import { sieve } from '../ntheory/sieve';
import { isIntegerQ, isNegative, isNonNegative, isPositive } from '../core/assumptions';
import { DefinedFunctionCall, defineFunction } from '../core/defun';
import type { DefinedFunction, FunctionDefinition } from '../core/defun';
import { gcd } from '../core/numbers';
import { count } from '../core/match';
import { ratMod } from '../core/num';
import { rationalFromFloat } from '../core/numberutils';
import { fromRational } from '../numeric/mpf';

/** Closed assumptions supplied by a symbol, without loading the full predicate engine. */
const symbolFact = (e: Expr, name: string): boolean | undefined => e instanceof Sym ? e.assumptions0.get(name) : undefined;

function evalMod(p: Expr, q: Expr): Expr | undefined {
  if (q instanceof Rational && q.isZero) throw new RangeError('Modulo by zero');
  if (p instanceof Rational && q instanceof Rational) return ratMod(p, q);
  const exactFloat = p instanceof Float && q instanceof Rational && !q.isInteger ? p
    : q instanceof Float && p instanceof Rational ? q : undefined;
  if (exactFloat !== undefined) {
    const r = ratMod(p instanceof Rational ? p : rationalFromFloat(exactFloat), q instanceof Rational ? q : rationalFromFloat(exactFloat));
    return new Float(fromRational(r.p, r.q, exactFloat.prec), exactFloat.prec);
  }
  if ((p instanceof Float || p instanceof Rational) && (q instanceof Float || q instanceof Rational)) {
    const a = p.toNumber();
    const b = q.toNumber();
    return new Float(a - b * Math.floor(a / b));
  }
  if (p instanceof Rational && p.isZero) return S.Zero;
  if (p instanceof Rational && p.isOne && (symbolFact(q, 'prime') === true || (symbolFact(q, 'even') === true && isPositive(q) === true))) return S.One;
  if (p.key === q.key || add(p, q).key === S.Zero.key) return S.Zero;
  if (q instanceof Rational && q.equals(S.One) && isIntegerQ(p) === true) return S.Zero;
  if (p instanceof Fn && p.name === 'factorial' && !(p.args[0] instanceof Rational)) {
    const n = at(p.args, 0);
    const aq = couldExtractMinusSign(q) ? mul(-1, q) : q;
    if (add(n, 1).key === aq.key) {
      if (symbolFact(aq, 'prime') === true) return aq.key === q.key ? add(q, -1) : S.NegOne;
      if (symbolFact(aq, 'composite') === true && (symbolFact(aq, 'odd') === true || isNonNegative(add(aq, -6)) === true)) return S.Zero;
    }
    if (isIntegerQ(n) === true && isPositive(aq) === true && isNonNegative(add(n, mul(-1, aq))) === true) return S.Zero;
  }
  const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
  if (isInt(q)) {
    if (p instanceof Fn && p.name === 'partition') {
      // Ramanujan's congruences p(5n+4), p(7n+5) and p(11n+6).
      const residue = q.p === 5n ? 4n : q.p === 7n ? 5n : q.p === 11n ? 6n : undefined;
      if (residue !== undefined && evalMod(at(p.args, 0), q)?.equals(Rational.of(residue))) return S.Zero;
    }
    if (p instanceof Pow) {
      if (isInt(p.base) && isInt(p.exp) && p.exp.p >= 0n) return Rational.of(powmod(p.base.p, p.exp.p, q.p));
      if (integerExpression(p)) {
        const r = integerTreeMod(p, q.p);
        if (r !== undefined) return Rational.of(r);
      }
    }
    if (p instanceof Fn && p.name === 'factorial' && p.args[0] instanceof Rational && p.args[0].isInteger && p.args[0].p >= 0n) return factorialMod(p.args[0].p, q.p);
  }
  // Pow._eval_Mod: an integer base divisible by q remains divisible at a positive integer power.
  if (p instanceof Pow && isIntegerQ(p.base) === true && isIntegerQ(p.exp) === true && isPositive(p.exp) === true) {
    const r = evalMod(p.base, q);
    if (r instanceof Rational && r.isZero) return S.Zero;
    if (r instanceof Rational && r.isOne && q instanceof Rational && q.p === 2n && q.q === 1n) return S.One;
  }
  if (q instanceof Rational && q.p === 2n && q.q === 1n) {
    if (symbolFact(p, 'even') === true) return S.Zero;
    if (symbolFact(p, 'odd') === true) return S.One;
  }
  // Denest when the inner modulus is a multiple of q, or its range lies inside q's range.
  const negative = mul(-1, p);
  const inner = Mod.isApplied(p) ? p : Mod.isApplied(negative) ? negative : undefined;
  if (inner !== undefined) {
    const innerQ = at(inner.args, 1);
    const ratio = mul(innerQ, pow(q, -1));
    if (isIntegerQ(ratio) === true) return Mod(mul(inner === p ? 1 : -1, at(inner.args, 0)), q);
    if (isNonNegative(mul(inner === p ? 1 : -1, innerQ, add(q, mul(inner === p ? -1 : 1, innerQ)))) === true) return p;
  }
  // a rational ratio k = p/q: Mod(p, q) = q*Mod(k, 1) (SymPy extracts gcd(p, q))
  const k = mul(p, pow(q, -1));
  if (k instanceof Rational) return mul(q, ratMod(k, S.One));
  if (isIntegerQ(k) === true) return S.Zero;
  const [cp, rp] = splitCoeff(p);
  const [cq, rq] = splitCoeff(q);
  if (cp instanceof Rational && cq instanceof Rational && cp.isInteger && cq.isInteger) {
    const g = gcd(cp.p, cq.p);
    if (g > 1n) return mul(Rational.of(g), Mod(mul(Rational.of(cp.p / g), rp), mul(Rational.of(cq.p / g), rq)));
  }
  if (couldExtractMinusSign(p) && couldExtractMinusSign(q)) return mul(-1, Mod(mul(-1, p), mul(-1, q)));
  // Extract common symbolic factors before reducing the additive terms.
  // The quotient is structural, so no assumptions about floating signs enter.
  for (const g of q instanceof Mul ? q.args : [q]) {
    if (isNum(g)) continue;
    const quotient = extractMultiplicatively(p, g);
    if (quotient !== undefined && quotient.key !== p.key) return mul(g, Mod(quotient, mul(q, pow(g, -1))));
  }
  if (p instanceof Mul && q instanceof Rational && q.isInteger && p.args.every((t) => Mod.isApplied(t) && at(t.args, 1).key === q.key ? isIntegerQ(at(t.args, 0)) === true : isIntegerQ(t) === true)) {
    const hasInner = p.args.some((t) => Mod.isApplied(t) && at(t.args, 1).key === q.key);
    const terms = p.args.map((t) => {
      if (Mod.isApplied(t) && at(t.args, 1).key === q.key) return at(t.args, 0);
      if (hasInner) {
        const r = Mod(t, q);
        return Mod.isApplied(r) ? at(r.args, 0) : r;
      }
      return t instanceof Rational && t.isInteger ? ratMod(t, q) : t;
    });
    const reduced = mul(...terms);
    if (reduced.key !== p.key) return Mod(reduced, q);
  }
  if (cp instanceof Float || cq instanceof Float) {
    const ratio = cp.toNumber() / cq.toNumber();
    if (Number.isInteger(ratio)) {
      if (ratio === 1 && cq instanceof Rational && cq.isOne) return undefined;
      return mul(cq, Mod(mul(ratio, rp), rq));
    }
    if (cp instanceof Rational) return new DefinedFunctionCall('Mod', [mul(new Float(cp.toNumber()), rp), q], modDefinition);
  }
  return byRatio(p, q) ?? byDifference(p, q) ?? reduceTerms(p, q);
}

/** SymPy Mod's bounded difference comparisons for symbolic moduli. */
function byDifference(p: Expr, q: Expr): Expr | undefined {
  const positive = isPositive(q);
  const negative = isNegative(q);
  if (positive !== true && negative !== true) return undefined;
  const sign = positive === true ? 1 : -1;
  for (let i = -2; i < 2; i++) {
    const lo = add(p, mul(-i, q));
    if (isNonNegative(mul(sign, lo)) !== true) return undefined;
    if (isPositive(mul(sign, add(mul(i + 1, q), mul(-1, p)))) === true) return lo;
  }
  return undefined;
}

/** A nonnegative integer expression, evaluated only while its value fits the bound. */
function boundedInteger(e: Expr, bound: bigint): bigint | undefined {
  if (e instanceof Rational) return e.p <= bound ? e.p : undefined;
  const b = boundedInteger(at(e.args, 0), bound);
  const n = boundedInteger(at(e.args, 1), BigInt(bound.toString(2).length));
  if (b === undefined || n === undefined) return undefined;
  let r = 1n;
  for (let i = 0n; i < n; i++) {
    r *= b;
    if (r > bound) return undefined;
  }
  return r;
}

/** Integer power trees have exact nonnegative exponents, even beyond bigint capacity. */
function integerExpression(e: Expr): boolean {
  return e instanceof Rational ? e.isInteger && e.p >= 0n : e instanceof Pow && integerExpression(e.base) && integerExpression(e.exp);
}

/** Pow._eval_Mod: reduce nested integer powers before constructing their huge values. */
function integerTreeMod(e: Expr, modulus: bigint): bigint | undefined {
  if (e instanceof Rational) return pyMod(e.p, modulus);
  const m = modulus < 0n ? -modulus : modulus;
  if (m === 1n) return 0n;
  const b = integerTreeMod(at(e.args, 0), m);
  if (b === undefined) return undefined;
  const exponent = at(e.args, 1);
  if (exponent instanceof Rational) return powmod(b, exponent.p, modulus);
  const phi = impl.fn?.('totient', [Rational.of(m)]);
  if (!(phi instanceof Rational)) return undefined;
  const small = boundedInteger(exponent, phi.p);
  if (small !== undefined) return powmod(b, small, modulus);
  const n = integerTreeMod(exponent, phi.p);
  return n === undefined ? undefined : powmod(b, n + phi.p, modulus);
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
  const terms = p.args.map((t) => {
    const r = evalMod(t, q);
    return r !== undefined && count(r, (e) => Mod.isApplied(e)) <= count(t, (e) => Mod.isApplied(e)) ? r : t;
  });
  const hasFloat = p.args.some((t) => t instanceof Float);
  const r = hasFloat ? add(...terms.map((t) => t instanceof Float ? t : mul(new Float(1), t))) : add(...terms);
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
const modDefinition: FunctionDefinition = {
  nargs: 2,
  eval: (p, q) => evalMod(p, q),
  rewrite: { floor: (p, q) => add(p, mul(-1, q, new Fn('floor', [mul(p, pow(q, -1))]))) },
};
/**
 * Computes the remainder with the sign of the divisor.
 *
 * @param args - The dividend followed by the divisor.
 * @returns The symbolic remainder.
 * @see SymPy `sympy.core.mod.Mod`
 * @example
 * ```ts
 * import { Mod } from '@symjs/symjs';
 *
 * Mod(5, 3); // => 2
 * ```
 */
export const Mod: DefinedFunction = /* @__PURE__ */ defineFunction('Mod', modDefinition);
