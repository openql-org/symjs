// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.core.exprtools.Factors: a product kept as a map from
 * base to exponent, with quotient and remainder by another product.
 */

import type { Expr, ExprLike } from './nodes';
import { Add, Float, Mul, Rational, S, isNum } from './nodes';
import { ExprMap } from './exprmap';
import { add, asBaseExp, mul, neg, pow, sub, sympify } from './ops';
import { argsCncSplit, asCoeffMul, asPowersDict, decomposePower, extractAdditively, primitive } from './methods';
import { str } from '../printing/str';
import { getOrThrow } from './guard';
import { ordered } from './match';
import { gcd, lcm } from './numbers';
import { isNegative } from './assumptions';

const isNumber = (e: Expr): boolean => isNum(e);
const isZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isOne = (e: Expr): boolean => e instanceof Rational && e.p === 1n && e.q === 1n;

/** SymPy as_coeff_Add: the numeric term and the rest. */
function asCoeffAddTerm(e: Expr): [Expr, Expr] {
  if (isNum(e)) return [e, S.Zero];
  if (e instanceof Add) {
    const c = e.args[0];
    if (c !== undefined && isNum(c)) return [c, add(...e.args.slice(1))];
  }
  return [S.Zero, e];
}

/** Sign of a number expression (-1, 0 or 1). */
const sign = (e: Expr): number => Math.sign(e.toNumber());

/** A Map input of Factors (its values are converted by sympify). */
const isExprMap = (x: unknown): x is ReadonlyMap<Expr, ExprLike> => x instanceof Map;

/**
 * A product as base -> exponent (SymPy Factors).
 *
 * @see SymPy `sympy.core.exprtools.Factors`
 */
export class Factors {
  /**
   * The underlying map from base to exponent (SymPy factors).
   *
   * @see SymPy `sympy.core.exprtools.Factors.factors`
   */
  readonly factors: ExprMap<Expr>;

  /**
   * Creates a `Factors`.
   *
   * @param factors - The product or base-to-exponent mapping.
   */
  constructor(factors?: Factors | ExprLike | ReadonlyMap<Expr, ExprLike> | null) {
    this.factors = Factors.build(factors);
  }

  private static build(input: Factors | ExprLike | ReadonlyMap<Expr, ExprLike> | null | undefined): ExprMap<Expr> {
    if (input instanceof Factors) return new ExprMap(input.factors);
    if (input === undefined || input === null) return new ExprMap();
    if (isExprMap(input)) {
      const f = new ExprMap<Expr>([...input].map(([k, v]) => [k, sympify(v)] as const));
      // powers of -1 and I are made canonical
      const handle = [...f.keys()].filter((k) => k.key === S.I.key || k.key === S.NegOne.key || k.key === S.One.key || (k instanceof Float && Math.abs(k.toNumber()) === 1));
      let i1: Expr = S.One;
      for (const k of handle) {
        const v = f.get(k);
        if (v === undefined || !isNumber(v)) continue;
        i1 = mul(i1, pow(k, v));
        f.delete(k);
      }
      if (!isOne(i1)) {
        for (const a of i1 instanceof Mul ? i1.args : [i1]) {
          if (a instanceof Float && a.isNegative) {
            f.set(neg(a), S.One);
            f.set(S.NegOne, S.One);
          } else if (a.key === S.NegOne.key || a.key === S.I.key) f.set(a, S.One);
          else {
            const [b, e] = asBaseExp(a);
            f.set(b, add(f.get(b) ?? S.Zero, e));
          }
        }
      }
      return f;
    }
    const e = sympify(input);
    if (isOne(e)) return new ExprMap();
    if (isZero(e)) return new ExprMap([[S.Zero, S.One]]);
    if (e instanceof Rational) {
      const f = new ExprMap<Expr>();
      let n = e;
      if (n.p < 0n) {
        f.set(S.NegOne, S.One);
        n = Rational.of(-n.p, n.q);
      }
      if (!isOne(n)) {
        if (n.q === 1n) f.set(n, S.One);
        else {
          if (n.p !== 1n) f.set(Rational.of(n.p), S.One);
          f.set(Rational.of(n.q), S.NegOne);
        }
      }
      return f;
    }
    if (e.key === S.NegativeInfinity.key || (e instanceof Float && e.isNegative)) return new ExprMap([[S.NegOne, S.One], [neg(e), S.One]]);
    if (isNum(e) || e.args.length === 0) return new ExprMap([[e, S.One]]);
    const [c0, nc] = argsCncSplit(e);
    const nI = c0.filter((x) => x.key === S.I.key).length;
    const c = c0.filter((x) => x.key !== S.I.key);
    const f = new ExprMap<Expr>(asPowersDict(mul(...c)));
    for (const k of [...f.keys()]) {
      if (k instanceof Rational && k.q !== 1n) {
        const p = Rational.of(k.p);
        const q = Rational.of(k.q);
        const ek = getOrThrow(f, k);
        f.delete(k);
        f.set(p, add(f.get(p) ?? S.Zero, ek));
        f.set(q, sub(f.get(q) ?? S.Zero, ek));
      }
    }
    if (nI) f.set(S.I, add(f.get(S.I) ?? S.Zero, nI));
    if (nc.length) f.set(new Mul(nc), S.One);
    return f;
  }

  /**
   * The bases (SymPy gens).
   *
   * @returns The bases (SymPy gens).
   * @see SymPy `sympy.core.exprtools.Factors.gens`
   */
  get gens(): Set<Expr> {
    return new Set(this.factors.keys());
  }
  /**
   * The product is zero.
   *
   * @returns Whether the value is zero.
   * @see SymPy `sympy.core.exprtools.Factors.is_zero`
   */
  get isZero(): boolean {
    return this.factors.size === 1 && this.factors.has(S.Zero);
  }
  /**
   * The product is one.
   *
   * @returns Whether the value equals one.
   * @see SymPy `sympy.core.exprtools.Factors.is_one`
   */
  get isOne(): boolean {
    return this.factors.size === 0;
  }

  /**
   * The product as an expression (SymPy as_expr).
   *
   * @returns The product of the stored factors raised to their exponents.
   * @see SymPy `sympy.core.exprtools.Factors.as_expr`
   */
  asExpr(): Expr {
    const args: Expr[] = [];
    for (const [factor, e] of this.factors) {
      if (isOne(e)) args.push(factor);
      else if (e instanceof Rational && e.q === 1n) {
        const [b, be] = asBaseExp(factor);
        args.push(pow(b, mul(e, be)));
      } else args.push(pow(factor, e));
    }
    return mul(...args);
  }

  /**
   * Factors of self * other (SymPy mul).
   *
   * @param other - The other operand.
   * @returns The product of the operands.
   * @see SymPy `sympy.core.exprtools.Factors.mul`
   */
  mul(other: Factors | ExprLike): Factors {
    const o = other instanceof Factors ? other : new Factors(other);
    if (this.isZero || o.isZero) return new Factors(S.Zero);
    const f = new ExprMap(this.factors);
    for (const [factor, e] of o.factors) {
      const cur = f.get(factor);
      if (cur !== undefined) {
        const s = add(cur, e);
        if (isZero(s)) {
          f.delete(factor);
          continue;
        }
        f.set(factor, s);
      } else f.set(factor, e);
    }
    return new Factors(f);
  }

  /**
   * self and other with their common part removed (SymPy div): the
   * quotient and the remaining factors of other.
   *
   * @param other - The other operand.
   * @returns The numerator and denominator products after cancelling common factors.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.core.exprtools.Factors.div`
   */
  div(other: Factors | ExprLike): [Factors, Factors] {
    const quo = new ExprMap(this.factors);
    const rem = new ExprMap<Expr>();
    let o: Factors;
    if (other instanceof Factors) o = other;
    else {
      o = new Factors(other);
      if (o.isZero) throw new RangeError('Factors.div: division by zero');
      if (this.isZero) return [new Factors(S.Zero), new Factors()];
    }
    for (const [factor, e0] of o.factors) {
      let e = e0;
      const q = quo.get(factor);
      if (q !== undefined) {
        const d = sub(q, e);
        if (isNumber(d)) {
          if (sign(d) <= 0) quo.delete(factor);
          if (sign(d) >= 0) {
            if (!isZero(d)) quo.set(factor, d);
            continue;
          }
          e = neg(d);
        } else {
          const r = extractAdditively(q, e);
          // r = q - e is not a number, so it is not zero
          if (r !== undefined) quo.set(factor, r);
          else {
            let otherExp = e;
            const [sc, sa] = asCoeffAddTerm(q);
            if (!isZero(sc)) {
              const [oc, oa] = asCoeffAddTerm(otherExp);
              const diff = sub(sc, oc);
              if (sign(diff) > 0) {
                quo.set(factor, sub(q, oc));
                otherExp = oa;
              } else if (sign(diff) < 0) {
                quo.set(factor, sub(q, sc));
                otherExp = sub(oa, diff);
              } else {
                quo.set(factor, sa);
                otherExp = oa;
              }
            }
            // a numeric exponent of other would have been extracted above, so otherExp is not zero
            if (!isZero(otherExp)) rem.set(factor, otherExp);
          }
          continue;
        }
      }
      rem.set(factor, e);
    }
    return [new Factors(quo), new Factors(rem)];
  }

  /**
   * Remove the common factors, allowing a zero denominator (SymPy normal).
   *
   * @param other - The other operand.
   * @returns The reduced pair of factor products.
   * @see SymPy `sympy.core.exprtools.Factors.normal`
   */
  normal(other: Factors | ExprLike): [Factors, Factors] {
    if (!(other instanceof Factors)) {
      const o = new Factors(other);
      if (o.isZero) return [new Factors(), o];
      if (this.isZero) return [new Factors(S.Zero), new Factors()];
      return this.div(o);
    }
    return this.div(other);
  }

  /**
   * Raise the product to a nonnegative integer power.
   *
   * @param other - The other operand.
   * @returns The resulting power.
   * @throws RangeError when the exponent is not a nonnegative integer.
   * @see SymPy `sympy.core.exprtools.Factors.pow`
   */
  pow(other: Factors | ExprLike): Factors {
    const e = other instanceof Factors ? other.asExpr() : sympify(other);
    if (!(e instanceof Rational) || !e.isInteger || e.p < 0n) throw new RangeError('expected non-negative integer');
    return new Factors(new ExprMap(e.isZero ? [] : [...this.factors].map(([b, x]) => [b, mul(x, e)] as const)));
  }

  /**
   * Common bases with the smaller provable exponent (SymPy gcd).
   *
   * @param other - The other operand.
   * @returns The common bases raised to their smaller exponents.
   * @see SymPy `sympy.core.exprtools.Factors.gcd`
   */
  gcd(other: Factors | ExprLike): Factors {
    const o = other instanceof Factors ? other : new Factors(other);
    if (!(other instanceof Factors) && o.isZero) return new Factors(this);
    const factors = new ExprMap<Expr>();
    for (const [b, e] of this.factors) {
      const x = o.factors.get(b);
      if (x === undefined) continue;
      const negative = isNegative(sub(e, x));
      if (negative !== undefined) factors.set(b, negative ? e : x);
    }
    return new Factors(factors);
  }

  /**
   * Union of bases with their larger exponent (SymPy lcm).
   *
   * @param other - The other operand.
   * @returns The combined bases raised to their larger exponents.
   * @throws TypeError when the relative order of symbolic exponents cannot be decided.
   * @see SymPy `sympy.core.exprtools.Factors.lcm`
   */
  lcm(other: Factors | ExprLike): Factors {
    const o = other instanceof Factors ? other : new Factors(other);
    if (!(other instanceof Factors) && (this.isZero || o.isZero)) return new Factors(S.Zero);
    const factors = new ExprMap(this.factors);
    for (const [b, e] of o.factors) {
      const x = factors.get(b);
      if (x === undefined) factors.set(b, e);
      else {
        const negative = isNegative(sub(e, x));
        if (negative === undefined) throw new TypeError('cannot compare symbolic exponents');
        factors.set(b, negative ? x : e);
      }
    }
    return new Factors(factors);
  }

  /**
   * The numerator Factors of self / other (SymPy quo, the / operator).
   *
   * @param other - The other operand.
   * @returns The numerator Factors of self / other (SymPy quo, the / operator).
   * @see SymPy `sympy.core.exprtools.Factors.quo`
   */
  quo(other: Factors | ExprLike): Factors {
    return this.div(other)[0];
  }
  /**
   * The denominator Factors of self / other (SymPy rem).
   *
   * @param other - The other operand.
   * @returns The denominator Factors of self / other (SymPy rem).
   * @see SymPy `sympy.core.exprtools.Factors.rem`
   */
  rem(other: Factors | ExprLike): Factors {
    return this.div(other)[1];
  }

  /**
   * Factors({x: 1, y: 2}), the bases in SymPy's order.
   *
   * @returns The formatted string.
   */
  toString(): string {
    const items = ordered([...this.factors.keys()]).map((k) => `${str(k)}: ${str(getOrThrow(this.factors, k))}`);
    return `Factors({${items.join(', ')}})`;
  }
}

/**
 * A commutative term as a coefficient times a quotient of two factor products.
 *
 * @see SymPy `sympy.core.exprtools.Term`
 */
export class Term {
  /**
   * The multiplicative coefficient of the term.
   *
   * @see SymPy `sympy.core.exprtools.Term.coeff`
   */
  readonly coeff: Expr;
  /**
   * The factorization of the numerator.
   *
   * @see SymPy `sympy.core.exprtools.Term.numer`
   */
  readonly numer: Factors;
  /**
   * The factorization of the denominator.
   *
   * @see SymPy `sympy.core.exprtools.Term.denom`
   */
  readonly denom: Factors;

  /**
   * Creates a `Term`.
   *
   * @param term - The expression to decompose, or the coefficient when factors are supplied.
   * @param numer - The factorization of the numerator.
   * @param denom - The factorization of the denominator.
   * @throws TypeError when the expression is noncommutative.
   */
  constructor(term: ExprLike, numer?: Factors, denom?: Factors) {
    const expr = sympify(term);
    if (numer !== undefined || denom !== undefined) {
      this.coeff = expr;
      this.numer = numer ?? new Factors();
      this.denom = denom ?? new Factors();
      return;
    }
    if (!expr.isCommutative) throw new TypeError('Term requires a commutative expression');
    const [coefficient, factors] = asCoeffMul(expr);
    let c = coefficient;
    const numerator = new ExprMap<bigint>();
    const denominator = new ExprMap<bigint>();
    for (const factor of factors) {
      const [base, exponent] = decomposePower(factor);
      const [content, prim] = base instanceof Add ? primitive(base) : [S.One, base];
      c = mul(c, pow(content, exponent));
      const target = exponent > 0n ? numerator : denominator;
      const power = exponent > 0n ? exponent : -exponent;
      if (power !== 0n) target.set(prim, (target.get(prim) ?? 0n) + power);
    }
    this.coeff = c;
    this.numer = new Factors(numerator);
    this.denom = new Factors(denominator);
  }

  /**
   * Reconstructs the expression from its coefficient and factors.
   *
   * @returns The coefficient times the numerator divided by the denominator.
   * @see SymPy `sympy.core.exprtools.Term.as_expr`
   */
  asExpr(): Expr {
    return mul(this.coeff, this.numer.asExpr(), pow(this.denom.asExpr(), -1));
  }

  /**
   * Multiplies the terms and cancels shared numerator and denominator factors.
   *
   * @param other - The other operand.
   * @returns The product of the operands.
   * @see SymPy `sympy.core.exprtools.Term.mul`
   */
  mul(other: Term): Term {
    const [numer, denom] = this.numer.mul(other.numer).normal(this.denom.mul(other.denom));
    return new Term(mul(this.coeff, other.coeff), numer, denom);
  }

  /**
   * Takes the reciprocal of the term.
   *
   * @returns The reciprocal term.
   * @see SymPy `sympy.core.exprtools.Term.inv`
   */
  inv(): Term {
    return new Term(pow(this.coeff, -1), this.denom, this.numer);
  }

  /**
   * Divides by another term.
   *
   * @param other - The other operand.
   * @returns The reduced quotient term.
   * @see SymPy `sympy.core.exprtools.Term.quo`
   */
  quo(other: Term): Term {
    return this.mul(other.inv());
  }

  /**
   * Raises the term to an integer power.
   *
   * @param exponent - The exponent.
   * @returns The resulting power.
   * @throws TypeError when the exponent is not an integer.
   * @see SymPy `sympy.core.exprtools.Term.pow`
   */
  pow(exponent: ExprLike): Term {
    const n = sympify(exponent);
    if (!(n instanceof Rational && n.isInteger)) throw new TypeError('Term powers require integer exponents');
    if (n.isNegative) return this.inv().pow(Rational.of(-n.p));
    return new Term(pow(this.coeff, n), this.numer.pow(n), this.denom.pow(n));
  }

  /**
   * Computes the greatest common divisor of the two terms.
   *
   * @param other - The other operand.
   * @returns The greatest common divisor of the two terms.
   * @see SymPy `sympy.core.exprtools.Term.gcd`
   */
  gcd(other: Term): Term {
    return new Term(termContent(this.coeff, other.coeff, false), this.numer.gcd(other.numer), this.denom.gcd(other.denom));
  }

  /**
   * Computes the least common multiple of the two terms.
   *
   * @param other - The other operand.
   * @returns The least common multiple of the two terms.
   * @see SymPy `sympy.core.exprtools.Term.lcm`
   */
  lcm(other: Term): Term {
    return new Term(termContent(this.coeff, other.coeff, true), this.numer.lcm(other.numer), this.denom.lcm(other.denom));
  }

  /**
   * Tests for structural equality with the other object.
   *
   * @param other - The other operand.
   * @returns Whether the two objects have equal components.
   */
  equals(other: Term): boolean {
    const sameFactors = (a: Factors, b: Factors): boolean => a.factors.size === b.factors.size &&
      [...a.factors].every(([base, exponent]) => b.factors.get(base)?.key === exponent.key);
    return this.coeff.key === other.coeff.key && sameFactors(this.numer, other.numer) && sameFactors(this.denom, other.denom);
  }

  /**
   * Formats the object as a string.
   *
   * @returns The formatted string.
   */
  toString(): string {
    return `Term(${str(this.coeff)}, ${String(this.numer)}, ${String(this.denom)})`;
  }
}

function termContent(a: Expr, b: Expr, multiple: boolean): Expr {
  if (a instanceof Rational && b instanceof Rational) {
    return multiple ? Rational.of(lcm(a.p, b.p), gcd(a.q, b.q)) : Rational.of(gcd(a.p, b.p), lcm(a.q, b.q));
  }
  if (a instanceof Float || b instanceof Float) {
    const prec = Math.max(a instanceof Float ? a.prec : 0, b instanceof Float ? b.prec : 0);
    return multiple ? mul(a, b) : new Float(1, prec);
  }
  throw new TypeError('Term coefficients must be real numbers');
}
