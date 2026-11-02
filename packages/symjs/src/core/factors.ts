// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.core.exprtools.Factors: a product kept as a map from
 * base to exponent, with quotient and remainder by another product.
 */

import type { Expr, ExprLike } from './nodes';
import { Add, Mul, Rational, S, isNum } from './nodes';
import { ExprMap } from './exprmap';
import { add, asBaseExp, mul, neg, pow, sub, sympify } from './ops';
import { argsCncSplit, asPowersDict, extractAdditively } from './methods';
import { str } from '../printing/str';
import { getOrThrow } from './guard';

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

/** A product as base -> exponent (SymPy Factors). */
export class Factors {
  /** The underlying map from base to exponent (SymPy factors). */
  readonly factors: ExprMap<Expr>;

  constructor(factors?: Factors | ExprLike | ReadonlyMap<Expr, ExprLike> | null) {
    this.factors = Factors.build(factors);
  }

  private static build(input: Factors | ExprLike | ReadonlyMap<Expr, ExprLike> | null | undefined): ExprMap<Expr> {
    if (input instanceof Factors) return new ExprMap(input.factors);
    if (input === undefined || input === null) return new ExprMap();
    if (isExprMap(input)) {
      const f = new ExprMap<Expr>([...input].map(([k, v]) => [k, sympify(v)] as const));
      // powers of -1 and I are made canonical
      const handle = [...f.keys()].filter((k) => k.key === S.I.key || k.key === S.NegOne.key || k.key === S.One.key);
      let i1: Expr = S.One;
      for (const k of handle) {
        const v = f.get(k);
        if (v === undefined || !isNumber(v)) continue;
        i1 = mul(i1, pow(k, v));
        f.delete(k);
      }
      if (!isOne(i1)) {
        for (const a of i1 instanceof Mul ? i1.args : [i1]) {
          if (a.key === S.NegOne.key || a.key === S.I.key) f.set(a, S.One);
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

  /** The bases (SymPy gens). */
  get gens(): Set<Expr> {
    return new Set(this.factors.keys());
  }
  /** The product is zero. */
  get isZero(): boolean {
    return this.factors.size === 1 && this.factors.has(S.Zero);
  }
  /** The product is one. */
  get isOne(): boolean {
    return this.factors.size === 0;
  }

  /** The product as an expression (SymPy as_expr). */
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

  /** Factors of self * other (SymPy mul). */
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
          if (r !== undefined) {
            if (!isZero(r)) quo.set(factor, r);
            else quo.delete(factor);
          } else {
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
            if (!isZero(otherExp)) rem.set(factor, otherExp);
          }
          continue;
        }
      }
      rem.set(factor, e);
    }
    return [new Factors(quo), new Factors(rem)];
  }

  /** The numerator Factors of self / other (SymPy quo, the / operator). */
  quo(other: Factors | ExprLike): Factors {
    return this.div(other)[0];
  }
  /** The denominator Factors of self / other (SymPy rem). */
  rem(other: Factors | ExprLike): Factors {
    return this.div(other)[1];
  }

  /** SymPy repr: Factors({x: 1, y: 2}). */
  toString(): string {
    return `Factors({${[...this.factors].map(([k, v]) => `${str(k)}: ${str(v)}`).join(', ')}})`;
  }
}
