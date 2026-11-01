// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Sums and products (SymPy Sum/Product/summation/product).
 */

import { Expr, ExprLike, Mul, Pow, Rational, Special, Sym } from '../core/nodes';
import { Lt, piecewise } from '../core/logic';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, xreplace } from '../core/traverse';
import { abs } from '../functions/elementary';
import { bernoulliNumber, factorial } from '../functions/special';
import { polyCoefficients } from '../polys/poly';
import { expandMul as expand } from '../simplify/expand';
import { Concrete } from './node';

export { Concrete };

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';

/** Unevaluated Sum(f, (k, a, b), ...). */
export function Sum(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Sum', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}

/** Unevaluated Product(f, (k, a, b), ...). */
export function Product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  return new Concrete('Product', [sympify(f), ...limits.flatMap(([k, a, b]) => [k, sympify(a), sympify(b)])]);
}

/** S_p(n) = sum_{k=1}^{n} k^p (Faulhaber, with B_1 = +1/2). */
function powerSum(p: number, n: Expr): Expr {
  const terms: Expr[] = [];
  for (let j = 0; j <= p; j++) {
    const binom = choose(p + 1, j);
    terms.push(mul(binom, bernoulliNumber(j), pow(n, p + 1 - j)));
  }
  return expand(mul(Rational.of(1, p + 1), add(...terms)));
}

function choose(n: number, k: number): Rational {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return Rational.of(r);
}

/** Closed form of sum_{k=a}^{b} f, or undefined. */
function sumOne(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if (!f.has(k)) {
    if (isOo(b) || (a instanceof Special && a.name === '-oo')) return undefined;
    return expand(mul(f, add(b, mul(-1, a), 1)));
  }
  // Karr convention for reversed limits
  const diff_ = add(b, mul(-1, a));
  if (isInt(diff_) && diff_.p < -1n) {
    const r = sumOne(f, k, add(b, 1), add(a, -1));
    return r === undefined ? undefined : mul(-1, r);
  }
  // explicit evaluation for short finite ranges
  if (isInt(diff_) && diff_.p >= -1n && diff_.p <= 1000n) {
    const terms: Expr[] = [];
    for (let i = 0n; i <= diff_.p; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
    return add(...terms);
  }
  const ef = expand(f);
  const pc = polyCoefficients(ef, k);
  if (pc && !isOo(b)) {
    const parts: Expr[] = [];
    for (const [p, c] of pc) {
      parts.push(mul(c, add(powerSum(p, b), mul(-1, powerSum(p, add(a, -1))))));
    }
    return expand(add(...parts));
  }
  // c * r**k (geometric)
  const factors = ef instanceof Mul ? ef.args : [ef];
  const dep = factors.filter((g) => g.has(k));
  const c = mul(...factors.filter((g) => !g.has(k)));
  if (dep.length === 1 && dep[0] instanceof Pow && !dep[0].base.has(k)) {
    const P = dep[0];
    const ePc = polyCoefficients(P.exp, k);
    if (ePc && Math.max(...ePc.keys()) === 1) {
      const r = pow(P.base, ePc.get(1)!);
      const first = xreplace(ef, [[k, a]]);
      if (isOo(b)) {
        const closed = mul(first, pow(add(1, mul(-1, r)), -1));
        const rv = numeric(r);
        if (rv !== undefined) return Math.abs(rv) < 1 ? closed : undefined;
        return piecewise([closed, Lt(abs(r), 1)], [Sum(f, [k, a, b]), true]);
      }
      return mul(c, add(pow(r, a), mul(-1, pow(r, add(b, 1)))), pow(add(1, mul(-1, r)), -1));
    }
  }
  // exponential series: x**k / k! from 0 to oo
  if (isOo(b) && a instanceof Rational && a.isZero) {
    const num = factors.find((g) => g instanceof Pow && g.exp.key === k.key);
    const den = factors.find((g) => g instanceof Pow && g.exp instanceof Rational && g.exp.p === -1n && g.base.key === factorial(k).key);
    if (num && den && factors.length === 2) return exp((num as Pow).base);
  }
  return undefined;
}

function numeric(e: Expr): number | undefined {
  if (freeSymbols(e).size) return undefined;
  try {
    const v = e.toComplex();
    return Math.abs(v.im) < 1e-14 ? v.re : undefined;
  } catch {
    return undefined;
  }
}

function productOne(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  const diff_ = add(b, mul(-1, a));
  if (isInt(diff_) && diff_.p < -1n) {
    const r = productOne(f, k, add(b, 1), add(a, -1));
    return r === undefined ? undefined : pow(r, -1);
  }
  if (isInt(diff_) && diff_.p >= -1n && diff_.p <= 1000n) {
    const terms: Expr[] = [];
    for (let i = 0n; i <= diff_.p; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
    return mul(...terms);
  }
  if (!f.has(k)) return pow(f, add(b, mul(-1, a), 1));
  // k**p from 1 to m
  if (a instanceof Rational && a.isOne) {
    if (f.key === k.key) return factorial(b);
    if (f instanceof Pow && f.base.key === k.key && !f.exp.has(k)) return pow(factorial(b), f.exp);
    if (f instanceof Mul) {
      const parts = f.args.map((g) => productOne(g, k, a, b));
      if (parts.every((p): p is Expr => p !== undefined)) return mul(...parts);
    }
  }
  return undefined;
}

/** Evaluate sums and products (SymPy summation / doit). */
export function summation(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  let e = sympify(f);
  for (const [k, a, b] of limits) {
    const r = sumOne(e, k, sympify(a), sympify(b));
    if (r === undefined) return Sum(e, [k, a, b]);
    e = r;
  }
  return e;
}

export function product(f: ExprLike, ...limits: [Sym, ExprLike, ExprLike][]): Expr {
  let e = sympify(f);
  for (const [k, a, b] of limits) {
    const r = productOne(e, k, sympify(a), sympify(b));
    if (r === undefined) return Product(e, [k, a, b]);
    e = r;
  }
  return e;
}

/** doit() for a Concrete node. */
export function doitConcrete(c: Concrete): Expr {
  const lims = c.limits.map(([k, a, b]) => [k as Sym, a, b] as [Sym, Expr, Expr]);
  return c.kind2 === 'Sum' ? summation(c.function, ...lims) : product(c.function, ...lims);
}

/** Reverse the order of the given limits (by index or variable), SymPy reverse_order. */
export function reverseOrder(c: Concrete, ...which: (number | Sym)[]): Expr {
  const lims = c.limits.map((l) => [...l] as [Expr, Expr, Expr]);
  let f = c.function;
  for (const w of which) {
    const i = typeof w === 'number' ? w : lims.findIndex(([k]) => k.key === w.key);
    const [k, a, b] = lims[i]!;
    lims[i] = [k, add(b, 1), add(a, -1)];
    f = c.kind2 === 'Sum' ? mul(-1, f) : pow(f, -1);
  }
  return new Concrete(c.kind2, [f, ...lims.flat()]);
}

