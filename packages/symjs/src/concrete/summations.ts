// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Sums and products (SymPy Sum/Product/summation/product).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Limit, Mul, Pow, Rational, S, Special, Sym, impl, isNum } from '../core/nodes';
import { apart } from '../polys/partfrac';
import { fraction } from '../simplify/rational';
import { Eq, Lt, piecewise } from '../core/logic';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, xreplace } from '../core/traverse';
import { abs, log, sin, tan } from '../functions/elementary';
import { bernoulliNumber, factorial, harmonic, rf } from '../functions/special';
import { polyCoefficients, roots } from '../polys/poly';
import { expandMul as expand } from '../simplify/expand';
import { combsimp } from '../simplify/gammasimp';
import { powsimp } from '../simplify/powsimp';
import { Concrete } from './node';

export { Concrete };

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger;
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';

export { Sum, Product } from '../core/concrete';
import { Sum, Product } from '../core/concrete';
import { at, cast, defined, first, getOrThrow } from '../core/guard';

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
    if (isOo(b) || isNegOo(a)) return f instanceof Rational && f.isZero ? S.Zero : mul(f, S.Infinity);
    return expand(mul(f, add(b, mul(-1, a), 1)));
  }
  // Karr convention for reversed limits (a range with a known length always has a sum)
  const diff_ = add(b, mul(-1, a));
  if (isInt(diff_) && diff_.p < -1n) return mul(-1, defined(sumOne(f, k, add(b, 1), add(a, -1)), 'sum over a finite range'));
  // explicit evaluation for short finite ranges (SymPy: fewer than 100 terms)
  if (isInt(diff_) && diff_.p < 100n) return directSum(f, k, a, diff_.p);
  // Karr convention: sum_{k=a}^{-oo} f = -sum_{k=-oo}^{a-1} f
  if (isNegOo(b) && !isNegOo(a)) {
    const r = sumOne(f, k, b, add(a, -1));
    return r === undefined ? undefined : mul(-1, r);
  }
  // k -> -k turns sum_{k=-oo}^{b} into a sum ending at oo
  if (isNegOo(a) && !isOo(b)) return sumOne(xreplace(f, [[k, mul(-1, k)]]), k, mul(-1, b), S.Infinity);
  if (isOo(b)) {
    const r = evalSumResidue(f, k, a, b);
    if (r) return r;
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
  // c * k**(-m) from a positive integer: generalized harmonic numbers (SymPy; harmonic(oo, m) = zeta(m))
  const [d0] = dep;
  if (dep.length === 1 && d0 instanceof Pow && d0.base.key === k.key && isInt(d0.exp) && d0.exp.isNegative && isInt(a) && a.isPositive) {
    const m = -d0.exp.p;
    const H = (u: Expr) => (m === 1n ? harmonic(u) : harmonic(u, Rational.of(m)));
    return mul(c, add(H(b), mul(-1, H(add(a, -1)))));
  }
  if (!isNegOo(a) && dep.length === 1 && d0 instanceof Pow && !d0.base.has(k)) {
    const P = d0;
    const ePc = polyCoefficients(P.exp, k);
    if (ePc && Math.max(...ePc.keys()) === 1) {
      const r = pow(P.base, getOrThrow(ePc, 1));
      const first = xreplace(ef, [[k, a]]);
      if (isOo(b)) {
        const closed = mul(first, pow(add(1, mul(-1, r)), -1));
        const rv = numeric(r);
        const fv = numeric(first);
        if (rv !== undefined) {
          if (Math.abs(rv) < 1) return closed;
          // a real geometric series with ratio >= 1 diverges to oo or -oo
          if (rv < 1 || fv === undefined || fv === 0) return undefined;
          return fv > 0 ? S.Infinity : S.NegativeInfinity;
        }
        return piecewise([closed, Lt(abs(r), 1)], [Sum(f, [k, a, b]), true]);
      }
      // c*base**(q + p*k) = c*base**q * r**k with r = base**p
      const c0 = mul(c, pow(P.base, ePc.get(0) ?? S.Zero));
      const closed = mul(add(pow(r, a), mul(-1, pow(r, add(b, 1)))), pow(add(1, mul(-1, r)), -1));
      // the closed form needs r != 1 (SymPy's Piecewise for a symbolic ratio)
      if (freeSymbols(r).size === 0) return mul(c0, closed);
      return mul(c0, piecewise([add(b, mul(-1, a), 1), Eq(r, 1)], [closed, true]));
    }
  }
  // exponential series: x**k / k! from 0 to oo
  if (isOo(b) && a instanceof Rational && a.isZero) {
    const num = factors.find((g): g is Pow => g instanceof Pow && g.exp.key === k.key);
    const den = factors.find((g) => g instanceof Pow && g.exp instanceof Rational && g.exp.p === -1n && g.base.key === factorial(k).key);
    if (num && den && factors.length === 2) return exp(num.base);
  }
  // two terms that cancel after a shift, also after a partial fraction decomposition (SymPy telescopic)
  if (!isOo(b)) {
    const t = telescopic(f, k, a, b) ?? (isRationalIn(f, k) ? telescopic(apart(f, k), k, a, b) : undefined);
    if (t !== undefined) return t;
  }
  // no closed form: a range with a known length is summed term by term (SymPy eval_sum_direct)
  return isInt(diff_) ? directSum(f, k, a, diff_.p) : undefined;
}

/** A rational function of k that is not a polynomial. */
function isRationalIn(f: Expr, k: Sym): boolean {
  const [n, d] = fraction(f);
  return d.has(k) && polyCoefficients(expand(n), k) !== undefined && polyCoefficients(expand(d), k) !== undefined;
}

/**
 * sum_{k=a}^{b} (L + R) for R = -L(k + s) with an integer shift s (SymPy telescopic): the first
 * |s| terms of L (of R) and the last ones of R (of L) remain.
 */
function telescopic(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if (!(f instanceof Add && f.args.length === 2)) return undefined;
  // (the terms of a sum are not sums)
  const [L, R] = [at(f.args, 0), at(f.args, 1)];
  for (let s = 1; s <= 8; s++) {
    for (const sh of [s, -s]) {
      if (!isZeroExpanded(add(xreplace(L, [[k, add(k, sh)]]), R))) continue;
      // telescopic_direct(L, R, s) for s > 0, telescopic_direct(R, L, |s|) for s < 0
      const [P, Q] = sh > 0 ? [L, R] : [R, L];
      const terms: Expr[] = [];
      for (let m = 0; m < s; m++) terms.push(xreplace(P, [[k, add(a, m)]]), xreplace(Q, [[k, add(b, -m)]]));
      return add(...terms);
    }
  }
  return undefined;
}

const isZeroExpanded = (e: Expr): boolean => {
  const x = expand(e);
  return x instanceof Rational && x.isZero;
};

/** sum_{i=0}^{len} f(a + i). */
function directSum(f: Expr, k: Sym, a: Expr, len: bigint): Expr {
  const terms: Expr[] = [];
  for (let i = 0n; i <= len; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
  return add(...terms);
}

/**
 * Port of SymPy eval_sum_residue: sums of rational functions (optionally
 * times (-1)**k) over infinite ranges via residues of f*cot(pi*z) (or
 * f*csc(pi*z)). Only simple poles are handled.
 */
function evalSumResidue(f: Expr, k: Sym, a: Expr, b: Expr): Expr | undefined {
  if ([...freeSymbols(f)].some((s) => s.key !== k.key)) return undefined;
  // the callers pass b = oo (a sum from -oo to b is mirrored first)
  if (!(isInt(a) || isNegOo(a))) return undefined;
  const ratCoeffs = (e: Expr): [Map<number, Expr>, Map<number, Expr>] | undefined => {
    const [n, d] = fractionOf(e);
    const pn = polyCoefficients(expand(n), k);
    const pd = polyCoefficients(expand(d), k);
    return pn && pd ? [pn, pd] : undefined;
  };
  let alternating = false;
  let m = ratCoeffs(f);
  if (!m) {
    m = ratCoeffs(mul(f, pow(-1, mul(-1, k))));
    if (!m) return undefined;
    alternating = true;
  }
  let [pn, pd] = m;
  const deg = (p: Map<number, Expr>) => Math.max(-Infinity, ...[...p].filter(([, c]) => !(c instanceof Rational && c.isZero)).map(([i]) => i));
  const toExpr = (p: Map<number, Expr>) => add(...[...p].map(([i, c]) => mul(c, pow(k, i))));
  if (deg(pd) - deg(pn) < 2) return undefined;
  const isEven = () => {
    const ms = (p: Map<number, Expr>) => [...p].filter(([, c]) => !(c instanceof Rational && c.isZero)).map(([i]) => i);
    const all = (p: Map<number, Expr>, r: number) => ms(p).every((i) => i % 2 === r);
    return (all(pn, 0) && all(pd, 0)) || (all(pn, 1) && all(pd, 1));
  };
  // poles: all roots of the denominator, which must be simple
  const poles = (): [Rational[], Expr[]] | undefined => {
    const D = toExpr(pd);
    let rs: Expr[];
    try {
      rs = roots(D, k);
    } catch {
      return undefined;
    }
    if (rs.length !== deg(pd) || new Set(rs.map((r) => r.key)).size !== rs.length) return undefined;
    return [rs.filter(isInt), rs.filter((r) => !isInt(r))];
  };
  const residues = (rs: Expr[]): Expr => {
    const N = toExpr(pn);
    const dPoly = (p: Map<number, Expr>) => new Map([...p].filter(([i]) => i > 0).map(([i, c]): [number, Expr] => [i - 1, mul(i, c)]));
    const dN = toExpr(dPoly(pn));
    const dD = toExpr(dPoly(pd));
    const d2D = toExpr(dPoly(dPoly(pd)));
    return add(
      ...rs.map((r) => {
        const at = (e: Expr) => xreplace(e, [[k, r]]);
        const piR = mul(S.Pi, r);
        if (isInt(r)) {
          // f = g/(z - r) has a double pole in f*cot(pi*z) (or f*csc(pi*z)) at the integer r:
          // the residue is g'(r)/pi (times (-1)**r), g'(r) = (N'(r)*D'(r) - N(r)*D''(r)/2)/D'(r)**2
          const g1 = mul(add(mul(at(dN), at(dD)), mul(Rational.of(-1, 2), at(N), at(d2D))), pow(at(dD), -2));
          const res = mul(g1, pow(S.Pi, -1));
          return alternating ? mul(res, pow(-1, r)) : res;
        }
        const res = mul(at(N), pow(at(dD), -1));
        return mul(res, pow(alternating ? sin(piR) : tan(piR), -1));
      }),
    );
  };
  if (!isInt(a)) {
    // a = -oo, b = oo: the sum over all integers
    const ps = poles();
    if (!ps || ps[0].length) return undefined;
    return mul(-1, S.Pi, residues(ps[1]));
  }
  if (!isEven()) {
    const n = deg(pd);
    const lead = getOrThrow(pd, n);
    const sub = pd.get(n - 1) ?? S.Zero;
    const shift = mul(-1, sub, pow(lead, -1), Rational.of(1, n));
    if (!isInt(shift) || shift.isZero) return undefined;
    const sh = (p: Map<number, Expr>) => expand(xreplace(toExpr(p), [[k, add(k, shift)]]));
    const nn = sh(pn);
    const dd = sh(pd);
    pn = defined(polyCoefficients(nn, k), 'shifted numerator coefficients');
    pd = defined(polyCoefficients(dd, k), 'shifted denominator coefficients');
    if (!isEven()) return undefined;
    const g = alternating ? mul(pow(-1, k), pow(-1, shift), nn, pow(dd, -1)) : mul(nn, pow(dd, -1));
    return evalSumResidue(g, k, add(a, mul(-1, shift)), b);
  }
  const ps = poles();
  if (!ps) return undefined;
  const [intRoots, nonInt] = ps;
  const ints = intRoots.map((r) => Number(r.p));
  if (ints.length) {
    const mx = Math.max(...ints);
    if (ints.length !== mx - Math.min(...ints) + 1) return undefined;
    if (Number(a.p) <= mx) return undefined;
  }
  const full = mul(-1, S.Pi, residues([...intRoots, ...nonInt]));
  const at = (i: number) => xreplace(f, [[k, Rational.of(i)]]);
  const ai = Number(a.p);
  if (!ints.length) {
    const half = mul(add(full, at(0)), Rational.of(1, 2));
    const neg: Expr[] = [];
    const pos: Expr[] = [];
    for (let i = ai; i < 0; i++) neg.push(at(i));
    for (let i = 0; i < ai; i++) pos.push(at(i));
    return add(half, ...neg, mul(-1, add(...pos)));
  }
  const extra: Expr[] = [];
  for (let i = Math.max(...ints) + 1; i < ai; i++) extra.push(at(i));
  return add(mul(full, Rational.of(1, 2)), mul(-1, add(...extra)));
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
  // Karr convention for reversed limits (a range with a known length always has a product)
  if (isInt(diff_) && diff_.p < -1n) return pow(defined(productOne(f, k, add(b, 1), add(a, -1)), 'product over a finite range'), -1);
  // explicit evaluation for short finite ranges (SymPy: fewer than 100 factors)
  if (isInt(diff_) && diff_.p < 100n) return directProduct(f, k, a, diff_.p);
  // no closed form: a range with a known length is multiplied out (SymPy _eval_product_direct)
  return evalProduct(f, k, a, b) ?? (isInt(diff_) ? directProduct(f, k, a, diff_.p) : undefined);
}

/** prod_{i=0}^{len} f(a + i). */
function directProduct(f: Expr, k: Sym, a: Expr, len: bigint): Expr {
  const terms: Expr[] = [];
  for (let i = 0n; i <= len; i++) terms.push(xreplace(f, [[k, add(a, Rational.of(i))]]));
  return mul(...terms);
}

/** Port of SymPy Product._eval_product for the indefinite cases. */
function evalProduct(term: Expr, k: Sym, a: Expr, n: Expr): Expr | undefined {
  const count = add(n, mul(-1, a), 1);
  if (!term.has(k)) return term instanceof Rational && term.isOne ? S.One : pow(term, count);
  const pc = polyCoefficients(expand(term), k);
  if (pc) {
    const deg = Math.max(...pc.keys());
    let rs: Expr[];
    try {
      rs = roots(expand(term), k);
    } catch {
      rs = [];
    }
    const mult = new Map<string, [Expr, number]>();
    for (const r of rs) {
      const cur = mult.get(r.key);
      mult.set(r.key, [r, (cur ? cur[1] : 0) + 1]);
    }
    let A: Expr = S.One;
    let M = 0;
    for (const [r, m] of mult.values()) {
      M += m;
      A = mul(A, pow(rf(add(a, mul(-1, r)), count), m));
    }
    if (M < deg) return undefined;
    return mul(pow(getOrThrow(pc, deg), count), A);
  }
  if (term instanceof Mul) {
    // the factors with a product, times the Product of the others (SymPy: of several factors with k
    // at least one must have a product; a single one stays a Product times the constant factors)
    const without = term.args.filter((t) => !t.has(k));
    const withK = term.args.filter((t) => t.has(k));
    const done: Expr[] = [];
    const left: Expr[] = [];
    for (const t of withK) {
      const p = evalProduct(t, k, a, n);
      if (p === undefined) left.push(t);
      else done.push(p);
    }
    if (!done.length && withK.length > 1) return undefined;
    const rest = left.length ? Product(mul(...left), [k, a, n]) : S.One;
    return mul(pow(mul(...without), count), ...done, rest);
  }
  if (term instanceof Pow) {
    if (!term.base.has(k)) return pow(term.base, summation(term.exp, [k, a, n]));
    if (!term.exp.has(k)) {
      const p = evalProduct(term.base, k, a, n);
      if (p !== undefined) return pow(p, term.exp);
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
  // SymPy product() is Product.doit(deep=False), which powsimps the result (2**(n*(n + 1)/2))
  // (a number times a sum is distributed, as SymPy's Mul does: 2**(-a**2/2 + a/2 + n**2/2 + n/2))
  const distribute = (e: Expr): Expr => (e instanceof Mul && e.args.length === 2 && isNum(at(e.args, 0)) && at(e.args, 1) instanceof Add ? expand(e) : e);
  return mapBottomUp(powsimp(productDeep(sympify(f), limits)), distribute);
}

/** Product(...).doit(): the product without the final powsimp. */
function productDeep(f: Expr, limits: readonly [Sym, ExprLike, ExprLike][]): Expr {
  let e = f;
  for (const [k, a, b] of limits) {
    const r = productOne(e, k, sympify(a), sympify(b));
    if (r === undefined || r.key === S.NaN.key) return Product(e, [k, a, b]);
    e = r;
  }
  return e;
}

/** doit() for a Concrete node. */
export function doitConcrete(c: Concrete): Expr {
  const lims = c.limits.map(([k, a, b]): [Sym, Expr, Expr] => [cast(k, Sym, 'limit variable'), a, b]);
  return c.kind2 === 'Sum' ? summation(c.function, ...lims) : productDeep(c.function, lims);
}

/** Reverse the order of the given limits (by index or variable), SymPy reverse_order. */
export function reverseOrder(c: Concrete, ...which: (number | Sym)[]): Expr {
  // as in SymPy, each selected limit is reversed once however often it is named
  const sel = new Set(which.map((w) => (typeof w === 'number' ? w : c.limits.findIndex(([k]) => k.key === w.key))));
  const lims = c.limits.map(([k, a, b], i): [Expr, Expr, Expr] => (sel.has(i) ? [k, add(b, 1), add(a, -1)] : [k, a, b]));
  const odd = c.limits.filter((_, i) => sel.has(i)).length % 2 === 1;
  const f = !odd ? c.function : c.kind2 === 'Sum' ? mul(-1, c.function) : pow(c.function, -1);
  return new Concrete(c.kind2, [f, ...lims.flat()]);
}


const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const isFiniteBound = (e: Expr) => !(e instanceof Special);

/** Limit of f(k) as k -> oo, or undefined. */
function limOo(f: Expr, k: Sym): Expr | undefined {
  // (a limit at oo does not raise: an undetermined one is an unevaluated Limit)
  const l = impl.limit(f, k, S.Infinity);
  return l instanceof Limit ? undefined : l;
}

/** Decay order p of a rational function f(k) ~ C*k**(-p) (or k**(-p) with rational p). */
function pSeriesOrder(f: Expr, k: Sym): number | undefined {
  if (f instanceof Pow && f.base.key === k.key && f.exp instanceof Rational) return -f.exp.value;
  const [n, d] = fractionOf(f);
  const pn = polyCoefficients(expand(n), k);
  const pd = polyCoefficients(expand(d), k);
  if (!pn || !pd) return undefined;
  return Math.max(...pd.keys()) - Math.max(...pn.keys());
}

function fractionOf(f: Expr): [Expr, Expr] {
  const fs = f instanceof Mul ? f.args : [f];
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const t of fs) {
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative) den.push(pow(t.base, mul(-1, t.exp)));
    else if (t instanceof Rational && !t.isInteger) {
      num.push(Rational.of(t.p));
      den.push(Rational.of(t.q));
    } else num.push(t);
  }
  return [mul(...num), mul(...den)];
}

/** SymPy Sum.is_convergent for common series tests (divergence, p-series, ratio, alternating). */
export function sumIsConvergent(c: Concrete): boolean | undefined {
  const [kE, a, b] = first(c.limits);
  const k0 = cast(kE, Sym, 'limit variable');
  if (isFiniteBound(a) && isFiniteBound(b)) return true;
  // as in SymPy, the summation variable is a positive integer
  const k = new Sym(k0.name, { integer: true, positive: true });
  const f0 = c.function;
  if (isNegOo(a)) {
    // k -> -k turns the range into one ending at oo
    const g = xreplace(f0, [[k0, mul(-1, k0)]]);
    if (!isOo(b)) return sumIsConvergent(new Concrete(c.kind2, [g, k0, mul(-1, b), S.Infinity]));
    const left = sumIsConvergent(new Concrete(c.kind2, [g, k0, S.Zero, S.Infinity]));
    const right = sumIsConvergent(new Concrete(c.kind2, [f0, k0, S.Zero, S.Infinity]));
    return left === false || right === false ? false : left === true && right === true ? true : undefined;
  }
  // Karr convention: Sum(f, (k, a, -oo)) = -Sum(f, (k, -oo, a - 1)) and Sum(f, (k, oo, b)) = -Sum(f, (k, b + 1, oo))
  if (isNegOo(b)) return sumIsConvergent(new Concrete(c.kind2, [f0, k0, b, add(a, -1)]));
  if (isOo(a) && !isOo(b)) return sumIsConvergent(new Concrete(c.kind2, [f0, k0, add(b, 1), S.Infinity]));
  // a complex infinity or nan as a limit
  if (!isOo(b)) return undefined;
  // other symbols (Sum(x**k, ...)): the answer depends on them (SymPy raises NotImplementedError)
  if ([...freeSymbols(f0)].some((v) => v.key !== k0.key)) return undefined;
  const f = xreplace(f0, [[k0, k]]);
  // a product converges with the sum of the logarithms of its factors (SymPy), which needs factors -> 1
  if (c.kind2 === 'Product') {
    const l = limOo(f, k);
    if (l !== undefined && !(l instanceof Rational && l.isOne)) return false;
    return sumIsConvergent(new Concrete('Sum', [log(f0), ...c.args.slice(1)]));
  }
  // divergence test: the terms (or their moduli) do not tend to 0
  const l = limOo(f, k);
  if (l !== undefined && !(l instanceof Rational && l.isZero)) return false;
  const la = limOo(impl.abs(f), k);
  if (la !== undefined && !(la instanceof Rational && la.isZero)) return false;
  // p-series: f ~ C*k**(-p) for rational functions
  const r = pSeriesOrder(f, k);
  if (r !== undefined) return r > 1;
  // limit comparison with a p-series: f ~ c*k**(-p) as k -> oo with a constant c != 0 (for a
  // complex c the real or the imaginary part compares, and |f| ~ |c|*k**(-p))
  try {
    const t = new Sym('_t', { positive: true });
    const [c0, e0] = defined(impl.leadterm?.(xreplace(f, [[k, pow(t, -1)]]), t), 'impl.leadterm');
    // f ~ C*k**(-p)*log(k)**(-q) (log(t) = -log(k) in the coefficient of t**p): it converges for p > 1,
    // or p = 1 and q > 1 (SymPy's comparison with 1/(n**p*log(n)**q))
    const logT = log(t);
    let q = 0;
    const rest: Expr[] = [];
    for (const g of c0 instanceof Mul ? c0.args : [c0]) {
      if (g.key === logT.key) q -= 1;
      else if (g instanceof Pow && g.base.key === logT.key && g.exp instanceof Rational) q -= g.exp.value;
      else rest.push(g);
    }
    const C = mul(...rest);
    if (e0 instanceof Rational && C.freeSymbols().size === 0 && !(C instanceof Rational && C.isZero)) return e0.value > 1 || (e0.value === 1 && q > 1);
  } catch {
    // no asymptotic expansion
  }
  // ratio test
  // SymPy simplifies the ratio with combsimp(powsimp(...)) first
  const ratio = limOo(impl.abs(combsimp(powsimp(mul(xreplace(f, [[k, add(k, 1)]]), pow(f, -1))))), k);
  if (ratio?.freeSymbols().size === 0 && !(ratio instanceof Special)) {
    const v = ratio.toNumber();
    if (v < 1) return true;
    if (v > 1) return false;
  }
  if (ratio instanceof Special && ratio.name === 'oo') return false;
  // alternating series (-1)**k * g(k) with g -> 0 monotonically
  const fs = f instanceof Mul ? f.args : [f];
  const alt = fs.find((t) => t instanceof Pow && t.base instanceof Rational && t.base.p === -1n && t.base.q === 1n && t.exp.key === k.key);
  if (alt) {
    const g = mul(...fs.filter((t) => t !== alt));
    const lg = limOo(g, k);
    if (lg instanceof Rational && lg.isZero) return true;
  }
  return undefined;
}

/** Sum(|f|) converges. */
export function sumIsAbsolutelyConvergent(c: Concrete): boolean | undefined {
  return sumIsConvergent(new Concrete(c.kind2, [abs(c.function), ...c.args.slice(1)]));
}

/**
 * SymPy Sum.euler_maclaurin(m, n): [approximation, error estimate] by the
 * Euler-Maclaurin formula with m explicit leading terms and n correction terms.
 */
export function eulerMaclaurin(sum: Concrete, mIn = 0, n = 0): [Expr, Expr] {
  let m = mIn;
  if (!(sum instanceof Concrete) || sum.limits.length !== 1) throw new TypeError('euler_maclaurin: a Sum with one limit expected');
  let f = sum.function;
  const [i0, a0, b0] = first(sum.limits);
  const i = cast(i0, Sym, 'limit variable');
  let a = a0;
  let b = b0;
  const bmaNum = add(b, mul(-1, a));
  if (bmaNum instanceof Rational && bmaNum.isNegative) {
    if (add(a, mul(-1, b)).key === S.One.key) return [S.Zero, S.Zero];
    [a, b] = [add(b, 1), add(a, -1)];
    f = mul(-1, f);
  }
  const at = (e: Expr, p: Expr) => xreplace(e, [[i, p]]);
  let s: Expr = S.Zero;
  if (m) {
    if (a instanceof Rational && b instanceof Rational) m = Math.min(m, Number((b).p - (a).p) + 1);
    s = add(...Array.from({ length: m }, (_, k) => at(f, add(a, k))));
    if (add(b, mul(-1, a), 1).key === Rational.of(m).key) return [s, S.Zero];
    a = add(a, m);
  }
  s = add(s, impl.integrate(f, i, [a, b]));
  const fpoint = (e: Expr): [Expr, Expr] => (b instanceof Special && b.name === 'oo' ? [at(e, a), S.Zero] : [at(e, a), at(e, b)]);
  const [fa, fb] = fpoint(f);
  const iterm = mul(add(fa, fb), S.Half);
  let g = impl.diff(f, i, 1);
  let term: Expr = S.Zero;
  for (let k = 1; k <= n + 1; k++) {
    const [ga, gb] = fpoint(g);
    term = mul(bernoulliNumber(2 * k), pow(factorial(2 * k), -1), add(gb, mul(-1, ga)));
    if (k > n) break;
    s = add(s, term);
    g = impl.diff(g, i, 2);
  }
  return [add(s, iterm), abs(term)];
}
