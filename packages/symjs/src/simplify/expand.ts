// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file expand(): distribute products over sums and expand integer powers of sums.
 */

import { isIntegerQ, isNegative, isNonNegative, isNonZero, isPositive, isReal } from '../core/assumptions';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, ExtensionExpr, Fn, Mul, Pow, Rational, S, Sym, impl, isNum } from '../core/nodes';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { cos, cosh, fn, im, log, re, sin, sinh, tan, tanh } from '../functions/elementary/elementary';
import { rebuild } from '../core/traverse';
import { at, defined, first } from '../core/guard';
import { integerNthroot } from '../core/numberutils';

const termsOf = (e: Expr): readonly Expr[] => (e instanceof Add ? e.args : [e]);

/** Multiply two expanded expressions, distributing over sums. */
function distribute(a: Expr, b: Expr): Expr {
  const ta = termsOf(a);
  const tb = termsOf(b);
  if (ta.length === 1 && tb.length === 1) return mul(a, b);
  const out: Expr[] = [];
  for (const x of ta) for (const y of tb) out.push(mul(x, y));
  return add(...out);
}

function expandPowInt(base: Expr, n: bigint): Expr {
  let result: Expr = Rational.of(1n);
  let b = base;
  let k = n;
  while (k > 0n) {
    if (k & 1n) result = distribute(result, b);
    k >>= 1n;
    if (k > 0n) b = distribute(b, b);
  }
  return result;
}

/**
 * SymPy Pow._eval_expand_multinomial for a sum raised to a rational power: (a + b)**n expanded
 * for an integer n, (a + b)**(n + r) as the expanded (a + b)**n times (a + b)**r for 0 < r < 1,
 * and 1/(a + b)**k expanded the same way for k > 1; undefined otherwise.
 */
function multinomialPow(b: Add, x: Rational): Expr | undefined {
  if (x.p < 0n) {
    if (-x.p <= x.q) return undefined;
    const inv = multinomialPow(b, Rational.of(-x.p, x.q));
    return pow(defined(inv, 'the expanded power'), -1);
  }
  const n = x.p / x.q;
  if (x.isInteger) return expandPowInt(b, n);
  if (n === 0n) return undefined;
  return distribute(expandPowInt(b, n), pow(b, Rational.of(x.p - n * x.q, x.q)));
}

function expandNode(e: Expr): Expr {
  if (e.args.length === 0) return e;
  const args = e.args.map(expandNode);
  const node = args.some((a, i) => a !== e.args[i]) ? rebuild(e, args) : e;

  if (node instanceof Mul) {
    if (!node.args.some((a) => a instanceof Add)) return node;
    return node.args.reduce<Expr>((acc, f) => distribute(acc, f), Rational.of(1n));
  }
  if (node instanceof Pow) {
    const [b, x] = node.args;
    // (x is not 0: b**0 evaluates to 1)
    return b instanceof Add && x instanceof Rational ? (multinomialPow(b, x) ?? node) : node;
  }
  return node;
}

/**
 * Distribute products over sums and expand integer powers of sums
 * (SymPy's `mul` and `multinomial` hints only), recursively.
 */
export function expandMul(e: ExprLike): Expr {
  return expandMulRounds(e, 8);
}

/** @internal expandMul with at most maxRounds passes (the result so far when no fixed point is reached). */
export function expandMulRounds(e: ExprLike, maxRounds: number): Expr {
  let cur = sympify(e);
  // Iterate to a fixed point: re-canonicalization can expose new sums.
  for (let i = 0; i < maxRounds; i++) {
    const next = expandNode(cur);
    if (next.key === cur.key) return next;
    cur = next;
  }
  return cur;
}

// ---------------------------------------------------------------------------
// SymPy-compatible expand() with hints
// ---------------------------------------------------------------------------

export interface ExpandHints {
  deep?: boolean;
  mul?: boolean;
  multinomial?: boolean;
  power_exp?: boolean;
  power_base?: boolean;
  log?: boolean;
  complex?: boolean;
  trig?: boolean;
  force?: boolean;
  /** Expand special functions into simpler ones (SymPy func=True). */
  func?: boolean;
  /** Expand numerator and denominator separately (SymPy frac=True). */
  frac?: boolean;
  /** Expand only the numerator (SymPy numer=True). */
  numer?: boolean;
  /** Expand only the denominator (SymPy denom=True). */
  denom?: boolean;
  /** Hints defined by extension nodes (ExtensionExpr.expandSelf), e.g. { double: true }. */
  [hint: string]: unknown;
}

const BUILTIN_HINTS = new Set(['deep', 'mul', 'multinomial', 'power_exp', 'power_base', 'log', 'complex', 'trig', 'force', 'func', 'frac', 'numer', 'denom', 'modulus', 'basic']);


const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
/** exp_polar(c) or a polar symbol (split off powers and logarithms like a positive factor). */
const isPolar = (f: Expr): boolean => (f instanceof Fn && f.name === 'exp_polar') || (f instanceof Sym && f.assumptions.polar === true);

/** All terms of the sum are nonnegative, or all nonpositive (SymPy `_all_nonneg_or_nonppos`). */
function allNonnegOrNonpos(e: Add): boolean {
  return e.args.every((a) => isNonNegative(a) === true) || e.args.every((a) => isNonPositive(a));
}
const isNonPositive = (e: Expr): boolean => isNegative(e) === true || (e instanceof Rational && e.isZero);

function powerExp(e: Expr, force: boolean): Expr {
  if (!(e instanceof Pow)) return e;
  const [b, x] = e.args;
  if (!(x instanceof Add)) return e;
  if (isE(b) || force || isNonZero(b) === true || allNonnegOrNonpos(x)) {
    return mul(...x.args.map((t) => pow(b, t)));
  }
  return e;
}

/** b**x with exp_polar(c)**x written exp_polar(c*x). */
const powPolar = (b: Expr, x: Expr): Expr => (b instanceof Fn && b.name === 'exp_polar' ? new Fn('exp_polar', [mul(first(b.args), x)]) : pow(b, x));

/** SymPy Pow._eval_expand_power_base: (a*b)**x = a**x*b**x for the factors that allow it. */
function powerBase(e: Expr, force: boolean): Expr {
  if (!(e instanceof Pow)) return e;
  const [b, x] = e.args;
  if (!(b instanceof Mul)) return e;
  const cargs = b.args.filter((f) => f.isCommutative);
  let nc = b.args.filter((f) => !f.isCommutative).map((f) => powerBase(f, force));
  if (nc.length) {
    // noncommutative factors keep their order: (A*B)**2 = A*B*A*B
    if (x instanceof Rational && x.isInteger) {
      const k = Number(x.p < 0n ? -x.p : x.p);
      const unit = x.p > 0n ? nc : nc.map((f) => pow(f, -1)).reverse();
      const rv = mul(...Array.from({ length: k }, () => unit).flat());
      return cargs.length ? mul(pow(mul(...cargs), x), rv) : rv;
    }
    if (!cargs.length) return e;
    nc = [mul(...nc)];
  }
  // commutative factors: nonnegative (or polar) ones always come out
  let other: Expr[] = [];
  const nonneg: Expr[] = [];
  const neg: Expr[] = [];
  for (const f of cargs) {
    const nn = isNonNegative(f);
    if (isPolar(f)) nonneg.push(f);
    else if (isReal(f) === false) other.push(f);
    else if (nn === true) nonneg.push(f);
    else if (nn === false) neg.push(f);
    else other.push(f);
  }
  let out: Expr[];
  if (force || isIntegerQ(x) === true) {
    out = [...nonneg, ...neg, ...other];
    other = nc;
  } else {
    // negative factors are made positive, the residual -1 stays with the others
    if (neg.length > 1) {
      let o: Expr = S.One;
      if (!other.length && isNum(first(neg))) o = defined(neg.shift(), 'a negative number');
      if (neg.length % 2) o = mul(-1, o);
      nonneg.push(...neg.map((f) => mul(-1, f)));
      if (!(o instanceof Rational && o.isOne)) other.push(o);
    } else if (neg.length && other.length) {
      const n0 = first(neg);
      if (isNum(n0) && !(n0 instanceof Rational && n0.p === -1n && n0.q === 1n)) {
        other.push(S.NegOne);
        nonneg.push(mul(-1, n0));
      } else other.push(n0);
    } else other.push(...neg);
    out = nonneg;
    other.push(...nc);
  }
  const parts = out.map((f) => powPolar(f, x));
  if (other.length) parts.push(pow(mul(...other), x));
  return mul(...parts);
}

/** (b, k) with b**k == n and k maximal (k >= 2), or undefined (SymPy perfect_power for n >= 2). */
function perfectPower(n: bigint): [bigint, number] | undefined {
  for (let k = n.toString(2).length - 1; k >= 2; k--) {
    const [b, exact] = integerNthroot(n, k);
    if (exact) return [b, k];
  }
  return undefined;
}

/** SymPy log._eval_expand_log. */
function expandLogNode(e: Expr, force: boolean): Expr {
  if (!(e instanceof Fn && e.name === 'log')) return e;
  const a = first(e.args);
  if (a instanceof Rational) {
    // perfect powers are removed (log(8) = 3*log(2)) and a fraction is split
    if (!a.isInteger) return add(log(Rational.of(a.p)), mul(-1, log(Rational.of(a.q))));
    const pp = perfectPower(a.p);
    return pp ? mul(pp[1], log(Rational.of(pp[0]))) : e;
  }
  if (a instanceof Mul) {
    // positive (or polar) factors are split off, negative ones as log(-f) with -1 left inside
    const terms: Expr[] = [];
    const nonpos: Expr[] = [];
    for (const f of a.args) {
      if (force || isPositive(f) === true || isPolar(f)) terms.push(expandLogNode(log(f), force));
      else if (isNegative(f) === true) {
        // not expanded further here (log(-n) would split again); the next round of expand does it
        terms.push(log(mul(-1, f)));
        nonpos.push(S.NegOne);
      } else nonpos.push(f);
    }
    return terms.length ? add(...terms, log(mul(...nonpos))) : e;
  }
  if (a instanceof Pow) {
    // log(b**x) = x*log(b) for real x when b > 0 or -1 < x <= 1
    const [b, x] = a.args;
    const unitExp = (): boolean => isPositive(add(x, 1)) === true && isNonPositive(add(x, -1));
    if (force || (isReal(x) === true && (isPositive(b) === true || unitExp())) || isPolar(b)) return mul(x, expandLogNode(log(b), force));
  }
  return e;
}

/** Binomial coefficient C(n, k) as a bigint. */
function binom(n: number, k: number): bigint {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return r;
}

/** Sum of c_k*s**k for the coefficient list (lowest degree first). */
const polyIn = (cs: readonly bigint[], s: Expr): Expr => add(...cs.map((c, k) => mul(Rational.of(c), pow(s, k))));

/** Coefficients of the Chebyshev polynomial T_n (first kind) or U_n (second kind). */
function chebyshev(n: number, second: boolean): bigint[] {
  let prev: bigint[] = [1n];
  let cur: bigint[] = second ? [0n, 2n] : [0n, 1n];
  // (n >= 1 here)
  for (let k = 1; k < n; k++) {
    // P_{k+1} = 2*s*P_k - P_{k-1}
    const next = [0n, ...cur.map((c) => 2n * c)];
    prev.forEach((c, i) => (next[i] = at(next, i) - c));
    prev = cur;
    cur = next;
  }
  return cur;
}

/** The elementary symmetric polynomials e_0, ..., e_n of the terms (as sums of products). */
function symmetricPolys(ts: readonly Expr[]): Expr[] {
  const out: Expr[][] = ts.map(() => []);
  const rec = (start: number, chosen: Expr[]) => {
    if (chosen.length) defined(out[chosen.length - 1], 'symmetric polynomial').push(mul(...chosen));
    for (let i = start; i < ts.length; i++) rec(i + 1, [...chosen, at(ts, i)]);
  };
  rec(0, []);
  return [S.One, ...out.map((ps) => add(...ps))];
}

/** a = first term + the rest (SymPy Add.as_two_terms). */
const twoTerms = (a: Add): [Expr, Expr] => [first(a.args), add(...a.args.slice(1))];

/** An integer coefficient n >= 2 of the argument and the rest (SymPy as_coeff_Mul), or undefined. */
function intMultiple(a: Expr): [number, Expr] | undefined {
  if (!(a instanceof Mul)) return undefined;
  const [c, rest] = splitCoeff(a);
  return c instanceof Rational && c.isInteger && c.p > 1n ? [Number(c.p), rest] : undefined;
}

/** tan(n*x) or tanh(n*x): the odd and even parts of (1 + I*t)**n (or (1 + t)**n), t = tan(x) or tanh(x). */
function multipleTan(n: number, t: Expr, hyperbolic: boolean): Expr {
  const odd = Array<bigint>(n + 1).fill(0n);
  const even = Array<bigint>(n + 1).fill(0n);
  for (let k = 0; k <= n; k++) (k % 2 ? odd : even)[k] = (hyperbolic || k % 4 < 2 ? 1n : -1n) * binom(n, k);
  return mul(polyIn(odd, t), pow(polyIn(even, t), -1));
}

/** tan or tanh of a sum: the ratio of the alternating sums of the symmetric polynomials of the terms. */
function sumTan(ts: readonly Expr[], hyperbolic: boolean): Expr {
  const e = symmetricPolys(ts);
  const num: Expr[] = [];
  const den: Expr[] = [];
  e.forEach((ei, i) => (i % 2 ? num : den).push(hyperbolic || i % 4 < 2 ? ei : mul(-1, ei)));
  return mul(add(...num), pow(add(...den), -1));
}

/** cot(n*x) or coth(n*x): the even and odd parts of (c + I)**n (or (c + 1)**n), c = cot(x) or coth(x). */
function multipleCot(n: number, c: Expr, hyperbolic: boolean): Expr {
  const num = Array<bigint>(n + 1).fill(0n);
  const den = Array<bigint>(n + 1).fill(0n);
  // the term C(n, k)*c**(n - k)*I**k
  for (let k = 0; k <= n; k++) (k % 2 ? den : num)[n - k] = (hyperbolic || k % 4 < 2 ? 1n : -1n) * binom(n, k);
  return mul(polyIn(num, c), pow(polyIn(den, c), -1));
}

/** cot or coth of a sum (SymPy cot._eval_expand_trig, coth._eval_expand_trig). */
function sumCot(cs: readonly Expr[], hyperbolic: boolean): Expr {
  const e = symmetricPolys(cs);
  const n = cs.length;
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (let i = n; i >= 0; i--) {
    const ei = at(e, i);
    ((n - i) % 2 ? den : num).push(hyperbolic || (n - i) % 4 < 2 ? ei : mul(-1, ei));
  }
  return mul(add(...num), pow(add(...den), -1));
}

/** Expand trigonometric and hyperbolic functions of sums and integer multiples (SymPy expand_trig). */
function expandTrigNode(e: Expr): Expr {
  if (!(e instanceof Fn)) return e;
  const a = first(e.args);
  switch (e.name) {
    case 'sin':
    case 'cos': {
      if (a instanceof Add) {
        const [x, y] = twoTerms(a);
        const [sx, sy, cx, cy] = [expandTrigNode(sin(x)), expandTrigNode(sin(y)), expandTrigNode(cos(x)), expandTrigNode(cos(y))];
        return e.name === 'sin' ? add(mul(sx, cy), mul(sy, cx)) : add(mul(cx, cy), mul(-1, sx, sy));
      }
      const m = intMultiple(a);
      if (!m) return e;
      const [n, x] = m;
      // multiple-angle formulas with Chebyshev polynomials (https://mathworld.wolfram.com/Multiple-AngleFormulas.html)
      if (e.name === 'cos') return polyIn(chebyshev(n, false), cos(x));
      if (n % 2) return mul(Rational.of(n % 4 === 1 ? 1n : -1n), polyIn(chebyshev(n, false), sin(x)));
      return expandMul(mul(Rational.of(n % 4 === 2 ? 1n : -1n), cos(x), polyIn(chebyshev(n - 1, true), sin(x))));
    }
    case 'tan':
    case 'tanh': {
      const hyperbolic = e.name === 'tanh';
      const f = hyperbolic ? tanh : tan;
      if (a instanceof Add) return sumTan(a.args.map((t) => expandTrigNode(f(t))), hyperbolic);
      const m = intMultiple(a);
      return m ? multipleTan(m[0], f(m[1]), hyperbolic) : e;
    }
    case 'cot':
    case 'coth': {
      const hyperbolic = e.name === 'coth';
      const f = (t: Expr) => fn(e.name === 'coth' ? 'coth' : 'cot', [t]);
      if (a instanceof Add) return sumCot(a.args.map((t) => expandTrigNode(f(t))), hyperbolic);
      const m = intMultiple(a);
      return m ? multipleCot(m[0], f(m[1]), hyperbolic) : e;
    }
    case 'sinh':
    case 'cosh': {
      const m = intMultiple(a);
      const xy: [Expr, Expr] | undefined = a instanceof Add ? twoTerms(a) : m ? [m[1], mul(m[0] - 1, m[1])] : undefined;
      if (!xy) return e;
      const [x, y] = xy;
      const r = e.name === 'sinh' ? add(mul(sinh(x), cosh(y)), mul(sinh(y), cosh(x))) : add(mul(cosh(x), cosh(y)), mul(sinh(x), sinh(y)));
      return expand(r, { trig: true });
    }
    case 'sec':
    case 'csc':
    case 'sech':
    case 'csch':
      // SymPy ReciprocalTrigonometricFunction: 1/(the expanded reciprocal function)
      return pow(expandTrigNode(fn(RECIPROCAL_OF[e.name], [a])), -1);
    default:
      return e;
  }
}

const RECIPROCAL_OF = { sec: 'cos', csc: 'sin', sech: 'cosh', csch: 'sinh' } as const;

/** Split into real and imaginary parts (SymPy expand(complex=True)). */
function expandComplexNode(e: Expr): Expr {
  const [r, i] = asRealImagExpand(e);
  return add(r, mul(S.I, i));
}

export function asRealImagExpand(e: Expr): [Expr, Expr] {
  if (e instanceof Fn) {
    const a = first(e.args);
    const ra = re(a);
    const ia = im(a);
    switch (e.name) {
      case 'cos':
        return [mul(cos(ra), cosh(ia)), mul(-1, sin(ra), sinh(ia))];
      case 'sin':
        return [mul(sin(ra), cosh(ia)), mul(cos(ra), sinh(ia))];
      case 'tan': {
        if (ia instanceof Rational && ia.isZero) return [tan(ra), S.Zero];
        const den = pow(add(cos(mul(2, ra)), cosh(mul(2, ia))), -1);
        return [mul(sin(mul(2, ra)), den), mul(sinh(mul(2, ia)), den)];
      }
      default:
        break;
    }
  }
  if (e instanceof Pow && isE(e.base)) {
    const ra = re(e.exp);
    const ia = im(e.exp);
    return [mul(pow(S.E, ra), cos(ia)), mul(pow(S.E, ra), sin(ia))];
  }
  const ex = expandMul(e);
  return [re(ex), im(ex)];
}

function applyBottomUp(e: Expr, f: (e: Expr) => Expr, deep: boolean): Expr {
  if (!deep || e.args.length === 0) return f(e);
  const args = e.args.map((a) => applyBottomUp(a, f, deep));
  const changed = args.some((a, i) => a !== e.args[i]);
  return f(changed ? rebuild(e, args) : e);
}

/**
 * SymPy-compatible expand. Default hints: mul, multinomial, power_exp,
 * power_base, log (and deep). Optional: complex, trig, force.
 */
export function expand(ex: ExprLike, hints: ExpandHints = {}): Expr {
  const { frac, numer, denom, ...rest } = hints;
  if (frac || numer || denom) {
    const [n, d] = defined(impl.fraction?.(sympify(ex)), 'impl.fraction (simplify/rational)');
    const en = frac || numer ? expand(n, rest) : n;
    const ed = frac || denom ? expand(d, rest) : d;
    return mul(en, pow(ed, -1));
  }
  const h = {
    deep: true,
    mul: true,
    multinomial: true,
    power_exp: true,
    power_base: true,
    log: true,
    complex: false,
    trig: false,
    force: false,
    ...hints,
  };
  let e = sympify(ex);
  // a node class with its own expand (SymPy Expectation.expand)
  if (e instanceof ExtensionExpr) {
    const own = e.expandTop(hints);
    if (own !== undefined) return own;
  }
  // hints of extension nodes (SymPy _eval_expand_<hint>), applied first like SymPy's unknown hints
  for (const [hint, on] of Object.entries(hints)) {
    if (!on || BUILTIN_HINTS.has(hint)) continue;
    e = applyBottomUp(e, (x) => (x instanceof ExtensionExpr ? (x.expandSelf(hint, h) ?? x) : x), h.deep);
  }
  if (h.func && impl.expandFunc) e = impl.expandFunc(e);
  for (let round = 0; round < 6; round++) {
    const was = e;
    if (h.complex) e = applyBottomUp(e, expandComplexNode, false);
    if (h.log) e = applyBottomUp(e, (x) => expandLogNode(x, h.force), h.deep);
    // SymPy applies the hints in the order log, multinomial, mul, power_base, power_exp, trig
    // (without multinomial, SymPy's mul hint leaves integer powers of sums as they are)
    if (h.mul) e = h.deep ? (h.multinomial ? expandMul(e) : expandMulOnly(e)) : expandMulShallow(e, h.mul, h.multinomial);
    else if (h.multinomial) e = applyBottomUp(e, (x) => expandMulShallow(x, false, true), h.deep);
    if (h.power_base) e = applyBottomUp(e, (x) => powerBase(x, h.force), h.deep);
    if (h.power_exp) e = applyBottomUp(e, (x) => powerExp(x, h.force), h.deep);
    if (h.trig) e = applyBottomUp(e, expandTrigNode, h.deep);
    if (h.mul && e.key !== was.key) e = h.deep ? (h.multinomial ? expandMul(e) : expandMulOnly(e)) : expandMulShallow(e, h.mul, h.multinomial);
    if (e.key === was.key) break;
  }
  return e;
}

function expandMulShallow(e: Expr, doMul: boolean, doMulti: boolean): Expr {
  if (doMul && e instanceof Mul && e.args.some((a) => a instanceof Add)) {
    return e.args.reduce<Expr>((acc, f) => distribute(acc, f), Rational.of(1n));
  }
  if (doMulti && e instanceof Pow && e.base instanceof Add && e.exp instanceof Rational) return multinomialPow(e.base, e.exp) ?? e;
  return e;
}

/**
 * @internal SymPy expand_mul proper: distribute products over sums at every level, leaving
 * integer powers of sums such as (a + b)**2 unexpanded.
 */
export function expandMulOnly(e: Expr): Expr {
  let cur = e;
  for (;;) {
    const next = applyBottomUp(cur, (x) => expandMulShallow(x, true, false), true);
    if (next.key === cur.key) return next;
    cur = next;
  }
}

export const expand_mul = (e: ExprLike): Expr =>
  expand(e, { power_exp: false, power_base: false, log: false, multinomial: false });
export const expand_multinomial = (e: ExprLike): Expr =>
  expand(e, { power_exp: false, power_base: false, log: false, mul: false });
export const expand_power_exp = (e: ExprLike, force = false): Expr =>
  expand(e, { power_base: false, log: false, mul: false, multinomial: false, force });
export const expand_power_base = (e: ExprLike, opts: { force?: boolean; deep?: boolean } = {}): Expr =>
  expand(e, { power_exp: false, log: false, mul: false, multinomial: false, ...opts });
export const expand_log = (e: ExprLike, force = false): Expr =>
  expand(e, { power_exp: false, power_base: false, mul: false, multinomial: false, force });
export const expand_trig = (e: ExprLike): Expr =>
  expand(e, { power_exp: false, power_base: false, log: false, mul: false, multinomial: false, trig: true });
export const expand_complex = (e: ExprLike): Expr =>
  expand(e, { complex: true, power_exp: false, power_base: false, log: false, mul: false, multinomial: false });

impl.expand = (e) => expand(e);
impl.expandMul = (e) => expandMul(e);
impl.asRealImagExpand = (e) => asRealImagExpand(e);
