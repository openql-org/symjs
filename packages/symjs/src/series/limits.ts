// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Limits.
 *
 * Strategy:
 * 1. structural: combine the limits of the parts with extended arithmetic
 *    (exp(-oo) = 0, bounded * 0 = 0, ...)
 * 2. series: the leading term of the Puiseux expansion decides 0/0, oo - oo
 *    and 1**oo forms (sin(x)/x, sqrt(x**2 + x) - x, (1 + 1/x)**x, ...)
 * 3. L'Hopital's rule for forms involving divergent exponentials
 * An unevaluated `Limit` is returned when all strategies fail.
 */

import { toGamma } from '../simplify/gammasimp';
import { powsimp } from '../simplify/powsimp';
import { isNegative, isPositive, isReal } from '../core/assumptions';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Float, Fn, Limit, Mul, Pow, Rational, S, Special, Sym, impl, isNum } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { mapBottomUp, xreplace as subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { fn, log } from '../functions/elementary';
import { polyCoefficients } from '../polys/poly';
import { expandMul as expand } from '../simplify/expand';
import { fraction, together } from '../simplify/rational';
import { Expander, isZeroCoeff } from './puiseux';
import { first, getOrThrow } from '../core/guard';
import { NotImplementedError } from '../core/errors';

const BOUNDED = Symbol('bounded');
/** Undetermined, and no other method should be tried (a branch cut crossed at infinity). */
const STOP = Symbol('stop');
type LV = Expr | typeof BOUNDED | undefined;
/** A determined limit value (neither undetermined nor merely bounded). */
const isValue = (v: LV): v is Expr => v !== undefined && v !== BOUNDED;

const isInf = (e: LV): e is Special => e instanceof Special && e.name !== 'nan';
const isNaN_ = (e: LV) => e instanceof Special && e.name === 'nan';
const isZeroE = (e: LV) => e instanceof Rational && e.isZero;
/** Functions whose exact values at large integers are huge. */
const COMBINATORIAL = new Set(['factorial', 'factorial2', 'subfactorial', 'gamma', 'binomial', 'rf', 'ff', 'fibonacci', 'lucas', 'catalan', 'bell', 'harmonic']);
/** A constant of modulus 1 ((-1)**(1/3), I). */
const isUnit = (e: Expr): boolean => {
  if (impl.freeSymbols(e).size !== 0) return false;
  try {
    const v = e.toComplex();
    return Math.abs(Math.hypot(v.re, v.im) - 1) < 1e-14;
  } catch {
    return false;
  }
};
const hasPolygamma = (e: Expr): boolean => (e instanceof Fn && e.name === 'polygamma') || e.args.some(hasPolygamma);
/** A finite value: no special values (oo, zoo, nan) inside. */
const isFinite_ = (e: Expr): boolean => !(e instanceof Special || hasSpecialInside(e));
/** c*oo with a finite constant c. */
const isDirectedInf = (e: Expr): boolean => e instanceof Mul && e.args.filter(isInf).length === 1 && e.args.every((a) => isInf(a) || isFinite_(a));
/** A sum of directed infinities and finite terms (oo - I, oo + oo*I, ...): its modulus is infinite. */
const isInfiniteSum = (e: Expr): boolean =>
  e instanceof Add && e.args.some((a) => isInf(a) || isDirectedInf(a)) && e.args.every((a) => isInf(a) || isDirectedInf(a) || isFinite_(a));
/** A finite value without the terms that expand to 0 (0 if the whole expands to 0). */
const dropZeros = (e: Expr): Expr => {
  if (isZeroE(expand(e))) return S.Zero;
  return e instanceof Add ? add(...e.args.filter((a) => !isZeroE(expand(a)))) : e;
};
/** The infinite term of a sum with one (oo - I -> oo). */
const infinitePart = (e: Expr): Expr => first(e.args.filter((a) => isInf(a) || isDirectedInf(a)));
const hasSpecialInside = (e: Expr): boolean => e.args.some((a) => a instanceof Special || hasSpecialInside(a));

/** Most nested limit computations one limit may spend (the recursion of L'Hopital's rule can grow exponentially). */
const BUDGET = 1000;

class Limiter {
  private depth = 0;
  private calls = 0;
  private readonly t = new Sym('_t', { positive: true });

  constructor(
    private readonly z: Sym,
    private readonly z0: Expr,
    private readonly dir: '+' | '-',
    private readonly budget: number,
  ) {}

  /** Numeric sign of e near the limit point (undefined if unknown or non-real). */
  private probeSign(e: Expr): number | undefined {
    const z0 = this.z0;
    let point: number;
    // the only special points left are oo and -oo (limit() answers nan and rejects zoo)
    if (z0 instanceof Special) point = z0.name === 'oo' ? 1e7 : -1e7;
    else {
      try {
        const v = z0.toComplex();
        if (v.im !== 0) return undefined;
        const h = 1e-7 * Math.max(1, Math.abs(v.re));
        point = this.dir === '+' ? v.re + h : v.re - h;
      } catch {
        return undefined;
      }
    }
    try {
      // a number to a power in z and the combinatorial functions are evaluated in floating point
      // ((2/3)**(z + 1) or factorial(z) exactly at z = 10**7 is huge); other functions are cheaper
      // at an integer (Ei at a Float of 10**7 is not)
      const exact = (g: Expr): boolean =>
        (g instanceof Pow && isNum(g.base) && g.exp.has(this.z)) || (g instanceof Fn && COMBINATORIAL.has(g.name)) || g.args.some(exact);
      const v = subs(e, [[this.z, exact(e) ? new Float(point) : point]]).toComplex();
      if (Number.isNaN(v.re) || Number.isNaN(v.im)) return undefined;
      if (Number.isFinite(v.re) && Math.abs(v.im) > 1e-9 * Math.max(1, Math.abs(v.re))) return undefined;
      return Math.sign(v.re);
    } catch {
      if (isPositive(e)) return 1;
      if (isNegative(e)) return -1;
      return undefined;
    }
  }

  /**
   * Is the candidate value r the limit of f numerically (near the point, on the
   * side of approach)? A function of z alone whose value jumps (a branch cut, a
   * pole hidden in an unevaluated argument) fails the check.
   */
  private continuous(f: Expr, r: Expr): boolean {
    if (impl.freeSymbols(f).size !== 1 || impl.freeSymbols(r).size !== 0) return true;
    // exponentials of z (exp(1/x) near 0) are too costly to evaluate in arbitrary precision; they have no cut
    const zExp = (e: Expr): boolean => (e instanceof Pow && e.exp.has(this.z)) || e.args.some(zExp);
    if (zExp(f)) return true;
    // branch cuts are crossed at finite points only, by functions that have one
    if (this.z0 instanceof Special) return true;
    const CUT = new Set(['log', 'asin', 'acos', 'atan', 'acot', 'asec', 'acsc', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch']);
    const branchy = (e: Expr): boolean =>
      (e instanceof Fn && CUT.has(e.name) && e.has(this.z)) ||
      (e instanceof Pow && e.base.has(this.z) && !(e.exp instanceof Rational && e.exp.isInteger)) ||
      e.args.some(branchy);
    if (!branchy(f)) return true;
    try {
      const v = this.z0.toComplex();
      if (v.im !== 0) return true;
      const b = r.toComplex();
      if (!Number.isFinite(b.re) || !Number.isFinite(b.im)) return true;
      // the distance to r must shrink as the point comes closer (a jump across a cut does not)
      const dist = (h: number): number => {
        const a = subs(f, [[this.z, new Float(this.dir === '+' ? v.re + h : v.re - h, 200)]]).toComplex();
        return Math.hypot(a.re - b.re, a.im - b.im);
      };
      const scale = Math.max(1, Math.hypot(b.re, b.im));
      const d1 = dist(1e-6 * Math.max(1, Math.abs(v.re)));
      const d2 = dist(1e-9 * Math.max(1, Math.abs(v.re)));
      // (a distance that is not finite near the point fails the check)
      return d2 <= 1e-6 * scale || d2 < 0.9 * d1;
    } catch {
      return true;
    }
  }

  /** The point in terms of the expansion variable t -> 0+ (z0 + t, z0 - t, 1/t or -1/t). */
  private point(): Expr {
    const { z0, t } = this;
    if (z0 instanceof Special) return z0.name === 'oo' ? pow(t, -1) : mul(-1, pow(t, -1));
    return this.dir === '+' ? add(z0, t) : add(z0, mul(-1, t));
  }

  /** Sign of e (tending to 0) near the point: from its leading term, else numerically. */
  private sideOf(e: Expr): number | undefined {
    try {
      const c = new Expander(this.t).leading(subs(e, [[this.z, this.point()]])).c;
      if (isNum(c)) return c.isPositive ? 1 : -1;
      if (isPositive(c)) return 1;
      if (isNegative(c)) return -1;
    } catch {
      // no expansion: decide numerically
    }
    // a sample that is exactly 0 (sin(pi*z)/z at z = 10**7) says nothing about the side
    const s = this.probeSign(e);
    return s === 0 ? undefined : s;
  }

  lim(f: Expr): LV {
    if (++this.calls > this.budget) return undefined;
    if (++this.depth > 60) {
      this.depth--;
      return undefined;
    }
    try {
      const r = this.structural(f);
      if (r === STOP) return undefined;
      if (r !== undefined && r !== BOUNDED && !isNaN_(r)) return r;
      // the expansions do not see branch cuts: check the value on the side of approach
      const v = this.fallback(f);
      // a bounded value may still have a limit (x**(I*x)*(x + 1)**(-I*x) -> exp(-I))
      if (r === BOUNDED && !isValue(v)) return BOUNDED;
      return isValue(v) && !this.continuous(f, v) ? undefined : v;
    } finally {
      this.depth--;
    }
  }

  /** structural, with STOP read as undetermined. */
  private settled(f: Expr): LV {
    const r = this.structural(f);
    return r === STOP ? undefined : r;
  }

  private structural(f: Expr): LV | typeof STOP {
    const z = this.z;
    if (!f.has(z)) return f;
    if (f.key === z.key) return this.z0;

    if (f instanceof Add) {
      const vals = f.args.map((a) => this.lim(a));
      if (vals.some((v) => v === undefined)) return undefined;
      if (vals.some((v) => v === BOUNDED)) {
        const infs = vals.filter((v): v is Expr => isInf(v) || (isValue(v) && isDirectedInf(v)));
        return infs.length ? add(...infs) : BOUNDED;
      }
      // a sum that expands to 0 (a + a**2 - a*(a + 1)) is 0: a quotient with it is a 0/0 form
      const r = add(...vals.filter(isValue));
      // infinities that cancel (oo*I - oo*I) are an indeterminate form
      if (isFinite_(r)) return vals.some((v) => isValue(v) && !isFinite_(v)) ? undefined : dropZeros(r);
      if (isInf(r) || isDirectedInf(r)) return r;
      // an infinity (oo, -oo, c*oo) plus real finite terms is that infinity, plus other finite terms it is kept
      // (oo - I); anything else with an infinite part (oo - sqrt(c + oo)) is undetermined
      const infs = r.args.filter((a) => isInf(a) || isDirectedInf(a));
      const [inf] = infs;
      const rest = r.args.filter((a) => a !== inf);
      if (r instanceof Add && infs.length === 1 && inf !== undefined && rest.every(isFinite_)) return rest.every((a) => isReal(a) === true) ? inf : r;
      return undefined;
    }

    if (f instanceof Mul) {
      const vals = f.args.map((a) => this.lim(a));
      if (vals.some((v) => v === undefined)) return undefined;
      if (vals.some((v) => v === BOUNDED)) {
        const others = vals.filter((v): v is Expr => v !== BOUNDED);
        if (others.some(isInf)) return undefined;
        const p = mul(...others);
        return isZeroE(p) ? S.Zero : BOUNDED;
      }
      // 0 times an infinite part is undetermined (mul would give 0 for a symbolic coefficient of oo)
      if (vals.some(isZeroE) && vals.some((v) => isValue(v) && !isFinite_(v))) return undefined;
      // an infinite sum (oo + I) is its infinite term in a product
      const p = mul(...vals.filter(isValue).map((v) => (v instanceof Add && isInfiniteSum(v) ? infinitePart(v) : v)));
      // c*oo with a constant c (log(3)*oo, I*pi*oo, ...) is a signed or directed infinity; the factors
      // other than oo are finite (a product keeps -oo as -1*oo, and zoo absorbs the others)
      if (p instanceof Mul) {
        const infs = p.args.filter((a): a is Special => a instanceof Special);
        const [inf] = infs;
        if (infs.length === 1 && inf?.name === 'oo') return this.infinity(mul(...p.args.filter((a) => a !== inf)));
      }
      return p;
    }

    if (f instanceof Pow) {
      const [b, h] = f.args;
      const lb = this.lim(b);
      const lh = h.has(z) ? this.lim(h) : h;
      // a bounded base to a constant positive power is bounded (sin(z)**2 at oo)
      if (lb === BOUNDED && !h.has(z) && isPositive(h)) return BOUNDED;
      if (lb === undefined || lh === undefined || lb === BOUNDED || lh === BOUNDED) return undefined;
      const expLog = (): LV => {
        const v = this.lim(mul(h, log(b)));
        if (v === undefined || v === BOUNDED) return undefined;
        return isDirectedInf(v) ? this.expInf(v, S.E) : exp(v);
      };
      if (isZeroE(lb)) {
        if (isZeroE(lh)) return expLog();
        const neg = isNegative(lh);
        if (neg) {
          const s = this.probeSign(b);
          if (lh instanceof Rational && lh.isInteger && lh.p % 2n === 0n) return S.Infinity;
          if (s === 1) return S.Infinity;
          if (s === -1 && lh instanceof Rational && lh.isInteger) return S.NegativeInfinity;
          return undefined;
        }
        if (isPositive(lh)) return S.Zero;
        return undefined;
      }
      // a sum of directed infinities (oo + oo*I, ...) has infinite modulus
      if (isInfiniteSum(lb) && lh instanceof Rational && lh.isNegative) return S.Zero;
      if (!isFinite_(lb) && !isInf(lb) && !isDirectedInf(lb)) return undefined;
      // a base tending to 0 that is not written as 0 (1 - cos(a)**2 - sin(a)**2): undetermined here
      if (isNegative(lh) && isFinite_(lb) && isZeroCoeff(lb)) return undefined;
      if (lb instanceof Rational && lb.isOne && isInf(lh)) return expLog();
      if (isInf(lb) && isZeroE(lh)) return expLog();
      // an infinite base off the positive axis to the power oo: the modulus grows, the direction turns (SymPy: zoo)
      if (isInf(lh) && lh.name === 'oo' && (isDirectedInf(lb) || (isInf(lb) && lb.name !== 'oo'))) return S.ComplexInfinity;
      // a constant base to an infinite power (a positive one to c*oo, another one to oo or -oo)
      if (isFinite_(lb) && ((isDirectedInf(lh) && isPositive(lb) === true) || (isInf(lh) && lh.name !== 'zoo' && isPositive(lb) !== true))) {
        return this.expInf(lh, lb);
      }
      const r = pow(lb, lh);
      if (isNaN_(r)) return expLog();
      // a fractional power on its branch cut (sqrt(-1 + I*x) from below)
      return lh instanceof Rational && !lh.isInteger && !this.continuous(f, r) ? undefined : r;
    }

    if (f instanceof Fn && f.args.length > 1) {
      const ls = f.args.map((a) => this.lim(a));
      const vs = ls.filter(isValue);
      if (vs.length !== ls.length) return undefined;
      const r = fn(f.name, vs);
      if (hasSpecialInside(r) || isNaN_(r)) return undefined;
      return r;
    }

    if (f instanceof Fn) {
      const arg = first(f.args);
      // |b**e| = |b|**e for a real exponent (z runs along the real axis): |(-x/(x + 1))**x| -> exp(-1)
      if (f.name === 'abs' && arg instanceof Pow && arg.exp.has(z) && !arg.exp.has(S.I) && impl.freeSymbols(arg.exp).size === 1) {
        return this.lim(pow(fn('abs', [arg.base]), arg.exp));
      }
      const la = this.lim(arg);
      if (la === undefined || la === BOUNDED) return undefined;
      if (la instanceof Special) {
        if ((f.name === 'sin' || f.name === 'cos') && la.name !== 'zoo') return BOUNDED;
        if (la.name === 'zoo') return undefined;
        const r = fn(f.name, [la]);
        if (r instanceof Fn || hasSpecialInside(r) || isNaN_(r)) return undefined;
        return r;
      }
      // an argument tending to oo - I (or another sum with an infinite part): the side decides
      // (log(-x - I) -> oo - I*pi), which the expansions do not see
      // log(w) with |w| -> oo is oo plus a bounded imaginary part, which SymPy drops (log(-x - I) -> oo)
      if (!isFinite_(la)) return f.name === 'log' ? S.Infinity : STOP;
      if (f.name === 'log' && isZeroE(la)) {
        return this.probeSign(arg) === 1 ? S.NegativeInfinity : undefined;
      }
      // floor, ceiling and sign jump at integers (at 0): the side of approach decides
      if ((f.name === 'floor' || f.name === 'ceiling') && la instanceof Rational && la.isInteger) {
        const side = this.sideOf(add(arg, mul(-1, la)));
        if (side === undefined) return undefined;
        return f.name === 'floor' ? (side > 0 ? la : add(la, -1)) : side > 0 ? add(la, 1) : la;
      }
      if (f.name === 'sign' && isZeroE(la)) {
        const side = this.sideOf(arg);
        return side === undefined ? undefined : Rational.of(side);
      }
      const r = fn(f.name, [la]);
      if (r instanceof Special && r.name === 'zoo') {
        const s = this.probeSign(f);
        return s === 1 ? S.Infinity : s === -1 ? S.NegativeInfinity : undefined;
      }
      // on a branch cut (log(-1 + I*x) from below, asin(2 + I*x), ...) the value is that of the side
      return this.continuous(f, r) ? r : undefined;
    }
    return undefined;
  }

  private fallback(f: Expr): LV {
    // explicit infinities (-oo + 1/x, (1 + x)**oo) are not expanded or differentiated
    if (hasSpecialInside(f)) return undefined;
    // exponentials combine first: exp(1/sin(x))*exp(-cot(x)) = exp(1/sin(x) - cot(x))
    // (powsimp always merges two powers of E into one)
    if (f instanceof Mul && f.args.filter((a) => a instanceof Pow && a.base.key === S.E.key && a.exp.has(this.z)).length > 1) {
      return this.lim(powsimp(f, { combine: 'exp' }));
    }
    // a product with powers of z to exponents in z (k**k*(k + 1)**(-k)) is the exponential of the sum
    // of the logarithms of its factors when the bases and the other factors are positive near the point
    const zPow = (a: Expr): a is Pow => a instanceof Pow && a.base.has(this.z) && a.exp.has(this.z);
    if (f instanceof Mul && f.args.some(zPow) && f.args.every((a) => this.probeSign(a instanceof Pow ? a.base : a) === 1)) {
      const v = this.lim(add(...f.args.map((a) => (a instanceof Pow ? mul(a.exp, log(a.base)) : log(a)))));
      if (isValue(v)) return isDirectedInf(v) ? this.expInf(v, S.E) : exp(v);
    }
    return this.bySeries(f) ?? this.byLHopital(f);
  }

  /** Leading term of the expansion at the limit point. */
  private bySeries(f: Expr): LV {
    const ex = new Expander(this.t);
    let lead;
    try {
      lead = ex.leading(subs(f, [[this.z, this.point()]]));
    } catch {
      return undefined;
    }
    // the coefficient is free of t; it may contain the dummy L = log(t) -> -oo
    const { e, c } = lead;
    const pc = polyCoefficients(c, ex.L);
    if (!pc) return undefined;
    const m = Math.max(...pc.keys());
    const a = expand(getOrThrow(pc, m));
    if (e.isPositive) return S.Zero;
    if (e.isZero && m === 0) return dropZeros(c);
    const sign = m % 2 === 0 ? a : mul(-1, a);
    return this.infinity(sign);
  }

  /**
   * Limit of b**v for a constant b and an infinite v (oo, -oo or c*oo): by the real part of
   * v*log(b) it is 0, oo (or zoo off the real axis), or bounded (|b**v| = 1).
   */
  private expInf(v: Expr, b: Expr): LV {
    // (a product keeps -oo as -1*oo, and zoo absorbs constant factors: a zoo times symbols leaves symbols in c)
    const coeff = v instanceof Special ? (v.name === 'oo' ? S.One : S.NegOne) : mul(...v.args.filter((a) => !isInf(a)));
    const c = mul(coeff, log(b));
    if (impl.freeSymbols(c).size !== 0) return undefined;
    const cv = c.toComplex();
    if (cv.re < 0) return S.Zero;
    if (cv.re > 0) return cv.im === 0 ? S.Infinity : S.ComplexInfinity;
    return BOUNDED;
  }

  private infinity(a: Expr): Expr {
    if (isNum(a)) return a.isPositive ? S.Infinity : S.NegativeInfinity;
    if (isPositive(a)) return S.Infinity;
    if (isNegative(a)) return S.NegativeInfinity;
    if (impl.freeSymbols(a).size === 0) {
      try {
        const v = a.toComplex();
        if (Math.abs(v.im) < 1e-12) return v.re > 0 ? S.Infinity : S.NegativeInfinity;
      } catch {
        // fall through
      }
    }
    // otherwise the sign of the coefficient is the direction (SymPy: limit(a*x, x, oo) = oo*sign(a));
    // positive factors do not change it (I*pi*oo = oo*I), and a constant of modulus 1 is its own sign
    const u = a instanceof Mul ? mul(...a.args.filter((f) => !isPositive(f))) : a;
    return mul(isUnit(u) ? u : fn('sign', [u]), S.Infinity);
  }

  private byLHopital(f: Expr): LV {
    if (this.depth > 30) return undefined;
    if (f instanceof Mul) {
      const zeros: Expr[] = [];
      const infs: Expr[] = [];
      const others: Expr[] = [];
      for (const a of f.args) {
        const v = this.settled(a);
        if (isZeroE(v)) zeros.push(a);
        else if (isInf(v)) infs.push(a);
        else others.push(a);
      }
      if (zeros.length && infs.length) {
        // a decaying c**g (g depending on z) goes in the denominator of algebraic divergent factors
        const zExp = (a: Expr): boolean => (a instanceof Pow && a.exp.has(this.z) && !a.base.has(this.z)) || a.args.some(zExp);
        const algebraic = (a: Expr): boolean => !(a instanceof Fn) && !zExp(a) && a.args.every(algebraic);
        const infOverZero = (): LV => this.lhopital(mul(...infs), pow(mul(...zeros), -1));
        const zeroOverInf = (): LV => this.lhopital(mul(...zeros), pow(mul(...infs), -1));
        // the other quotient when the preferred one does not resolve (exp(-x)*Ei(x): Ei(x)/exp(x))
        const q =
          infs.some((a) => a.has(S.E)) || (zeros.some(zExp) && infs.every(algebraic))
            ? infOverZero() ?? zeroOverInf()
            : zeroOverInf() ?? infOverZero();
        const rest = others.length ? this.lim(mul(...others)) : S.One;
        if (rest === undefined || rest === BOUNDED || q === undefined || q === BOUNDED) return undefined;
        // a signed infinity times a finite factor: the sign of the factor is the direction
        if (q instanceof Special && isFinite_(rest)) return this.infinity(q.name === 'oo' ? rest : mul(-1, rest));
        return mul(rest, q);
      }
    }
    if (f instanceof Add) {
      const g = together(f);
      if (g.key !== f.key) return this.lim(g);
    }
    const [n, d] = fraction(f);
    if (!(d instanceof Rational)) return this.lhopital(n, d);
    return undefined;
  }

  private lhopital(N0: Expr, D0: Expr): LV {
    let N = N0;
    let D = D0;
    for (let i = 0; i < 12; i++) {
      const ln = this.settled(N);
      const ld = this.settled(D);
      const infinite = (v: LV): boolean => isInf(v) || (isValue(v) && isDirectedInf(v));
      const indeterminate = (isZeroE(ln) && isZeroE(ld)) || (infinite(ln) && infinite(ld));
      if (!indeterminate) {
        if (ln === undefined || ld === undefined || ln === BOUNDED || ld === BOUNDED) return undefined;
        const r = mul(ln, pow(ld, -1));
        if (isInf(r)) {
          if (r.name !== 'zoo') return r;
          // c/0: the sign of the quotient near the point decides
          const s = this.probeSign(mul(N, pow(D, -1)));
          return s === 1 ? S.Infinity : s === -1 ? S.NegativeInfinity : undefined;
        }
        // oo/c with a symbolic or nonreal c: the sign of 1/c is the direction
        if (isInf(ln)) return this.infinity(mul(ln.name === 'oo' ? 1 : -1, pow(ld, -1)));
        // (not nan: 0/0 and oo/oo are the indeterminate forms, and structural values are never nan)
        return r;
      }
      // (abs of a non-real argument has no derivative here: no limit by this rule)
      try {
        N = diff(N, this.z);
        D = diff(D, this.z);
      } catch {
        return undefined;
      }
      // derivatives of gamma functions (polygamma) never resolve the form and only grow
      if (hasPolygamma(N) || hasPolygamma(D)) return undefined;
      // simplify the quotient when possible
      const q = mul(N, pow(D, -1));
      const [qn, qd] = fraction(q);
      N = qn;
      D = qd;
    }
    return undefined;
  }
}

/**
 * Limit of e as z -> z0. dir is '+' (default, like SymPy), '-' or '+-'
 * (two-sided; throws if the one-sided limits differ). Returns an unevaluated
 * `Limit` when the limit cannot be determined.
 */
export function limit(ex: ExprLike, z: Sym, z0x: ExprLike, dir: '+' | '-' | '+-' = '+'): Expr {
  return limitWithin(ex, z, z0x, dir, BUDGET);
}

/** limit() with at most `budget` nested limit computations per one-sided limit (internal; for tests). */
export function limitWithin(ex: ExprLike, z: Sym, z0x: ExprLike, dir: '+' | '-' | '+-', budget: number): Expr {
  const e = sympify(ex);
  const z0 = sympify(z0x);
  if (dir === '+-' && !(z0 instanceof Special)) {
    const l = limitWithin(e, z, z0, '-', budget);
    const r = limitWithin(e, z, z0, '+', budget);
    // neither one-sided limit is known: the two-sided one is not either
    if (l instanceof Limit && r instanceof Limit) return new Limit([e, z, z0], dir);
    if (l.key !== r.key) {
      if (l instanceof Special && r instanceof Special && l.name !== 'nan' && r.name !== 'nan') return S.ComplexInfinity;
      throw new RangeError(
        `The limit does not exist since left hand limit = ${l.toString()} and right hand limit = ${r.toString()}`,
      );
    }
    return r;
  }
  if (z0 instanceof Special && z0.name === 'zoo') throw new NotImplementedError('Limits at complex infinity are not implemented');
  if (e.key === z.key) return z0;
  if (!e.has(z)) return e;
  if (z0 instanceof Special && z0.name === 'nan') return S.NaN;
  // a directed infinity c*oo: the limit of e(c*z/|c|) as z -> oo (SymPy)
  if (isDirectedInf(z0)) {
    // (a product keeps -oo as -1*oo, so the infinity in it is oo)
    const c = mul(...z0.args.filter((a) => !isInf(a)));
    const v = limitWithin(subs(e, [[z, mul(c, pow(fn('abs', [c]), -1), z)]]), z, S.Infinity, '+', budget);
    return v instanceof Limit ? new Limit([e, z, z0], dir) : v;
  }
  const d = dir === '-' ? '-' : '+';
  const v = new Limiter(z, z0, d, budget).lim(e);
  if (v === undefined || v === BOUNDED) {
    const g = z0 instanceof Special && z0.name === 'oo' ? gammaAsymptotic(e, z) : undefined;
    if (g !== undefined) {
      const w = new Limiter(z, z0, d, budget).lim(g);
      if (w !== undefined && w !== BOUNDED) return w;
    }
    // SymPy's Limit approaches oo from below and -oo from above
    return new Limit([e, z, z0], z0 instanceof Special ? (z0.name === 'oo' ? '-' : '+') : dir);
  }
  // an infinity plus finite (possibly complex) terms: SymPy gives the infinity (limit(x**2 - I, x, oo) = oo);
  // the structural sums keep a single infinite term
  if (v instanceof Add && isInfiniteSum(v)) return infinitePart(v);
  return v;
}

/**
 * Factorials, binomials and rising/falling factorials at infinity: written
 * with Gamma, each Gamma(n + c) is replaced by Gamma(n)*n**c (the leading
 * asymptotic behaviour); the result when the Gamma(n) factors cancel.
 */
function gammaAsymptotic(e: Expr, n: Sym): Expr | undefined {
  const isGammaLike = (x: Expr): boolean => (x instanceof Fn && ['gamma', 'factorial', 'binomial', 'rf', 'ff'].includes(x.name) && x.has(n)) || x.args.some(isGammaLike);
  if (!isGammaLike(e)) return undefined;
  const g = toGamma(e);
  let failed = false as boolean; // set inside a callback
  const out = mapBottomUp(g, (x: Expr) => {
    if (!(x instanceof Fn && x.name === 'gamma') || !x.has(n)) return x;
    const c = expand(add(first(x.args), mul(-1, n)));
    if (c.has(n)) {
      failed = true;
      return x;
    }
    return mul(fn('gamma', [n]), pow(n, c));
  });
  if (failed) return undefined;
  const r = powsimp(out);
  return r.has(fn('gamma', [n])) ? undefined : r;
}

impl.limit = limit;
