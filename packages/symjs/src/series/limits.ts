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
import { Expander } from './puiseux';
import { first, getOrThrow } from '../core/guard';

const BOUNDED = Symbol('bounded');
/** Undetermined, and no other method should be tried (a branch cut crossed at infinity). */
const STOP = Symbol('stop');
type LV = Expr | typeof BOUNDED | undefined;
/** A determined limit value (neither undetermined nor merely bounded). */
const isValue = (v: LV): v is Expr => v !== undefined && v !== BOUNDED;

const isInf = (e: LV): e is Special => e instanceof Special && e.name !== 'nan';
const isNaN_ = (e: LV) => e instanceof Special && e.name === 'nan';
const isZeroE = (e: LV) => e instanceof Rational && e.isZero;
/** Numerically zero (for sample values of its symbols) without being 0 symbolically. */
const nearlyZero = (e: Expr): boolean => {
  if (e instanceof Rational) return false;
  const syms = [...impl.freeSymbols(e)];
  const samples = [0.6180339887, 1.3247179572];
  try {
    return samples.every((v, i) => {
      const val = subs(e, syms.map((x, j) => [x, (v + 0.1 * j) * (i + 1)] as [Expr, number])).toComplex();
      return Math.hypot(val.re, val.im) < 1e-12;
    });
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
const hasSpecialInside = (e: Expr): boolean => e.args.some((a) => a instanceof Special || hasSpecialInside(a));

class Limiter {
  private depth = 0;
  private readonly t = new Sym('_t', { positive: true });

  constructor(
    private readonly z: Sym,
    private readonly z0: Expr,
    private readonly dir: '+' | '-',
  ) {}

  /** Numeric sign of e near the limit point (undefined if unknown or non-real). */
  private probeSign(e: Expr): number | undefined {
    const z0 = this.z0;
    let point: number;
    if (z0 instanceof Special) {
      if (z0.name === 'oo') point = 1e7;
      else if (z0.name === '-oo') point = -1e7;
      else return undefined;
    } else {
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
      const v = subs(e, [[this.z, point]]).toComplex();
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
      if (!Number.isFinite(d1) || !Number.isFinite(d2)) return true;
      return d2 <= 1e-6 * scale || d2 < 0.9 * d1;
    } catch {
      return true;
    }
  }

  /** Sign of e (tending to 0) near the point: from its leading term, else numerically. */
  private sideOf(e: Expr): number | undefined {
    if (e instanceof Rational) return e.isZero ? 0 : e.isPositive ? 1 : -1;
    const { z, z0, t } = this;
    let point: Expr | undefined;
    if (z0 instanceof Special) point = z0.name === 'oo' ? pow(t, -1) : z0.name === '-oo' ? mul(-1, pow(t, -1)) : undefined;
    else point = this.dir === '+' ? add(z0, t) : add(z0, mul(-1, t));
    if (point !== undefined) {
      try {
        const c = new Expander(t).leading(subs(e, [[z, point]])).c;
        if (isNum(c)) return c.isPositive ? 1 : -1;
        if (isPositive(c)) return 1;
        if (isNegative(c)) return -1;
      } catch {
        // no expansion: decide numerically
      }
    }
    return this.probeSign(e);
  }

  lim(f: Expr): LV {
    if (++this.depth > 60) {
      this.depth--;
      return undefined;
    }
    try {
      const r = this.structural(f);
      if (r === STOP) return undefined;
      if (r !== undefined && !isNaN_(r)) return r;
      // the expansions do not see branch cuts: check the value on the side of approach
      const v = this.fallback(f);
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
        const infs = vals.filter(isInf);
        return infs.length ? add(...infs) : BOUNDED;
      }
      const r = add(...vals.filter(isValue));
      if (isFinite_(r) || isInf(r) || isDirectedInf(r)) return r;
      // oo plus real finite terms is oo; anything else with an infinite part (oo - sqrt(c + oo)) is undetermined
      const infs = r.args.filter(isInf);
      const [inf] = infs;
      if (r instanceof Add && infs.length === 1 && inf !== undefined && (inf.name === 'oo' || inf.name === '-oo')) {
        const rest = r.args.filter((a) => a !== inf);
        if (rest.every((a) => isFinite_(a) && isReal(a) === true)) return inf;
        if (rest.every(isFinite_)) return r;
      }
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
      const p = mul(...vals.filter(isValue));
      // c*oo with a real constant c (log(3)*oo, ...) is a signed infinity
      if (p instanceof Mul) {
        const infs = p.args.filter((a): a is Special => a instanceof Special);
        const [inf] = infs;
        if (infs.length === 1 && inf !== undefined && (inf.name === 'oo' || inf.name === '-oo')) {
          const c = mul(...p.args.filter((a) => a !== inf));
          if (impl.freeSymbols(c).size === 0 && !hasSpecialInside(c)) {
            const r = this.infinity(inf.name === 'oo' ? c : mul(-1, c));
            if (r instanceof Special) return r;
          }
        }
      }
      return p;
    }

    if (f instanceof Pow) {
      const [b, h] = f.args;
      const lb = this.lim(b);
      const lh = h.has(z) ? this.lim(h) : h;
      if (lb === undefined || lh === undefined || lb === BOUNDED || lh === BOUNDED) return undefined;
      const expLog = () => {
        const v = this.lim(mul(h, log(b)));
        return v === undefined || v === BOUNDED ? undefined : exp(v);
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
      if (isNegative(lh) && isFinite_(lb) && nearlyZero(lb)) return undefined;
      if (lb instanceof Rational && lb.isOne && isInf(lh)) return expLog();
      if (isInf(lb) && isZeroE(lh)) return expLog();
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
      if (!isFinite_(la)) return STOP;
      if (f.name === 'log' && isZeroE(la)) {
        return this.probeSign(arg) === 1 ? S.NegativeInfinity : undefined;
      }
      // floor, ceiling and sign jump at integers (at 0): the side of approach decides
      if ((f.name === 'floor' || f.name === 'ceiling') && la instanceof Rational && la.isInteger) {
        const side = this.sideOf(add(arg, mul(-1, la)));
        if (side === undefined) return undefined;
        if (side === 0) return la;
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
    if (f instanceof Mul && f.args.filter((a) => a instanceof Pow && a.base.key === S.E.key && a.exp.has(this.z)).length > 1) {
      const g = powsimp(f, { combine: 'exp' });
      if (g.key !== f.key) return this.lim(g);
    }
    return this.bySeries(f) ?? this.byLHopital(f);
  }

  /** Leading term of the expansion at the limit point. */
  private bySeries(f: Expr): LV {
    const { z, z0, t } = this;
    let point: Expr;
    if (z0 instanceof Special) {
      if (z0.name === 'oo') point = pow(t, -1);
      else if (z0.name === '-oo') point = mul(-1, pow(t, -1));
      else return undefined;
    } else point = this.dir === '+' ? add(z0, t) : add(z0, mul(-1, t));
    const ex = new Expander(t);
    let lead;
    try {
      lead = ex.leading(subs(f, [[z, point]]));
    } catch {
      return undefined;
    }
    const { e, c } = lead;
    if (c.has(t)) return undefined;
    // coefficient may contain the dummy L = log(t) -> -oo
    const pc = polyCoefficients(c, ex.L);
    if (!pc) return undefined;
    const m = Math.max(...pc.keys());
    const a = expand(getOrThrow(pc, m));
    if (e.isPositive) return S.Zero;
    if (e.isZero && m === 0) return c;
    const sign = m % 2 === 0 ? a : mul(-1, a);
    return this.infinity(sign);
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
    return mul(a, S.Infinity);
  }

  private byLHopital(f: Expr): LV {
    if (this.depth > 30) return undefined;
    let N: Expr | undefined;
    let D: Expr | undefined;
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
        if (infs.some((a) => a.has(S.E)) || (zeros.some(zExp) && infs.every(algebraic))) {
          N = mul(...infs);
          D = pow(mul(...zeros), -1);
        } else {
          N = mul(...zeros);
          D = pow(mul(...infs), -1);
        }
        const rest = others.length ? this.lim(mul(...others)) : S.One;
        const q = this.lhopital(N, D);
        if (rest === undefined || rest === BOUNDED || q === undefined || q === BOUNDED) return undefined;
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
      const indeterminate = (isZeroE(ln) && isZeroE(ld)) || (isInf(ln) && isInf(ld));
      if (!indeterminate) {
        if (ln === undefined || ld === undefined || ln === BOUNDED || ld === BOUNDED) return undefined;
        const r = mul(ln, pow(ld, -1));
        if (r instanceof Special && (r.name === 'oo' || r.name === '-oo')) return r;
        if (isInf(ln) && !isInf(ld)) {
          const s = this.probeSign(mul(N, pow(D, -1)));
          return s === 1 ? S.Infinity : s === -1 ? S.NegativeInfinity : undefined;
        }
        if (r instanceof Special && r.name === 'zoo') {
          const s = this.probeSign(mul(N, pow(D, -1)));
          return s === 1 ? S.Infinity : s === -1 ? S.NegativeInfinity : undefined;
        }
        return isNaN_(r) ? undefined : r;
      }
      N = diff(N, this.z);
      D = diff(D, this.z);
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
  const e = sympify(ex);
  const z0 = sympify(z0x);
  if (dir === '+-' && !(z0 instanceof Special)) {
    const l = limit(e, z, z0, '-');
    const r = limit(e, z, z0, '+');
    if (l.key !== r.key) {
      if (l instanceof Special && r instanceof Special && l.name !== 'nan' && r.name !== 'nan') return S.ComplexInfinity;
      throw new RangeError(
        `The limit does not exist since left hand limit = ${l.toString()} and right hand limit = ${r.toString()}`,
      );
    }
    return r;
  }
  const d = dir === '-' ? '-' : '+';
  const v = new Limiter(z, z0, d).lim(e);
  if (v === undefined || v === BOUNDED) {
    const g = z0 instanceof Special && z0.name === 'oo' ? gammaAsymptotic(e, z) : undefined;
    if (g !== undefined) {
      const w = new Limiter(z, z0, d).lim(g);
      if (w !== undefined && w !== BOUNDED) return w;
    }
    return new Limit([e, z, z0], dir);
  }
  // oo plus finite (possibly complex) terms: SymPy gives oo (limit(x**2 - I, x, oo) = oo)
  if (v instanceof Add && isInfiniteSum(v)) {
    const infs = v.args.filter(isInf);
    const [inf] = infs;
    if (infs.length === 1 && inf !== undefined && (inf.name === 'oo' || inf.name === '-oo') && v.args.every((a) => a === inf || isFinite_(a))) return inf;
  }
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
