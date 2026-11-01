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

import { isNegative, isPositive } from '../core/assumptions';
import { Add, Expr, ExprLike, Fn, Limit, Mul, Pow, Rational, S, Special, Sym, impl, isNum } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { xreplace as subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { fn, log } from '../functions/elementary';
import { polyCoefficients } from '../polys/poly';
import { expandMul as expand } from '../simplify/expand';
import { fraction, together } from '../simplify/rational';
import { Expander } from './puiseux';

const BOUNDED = Symbol('bounded');
type LV = Expr | typeof BOUNDED | undefined;

const isInf = (e: LV): e is Special => e instanceof Special && e.name !== 'nan';
const isNaN_ = (e: LV) => e instanceof Special && e.name === 'nan';
const isZeroE = (e: LV) => e instanceof Rational && e.isZero;
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

  lim(f: Expr): LV {
    if (++this.depth > 60) {
      this.depth--;
      return undefined;
    }
    try {
      const r = this.structural(f);
      if (r === undefined || isNaN_(r)) return this.fallback(f);
      return r;
    } finally {
      this.depth--;
    }
  }

  private structural(f: Expr): LV {
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
      return add(...(vals as Expr[]));
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
      return mul(...(vals as Expr[]));
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
      if (lb instanceof Rational && lb.isOne && isInf(lh)) return expLog();
      if (isInf(lb) && isZeroE(lh)) return expLog();
      const r = pow(lb, lh);
      return isNaN_(r) ? expLog() : r;
    }

    if (f instanceof Fn && f.args.length > 1) {
      const ls = f.args.map((a) => this.lim(a));
      if (ls.some((v) => v === undefined || v === BOUNDED)) return undefined;
      const r = fn(f.name, ls as Expr[]);
      if (hasSpecialInside(r) || isNaN_(r)) return undefined;
      return r;
    }

    if (f instanceof Fn) {
      const arg = f.args[0]!;
      const la = this.lim(arg);
      if (la === undefined || la === BOUNDED) return undefined;
      if (la instanceof Special) {
        if ((f.name === 'sin' || f.name === 'cos') && la.name !== 'zoo') return BOUNDED;
        if (la.name === 'zoo') return undefined;
        const r = fn(f.name, [la]);
        if (r instanceof Fn || hasSpecialInside(r) || isNaN_(r)) return undefined;
        return r;
      }
      if (f.name === 'log' && isZeroE(la)) {
        return this.probeSign(arg) === 1 ? S.NegativeInfinity : undefined;
      }
      const r = fn(f.name, [la]);
      if (r instanceof Special && r.name === 'zoo') {
        const s = this.probeSign(f);
        return s === 1 ? S.Infinity : s === -1 ? S.NegativeInfinity : undefined;
      }
      return r;
    }
    return undefined;
  }

  private fallback(f: Expr): LV {
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
    const a = expand(pc.get(m)!);
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
        const v = this.structural(a);
        if (isZeroE(v)) zeros.push(a);
        else if (isInf(v)) infs.push(a);
        else others.push(a);
      }
      if (zeros.length && infs.length) {
        const hasExp = infs.some((a) => a.has(S.E));
        if (hasExp) {
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
      const ln = this.structural(N);
      const ld = this.structural(D);
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
      throw new Error(
        `The limit does not exist since left hand limit = ${l.toString()} and right hand limit = ${r.toString()}`,
      );
    }
    return r;
  }
  const d = dir === '-' ? '-' : '+';
  const v = new Limiter(z, z0, d).lim(e);
  if (v === undefined || v === BOUNDED) return new Limit([e, z, z0], dir);
  return v;
}

impl.limit = limit;
