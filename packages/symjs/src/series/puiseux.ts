// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Truncated Puiseux series in a variable t about t = 0.
 *
 * A series is a finite set of terms c * t**e (e rational, c free of t) plus an
 * order bound: every term with exponent < order is exact. log(t) is kept as a
 * dummy symbol L in the coefficients, which is valid asymptotically because
 * log(t) grows slower than any power of t.
 */

import { NotImplementedError } from '../core/errors';
import type { Expr } from '../core/nodes';
import { Add, Constant, Fn, Mul, Pow, Rational, S, Special, Sym } from '../core/nodes';
import { numAdd, numCmp, numMul, numNeg } from '../core/num';
import { add, exp, mul, pow } from '../core/ops';
import { xreplace as subs } from '../core/traverse';
import { fn, log } from '../functions/elementary';
import { expandMul as expand } from '../simplify/expand';

/** A series that the expansion cannot compute (SymPy raises NotImplementedError or ValueError). */
export class SeriesError extends NotImplementedError {}

const INF = Rational.of(1000000n);

type Term = { e: Rational; c: Expr };

const minR = (a: Rational, b: Rational) => (numCmp(a, b) <= 0 ? a : b);

/** Is a coefficient zero? (exact check after expansion, numeric check for constants) */
export function isZeroCoeff(c: Expr): boolean {
  if (c instanceof Rational) return c.isZero;
  const x = expand(c);
  if (x instanceof Rational) return x.isZero;
  if (x.freeSymbols().size === 0) {
    try {
      const v = x.toComplex();
      return Math.hypot(v.re, v.im) < 1e-12;
    } catch {
      return false;
    }
  }
  return false;
}

export class PS {
  constructor(
    readonly terms: readonly Term[],
    /** all terms with exponent < order are exact */
    readonly order: Rational,
  ) {}

  static exact(terms: Term[]): PS {
    return new PS(normalize(terms, INF), INF);
  }
  static constant(c: Expr): PS {
    return PS.exact([{ e: S.Zero, c }]);
  }

  /** Lowest exponent with a nonzero coefficient, if determined within the order. */
  lead(): Term | undefined {
    for (const t of this.terms) if (!isZeroCoeff(t.c)) return t;
    return undefined;
  }

  leadExp(): Rational {
    return this.lead()?.e ?? this.order;
  }

  coeff(e: Rational): Expr {
    return this.terms.find((t) => t.e.key === e.key)?.c ?? S.Zero;
  }

  add(o: PS): PS {
    const order = minR(this.order, o.order);
    return new PS(normalize([...this.terms, ...o.terms], order), order);
  }

  scale(k: Expr): PS {
    return new PS(normalize(this.terms.map((t) => ({ e: t.e, c: mul(k, t.c) })), this.order), this.order);
  }

  shift(d: Rational): PS {
    const order = this.isExact ? this.order : (numAdd(this.order, d) as Rational);
    return new PS(this.terms.map((t) => ({ e: numAdd(t.e, d) as Rational, c: t.c })), order);
  }

  mul(o: PS): PS {
    const la = this.leadExp();
    const lb = o.leadExp();
    const order =
      this.isExact && o.isExact
        ? INF
        : minR(
            this.isExact ? INF : (numAdd(this.order, lb) as Rational),
            o.isExact ? INF : (numAdd(o.order, la) as Rational),
          );
    const out: Term[] = [];
    for (const a of this.terms) for (const b of o.terms) out.push({ e: numAdd(a.e, b.e) as Rational, c: mul(a.c, b.c) });
    return new PS(normalize(out, order), order);
  }

  get isExact(): boolean {
    return numCmp(this.order, Rational.of(100000n)) >= 0;
  }

  /** Force the order bound (used after truncating an infinite series). */
  cut(order: Rational): PS {
    const o = minR(order, this.order);
    return new PS(normalize([...this.terms], o), o);
  }

  /** Drop terms with exponent >= order; an exact series stays exact if nothing is dropped. */
  truncate(order: Rational): PS {
    if (this.isExact && this.terms.every((t) => numCmp(t.e, order) < 0)) return this;
    const o = minR(order, this.order);
    return new PS(normalize([...this.terms], o), o);
  }

  toExpr(t: Expr): Expr {
    return add(...this.terms.map((x) => mul(x.c, pow(t, x.e))));
  }
}

function normalize(terms: Term[], order: Rational): Term[] {
  const m = new Map<string, Term>();
  for (const t of terms) {
    if (numCmp(t.e, order) >= 0) continue;
    const cur = m.get(t.e.key);
    if (cur) cur.c = add(cur.c, t.c);
    else m.set(t.e.key, { e: t.e, c: t.c });
  }
  return [...m.values()].filter((t) => !(t.c instanceof Rational && t.c.isZero)).sort((a, b) => numCmp(a.e, b.e));
}

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';

/** Expansion of an expression in t (log(t) is replaced by the dummy L). */
export class Expander {
  readonly L = new Sym('_L');
  private depth = 0;

  constructor(readonly t: Sym) {}

  /** Series of e correct for all exponents < n. */
  ser(e: Expr, n: Rational): PS {
    if (++this.depth > 200) throw new SeriesError('recursion too deep');
    try {
      return this.serInner(e, n);
    } finally {
      this.depth--;
    }
  }

  private serInner(e: Expr, n: Rational): PS {
    const t = this.t;
    if (!e.has(t)) {
      if (e instanceof Special) throw new SeriesError('infinite coefficient');
      return PS.constant(e);
    }
    if (e.key === t.key) return PS.exact([{ e: S.One, c: S.One }]);
    if (e instanceof Add) return e.args.map((a) => this.ser(a, n)).reduce((a, b) => a.add(b));
    if (e instanceof Mul) return this.serMul(e.args, n);
    if (e instanceof Pow) {
      const [b, k] = e.args;
      if (isE(b)) return this.serExp(k, n);
      if (k.has(t)) return this.serExp(mul(k, log(b)), n);
      return this.serPow(b, k, n);
    }
    if (e instanceof Fn) return this.serFn(e, n);
    throw new SeriesError(`cannot expand ${e.toString()}`);
  }

  private serMul(factors: readonly Expr[], n: Rational): PS {
    // first pass for the leading exponents, second pass with enough precision
    const first = factors.map((f) => this.ser(f, n));
    const leads = first.map((s) => s.leadExp());
    const total = leads.reduce((a, b) => numAdd(a, b) as Rational, S.Zero);
    const parts = factors.map((f, i) => {
      const need = numAdd(n, numNeg(numAdd(total, numNeg(leads[i]!)))) as Rational;
      return numCmp(need, first[i]!.order) > 0 && numCmp(need, n) > 0 ? this.ser(f, need) : first[i]!;
    });
    return parts.reduce((a, b) => a.mul(b)).truncate(n);
  }

  /** b**k for constant k. */
  private serPow(b: Expr, k: Expr, n: Rational): PS {
    let sb = this.ser(b, n);
    let lead = sb.lead();
    if (!lead) {
      // try harder before giving up
      sb = this.ser(b, numAdd(n, Rational.of(6n)) as Rational);
      lead = sb.lead();
      if (!lead) throw new SeriesError('cannot determine leading term');
    }
    const e0 = lead.e;
    const c0 = lead.c;
    if (k instanceof Rational && k.isInteger && k.p >= 0n && k.p <= 16n) {
      // repeated multiplication with enough precision
      const need = numAdd(n, numMul(Rational.of(1n - k.p), e0)) as Rational;
      const s = numCmp(need, sb.order) > 0 ? this.ser(b, need) : sb;
      let r = PS.constant(S.One);
      for (let i = 0n; i < k.p; i++) r = r.mul(s);
      return r.truncate(n);
    }
    // b = c0 t^e0 (1 + u)
    const ke0 = mul(k, e0);
    if (!(ke0 instanceof Rational)) throw new SeriesError('non-rational exponent');
    const rel = numAdd(n, numNeg(ke0)) as Rational; // relative precision needed for (1+u)^k
    const need = numAdd(e0, rel) as Rational;
    const s = numCmp(need, sb.order) > 0 ? this.ser(b, need) : sb;
    const u = s.scale(pow(c0, -1)).shift(numNeg(e0) as Rational).add(PS.constant(S.NegOne)).truncate(rel);
    const d = u.lead()?.e;
    let acc = PS.constant(S.One);
    const infinite = !!(d?.isPositive);
    if (d?.isPositive) {
      let term = PS.constant(S.One);
      let binom: Expr = S.One;
      const J = Math.ceil(rel.value / d.value) + 1;
      for (let j = 1; j <= J; j++) {
        binom = mul(binom, add(k, -(j - 1)), Rational.of(1, j));
        term = term.mul(u).truncate(rel);
        acc = acc.add(term.scale(binom));
      }
    }
    const body = infinite || !u.isExact ? acc.cut(rel) : acc;
    return body.scale(pow(c0, k)).shift(ke0);
  }

  private serExp(g: Expr, n: Rational): PS {
    const sg = this.ser(g, n.isPositive ? n : S.One);
    for (const term of sg.terms) {
      if (term.e.isNegative && !isZeroCoeff(term.c)) throw new SeriesError('essential singularity');
    }
    const g0 = sg.coeff(S.Zero);
    const h = new PS(
      sg.terms.filter((x) => x.e.isPositive),
      sg.order,
    );
    return this.analytic((w) => exp(w), g0, h, n);
  }

  private serFn(e: Fn, n: Rational): PS {
    if (e.args.length > 1) {
      // several arguments: expand in the only one that depends on the variable
      const dep = e.args.map((a, i) => [a, i] as const).filter(([a]) => a.has(this.t));
      if (dep.length !== 1) throw new SeriesError(`cannot expand ${e.name}`);
      const [g, k] = dep[0]!;
      const sg = this.ser(g, n.isPositive ? n : S.One);
      for (const term of sg.terms) {
        if (term.e.isNegative && !isZeroCoeff(term.c)) throw new SeriesError('essential singularity');
      }
      const g0 = sg.coeff(S.Zero);
      const h = new PS(
        sg.terms.filter((x) => x.e.isPositive),
        sg.order,
      );
      return this.analytic((w) => fn(e.name, e.args.map((a, i) => (i === k ? w : a))), g0, h, n);
    }
    const g = e.args[0]!;
    if (e.name === 'log') {
      let sg = this.ser(g, n);
      let lead = sg.lead();
      if (!lead) {
        sg = this.ser(g, numAdd(n, Rational.of(6n)) as Rational);
        lead = sg.lead();
        if (!lead) throw new SeriesError('cannot determine leading term');
      }
      const s = numCmp(numAdd(n, lead.e), sg.order) > 0 ? this.ser(g, numAdd(n, lead.e) as Rational) : sg;
      const u = s.scale(pow(lead.c, -1)).shift(numNeg(lead.e) as Rational).add(PS.constant(S.NegOne));
      const head = PS.constant(add(log(lead.c), mul(lead.e, this.L)));
      return head.add(this.analytic((w) => log(add(1, w)), S.Zero, u, n));
    }
    const sg = this.ser(g, n.isPositive ? n : S.One);
    for (const term of sg.terms) {
      if (term.e.isNegative && !isZeroCoeff(term.c)) throw new SeriesError('essential singularity');
    }
    const g0 = sg.coeff(S.Zero);
    const h = new PS(
      sg.terms.filter((x) => x.e.isPositive),
      sg.order,
    );
    if (e.name === 'abs' || e.name === 're' || e.name === 'im' || e.name === 'arg' || e.name === 'conjugate') {
      if (h.terms.length === 0) return PS.constant(fn(e.name, [g0]));
      // abs(g) with g -> 0 along t -> 0+: the sign of the leading coefficient decides
      if (e.name === 'abs' && isZeroCoeff(g0)) {
        const lc = sg.lead()?.c;
        if (lc instanceof Rational) return lc.isNegative ? sg.scale(S.NegOne) : sg;
      }
      throw new SeriesError(`cannot expand ${e.name}`);
    }
    // gamma has poles at 0, -1, -2, ...: gamma(u) = gamma(u + 1)/u
    if (e.name === 'gamma' && g0 instanceof Rational && g0.isInteger && !g0.isPositive) {
      return this.ser(mul(fn('gamma', [add(g, 1)]), pow(g, -1)), n);
    }
    return this.analytic((w) => fn(e.name, [w]), g0, h, n);
  }

  /** f(g0 + h) = sum_j f^(j)(g0)/j! h^j, h with positive exponents only. */
  private analytic(f: (w: Expr) => Expr, g0: Expr, h: PS, n: Rational): PS {
    const w = new Sym('_w');
    let deriv = f(w);
    const value = (d: Expr) => {
      const v = expand(subs(d, [[w, g0]]));
      if (v instanceof Special || v.has(S.ComplexInfinity) || v.has(S.NaN)) throw new SeriesError('singular point');
      return v;
    };
    let acc = PS.constant(value(deriv));
    const d = h.lead()?.e;
    if (!n.isPositive) return acc;
    if (!d) return h.isExact ? acc : acc.cut(minR(n, h.order));
    const J = Math.ceil(n.value / d.value);
    let hp = PS.constant(S.One);
    let fact = 1n;
    for (let j = 1; j <= J; j++) {
      deriv = deriv.diff(w);
      fact *= BigInt(j);
      hp = hp.mul(h).truncate(n);
      const c = value(deriv);
      if (!(c instanceof Rational && c.isZero)) acc = acc.add(hp.scale(mul(c, Rational.of(1n, fact))));
    }
    return acc.cut(minR(n, h.order));
  }

  /** Leading term of e as t -> 0+, searching with increasing precision. */
  leading(e: Expr): Term {
    let n = Rational.of(1n);
    for (let i = 0; i < 6; i++) {
      const s = this.ser(e, n);
      const l = s.lead();
      if (l) return l;
      n = Rational.of(n.p * 2n + 2n);
    }
    throw new SeriesError('leading term not found');
  }
}

