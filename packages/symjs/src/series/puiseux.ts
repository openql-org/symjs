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
import type { Expr, FnName } from '../core/nodes';
import { Add, Constant, Fn, Mul, Pow, Rational, S, Special, Sym, UndefFn, isNum } from '../core/nodes';
import { numAdd, numCmp, numMul, numNeg } from '../core/num';
import { add, exp, mul, pow } from '../core/ops';
import { xreplace as subs } from '../core/traverse';
import { fn, log } from '../functions/elementary';
import { fnTaylorAtZero } from '../calculus/diff';
import { expandMul as expand } from '../simplify/expand';
import { first, last } from '../core/guard';
import { isNegative, isPositive, isReal } from '../core/assumptions';

/** A series that the expansion cannot compute (SymPy raises NotImplementedError or ValueError). */
export class SeriesError extends NotImplementedError {}

/** exp(g) with g -> oo along t -> 0+ (g has a term c*t**e, e < 0, with c not negative): no power series. */
export class EssentialSingularity extends SeriesError {
  constructor(readonly coeff: Expr) {
    super('essential singularity');
  }
}

const INF = Rational.of(1000000n);

type Term = { e: Rational; c: Expr };

const minR = (a: Rational, b: Rational) => (numCmp(a, b) <= 0 ? a : b);

/** Is a coefficient zero? (exact check after expansion, numeric check for constants) */
export function isZeroCoeff(c: Expr): boolean {
  if (c instanceof Rational) return c.isZero;
  // a product is zero when a factor is, a power b**k with k > 0 when b is (without expanding (x + 1)**1000)
  if (c instanceof Mul) return c.args.some(isZeroCoeff);
  if (c instanceof Pow && isPositive(c.exp)) return isZeroCoeff(c.base);
  // (a power with a negative exponent is not zero)
  if (c instanceof Pow && isNegative(c.exp)) return false;
  // a sum that is clearly nonzero at a sample point is not expanded
  if (c instanceof Add && clearlyNonzero(c)) return false;
  const x = expand(c);
  if (x instanceof Rational) return x.isZero;
  // a constant is evaluated; an expression with symbols is evaluated at two complex sample points
  // (1 - cos(a)**2 - sin(a)**2 does not expand to 0, a + 1 - sqrt((a + 1)**2) is 0 only for some a)
  const syms = [...x.freeSymbols()];
  const samples: [number, number][] = syms.length === 0 ? [[0, 0]] : [[0.6180339887, -1.3247179572], [-2.2055694304, 0.7548776662]];
  try {
    return samples.every(([re, im]) => {
      const val = subs(x, syms.map((y, j): [Expr, Expr] => [y, add(re + 0.1 * j, mul(im, S.I))])).toComplex();
      return Math.hypot(val.re, val.im) < 1e-12;
    });
  } catch {
    return false;
  }
}

/**
 * Does c*(1 + u) approach the negative real axis c < 0 from below (the side off the principal
 * branch of log and of fractional powers)? The first term of u with a non-real coefficient decides.
 */
function belowCut(u: PS): boolean {
  for (const t of u.terms) {
    if (t.c.freeSymbols().size !== 0) return false;
    let im: number;
    try {
      im = t.c.toComplex().im;
    } catch {
      return false;
    }
    if (im !== 0) return im > 0;
  }
  return false;
}

/** A constant with a zero imaginary part. */
function isRealConst(c: Expr): boolean {
  if (c.freeSymbols().size !== 0) return false;
  try {
    return c.toComplex().im === 0;
  } catch {
    return false;
  }
}

/** Is the sum numerically far from 0 (relative to its terms) at a sample point? */
function clearlyNonzero(c: Add): boolean {
  const syms = [...c.freeSymbols()];
  const point = syms.map((y, j): [Expr, Expr] => [y, add(0.6180339887 + 0.1 * j, mul(-1.3247179572, S.I))]);
  try {
    const vals = c.args.map((a) => subs(a, point).toComplex());
    const sum = vals.reduce((acc, v) => ({ re: acc.re + v.re, im: acc.im + v.im }), { re: 0, im: 0 });
    const scale = vals.reduce((acc, v) => acc + Math.hypot(v.re, v.im), 0);
    const m = Math.hypot(sum.re, sum.im);
    return Number.isFinite(scale) && m > 1e-8 * scale;
  } catch {
    return false;
  }
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
    const order = this.isExact ? this.order : numAdd(this.order, d);
    return new PS(this.terms.map((t) => ({ e: numAdd(t.e, d), c: t.c })), order);
  }

  mul(o: PS): PS {
    const la = this.leadExp();
    const lb = o.leadExp();
    const order =
      this.isExact && o.isExact
        ? INF
        : minR(
            this.isExact ? INF : numAdd(this.order, lb),
            o.isExact ? INF : numAdd(o.order, la),
          );
    const out: Term[] = [];
    for (const a of this.terms) for (const b of o.terms) out.push({ e: numAdd(a.e, b.e), c: mul(a.c, b.c) });
    return new PS(normalize(out, order), order);
  }

  /** The series without its terms below exponent e (known to be zero: those before the leading term). */
  from(e: Rational): PS {
    return new PS(this.terms.filter((t) => numCmp(t.e, e) >= 0), this.order);
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

/** Functions with poles written as quotients: name -> [numerator (undefined for 1), denominator]. */
const QUOTIENTS: Readonly<Partial<Record<string, readonly [FnName | undefined, FnName]>>> = {
  tan: ['sin', 'cos'],
  cot: ['cos', 'sin'],
  sec: [undefined, 'cos'],
  csc: [undefined, 'sin'],
  tanh: ['sinh', 'cosh'],
  coth: ['cosh', 'sinh'],
  sech: [undefined, 'cosh'],
  csch: [undefined, 'sinh'],
};

/** Taylor coefficient of LambertW at 0: (-j)**(j-1)/j!. */
function lambertWCoeff(j: number): Rational {
  if (j === 0) return S.Zero;
  let fact = 1n;
  for (let i = 2n; i <= BigInt(j); i++) fact *= i;
  return Rational.of(BigInt(-j) ** BigInt(j - 1), fact);
}

export const isE = (e: Expr): boolean => e instanceof Constant && e.name === 'E';

/** Expansion of an expression in t (log(t) is replaced by the dummy L). */
/** The sign of a real constant evaluated numerically (-log(2) < 0), 0 when it is not a real number. */
function numericSign(c: Expr): number {
  if (c.freeSymbols().size !== 0) return 0;
  try {
    const v = c.toComplex();
    return v.im === 0 ? Math.sign(v.re) : 0;
  } catch {
    return 0;
  }
}

/** The Gruntz helpers exp(-g)*besseli(nu, g) and exp(g)*besselk(nu, g) (SymPy _besseli, _besselk). */
export const SCALED_BESSELI = '_besseli';
export const SCALED_BESSELK = '_besselk';

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
    if (e instanceof UndefFn && (e.name === SCALED_BESSELI || e.name === SCALED_BESSELK)) return this.scaledBessel(e, n);
    throw new SeriesError(`cannot expand ${e.toString()}`);
  }

  private serMul(factors: readonly Expr[], n: Rational): PS {
    // first pass for the leading exponents, second pass with enough precision
    const firstPass = factors.map((f) => {
      const s = this.ser(f, n);
      return { f, s, lead: s.leadExp() };
    });
    const total = firstPass.reduce((a, { lead }) => numAdd(a, lead), S.Zero);
    const parts = firstPass.map(({ f, s, lead }) => {
      const need = numAdd(n, numNeg(numAdd(total, numNeg(lead))));
      return numCmp(need, s.order) > 0 && numCmp(need, n) > 0 ? this.ser(f, need) : s;
    });
    return parts.reduce((a, b) => a.mul(b)).truncate(n);
  }

  /** b**k for constant k. */
  private serPow(b: Expr, k: Expr, n: Rational): PS {
    let sb = this.ser(b, n);
    let lead = sb.lead();
    if (!lead) {
      // try harder before giving up
      sb = this.ser(b, numAdd(n, Rational.of(6n)));
      lead = sb.lead();
      if (!lead) throw new SeriesError('cannot determine leading term');
    }
    const e0 = lead.e;
    const c0 = lead.c;
    if (k instanceof Rational && k.isInteger && k.p >= 0n && k.p <= 16n) {
      // repeated multiplication with enough precision
      const need = numAdd(n, numMul(Rational.of(1n - k.p), e0));
      const s = numCmp(need, sb.order) > 0 ? this.ser(b, need) : sb;
      let r = PS.constant(S.One);
      for (let i = 0n; i < k.p; i++) r = r.mul(s.from(e0));
      return r.truncate(n);
    }
    // b = c0 t^e0 (1 + u)
    const ke0 = mul(k, e0);
    if (!(ke0 instanceof Rational)) throw new SeriesError('non-rational exponent');
    const rel = numAdd(n, numNeg(ke0)); // relative precision needed for (1+u)^k
    const need = numAdd(e0, rel);
    const s = numCmp(need, sb.order) > 0 ? this.ser(b, need) : sb;
    // (the terms before the leading one have coefficients that are zero but not written as 0: 1 - cos(a)**2 - sin(a)**2)
    const u = s.from(e0).scale(pow(c0, -1)).shift(numNeg(e0)).add(PS.constant(S.NegOne)).truncate(rel);
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
    // below the cut of a negative base the power is that of the other branch: c0**k*exp(-2*I*pi*k)
    const c0k = this.belowCutOf(b, c0, e0, u) ? mul(pow(c0, k), pow(S.NegOne, mul(-2, k))) : pow(c0, k);
    return body.scale(c0k).shift(ke0);
  }

  private serExp(g: Expr, n: Rational): PS {
    const sg = this.ser(g, n.isPositive ? n : S.One);
    const poles = sg.terms.filter((term) => term.e.isNegative && !isZeroCoeff(term.c));
    if (poles.length > 0) {
      // (the terms are in increasing order of the exponent: the first is the leading one)
      const pole = first(poles);
      // g -> -oo: exp(g) is smaller than every power of t (SymPy exp._eval_nseries gives O(x**n))
      if (isNegative(pole.c) === true || numericSign(pole.c) < 0) return new PS([], n);
      throw new EssentialSingularity(pole.c);
    }
    const g0 = sg.coeff(S.Zero);
    const h = new PS(
      sg.terms.filter((x) => x.e.isPositive),
      sg.order,
    );
    return this.analytic((w) => exp(w), g0, h, n);
  }

  private serFn(e: Fn, n: Rational): PS {
    const asym = this.asymptotic(e, n);
    if (asym !== undefined) return asym;
    if (e.args.length > 1) {
      // several arguments: expand in the only one that depends on the variable
      const dep = e.args.map((a, i) => [a, i] as const).filter(([a]) => a.has(this.t));
      if (dep.length !== 1) throw new SeriesError(`cannot expand ${e.name}`);
      const [g, k] = first(dep);
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
    const g = first(e.args);
    if (e.name === 'log') {
      let sg = this.ser(g, n);
      let lead = sg.lead();
      if (!lead) {
        sg = this.ser(g, numAdd(n, Rational.of(6n)));
        lead = sg.lead();
        if (!lead) throw new SeriesError('cannot determine leading term');
      }
      const s = numCmp(numAdd(n, lead.e), sg.order) > 0 ? this.ser(g, numAdd(n, lead.e)) : sg;
      const u = s.from(lead.e).scale(pow(lead.c, -1)).shift(numNeg(lead.e)).add(PS.constant(S.NegOne));
      // below the cut of a negative argument: log(c) - 2*I*pi
      const lc = this.belowCutOf(g, lead.c, lead.e, u) ? add(log(lead.c), mul(-2, S.Pi, S.I)) : log(lead.c);
      const head = PS.constant(add(lc, mul(lead.e, this.L)));
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
    if (e.name === 'abs' || e.name === 're' || e.name === 'im' || e.name === 'arg' || e.name === 'conjugate' || e.name === 'sign') {
      if (h.terms.length === 0) return PS.constant(fn(e.name, [g0]));
      // sign(c*t**e*(1 + o(1))) tends to sign(c); away from 0 a real argument keeps its sign
      if (e.name === 'sign') {
        if (!isZeroCoeff(g0)) {
          if (isReal(g0) === true) return PS.constant(fn('sign', [g0]));
        } else {
          const lc = sg.lead()?.c;
          if (lc !== undefined) return PS.constant(fn('sign', [lc]));
        }
      }
      // abs(g) with g -> 0 along t -> 0+: the sign of the leading coefficient decides
      if (e.name === 'abs' && isZeroCoeff(g0)) {
        const lc = sg.lead()?.c;
        if (lc instanceof Rational) return lc.isNegative ? sg.scale(S.NegOne) : sg;
      }
      throw new SeriesError(`cannot expand ${e.name}`);
    }
    // floor and ceiling are locally constant: at an integer the side is that of the leading term
    if (e.name === 'floor' || e.name === 'ceiling') {
      const lc = h.lead()?.c;
      if (lc === undefined) return PS.constant(fn(e.name, [g0]));
      const sign = isPositive(lc) ? 1 : isNegative(lc) ? -1 : 0;
      if (!(g0 instanceof Rational && g0.isInteger)) {
        // off the integers floor/ceiling is constant. A symbolic g0 could be an integer: floor is
        // continuous from the right and ceiling from the left, so floor(g0) and ceiling(g0) are the
        // values on those sides (SymPy floor._eval_nseries). On the other side SymPy also gives
        // floor(y) for floor(y - x) and ceiling(y) for ceiling(y + x), which is wrong for an integer y.
        const r = fn(e.name, [g0]);
        if (r instanceof Rational || (e.name === 'floor' ? sign > 0 : sign < 0)) return PS.constant(r);
        throw new SeriesError(`cannot expand ${e.name}`);
      }
      if (sign === 0) throw new SeriesError(`cannot expand ${e.name}`);
      const up = e.name === 'floor' ? (sign > 0 ? 0 : -1) : sign > 0 ? 1 : 0;
      return PS.constant(add(g0, up));
    }
    // Ei(g) = EulerGamma + log(g) + sum_k g**k/(k*k!) for g -> 0, with log(-g) on the negative real axis,
    // where Ei is real (SymPy Ei._eval_nseries: series(Ei(-x), x) = EulerGamma + log(x) - x + ...,
    // series(Ei(I*x), x) = I*pi/2 + EulerGamma + log(x) + I*x + ...)
    if (e.name === 'Ei' && isZeroCoeff(g0)) {
      const lc = this.leading(g).c;
      const side = isNegative(lc) === true || numericSign(lc) < 0 ? -1 : 1;
      let fact = 1n;
      const sum = this.powerSeries((k) => {
        if (k === 0) return S.Zero;
        fact *= BigInt(k);
        return Rational.of(1n, BigInt(k) * fact);
      }, h, n);
      return PS.constant(S.EulerGamma).add(this.ser(log(mul(side, g)), n)).add(sum);
    }
    // frac(g) = g - floor(g): h plus frac(g0), or plus 1 below an integer (SymPy: series(frac(x), x) = x)
    if (e.name === 'frac') {
      const lc = h.lead()?.c;
      const sign = lc === undefined ? 0 : isPositive(lc) ? 1 : isNegative(lc) ? -1 : 0;
      if (g0 instanceof Rational && g0.isInteger) {
        if (sign === 0) throw new SeriesError('cannot expand frac');
        return sign > 0 ? h : PS.constant(S.One).add(h);
      }
      // (a symbolic g0 could be an integer: frac is continuous from the right; SymPy also gives
      // frac(y) - x for frac(y - x), which is wrong for an integer y)
      const f0 = fn('frac', [g0]);
      if (f0 instanceof Rational || sign > 0) return PS.constant(f0).add(h);
      throw new SeriesError('cannot expand frac');
    }
    // acoth, asech and acsch at 0 (a branch point on their cut): the value on the side of approach,
    // given by the sign of the real leading coefficient of the argument (SymPy _eval_nseries)
    if ((e.name === 'acoth' || e.name === 'asech' || e.name === 'acsch') && isZeroCoeff(g0)) {
      const lc = this.leading(g).c;
      const side = isNum(lc) ? (lc.isPositive ? 1 : -1) : 0;
      if (side === 0) throw new SeriesError(`cannot expand ${e.name}`);
      const ipi = mul(S.I, S.Pi);
      if (e.name === 'acoth') return this.ser(add(fn('atanh', [g]), mul(-side, S.Half, ipi)), n);
      const sq = pow(add(1, mul(e.name === 'asech' ? -1 : 1, pow(g, 2))), S.Half);
      const main = add(log(add(1, sq)), mul(-1, log(mul(side, g))));
      // asech(g) = log(2) - log(-g) + I*pi for g < 0; acsch is odd
      if (e.name === 'asech') return this.ser(side > 0 ? main : add(main, ipi), n);
      return this.ser(side > 0 ? main : mul(-1, main), n);
    }
    // gamma has poles at 0, -1, -2, ...: gamma(u) = gamma(u + 1)/u
    if (e.name === 'gamma' && g0 instanceof Rational && g0.isInteger && !g0.isPositive) {
      return this.ser(mul(fn('gamma', [add(g, 1)]), pow(g, -1)), n);
    }
    // at a pole of a reciprocal or quotient function (cot(0), sec(pi/2)): expand the quotient
    const quot = QUOTIENTS[e.name];
    if (quot !== undefined && fn(e.name, [g0]).key === S.ComplexInfinity.key) {
      const [num, den] = quot;
      return this.ser(mul(num === undefined ? S.One : fn(num, [g]), pow(fn(den, [g]), -1)), n);
    }
    // acosh has infinite derivatives at its branch points 1 and -1: acosh(g) = log(g + sqrt(g - 1)*sqrt(g + 1))
    if (e.name === 'acosh' && g0 instanceof Rational && g0.q === 1n && (g0.p === 1n || g0.p === -1n)) {
      return this.ser(log(add(g, mul(pow(add(g, -1), S.Half), pow(add(g, 1), S.Half)))), n);
    }
    // the derivatives of LambertW at 0 are 0/0 forms: W(h) = sum_{j>=1} (-j)**(j-1)/j! h**j
    if (e.name === 'LambertW' && g0 instanceof Rational && g0.isZero) return this.powerSeries(lambertWCoeff, h, n);
    const taylor = fnTaylorAtZero[e.name];
    if (taylor && g0 instanceof Rational && g0.isZero) return this.powerSeries(taylor, h, n);
    return this.analytic((w) => fn(e.name, [w]), g0, h, n);
  }

  /**
   * Stirling's series of loggamma(g) and the asymptotic series of polygamma(0, g) for an argument
   * g -> +oo (SymPy loggamma._eval_aseries, polygamma._eval_aseries); undefined for other functions.
   */
  private asymptotic(e: Fn, n: Rational): PS | undefined {
    const digamma = e.name === 'polygamma' && e.args.length === 2 && e.args[0] instanceof Rational && e.args[0].isZero;
    if (!(e.name === 'loggamma' || digamma)) return undefined;
    // (the argument depends on t: the first argument of polygamma is 0)
    const g = last(e.args);
    const lead = this.leading(g);
    if (!(lead.e.isNegative && isPositive(lead.c))) return undefined;
    const d = -lead.e.value;
    // terms up to z**(1 - 2K) (loggamma) or z**(-2K) (digamma); the rest is O(z**(-2K - 1))
    const K = Math.max(1, Math.ceil((Math.max(n.value, 1) / d - 1) / 2) + 1);
    const terms: Expr[] = digamma ? [log(g), mul(Rational.of(-1n, 2n), pow(g, -1))] : [mul(add(g, Rational.of(-1n, 2n)), log(g)), mul(-1, g), mul(S.Half, log(mul(2, S.Pi)))];
    for (let k = 1; k <= K; k++) {
      const b = fn('bernoulli', [Rational.of(2 * k)]);
      terms.push(digamma ? mul(-1, b, pow(mul(2 * k, pow(g, 2 * k)), -1)) : mul(b, pow(mul(2 * k * (2 * k - 1), pow(g, 2 * k - 1)), -1)));
    }
    return this.ser(add(...terms), n).cut(Rational.of(BigInt(Math.round((2 * K + 1) * d * 1000)), 1000n));
  }

  /**
   * The asymptotic series of exp(-g)*besseli(nu, g) and exp(g)*besselk(nu, g) (the helpers of the
   * Gruntz algorithm, SymPy _besseli and _besselk) for g -> +oo: (2*pi*g)**(-1/2) and (pi/(2*g))**(1/2)
   * times sum_k (+-1)**k*a_k(nu)/g**k, a_k(nu) = (4*nu**2 - 1)*...*(4*nu**2 - (2*k - 1)**2)/(k!*8**k)
   * (Abramowitz and Stegun 9.7.1 and 9.7.2).
   */
  private scaledBessel(e: UndefFn, n: Rational): PS {
    const [nu, g] = [first(e.args), last(e.args)];
    const lead = this.leading(g);
    if (!(lead.e.isNegative && isPositive(lead.c))) throw new SeriesError(`cannot expand ${e.name}`);
    const d = -lead.e.value;
    // terms up to g**(-K); the rest is O(g**(-K - 3/2))
    const K = Math.max(1, Math.ceil(Math.max(n.value, 1) / d));
    const besseli = e.name === SCALED_BESSELI;
    const terms: Expr[] = [];
    let c: Expr = S.One;
    for (let k = 0; k <= K; k++) {
      if (k > 0) {
        // (-1)**k*a_k(nu) = rf(1/2 - nu, k)*rf(1/2 + nu, k)/(k!*2**k)
        const j = Rational.of(2 * k - 1, 2);
        c = mul(c, add(j, mul(-1, nu)), add(j, nu), Rational.of(besseli ? 1n : -1n, BigInt(2 * k)));
      }
      terms.push(mul(c, pow(g, -k)));
    }
    const front = besseli ? pow(mul(2, S.Pi, g), Rational.of(-1n, 2n)) : pow(mul(S.Pi, pow(mul(2, g), -1)), S.Half);
    return this.ser(mul(front, add(...terms)), n).cut(Rational.of(BigInt(Math.round((2 * K + 3) * d * 1000)), 2000n));
  }

  /** belowCut for b = c*t**e*(1 + u), with more terms of u when those known do not decide it. */
  private belowCutOf(b: Expr, c: Expr, e: Rational, u: PS): boolean {
    if (!(isNum(c) && c.isNegative)) return false;
    if (belowCut(u) || u.terms.some((t) => !isRealConst(t.c))) return belowCut(u);
    const more = this.ser(b, numAdd(e, Rational.of(4n)));
    return belowCut(more.from(e).scale(pow(c, -1)).shift(numNeg(e)).add(PS.constant(S.NegOne)));
  }

  /** f(g0 + h) = sum_j f^(j)(g0)/j! h^j, h with positive exponents only. */
  private analytic(f: (w: Expr) => Expr, g0: Expr, h: PS, n: Rational): PS {
    const w = new Sym('_w');
    let deriv = f(w);
    let fact = 1n;
    const value = (d: Expr) => {
      const v = expand(subs(d, [[w, g0]]));
      if (v instanceof Special || v.has(S.ComplexInfinity) || v.has(S.NaN)) throw new SeriesError('singular point');
      return v;
    };
    return this.powerSeries((j) => {
      if (j === 0) return value(deriv);
      deriv = deriv.diff(w);
      fact *= BigInt(j);
      return mul(value(deriv), Rational.of(1n, fact));
    }, h, n);
  }

  /** sum_j coeff(j) h^j, h with positive exponents only; coeff is called for j = 0, 1, 2, ... in order. */
  private powerSeries(coeff: (j: number) => Expr, h: PS, n: Rational): PS {
    let acc = PS.constant(coeff(0));
    const d = h.lead()?.e;
    if (!n.isPositive) return acc;
    if (!d) return h.isExact ? acc : acc.cut(minR(n, h.order));
    const J = Math.ceil(n.value / d.value);
    let hp = PS.constant(S.One);
    for (let j = 1; j <= J; j++) {
      hp = hp.mul(h).truncate(n);
      const c = coeff(j);
      if (!(c instanceof Rational && c.isZero)) acc = acc.add(hp.scale(c));
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

