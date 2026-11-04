// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sympy/series/gruntz.py (BSD 3-Clause, see LICENSE).

/**
 * @file The Gruntz algorithm for limits at infinity.
 *
 * The most rapidly varying subexpressions (the mrv set) of an expression are
 * found, rewritten in terms of one of them, w -> 0+, and the leading term of
 * the expansion in w decides the limit; a leading coefficient that still
 * depends on x is handled recursively (D. Gruntz, "On Computing Limits in a
 * Symbolic Manipulation System", 1996).
 */

import { isNegative, isPositive } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, first, last } from '../core/guard';
import type { Expr, Sym } from '../core/nodes';
import { Add, Constant, Dummy, Fn, Mul, Pow, Rational, S, Special, UndefFn, impl } from '../core/nodes';
import { add, exp, mul, pow } from '../core/ops';
import { mapBottomUp, xreplace } from '../core/traverse';
import { fn, log } from '../functions/elementary';
import { powdenest, powsimp } from '../simplify/powsimp';
import { together } from '../simplify/rational';
import { expand, expandMul } from '../simplify/expand';
import { coeff } from '../core/methods';
import { Expander, SCALED_BESSELI, SCALED_BESSELK, isZeroCoeff } from './puiseux';

/** Functions whose expansion at an infinite argument is known (or that the expansion rejects). */
const TAME = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch', 'asin', 'acos', 'atan', 'acot', 'asec', 'acsc', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch', 'loggamma', 'polygamma', 'abs', 're', 'im', 'arg']);

/** Functions continuous at 0. */
const AT_ZERO = new Set(['sin', 'cos', 'tan', 'sinh', 'cosh', 'tanh', 'asin', 'acos', 'atan', 'asinh', 'atanh', 'erf', 'erfc']);

/** The algorithm cannot decide the limit (SymPy raises PoleError, ValueError or NotImplementedError). */
export class GruntzError extends NotImplementedError {}
/** The sign of an mrv element's exponent is not known: SymPy raises NotImplementedError from limit(). */
export class SignUnknownError extends GruntzError {}

const isExp = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
/** A power that is not exp(...). */
const isPlainPow = (e: Expr): e is Pow => e instanceof Pow && !isExp(e);

/** A map from mrv subexpressions to dummies, with the rewrites of the exponentials (SymPy SubsSet). */
class SubsSet {
  /** expression key -> [expression, dummy] */
  readonly items = new Map<string, [Expr, Dummy]>();
  /** dummy key -> its exponential written with the dummies of its argument */
  readonly rewrites = new Map<string, Expr>();

  get size(): number {
    return this.items.size;
  }

  /** Add e with a new dummy (the sets are built from single elements by union). */
  add(e: Expr): Dummy {
    const d = new Dummy();
    this.items.set(e.key, [e, d]);
    return d;
  }

  has(e: Expr): boolean {
    return this.items.has(e.key);
  }

  /** e with the dummies replaced by their expressions. */
  doSubs(e: Expr): Expr {
    let r = e;
    for (const [expr, v] of this.items.values()) r = xreplace(r, [[v, expr]]);
    return r;
  }

  meets(o: SubsSet): boolean {
    for (const k of this.items.keys()) if (o.items.has(k)) return true;
    return false;
  }

  /** The union, and exps with the dummies of o that are also in this set replaced by ours. */
  union(o: SubsSet, expsIn: Expr): [SubsSet, Expr] {
    const res = this.copy();
    let exps = expsIn;
    const tr: [Expr, Expr][] = [];
    for (const [k, [expr, v]] of o.items) {
      const mine = res.items.get(k);
      if (mine) {
        exps = xreplace(exps, [[v, mine[1]]]);
        tr.push([v, mine[1]]);
      } else res.items.set(k, [expr, v]);
    }
    for (const [v, rw] of o.rewrites) res.rewrites.set(v, xreplace(rw, tr));
    return [res, exps];
  }

  copy(): SubsSet {
    const r = new SubsSet();
    for (const [k, v] of this.items) r.items.set(k, v);
    for (const [k, v] of this.rewrites) r.rewrites.set(k, v);
    return r;
  }
}

/** Limits at infinity by the Gruntz algorithm; one instance per limit (it bounds the work). */
export class Gruntz {
  private calls = 0;
  private readonly limits = new Map<string, Expr>();

  constructor(private readonly budget = 3000) {}

  private tick(): void {
    if (++this.calls > this.budget) throw new GruntzError('too many steps');
  }

  /** Compare the growth of two mrv candidates: '<', '>' or '='. */
  private compare(a: Expr, b: Expr, x: Sym): '<' | '>' | '=' {
    const la = isExp(a) ? a.exp : log(a);
    const lb = isExp(b) ? b.exp : log(b);
    const c = this.limitinf(mul(la, pow(lb, -1)), x);
    if (c instanceof Rational && c.isZero) return '<';
    if (isInfinite(c)) return '>';
    return '=';
  }

  private mrvMax3(f: SubsSet, expsf: Expr, g: SubsSet, expsg: Expr, union: SubsSet, expsboth: Expr, x: Sym): [SubsSet, Expr] {
    // (both sets are nonempty: their expressions depend on x)
    if (f.meets(g)) return [union, expsboth];
    const c = this.compare(first([...f.items.values()])[0], first([...g.items.values()])[0], x);
    if (c === '>') return [f, expsf];
    if (c === '<') return [g, expsg];
    return [union, expsboth];
  }

  private mrvMax1(f: SubsSet, g: SubsSet, exps: Expr, x: Sym): [SubsSet, Expr] {
    const [u, b] = f.union(g, exps);
    return this.mrvMax3(f, g.doSubs(exps), g, f.doSubs(exps), u, b, x);
  }

  /** The mrv set of e and e with its elements replaced by their dummies. */
  mrv(eIn: Expr, x: Sym): [SubsSet, Expr] {
    this.tick();
    const e = powsimp(eIn, { deep: true, combine: 'exp' });
    if (!e.has(x)) return [new SubsSet(), e];
    if (e.key === x.key) {
      const s = new SubsSet();
      return [s, s.add(x)];
    }
    if (e instanceof Mul || e instanceof Add) {
      const indep = e.args.filter((a) => !a.has(x));
      const dep = e.args.filter((a) => a.has(x));
      const op = e instanceof Mul ? mul : add;
      const i = op(...indep);
      if (dep.length === 1) {
        const [s, expr] = this.mrv(first(dep), x);
        return [s, op(i, expr)];
      }
      const [s1, e1] = this.mrv(first(dep), x);
      const [s2, e2] = this.mrv(op(...dep.slice(1)), x);
      return this.mrvMax1(s1, s2, op(i, e1, e2), x);
    }
    if (isPlainPow(e)) {
      let b: Expr = e;
      let k: Expr = S.One;
      while (isPlainPow(b)) {
        k = mul(k, b.exp);
        b = b.base;
      }
      if (k.has(x)) return this.mrv(exp(mul(k, log(b))), x);
      const [s, expr] = this.mrv(b, x);
      return [s, pow(expr, k)];
    }
    if (isExp(e)) {
      const arg = e.exp;
      const li = this.limitinf(arg, x);
      const factors = li instanceof Mul ? li.args : [li];
      if (factors.some(isInfinite)) {
        const s1 = new SubsSet();
        const e1 = s1.add(e);
        const [s2, e2] = this.mrv(arg, x);
        const [su] = s1.union(s2, S.Zero);
        su.rewrites.set(e1.key, exp(e2));
        return this.mrvMax3(s1, e1, s2, exp(e2), su, e1, x);
      }
      const [s, expr] = this.mrv(arg, x);
      return [s, exp(expr)];
    }
    if (e instanceof Fn) {
      if (e.name === 'log') {
        const [s, expr] = this.mrv(first(e.args), x);
        return [s, log(expr)];
      }
      // a function whose growth at infinity is not known here (uppergamma(x, 1)) would be taken for
      // a coefficient of lower comparability class
      if (!TAME.has(e.name) && e.args.some((a) => a.has(x) && isInfinite(this.limitinf(a, x)))) {
        throw new GruntzError(`${e.name} at infinity is not supported`);
      }
      const l = e.args.map((a) => this.mrv(a, x));
      const l2 = l.filter(([s]) => s.size !== 0);
      if (l2.length !== 1) throw new GruntzError('mrv of a function of several arguments in x');
      return [first(l2)[0], fn(e.name, l.map(([, a]) => a))];
    }
    if (e instanceof UndefFn && (e.name === SCALED_BESSELI || e.name === SCALED_BESSELK)) {
      // (the Bessel helpers of rewriteTractable: their order nu is free of x)
      const [s, expr] = this.mrv(last(e.args), x);
      return [s, new UndefFn(e.name, [first(e.args), expr])];
    }
    throw new GruntzError(`cannot compute the mrv set of ${e.toString()}`);
  }

  /** Sign of e as x -> oo: 1, -1, 0, or sign(c) for a constant c of unknown sign. */
  sign(e: Expr, x: Sym): Expr {
    this.tick();
    if (isPositive(e)) return S.One;
    if (isNegative(e)) return S.NegOne;
    if (e instanceof Rational && e.isZero) return S.Zero;
    if (!e.has(x)) return constSign(e);
    if (e instanceof Mul) {
      const [a, ...rest] = e.args;
      return mul(this.sign(defined(a, 'factor'), x), this.sign(mul(...rest), x));
    }
    if (isExp(e)) return S.One;
    if (e instanceof Pow) {
      const s = this.sign(e.base, x);
      if (s instanceof Rational && s.isOne) return S.One;
      if (e.exp instanceof Rational && e.exp.isInteger) return pow(s, e.exp);
    }
    if (e instanceof Fn && e.name === 'log' && isPositive(first(e.args))) return this.sign(add(first(e.args), -1), x);
    const [c0] = this.mrvLeadterm(e, x);
    return this.sign(c0, x);
  }

  /** Limit of e as x -> oo (x positive). */
  limitinf(eIn: Expr, x: Sym): Expr {
    this.tick();
    if (!eIn.has(x)) return eIn;
    // (the limits are cached like in SymPy: comparisons of mrv elements ask for the same limits again)
    const key = `${eIn.key}|${x.key}`;
    const known = this.limits.get(key);
    if (known !== undefined) return known;
    const r = this.limitinfUncached(eIn, x);
    this.limits.set(key, r);
    return r;
  }

  /** limitinf, or undefined when the algorithm cannot decide it. */
  private tryLimitinf(e: Expr, x: Sym): Expr | undefined {
    try {
      return this.limitinf(e, x);
    } catch {
      return undefined;
    }
  }

  private limitinfUncached(eIn: Expr, x: Sym): Expr {
    const e = powdenest(rewriteTractable(eIn, x, (g) => this.tryLimitinf(g, x)));
    const [c0, e0] = this.mrvLeadterm(e, x);
    const sig = this.sign(e0, x);
    if (sig instanceof Rational && sig.isOne) return S.Zero;
    if (sig instanceof Rational && sig.p === -1n && sig.q === 1n) {
      // an imaginary coefficient I*a is a direction (I*oo)
      if (c0 instanceof Mul && c0.args.some((a) => a.key === S.I.key) && !c0.has(x)) return mul(c0, S.Infinity);
      // (the leading coefficient is not 0)
      return mul(this.sign(c0, x), S.Infinity);
    }
    if (!(sig instanceof Rational && sig.isZero)) throw new GruntzError(`the sign of the exponent ${e0.toString()} is not known`);
    return this.limitinf(c0, x);
  }

  /** Leading coefficient and exponent of e in the most rapidly varying subexpression w -> 0+. */
  mrvLeadterm(e: Expr, x: Sym): [Expr, Expr] {
    if (!e.has(x)) return [e, S.Zero];
    // (the mrv set of an expression in x is not empty)
    let [omega, exps] = this.mrv(e, x);
    if (omega.has(x)) {
      // move the whole set up: x -> exp(x)
      const up = new SubsSet();
      const ex = exp(x);
      for (const [expr, v] of omega.items.values()) up.items.set(xreplace(expr, [[x, ex]]).key, [xreplace(expr, [[x, ex]]), v]);
      for (const [v, rw] of omega.rewrites) up.rewrites.set(v, xreplace(rw, [[x, ex]]));
      omega = up;
      exps = xreplace(exps, [[x, ex]]);
    }
    const w = new Dummy('w', { positive: true });
    const [f, logw] = this.rewrite(exps, omega, x, w);
    const ex = new Expander(w);
    try {
      // log(w) = logw is substituted before the leading term is chosen: the coefficients may cancel
      // (x*log(x/E) - loggamma(x + 1): the terms of order 1/w cancel)
      let n = Rational.of(1n);
      for (let i = 0; i < 6; i++) {
        for (const t of ex.ser(f, n).terms) {
          const c = xreplace(t.c, [[ex.L, logw]]);
          if (!isZeroCoeff(c)) return [c, t.e];
        }
        n = Rational.of(n.p * 2n + 2n);
      }
      throw new GruntzError('leading term not found');
    } catch {
      // powers of w with irrational exponents (2**x and 3**x in one mrv set): the leading monomial
      // (also when the expansion finds no nonzero term or fails otherwise)
      const lt = monomialLead(f, w, ex.L, x, logw);
      return [xreplace(lt.c, [[ex.L, logw]]), lt.e];
    }
  }

  /** e with the elements of omega written in terms of w; and log(w) in terms of x. */
  private rewrite(e: Expr, omegaSet: SubsSet, x: Sym, w: Dummy): [Expr, Expr] {
    const entries = [...omegaSet.items.values()];
    // (after moving up, every element is an exponential)
    const rewrites = omegaSet.rewrites;
    // the height of an element in the tree of rewrites (an element whose rewrite contains another goes first)
    const height = (v: Dummy, seen: number): number => {
      const r = rewrites.get(v.key);
      if (r === undefined || seen > entries.length) return 1;
      return 1 + entries.filter(([, v2]) => r.has(v2)).reduce((a, [, v2]) => a + height(v2, seen + 1), 0);
    };
    const omega = entries.map((it) => ({ it, h: height(it[1], 0) })).sort((a, b) => b.h - a.h).map(({ it }) => it);
    let sig: Expr = S.Zero;
    for (const [g] of omega) {
      sig = this.sign(expectExp(g).exp, x);
      if (!(sig instanceof Rational && (sig.isOne || (sig.p === -1n && sig.q === 1n)))) throw new SignUnknownError(`Result depends on the sign of ${sig.toString()}`);
    }
    const g = expectExp(first(omega.slice(-1))[0]);
    const up = sig instanceof Rational && sig.isOne;
    const wsym = up ? pow(w, -1) : w;
    const o2: [Expr, Expr][] = [];
    let denom = 1n;
    for (const [f, v] of omega) {
      const fe = expectExp(f).exp;
      const c = this.limitinf(mul(fe, pow(g.exp, -1)), x);
      if (c instanceof Rational) denom = lcm(denom, c.q);
      const rw = rewrites.get(v.key);
      const arg = rw === undefined ? fe : expectExp(rw).exp;
      // (expanded like in SymPy: the parts of the same class cancel, x*log(x + 1) - (x + 1)*log(x))
      o2.push([v, mul(exp(expand(add(arg, mul(-1, c, g.exp)))), pow(wsym, c))]);
    }
    let f = powsimp(e, { deep: true, combine: 'exp' });
    for (const s of o2) f = xreplace(f, [s]);
    let logw = up ? mul(-1, g.exp) : g.exp;
    if (denom !== 1n) {
      f = xreplace(f, [[w, pow(w, Rational.of(denom))]]);
      logw = mul(logw, Rational.of(1n, denom));
    }
    f = mapBottomUp(f, (a) => (a instanceof Add ? together(a) : a));
    return [f, logw];
  }
}

type Mono = { c: Expr; e: Expr };

/** The numeric value of a real constant exponent. */
function expValue(e: Expr): number {
  if (e instanceof Rational) return e.value;
  try {
    const v = e.toComplex();
    if (v.im === 0) return v.re;
  } catch {
    // not numeric
  }
  throw new GruntzError(`exponent ${e.toString()} is not a real number`);
}

/**
 * Leading monomial c*w**e of f as w -> 0+ with real constant exponents (log(w) is L in c), for
 * the expressions the Puiseux expansion does not handle; a cancellation of leading terms is not decided.
 */
export function monomialLead(f: Expr, w: Sym, L: Sym, x: Sym, logw: Expr): Mono {
  const lead = (g: Expr): Mono => monomialLead(g, w, L, x, logw);
  if (!f.has(w)) return { c: f, e: S.Zero };
  if (f.key === w.key) return { c: S.One, e: S.One };
  if (f instanceof Mul) {
    const ls = f.args.map(lead);
    return { c: mul(...ls.map((l) => l.c)), e: add(...ls.map((l) => l.e)) };
  }
  if (isExp(f)) {
    // exp(g) with g = g0 + o(1), where g0 = a + b*L gives exp(a)*w**b
    const terms = (f.exp instanceof Add ? f.exp.args : [f.exp]).map(lead);
    let g0: Expr = S.Zero;
    for (const t of terms) {
      const v = expValue(t.e);
      if (v < 0) throw new GruntzError('essential singularity');
      if (v === 0) g0 = add(g0, t.c);
    }
    const b = coeff(expandMul(g0), L);
    const a = expandMul(add(g0, mul(-1, b, L)));
    if (a.has(L) || b.has(L)) throw new GruntzError('power of log(w) in an exponent');
    // a factor of log(w) that depends on x is not a power of w: exp(log(w)/x) = exp(logw/x)
    if (b.has(x)) return { c: exp(xreplace(g0, [[L, logw]])), e: S.Zero };
    return { c: exp(a), e: b };
  }
  if (f instanceof Pow) {
    if (f.exp.has(w)) return lead(exp(mul(f.exp, log(f.base))));
    const l = lead(f.base);
    return { c: pow(l.c, f.exp), e: mul(l.e, f.exp) };
  }
  if (f instanceof Add) {
    const ls = f.args.map(lead);
    const vals = ls.map((l) => expValue(l.e));
    const m = Math.min(...vals);
    const low = ls.filter((_, i) => Math.abs(at(vals, i) - m) <= 1e-12 * Math.max(1, Math.abs(m)));
    const c = add(...low.map((l) => l.c));
    if (isZeroCoeff(c)) throw new GruntzError('cancellation of leading terms');
    return { c, e: first(low).e };
  }
  if (f instanceof Fn) {
    const a = f.args.map(lead);
    if (f.name === 'log' && a.length === 1) {
      const l = first(a);
      if (!(l.e instanceof Rational && l.e.isZero && l.c instanceof Rational && l.c.isOne)) return { c: add(log(l.c), mul(l.e, L)), e: S.Zero };
      return lead(add(first(f.args), -1));
    }
    // a function continuous at the limits of its arguments, with a nonzero value there
    const vals = a.map((l) => {
      const v = expValue(l.e);
      // (a function with a cut through 0, acoth(0+) = -I*pi/2, is not continuous there)
      if (v < 0 || l.c.has(L) || (v > 0 && !AT_ZERO.has(f.name))) throw new GruntzError(`cannot expand ${f.name}`);
      return v > 0 ? S.Zero : l.c;
    });
    const r = fn(f.name, vals);
    const infinite = (u: Expr): boolean => u instanceof Special || u.args.some(infinite);
    if (isZeroCoeff(r) || infinite(r)) throw new GruntzError(`cannot expand ${f.name}`);
    return { c: r, e: S.Zero };
  }
  throw new GruntzError(`cannot expand ${f.toString()}`);
}

function expectExp(e: Expr): Pow {
  return cast(e, Pow, 'mrv element');
}

function lcm(a: bigint, b: bigint): bigint {
  const g = (p: bigint, q: bigint): bigint => (q === 0n ? p : g(q, p % q));
  return (a / g(a, b)) * b;
}

const isInfinite = (e: Expr): boolean => e instanceof Special && e.name !== 'nan';

/** Sign of a constant: 1, -1, 0, or sign(c) when it cannot be decided. */
function constSign(e: Expr): Expr {
  // (a constant that is 0 without being written as 0: log(2)/log(2/3) - log(4/3)/log(2/3) + 1)
  if (isZeroCoeff(e)) return S.Zero;
  if (impl.freeSymbols(e).size === 0) {
    try {
      const v = e.toComplex();
      if (v.im === 0 && v.re !== 0) return Rational.of(Math.sign(v.re));
    } catch {
      // undecided
    }
  }
  return fn('sign', [e]);
}

/**
 * Functions written with tractable ones for the expansion at infinity (SymPy rewrite('tractable')):
 * gamma(z) = exp(loggamma(z)), whose argument tends to oo.
 */
/** The hyperbolic functions in terms of sinh and cosh. */
const HYPERBOLIC: Partial<Record<string, (sh: Expr, ch: Expr) => Expr>> = {
  sinh: (sh) => sh,
  cosh: (_sh, ch) => ch,
  tanh: (sh, ch) => mul(sh, pow(ch, -1)),
  coth: (sh, ch) => mul(ch, pow(sh, -1)),
  sech: (_sh, ch) => pow(ch, -1),
  csch: (sh) => pow(sh, -1),
};

function rewriteTractable(e: Expr, x: Sym, limitinf: (g: Expr) => Expr | undefined): Expr {
  return mapBottomUp(e, (a) => {
    if (a instanceof Fn && a.has(x)) {
      // besseli(nu, g) = exp(g)*_besseli(nu, g) and besselk(nu, g) = exp(-g)*_besselk(nu, g) for g -> oo
      // (SymPy _eval_rewrite_as_tractable)
      // hyperbolic functions of an argument tending to oo or -oo are exponentials (SymPy _eval_rewrite_as_tractable)
      const hyp = HYPERBOLIC[a.name];
      if (hyp !== undefined) {
        const g = first(a.args);
        const l = limitinf(g);
        if (l === S.Infinity || l === S.NegativeInfinity) {
          const [ep, em] = [exp(g), exp(mul(-1, g))];
          const [sh, ch] = [mul(S.Half, add(ep, mul(-1, em))), mul(S.Half, add(ep, em))];
          return hyp(sh, ch);
        }
      }
      if ((a.name === 'besseli' || a.name === 'besselk') && !first(a.args).has(x) && limitinf(last(a.args)) === S.Infinity) {
        const g = last(a.args);
        const i = a.name === 'besseli';
        return mul(exp(i ? g : mul(-1, g)), new UndefFn(i ? SCALED_BESSELI : SCALED_BESSELK, a.args));
      }
      if (a.name === 'factorial') return exp(fn('loggamma', [add(first(a.args), 1)]));
      if (a.name === 'gamma') return exp(fn('loggamma', [first(a.args)]));
      // binomial(n, k) = gamma(n + 1)/(gamma(k + 1)*gamma(n - k + 1))
      if (a.name === 'binomial') {
        const [m, k] = [at(a.args, 0), at(a.args, 1)];
        const lg = (u: Expr): Expr => fn('loggamma', [add(u, 1)]);
        return exp(add(lg(m), mul(-1, lg(k)), mul(-1, lg(add(m, mul(-1, k))))));
      }
    }
    return a;
  });
}

/**
 * Limit of e as z -> z0 by the Gruntz algorithm (SymPy gruntz); throws GruntzError when
 * the algorithm cannot decide it.
 */
export function gruntz(e: Expr, z: Sym, z0: Expr, dir: '+' | '-', budget?: number): Expr {
  const p = new Dummy('p', { positive: true });
  let e0: Expr;
  if (z0 instanceof Special && z0.name === 'oo') e0 = xreplace(e, [[z, p]]);
  else if (z0 instanceof Special && z0.name === '-oo') e0 = xreplace(e, [[z, mul(-1, p)]]);
  else e0 = xreplace(e, [[z, add(z0, mul(dir === '-' ? -1 : 1, pow(p, -1)))]]);
  return new Gruntz(budget).limitinf(e0, p);
}
