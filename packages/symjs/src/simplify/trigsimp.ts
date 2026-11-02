// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Trigonometric / exponential simplification via the exponential form.
 *
 * Strategy: rewrite sin/cos as complex exponentials, expand (products of
 * exponentials combine automatically), then convert each exp(I*y) back to
 * cos(y) + I*sin(y). This proves identities such as sin^2 + cos^2 = 1 and
 * collapses angle-addition patterns like cos(a)cos(b) - sin(a)sin(b) -> cos(a+b),
 * which are ubiquitous in products of rotation gates.
 */

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, Constant, Dummy, Fn, Mul, Pow, Rational, S } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, neg, pow, sympify } from '../core/ops';
import { countOps, mapBottomUp, some, xreplace } from '../core/traverse';
import { cos, cosh, fn, sin, sinh } from '../functions/elementary';
import { expandMul as expand } from './expand';
import { rewrite } from './rewrite';
import { cancel, fraction, together } from './rational';
import { at, defined, first } from '../core/guard';

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
const isI = (e: Expr) => e instanceof Constant && e.name === 'I';

const isTrigFn = (x: Expr) => x instanceof Fn && (x.name === 'sin' || x.name === 'cos' || x.name === 'tan');

/** Contains sin/cos/tan. */
export const hasTrigFunctions = (e: Expr): boolean => some(e, isTrigFn);

/** Contains sin/cos/tan or exp. */
export const hasTrig = (e: Expr): boolean => some(e, (x) => isTrigFn(x) || (x instanceof Pow && isE(x.base)));

/** Combine all exp() factors of each product into a single exp (SymPy `powsimp` for exp). */
export function combineExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Mul)) return e;
    const exps = e.args.filter((f): f is Pow => f instanceof Pow && isE(f.base));
    if (exps.length < 2) return e;
    const others = e.args.filter((f) => !(f instanceof Pow && isE(f.base)));
    return mul(...others, exp(expand(add(...exps.map((f) => f.exp)))));
  });
}

/** Rewrite sin, cos (and tan) in terms of exp. */
export function rewriteExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Fn)) return e;
    const u = first(e.args);
    const ep = exp(mul(S.I, u));
    const em = exp(mul(-1, S.I, u));
    if (e.name === 'cos') return mul(S.Half, add(ep, em));
    if (e.name === 'sin') return mul(neg(S.I), S.Half, add(ep, mul(-1, em)));
    if (e.name === 'tan') return mul(neg(S.I), add(ep, mul(-1, em)), add(ep, em).pow(-1));
    return e;
  });
}

/** If e = exp(I*y) with I-free y, return y. */
function imaginaryExponent(e: Expr): Expr | undefined {
  if (!(e instanceof Pow && isE(e.base))) return undefined;
  const y = expand(mul(-1, S.I, e.exp));
  if (some(y, isI)) return undefined;
  return y;
}

/** Rewrite exp(I*y) as cos(y) + I*sin(y) (y chosen with a canonical sign). */
export function rewriteTrig(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    const y = imaginaryExponent(e);
    if (y === undefined) return e;
    if (couldExtractMinusSign(y)) {
      const z = neg(y);
      return add(cos(z), mul(-1, S.I, sin(z)));
    }
    return add(cos(y), mul(S.I, sin(y)));
  });
}

/** Rewrite to trigonometric form via exponentials (exp(I*y) -> cos(y) + I*sin(y)). */
export function exptotrig(ex: ExprLike): Expr {
  return expand(rewriteTrig(expsimp(ex)));
}

/**
 * Simplify expressions containing trigonometric functions. Like SymPy, an
 * expression without trigonometric functions is returned unchanged, and the
 * result is never more complex than the input.
 */
export function trigsimp(ex: ExprLike, opts: { old?: boolean; deep?: boolean; method?: string; combineFractions?: boolean; keepReciprocals?: boolean } = {}): Expr {
  if (opts.old && !opts.deep) {
    // SymPy trigsimp_old without deep does not look inside other functions
    const frozen: [Expr, Expr][] = [];
    const outer = mapBottomUp(sympify(ex), (x) => {
      if (x instanceof Fn && !TRIG_NAMES.has(x.name) && hasTrigFunctions(x)) {
        const d = new Dummy(`_trigsimp${frozen.length}`);
        frozen.push([d, x]);
        return d;
      }
      return x;
    });
    const inner = { combineFractions: opts.method === 'groebner', keepReciprocals: true };
    return frozen.length ? xreplace(trigsimp(outer, inner), frozen) : trigsimp(outer, inner);
  }
  let e = sympify(ex);
  // SymPy's old algorithm leaves a lone power of a reciprocal function alone (1/cot(x)**2)
  if (opts.keepReciprocals && e instanceof Pow && e.base instanceof Fn && RECIPROCAL[e.base.name]) return e;
  // reciprocal functions (cot, coth, sec, ...) in terms of the basic ones when that is shorter
  const recip = mapBottomUp(e, (x) => {
    if (!(x instanceof Fn)) return x;
    const r = RECIPROCAL[x.name];
    return r ? pow(fn(r, [first(x.args)]), -1) : x;
  });
  if (recip.key !== e.key && countOps(recip) < countOps(e)) e = recip;
  if (!hasTrigFunctions(e)) return e;
  // SymPy futrig only rewrites trigonometric parts: c*sin(u)**2 + c*cos(u)**2 -> c without
  // touching the rest ((x + x**2)/(x*sin(y)**2 + x*cos(y)**2) -> (x**2 + x)/x)
  const pyth = mapBottomUp(e, pythagorean);
  if (pyth.key !== e.key && trigCount(pyth) === 0) return pyth;
  let t = exptotrig(e);
  // a sum of fractions: simplify the combined numerator, then cancel (SymPy trigsimp_groebner-like)
  // (SymPy's old algorithm without method="groebner" does not do this)
  const combine = opts.combineFractions ?? !(opts.old && opts.method !== 'groebner');
  if (combine && e instanceof Add && e.args.some((a) => fraction(a)[1].freeSymbols().size > 0)) {
    try {
      const [n, d] = fraction(together(e));
      const c = cancel(mul(exptotrig(expand(n)), pow(d, -1)));
      if (trigCount(c) < trigCount(t) || (trigCount(c) === trigCount(t) && countOps(c) < countOps(t))) t = c;
    } catch {
      // keep the plain result
    }
  }
  // SymPy futrig objective: fewer trigonometric functions first, then count_ops
  const lt = trigCount(t);
  const le = trigCount(e);
  if (lt !== le) return lt < le && countOps(t) <= countOps(e) + 1 ? t : countOps(t) <= countOps(e) ? t : e;
  return countOps(t) <= countOps(e) ? t : e;
}

/** c*sin(u)**2 + c*cos(u)**2 -> c (and cosh**2 - sinh**2 -> 1) inside a sum. */
function pythagorean(e: Expr): Expr {
  if (!(e instanceof Add)) return e;
  const terms = [...e.args];
  const PARTNER = { sin: 'cos', cos: 'sin', sinh: 'cosh', cosh: 'sinh' } as const;
  type Squared = keyof typeof PARTNER;
  const isSquared = (name: string): name is Squared => Object.hasOwn(PARTNER, name);
  const split = (t: Expr): [Expr, Squared, Expr] | undefined => {
    const fs = t instanceof Mul ? t.args : [t];
    for (const [i, f] of fs.entries()) {
      if (f instanceof Pow && f.exp instanceof Rational && f.exp.p === 2n && f.exp.q === 1n && f.base instanceof Fn && isSquared(f.base.name)) {
        return [mul(...fs.filter((_, j) => j !== i)), f.base.name, first(f.base.args)];
      }
    }
    return undefined;
  };
  for (const [i, ti] of terms.entries()) {
    const a = split(ti);
    if (!a) continue;
    const partner = PARTNER[a[1]];
    // sin**2 + cos**2 = 1; cosh**2 - sinh**2 = 1
    const sign = a[1] === 'sinh' ? -1 : a[1] === 'cosh' ? -1 : 1;
    const j = terms.findIndex((t, k) => {
      if (k === i) return false;
      const b = split(t);
      return b?.[1] === partner && b[2].key === a[2].key && b[0].key === mul(sign, a[0]).key;
    });
    if (j < 0) continue;
    const c = a[1] === 'sinh' ? defined(split(at(terms, j)))[0] : a[0];
    const rest = terms.filter((_, k) => k !== i && k !== j);
    return pythagorean(add(...rest, c));
  }
  return e;
}

const RECIPROCAL: Record<string, FnName> = { cot: 'tan', coth: 'tanh', sec: 'cos', csc: 'sin', sech: 'cosh', csch: 'sinh' };
const TRIG_NAMES = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);
function trigCount(e: Expr): number {
  let n = 0;
  some(e, (x) => {
    if (x instanceof Fn && TRIG_NAMES.has(x.name)) n++;
    return false;
  });
  return n;
}

/** Exponential form: sin/cos rewritten as exponentials, expanded and combined. */
export function expsimp(ex: ExprLike): Expr {
  return combineExp(expand(rewriteExp(sympify(ex))));
}


/**
 * Simplify between exponential and trigonometric/hyperbolic forms (a port of
 * the main steps of SymPy exptrigsimp): every subexpression is replaced by
 * the shorter of itself and its exponential form, then pairs
 * c*exp(a) +- c*exp(-a) are recombined into 2*c*cosh(a) or 2*c*sinh(a).
 */
export function exptrigsimp(ex: ExprLike): Expr {
  const e0 = sympify(ex);
  const step1 = mapBottomUp(e0, (e) => {
    if (!some(e, (x) => x instanceof Fn && TRIG_NAMES.has(x.name)) || !(e instanceof Fn || e instanceof Add)) return e;
    const r = expand(rewrite(e, 'exp'));
    return countOps(r) < countOps(e) ? r : e;
  });
  const step2 = mapBottomUp(step1, (e) => (e instanceof Add ? combineExpPairs(e) : e));
  return countOps(step2) <= countOps(e0) ? step2 : e0;
}

function expTerm(t: Expr): [Expr, Expr] | undefined {
  const factors = t instanceof Mul ? t.args : [t];
  for (const [i, f] of factors.entries()) {
    if (f instanceof Pow && f.base instanceof Constant && f.base.name === 'E') return [mul(...factors.filter((_, j) => j !== i)), f.exp];
  }
  return undefined;
}

function combineExpPairs(e: Add): Expr {
  const terms = [...e.args];
  const used = new Set<number>();
  const out: Expr[] = [];
  for (const [i, term] of terms.entries()) {
    if (used.has(i)) continue;
    const ti = expTerm(term);
    if (ti) {
      for (const [j, termJ] of terms.entries()) {
        if (j <= i || used.has(j)) continue;
        const tj = expTerm(termJ);
        if (!tj || add(ti[1], tj[1]).key !== S.Zero.key) continue;
        const [pos, neg_] = couldExtractMinusSign(ti[1]) ? [tj, ti] : [ti, tj];
        if (pos[0].key === neg_[0].key) {
          out.push(mul(2, pos[0], cosh(pos[1])));
        } else if (pos[0].key === neg(neg_[0]).key) {
          out.push(mul(2, pos[0], sinh(pos[1])));
        } else continue;
        used.add(i).add(j);
        break;
      }
    }
    if (!used.has(i)) out.push(term);
  }
  return add(...out);
}
