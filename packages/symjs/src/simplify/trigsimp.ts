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

import { Add, Constant, Dummy, Expr, ExprLike, Fn, FnName, Mul, Pow, S } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, neg, pow, sympify } from '../core/ops';
import { countOps, mapBottomUp, some, xreplace } from '../core/traverse';
import { cos, cosh, fn, sin, sinh } from '../functions/elementary';
import { expandMul as expand } from './expand';
import { rewrite } from './rewrite';

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
    const exps = e.args.filter((f) => f instanceof Pow && isE(f.base)) as Pow[];
    if (exps.length < 2) return e;
    const others = e.args.filter((f) => !(f instanceof Pow && isE(f.base)));
    return mul(...others, exp(expand(add(...exps.map((f) => f.exp)))));
  });
}

/** Rewrite sin, cos (and tan) in terms of exp. */
export function rewriteExp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Fn)) return e;
    const u = e.args[0]!;
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
export function trigsimp(ex: ExprLike, opts: { old?: boolean; deep?: boolean; method?: string } = {}): Expr {
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
    return frozen.length ? xreplace(trigsimp(outer), frozen) : trigsimp(outer);
  }
  let e = sympify(ex);
  // reciprocal functions (cot, coth, sec, ...) in terms of the basic ones when that is shorter
  const recip = mapBottomUp(e, (x) => {
    if (!(x instanceof Fn)) return x;
    const r = RECIPROCAL[x.name];
    return r ? pow(fn(r as FnName, [x.args[0]!]), -1) : x;
  });
  if (recip.key !== e.key && countOps(recip) < countOps(e)) e = recip;
  if (!hasTrigFunctions(e)) return e;
  const t = exptotrig(e);
  // SymPy futrig objective: fewer trigonometric functions first, then count_ops
  const lt = trigCount(t);
  const le = trigCount(e);
  if (lt !== le) return lt < le && countOps(t) <= countOps(e) + 1 ? t : countOps(t) <= countOps(e) ? t : e;
  return countOps(t) <= countOps(e) ? t : e;
}

const RECIPROCAL: Record<string, string> = { cot: 'tan', coth: 'tanh', sec: 'cos', csc: 'sin', sech: 'cosh', csch: 'sinh' };
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
  const i = factors.findIndex((f) => f instanceof Pow && f.base instanceof Constant && f.base.name === 'E');
  if (i < 0) return undefined;
  const c = mul(...factors.filter((_, j) => j !== i));
  return [c, (factors[i] as Pow).exp];
}

function combineExpPairs(e: Add): Expr {
  const terms = [...e.args];
  const used = new Set<number>();
  const out: Expr[] = [];
  for (let i = 0; i < terms.length; i++) {
    if (used.has(i)) continue;
    const ti = expTerm(terms[i]!);
    if (ti) {
      for (let j = i + 1; j < terms.length; j++) {
        if (used.has(j)) continue;
        const tj = expTerm(terms[j]!);
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
    if (!used.has(i)) out.push(terms[i]!);
  }
  return add(...out);
}
