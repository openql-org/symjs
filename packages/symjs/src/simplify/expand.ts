// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file expand(): distribute products over sums and expand integer powers of sums.
 */

import { isNegative, isNonNegative, isNonZero, isPositive, isReal } from '../core/assumptions';
import { Add, Constant, Expr, ExprLike, ExtensionExpr, Fn, Mul, Pow, Rational, S, Sym, impl, isNum } from '../core/nodes';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { cos, cosh, im, log, re, sin, sinh, tan } from '../functions/elementary';
import { rebuild } from '../core/traverse';

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
    if (b instanceof Add && x instanceof Rational && x.isInteger) {
      if (x.p > 0n) return expandPowInt(b, x.p);
      if (x.p < 0n) return pow(expandPowInt(b, -x.p), -1);
    }
    return node;
  }
  return node;
}

/**
 * Distribute products over sums and expand integer powers of sums
 * (SymPy's `mul` and `multinomial` hints only), recursively.
 */
export function expandMul(e: ExprLike): Expr {
  let cur = sympify(e);
  // Iterate to a fixed point: re-canonicalization can expose new sums.
  for (let i = 0; i < 8; i++) {
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

function powerBase(e: Expr, force: boolean): Expr {
  if (!(e instanceof Pow)) return e;
  const [b, x] = e.args;
  if (!(b instanceof Mul)) return e;
  if (x instanceof Rational && x.isInteger) return mul(...b.args.map((f) => pow(f, x)));
  if (force) return mul(...b.args.map((f) => pow(f, x)));
  // factors known to be nonnegative or polar (SymPy polar=True, exp_polar) can be split off
  const polar = (f: Expr) => (f instanceof Fn && f.name === 'exp_polar') || (f instanceof Sym && f.assumptions.polar === true);
  const nonneg: Expr[] = [];
  const other: Expr[] = [];
  for (const f of b.args) {
    if (isNonNegative(f) === true || polar(f)) nonneg.push(f);
    else other.push(f);
  }
  if (nonneg.length === 0) return e;
  // exp_polar(c)**y = exp_polar(c*y)
  const parts = nonneg.map((f) => (f instanceof Fn && f.name === 'exp_polar' ? new Fn('exp_polar', [mul(f.args[0]!, x)]) : pow(f, x)));
  if (other.length === 1) parts.push(pow(other[0]!, x));
  else if (other.length > 1) parts.push(new Pow(new Mul(other), x));
  return mul(...parts);
}

function expandLogNode(e: Expr, force: boolean): Expr {
  if (!(e instanceof Fn && e.name === 'log')) return e;
  const a = e.args[0]!;
  const ok = (f: Expr) => force || isPositive(f) === true;
  if (a instanceof Mul) {
    const factors = a.args;
    // SymPy expands only if every factor is positive (or force)
    if (factors.every((f) => ok(f instanceof Pow ? f.base : f) || (isNum(f) && f.isPositive))) {
      return add(...factors.map((f) => expandLogNode(log(f), force)));
    }
    return e;
  }
  if (a instanceof Pow) {
    const [b, x] = a.args;
    if ((ok(b) && isReal(x) === true) || force) return mul(x, expandLogNode(log(b), force));
  }
  return e;
}

/** Expand sin/cos/tan of sums and integer multiples (SymPy expand_trig). */
function expandTrigNode(e: Expr): Expr {
  if (!(e instanceof Fn) || !['sin', 'cos', 'tan'].includes(e.name)) return e;
  const a = e.args[0]!;
  if (a instanceof Add) {
    const [first, ...rest] = a.args;
    const r = add(...rest);
    const s1 = expandTrigNode(sin(first!));
    const c1 = expandTrigNode(cos(first!));
    const s2 = expandTrigNode(sin(r));
    const c2 = expandTrigNode(cos(r));
    if (e.name === 'sin') return expandMul(add(mul(s1, c2), mul(c1, s2)));
    if (e.name === 'cos') return expandMul(add(mul(c1, c2), mul(-1, s1, s2)));
    const t1 = expandTrigNode(tan(first!));
    const t2 = expandTrigNode(tan(r));
    return mul(add(t1, t2), pow(add(1, mul(-1, t1, t2)), -1));
  }
  const [c, rest] = splitCoeff(a);
  if (c instanceof Rational && c.isInteger && c.p > 1n && !(rest instanceof Rational)) {
    const n = Number(c.p);
    const x = rest;
    if (e.name === 'tan') {
      return mul(expandTrigNode(sin(a)), pow(expandTrigNode(cos(a)), -1));
    }
    // sin(n x), cos(n x) via de Moivre: (cos x + I sin x)^n
    const z = expandMul(pow(add(cos(x), mul(S.I, sin(x))), n));
    const re_: Expr[] = [];
    const im_: Expr[] = [];
    for (const t of z instanceof Add ? z.args : [z]) {
      const [k, r] = splitCoeffI(t);
      if (k) im_.push(r);
      else re_.push(r);
    }
    return e.name === 'cos' ? add(...re_) : add(...im_);
  }
  return e;
}

/** Split t into (has factor I, t / I). */
function splitCoeffI(t: Expr): [boolean, Expr] {
  if (t instanceof Constant && t.name === 'I') return [true, S.One];
  if (t instanceof Mul && t.args.some((f) => f instanceof Constant && f.name === 'I')) {
    return [true, mul(...t.args.filter((f) => !(f instanceof Constant && f.name === 'I')))];
  }
  return [false, t];
}

/** Split into real and imaginary parts (SymPy expand(complex=True)). */
function expandComplexNode(e: Expr): Expr {
  const [r, i] = asRealImagExpand(e);
  return add(r, mul(S.I, i));
}

export function asRealImagExpand(e: Expr): [Expr, Expr] {
  if (e instanceof Fn) {
    const a = e.args[0]!;
    const ra = re(a);
    const ia = im(a);
    switch (e.name) {
      case 'cos':
        return [mul(cos(ra), cosh(ia)), mul(-1, sin(ra), sinh(ia))];
      case 'sin':
        return [mul(sin(ra), cosh(ia)), mul(cos(ra), sinh(ia))];
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
    const [n, d] = impl.fraction!(sympify(ex));
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
    if (h.mul) e = h.deep ? expandMul(e) : expandMulShallow(e, h.mul, h.multinomial);
    else if (h.multinomial) e = applyBottomUp(e, (x) => expandMulShallow(x, false, true), h.deep);
    if (h.power_base) e = applyBottomUp(e, (x) => powerBase(x, h.force), h.deep);
    if (h.power_exp) e = applyBottomUp(e, (x) => powerExp(x, h.force), h.deep);
    if (h.trig) e = applyBottomUp(e, expandTrigNode, h.deep);
    if (h.mul && e.key !== was.key) e = h.deep ? expandMul(e) : expandMulShallow(e, h.mul, h.multinomial);
    if (e.key === was.key) break;
  }
  return e;
}

function expandMulShallow(e: Expr, doMul: boolean, doMulti: boolean): Expr {
  if (doMul && e instanceof Mul && e.args.some((a) => a instanceof Add)) {
    return e.args.reduce<Expr>((acc, f) => distribute(acc, f), Rational.of(1n));
  }
  if (doMulti && e instanceof Pow && e.base instanceof Add && e.exp instanceof Rational && e.exp.isInteger && e.exp.p > 0n) {
    return expandPowInt(e.base, e.exp.p);
  }
  return e;
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
export const expand_complex = (e: ExprLike): Expr => expand(e, { complex: true });

impl.expand = (e) => expand(e);
impl.expandComplex = (e) => expand(e, { complex: true });
