// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arbitrary-precision evaluation of expression trees (SymPy evalf).
 *
 * `evalMp` evaluates at a working precision; `evalAdaptive` repeats the
 * evaluation with more guard bits until the result rounded to the target
 * precision is stable, which certifies the digits in the presence of
 * cancellation.
 */

import type { ConstantName, Expr } from '../core/nodes';
import { Add, Constant, ExtensionExpr, Float, Fn, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, mul } from '../core/ops';
import { at } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc } from './mpfun';


export type { Mpc };

/** An mpFns entry taking exactly one argument. */
export const mpFn1 =
  (f: (a: Mpc, prec: number) => Mpc) =>
  (args: Mpc[], prec: number): Mpc =>
    f(at(args, 0), prec);

/** An mpFns entry taking exactly two arguments. */
export const mpFn2 =
  (f: (a: Mpc, b: Mpc, prec: number) => Mpc) =>
  (args: Mpc[], prec: number): Mpc =>
    f(at(args, 0), at(args, 1), prec);

/** Arbitrary-precision implementations of functions: args and result as Mpc at `prec` bits. */
export const mpFns: Record<string, (args: Mpc[], prec: number) => Mpc> = {
  sin: mpFn1(M.csin),
  cos: mpFn1(M.ccos),
  tan: mpFn1(M.ctan),
  asin: mpFn1(M.casin),
  acos: mpFn1(M.cacos),
  atan: mpFn1(M.catan),
  sinh: mpFn1(M.csinh),
  cosh: mpFn1(M.ccosh),
  tanh: mpFn1(M.ctanh),
  asinh: mpFn1(M.casinh),
  acosh: mpFn1(M.cacosh),
  atanh: mpFn1(M.catanh),
  log: (args, p) => {
    const l = M.clog(at(args, 0), p + 10);
    if (args.length === 1) return [F.round(l[0], p), F.round(l[1], p)];
    return M.cdiv(l, M.clog(at(args, 1), p + 10), p);
  },
  exp: mpFn1(M.cexp),
  abs: mpFn1((a, p) => [M.cabs(a, p), ZERO]),
  re: mpFn1((a, p) => [F.round(a[0], p), ZERO]),
  im: mpFn1((a, p) => [F.round(a[1], p), ZERO]),
  arg: mpFn1((a, p) => [M.carg(a, p), ZERO]),
  conjugate: mpFn1((a, p) => [F.round(a[0], p), F.round(F.neg(a[1]), p)]),
  sign: mpFn1((a, p) => {
    if (M.isReal(a)) return [F.fromInt(BigInt(F.sign(a[0]))), ZERO];
    return M.cdiv(a, [M.cabs(a, p + 10), ZERO], p);
  }),
  atan2: mpFn2((y, x, p) => [M.atan2(y[0], x[0], p), ZERO]),
};

/** Fallback double-precision implementations (registered by evalf.ts / special.ts). */
let doubleFallback: (name: string, args: Mpc[]) => Mpc | undefined = () => undefined;
export function setDoubleFallback(f: typeof doubleFallback): void {
  doubleFallback = f;
}

const CONSTANTS: Record<ConstantName, (prec: number) => Mpc> = {
  pi: (prec) => [M.mpPi(prec), ZERO],
  E: (prec) => [M.mpE(prec), ZERO],
  I: () => M.CI,
  EulerGamma: (prec) => [M.mpEuler(prec), ZERO],
  Catalan: (prec) => [M.mpCatalan(prec), ZERO],
  GoldenRatio: (prec) => [M.mpPhi(prec), ZERO],
  TribonacciConstant: (prec) => [M.mpTribonacci(prec), ZERO],
};

/**
 * The value of a symbol at working precision wp, or undefined; the default
 * serves expressions without free symbols (no symbol has a value).
 */
export type SymbolLookup = (s: Sym, wp: number) => Mpc | undefined;

const noValue = (): Mpc | undefined => undefined;

/** Evaluate at working precision wp (each operation rounded to wp bits). */
export function evalMp(e: Expr, wp: number, lookup: SymbolLookup = noValue): Mpc {
  const ev = (x: Expr): Mpc => {
    if (x instanceof Rational) return [x.q === 1n ? F.fromInt(x.p) : F.fromRational(x.p, x.q, wp), ZERO];
    if (x instanceof Float) return [x.mpf, ZERO];
    if (x instanceof Constant) return CONSTANTS[x.name](wp);
    if (x instanceof Sym) {
      const v = lookup(x, wp);
      if (v === undefined) throw new TypeError(`no value for ${x.name}`);
      return v;
    }
    if (x instanceof Add) {
      let acc: Mpc = M.C0;
      for (const a of x.args) acc = M.cadd(acc, ev(a), wp);
      return acc;
    }
    if (x instanceof Mul) {
      let acc: Mpc = M.C1;
      for (const a of x.args) acc = M.cmul(acc, ev(a), wp);
      return acc;
    }
    if (x instanceof Pow) {
      if (x.base instanceof Constant && x.base.name === 'E') return M.cexp(ev(x.exp), wp);
      const b = ev(x.base);
      if (x.exp instanceof Rational) {
        if (x.exp.q === 1n) return M.cpowInt(b, x.exp.p, wp);
        if (x.exp.q === 2n) return M.cpowInt(M.csqrt(b, wp + 10), x.exp.p, wp);
        if (M.isReal(b) && b[0].man > 0n && x.exp.p === 1n) return [M.nthRoot(b[0], x.exp.q, wp), ZERO];
      }
      return M.cpow(b, ev(x.exp), wp);
    }
    if (x instanceof Fn) {
      // Gamma at thirds and quarters from Gamma(1/3), Gamma(1/4) by binary splitting
      const a0 = x.args[0];
      if (x.name === 'gamma' && x.args.length === 1 && a0 instanceof Rational) {
        const g = M.mpGammaRational(a0.p, a0.q, wp);
        if (g !== undefined) return [g, ZERO];
      }
      const args = x.args.map(ev);
      const f = mpFns[x.name];
      if (f) return f(args, wp);
      const d = doubleFallback(x.name, args);
      if (d) return d;
      throw new TypeError(`cannot evaluate ${x.name}`);
    }
    if (x instanceof ExtensionExpr) {
      const v = x.numericValue(Math.ceil(wp / 3.32) + 5);
      if (v !== undefined) return ev(v);
    }
    throw new TypeError(`cannot evaluate ${x.kind}`);
  };
  return ev(e);
}

function sameAt(a: Mpf, b: Mpf, prec: number): boolean {
  const ra = F.round(a, prec);
  const rb = F.round(b, prec);
  return ra.man === rb.man && ra.exp === rb.exp;
}

/** True when part x is negligible next to `ref` at working precision wp. */
function negligible(x: Mpf, ref: number, wp: number): boolean {
  return F.isZero(x) || F.mag(x) < ref - wp + 8;
}

/**
 * Evaluate to `prec` correct bits, raising the working precision until two
 * successive evaluations agree. Parts that vanish relative to the other
 * part (cancellation to zero) are returned as exact zeros.
 */
export function evalAdaptive(e: Expr, prec: number, lookup: SymbolLookup = noValue): Mpc {
  let wp = prec + 20;
  let prev = evalMp(e, wp, lookup);
  for (let i = 0; i < 8; i++) {
    const wp2 = prec + 20 + 40 * 2 ** (i + 1);
    const cur = evalMp(e, wp2, lookup);
    const ref = Math.max(F.mag(cur[0]), F.mag(cur[1]));
    const refPrev = Math.max(F.mag(prev[0]), F.mag(prev[1]));
    // The stable value of one component, or undefined when it has not settled.
    const settled = (k: 0 | 1): Mpf | undefined => {
      const negPrev = negligible(prev[k], refPrev, wp);
      const negCur = negligible(cur[k], ref, wp2);
      if (negPrev && negCur) return ZERO;
      if (!negPrev && !negCur && sameAt(prev[k], cur[k], prec)) return F.round(cur[k], prec);
      return undefined;
    };
    const re = settled(0);
    const im = settled(1);
    if (re !== undefined && im !== undefined) return [re, im];
    prev = cur;
    wp = wp2;
  }
  return [F.round(prev[0], prec), F.round(prev[1], prec)];
}

/** Build a Float / complex Float expression from an Mpc. */
export function fromMpc(v: Mpc, prec: number, chop?: boolean | number): Expr {
  let [re, im] = v;
  if (chop !== undefined && chop !== false) {
    // SymPy chop_parts: drop parts below 2**(-chopPrec + 4)
    const chopPrec = chop === true ? prec : Math.round(-3.321 * Math.log10(chop) + 2.5);
    if (!F.isZero(re) && F.mag(re) < -chopPrec + 4) re = ZERO;
    if (!F.isZero(im) && F.mag(im) < -chopPrec + 4) im = ZERO;
  }
  if (F.isZero(im)) return F.isZero(re) ? S.Zero : new Float(re, prec);
  const imPart = mul(new Float(im, prec), S.I);
  if (F.isZero(re)) return imPart;
  return add(new Float(re, prec), imPart);
}
