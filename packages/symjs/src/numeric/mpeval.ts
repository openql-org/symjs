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
import { Add, Constant, ExtensionExpr, Float, Fn, Mul, Pow, Rational, S, Special, Sym, isNum } from '../core/nodes';
import { add, mul } from '../core/ops';
import { at } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE, ZERO } from './mpf';
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

/** A component of an mpmath number that may be one of mpmath's special values. */
export type MpPart = Mpf | 'inf' | '-inf' | 'nan';
const isSpecialPart = (p: MpPart): p is 'inf' | '-inf' | 'nan' => typeof p === 'string';
const isFinitePart = (p: MpPart): p is Mpf => typeof p !== 'string';
type Parts = readonly [MpPart, MpPart];
const isFiniteValue = (v: Parts): v is Mpc => isFinitePart(v[0]) && isFinitePart(v[1]);

/**
 * A value with an infinite or undefined component, as mpmath returns it (mpf inf, -inf, nan per
 * real and imaginary part). A kernel throws it; sums and products combine it as SymPy's evalf does
 * (evalf_add, evalf_mul), and evalf gives SymPy's result (Float._new: finf -> oo, fninf -> -oo, fnan -> nan).
 */
export class MpSpecialValue extends RangeError {
  constructor(
    readonly re: MpPart,
    readonly im: MpPart = ZERO,
  ) {
    super('mpmath special value');
    this.name = 'MpSpecialValue';
  }
}

/** SymPy Add(*special) of oo, -oo and nan. */
function addSpecials(parts: readonly ('inf' | '-inf' | 'nan')[]): 'inf' | '-inf' | 'nan' {
  if (parts.includes('nan') || (parts.includes('inf') && parts.includes('-inf'))) return 'nan';
  return parts.includes('inf') ? 'inf' : '-inf';
}

/** SymPy add_terms for one component: the special values decide when there are any. */
function addParts(parts: readonly MpPart[], wp: number): MpPart {
  const specials = parts.filter(isSpecialPart);
  if (specials.length) return addSpecials(specials);
  return parts.filter(isFinitePart).reduce((acc, q) => F.add(acc, q, wp), ZERO);
}

/**
 * SymPy evalf_mul with special factors: nan when a factor has a nan real part or is zero, else the
 * product of the infinite real parts (the finite factors are not looked at: (2 + I)*(oo + oo*I) = oo).
 * Powers and functions of a special value are not evaluated (SymPy uses mpmath's arithmetic with inf).
 */
function mulSpecial(vals: readonly Parts[]): MpSpecialValue {
  const signs: number[] = [];
  let hasZero = false;
  for (const [re, im] of vals) {
    if (re === 'nan') return new MpSpecialValue('nan');
    if (isSpecialPart(re)) signs.push(re === 'inf' ? 1 : -1);
    else if (F.isZero(re) && isFinitePart(im) && F.isZero(im)) hasZero = true;
  }
  // (no infinite real part: SymPy's product of the parts as mpf tuples gives nan, (1 + oo*I)*2 = nan)
  if (!signs.length || hasZero) return new MpSpecialValue('nan');
  return new MpSpecialValue(signs.reduce((a, b) => a * b, 1) > 0 ? 'inf' : '-inf');
}

/** The sign of a part (NaN for nan). */
const partSign = (p: MpPart): number => (p === 'nan' ? NaN : p === 'inf' ? 1 : p === '-inf' ? -1 : F.sign(p));

/** mpmath mpf_mul with inf and nan: inf*0 = nan. */
function extMul(a: MpPart, b: MpPart, wp: number): MpPart {
  if (isFinitePart(a) && isFinitePart(b)) return F.mul(a, b, wp);
  // (a zero or nan sign gives nan)
  const s = partSign(a) * partSign(b);
  return s > 0 ? 'inf' : s < 0 ? '-inf' : 'nan';
}
const extNeg = (a: MpPart): MpPart => (isFinitePart(a) ? F.neg(a) : a === 'inf' ? '-inf' : a === '-inf' ? 'inf' : 'nan');

/** Real exp, cos, sin, cosh, sinh with mpmath's values at inf and nan. */
const extExp = (a: MpPart, wp: number): MpPart => (isFinitePart(a) ? M.exp(a, wp) : a === 'inf' ? 'inf' : a === '-inf' ? ZERO : 'nan');
const extCosSin = (a: MpPart, wp: number): [MpPart, MpPart] => {
  if (!isFinitePart(a)) return ['nan', 'nan'];
  const [s, c] = M.sinCos(a, wp);
  return [c, s];
};
const extCosh = (a: MpPart, wp: number): MpPart => (isFinitePart(a) ? M.cosh(a, wp) : a === 'nan' ? 'nan' : 'inf');
const extSinh = (a: MpPart, wp: number): MpPart => (isFinitePart(a) ? M.sinh(a, wp) : a);
const isZeroPart = (p: MpPart): boolean => isFinitePart(p) && F.isZero(p);

/** mpmath mpc_exp: (exp a, 0) for a real argument, else exp(a) (cos b, sin b). */
function extCexp([a, b]: Parts, wp: number): Parts {
  if (isZeroPart(b)) return [extExp(a, wp), ZERO];
  const m = extExp(a, wp);
  const [c, s] = extCosSin(b, wp);
  return [extMul(m, c, wp), extMul(m, s, wp)];
}

/** mpmath mpc_sin: sin a cosh b + i cos a sinh b, with the real and imaginary axes exact. */
function extCsin([a, b]: Parts, wp: number): Parts {
  const [c, s] = extCosSin(a, wp);
  if (isZeroPart(b)) return [s, ZERO];
  if (isZeroPart(a)) return [ZERO, extSinh(b, wp)];
  return [extMul(s, extCosh(b, wp), wp), extMul(c, extSinh(b, wp), wp)];
}

/** mpmath mpc_cos: cos a cosh b - i sin a sinh b, with the real and imaginary axes exact. */
function extCcos([a, b]: Parts, wp: number): Parts {
  const [c, s] = extCosSin(a, wp);
  if (isZeroPart(b)) return [c, ZERO];
  if (isZeroPart(a)) return [extCosh(b, wp), ZERO];
  return [extMul(c, extCosh(b, wp), wp), extNeg(extMul(s, extSinh(b, wp), wp))];
}

/** The rotations z -> i z and z -> -i z of parts. */
const extMulI = ([a, b]: Parts): Parts => [extNeg(b), a];
const extMulNegI = ([a, b]: Parts): Parts => [b, extNeg(a)];

/** mpmath atan2 with inf and nan (atan2(inf, inf) = nan). */
function extAtan2(y: MpPart, x: MpPart, wp: number): MpPart {
  if (isFinitePart(y) && isFinitePart(x)) return M.atan2(y, x, wp);
  if (y === 'nan' || x === 'nan' || (!isFinitePart(y) && !isFinitePart(x))) return 'nan';
  const pi = M.mpPi(wp);
  if (!isFinitePart(y)) return F.ldexp(y === 'inf' ? pi : F.neg(pi), -1);
  if (x === 'inf') return ZERO;
  return F.sign(y) < 0 ? F.neg(pi) : pi;
}

/**
 * tan at a point with an infinite or undefined part: the limit i*sign(b) for a finite real part
 * (tan(x + i*y) -> i as y -> oo; mpmath's mpc_tan gives 0 + nan*j, SymPy prints nan) and nan
 * otherwise (no limit along the real axis).
 */
function extCtan([a, b]: Parts): Parts {
  if (isFinitePart(a) && b !== 'nan' && !isFinitePart(b)) return [ZERO, F.fromInt(BigInt(partSign(b)))];
  return ['nan', isZeroPart(b) ? ZERO : 'nan'];
}

/** 1/w for the limits of extCtan: 1/(+-i) = -+i; nan stays nan. */
const extRecipUnit = ([a, b]: Parts): Parts => (isFinitePart(b) && !F.isZero(b) ? [a, F.neg(b)] : [a, b]);

/** The reciprocal of sin or cos at a point with an infinite part: 0 where they tend to infinity, else nan. */
function extRecipBig([a, b]: Parts): Parts {
  if (isFinitePart(a) && b !== 'nan' && !isFinitePart(b)) return [ZERO, ZERO];
  return ['nan', 'nan'];
}

/**
 * Functions of arguments with an infinite or undefined part (mpmath's inf and nan arithmetic,
 * which SymPy's evalf uses through mpmath). sin, cos, sinh, cosh and exp follow mpmath's
 * formulas exactly; tan, tanh, cot, sec, csc and atan give the limits where mpmath's formulas
 * produce nan although the limit exists (tan(1 + oo*I) = I, atan(oo + oo*I) = pi/2).
 */
export const mpSpecialFns: Record<string, (args: readonly Parts[], wp: number) => Parts> = {
  exp: (args, wp) => extCexp(at(args, 0), wp),
  sin: (args, wp) => extCsin(at(args, 0), wp),
  cos: (args, wp) => extCcos(at(args, 0), wp),
  // sinh z = -i sin(i z), cosh z = cos(i z)
  sinh: (args, wp) => extMulNegI(extCsin(extMulI(at(args, 0)), wp)),
  cosh: (args, wp) => extCcos(extMulI(at(args, 0)), wp),
  tan: (args) => extCtan(at(args, 0)),
  cot: (args) => extRecipUnit(extCtan(at(args, 0))),
  // tanh z = -i tan(i z)
  tanh: (args) => extMulNegI(extCtan(extMulI(at(args, 0)))),
  coth: (args) => extRecipUnit(extMulNegI(extCtan(extMulI(at(args, 0))))),
  sec: (args) => extRecipBig(at(args, 0)),
  csc: (args) => extRecipBig(at(args, 0)),
  // log z = log|z| + i arg z with |z| = inf
  log: (args, wp) => {
    const [a, b] = at(args, 0);
    return [a === 'nan' || b === 'nan' ? 'nan' : 'inf', extAtan2(b, a, wp)];
  },
  // atan z -> sign(re z) pi/2 as |z| -> oo (sign(im z) on the imaginary axis), as in mpmath except at
  // (+-inf, +-inf), where mpmath gives nan
  atan: (args, wp) => {
    const [a, b] = at(args, 0);
    if (a === 'nan' || b === 'nan') return ['nan', 'nan'];
    const s = isZeroPart(a) ? partSign(b) : partSign(a);
    const hp = F.ldexp(M.mpPi(wp), -1);
    return [s < 0 ? F.neg(hp) : hp, ZERO];
  },
  atan2: (args, wp) => [extAtan2(at(args, 0)[0], at(args, 1)[0], wp), ZERO],
  arg: (args, wp) => {
    const [a, b] = at(args, 0);
    return [extAtan2(b, a, wp), ZERO];
  },
  abs: (args) => {
    const [a, b] = at(args, 0);
    return [a === 'nan' || b === 'nan' ? 'nan' : 'inf', ZERO];
  },
  re: (args) => [at(args, 0)[0], ZERO],
  im: (args) => [at(args, 0)[1], ZERO],
  conjugate: (args) => {
    const [a, b] = at(args, 0);
    return [a, extNeg(b)];
  },
  // the direction of z: 1, -1, I or -I when one part is infinite and the other finite, else nan
  // (mpmath's z/|z| gives nan there)
  sign: (args) => {
    const [a, b] = at(args, 0);
    if (isFinitePart(a) && b !== 'nan' && !isFinitePart(b)) return [ZERO, F.fromInt(BigInt(partSign(b)))];
    if (isFinitePart(b) && a !== 'nan' && !isFinitePart(a)) return [F.fromInt(BigInt(partSign(a))), ZERO];
    return ['nan', 'nan'];
  },
};

/** A finite value as an Mpc; else thrown as a special value (nan when a part is nan, as SymPy _from_mpmath). */
function fromSpecialResult([re, im]: Parts): Mpc {
  if (re === 'nan' || im === 'nan') throw new MpSpecialValue('nan');
  if (isFinitePart(re) && isFinitePart(im)) return [re, im];
  throw new MpSpecialValue(re, im);
}

/** No value (the default symbol lookup). */
const noValue = (): Mpc | undefined => undefined;

const SPECIAL_PARTS = { oo: 'inf', '-oo': '-inf', nan: 'nan' } as const;

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

/** Evaluate at working precision wp (each operation rounded to wp bits). */
export function evalMp(e: Expr, wp: number, lookup: SymbolLookup = noValue): Mpc {
  /** The value of x as parts, special values included. */
  const evParts = (x: Expr): Parts => {
    try {
      return ev(x);
    } catch (err) {
      if (err instanceof MpSpecialValue) return [err.re, err.im];
      throw err;
    }
  };
  /** The value of an argument of a power or a function, which may not be special. */
  const evArg = (x: Expr): Mpc => {
    const v = evParts(x);
    if (!isFiniteValue(v)) throw new TypeError('an infinite or undefined argument');
    return v;
  };
  const ev = (x: Expr): Mpc => {
    if (x instanceof Rational) return [x.q === 1n ? F.fromInt(x.p) : F.fromRational(x.p, x.q, wp), ZERO];
    if (x instanceof Float) return [x.mpf, ZERO];
    if (x instanceof Constant) return CONSTANTS[x.name](wp);
    // mpmath's inf, -inf and nan (SymPy oo._to_mpmath, ...); zoo has no mpmath value
    if (x instanceof Special && x.name !== 'zoo') throw new MpSpecialValue(SPECIAL_PARTS[x.name]);
    if (x instanceof Sym) {
      const v = lookup(x, wp);
      if (v === undefined) throw new TypeError(`no value for ${x.name}`);
      return v;
    }
    if (x instanceof Add) {
      const vals = x.args.map(evParts);
      if (!vals.every(isFiniteValue)) throw new MpSpecialValue(addParts(vals.map((v) => v[0]), wp), addParts(vals.map((v) => v[1]), wp));
      let acc: Mpc = M.C0;
      for (const v of vals) acc = M.cadd(acc, v, wp);
      return acc;
    }
    if (x instanceof Mul) {
      // SymPy evalf_mul of a pure imaginary h*I: (None, h), so oo*I is the imaginary infinity
      // (a number times I, where -oo is -1*oo here)
      const iIndex = x.args.findIndex((a) => a.key === S.I.key);
      const vals = x.args.map(evParts);
      if (!vals.every(isFiniteValue) && iIndex >= 0 && x.args.every((a, k) => k === iIndex || isNum(a) || a instanceof Special)) {
        throw new MpSpecialValue(ZERO, vals.reduce<MpPart>((acc, v, k) => (k === iIndex ? acc : extMul(acc, v[0], wp)), ONE));
      }
      if (!vals.every(isFiniteValue)) {
        // a numeric coefficient is part of SymPy's infinity (-1*oo is the atom -oo there)
        const c = at(x.args, 0);
        const err = mulSpecial(vals);
        if (isNum(c) && c.isNegative && x.args.some((a) => a instanceof Special) && (err.re === 'inf' || err.re === '-inf')) throw new MpSpecialValue(extNeg(err.re));
        throw err;
      }
      let acc: Mpc = M.C1;
      for (const v of vals) acc = M.cmul(acc, v, wp);
      return acc;
    }
    if (x instanceof Pow) {
      if (x.base instanceof Constant && x.base.name === 'E') {
        const v = evParts(x.exp);
        if (isFiniteValue(v)) return M.cexp(v, wp);
        return fromSpecialResult(extCexp(v, wp));
      }
      const b = evArg(x.base);
      if (x.exp instanceof Rational) {
        if (x.exp.q === 1n) return M.cpowInt(b, x.exp.p, wp);
        if (x.exp.q === 2n) return M.cpowInt(M.csqrt(b, wp + 10), x.exp.p, wp);
        if (M.isReal(b) && b[0].man > 0n && x.exp.p === 1n) return [M.nthRoot(b[0], x.exp.q, wp), ZERO];
      }
      return M.cpow(b, evArg(x.exp), wp);
    }
    if (x instanceof Fn) {
      // Gamma at thirds and quarters from Gamma(1/3), Gamma(1/4) by binary splitting
      const a0 = x.args[0];
      if (x.name === 'gamma' && x.args.length === 1 && a0 instanceof Rational) {
        const g = M.mpGammaRational(a0.p, a0.q, wp);
        if (g !== undefined) return [g, ZERO];
      }
      const parts = x.args.map(evParts);
      if (!parts.every(isFiniteValue)) {
        const g = mpSpecialFns[x.name];
        if (!g) throw new TypeError(`${x.name} of an infinite or undefined argument`);
        return fromSpecialResult(g(parts, wp));
      }
      const args: Mpc[] = parts;
      const f = mpFns[x.name];
      if (f) {
        try {
          return f(args, wp);
        } catch (err) {
          // SymPy _from_mpmath: Float(re) + Float(im)*I, which is nan when a part is nan
          if (err instanceof MpSpecialValue && (err.re === 'nan' || err.im === 'nan')) throw new MpSpecialValue('nan');
          throw err;
        }
      }
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
 * successive evaluations agree. As in SymPy (which tracks the accuracy of the
 * real and imaginary parts separately), a part far below the other one is
 * kept when it is stable (1 + I*exp(-1000) = 1.0 + 5.07595889754946e-435*I),
 * and returned as an exact zero when it is rounding noise that shrinks with
 * the working precision (cancellation to zero).
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
      const a = prev[k];
      const b = cur[k];
      const negPrev = negligible(a, refPrev, wp);
      const negCur = negligible(b, ref, wp2);
      if (negPrev !== negCur) return undefined;
      if (!negCur) return sameAt(a, b, prec) ? F.round(b, prec) : undefined;
      if (F.isZero(b)) return ZERO;
      if (F.isZero(a)) return undefined;
      if (sameAt(a, b, prec)) return F.round(b, prec);
      // noise of a cancellation shrinks with the working precision
      return F.mag(b) < F.mag(a) - (wp2 - wp) / 2 ? ZERO : undefined;
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
