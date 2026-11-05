// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file nfloat and comp (SymPy core.function.nfloat, core.numbers.comp).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, ExtensionExpr, Float, Mul, Pow, Rational, S, Special } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { rebuild, xreplace } from '../core/traverse';
import { evalf } from './evalf';
import { float } from './floatctor';
import { at, pair } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE } from './mpf';
import * as M from './mpfun';
import { identify, pslq } from './identification';
import { parse } from '../parsing/parser';
import { limitDenominator } from '../core/numberutils';

/** Make all rationals Floats, keeping exponents exact unless exponent=true. */
export function nfloat(exIn: ExprLike, n = 15, exponent = false): Expr {
  const e = sympify(exIn);
  if (e instanceof Rational) return float(e, n);
  if (e.freeSymbols().size === 0) return evalf(e, n);
  if (e.args.length === 0) return e;
  const reps: [Expr, Expr][] = [];
  const back: [Expr, Expr][] = [];
  if (!exponent) {
    const visit = (x: Expr) => {
      x.args.forEach(visit);
      if (x instanceof Pow && !reps.some(([p]) => p.key === x.key)) {
        const d = new Dummy('e');
        reps.push([x, new Pow(x.base, d)]);
        back.push([d, x.exp]);
      }
    };
    visit(e);
  }
  let rv = reps.length ? xreplace(e, reps) : e;
  rv = evalf(rv, n);
  if (!exponent) rv = xreplace(rv, back);
  else {
    // like SymPy's xreplace: a power with an integer exponent is replaced whole,
    // so powers inside its base keep their exponents
    const fix = (x: Expr): Expr => {
      if (x instanceof Pow && x.exp instanceof Rational && x.exp.isInteger) return new Pow(x.base, float(x.exp, n));
      const args = x.args.map(fix);
      if (!args.some((a, i) => a !== x.args[i])) return x;
      return x instanceof Pow ? pow(...pair(args)) : rebuild(x, args);
    };
    rv = fix(rv);
  }
  return rv;
}

/** Are z1 and z2 equal within tolerance (SymPy comp)? */
export function comp(z1In: ExprLike, z2In: ExprLike, tol?: number | ''): boolean {
  let z1 = sympify(z1In);
  let z2 = sympify(z2In);
  if (z1 instanceof Rational && z1.isZero) [z1, z2] = [z2, z1];
  if (z1 instanceof Rational && z1.isZero) return true;
  if (tol === undefined || tol === '' || tol === 0) {
    if (tol === '') return z1.toString() === z2.toString();
    const fa = floats(z1);
    const fb = floats(z2);
    if (!fa.length && !fb.length) return z1.key === z2.key;
    const prec = Math.min(...[...fa, ...fb].map((f) => f.prec));
    const a = evalf(z1, F.precToDps(prec)).toNumber();
    const b = evalf(z2, F.precToDps(prec)).toNumber();
    const t = 10 ** F.precToDps(Math.min(fa.length ? Math.min(...fa.map((f) => f.prec)) : prec, fb.length ? Math.min(...fb.map((f) => f.prec)) : prec));
    return Math.trunc(Math.abs(a - b) * t) <= 5;
  }
  const a = z1.toNumber();
  const b = z2.toNumber();
  const diff = Math.abs(a - b);
  const az1 = Math.abs(a);
  if (b && az1 > 1) return diff / az1 <= tol;
  return diff <= tol;
}

function floats(e: Expr): Float[] {
  const out: Float[] = [];
  const go = (x: Expr) => {
    if (x instanceof Float) out.push(x);
    x.args.forEach(go);
  };
  go(e);
  return out;
}



/**
 * Find a simple closed form of a number (SymPy nsimplify): the value at 30
 * digits is identified by mpmath's identify (PSLQ) with the given constants;
 * with free symbols or `rational: true` the Floats are replaced by
 * Rationals. Ported from SymPy 1.14 simplify/simplify.py.
 */
export function nsimplify(
  exIn: ExprLike,
  opts: {
    /** Closed-form constants to try (SymPy `constants`), e.g. [pi, E]. */
    constants?: readonly ExprLike[];
    /** Accepted error; defaults to the least precision of the Floats (10**-15 for 15 digits). */
    tolerance?: number;
    /** A more extensive search (SymPy `full`). */
    full?: boolean;
    /** true: only replace Floats by Rationals; false: never fall back to Rationals; unset: SymPy None. */
    rational?: boolean;
    /** 'base10' (default): Floats from their decimal string; 'exact': their binary value. */
    rationalConversion?: 'base10' | 'exact';
  } = {},
): Expr {
  const e = sympify(exIn);
  if (e instanceof Rational && e.isInteger) return e;
  const conversion = opts.rationalConversion ?? 'base10';
  const { rational, full = false } = opts;
  // (a matrix expression such as 0.5*A is symbolic too: SymPy counts a MatrixSymbol as a free symbol)
  if (rational === true || e.freeSymbols().size > 0 || matrixValued(e)) return realToRational(e, opts.tolerance, conversion);
  // the least precision of the Floats sets the tolerance (Floats of 15 digits: 10**-15)
  const tolerance = opts.tolerance ?? Number(`1e-${Math.min(15, ...floats(e).map((f) => F.precToDps(f.prec)))}`);
  const prec = 30;
  const wp = F.dpsToPrec(prec); // mpmath mp.dps = 30
  const bprec = Math.trunc(prec * 3.33);
  const constants: [Mpf, string][] = [];
  for (const cIn of opts.constants ?? []) {
    const c = sympify(cIn);
    const v = evalf(c, prec);
    if (!(v instanceof Float)) throw new TypeError('constants must be real-valued');
    constants.push([F.round(v.mpf, bprec), c.toString()]);
  }
  constants.sort((a, b) => (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0));
  const parts = realImag(evalf(e, prec, { chop: true }));
  // not a number (an undefined function, ...)
  if (parts === undefined) return e;
  const simplifyReal = (x: Float): Expr | undefined => {
    const xv = F.round(x.mpf, bprec);
    if (tolerance === 0 && !full) {
      // happy with a simple fraction at low precision
      const rat = pslq([xv, ONE], 53);
      if (rat) return Rational.of(-at(rat, 1), at(rat, 0));
    }
    const found = identify(xv, constants, wp, { tol: F.fromNumber(tolerance), full });
    const s = found?.[0];
    if (s === undefined) return undefined;
    const r = parse(s);
    // don't let x become 0 (or infinite, as 1/log(1) for a huge x)
    if ((r instanceof Rational && r.isZero) || (r instanceof Special && r.isInfinite)) return undefined;
    return r;
  };
  const [re, im] = parts.map((x) => (x instanceof Float ? simplifyReal(x) : x));
  if (re === undefined || im === undefined) return rational === undefined ? realToRational(e, undefined, conversion) : e;
  const rv = add(re, mul(im, S.I));
  if (rv.key !== e.key || rational === false) return rv;
  return realToRational(e, undefined, conversion);
}

/** The expression contains a matrix-valued node (a MatrixSymbol, MatMul, ...). */
const matrixValued = (x: Expr): boolean => (x instanceof ExtensionExpr && !x.isScalar) || x.args.some(matrixValued);

/** [re, im] of an evaluated number as Floats or zeros, or undefined when it is not a finite number. */
function realImag(v: Expr): [Float | Rational, Float | Rational] | undefined {
  const num = (x: Expr | undefined): x is Float | Rational => x instanceof Float || x instanceof Rational;
  const imag = (x: Expr): Float | Rational | undefined => {
    const c = x.args[0];
    if (!(x instanceof Mul) || x.args.length !== 2 || x.args[1] !== S.I || !num(c)) return undefined;
    return c;
  };
  if (num(v)) return [v, S.Zero];
  const iv = imag(v);
  if (iv) return [S.Zero, iv];
  if (v instanceof Add && v.args.length === 2) {
    const [a, b] = pair(v.args);
    const ib = imag(b);
    if (num(a) && ib) return [a, ib];
  }
  return undefined;
}

/**
 * Replace the Floats of e by Rationals (SymPy _real_to_rational): within the
 * tolerance, from the exact binary value, or from the decimal string.
 */
function realToRational(e: Expr, tolerance: number | undefined, conversion: 'base10' | 'exact'): Expr {
  const reduceNum = tolerance !== undefined && tolerance < 1 ? BigInt(Math.ceil(1 / tolerance)) : undefined;
  const reps: [Expr, Expr][] = [];
  for (const fl of floats(e)) {
    if (reps.some(([k]) => k.key === fl.key)) continue;
    const exact = (): Rational => Rational.of(...F.toRational(fl.mpf));
    let r: Expr;
    if (reduceNum !== undefined) r = limitDenominator(exact(), reduceNum);
    else if (tolerance !== undefined && tolerance >= 1 && !isIntegral(fl)) {
      // tolerance*round(fl/tolerance), rounded half to even like SymPy Float.__round__
      const q = F.div(fl.mpf, F.fromNumber(tolerance), fl.prec);
      const k = roundHalfEven(q);
      const v = Number.isInteger(tolerance) ? Rational.of(BigInt(tolerance) * k) : Rational.of(...F.toRational(F.mul(F.fromNumber(tolerance), F.fromInt(k), fl.prec)));
      r = limitDenominator(v, BigInt(Math.trunc(tolerance)));
    } else if (conversion === 'exact') r = exact();
    else {
      r = nsimplify(fl, { rational: false });
      if (!fl.isZero && r instanceof Rational && r.isZero) r = exact();
      else if (!(r instanceof Rational)) r = decimalRational(fl);
    }
    reps.push([fl, r]);
  }
  return reps.length ? xreplace(e, reps) : e;
}

const isIntegral = (f: Float): boolean => f.mpf.exp >= 0n || f.mpf.man === 0n;

function roundHalfEven(x: Mpf): bigint {
  const fl = F.floor(x);
  const d = F.sub(x, F.fromInt(fl));
  const c = F.cmp(d, { man: 1n, exp: -1n });
  return c > 0 || (c === 0 && (fl & 1n) === 1n) ? fl + 1n : fl;
}

/** Rational(str(fl/d))*d with d = 10**int(log10|fl|) (the base-10 branch of SymPy _real_to_rational). */
function decimalRational(fl: Float): Rational {
  const a = F.abs(fl.mpf);
  const k = Math.trunc(F.toNumber(F.div(M.log(a, 53), M.log(F.fromInt(10n), 53), 53)));
  const d = k >= 0 ? Rational.of(10n ** BigInt(k)) : Rational.of(1n, 10n ** BigInt(-k));
  const scaled = F.div(a, F.fromRational(d.p, d.q, fl.prec), fl.prec);
  const s = F.floatToString(scaled, fl.prec, false);
  const [int = '', frac = ''] = s.split('.');
  const r = Rational.of(BigInt(int + frac) * (fl.mpf.man < 0n ? -1n : 1n) * d.p, 10n ** BigInt(frac.length) * d.q);
  return r;
}
