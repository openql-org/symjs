// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file nfloat and comp (SymPy core.function.nfloat, core.numbers.comp).
 */

import { Dummy, Expr, ExprLike, Float, Pow, Rational } from '../core/nodes';
import { pow, sympify } from '../core/ops';
import { rebuild, xreplace } from '../core/traverse';
import { evalf } from './evalf';
import { float } from './floatctor';
import * as F from './mpf';
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
    const fix = (x: Expr): Expr => {
      const args = x.args.map(fix);
      const y = args.some((a, i) => a !== x.args[i]) ? (x instanceof Pow ? pow(args[0]!, args[1]!) : rebuild(x, args)) : x;
      if (y instanceof Pow && y.exp instanceof Rational && y.exp.isInteger) return new Pow(y.base, float(y.exp, n));
      return y;
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
  if (!tol) {
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



/** Simplest rational within a relative tolerance of v (continued fractions). */
function simpleRational(v: number, rtol: number): Rational | undefined {
  if (!Number.isFinite(v)) return undefined;
  const sign = v < 0 ? -1n : 1n;
  let x = Math.abs(v);
  let [h0, h1, k0, k1] = [0n, 1n, 1n, 0n];
  for (let i = 0; i < 40; i++) {
    const a = Math.floor(x);
    const A = BigInt(a);
    [h0, h1] = [h1, A * h1 + h0];
    [k0, k1] = [k1, A * k1 + k0];
    const approx = Number(h1) / Number(k1);
    if (Math.abs(approx - Math.abs(v)) <= rtol * Math.max(1, Math.abs(v))) return Rational.of(sign * h1, k1);
    const frac = x - a;
    if (frac < 1e-300) break;
    x = 1 / frac;
  }
  return undefined;
}

/**
 * Replace Floats by simple rationals (the rational part of SymPy nsimplify):
 * `tolerance` bounds the error, `rational: true` with `rationalConversion:
 * 'exact'` uses the exact binary value.
 */
export function nsimplify(exIn: ExprLike, opts: { tolerance?: number; rational?: boolean; rationalConversion?: 'base10' | 'exact' } = {}): Expr {
  const e = sympify(exIn);
  const conv = (f: Float): Expr => {
    if (opts.rationalConversion === 'exact') {
      const [p, q] = F.toRational(f.mpf);
      return Rational.of(p, q);
    }
    if (opts.tolerance !== undefined && opts.tolerance < 1) {
      const lim = BigInt(Math.ceil(1 / opts.tolerance));
      return limitDenominatorR(f, lim);
    }
    const r = simpleRational(f.value, 1e-14);
    return r ?? f;
  };
  if (e instanceof Float) return conv(e);
  if (!opts.rational && e.freeSymbols().size === 0 && !(e instanceof Rational) && opts.tolerance !== undefined) {
    // rational approximation of a constant, e.g. nsimplify(pi, tolerance=0.01) = 22/7
    // the simplest fraction within the tolerance (continued-fraction convergents)
    return simpleRational(e.toNumber(), opts.tolerance) ?? e;
  }
  const go = (x: Expr): Expr => {
    if (x instanceof Float) return conv(x);
    if (x.args.length === 0) return x;
    const args = x.args.map(go);
    return args.every((a, i) => a === x.args[i]) ? x : rebuild(x, args);
  };
  return go(e);
}

function limitDenominatorR(f: Float, lim: bigint): Rational {
  const [p, q] = F.toRational(f.mpf);
  return limitDenominator(Rational.of(p, q), lim);
}

