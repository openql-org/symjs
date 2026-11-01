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


