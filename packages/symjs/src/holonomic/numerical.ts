// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (holonomic/numerical.py, with the parts of
// core/evalf.py and mpmath 1.3.0 libmp/libmpc.py its arithmetic goes
// through), Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause
// License, and Copyright (c) 2005-2023 Fredrik Johansson and mpmath
// contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Numerical integration of holonomic functions along a path of points
 * in the complex plane (SymPy sympy.holonomic.numerical): Euler's method and
 * the Runge-Kutta method of order 4. The arithmetic is that of SymPy's
 * implementation (53-bit mpmath numbers, Python integers and SymPy Floats
 * combined, and SymPy's evalf of a quotient by a complex number), so the
 * values agree with SymPy's to the last bit.
 */

import { at, cast } from '../core/guard';
import { babs } from '../core/numbers';
import type { Expr } from '../core/nodes';
import { Add, Float, Mul, Rational, S } from '../core/nodes';
import { add, mul } from '../core/ops';
import type { Mpf } from '../numeric/mpf';
import { ONE, ZERO, add as fadd, bitLength, div as fdiv, fromInt, fromRational, mul as fmul, neg as fneg, normalize } from '../numeric/mpf';
import { evalfPrec } from '../numeric/evalf';
import type { DMF } from '../polys/domains';
import type { HolonomicFunction } from './holonomic';

const PREC = 53;

/** A number of the computation: a Python int (exact integer) or an mpmath mpf/mpc (im = 0 for a real one). */
interface Num {
  readonly re: Mpf;
  readonly im: Mpf;
  /** A Python int (SymPy's _to_mpmath gives ints for Integers). */
  readonly int: boolean;
}

const real = (re: Mpf, int = false): Num => ({ re, im: ZERO, int });
const isRealNum = (a: Num): boolean => a.im.man === 0n;
const isZeroNum = (a: Num): boolean => a.re.man === 0n && a.im.man === 0n;
const rnd = (a: Mpf, prec = PREC): Mpf => normalize(a.man, a.exp, prec);

/** a rounded toward zero to prec bits (mpmath round_down, the default round_fast); bigint division truncates toward zero. */
function truncate(a: Mpf, prec: number): Mpf {
  const n = Math.max(0, bitLength(babs(a.man)) - prec);
  return normalize(a.man / (1n << BigInt(n)), a.exp + BigInt(n), prec);
}

/** a/b rounded toward zero to prec bits. */
function divDown(a: Mpf, b: Mpf, prec: number): Mpf {
  const shift = Math.max(0, prec + 3 + bitLength(babs(b.man)) - bitLength(babs(a.man)));
  return truncate({ man: (a.man << BigInt(shift)) / b.man, exp: a.exp - b.exp - BigInt(shift) }, prec);
}

function nAdd(a: Num, b: Num): Num {
  if (a.int && b.int) return real(fadd(a.re, b.re), true);
  return { re: fadd(a.re, b.re, PREC), im: fadd(a.im, b.im, PREC), int: false };
}

/** The product (exact products of the parts, each part rounded once, as mpmath's mpc_mul). */
function nMul(a: Num, b: Num): Num {
  if (a.int && b.int) return real(fmul(a.re, b.re), true);
  const re = fadd(fmul(a.re, b.re), fneg(fmul(a.im, b.im)), PREC);
  const im = fadd(fmul(a.re, b.im), fmul(a.im, b.re), PREC);
  return { re, im, int: false };
}

/** a/n for a Python int n (true division: a float for two ints). */
function nDivInt(a: Num, n: bigint): Num {
  const d = fromInt(n);
  return { re: fdiv(a.re, d, PREC), im: a.im.man === 0n ? ZERO : fdiv(a.im, d, PREC), int: false };
}

const nMulInt = (a: Num, n: bigint): Num => nMul(a, real(fromInt(n), true));

/** a**n for an integer n >= 0 (exact, then each part rounded, as mpc_pow_int and mpf_pow_int). */
function nPowInt(a: Num, n: number): Num {
  if (a.int) return real(n === 0 ? ONE : { man: a.re.man ** BigInt(n), exp: a.re.exp * BigInt(n) }, true);
  let re = ONE;
  let im = ZERO;
  for (let k = 0; k < n; k++) [re, im] = [fadd(fmul(re, a.re), fneg(fmul(im, a.im))), fadd(fmul(re, a.im), fmul(im, a.re))];
  return { re: rnd(re), im: im.man === 0n ? ZERO : rnd(im), int: false };
}

/** The parts of the value of a number at a binary precision. */
function parts(e: Expr, prec: number): [Mpf, Mpf] {
  const v = evalfPrec(e, prec);
  let re = ZERO;
  let im = ZERO;
  // after evalf the terms are Floats c or c*I
  for (const t of v instanceof Add ? v.args : [v]) {
    if (t instanceof Mul) im = cast(at(t.args, 0), Float).mpf;
    else re = cast(t, Float).mpf;
  }
  return [re, im];
}

/**
 * SymPy _to_mpmath(53) of a number: an int for an Integer, otherwise the
 * value of evalf, whose parts are not rounded to 53 bits when a sum has a
 * single real or imaginary term (evalf_add evaluates the terms at 63 bits).
 */
function toNum(e: Expr): Num {
  if (e instanceof Rational) return e.isInteger ? real(fromInt(e.p), true) : real(fromRational(e.p, e.q, PREC));
  if (e instanceof Float) return real(rnd(e.mpf));
  if (!(e instanceof Add)) {
    const [re, im] = parts(e, PREC);
    return { re, im, int: false };
  }
  const res: Mpf[] = [];
  const ims: Mpf[] = [];
  for (const t of e.args) {
    const [re, im] = parts(t, PREC + 10);
    if (re.man !== 0n) res.push(re);
    if (im.man !== 0n) ims.push(im);
  }
  const sum = (l: readonly Mpf[]): Mpf => (l.length === 1 ? at(l, 0) : l.length ? rnd(l.reduce((u, v) => fadd(u, v))) : ZERO);
  return { re: sum(res), im: sum(ims), int: false };
}

/** SymPy sympify of a result: an Integer for an int, Floats otherwise (no imaginary part when it is zero). */
function fromNum(a: Num): Expr {
  if (a.int) return Rational.of(a.re.man * 2n ** BigInt(a.re.exp));
  const re = new Float(a.re, PREC);
  return isRealNum(a) ? re : add(re, mul(new Float(a.im, PREC), S.I));
}

/** p/q as SymPy computes the quotient of its sums of terms: Rational or Float division, or evalf of p*q**-1 for a complex q. */
function quotient(p: Num, q: Num): Num {
  if (isZeroNum(p) && p.int) return p;
  if (isRealNum(q)) {
    if (p.int && q.int) {
      const r = Rational.of(p.re.man * 2n ** BigInt(p.re.exp), q.re.man * 2n ** BigInt(q.re.exp));
      return r.isInteger ? real(fromInt(r.p), true) : real(fromRational(r.p, r.q, PREC));
    }
    if (isRealNum(p)) return real(fdiv(p.re, q.re, PREC));
    // Float*(a + b*I) distributes over the sum: each part times the rounded reciprocal
    const r = fdiv(ONE, q.re, PREC);
    return { re: fmul(p.re, r, PREC), im: fmul(p.im, r, PREC), int: false };
  }
  // evalf_mul of p*Pow(q, -1) at 53 bits: working precision 60, the reciprocal by mpc_reciprocal, rounding toward zero
  const wp = PREC + 7;
  const m = truncate(fadd(fmul(q.re, q.re), fmul(q.im, q.im)), wp + 10);
  const rre = divDown(q.re, m, wp);
  const rim = fneg(divDown(q.im, m, wp));
  if (isRealNum(p)) return { re: truncate(fmul(p.re, rre), wp), im: truncate(fmul(p.re, rim), wp), int: false };
  const A = truncate(fmul(rre, p.re), wp);
  const B = truncate(fmul(fneg(rim), p.im), wp);
  const C = truncate(fmul(rre, p.im), wp);
  const D = truncate(fmul(rim, p.re), wp);
  return { re: truncate(fadd(A, B), wp), im: truncate(fadd(C, D), wp), int: false };
}

/** DMFsubs(frac, x0, mpm=True) of SymPy: p(x0)/q(x0) with the coefficients as mpmath numbers. */
function dmfSubs(frac: DMF, x0: Num): Num {
  const value = (rep: readonly Expr[]): Num => {
    let s = real(ZERO, true);
    for (const [i, j] of [...rep].reverse().entries()) s = nAdd(s, nMul(toNum(frac.field.dom.toSympy(j)), nPowInt(x0, i)));
    return s;
  };
  return quotient(value(frac.num.rep), value(frac.den.rep));
}

type Method = (red: readonly DMF[], x0: Num, x1: Num, y0: readonly Num[], a: number) => Num[];

/** Euler's method from x0 to x1 (SymPy _euler). */
const euler: Method = (red, A, B, y0, a) => {
  const h = nAdd(B, nMul(A, real(fromInt(-1n), true)));
  const f0 = y0.slice(1);
  let f0n = real(ZERO, true);
  for (let i = 0; i < a; i++) f0n = nAdd(f0n, nMul(dmfSubs(at(red, i), A), at(y0, i)));
  f0.push(f0n);
  return y0.slice(0, a).map((y, i) => nAdd(y, nMul(h, at(f0, i))));
};

/** The Runge-Kutta method of order 4 from x0 to x1 (SymPy _rk4). */
const rk4: Method = (red, A, B, y0, a) => {
  const h = nAdd(B, nMul(A, real(fromInt(-1n), true)));
  const half = nDivInt(h, 2n);
  const stage = (f: readonly Num[], x: Num, step: (v: Num) => Num): Num[] => {
    const g = y0.slice(1, a).map((y, i) => nAdd(y, step(at(f, i + 1))));
    let n = real(ZERO, true);
    for (let i = 0; i < a; i++) n = nAdd(n, nMul(dmfSubs(at(red, i), x), nAdd(at(y0, i), step(at(f, i)))));
    g.push(n);
    return g;
  };
  const f0 = y0.slice(1);
  let f0n = real(ZERO, true);
  for (let i = 0; i < a; i++) f0n = nAdd(f0n, nMul(dmfSubs(at(red, i), A), at(y0, i)));
  f0.push(f0n);
  const mid = nAdd(A, half);
  const f1 = stage(f0, mid, (v) => nDivInt(nMul(v, h), 2n));
  const f2 = stage(f1, mid, (v) => nDivInt(nMul(v, h), 2n));
  const f3 = stage(f2, nAdd(A, h), (v) => nMul(v, h));
  return y0.slice(0, a).map((y, i) => {
    const s = nAdd(nAdd(nAdd(at(f0, i), nMulInt(at(f1, i), 2n)), nMulInt(at(f2, i), 2n)), at(f3, i));
    return nAdd(y, nDivInt(nMul(h, s), 6n));
  });
};

/**
 * The values of a holonomic function and its derivatives up to the order
 * minus one at the points of a path (SymPy numerical._evalf with
 * derivatives).
 */
export function evalfHolonomic(func: HolonomicFunction, points: readonly Expr[], method: 'RK4' | 'Euler' = 'RK4'): Expr[][] {
  const ann = func.annihilator;
  const a = ann.order;
  const K = ann.parent.base.getField();
  const meth = method === 'Euler' ? euler : rk4;
  const dmf = ann.listofpoly.map((j) => K.new(j));
  const red = dmf.slice(0, a).map((d) => d.neg().div(at(dmf, a)));
  const y0 = func.y0;
  if (!Array.isArray(y0) || y0.length < a) throw new TypeError('Not Enough Initial Conditions');
  let x0 = toNum(func.x0);
  let y = y0.map(toNum);
  const sol: Num[][] = [];
  for (const p of points) {
    const x1 = toNum(p);
    y = meth(red, x0, x1, y, a);
    sol.push(y);
    x0 = x1;
  }
  return sol.map((s) => s.map(fromNum));
}
