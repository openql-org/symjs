// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Numerical roots of a univariate polynomial (SymPy nroots):
 * Durand-Kerner in double precision followed by arbitrary-precision
 * Newton refinement, sorted like SymPy (real roots first).
 */

import { Expr, ExprLike, Float, Rational, S, Sym } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import * as F from '../numeric/mpf';
import * as M from '../numeric/mpfun';
import type { Mpc } from '../numeric/mpfun';
import { Poly } from './sympoly';
import { evalAdaptive } from '../numeric/mpeval';
import { freeSymbols } from '../core/traverse';

type C = { re: number; im: number };
const cm = (a: C, b: C): C => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
const cs = (a: C, b: C): C => ({ re: a.re - b.re, im: a.im - b.im });
const cdv = (a: C, b: C): C => {
  const d = b.re * b.re + b.im * b.im;
  return { re: (a.re * b.re + a.im * b.im) / d, im: (a.im * b.re - a.re * b.im) / d };
};

function durandKerner(coeffs: C[]): C[] {
  const n = coeffs.length - 1;
  const lc = coeffs[0]!;
  const a = coeffs.map((c) => cdv(c, lc));
  const evalP = (z: C): C => a.reduce<C>((acc, c) => ({ re: acc.re * z.re - acc.im * z.im + c.re, im: acc.re * z.im + acc.im * z.re + c.im }), { re: 0, im: 0 });
  let z: C[] = Array.from({ length: n }, (_, k) => {
    const r = 0.4;
    const t = 0.9;
    let p: C = { re: 1, im: 0 };
    for (let i = 0; i < k; i++) p = cm(p, { re: r, im: t });
    return p;
  });
  for (let it = 0; it < 500; it++) {
    let delta = 0;
    z = z.map((zi, i) => {
      let den: C = { re: 1, im: 0 };
      z.forEach((zj, j) => {
        if (j !== i) den = cm(den, cs(zi, zj));
      });
      const step = cdv(evalP(zi), den);
      delta = Math.max(delta, Math.hypot(step.re, step.im));
      return cs(zi, step);
    });
    if (delta < 1e-15) break;
  }
  return z;
}

/** Newton refinement of a root at the given binary precision. */
function refine(coeffs: Expr[], z0: C, prec: number): Mpc {
  const wp = prec + 30;
  const cf: Mpc[] = coeffs.map((c) => (c instanceof Rational ? [F.fromRational(c.p, c.q, wp), F.ZERO] : evalAdaptive(c, wp, () => undefined)));
  const dcf: Mpc[] = cf.slice(0, -1).map((c, i) => M.cmul(c, [F.fromInt(BigInt(cf.length - 1 - i)), F.ZERO], wp));
  const horner = (cs0: Mpc[], z: Mpc): Mpc => cs0.reduce<Mpc>((acc, c) => M.cadd(M.cmul(acc, z, wp), c, wp), M.C0);
  let z: Mpc = [F.fromNumber(z0.re), F.fromNumber(z0.im)];
  for (let i = 0; i < 200; i++) {
    const d = horner(dcf, z);
    if (F.isZero(d[0]) && F.isZero(d[1])) break;
    const step = M.cdiv(horner(cf, z), d, wp);
    z = M.csub(z, step, wp);
    const mag = Math.max(F.mag(step[0]), F.mag(step[1]));
    if (mag < Math.max(F.mag(z[0]), F.mag(z[1]), -wp) - wp) break;
  }
  return z;
}

/** Numerical roots to n digits. */
export function nroots(fIn: ExprLike | Poly, n = 15, x?: Sym): Expr[] {
  let p = fIn instanceof Poly ? fIn : Poly.from(sympify(fIn), x ? [x] : undefined);
  // numeric generators such as sqrt(2) belong to the coefficients
  const syms = p.gens.filter((g) => freeSymbols(g).size > 0);
  if (syms.length === 1 && p.gens.length > 1) p = Poly.from(p.asExpr(), syms);
  const coeffs = p.allCoeffs().map((c) => {
    if (!(c instanceof Rational) && freeSymbols(c).size > 0) throw new Error('nroots: numeric coefficients expected');
    return c;
  });
  const prec = F.dpsToPrec(n);
  const approx = durandKerner(coeffs.map((c) => (c instanceof Rational ? { re: c.value, im: 0 } : c.toComplex())));
  const roots = approx.map((z) => refine(coeffs, z, prec));
  const tol = -prec + 4;
  const items = roots.map((r) => {
    const reMag = F.mag(r[0]);
    const imMag = F.mag(r[1]);
    const isReal = F.isZero(r[1]) || imMag < Math.max(reMag, 0) + tol || imMag < tol;
    return { r, isReal, re: F.toNumber(r[0]), im: isReal ? 0 : F.toNumber(r[1]) };
  });
  items.sort((a, b) => (a.isReal ? 0 : 1) - (b.isReal ? 0 : 1) || a.re - b.re || Math.abs(a.im) - Math.abs(b.im) || Math.sign(a.im) - Math.sign(b.im));
  return items.map(({ r, isReal }) => {
    const re = F.isZero(r[0]) || F.mag(r[0]) < tol ? S.Zero : new Float(r[0], prec);
    if (isReal) return re instanceof Float ? re : new Float(F.ZERO, prec);
    return add(re, mul(new Float(r[1], prec), S.I));
  });
}
