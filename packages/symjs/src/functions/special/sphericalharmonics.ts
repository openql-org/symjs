// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Spherical harmonics (SymPy functions/special/spherical_harmonics.py):
 * Ynm, Ynm_c and the real harmonics Znm, with SymPy's evaluation rules,
 * derivatives, conjugate, expand_func and numerics (mpmath spherharm).
 *
 * Ported from SymPy 1.14 and mpmath 1.3.0 (BSD 3-Clause, see LICENSE).
 */

import { NotImplementedError } from '../../core/errors';
import { at } from '../../core/guard';
import { isNegative, isPositive, isZero } from '../../core/assumptions';
import type { ComplexValue, Expr, ExprLike } from '../../core/nodes';
import { S } from '../../core/nodes';
import { add, couldExtractMinusSign, exp, mul, neg, pow, sqrt } from '../../core/ops';
import { xreplace } from '../../core/traverse';
import { fnPartials } from '../../calculus/diff';
import { numericFns } from '../../numeric/evalf';
import { mpFns } from '../../numeric/mpeval';
import * as F from '../../numeric/mpf';
import type { Mpc } from '../../numeric/mpfun';
import { mpSpherharm } from '../../numeric/mpspherharm';
import { conjugate, conjugateRules, cos, evaluators, fn, sin } from '../elementary/elementary';
import { funcExpanders } from './special';

const four = (args: readonly Expr[]): [Expr, Expr, Expr, Expr] => [at(args, 0), at(args, 1), at(args, 2), at(args, 3)];

/** SymPy Ynm.eval: pull the sign out of m, theta and phi. */
evaluators.Ynm = (n, ...rest) => {
  const [m, t, p] = [at(rest, 0), at(rest, 1), at(rest, 2)];
  if (couldExtractMinusSign(m)) {
    const mm = neg(m);
    return mul(pow(-1, mm), exp(mul(-2, S.I, mm, p)), fn('Ynm', [n, mm, t, p]));
  }
  if (couldExtractMinusSign(t)) return fn('Ynm', [n, m, neg(t), p]);
  if (couldExtractMinusSign(p)) {
    const pp = neg(p);
    return mul(exp(mul(-2, S.I, m, pp)), fn('Ynm', [n, m, t, pp]));
  }
  return undefined;
};

fnPartials.Ynm = (args, i) => {
  const [n, m, theta, phi] = four(args);
  const y = fn('Ynm', args);
  // d/dtheta Ynm = m*cot(theta)*Ynm + sqrt((n - m)*(n + m + 1))*exp(-I*phi)*Ynm(n, m + 1, theta, phi)
  if (i === 2) {
    return add(mul(m, fn('cot', [theta]), y), mul(sqrt(mul(add(n, neg(m)), add(n, m, 1))), exp(mul(-1, S.I, phi)), fn('Ynm', [n, add(m, 1), theta, phi])));
  }
  if (i === 3) return mul(S.I, m, y);
  throw new NotImplementedError(`diff: Ynm w.r.t. argument ${i + 1}`);
};

// conjugate(Ynm(n, m, theta, phi)) = (-1)**m*Ynm(n, -m, theta, phi) (for real theta and phi, as in SymPy)
conjugateRules.Ynm = (args) => {
  const [n, m, theta, phi] = four(args);
  return mul(pow(-1, m), fn('Ynm', [n, neg(m), theta, phi]));
};

// Ynm = sqrt((2n + 1)/(4 pi) (n - m)!/(n + m)!) exp(I m phi) assoc_legendre(n, m, cos(theta))
funcExpanders.Ynm = (args) => {
  const [n, m, theta, phi] = four(args);
  const rv = mul(
    sqrt(mul(add(mul(2, n), 1), pow(mul(4, S.Pi), -1), fn('factorial', [add(n, neg(m))]), pow(fn('factorial', [add(n, m)]), -1))),
    exp(mul(S.I, m, phi)),
    fn('assoc_legendre', [n, m, cos(theta)]),
  );
  // (theta is in [0, pi])
  return xreplace(rv, [[sqrt(add(1, mul(-1, pow(cos(theta), 2)))), sin(theta)]]);
};

/** SymPy Znm.eval: the real harmonics in terms of Ynm and its conjugate. */
evaluators.Znm = (n, ...rest) => {
  const m = at(rest, 0);
  const args = [n, ...rest];
  const y = fn('Ynm', args);
  const yc = conjugate(y);
  if (isPositive(m) === true) return mul(add(y, yc), pow(sqrt(2), -1));
  if (isZero(m) === true) return y;
  if (isNegative(m) === true) return mul(add(y, neg(yc)), pow(mul(sqrt(2), S.I), -1));
  return undefined;
};

// ---- numerics (mpmath spherharm) ------------------------------------------------------

mpFns.Ynm = mpSpherharm;
numericFns.Ynm = (args) => {
  const v = mpSpherharm(
    args.map((a: ComplexValue): Mpc => [F.fromNumber(a.re), F.fromNumber(a.im)]),
    53,
  );
  return { re: F.toNumber(v[0]), im: F.toNumber(v[1]) };
};

// ---- public API ---------------------------------------------------------------------

/** SymPy Ynm(n, m, theta, phi): the spherical harmonic Y_n^m. */
export const Ynm = (n: ExprLike, m: ExprLike, theta: ExprLike, phi: ExprLike): Expr => fn('Ynm', [n, m, theta, phi]);
/** SymPy Ynm_c(n, m, theta, phi) = conjugate(Ynm(n, m, theta, phi)): the conjugate spherical harmonic. */
export const YnmC = (n: ExprLike, m: ExprLike, theta: ExprLike, phi: ExprLike): Expr => conjugate(Ynm(n, m, theta, phi));
/** SymPy Znm(n, m, theta, phi): the real spherical harmonic. */
export const Znm = (n: ExprLike, m: ExprLike, theta: ExprLike, phi: ExprLike): Expr => fn('Znm', [n, m, theta, phi]);
