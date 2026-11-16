// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of the helpers of SymPy's integrators
 * (sympy.integrals.rationaltools, trigonometry, deltafunctions, meijerint;
 * docs/api-policy.md): where SymPy returns None the result is NoMatch, never
 * undefined.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Dummy, Fn, S } from '../core/nodes';
import { at } from '../core/guard';
import { piecewise } from '../core/logic';
import { div, mul, pow, sympify } from '../core/ops';
import { mapBottomUp } from '../core/traverse';
import { cos, sin } from '../functions/elementary/elementary';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, orNoMatch } from '../core/truth';
import { Poly } from '../polys/sympoly';
import * as RT from './rationaltools';
import * as TR from './trigonometry';
import * as DF from './deltafunctions';
import * as MI from './meijerint';
import { InverseLaplaceTransform } from './transforms/inverse-laplace';
import * as HE from './heurisch';
import type { HeurischOptions } from './heurisch';
import type { SetExpr } from '../sets/sets';
import { finiteSet } from '../sets/sets';
/**
 * SymPy ratint(f, x, real=None): the integral of the rational function f in x (f may be given as
 * [numerator, denominator]); NoMatch when f is not a rational function of x or the roots of the
 * logarithmic part cannot be written. With `real: false` the logarithms are not turned into real
 * arctangents (by default they are when the other symbols are real).
 *
 * @example
 * ratint(parse('1/(x**2 + 1)'), x)  // atan(x)
 * ratint(parse('1/(x**2 + 1)'), x, { real: false })  // -I*log(x - I)/2 + I*log(x + I)/2
 */
export const ratint = (f: ExprLike | readonly [ExprLike, ExprLike], x: Sym, opts: { real?: boolean } = {}): Expr | NoMatchResult =>
  orNoMatch(RT.ratint(isPair(f) ? div(f[0], f[1]) : sympify(f), x, opts));

const isPair = (f: ExprLike | readonly [ExprLike, ExprLike]): f is readonly [ExprLike, ExprLike] => Array.isArray(f);

/**
 * SymPy ratint_logpart(f, g, x, t=None): the logarithmic part of the integral
 * of f/g as pairs [s, q] with integral(f/g) = sum over the roots a of q(t) of
 * a*log(s(x, a)); `t` is a new Dummy by default.
 */
export const ratintLogpart = (f: Poly | ExprLike, g: Poly | ExprLike, x: Sym, t: Sym = new Dummy('t')): [Poly, Poly][] =>
  RT.ratintLogpart(f instanceof Poly ? f : Poly.from(f, [x]), g instanceof Poly ? g : Poly.from(g, [x]), x, t);

/**
 * SymPy log_to_real(h, q, x, t): the sum over the roots a of q of
 * a*log(h(x, a)) with real functions; NoMatch when the real roots are not
 * found (SymPy None).
 */
export const logToReal = (h: Poly, q: Poly, x: Sym, t: Sym): Expr | NoMatchResult => orNoMatch(RT.logToReal(h, q, x, t));

/**
 * SymPy trigintegrate(f, x): the integral of sin(a*x)**n*cos(a*x)**m (and of
 * the functions rewritten to that form); NoMatch when f has another form.
 *
 * @example
 * trigintegrate(parse('sin(x)**2'), x)  // x/2 - sin(x)*cos(x)/2
 */
export const trigintegrate = (f: ExprLike, x: Sym): Expr | NoMatchResult => {
  const g = rewriteSinCos(sympify(f));
  // sin(a*x)**0*cos(a*x)**0
  return g.equals(S.One) ? x : orNoMatch(TR.trigintegrate(g, x));
};

/** tan, cot, sec and csc written with sin and cos (SymPy f.rewrite('sincos') in trigintegrate). */
function rewriteSinCos(f: Expr): Expr {
  return mapBottomUp(f, (e) => {
    if (!(e instanceof Fn && e.args.length === 1)) return e;
    const a = at(e.args, 0);
    switch (e.name) {
      case 'tan':
        return mul(sin(a), pow(cos(a), -1));
      case 'cot':
        return mul(cos(a), pow(sin(a), -1));
      case 'sec':
        return pow(cos(a), -1);
      case 'csc':
        return pow(sin(a), -1);
      default:
        return e;
    }
  });
}

/**
 * SymPy deltaintegrate(f, x): the integral of an expression containing
 * DiracDelta; NoMatch when the method does not apply.
 *
 * @example
 * deltaintegrate(parse('x*DiracDelta(x - 1)'), x)  // Heaviside(x - 1)
 */
export const deltaintegrate = (f: ExprLike, x: Sym): Expr | NoMatchResult => orNoMatch(DF.deltaintegrate(sympify(f), x));

/**
 * SymPy change_mul(node, x): [the simple DiracDelta factor, the rest of the
 * product], or (without one) [NoMatch, the product with its DiracDelta
 * factors expanded], [NoMatch, NoMatch] when nothing changes.
 */
export function changeMul(node: ExprLike, x: Sym): [Expr | NoMatchResult, Expr | NoMatchResult] {
  const [dirac, rest] = DF.changeMul(sympify(node), x);
  return [orNoMatch(dirac), orNoMatch(rest)];
}

/**
 * SymPy meijerint_definite(f, x, a, b): [the integral of f over [a, b],
 * its convergence condition] by Meijer G-functions; NoMatch when f cannot
 * be rewritten.
 *
 * @example
 * meijerintDefinite(parse('exp(-x**2)'), x, S.NegativeInfinity, S.Infinity)  // [sqrt(pi), True]
 */
export const meijerintDefinite = (f: ExprLike, x: Sym, a: ExprLike, b: ExprLike): [Expr, Expr] | NoMatchResult => orNoMatch(MI.meijerintDefinite(f, x, a, b));

/**
 * SymPy meijerint_indefinite(f, x): an antiderivative of f by Meijer
 * G-functions; NoMatch when f cannot be rewritten.
 *
 * @example
 * meijerintIndefinite(parse('sin(x)'), x)  // -cos(x)
 */
export const meijerintIndefinite = (f: ExprLike, x: Sym): Expr | NoMatchResult => orNoMatch(MI.meijerintIndefinite(f, x));

/**
 * SymPy meijerint_inversion(f, x, t): the inverse Laplace transform of f,
 * Piecewise((F(t), cond), (InverseLaplaceTransform(f, x, t, None), True));
 * NoMatch when f cannot be rewritten or the condition is False.
 *
 * @example
 * meijerintInversion(parse('1/x'), x, t)  // Heaviside(t)
 */
export function meijerintInversion(f: ExprLike, x: Sym, t: Sym): Expr | NoMatchResult {
  const fe = sympify(f);
  const r = MI.meijerintInversion(fe, x, t);
  if (r === undefined) return NoMatch;
  return piecewise(r, [new InverseLaplaceTransform(fe, x, t), S.true]);
}

/**
 * SymPy components(f, x): the set of the functional components of f (its
 * symbols, function applications and non-integer powers, a rational power
 * with its minimal positive exponent).
 *
 * @example
 * components(parse('sin(x)*cos(x)**2'), x)  // {x, cos(x), sin(x)}
 */
export const components = (f: ExprLike, x: Sym): SetExpr => finiteSet(...HE.componentsOf(sympify(f), x));

/**
 * SymPy heurisch(f, x): an antiderivative by the heuristic Risch algorithm;
 * NoMatch when none is found (not a proof that none is elementary).
 *
 * @example
 * heurisch(parse('cos(n*x)'), x)  // sin(n*x)/n
 */
export const heurisch = (f: ExprLike, x: Sym, opts: HeurischOptions = {}): Expr | NoMatchResult => orNoMatch(HE.heurisch(sympify(f), x, opts));

/**
 * SymPy heurisch_wrapper(f, x): heurisch with the special cases where a
 * symbolic denominator of the result vanishes, as a Piecewise; NoMatch when
 * heurisch finds no antiderivative.
 *
 * @example
 * heurischWrapper(parse('cos(n*x)'), x)  // Piecewise((sin(n*x)/n, Ne(n, 0)), (x, True))
 */
export const heurischWrapper = (f: ExprLike, x: Sym, opts: HeurischOptions = {}): Expr | NoMatchResult => orNoMatch(HE.heurischWrapper(sympify(f), x, opts));
