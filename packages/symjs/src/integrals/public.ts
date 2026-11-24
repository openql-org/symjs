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
 * The integral of the rational function f in x (f may be given as
 * [numerator, denominator]); NoMatch when f is not a rational function of x or the roots of the
 * logarithmic part cannot be written. With `real: false` the logarithms are not turned into real
 * arctangents (by default they are when the other symbols are real).
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @param opts - `real` controls real logarithms and arctangents.
 * @returns The rational-function integral, or `NoMatch`.
 * @see SymPy `sympy.integrals.rationaltools.ratint`
 * @example
 * ```ts
 * import { ex, ratint, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * ratint(ex`1/(x**2 + 1)`, x); // => atan(x)
 * ratint(ex`1/(x**2 + 1)`, x, { real: false }); // => -I*log(x - I)/2 + I*log(x + I)/2
 * ```
 */
export const ratint = (f: ExprLike | readonly [ExprLike, ExprLike], x: Sym, opts: { real?: boolean } = {}): Expr | NoMatchResult =>
  orNoMatch(RT.ratint(isPair(f) ? div(f[0], f[1]) : sympify(f), x, opts));

const isPair = (f: ExprLike | readonly [ExprLike, ExprLike]): f is readonly [ExprLike, ExprLike] => Array.isArray(f);

/**
 * The logarithmic part of the integral
 * of f/g as pairs [s, q] with integral(f/g) = sum over the roots a of q(t) of
 * a*log(s(x, a)); `t` is a new Dummy by default.
 *
 * @remarks SymPy returns `[(Poly(x + 3*_t/2 + 1/2, x, domain='QQ[_t]'), Poly(3*_t**2 + 1, _t, domain='ZZ'))]`.
 *
 * @param f - The numerator polynomial.
 * @param g - The denominator polynomial.
 * @param x - The integration variable.
 * @param t - The auxiliary residue variable.
 * @returns Pairs of polynomials defining the logarithmic terms.
 * @see SymPy `sympy.integrals.rationaltools.ratint_logpart`
 * @example
 * ```ts
 * import { Poly, ex, ratintLogpart, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * ratintLogpart(Poly.from(ex`1`, [x]), Poly.from(ex`x**2 + x + 1`, [x]), x); // => [[Poly(x + 3*_t/2 + 1/2, x, domain='QQ[_t]'), Poly(3*_t**2 + 1, _t, domain='ZZ')]]
 * ```
 */
export const ratintLogpart = (f: Poly | ExprLike, g: Poly | ExprLike, x: Sym, t: Sym = new Dummy('t')): [Poly, Poly][] =>
  RT.ratintLogpart(f instanceof Poly ? f : Poly.from(f, [x]), g instanceof Poly ? g : Poly.from(g, [x]), x, t);

/**
 * The sum over the roots a of q of
 * a*log(h(x, a)) with real functions; NoMatch when the real roots are not
 * found.
 *
 * @param h - The polynomial inside the logarithm.
 * @param q - The polynomial defining its residues.
 * @param x - The integration variable.
 * @param t - The residue variable.
 * @returns The corresponding real logarithms and arctangents, or `NoMatch`.
 * @see SymPy `sympy.integrals.rationaltools.log_to_real`
 * @example
 * ```ts
 * import { Poly, ex, logToReal, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * logToReal(Poly.from(ex`x**2 - 1`, [x]), Poly.from(ex`1 - 2*y`, [y]), x, y); // => log(x**2 - 1)/2
 * ```
 */
export const logToReal = (h: Poly, q: Poly, x: Sym, t: Sym): Expr | NoMatchResult => orNoMatch(RT.logToReal(h, q, x, t));

/**
 * The integral of sin(a*x)**n*cos(a*x)**m (and of
 * the functions rewritten to that form); NoMatch when f has another form.
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.trigonometry.trigintegrate`
 * @example
 * ```ts
 * import { ex, symbols, trigintegrate } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * trigintegrate(ex`sin(x)**2`, x); // => x/2 - sin(x)*cos(x)/2
 * ```
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
 * The integral of an expression containing
 * DiracDelta; NoMatch when the method does not apply.
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.deltafunctions.deltaintegrate`
 * @example
 * ```ts
 * import { deltaintegrate, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * deltaintegrate(ex`x*DiracDelta(x - 1)`, x); // => Heaviside(x - 1)
 * ```
 */
export const deltaintegrate = (f: ExprLike, x: Sym): Expr | NoMatchResult => orNoMatch(DF.deltaintegrate(sympify(f), x));

/**
 * Separates a simple Dirac delta factor from the remaining factors of a product. If no factor can be isolated, the second entry contains the expanded product or `NoMatch` when expansion has no effect.
 *
 * @remarks SymPy returns `(DiracDelta(x), x*y*cos(x))`.
 *
 * @param node - The product to search for a simple delta factor.
 * @param x - The integration variable.
 * @returns The isolated delta factor and the remaining product, with `NoMatch` for a missing part.
 * @see SymPy `sympy.integrals.deltafunctions.change_mul`
 * @example
 * ```ts
 * import { changeMul, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * changeMul(ex`x*y*cos(x)*DiracDelta(x)`, x); // => [DiracDelta(x), x*y*cos(x)]
 * ```
 */
export function changeMul(node: ExprLike, x: Sym): [Expr | NoMatchResult, Expr | NoMatchResult] {
  const [dirac, rest] = DF.changeMul(sympify(node), x);
  return [orNoMatch(dirac), orNoMatch(rest)];
}

/**
 * Integrates over a real interval by rewriting the integrand in terms of Meijer G-functions.
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @param a - The lower integration limit.
 * @param b - The upper integration limit.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.meijerint.meijerint_definite`
 * @example
 * ```ts
 * import { meijerintDefinite, ex, S, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * meijerintDefinite(ex`exp(-x**2)`, x, S.NegativeInfinity, S.Infinity); // => [sqrt(pi), True]
 * ```
 */
export const meijerintDefinite = (f: ExprLike, x: Sym, a: ExprLike, b: ExprLike): [Expr, Expr] | NoMatchResult => orNoMatch(MI.meijerintDefinite(f, x, a, b));

/**
 * An antiderivative of f by Meijer
 * G-functions; NoMatch when f cannot be rewritten.
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.meijerint.meijerint_indefinite`
 * @example
 * ```ts
 * import { meijerintIndefinite, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * meijerintIndefinite(ex`sin(x)`, x); // => -cos(x)
 * ```
 */
export const meijerintIndefinite = (f: ExprLike, x: Sym): Expr | NoMatchResult => orNoMatch(MI.meijerintIndefinite(f, x));

/**
 * The inverse Laplace transform of f,
 * Piecewise((F(t), cond), (InverseLaplaceTransform(f, x, t, None), True));
 * NoMatch when f cannot be rewritten or the condition is False.
 *
 * @param f - The integrand.
 * @param x - The transform variable.
 * @param t - The time variable of the inverse transform.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.meijerint.meijerint_inversion`
 * @example
 * ```ts
 * import { meijerintInversion, ex, symbols } from '@symjs/symjs';
 *
 * const [x, t] = symbols('x t');
 * meijerintInversion(ex`1/x`, x, t); // => Heaviside(t)
 * ```
 */
export function meijerintInversion(f: ExprLike, x: Sym, t: Sym): Expr | NoMatchResult {
  const fe = sympify(f);
  const r = MI.meijerintInversion(fe, x, t);
  if (r === undefined) return NoMatch;
  return piecewise(r, [new InverseLaplaceTransform(fe, x, t), S.true]);
}

/**
 * The set of the functional components of f (its
 * symbols, function applications and non-integer powers, a rational power
 * with its minimal positive exponent).
 *
 * @param f - The expression to decompose into functional components.
 * @param x - The integration variable.
 * @returns The distinct components depending on the integration variable.
 * @see SymPy `sympy.integrals.heurisch.components`
 * @example
 * ```ts
 * import { components, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * components(ex`sin(x)*cos(x)**2`, x); // => {x, sin(x), cos(x)}
 * ```
 */
export const components = (f: ExprLike, x: Sym): SetExpr => finiteSet(...HE.componentsOf(sympify(f), x));

/**
 * An antiderivative by the heuristic Risch algorithm;
 * NoMatch when none is found (not a proof that none is elementary).
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @param opts - The heurisch settings.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.heurisch.heurisch`
 * @example
 * ```ts
 * import { heurisch, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * heurisch(ex`cos(n*x)`, x); // => sin(n*x)/n
 * ```
 */
export const heurisch = (f: ExprLike, x: Sym, opts: HeurischOptions = {}): Expr | NoMatchResult => orNoMatch(HE.heurisch(sympify(f), x, opts));

/**
 * Heurisch with the special cases where a
 * symbolic denominator of the result vanishes, as a Piecewise; NoMatch when
 * heurisch finds no antiderivative.
 *
 * @param f - The integrand.
 * @param x - The integration variable.
 * @param opts - The heurisch settings.
 * @returns The antiderivative, or `NoMatch` when the method does not apply.
 * @see SymPy `sympy.integrals.heurisch.heurisch_wrapper`
 * @example
 * ```ts
 * import { heurischWrapper, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * heurischWrapper(ex`cos(n*x)`, x); // => Piecewise((sin(n*x)/n, Ne(n, 0)), (x, True))
 * ```
 */
export const heurischWrapper = (f: ExprLike, x: Sym, opts: HeurischOptions = {}): Expr | NoMatchResult => orNoMatch(HE.heurischWrapper(sympify(f), x, opts));
