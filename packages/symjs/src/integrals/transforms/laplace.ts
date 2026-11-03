// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The Laplace transform (a port of sympy.integrals.laplace, the
 * forward part): the rule table of Bateman's Tables of Integral Transforms,
 * the program rules (time shift, frequency shift, time scaling,
 * differentiation, multiplication with t, trigonometric factors, Dirac
 * impulses), laplace_correspondence and laplace_initial_conds.
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { Sym } from '../../core/nodes';
import { Add, BoolAtom, Constant, Derivative, Dummy, ExtensionExpr, Float, Fn, Integral, Mul, Piecewise, Pow, Rational, Rel, S, UndefFn } from '../../core/nodes';
import { BoolOp, and, or } from '../../core/boolalg';
import { Eq, Ge, Gt, Le, Lt } from '../../core/logic';
import { add, exp, mul, neg, pow, sqrt, sub, sympify } from '../../core/ops';
import { isNegative, isPositive, isReal } from '../../core/assumptions';
import { asIndependent, asNumerDenom, asRealImag } from '../../core/methods';
import { mapBottomUp, some, subs, xreplace } from '../../core/traverse';
import { rebuild } from '../../core/traverse';
import type { UndefinedFunction } from '../../core/undef';
import { derivative } from '../../core/undef';
import { Subs } from '../../core/subsnode';
import { abs, arg, atan, cos, im, log, re, sin, sinh, cosh } from '../../functions/elementary';
import { asinh, coth, sinc } from '../../functions/trigext';
import { Ei, Max, digamma, erf, erfc, gamma, lowergamma, uppergamma } from '../../functions/special';
import { besseli, besselj, besselk, bessely } from '../../functions/bessel';
import { diff } from '../../calculus/diff';
import { Matrix } from '../../matrices/matrix';
import { Poly } from '../../polys/sympoly';
import { rootsDict } from '../../polys/poly';
import { collect } from '../../simplify/radsimp';
import { expand, expandMul, expand_trig as expandTrig } from '../../simplify/expand';
import { powsimp } from '../../simplify/powsimp';
import { cancel } from '../../simplify/rational';
import { rewrite } from '../../simplify/rewrite';
import { simplify as simplifyExpr } from '../../simplify/simplify';
import { piecewiseExclusive } from '../../solvers/inequalities';
import type { TransformHints } from './base';
import { IntegralTransform, addArgs, isFalseExpr, diffTransforms, holds, isPolyIn, maxPlane, planeAdd, matchByName, polyCoeffs, mget, mulArgs, wild, transformArgs, asSymbolVariable } from './base';
import { at, cast, defined, last, pair } from '../../core/guard';
import { DiracDelta, Heaviside, isDiracDelta, isHeaviside } from './delta';
import { InverseLaplaceTransform } from './inverse-laplace';

/** A Laplace transform result: (F, convergence abscissa, auxiliary condition). */
export type LaplaceTriple = [Expr, Expr, Expr];

const isExpPow = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const isTrig = (e: Expr): boolean => some(e, (n) => n instanceof Fn && (n.name === 'sin' || n.name === 'cos' || n.name === 'sinh' || n.name === 'cosh'));
const hasFn = (e: Expr, names: readonly string[]): boolean => some(e, (n) => (n instanceof Fn && names.includes(n.name)) || (names.includes('exp') && isExpPow(n)));
const sameExpr = (a: Expr, b: Expr): boolean => a.key === b.key;

/**
 * SymPy _laplace_deep_collect: write every subexpression that is a
 * polynomial in t as a polynomial (so that f(w*t - t) becomes f((w - 1)*t)).
 */
export function laplaceDeepCollect(f: Expr, t: Expr): Expr {
  if (f instanceof Rel || f instanceof BoolOp || f instanceof BoolAtom) return f;
  if (isPolyIn(f, t)) {
    try {
      return Poly.from(f, [t]).asExpr();
    } catch {
      // not a polynomial in the strict sense
    }
  }
  const args = f.args.map((a) => laplaceDeepCollect(a, t));
  return args.every((a, i) => a === f.args[i]) ? f : rebuild(f, args);
}

/** Combine products of absolute values: Abs(a)*Abs(b) -> Abs(a*b) (SymPy collect_abs). */
function collectAbs(e: Expr): Expr {
  return mapBottomUp(e, (x) => {
    if (!(x instanceof Mul)) return x;
    const absF = x.args.filter((f) => f instanceof Fn && f.name === 'abs');
    if (absF.length < 2) return x;
    const other = x.args.filter((f) => !(f instanceof Fn && f.name === 'abs'));
    return mul(...other, abs(mul(...absF.map((f) => at(f.args, 0)))));
  });
}

/**
 * Naively simplify the conditions in expr given that Re(s) > a (SymPy
 * _simplifyconds): |s**n| < c, c < |s**n| and Ne(c, s**n) are decided when
 * the bound a settles them.
 *
 * @internal
 */
export function simplifyConds(exprIn: ExprLike, s: Sym, aIn: ExprLike): Expr {
  const a = sympify(aIn);
  const power = (ex: Expr): Expr | undefined => {
    if (ex.key === s.key) return S.One;
    if (ex instanceof Pow && ex.base.key === s.key) return ex.exp;
    return undefined;
  };
  const isAbsFn = (e: Expr): e is Fn => e instanceof Fn && e.name === 'abs';
  // Abs(y) -> y; Abs(y)**n (symjs's form of Abs(y**n)) -> y**n
  const stripAbs = (e: Expr): Expr => (isAbsFn(e) ? at(e.args, 0) : e instanceof Pow && isAbsFn(e.base) ? pow(at(e.base.args, 0), e.exp) : e);
  const bigger = (ex1In: Expr, ex2In: Expr): boolean | undefined => {
    if (ex1In.has(s) && ex2In.has(s)) return undefined;
    const ex1 = stripAbs(ex1In);
    const ex2 = stripAbs(ex2In);
    if (ex1.has(s)) return bigger(pow(ex2, -1), pow(ex1, -1));
    const n = power(ex2);
    if (n === undefined) return undefined;
    // SymPy catches the TypeError of comparing a non-real n; symjs's relationals stay undecided instead
    const bound = pow(abs(a), n);
    if (bound.key === S.ComplexInfinity.key || bound.key === S.NaN.key) return undefined;
    if (holds(Gt(n, 0)) && holds(Le(abs(ex1), bound))) return false;
    if (holds(Lt(n, 0)) && holds(Ge(abs(ex1), bound))) return true;
    return undefined;
  };
  const isAbs = (e: Expr): boolean => isAbsFn(e) || (e instanceof Pow && isAbsFn(e.base));
  const replie = (x: Expr, y: Expr, orig: Expr): Expr => {
    if (!(isPositive(x) === true || isAbs(x)) || !(isPositive(y) === true || isAbs(y))) return orig;
    const r = bigger(x, y);
    if (r !== undefined) return r ? S.false : S.true;
    return orig;
  };
  const replue = (x: Expr, y: Expr, orig: Expr): Expr => {
    const b = bigger(x, y);
    return b === undefined ? orig : S.true;
  };
  let expr = collectAbs(sympify(exprIn));
  expr = mapBottomUp(expr, (e) => {
    if (!(e instanceof Rel)) return e;
    if (e.op === 'Lt') return replie(e.lhs, e.rhs, e);
    if (e.op === 'Gt') return replie(e.rhs, e.lhs, e);
    if (e.op === 'Ne') return replue(e.lhs, e.rhs, e);
    return e;
  });
  return expr;
}

// ---------------------------------------------------------------------------
// The rule table (SymPy _laplace_build_rules)
// ---------------------------------------------------------------------------

interface LaplaceRule {
  /** Time-domain pattern in tD with the Wilds a, b, n, tau, omega. */
  readonly pattern: Expr;
  /** Frequency-domain result in sD given the match. */
  readonly F: (m: ReadonlyMap<string, Expr>) => Expr;
  /** Condition for the rule to apply. */
  readonly check: (m: ReadonlyMap<string, Expr>) => Expr;
  /** Convergence abscissa. */
  readonly plane: (m: ReadonlyMap<string, Expr>) => Expr;
}

interface RuleTable {
  readonly rules: readonly LaplaceRule[];
  readonly t: Dummy;
  readonly s: Dummy;
}

let ruleTable: RuleTable | undefined;

function buildRules(): RuleTable {
  const t = new Dummy('t');
  const s = new Dummy('s');
  const a = wild('a', t);
  const b = wild('b', t);
  const n = wild('n', t);
  const tau = wild('tau', t);
  const omega = wild('omega', t);
  const g = (m: ReadonlyMap<string, Expr>, k: string): Expr => mget(m, k);
  const T = S.true;
  const Z = S.Zero;
  const r = (pattern: Expr, F: LaplaceRule['F'], check: LaplaceRule['check'], plane: LaplaceRule['plane']): LaplaceRule => ({ pattern, F, check, plane });
  const half = S.Half;
  const absArgLtPi = (x: Expr): Expr => Lt(abs(arg(x)), S.Pi);
  const pi = S.Pi;
  const rules: LaplaceRule[] = [
    // 4.2.1 (a constant) is applied by laplaceApplySimpleRules before the table
    r(t, () => pow(s, -2), () => T, () => Z), // 4.2.3
    r(pow(add(mul(a, t), b), -1), (m) => {
      const ba = mul(g(m, 'b'), pow(g(m, 'a'), -1));
      return mul(-1, exp(mul(-1, ba, s)), Ei(mul(-1, ba, s)), pow(g(m, 'a'), -1));
    }, (m) => absArgLtPi(mul(g(m, 'b'), pow(g(m, 'a'), -1))), () => Z), // 4.2.6
    r(pow(add(mul(a, t), b), S.NegHalf), (m) => {
      const ba = mul(g(m, 'b'), pow(g(m, 'a'), -1));
      return mul(sqrt(mul(g(m, 'a'), pi, pow(s, -1))), exp(mul(ba, s)), erfc(sqrt(mul(ba, s))), pow(g(m, 'a'), -1));
    }, (m) => absArgLtPi(mul(g(m, 'b'), pow(g(m, 'a'), -1))), () => Z), // 4.2.18
    r(pow(add(mul(a, t), b), Rational.of(-3n, 2n)), (m) => {
      const ba = mul(g(m, 'b'), pow(g(m, 'a'), -1));
      return sub(mul(2, pow(g(m, 'b'), S.NegHalf)), mul(2, pow(mul(pi, s, pow(g(m, 'a'), -1)), half), exp(mul(ba, s)), erfc(sqrt(mul(ba, s))), pow(g(m, 'a'), -1)));
    }, (m) => absArgLtPi(mul(g(m, 'b'), pow(g(m, 'a'), -1))), () => Z), // 4.2.20
    r(mul(sqrt(t), pow(add(t, b), -1)), (m) => sub(sqrt(mul(pi, pow(s, -1))), mul(pi, sqrt(g(m, 'b')), exp(mul(g(m, 'b'), s)), erfc(sqrt(mul(g(m, 'b'), s))))), (m) => absArgLtPi(g(m, 'b')), () => Z), // 4.2.22
    r(pow(add(mul(a, sqrt(t)), pow(t, Rational.of(3n, 2n))), -1), (m) => mul(pi, pow(g(m, 'a'), half), exp(mul(g(m, 'a'), s)), erfc(sqrt(mul(g(m, 'a'), s)))), () => T, () => Z),
    // SymPy's pattern is written with the float 3/2 = 1.5
    r(pow(add(mul(a, sqrt(t)), pow(t, new Float(1.5))), -1), (m) => mul(pi, pow(g(m, 'a'), half), exp(mul(g(m, 'a'), s)), erfc(sqrt(mul(g(m, 'a'), s)))), () => T, () => Z),
    r(pow(t, n), (m) => mul(gamma(add(g(m, 'n'), 1)), pow(pow(s, add(g(m, 'n'), 1)), -1)), (m) => Gt(g(m, 'n'), -1), () => Z), // 4.3.1
    r(pow(add(mul(a, t), b), n), (m) => {
      const ba = mul(g(m, 'b'), pow(g(m, 'a'), -1));
      return mul(uppergamma(add(g(m, 'n'), 1), mul(ba, s)), exp(mul(-1, ba, s)), pow(pow(s, add(g(m, 'n'), 1)), -1), pow(g(m, 'a'), -1));
    }, (m) => and(Gt(g(m, 'n'), -1), absArgLtPi(mul(g(m, 'b'), pow(g(m, 'a'), -1)))), () => Z), // 4.3.4
    r(mul(pow(t, n), pow(add(t, a), -1)), (m) => mul(pow(g(m, 'a'), g(m, 'n')), gamma(add(g(m, 'n'), 1)), uppergamma(neg(g(m, 'n')), mul(g(m, 'a'), s))), (m) => and(Gt(g(m, 'n'), -1), absArgLtPi(g(m, 'a'))), () => Z), // 4.3.7
    r(exp(sub(mul(a, t), tau)), (m) => mul(exp(neg(g(m, 'tau'))), pow(sub(s, g(m, 'a')), -1)), () => T, (m) => re(g(m, 'a'))), // 4.5.1
    r(mul(t, exp(sub(mul(a, t), tau))), (m) => mul(exp(neg(g(m, 'tau'))), pow(sub(s, g(m, 'a')), -2)), () => T, (m) => re(g(m, 'a'))), // 4.5.2
    r(mul(pow(t, n), exp(mul(a, t))), (m) => mul(gamma(add(g(m, 'n'), 1)), pow(pow(sub(s, g(m, 'a')), add(g(m, 'n'), 1)), -1)), (m) => Gt(re(g(m, 'n')), -1), (m) => re(g(m, 'a'))), // 4.5.3
    r(exp(mul(-1, a, pow(t, 2))), (m) => {
      const A = g(m, 'a');
      return mul(sqrt(mul(pi, pow(mul(4, A), -1))), exp(mul(pow(s, 2), pow(mul(4, A), -1))), erfc(mul(s, pow(sqrt(mul(4, A)), -1))));
    }, (m) => Gt(re(g(m, 'a')), 0), () => Z), // 4.5.21
    r(mul(t, exp(mul(-1, a, pow(t, 2)))), (m) => {
      const A = g(m, 'a');
      return sub(pow(mul(2, A), -1), mul(2, pow(sqrt(pi), -1), pow(pow(mul(4, A), Rational.of(3n, 2n)), -1), s, erfc(mul(s, pow(sqrt(mul(4, A)), -1)))));
    }, (m) => Gt(re(g(m, 'a')), 0), () => Z), // 4.5.22
    r(exp(mul(-1, a, pow(t, -1))), (m) => mul(2, sqrt(mul(g(m, 'a'), pow(s, -1))), besselk(1, mul(2, sqrt(mul(g(m, 'a'), s))))), (m) => Ge(re(g(m, 'a')), 0), () => Z), // 4.5.25
    r(mul(sqrt(t), exp(mul(-1, a, pow(t, -1)))), (m) => mul(half, sqrt(mul(pi, pow(s, -3))), add(1, mul(2, sqrt(mul(g(m, 'a'), s)))), exp(mul(-2, sqrt(mul(g(m, 'a'), s))))), (m) => Ge(re(g(m, 'a')), 0), () => Z), // 4.5.26
    r(mul(exp(mul(-1, a, pow(t, -1))), pow(sqrt(t), -1)), (m) => mul(sqrt(mul(pi, pow(s, -1))), exp(mul(-2, sqrt(mul(g(m, 'a'), s))))), (m) => Ge(re(g(m, 'a')), 0), () => Z), // 4.5.27
    r(mul(exp(mul(-1, a, pow(t, -1))), pow(mul(t, sqrt(t)), -1)), (m) => mul(sqrt(mul(pi, pow(g(m, 'a'), -1))), exp(mul(-2, sqrt(mul(g(m, 'a'), s))))), (m) => Gt(re(g(m, 'a')), 0), () => Z), // 4.5.28
    r(mul(pow(t, n), exp(mul(-1, a, pow(t, -1)))), (m) => {
      const N = g(m, 'n');
      return mul(2, pow(mul(g(m, 'a'), pow(s, -1)), mul(add(N, 1), half)), besselk(add(N, 1), mul(2, sqrt(mul(g(m, 'a'), s)))));
    }, (m) => Gt(re(g(m, 'a')), 0), () => Z), // 4.5.29
    r(exp(mul(-1, a, exp(neg(t)))), (m) => mul(pow(g(m, 'a'), neg(s)), lowergamma(s, g(m, 'a'))), () => T, () => Z), // 4.5.36
    r(exp(mul(-1, a, exp(t))), (m) => mul(pow(g(m, 'a'), s), uppergamma(neg(s), g(m, 'a'))), (m) => Gt(re(g(m, 'a')), 0), () => Z), // 4.5.37
    r(log(mul(a, t)), (m) => mul(-1, log(mul(exp(S.EulerGamma), s, pow(g(m, 'a'), -1))), pow(s, -1)), (m) => Gt(g(m, 'a'), 0), () => Z), // 4.6.1
    r(log(add(1, mul(a, t))), (m) => mul(-1, exp(mul(s, pow(g(m, 'a'), -1))), pow(s, -1), Ei(mul(-1, s, pow(g(m, 'a'), -1)))), (m) => absArgLtPi(g(m, 'a')), () => Z), // 4.6.4
    r(log(add(mul(a, t), b)), (m) => {
      const A = g(m, 'a');
      const B = g(m, 'b');
      return mul(sub(log(B), mul(exp(mul(s, pow(B, -1), pow(A, -1))), pow(s, -1), A, Ei(mul(-1, s, pow(B, -1))))), pow(s, -1), A);
    }, (m) => and(Gt(g(m, 'a'), 0), absArgLtPi(g(m, 'b'))), () => Z), // 4.6.5
    // 4.6.9, log(t)/sqrt(t) -> -sqrt(pi/s)*log(4*s*exp(EulerGamma)), is left out: SymPy never
    // applies it (a pattern without Wilds matches with the empty, falsy dict), so log(t)/sqrt(t)
    // goes to 4.6.11 with n = -1/2, which gives the same function written as SymPy writes it
    r(mul(pow(t, n), log(t)), (m) => {
      const N = g(m, 'n');
      return mul(gamma(add(N, 1)), pow(s, sub(neg(N), 1)), sub(digamma(add(N, 1)), log(s)));
    }, (m) => Gt(re(g(m, 'n')), -1), () => Z), // 4.6.11
    r(pow(log(mul(a, t)), 2), (m) => mul(add(pow(log(mul(exp(S.EulerGamma), s, pow(g(m, 'a'), -1))), 2), mul(pow(pi, 2), Rational.of(1n, 6n))), pow(s, -1)), (m) => Gt(g(m, 'a'), 0), () => Z), // 4.6.13
    r(sin(mul(omega, t)), (m) => mul(g(m, 'omega'), pow(add(pow(s, 2), pow(g(m, 'omega'), 2)), -1)), () => T, (m) => abs(im(g(m, 'omega')))), // 4.7.1
    r(abs(sin(mul(omega, t))), (m) => {
      const w = g(m, 'omega');
      return mul(w, pow(add(pow(s, 2), pow(w, 2)), -1), coth(mul(pi, s, pow(mul(2, w), -1))));
    }, (m) => Gt(g(m, 'omega'), 0), () => Z), // 4.7.2
    r(mul(sin(mul(omega, t)), pow(t, -1)), (m) => atan(mul(g(m, 'omega'), pow(s, -1))), () => T, (m) => abs(im(g(m, 'omega')))), // 4.7.16
    r(mul(pow(sin(mul(omega, t)), 2), pow(t, -1)), (m) => mul(log(add(1, mul(4, pow(g(m, 'omega'), 2), pow(s, -2)))), Rational.of(1n, 4n)), () => T, (m) => mul(2, abs(im(g(m, 'omega'))))), // 4.7.17
    r(mul(pow(sin(mul(omega, t)), 2), pow(t, -2)), (m) => {
      const w = g(m, 'omega');
      return sub(mul(w, atan(mul(2, w, pow(s, -1)))), mul(s, log(add(1, mul(4, pow(w, 2), pow(s, -2)))), Rational.of(1n, 4n)));
    }, () => T, (m) => mul(2, abs(im(g(m, 'omega'))))), // 4.7.20
    r(cos(mul(omega, t)), (m) => mul(s, pow(add(pow(s, 2), pow(g(m, 'omega'), 2)), -1)), () => T, (m) => abs(im(g(m, 'omega')))), // 4.7.43
    r(pow(cos(mul(omega, t)), 2), (m) => {
      const w = g(m, 'omega');
      return mul(add(pow(s, 2), mul(2, pow(w, 2))), pow(add(pow(s, 2), mul(4, pow(w, 2))), -1), pow(s, -1));
    }, () => T, (m) => mul(2, abs(im(g(m, 'omega'))))), // 4.7.45
    r(mul(sin(mul(a, t)), sin(mul(b, t))), (m) => {
      const A = g(m, 'a');
      const B = g(m, 'b');
      return mul(2, A, B, s, pow(add(pow(s, 2), pow(add(A, B), 2)), -1), pow(add(pow(s, 2), pow(sub(A, B), 2)), -1));
    }, () => T, (m) => add(abs(im(g(m, 'a'))), abs(im(g(m, 'b'))))), // 4.7.78
    r(mul(cos(mul(a, t)), sin(mul(b, t))), (m) => {
      const A = g(m, 'a');
      const B = g(m, 'b');
      return mul(B, add(pow(s, 2), neg(pow(A, 2)), pow(B, 2)), pow(add(pow(s, 2), pow(add(A, B), 2)), -1), pow(add(pow(s, 2), pow(sub(A, B), 2)), -1));
    }, () => T, (m) => add(abs(im(g(m, 'a'))), abs(im(g(m, 'b'))))), // 4.7.79
    r(mul(cos(mul(a, t)), cos(mul(b, t))), (m) => {
      const A = g(m, 'a');
      const B = g(m, 'b');
      return mul(s, add(pow(s, 2), pow(A, 2), pow(B, 2)), pow(add(pow(s, 2), pow(add(A, B), 2)), -1), pow(add(pow(s, 2), pow(sub(A, B), 2)), -1));
    }, () => T, (m) => add(abs(im(g(m, 'a'))), abs(im(g(m, 'b'))))), // 4.7.80
    r(sinh(mul(a, t)), (m) => mul(g(m, 'a'), pow(sub(pow(s, 2), pow(g(m, 'a'), 2)), -1)), () => T, (m) => abs(re(g(m, 'a')))), // 4.9.1
    r(cosh(mul(a, t)), (m) => mul(s, pow(sub(pow(s, 2), pow(g(m, 'a'), 2)), -1)), () => T, (m) => abs(re(g(m, 'a')))), // 4.9.2
    r(pow(sinh(mul(a, t)), 2), (m) => mul(2, pow(g(m, 'a'), 2), pow(sub(pow(s, 3), mul(4, pow(g(m, 'a'), 2), s)), -1)), () => T, (m) => mul(2, abs(re(g(m, 'a'))))), // 4.9.3
    r(pow(cosh(mul(a, t)), 2), (m) => mul(sub(pow(s, 2), mul(2, pow(g(m, 'a'), 2))), pow(sub(pow(s, 3), mul(4, pow(g(m, 'a'), 2), s)), -1)), () => T, (m) => mul(2, abs(re(g(m, 'a'))))), // 4.9.4
    r(mul(sinh(mul(a, t)), pow(t, -1)), (m) => mul(log(mul(add(s, g(m, 'a')), pow(sub(s, g(m, 'a')), -1))), half), () => T, (m) => abs(re(g(m, 'a')))), // 4.9.12
    r(mul(pow(t, n), sinh(mul(a, t))), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      return mul(gamma(add(N, 1)), half, sub(pow(sub(s, A), sub(neg(N), 1)), pow(add(s, A), sub(neg(N), 1))));
    }, (m) => Gt(g(m, 'n'), -2), (m) => abs(g(m, 'a'))), // 4.9.18
    r(mul(pow(t, n), cosh(mul(a, t))), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      return mul(gamma(add(N, 1)), half, add(pow(sub(s, A), sub(neg(N), 1)), pow(add(s, A), sub(neg(N), 1))));
    }, (m) => Gt(g(m, 'n'), -1), (m) => abs(g(m, 'a'))), // 4.9.19
    r(erf(mul(a, t)), (m) => {
      const A = g(m, 'a');
      return mul(exp(mul(pow(s, 2), pow(pow(mul(2, A), 2), -1))), erfc(mul(s, pow(mul(2, A), -1))), pow(s, -1));
    }, (m) => Lt(mul(4, abs(arg(g(m, 'a')))), pi), () => Z), // 4.12.2
    r(besselj(n, mul(a, t)), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      const q = sqrt(add(pow(s, 2), pow(A, 2)));
      return mul(pow(A, N), pow(mul(q, pow(add(s, q), N)), -1));
    }, (m) => Gt(re(g(m, 'n')), -1), (m) => abs(im(g(m, 'a')))), // 4.14.1
    r(mul(pow(t, b), besselj(n, mul(a, t))), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      return mul(pow(2, N), pow(sqrt(pi), -1), gamma(add(N, half)), pow(A, N), pow(add(pow(s, 2), pow(A, 2)), sub(neg(N), half)));
    }, (m) => and(Gt(re(g(m, 'n')), S.NegHalf), Eq(g(m, 'b'), g(m, 'n'))), (m) => abs(im(g(m, 'a')))), // 4.14.7
    r(mul(pow(t, b), besselj(n, mul(a, t))), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      return mul(pow(2, add(N, 1)), pow(sqrt(pi), -1), gamma(add(N, Rational.of(3n, 2n))), pow(A, N), s, pow(add(pow(s, 2), pow(A, 2)), sub(neg(N), Rational.of(3n, 2n))));
    }, (m) => and(Gt(re(g(m, 'n')), -1), Eq(g(m, 'b'), add(g(m, 'n'), 1))), (m) => abs(im(g(m, 'a')))), // 4.14.8
    r(besselj(0, mul(a, sqrt(add(pow(t, 2), mul(b, t))))), (m) => {
      const A = g(m, 'a');
      const B = g(m, 'b');
      const q = sqrt(add(pow(s, 2), pow(A, 2)));
      return mul(exp(sub(mul(B, s), mul(B, q))), pow(q, -1));
    }, (m) => absArgLtPi(g(m, 'b')), (m) => abs(im(g(m, 'a')))), // 4.15.19
    r(besseli(n, mul(a, t)), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      const q = sqrt(sub(pow(s, 2), pow(A, 2)));
      return mul(pow(A, N), pow(mul(q, pow(add(s, q), N)), -1));
    }, (m) => Gt(re(g(m, 'n')), -1), (m) => abs(re(g(m, 'a')))), // 4.16.1
    r(mul(pow(t, b), besseli(n, mul(a, t))), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      return mul(pow(2, N), pow(sqrt(pi), -1), gamma(add(N, half)), pow(A, N), pow(sub(pow(s, 2), pow(A, 2)), sub(neg(N), half)));
    }, (m) => and(Gt(re(g(m, 'n')), S.NegHalf), Eq(g(m, 'b'), g(m, 'n'))), (m) => abs(re(g(m, 'a')))), // 4.16.6
    r(mul(pow(t, b), besseli(n, mul(a, t))), (m) => {
      const N = g(m, 'n');
      const A = g(m, 'a');
      return mul(pow(2, add(N, 1)), pow(sqrt(pi), -1), gamma(add(N, Rational.of(3n, 2n))), pow(A, N), s, pow(sub(pow(s, 2), pow(A, 2)), sub(neg(N), Rational.of(3n, 2n))));
    }, (m) => and(Gt(re(g(m, 'n')), -1), Eq(g(m, 'b'), add(g(m, 'n'), 1))), (m) => abs(re(g(m, 'a')))), // 4.16.7
    r(bessely(0, mul(a, t)), (m) => {
      const A = g(m, 'a');
      return mul(-2, pow(pi, -1), asinh(mul(s, pow(A, -1))), pow(sqrt(add(pow(s, 2), pow(A, 2))), -1));
    }, () => T, (m) => abs(im(g(m, 'a')))), // 4.15.44
    r(besselk(0, mul(a, t)), (m) => {
      const A = g(m, 'a');
      const q = sqrt(sub(pow(s, 2), pow(A, 2)));
      return mul(log(mul(add(s, q), pow(A, -1))), pow(q, -1));
    }, () => T, (m) => neg(re(g(m, 'a')))), // 4.16.23
  ];
  return { rules, t, s };
}

function getRules(): RuleTable {
  ruleTable ??= buildRules();
  return ruleTable;
}

/** Split a linear argument b*t + c (b != 0 and c free of t); undefined otherwise. */
function linearIn(e: Expr, t: Expr): [Expr, Expr] | undefined {
  const cs = polyCoeffs(laplaceDeepCollect(e, t), t);
  return cs?.length === 2 ? pair(cs) : undefined;
}

/** The Heaviside and DiracDelta rules of the table (written out, as they need exact function heads). */
function laplaceDistributionRules(f: Expr, t: Expr, s: Expr): LaplaceTriple | undefined {
  const isH = isHeaviside(f) && f.args.length === 1;
  const isD = isDiracDelta(f) && f.args.length === 1;
  if (!isH && !isD) return undefined;
  const lin = linearIn(at(f.args, 0), t);
  if (!lin) return undefined;
  const [a, mb] = lin;
  const b = neg(mb);
  const ok = (c: Expr): boolean => holds(c);
  if (isD) {
    if (ok(or(and(Gt(a, 0), Ge(b, 0)), and(Lt(a, 0), Le(b, 0))))) return [mul(exp(mul(-1, s, b, pow(a, -1))), pow(abs(a), -1)), S.NegativeInfinity, S.true];
    if (ok(or(and(Lt(a, 0), Ge(b, 0)), and(Gt(a, 0), Le(b, 0))))) return [S.Zero, S.NegativeInfinity, S.true];
    return undefined;
  }
  if (ok(and(Gt(a, 0), Gt(b, 0)))) return [mul(exp(mul(-1, s, b, pow(a, -1))), pow(s, -1)), S.Zero, S.true];
  if (ok(and(Lt(a, 0), Lt(b, 0)))) return [mul(sub(1, exp(mul(-1, s, b, pow(a, -1)))), pow(s, -1)), S.Zero, S.true];
  if (ok(and(Gt(a, 0), Le(b, 0)))) return [pow(s, -1), S.Zero, S.true];
  if (ok(and(Lt(a, 0), Gt(b, 0)))) return [S.Zero, S.Zero, S.true];
  return undefined;
}

/** SymPy _laplace_apply_simple_rules. */
function laplaceApplySimpleRules(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  const { rules, t: tD, s: sD } = getRules();
  const prepF = laplaceDeepCollect(subs(f, [[t, tD]]), tD);
  // The distribution rules come second and third in SymPy's table, right after the constant rule
  if (!prepF.has(tD)) return [mul(prepF, pow(s, -1)), S.Zero, S.true];
  const dist = laplaceDistributionRules(prepF, tD, sD);
  if (dist) return [subs(dist[0], [[sD, s]]), dist[1], dist[2]];
  // the patterns contain no ExtensionExpr (DiracDelta, Heaviside, ...): a Wild would match such a function as a generic one
  if (some(prepF, (n) => n instanceof ExtensionExpr)) return undefined;
  for (const rule of rules) {
    const m = matchByName(prepF, rule.pattern);
    if (!m) continue;
    let c: Expr;
    try {
      c = rule.check(m);
    } catch {
      // SymPy skips a rule whose check raises TypeError, as ordering nan does (arg(0) is nan)
      continue;
    }
    if (holds(c)) return [subs(rule.F(m), [[sD, s]]), rule.plane(m), S.true];
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Program rules
// ---------------------------------------------------------------------------

/**
 * SymPy _laplace_rule_timescale: f(a*t) -> F(s/a)/a for a > 0. exp(a*t) never gets here: table
 * rule 4.5.1 transforms it for every a.
 */
function laplaceRuleTimescale(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  if (!((f instanceof Fn || f instanceof UndefFn || f instanceof ExtensionExpr) && f.args.length === 1 && !(f instanceof IntegralTransform))) return undefined;
  const a = wild('a', t);
  const m = matchByName(collect(at(f.args, 0), [t]), mul(a, t));
  if (!m) return undefined;
  const A = mget(m, 'a');
  if (isPositive(A) === true && A.key !== S.One.key) {
    const [r, pr, cr] = laplaceTransformImpl(mul(pow(A, -1), rebuild(f, [t])), t, mul(s, pow(A, -1)), false);
    return [r, pr, cr];
  }
  return undefined;
}

/** SymPy _laplace_rule_heaviside: time-shifted Heaviside factors. */
function laplaceRuleHeaviside(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  const facs = mulArgs(f);
  const i = facs.findIndex((x) => isHeaviside(x) && x.args.length === 1);
  if (i < 0) return undefined;
  const y = at(at(facs, i).args, 0);
  const g = mul(...facs.filter((_, j) => j !== i));
  const a = wild('a', t);
  const m1 = matchByName(y, sub(t, a));
  if (m1) {
    const A = mget(m1, 'a');
    if (isPositive(A) === true) {
      const [r, pr, cr] = laplaceTransformImpl(subs(g, [[t, add(t, A)]]), t, s, false);
      return [mul(exp(mul(-1, A, s)), r), pr, cr];
    }
    if (isNegative(A) === true) return laplaceTransformImpl(g, t, s, false);
  }
  const m2 = matchByName(y, sub(a, t));
  if (m2) {
    const A = mget(m2, 'a');
    if (isPositive(A) === true) return laplaceTransformImpl(mul(sub(1, Heaviside(sub(t, A))), g), t, s, false);
    if (isNegative(A) === true) return [S.Zero, S.Zero, S.true];
  }
  return undefined;
}

/** SymPy _laplace_rule_exp: exp(a*t)*f(t) -> F(s - a). */
function laplaceRuleExp(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  const facs = mulArgs(f);
  const i = facs.findIndex(isExpPow);
  if (i < 0) return undefined;
  const y = cast(at(facs, i), Pow, 'exp factor').exp;
  const z = mul(...facs.filter((_, j) => j !== i));
  const a = wild('a', t);
  const m = matchByName(collect(y, [t]), mul(a, t));
  if (!m) return undefined;
  const A = mget(m, 'a');
  const [r, pr, cr] = laplaceTransformImpl(z, t, sub(s, A), false);
  return [r, planeAdd(pr, re(A)), cr];
}

/** SymPy _laplace_rule_delta: the sifting property of DiracDelta. */
function laplaceRuleDelta(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  const facs = mulArgs(f);
  const i = facs.findIndex((x) => isDiracDelta(x) && x.args.length === 1);
  if (i < 0) return undefined;
  const y = at(at(facs, i).args, 0);
  const z = mul(...facs.filter((_, j) => j !== i));
  if (some(z, isDiracDelta)) return undefined;
  const lin = linearIn(y, t);
  if (lin) {
    const [b, ma] = lin;
    const A = neg(ma);
    const loc = mul(A, pow(b, -1));
    const reNonNeg = Ge(re(loc), 0);
    const imZero = im(loc);
    if (holds(reNonNeg) && imZero.key === S.Zero.key) {
      let fn = mul(exp(mul(-1, A, pow(b, -1), s)), z);
      if (some(fn, (n) => n instanceof Fn && (n.name === 'sin' || n.name === 'cos'))) fn = cancel(mapBottomUp(fn, (u) => (u instanceof Fn && u.name === 'sin' ? mul(at(u.args, 0), sinc(at(u.args, 0))) : u)));
      const [n0, d0] = asNumerDenom(fn);
      const n = subs(n0, [[t, loc]]);
      const d = subs(d0, [[t, loc]]);
      // delta(b*t - a) = delta(t - a/b)/|b|: SymPy 1.14 divides by b, which flips the sign for b < 0
      if (d.key !== S.Zero.key) return [mul(n, pow(d, -1), pow(abs(b), -1)), S.NegativeInfinity, S.true];
      return undefined;
    }
    if (holds(Lt(re(loc), 0)) || (imZero.isNumber && imZero.key !== S.Zero.key)) return [S.Zero, S.NegativeInfinity, S.true];
    return undefined;
  }
  if (isPolyIn(y, t)) {
    let ro;
    try {
      ro = rootsDict(y, t);
    } catch {
      return undefined;
    }
    if (ro.size > 0 && [...ro.values()].every((v) => v === 1)) {
      const slope = diff(y, t);
      const terms: Expr[] = [];
      for (const [x] of ro) {
        // delta(y(t)) = sum delta(t - x)/|y'(x)| over the simple roots x; SymPy 1.14 substitutes s
        // for t in the other factor and divides by y'(x) without Abs, which is wrong
        if (im(x).key === S.Zero.key && holds(Ge(re(x), 0))) terms.push(mul(exp(mul(-1, x, s)), subs(z, [[t, x]]), pow(abs(subs(slope, [[t, x]])), -1)));
      }
      return [add(...terms), S.NegativeInfinity, S.true];
    }
  }
  return undefined;
}

/** SymPy _laplace_trig_split. */
function laplaceTrigSplit(fn: Expr): [Expr, Expr] {
  const trigs: Expr[] = [];
  const other: Expr[] = [];
  for (const term of mulArgs(fn)) {
    if (hasFn(term, ['sin', 'cos', 'sinh', 'cosh', 'exp'])) trigs.push(term);
    else other.push(term);
  }
  return [mul(...trigs), mul(...other)];
}

interface ExpTerm {
  k: Expr;
  a: Expr;
  re: Expr;
  im: Expr;
}

/** SymPy _laplace_trig_expsum. */
function laplaceTrigExpsum(f: Expr, t: Sym): [ExpTerm[], Expr[]] {
  const c1 = wild('c1', t);
  const c0 = wild('c0', t);
  const p = wild('p', t);
  const xm: ExpTerm[] = [];
  const xn: Expr[] = [];
  const x1 = expand(rewrite(f, 'exp'));
  for (const term0 of addArgs(x1)) {
    if (!term0.has(t)) {
      xm.push({ k: term0, a: S.Zero, re: S.Zero, im: S.Zero });
      continue;
    }
    const term = laplaceDeepCollect(powsimp(term0, { combine: 'exp' }), t);
    const r = matchByName(term, mul(p, exp(add(mul(c1, t), c0))));
    if (r) {
      const C1 = mget(r, 'c1');
      xm.push({ k: mul(mget(r, 'p'), exp(mget(r, 'c0'))), a: C1, re: re(C1), im: im(C1) });
    } else xn.push(term);
  }
  return [xm, xn];
}

/** SymPy _laplace_trig_ltex: combine conjugate and symmetric poles. */
function laplaceTrigLtex(xm0: ExpTerm[], s: Expr): [Expr, Expr] {
  const xm = [...xm0];
  const results: Expr[] = [];
  const planes: Expr[] = [];
  const I = S.I;
  const simpc = (coeffs: Expr[]): Expr[] =>
    coeffs.map((c) => {
      const [r0, i0] = asRealImag(c);
      const reIm = (x: Expr): boolean => some(x, (n) => n instanceof Fn && (n.name === 're' || n.name === 'im'));
      if (reIm(r0) || reIm(i0)) return rewrite(c, 'cos');
      return rewrite(add(r0, mul(I, i0)), 'cos');
    });
  const poly = (cs: Expr[]): Expr => add(...cs.map((c, i) => mul(c, pow(s, cs.length - 1 - i))));
  const quadpole = (t1: ExpTerm, k1: Expr, k2: Expr, k3: Expr): Expr => {
    const { a, k: k0, re: ar, im: ai } = t1;
    const nc = [
      add(k0, k1, k2, k3),
      add(mul(a, add(k0, k1, neg(k2), neg(k3))), mul(-2, I, ai, k1), mul(2, I, ai, k2)),
      add(mul(pow(a, 2), add(neg(k0), neg(k1), neg(k2), neg(k3))), mul(a, add(mul(4, I, ai, k0), mul(4, I, ai, k3))), mul(4, pow(ai, 2), k0), mul(4, pow(ai, 2), k3)),
      add(
        mul(pow(a, 3), add(neg(k0), neg(k1), k2, k3)),
        mul(pow(a, 2), add(mul(4, I, ai, k0), mul(2, I, ai, k1), mul(-2, I, ai, k2), mul(-4, I, ai, k3))),
        mul(a, add(mul(4, pow(ai, 2), k0), mul(-4, pow(ai, 2), k3))),
      ),
    ];
    const dc = [S.One, S.Zero, sub(mul(2, pow(ai, 2)), mul(2, pow(ar, 2))), S.Zero, add(pow(ai, 4), mul(2, pow(ai, 2), pow(ar, 2)), pow(ar, 4))];
    return mul(poly(simpc(nc)), pow(poly(dc), -1));
  };
  const ccpole = (t1: ExpTerm, k1: Expr): Expr => {
    const { a, k: k0, re: ar, im: ai } = t1;
    const nc = [add(k0, k1), add(mul(-1, a, k0), mul(-1, a, k1), mul(2, I, ai, k0))];
    const dc = [S.One, mul(-2, ar), add(pow(ai, 2), pow(ar, 2))];
    return mul(poly(simpc(nc)), pow(poly(dc), -1));
  };
  const rspole = (t1: ExpTerm, k2: Expr): Expr => {
    const { a, k: k0, re: ar, im: ai } = t1;
    const nc = [add(k0, k2), add(mul(a, k0), mul(-1, a, k2), mul(-2, I, ai, k0))];
    const dc = [S.One, mul(-2, I, ai), sub(neg(pow(ai, 2)), pow(ar, 2))];
    return mul(poly(simpc(nc)), pow(poly(dc), -1));
  };
  const sypole = (t1: ExpTerm, k3: Expr): Expr => {
    const { a, k: k0 } = t1;
    const nc = [add(k0, k3), mul(a, sub(k0, k3))];
    const dc = [S.One, S.Zero, neg(pow(a, 2))];
    return mul(poly(simpc(nc)), pow(poly(dc), -1));
  };
  while (xm.length > 0) {
    const t1 = defined(xm.pop(), 'term');
    let iImag: number | undefined;
    let iReal: number | undefined;
    let iPoint: number | undefined;
    for (let i = 0; i < xm.length; i++) {
      const x = at(xm, i);
      const realEq = sameExpr(t1.re, x.re);
      const realSym = sameExpr(t1.re, neg(x.re));
      const imagEq = sameExpr(t1.im, x.im);
      const imagSym = sameExpr(t1.im, neg(x.im));
      const reNz = t1.re.key !== S.Zero.key;
      const imNz = t1.im.key !== S.Zero.key;
      if (realSym && imagSym && reNz && imNz) iPoint = i;
      else if (realSym && imagEq && reNz) iReal = i;
      else if (realEq && imagSym && imNz) iImag = i;
    }
    if (iImag !== undefined && iReal !== undefined && iPoint !== undefined) {
      results.push(quadpole(t1, at(xm, iImag).k, at(xm, iReal).k, at(xm, iPoint).k));
      planes.push(abs(re(t1.a)));
      for (const i of [iImag, iReal, iPoint].sort((p, q) => q - p)) xm.splice(i, 1);
    } else if (iImag !== undefined) {
      results.push(ccpole(t1, at(xm, iImag).k));
      planes.push(t1.re);
      xm.splice(iImag, 1);
    } else if (iReal !== undefined) {
      results.push(rspole(t1, at(xm, iReal).k));
      planes.push(abs(t1.re));
      xm.splice(iReal, 1);
    } else if (iPoint !== undefined) {
      results.push(sypole(t1, at(xm, iPoint).k));
      planes.push(abs(t1.re));
      xm.splice(iPoint, 1);
    } else {
      results.push(mul(t1.k, pow(sub(s, t1.a), -1)));
      planes.push(t1.re);
    }
  }
  return [add(...results), maxPlane(planes)];
}

/** SymPy _laplace_rule_trig: trigonometric factors as sums of exponentials. */
function laplaceRuleTrig(fn: Expr, t0: Sym, s: Expr): LaplaceTriple | undefined {
  if (!isTrig(fn)) return undefined;
  const t = new Dummy('t', { real: true });
  const [f, g] = laplaceTrigSplit(subs(fn, [[t0, t]]));
  const [xm, xn] = laplaceTrigExpsum(f, t);
  if (xn.length > 0) return undefined;
  if (!g.has(t)) {
    const [r, p] = laplaceTrigLtex(xm, s);
    return [mul(g, r), p, S.true];
  }
  const planes: Expr[] = [];
  const results: Expr[] = [];
  const [G, Gplane, Gcond] = laplaceTransformImpl(g, t, s, false);
  for (const x1 of xm) {
    results.push(mul(x1.k, subs(G, [[s, sub(s, x1.a)]])));
    planes.push(planeAdd(Gplane, re(x1.a)));
  }
  return [xreplace(add(...results), [[t, t0]]), maxPlane(planes), Gcond];
}

/** SymPy _laplace_rule_diff: derivatives in the time domain. */
function laplaceRuleDiff(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  const facs = mulArgs(f);
  const i = facs.findIndex((x) => x instanceof Derivative);
  if (i < 0) return undefined;
  const d = cast(at(facs, i), Derivative);
  const a = mul(...facs.filter((_, j) => j !== i));
  if (a.has(t)) return undefined;
  const vc = d.variableCount;
  const vc0 = vc[0];
  if (vc.length !== 1 || vc0 === undefined || vc0[0].key !== t.key) return undefined;
  const n = vc0[1];
  const g = d.expr;
  if (!(g instanceof UndefFn || g instanceof Fn || g instanceof ExtensionExpr)) return undefined;
  if (g.args.filter((z) => z.has(t)).length !== 1) return undefined;
  const terms: Expr[] = [];
  for (let k = 0; k < n; k++) {
    const y = k === 0 ? subs(g, [[t, 0]]) : Subs(derivative(g, [[t, k]]), t, 0);
    terms.push(mul(pow(s, n - k - 1), y));
  }
  const [r, pr, cr] = laplaceTransformImpl(g, t, s, false);
  return [mul(a, sub(mul(pow(s, n), r), add(...terms))), pr, cr];
}

/** SymPy _laplace_rule_sdiff: multiplication with a polynomial in t. */
function laplaceRuleSdiff(f: Expr, t: Sym, s: Sym): LaplaceTriple | undefined {
  if (f instanceof Mul) {
    const pfac: Expr[] = [];
    const ofac: Expr[] = [];
    for (const fac of f.args) (isPolyIn(fac, t) ? pfac : ofac).push(fac);
    const pc = pfac.length > 0 ? polyCoeffs(mul(...pfac), t) : undefined;
    if (pc) {
      const N = pc.length;
      if (N > 1) {
        const oex = mul(...ofac);
        const [r_, p_, c_] = laplaceTransformImpl(oex, t, s, false);
        const deri: Expr[] = [r_];
        // SymPy catches the ValueError of differentiating with respect to a non-symbol; s is a symbol here.
        // A zero first derivative (falsy in SymPy) gives the same sum as the derivatives taken below.
        if (some(r_, (x) => x instanceof LaplaceTransform)) {
          for (let k = 0; k < N - 1; k++) deri.push(mul(pow(-1, k + 1), derivative(r_, [[s, k + 1]])));
        } else {
          for (let k = 0; k < N - 1; k++) deri.push(neg(diffTransforms(last(deri), s, 1)));
        }
        return [add(...pc.map((_, n) => mul(at(pc, N - n - 1), at(deri, n)))), p_, c_];
      }
    }
  }
  // SymPy also matches t**n*g with a symbolic positive integer n and returns (-1)**n times the n-th
  // derivative of G; symjs Derivative nodes need a numeric order, so that case stays unevaluated
  // (a numeric power of t is a polynomial factor, handled above)
  return undefined;
}

/** SymPy _laplace_expand. */
function laplaceExpand(f: Expr, t: Sym, s: Sym): LaplaceTriple | undefined {
  let r = expand(f, { deep: false });
  if (r instanceof Add) return laplaceTransformImpl(r, t, s, false);
  r = expandMul(f);
  if (r instanceof Add) return laplaceTransformImpl(r, t, s, false);
  r = expand(f);
  if (r instanceof Add) return laplaceTransformImpl(r, t, s, false);
  if (r.key !== f.key) return laplaceTransformImpl(r, t, s, false);
  r = expand(expandTrig(f));
  if (r instanceof Add) return laplaceTransformImpl(r, t, s, false);
  return undefined;
}

/** SymPy _laplace_apply_prog_rules. */
function laplaceApplyProgRules(f: Expr, t: Sym, s: Sym): LaplaceTriple | undefined {
  return (
    laplaceRuleHeaviside(f, t, s) ??
    laplaceRuleDelta(f, t, s) ??
    laplaceRuleTimescale(f, t, s) ??
    laplaceRuleExp(f, t, s) ??
    laplaceRuleTrig(f, t, s) ??
    laplaceRuleDiff(f, t, s) ??
    laplaceRuleSdiff(f, t, s)
  );
}

/**
 * SymPy _piecewise_to_heaviside: a Piecewise in t written with Heaviside
 * functions (exact for the Laplace transform).
 */
export function piecewiseToHeaviside(f: Expr, t: Sym): Expr {
  if (isReal(t) !== true) {
    const r = new Dummy('r', { real: true });
    return xreplace(piecewiseToHeaviside(xreplace(f, [[t, r]]), r), [[r, t]]);
  }
  // symjs's piecewise_exclusive takes conditions in t only; SymPy's keeps the others, and a
  // condition with another symbol makes the loop below return f (or a Heaviside of t - y for t > y)
  if (cast(f, Piecewise, 'Piecewise').pairs.some(([, c]) => [...c.freeSymbols()].some((v) => v.key !== t.key))) return f;
  const x = piecewiseExclusive(f);
  // a single piece that holds everywhere (SymPy 1.14 then iterates over the args of that expression
  // and returns 0)
  if (!(x instanceof Piecewise)) return x;
  const out: Expr[] = [];
  // An inequality linear in t as [b, lower]: t > b (or t >= b) when lower, t < b (or t <= b) otherwise.
  // SymPy's Piecewise holds canonical relationals (t > 5/2 for 2*t > 5 or 5/2 < t) and accepts only
  // those with t on one side; symjs keeps the relationals as written and solves them here.
  const bound = (c: Expr): [Expr, boolean] | undefined => {
    if (!(c instanceof Rel) || c.op === 'Eq' || c.op === 'Ne') return undefined;
    const [g, l] = c.op === 'Gt' || c.op === 'Ge' ? [c.lhs, c.rhs] : [c.rhs, c.lhs];
    const lin = linearIn(sub(g, l), t);
    if (!lin) return undefined;
    // k is a nonzero real number: the conditions have no symbol but t (checked above)
    const [k, c0] = lin;
    return [neg(mul(c0, pow(k, -1))), isPositive(k) === true];
  };
  const step = ([b, lower]: [Expr, boolean]): Expr => Heaviside(lower ? sub(t, b) : sub(b, t));
  for (const [fn, cond] of x.pairs) {
    const b = bound(cond);
    if (b) {
      out.push(mul(step(b), fn));
      continue;
    }
    // Eq and Ne (single points, SymPy returns f), and conditions that are not linear in t
    if (!(cond instanceof BoolOp) || cond.args.length !== 2) return f;
    const [b0, b1] = pair(cond.args.map(bound));
    if (!b0 || !b1) return f;
    if (cond.op === 'Or') out.push(mul(step(b0), fn), mul(step(b1), fn));
    else if (cond.op === 'And' && b0[1] !== b1[1]) {
      const [lo, hi] = b0[1] ? [b0, b1] : [b1, b0];
      out.push(mul(sub(Heaviside(sub(t, lo[0])), Heaviside(sub(t, hi[0]))), fn));
    } else return f;
  }
  return add(...out);
}

/**
 * SymPy _laplace_transform_integration. SymPy integrates with the Meijer G
 * method here; symjs covers the integrals SymPy's table leaves to it that
 * have a closed form in terms of the Gamma function: c*t**a with symbolic a.
 */
function laplaceTransformIntegration(f: Expr, t: Sym, s: Expr): LaplaceTriple | undefined {
  if (some(f, isDiracDelta)) return undefined;
  // a factor Heaviside(a*t - b) with a < 0 and b >= 0 vanishes for t > 0 (the integral is 0)
  for (const fac of mulArgs(f)) {
    if (!isHeaviside(fac) || fac.args.length !== 1) continue;
    const lin = linearIn(at(fac.args, 0), t);
    if (lin && holds(Lt(lin[0], 0)) && holds(Le(lin[1], 0))) return [S.Zero, S.NegativeInfinity, S.true];
  }
  if (f instanceof Pow && f.base.key === t.key && !f.exp.has(t)) {
    const a = f.exp;
    const cond = Gt(re(a), -1);
    // the integral diverges at 0 for re(a) <= -1 (SymPy leaves 1/t and t**(-3/2) unevaluated)
    if (isFalseExpr(cond)) return undefined;
    return [mul(gamma(add(a, 1)), pow(s, -1), pow(s, neg(a))), S.Zero, cond];
  }
  return undefined;
}

/**
 * SymPy _laplace_transform: the front end that applies the rules
 * recursively to every term.
 */
export function laplaceTransformImpl(fn: Expr, t: Sym, s: Expr, simplify: boolean): LaplaceTriple {
  const { sym: sv, back } = asSymbolVariable(s);
  const terms: [Expr, Expr][] = [];
  for (const ff of addArgs(fn)) {
    const [k, ft] = asIndependent(ff, [t], { asAdd: false });
    if (ft instanceof Piecewise && !ft.has(DiracDelta(t))) {
      for (const term of addArgs(piecewiseToHeaviside(ft, t))) {
        const [k1, f1] = asIndependent(term, [t], { asAdd: false });
        terms.push([mul(k, k1), f1]);
      }
    } else terms.push([k, ft]);
  }
  const termsS: Expr[] = [];
  const planes: Expr[] = [];
  const conditions: Expr[] = [];
  const H = Heaviside(t);
  for (const [k, ft0] of terms) {
    let ft = ft0;
    if (ft.has(H) && !ft.has(DiracDelta(t))) ft = subs(ft, [[H, 1]]);
    let r = laplaceApplySimpleRules(ft, t, sv) ?? laplaceApplyProgRules(ft, t, sv) ?? laplaceExpand(ft, t, sv);
    if (!r) {
      if (some(ft, (u) => u instanceof UndefFn && u.has(t))) r = [new LaplaceTransform(ft, t, sv), S.NegativeInfinity, S.true];
      else r = laplaceTransformIntegration(ft, t, sv) ?? [new LaplaceTransform(ft, t, sv), S.NegativeInfinity, S.true];
    }
    termsS.push(mul(k, r[0]));
    planes.push(r[1]);
    conditions.push(r[2]);
  }
  let result = add(...termsS);
  if (simplify) result = simplifyExpr(result);
  return [back(result), back(maxPlane(planes)), back(and(...conditions))];
}

/** Options of laplaceTransform (SymPy keyword arguments). */
export interface LaplaceOptions extends TransformHints {
  /** Return only F (SymPy noconds); default false. */
  noconds?: boolean;
}

/**
 * The Laplace transform F(s) of f(t) (SymPy laplace_transform):
 * the integral of exp(-s*t)*f(t) from 0- to oo. Returns [F, a, cond] where
 * a is the abscissa of convergence (Re(s) > a) and cond the auxiliary
 * conditions, or F alone with `noconds: true`. Parts that cannot be
 * transformed stay as unevaluated LaplaceTransform objects.
 *
 * @example
 * laplaceTransform(t**4, t, s)  // [24/s**5, 0, True]
 */
export function laplaceTransform(f: ExprLike, t: Sym, s: ExprLike, opts: LaplaceOptions & { noconds: true }): Expr;
export function laplaceTransform(f: ExprLike, t: Sym, s: ExprLike, opts?: LaplaceOptions): LaplaceTriple;
export function laplaceTransform(f: Matrix, t: Sym, s: ExprLike, opts: LaplaceOptions & { noconds: true }): Matrix;
export function laplaceTransform(f: Matrix, t: Sym, s: ExprLike, opts?: LaplaceOptions): [Matrix, Expr, Expr];
export function laplaceTransform(f: ExprLike | Matrix, t: Sym, sIn: ExprLike, opts: LaplaceOptions = {}): Expr | LaplaceTriple | Matrix | [Matrix, Expr, Expr] {
  const s = sympify(sIn);
  const simplify = opts.simplify ?? false;
  if (f instanceof Matrix) {
    // SymPy legacy_matrix=False: the transformed matrix with the combined plane and conditions
    const planes: Expr[] = [];
    const conds: Expr[] = [];
    const M = f.map((e) => {
      const [F, p, c] = laplaceTransformImpl(e, t, s, simplify);
      planes.push(p);
      conds.push(c);
      return F;
    });
    return opts.noconds === true ? M : [M, Max(...planes), and(...conds)];
  }
  const r = laplaceTransformImpl(sympify(f), t, s, simplify);
  return opts.noconds === true ? r[0] : r;
}

/**
 * Replace unevaluated LaplaceTransform(y(t), t, s) by Y(s) and
 * InverseLaplaceTransform(Y(s), s, t) by y(t) for every correspondence
 * y -> Y in `fdict` (SymPy laplace_correspondence).
 */
export function laplaceCorrespondence(f: ExprLike, fdict: ReadonlyMap<UndefinedFunction, UndefinedFunction>): Expr {
  const e = sympify(f);
  const isLT = (x: Expr): boolean => x instanceof LaplaceTransform || x instanceof InverseLaplaceTransform;
  if (!some(e, isLT)) return e;
  const appliedTo = (g: Expr, name: string, v: Expr): boolean => g instanceof UndefFn && g.name === name && g.args.length === 1 && at(g.args, 0).key === v.key;
  for (const [y, Y] of fdict) {
    if (e instanceof LaplaceTransform && appliedTo(e.function, y.functionName, e.functionVariable)) return Y(e.transformVariable);
    if (e instanceof InverseLaplaceTransform && appliedTo(e.function, Y.functionName, e.functionVariable)) return y(e.transformVariable);
  }
  return rebuild(
    e,
    e.args.map((a) => laplaceCorrespondence(a, fdict)),
  );
}

/**
 * Substitute initial conditions y(0), y'(0), ... given as lists in `fdict`
 * (SymPy laplace_initial_conds).
 */
export function laplaceInitialConds(f: ExprLike, t: Sym, fdict: ReadonlyMap<UndefinedFunction, readonly ExprLike[]>): Expr {
  let e = sympify(f);
  for (const [y, ic] of fdict) {
    for (let k = 0; k < ic.length; k++) {
      const target = k === 0 ? y(0) : Subs(derivative(y(t), [[t, k]]), t, 0);
      e = xreplace(e, [[target, sympify(at(ic, k))]]);
    }
  }
  return e;
}

/**
 * The unevaluated Laplace transform of f(t) (SymPy LaplaceTransform);
 * doit() evaluates it with laplaceTransform.
 */
export class LaplaceTransform extends IntegralTransform {
  constructor(f: ExprLike, t: ExprLike, s: ExprLike) {
    super('LaplaceTransform', [sympify(f), sympify(t), sympify(s)]);
  }
  /** SymPy LaplaceTransform._name. */
  static readonly transformName = 'Laplace';
  get transformName(): string {
    return 'Laplace';
  }
  protected get latexName(): string {
    return '\\mathcal{L}';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new LaplaceTransform(...transformArgs(args));
  }
  get asIntegral(): Expr {
    return new Integral([mul(this.function, exp(mul(-1, this.transformVariable, this.functionVariable))), this.functionVariable, S.Zero, S.Infinity]);
  }
  /** Evaluate (SymPy doit): F, or [F, plane, cond] with `noconds: false`. */
  doit(hints: TransformHints = {}): Expr | LaplaceTriple {
    const t = this.functionVariable;
    const r: LaplaceTriple = t instanceof Sym ? laplaceTransformImpl(this.function, t, this.transformVariable, hints.simplify ?? false) : [this, S.NegativeInfinity, S.true];
    return hints.noconds === false ? r : r[0];
  }
}
