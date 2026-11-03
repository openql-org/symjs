// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The inverse Laplace transform (a port of the inverse part of
 * sympy.integrals.laplace): partial fractions of rational functions, the
 * rule table, time and frequency shifts, differentiation and the
 * irrational rules of Bateman's tables (5.3).
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { Sym } from '../../core/nodes';
import { Add, Constant, Derivative, Dummy, Fn, Integral, Mul, Pow, Rational, Rel, S, UndefFn } from '../../core/nodes';
import { and } from '../../core/boolalg';
import { add, exp, mul, neg, pow, splitCoeff, sqrt, sub, sympify } from '../../core/ops';
import { isNegative, isPositive } from '../../core/assumptions';
import { asIndependent, asNumerDenom, extractMultiplicatively, isRationalFunction } from '../../core/methods';
import { mapBottomUp, rebuild, some, subs } from '../../core/traverse';
import { cos, cosh, re, sin, sinh } from '../../functions/elementary';
import { erf, erfc, gamma, lowergamma } from '../../functions/special';
import { besseli, besselj } from '../../functions/bessel';
import { diff } from '../../calculus/diff';
import { Matrix } from '../../matrices/matrix';
import { Poly, factor } from '../../polys/sympoly';
import { rootsDict } from '../../polys/poly';
import { apart } from '../../polys/partfrac';
import { asOrderedFactors } from '../../printing/sortkey';
import { expand, expandMul } from '../../simplify/expand';
import { cancel, together } from '../../simplify/rational';
import { simplify as simplifyExpr } from '../../simplify/simplify';
import type { TransformHints } from './base';
import { IntegralTransform, addArgs, decide, diffTransforms, matchByName, mget, mulArgs, polyCoeffs, wild, transformArgs } from './base';
import { at, cast, first, pair } from '../../core/guard';
import { DiracDelta, Heaviside } from './delta';

/** An inverse Laplace transform result: (f, condition). */
export type InverseLaplacePair = [Expr, Expr];

/** SymPy's sentinel for an unspecified plane (printed as _None). */
const NONE_SENTINEL = new Dummy('None');

const isExpPow = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const hasExp = (e: Expr): boolean => some(e, isExpPow);
const isExpBase = (e: Expr): boolean => isExpPow(e);
const isZeroE = (e: Expr): boolean => e.key === S.Zero.key;
const isOneE = (e: Expr): boolean => e.key === S.One.key;

/**
 * The unevaluated inverse Laplace transform of F(s) (SymPy
 * InverseLaplaceTransform); the fourth argument is the plane of
 * convergence (printed as _None when not given).
 */
export class InverseLaplaceTransform extends IntegralTransform {
  constructor(F: ExprLike, s: ExprLike, t: ExprLike, plane?: ExprLike) {
    super('InverseLaplaceTransform', [sympify(F), sympify(s), sympify(t), plane === undefined ? NONE_SENTINEL : sympify(plane)]);
  }
  /** SymPy InverseLaplaceTransform._name. */
  static readonly transformName = 'Inverse Laplace';
  get transformName(): string {
    return 'Inverse Laplace';
  }
  protected get latexName(): string {
    return '\\mathcal{L}^{-1}';
  }
  /** The plane of convergence, or undefined when not given (SymPy fundamental_plane). */
  get fundamentalPlane(): Expr | undefined {
    const p = at(this.args, 3);
    return p === NONE_SENTINEL ? undefined : p;
  }
  withArgs(args: readonly Expr[]): Expr {
    return new InverseLaplaceTransform(...transformArgs(args), args[3]);
  }
  get asIntegral(): Expr {
    const c = new Dummy('c');
    const s = this.functionVariable;
    const t = this.transformVariable;
    const integral = new Integral([mul(exp(mul(s, t)), this.function), s, sub(c, mul(S.I, S.Infinity)), add(c, mul(S.I, S.Infinity))]);
    return mul(integral, pow(mul(2, S.Pi, S.I), -1));
  }
  /** Evaluate (SymPy doit): f, or [f, cond] with `noconds: false`. */
  doit(hints: TransformHints = {}): Expr | InverseLaplacePair {
    const s = this.functionVariable;
    const r: InverseLaplacePair = s instanceof Sym ? inverseLaplaceTransformImpl(this.function, s, this.transformVariable, this.fundamentalPlane, hints.simplify ?? false, true) : [this, S.true];
    return hints.noconds === false ? r : r[0];
  }
}

// ---------------------------------------------------------------------------
// Rules
// ---------------------------------------------------------------------------

interface IltRule {
  readonly pattern: Expr;
  readonly f: (m: ReadonlyMap<string, Expr>) => Expr;
}

let iltRules: { rules: IltRule[]; s: Dummy; t: Dummy } | undefined;

/** SymPy _inverse_laplace_build_rules. */
function buildInverseRules(): { rules: IltRule[]; s: Dummy; t: Dummy } {
  const s = new Dummy('s');
  const t = new Dummy('t');
  const a = wild('a', s);
  const b = wild('b', s);
  const c = wild('c', s);
  const g = (m: ReadonlyMap<string, Expr>, k: string): Expr => mget(m, k);
  const rules: IltRule[] = [
    { pattern: mul(a, pow(s, -1)), f: (m) => g(m, 'a') },
    {
      pattern: mul(b, pow(add(s, a), neg(c))),
      // SymPy drops the factor b, which is 1 for the inputs it receives; it is kept here.
      // With a = 0 this rule also covers SymPy's separate rule 1/s**b o---o t**(b - 1)/gamma(b)
      // (the matcher binds the Wild a to 0), which therefore is not repeated here
      f: (m) => mul(g(m, 'b'), pow(t, sub(g(m, 'c'), 1)), exp(mul(-1, g(m, 'a'), t)), pow(gamma(g(m, 'c')), -1)),
    },
    {
      pattern: pow(add(pow(s, 2), pow(a, 2)), -2),
      f: (m) => {
        const A = g(m, 'a');
        return mul(sub(sin(mul(A, t)), mul(A, t, cos(mul(A, t)))), pow(mul(2, pow(A, 3)), -1));
      },
    },
    {
      pattern: pow(mul(s, pow(add(s, a), b)), -1),
      f: (m) => mul(lowergamma(g(m, 'b'), mul(g(m, 'a'), t)), pow(mul(pow(g(m, 'a'), g(m, 'b')), gamma(g(m, 'b'))), -1)),
    },
  ];
  return { rules, s, t };
}

/** SymPy _inverse_laplace_apply_simple_rules. */
function inverseLaplaceApplySimpleRules(f: Expr, s: Sym, t: Expr): InverseLaplacePair | undefined {
  if (isOneE(f)) return [DiracDelta(t), S.true];
  iltRules ??= buildInverseRules();
  const { rules, s: sD, t: tD } = iltRules;
  const F = subs(f, [[s, sD]]);
  for (const rule of rules) {
    const m = matchByName(F, rule.pattern);
    if (m) return [mul(Heaviside(t), subs(rule.f(m), [[tD, t]])), S.true];
  }
  return undefined;
}

/** SymPy _inverse_laplace_diff: derivatives in the frequency domain. */
function inverseLaplaceDiff(f: Expr, s: Sym, t: Expr, plane: Expr | undefined): InverseLaplacePair | undefined {
  const facs = mulArgs(f);
  const i = facs.findIndex((x) => x instanceof Derivative);
  if (i < 0) return undefined;
  const d = cast(at(facs, i), Derivative);
  const a = mul(...facs.filter((_, j) => j !== i));
  if (a.has(s)) return undefined;
  const vc = d.variableCount;
  const vc0 = vc[0];
  if (vc.length !== 1 || vc0 === undefined || vc0[0].key !== s.key) return undefined;
  const [r, c] = inverseLaplaceTransformImpl(d.expr, s, t, plane, false, false);
  return [mul(a, pow(neg(t), vc0[1]), r), c];
}

/** SymPy _inverse_laplace_time_shift: exp(-a*s)*F(s) -> Heaviside(t - a)*f(t - a). */
function inverseLaplaceTimeShift(F: Expr, s: Sym, t: Expr, plane: Expr | undefined): InverseLaplacePair | undefined {
  // F always depends on s here: the front end splits off the factor independent of s
  if (!hasExp(F)) return undefined;
  const a = wild('a', s);
  const facs = mulArgs(F);
  for (const [i, fac] of facs.entries()) {
    if (!isExpPow(fac)) continue;
    // exp(c + a*s) = exp(c)*exp(a*s), as SymPy's match of exp(a*s)*g splits it
    const [c, dep] = asIndependent(fac.exp, [s], { asAdd: true });
    const m = matchByName(dep, mul(a, s));
    if (!m) continue;
    const A = mget(m, 'a');
    // a positive or unknown shift is not causal: SymPy shifts by a negative a only
    // (for exp(a*s - b)/s SymPy 1.14 gives exp(-b)*Heaviside(a + t), a time advance)
    if (isNegative(A) !== true) return [new InverseLaplaceTransform(F, s, t, plane), S.true];
    const g = mul(exp(c), ...facs.filter((_, j) => j !== i));
    return inverseLaplaceTransformImpl(g, s, add(t, A), plane, false, true);
  }
  return undefined;
}

/** SymPy _inverse_laplace_freq_shift: F(s - a) -> exp(a*t)*f(t). */
function inverseLaplaceFreqShift(F: Expr, s: Sym, t: Expr, plane: Expr | undefined): InverseLaplacePair | undefined {
  if (F.args.length === 1 && (F instanceof UndefFn || F instanceof Fn)) {
    const a = wild('a', s);
    const m = matchByName(at(F.args, 0), sub(s, a));
    if (m && isPositive(re(mget(m, 'a'))) === true) {
      const A = mget(m, 'a');
      return [mul(exp(mul(-1, A, t)), new InverseLaplaceTransform(rebuild(F, [s]), s, t, plane)), S.true];
    }
  }
  return undefined;
}

/** SymPy _inverse_laplace_time_diff: s**n*F(s) -> the n-th derivative of f. */
function inverseLaplaceTimeDiff(F: Expr, s: Sym, t: Expr, plane: Expr | undefined): InverseLaplacePair | undefined {
  const facs = mulArgs(F);
  let n = 0;
  const rest: Expr[] = [];
  for (const fac of facs) {
    if (fac.key === s.key) n += 1;
    else if (fac instanceof Pow && fac.base.key === s.key && fac.exp instanceof Rational && fac.exp.isInteger && fac.exp.isPositive) n += Number(fac.exp.p);
    else rest.push(fac);
  }
  if (n <= 0) return undefined;
  const [r0, c] = inverseLaplaceTransformImpl(mul(...rest), s, t, plane, false, true);
  const r = subs(r0, [[Heaviside(t), 1]]);
  if (some(r, (x) => x instanceof InverseLaplaceTransform)) return [diffTransforms(r, t, n), c];
  return [mul(Heaviside(t), diff(r, t, n)), c];
}

interface PowerFactor {
  a: Expr;
  b: Expr;
  m: Expr;
  n: Expr;
}

const num = (e: Expr): number => (e.isNumber ? e.toNumber() : NaN);
const eqNum = (e: Expr, v: number): boolean => e instanceof Rational && e.value === v;

/** Match a factor as (a*s**m + b)**n. */
function powerFactor(x: Expr, s: Sym): PowerFactor | undefined {
  const [base, n] = x instanceof Pow && !isExpBase(x) ? [x.base, x.exp] : [x, S.One];
  if (n.has(s)) return undefined;
  // every factor depends on s (the front end splits off the factor independent of s),
  // so a is never 0 and SymPy's collection of such factors into a constant is not needed
  const terms = addArgs(base);
  const dep = terms.filter((term) => term.has(s));
  if (dep.length !== 1) return undefined;
  const [a, sm] = asIndependent(first(dep), [s], { asAdd: false });
  let m: Expr;
  if (sm.key === s.key) m = S.One;
  else if (sm instanceof Pow && sm.base.key === s.key && !sm.exp.has(s)) m = sm.exp;
  else return undefined;
  return { a, b: add(...terms.filter((term) => !term.has(s))), m, n };
}

/** besselj with SymPy's evaluation besselj(nu, I*z) = I**nu*besseli(nu, z). */
function besseljEval(nu: ExprLike, z: Expr): Expr {
  const w = extractMultiplicatively(z, S.I);
  if (w !== undefined) return mul(pow(S.I, nu), besseli(nu, w));
  return besselj(nu, z);
}

/** SymPy _inverse_laplace_irrational: Bateman 5.3 for powers of sqrt(s). */
function inverseLaplaceIrrational(fn: Expr, s: Sym, t: Expr): InverseLaplacePair | undefined {
  const fa = asOrderedFactors(fn);
  const ma: PowerFactor[] = [];
  for (const x of fa) {
    const pf = powerFactor(x, s);
    if (pf === undefined) return undefined;
    ma.push(pf);
  }
  const zeros: PowerFactor[] = [];
  const poles: PowerFactor[] = [];
  for (const term of ma) {
    if (isPositive(term.n) === true) zeros.push(term);
    else if (isNegative(term.n) === true) poles.push(term);
    else return undefined;
  }
  const key = (x: PowerFactor): [number, number, number] => [num(x.n), isZeroE(x.b) ? 0 : 1, num(x.b)];
  const cmp = (p: PowerFactor, q: PowerFactor): number => {
    const [a0, a1, a2] = key(p);
    const [b0, b1, b2] = key(q);
    if (a0 - b0 || a1 - b1) return a0 - b0 || a1 - b1;
    if (!Number.isNaN(a2) && !Number.isNaN(b2)) return a2 - b2;
    // symbolic: compare with the assumptions (SymPy sorts with evaluated relationals)
    const lt = decide(new Rel('Lt', p.b, q.b));
    return lt === true ? -1 : decide(new Rel('Gt', p.b, q.b)) === true ? 1 : 0;
  };
  poles.sort(cmp);
  zeros.sort(cmp);
  const pi = S.Pi;
  const st = sqrt(t);
  let result: Expr | undefined;
  const P = (i: number): PowerFactor => at(poles, i);
  const Zr = (i: number): PowerFactor => at(zeros, i);
  const pos = (e: Expr): boolean => isPositive(e) === true;
  if (poles.length === 1 && zeros.length === 0) {
    const p0 = P(0);
    if (eqNum(p0.n, -1) && eqNum(p0.m, 0.5)) {
      const a_ = mul(p0.b, pow(p0.a, -1));
      const k_ = pow(p0.a, -1);
      if (pos(a_)) result = sub(mul(k_, pow(sqrt(pi), -1), pow(st, -1)), mul(k_, a_, exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))));
    } else if (eqNum(p0.n, -2) && eqNum(p0.m, 0.5)) {
      const aSq = mul(p0.b, pow(p0.a, -1));
      const a_ = pow(aSq, 2);
      const k_ = pow(p0.a, -2);
      if (pos(aSq)) result = mul(k_, add(1, mul(-2, pow(sqrt(pi), -1), sqrt(a_), st), mul(sub(1, mul(2, a_, t)), exp(mul(a_, t)), sub(erf(mul(sqrt(a_), st)), 1))));
    } else if (eqNum(p0.n, -3) && eqNum(p0.m, 0.5)) {
      const a_ = mul(p0.b, pow(p0.a, -1));
      const k_ = pow(p0.a, -3);
      if (pos(a_)) result = mul(k_, sub(mul(2, pow(sqrt(pi), -1), add(mul(pow(a_, 2), t), 1), st), mul(a_, t, exp(mul(pow(a_, 2), t)), add(mul(2, pow(a_, 2), t), 3), erfc(mul(a_, st)))));
    } else if (eqNum(p0.n, -4) && eqNum(p0.m, 0.5)) {
      const a_ = mul(p0.b, pow(p0.a, -1));
      const k_ = mul(pow(p0.a, -4), Rational.of(1n, 3n));
      if (pos(a_)) {
        result = mul(
          k_,
          sub(
            mul(t, add(mul(4, pow(a_, 4), pow(t, 2)), mul(12, pow(a_, 2), t), 3), exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))),
            mul(2, pow(sqrt(pi), -1), pow(a_, 3), pow(t, Rational.of(5n, 2n)), add(mul(2, pow(a_, 2), t), 5)),
          ),
        );
      }
    } else if (eqNum(p0.n, -0.5) && eqNum(p0.m, 2)) {
      const a_ = sqrt(mul(p0.b, pow(p0.a, -1)));
      const k_ = pow(sqrt(p0.a), -1);
      result = mul(k_, besseljEval(0, mul(a_, t)));
    }
  } else if (poles.length === 1 && zeros.length === 1) {
    const p0 = P(0);
    const z0 = Zr(0);
    if (eqNum(p0.n, -3) && eqNum(p0.m, 0.5) && eqNum(z0.n, 0.5) && isZeroE(z0.b)) {
      const a_ = p0.b;
      const k_ = mul(sqrt(z0.a), pow(p0.a, -1));
      result = sub(
        mul(k_, add(mul(2, pow(a_, 4), pow(t, 2)), mul(5, pow(a_, 2), t), 1), exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))),
        mul(2, pow(sqrt(pi), -1), a_, add(mul(pow(a_, 2), t), 2), st),
      );
    }
    if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && eqNum(z0.n, 0.5) && eqNum(z0.m, 1)) {
      const a_ = mul(z0.b, pow(z0.a, -1));
      const b_ = mul(p0.b, pow(p0.a, -1));
      const k_ = mul(sqrt(z0.a), pow(p0.a, -1));
      result = mul(k_, add(mul(exp(mul(-1, a_, t)), pow(st, -1), pow(sqrt(pi), -1)), mul(sqrt(sub(a_, b_)), exp(mul(-1, b_, t)), erf(mul(sqrt(sub(a_, b_)), st)))));
    }
  } else if (poles.length === 2 && zeros.length === 0) {
    const p0 = P(0);
    const p1 = P(1);
    if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && eqNum(p1.n, -0.5) && eqNum(p1.m, 1) && isZeroE(p1.b)) {
      const a_ = neg(mul(p0.b, pow(p0.a, -1)));
      const k_ = mul(pow(sqrt(p1.a), -1), pow(p0.a, -1));
      if (pos(a_)) result = mul(k_, pow(sqrt(a_), -1), exp(mul(a_, t)), erf(mul(sqrt(a_), st)));
    } else if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && isZeroE(p0.b) && eqNum(p1.n, -1) && eqNum(p1.m, 0.5)) {
      const a_ = mul(p1.b, pow(p1.a, -1));
      const k_ = mul(pow(p0.a, -1), pow(p1.a, -1), pow(a_, -1));
      if (pos(a_)) result = mul(k_, sub(1, mul(exp(mul(pow(a_, 2), t)), erfc(mul(a_, st)))));
    } else if (eqNum(p0.n, -1) && eqNum(p0.m, 0.5) && eqNum(p1.n, -0.5) && eqNum(p1.m, 1) && isZeroE(p1.b)) {
      const a_ = mul(p0.b, pow(p0.a, -1));
      const k_ = pow(mul(p0.a, sqrt(p1.a)), -1);
      if (pos(a_)) result = mul(k_, exp(mul(pow(a_, 2), t)), erfc(mul(a_, st)));
    } else if (eqNum(p0.n, -1.5) && eqNum(p0.m, 1) && isZeroE(p0.b) && eqNum(p1.n, -1) && eqNum(p1.m, 0.5)) {
      const a_ = mul(p1.b, pow(p1.a, -1));
      const k_ = mul(pow(mul(pow(p0.a, Rational.of(3n, 2n)), p1.a), -1), pow(a_, -2));
      if (pos(a_)) result = mul(k_, add(mul(2, pow(sqrt(pi), -1), a_, st), mul(exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))), -1));
    } else if (eqNum(p0.n, -1.5) && eqNum(p0.m, 1) && isZeroE(p0.b) && eqNum(p1.n, -1) && eqNum(p1.m, 1)) {
      // 1/((a0*s)**(3/2)*(a1*s + b1)), Bateman 5.3 (2) with s*sqrt(s) combined into
      // s**(3/2); SymPy has this rule only for the three factors s, a1*s + b1 and
      // sqrt(a2*s + b2) (below) and evaluates this form with Meijer G functions. It
      // applies that rule also for b2 != 0, which is wrong (SymPy 1.14:
      // 1/(s*(s - 1)*sqrt(s + 2)) -> (-2*sqrt(t)/sqrt(pi) + exp(t)*erf(sqrt(t)))*Heaviside(t))
      const a_ = neg(mul(p1.b, pow(p1.a, -1)));
      const k_ = pow(mul(pow(p0.a, Rational.of(3n, 2n)), p1.a), -1);
      if (pos(a_)) result = mul(k_, sub(mul(pow(a_, Rational.of(-3n, 2n)), exp(mul(a_, t)), erf(mul(sqrt(a_), st))), mul(2, pow(a_, -1), pow(sqrt(pi), -1), st)));
    } else if (eqNum(p0.n, -2) && eqNum(p0.m, 0.5) && eqNum(p1.n, -1) && eqNum(p1.m, 1) && isZeroE(p1.b)) {
      const aSq = mul(p0.b, pow(p0.a, -1));
      const a_ = pow(aSq, 2);
      const k_ = mul(pow(p0.a, -2), pow(p1.a, -1));
      if (pos(aSq)) result = mul(k_, add(pow(a_, -1), mul(sub(mul(2, t), pow(a_, -1)), exp(mul(a_, t)), erfc(mul(sqrt(a_), st))), mul(-2, pow(sqrt(pi), -1), pow(sqrt(a_), -1), st)));
    } else if (eqNum(p0.n, -2) && eqNum(p0.m, 0.5) && eqNum(p1.n, -0.5) && eqNum(p1.m, 1) && isZeroE(p1.b)) {
      const a_ = mul(p0.b, pow(p0.a, -1));
      const k_ = mul(pow(p0.a, -2), pow(sqrt(p1.a), -1));
      if (pos(a_)) result = mul(k_, sub(mul(2, pow(sqrt(pi), -1), st), mul(2, a_, t, exp(mul(pow(a_, 2), t)), erfc(mul(a_, st)))));
    } else if (eqNum(p0.n, -3) && eqNum(p0.m, 0.5) && eqNum(p1.n, -0.5) && eqNum(p1.m, 1) && isZeroE(p1.b)) {
      const a_ = p0.b;
      const k_ = mul(pow(sqrt(p1.a), -1), pow(p0.a, -1));
      result = mul(k_, sub(mul(add(mul(2, pow(a_, 2), t), 1), t, exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))), mul(2, pow(sqrt(pi), -1), a_, pow(t, Rational.of(3n, 2n)))));
    } else if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && eqNum(p1.n, -0.5) && eqNum(p1.m, 1)) {
      const a_ = mul(p0.b, pow(p0.a, -1));
      const b_ = mul(p1.b, pow(p1.a, -1));
      const k_ = mul(pow(sqrt(p1.a), -1), pow(p0.a, -1));
      result = mul(k_, pow(sqrt(sub(b_, a_)), -1), exp(mul(-1, a_, t)), erf(mul(sqrt(sub(b_, a_)), st)));
    }
  } else if (poles.length === 2 && zeros.length === 1) {
    const p0 = P(0);
    const p1 = P(1);
    const z0 = Zr(0);
    if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && eqNum(p1.n, -1) && eqNum(p1.m, 0.5) && eqNum(z0.n, 0.5) && eqNum(z0.m, 1) && isZeroE(z0.b)) {
      const aSq = mul(p1.b, pow(p1.a, -1));
      const a_ = pow(aSq, 2);
      const b_ = neg(mul(p0.b, pow(p0.a, -1)));
      const k_ = mul(sqrt(z0.a), pow(p0.a, -1), pow(p1.a, -1), pow(sub(a_, b_), -1));
      if (pos(aSq) && pos(b_)) {
        result = mul(
          k_,
          // SymPy 1.14 has erfc in the second term (also in its test of rule 5.3.6), which is
          // wrong: sqrt(s)/((s - b)*(sqrt(s) + sqrt(a))) = (s - sqrt(a)*sqrt(s))/((s - a)*(s - b))
          // inverts to (a*exp(a*t)*erfc(sqrt(a*t)) + sqrt(a*b)*exp(b*t)*erf(sqrt(b*t)) - b*exp(b*t))/(a - b)
          add(mul(a_, exp(mul(a_, t)), erfc(mul(sqrt(a_), st))), mul(sqrt(a_), sqrt(b_), exp(mul(b_, t)), erf(mul(sqrt(b_), st))), mul(-1, b_, exp(mul(b_, t)))),
        );
      }
    } else if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && isZeroE(p0.b) && eqNum(p1.n, -1) && eqNum(p1.m, 0.5) && eqNum(z0.n, 1) && eqNum(z0.m, 0.5)) {
      const aNum = mul(z0.b, pow(z0.a, -1));
      const a_ = mul(p1.b, pow(p1.a, -1));
      if (isZeroE(add(a_, aNum))) {
        const k_ = mul(z0.a, pow(p0.a, -1), pow(p1.a, -1));
        result = mul(k_, sub(mul(2, exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))), 1));
      }
    } else if (eqNum(p1.n, -1) && eqNum(p1.m, 1) && isZeroE(p1.b) && eqNum(p0.n, -2) && eqNum(p0.m, 0.5) && eqNum(z0.n, 2) && eqNum(z0.m, 0.5)) {
      const aNum = mul(z0.b, pow(z0.a, -1));
      const a_ = mul(p0.b, pow(p0.a, -1));
      if (isZeroE(add(a_, aNum))) {
        const k_ = mul(pow(z0.a, 2), pow(p1.a, -1), pow(p0.a, -2));
        result = mul(k_, add(1, mul(8, pow(a_, 2), t, exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))), mul(-8, pow(sqrt(pi), -1), a_, st)));
      }
    } else if (eqNum(p1.n, -1) && eqNum(p1.m, 1) && isZeroE(p1.b) && eqNum(p0.n, -3) && eqNum(p0.m, 0.5) && eqNum(z0.n, 3) && eqNum(z0.m, 0.5)) {
      const aNum = mul(z0.b, pow(z0.a, -1));
      const a_ = mul(p0.b, pow(p0.a, -1));
      if (isZeroE(add(a_, aNum))) {
        const k_ = mul(pow(z0.a, 3), pow(p1.a, -1), pow(p0.a, -3));
        result = mul(
          k_,
          add(
            mul(mul(2, add(mul(8, pow(a_, 4), pow(t, 2)), mul(8, pow(a_, 2), t), 1)), exp(mul(pow(a_, 2), t)), erfc(mul(a_, st))),
            mul(-8, pow(sqrt(pi), -1), a_, st, add(mul(2, pow(a_, 2), t), 1)),
            -1,
          ),
        );
      }
    }
  } else if (poles.length === 3 && zeros.length === 0) {
    const p0 = P(0);
    const p1 = P(1);
    const p2 = P(2);
    if (eqNum(p0.n, -1) && isZeroE(p0.b) && eqNum(p0.m, 1) && eqNum(p1.n, -1) && eqNum(p1.m, 1) && eqNum(p2.n, -0.5) && eqNum(p2.m, 1) && isZeroE(p2.b)) {
      // Bateman 5.3 (2) with the factors s and sqrt(a2*s) apart (sqrt(k*s) for a k not
      // known to be positive). SymPy does not check b2 = 0 and so gives a wrong result
      // for sqrt(a2*s + b2) (see the two-pole form of this rule above)
      const a_ = neg(mul(p1.b, pow(p1.a, -1)));
      const k_ = mul(pow(p0.a, -1), pow(p1.a, -1), pow(sqrt(p2.a), -1));
      if (pos(a_)) result = mul(k_, sub(mul(pow(a_, Rational.of(-3n, 2n)), exp(mul(a_, t)), erf(mul(sqrt(a_), st))), mul(2, pow(a_, -1), pow(sqrt(pi), -1), st)));
    } else if (eqNum(p0.n, -1) && eqNum(p0.m, 1) && eqNum(p1.n, -1) && eqNum(p1.m, 0.5) && eqNum(p2.n, -0.5) && eqNum(p2.m, 1) && isZeroE(p2.b)) {
      const aSq = mul(p1.b, pow(p1.a, -1));
      const a_ = pow(aSq, 2);
      const b_ = neg(mul(p0.b, pow(p0.a, -1)));
      const k_ = mul(pow(p0.a, -1), pow(p1.a, -1), pow(sqrt(p2.a), -1), pow(mul(sqrt(b_), sub(a_, b_)), -1));
      if (pos(aSq) && pos(b_)) {
        result = mul(k_, add(mul(sqrt(b_), exp(mul(a_, t)), erfc(mul(sqrt(a_), st))), mul(sqrt(a_), exp(mul(b_, t)), erf(mul(sqrt(b_), st))), mul(-1, sqrt(b_), exp(mul(b_, t)))));
      }
    }
  }
  if (result === undefined) return undefined;
  return [mul(Heaviside(t), result), S.true];
}

/** SymPy _inverse_laplace_apply_prog_rules. */
function inverseLaplaceApplyProgRules(F: Expr, s: Sym, t: Expr, plane: Expr | undefined): InverseLaplacePair | undefined {
  return (
    inverseLaplaceTimeShift(F, s, t, plane) ??
    inverseLaplaceFreqShift(F, s, t, plane) ??
    inverseLaplaceTimeDiff(F, s, t, plane) ??
    inverseLaplaceDiff(F, s, t, plane) ??
    inverseLaplaceIrrational(F, s, t)
  );
}

/** SymPy _inverse_laplace_expand. */
function inverseLaplaceExpand(fn: Expr, s: Sym, t: Expr, plane: Expr | undefined): InverseLaplacePair | undefined {
  if (fn instanceof Add) return undefined;
  let r = expand(fn, { deep: false });
  if (r instanceof Add) return inverseLaplaceTransformImpl(r, s, t, plane, false, true);
  r = expandMul(fn);
  if (r instanceof Add) return inverseLaplaceTransformImpl(r, s, t, plane, false, true);
  r = expand(fn);
  if (r instanceof Add) return inverseLaplaceTransformImpl(r, s, t, plane, false, true);
  if (isRationalFunction(fn, [s])) r = apartS(fn, s);
  if (r instanceof Add) return inverseLaplaceTransformImpl(r, s, t, plane, false, true);
  return undefined;
}

/**
 * Distribute a factor -1 over the only sum of a product, as SymPy's simplify
 * leaves sqrt((-d**2 + 4*k*m)/m**2) (symjs keeps sqrt(-(d**2 - 4*k*m)/m**2)).
 */
function distributeMinusOne(e: Expr): Expr {
  return mapBottomUp(e, (x) => {
    if (!(x instanceof Mul)) return x;
    const [c, rest] = splitCoeff(x);
    if (!(c instanceof Rational) || c.p !== -1n || c.q !== 1n) return x;
    const facs = mulArgs(rest);
    const sums = facs.filter((f) => f instanceof Add);
    if (sums.length !== 1) return x;
    return mul(...facs.map((f) => (f instanceof Add ? add(...f.args.map(neg)) : f)));
  });
}

/** The coefficients of a polynomial in s, highest first. */
const allCoeffs = (e: Expr, s: Sym): Expr[] => Poly.from(e, [s]).allCoeffs();

/**
 * Recognize d = c*p**m with p linear or quadratic in s and m > 1 (symjs
 * factor does not factor such powers with symbolic coefficients).
 */
function purePower(d: Expr, s: Sym): [Expr, Expr, number] | undefined {
  const cs = polyCoeffs(expand(d), s);
  if (!cs || cs.length < 3) return undefined;
  const n = cs.length - 1;
  const lc = at(cs, 0);
  const norm = cs.map((x) => mul(x, pow(lc, -1)));
  const check = (p: Expr, m: number): boolean => {
    const diffE = expand(sub(mul(lc, pow(p, m)), d));
    return diffE.key === S.Zero.key || cancel(diffE).key === S.Zero.key;
  };
  // (s + c)**n
  const c = cancel(mul(at(norm, 1), Rational.of(1n, BigInt(n))));
  const lin = add(s, c);
  if (check(lin, n)) return [lc, lin, n];
  // (s**2 + p*s + q)**m
  if (n % 2 === 0 && n >= 4) {
    const m = n / 2;
    const pc = cancel(mul(at(norm, 1), Rational.of(1n, BigInt(m))));
    const qc = cancel(mul(sub(at(norm, 2), mul(Rational.of(BigInt(m * (m - 1)), 2n), pow(pc, 2))), Rational.of(1n, BigInt(m))));
    const quad = add(pow(s, 2), mul(pc, s), qc);
    if (check(quad, m)) return [lc, quad, m];
  }
  return undefined;
}

/**
 * SymPy's apart in s: the partial fractions of symjs apart, with the
 * denominators factored and the terms over a power of one factor p split
 * into sum(q_j/p**(m - j)) (symjs apart leaves repeated factors with
 * symbolic coefficients expanded).
 */
function apartS(f: Expr, s: Sym): Expr {
  const out: Expr[] = [];
  for (const term of addArgs(apart(f, s))) {
    const [n, d] = asNumerDenom(term);
    if (!d.has(s)) {
      out.push(term);
      continue;
    }
    const pp = purePower(d, s);
    // a denominator that is not a power of one linear or quadratic factor is only factored
    // (apart has already split the coprime factors)
    if (!pp) {
      out.push(mul(n, pow(factor(d), -1)));
      continue;
    }
    const [c, p, m] = pp;
    // n = sum q_j*p**j + rest*p**m with deg q_j < deg p (rest is 0 for the proper
    // fractions of apart); zero coefficients vanish in the sum
    let rest = Poly.from(n, [s]);
    const P = Poly.from(p, [s]);
    for (let j = 0; j < m; j++) {
      const [q, r] = rest.div(P);
      out.push(mul(r.asExpr(), pow(c, -1), pow(p, -(m - j))));
      rest = q;
    }
    out.push(mul(rest.asExpr(), pow(c, -1)));
  }
  return add(...out);
}

/** SymPy _inverse_laplace_rational: partial fractions term by term. */
function inverseLaplaceRational(fn: Expr, s: Sym, t: Expr, plane: Expr | undefined, simplify: boolean): InverseLaplacePair | undefined {
  const xD = new Dummy('x_');
  const f = apartS(fn, s);
  const termsT: Expr[] = [];
  const conditions: Expr[] = [S.true];
  for (const term of addArgs(f)) {
    const [n, d] = asNumerDenom(term);
    let dc = allCoeffs(d, s);
    const dcLead = at(dc, 0);
    dc = dc.map((x) => mul(x, pow(dcLead, -1)));
    let nc = allCoeffs(n, s).map((x) => mul(x, pow(dcLead, -1)));
    if (dc.length === 1) {
      const N = nc.length - 1;
      nc.forEach((c, i) => termsT.push(mul(c, N - i === 0 ? DiracDelta(t) : DiracDelta(t, N - i))));
    } else if (dc.length === 2) {
      termsT.push(mul(Heaviside(t), at(nc, 0), exp(mul(-1, at(dc, 1), t))));
    } else if (dc.length === 3) {
      const a = mul(at(dc, 1), S.Half);
      let b = factor(together(sub(at(dc, 2), pow(a, 2))));
      if (nc.length === 1) nc = [S.Zero, ...nc];
      const [l, m] = pair(nc);
      let r: Expr;
      if (isZeroE(b)) {
        r = mul(add(mul(m, t), mul(l, sub(1, mul(a, t)))), exp(mul(-1, a, t)));
      } else {
        let hyp = false;
        if (isNegative(b) === true) {
          b = neg(b);
          hyp = true;
        }
        const b2 = first([...rootsDict(sub(pow(xD, 2), b), xD).keys()]);
        const bs = distributeMinusOne(simplifyExpr(sqrt(b)));
        r = hyp
          ? add(mul(l, exp(mul(-1, a, t)), cosh(mul(b2, t))), mul(sub(m, mul(a, l)), pow(bs, -1), exp(mul(-1, a, t)), sinh(mul(bs, t))))
          : add(mul(l, exp(mul(-1, a, t)), cos(mul(b2, t))), mul(sub(m, mul(a, l)), pow(bs, -1), exp(mul(-1, a, t)), sin(mul(bs, t))));
      }
      termsT.push(mul(Heaviside(t), r));
    } else {
      const [ft, cond] = inverseLaplaceTransformImpl(term, s, t, plane, simplify, false);
      termsT.push(ft);
      conditions.push(cond);
    }
  }
  let result = add(...termsT);
  if (simplify) result = simplifyExpr(result);
  return [result, and(...conditions)];
}

/**
 * SymPy _inverse_laplace_transform: the front end that applies the rules
 * recursively to every term.
 */
export function inverseLaplaceTransformImpl(fn: Expr, s: Sym, t: Expr, plane: Expr | undefined, simplify: boolean, dorational: boolean): InverseLaplacePair {
  const termsT: Expr[] = [];
  const conditions: Expr[] = [];
  for (const term0 of addArgs(fn)) {
    let term = term0;
    if (hasExp(term)) term = subs(together(subs(term, [[s, neg(s)]])), [[s, neg(s)]]);
    const [k, f] = asIndependent(term, [s], { asAdd: false });
    let r: InverseLaplacePair | undefined;
    if (dorational && isRationalFunction(term, [s])) r = inverseLaplaceRational(f, s, t, plane, simplify);
    r ??= inverseLaplaceApplySimpleRules(f, s, t) ?? inverseLaplaceIrrational(f, s, t) ?? inverseLaplaceExpand(f, s, t, plane) ?? inverseLaplaceApplyProgRules(f, s, t, plane);
    // SymPy finally evaluates the inversion integral with Meijer G functions
    // (_inverse_laplace_transform_integration); symjs has no Meijer G
    // integrator, so the term stays unevaluated. (A rational function whose
    // partial fractions form a sum was already handled by the expansion rule.)
    r ??= [new InverseLaplaceTransform(f, s, t, plane), S.true];
    termsT.push(mul(k, r[0]));
    conditions.push(r[1]);
  }
  let result = add(...termsT);
  if (simplify) result = simplifyExpr(result);
  return [result, and(...conditions)];
}

/** Options of inverseLaplaceTransform (SymPy keyword arguments). */
export interface InverseLaplaceOptions extends TransformHints {
  /** Return only f (SymPy noconds); default true. */
  noconds?: boolean;
}

/**
 * The inverse Laplace transform f(t) of F(s) (SymPy
 * inverse_laplace_transform). t is assumed real. Parts that cannot be
 * inverted stay as unevaluated InverseLaplaceTransform objects. With
 * `noconds: false` the result is [f, cond].
 *
 * @example
 * inverseLaplaceTransform(exp(-a*s)/s, s, t)  // Heaviside(-a + t) for positive a
 */
export function inverseLaplaceTransform(F: ExprLike, s: Sym, t: ExprLike, plane: ExprLike | undefined, opts: InverseLaplaceOptions & { noconds: false }): InverseLaplacePair;
export function inverseLaplaceTransform(F: ExprLike, s: Sym, t: ExprLike, plane?: ExprLike, opts?: InverseLaplaceOptions): Expr;
export function inverseLaplaceTransform(F: Matrix, s: Sym, t: ExprLike, plane?: ExprLike, opts?: InverseLaplaceOptions): Matrix;
export function inverseLaplaceTransform(F: ExprLike | Matrix, s: Sym, tIn: ExprLike, plane?: ExprLike, opts: InverseLaplaceOptions = {}): Expr | InverseLaplacePair | Matrix {
  const t = sympify(tIn);
  if (F instanceof Matrix) return F.map((e) => inverseLaplaceTransformImpl(e, s, t, plane === undefined ? undefined : sympify(plane), opts.simplify ?? false, true)[0]);
  const r = inverseLaplaceTransformImpl(sympify(F), s, t, plane === undefined ? undefined : sympify(plane), opts.simplify ?? false, true);
  return opts.noconds === false ? r : r[0];
}

