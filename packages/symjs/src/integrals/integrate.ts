// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Symbolic integration.
 *
 * A heuristic integrator whose output forms follow SymPy's `integrate`:
 * - linearity, polynomials and a table of elementary antiderivatives
 * - linear substitution u = a*x + b (with Piecewise when a may vanish)
 * - "derivative divides" patterns c*g'/g -> c*log(g) and c*g'*g^n
 * - sin^m cos^n via substitution / reduction formulas
 * - integration by parts for polynomial * exp/sin/cos, polynomial * log^k,
 *   exp*sin/cos and inverse trigonometric functions
 * - rational functions by partial fractions (log and atan terms)
 * Unsupported integrands are returned as an unevaluated `Integral`.
 */

import { isNegative as isNegativeQ, isNonZero, isPositive as isPositiveQ, isReal, isNegative, isPositive } from '../core/assumptions';
import { AccumBounds } from '../core/accumbounds';
import { Eq, Gt, Ne, piecewise, Le, Lt, rel } from '../core/logic';
import type { ExprLike, IntegrateLimitArg, IntegrateOptions, RelOp } from '../core/nodes';
export type { IntegrateLimitArg, IntegrateOptions } from '../core/nodes';
import { Add, BoolAtom, Expr, Constant, Derivative, Dummy, ExtensionExpr, Float, Fn, Integral, Mul, Order, Piecewise, Pow, Rational, Rel, S, Special, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { Concrete } from '../core/concrete';
import { registerHandler } from '../core/refine';
import { fact } from '../core/exprfacts';
import { O } from '../series/series';
import { cmpReal } from '../sets/sets';
import { numAdd, numInv, numMul, numNeg } from '../core/num';
import { at, defined, expectType, getOrThrow, pair } from '../core/guard';
import { babs, gcd, lcm } from '../core/numbers';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { mapBottomUp as mapBottomUpI, piecewiseFold, some, xreplace as subs, mapBottomUp, preorderTraversal, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { asin, atan, cos, cosh, log, sin, sinh } from '../functions/elementary/elementary';
import { factor } from '../polys/sympoly';
import { NotImplementedError } from '../core/errors';
import { Mod } from '../functions/mod';
import { UPoly, polyCoefficients, roots } from '../polys/poly';
import { fn as fnErf } from '../functions/elementary/elementary';
import { expand as expandFull, expandMul as expand } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { trigsimp, expsimp, hasTrigFunctions } from '../simplify/trigsimp';
import { meijerintDefinite, meijerintIndefinite } from './meijerint';
import { NonElementaryIntegral, rischHooks, rischIntegrate } from './risch';
import { isDiracDelta, isHeaviside, isSingularityFunction } from './transforms/delta';
import { deltaIntegral } from './deltafunctions';
import { singularityIntegral } from './singularityfunctions';
import { cancelFraction, isRationalIn, ratint } from './rationaltools';
import { trigintegrate } from './trigonometry';
import { heurisch, heurischTrig, heurischWrapper } from './heurisch';
import { manualintegrate, sqrtQuadraticRule } from './manualintegrate';
import { floor, Max, Min, sign } from '../functions/special/special';
import { and, or, BoolOp } from '../core/boolalg';
import { ordered } from '../core/match';
import { reduceInequalities } from '../solvers/inequalities';
import { RootSumNode } from '../polys/rootsum';
import { asIndependent, asNumerDenom } from '../core/methods';

import { isReal as rootIsReal } from '../core/public';
type R = Expr | undefined;

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
const isI = (e: Expr) => e instanceof Constant && e.name === 'I';
const isRational = (v: unknown): v is Rational => v instanceof Rational;
const isExp = (e: Expr): e is Pow => e instanceof Pow && isE(e.base);
const isZeroR = (e: Expr) => e instanceof Rational && e.isZero;

/** Widths of equal limits and integrals of constants can be checked without integration. */
registerHandler('zero', (e) => {
  if (!(e instanceof Integral)) return 'unknown';
  const limits: (readonly Expr[])[] = [];
  let f: Expr = e;
  while (f instanceof Integral) {
    limits.unshift(f.args.slice(1));
    f = f.integrand;
  }
  if (fact(f, 'zero') === true) return true;
  let value: Expr | undefined = f;
  for (const limit of limits) {
    const variable = at(limit, 0), a = limit[1], b = limit[2];
    if (a !== undefined && b !== undefined && a.equals(b)) return true;
    if (value === undefined || value.has(variable)) {
      value = undefined;
      continue;
    }
    const width = b === undefined ? a ?? variable : add(b, mul(-1, defined(a)));
    value = mul(value, width);
    if (fact(value, 'zero') === true) return true;
  }
  return value === undefined ? 'unknown' : fact(value, 'zero') ?? 'unknown';
});

class Integrator {
  private static readonly substitutionVariable = new Dummy('u');
  private depth = 0;

  constructor(private readonly x: Sym, private readonly noConditions = false, private readonly symbolicBounds = false) {}

  private free(e: Expr): boolean {
    return !e.has(this.x);
  }

  /** If u = a*x + b with a, b free of x and a != 0, return [a, b]. */
  private linear(u: Expr): [Expr, Expr] | undefined {
    const pc = polyCoefficients(u, this.x);
    if (!pc) return undefined;
    const a = pc.get(1);
    if ([...pc.keys()].some((k) => k > 1) || a === undefined) return undefined;
    return [a, pc.get(0) ?? S.Zero];
  }

  /**
   * Return F, or Piecewise((F, Ne(a, 0)), (fallback, True)) when the
   * coefficient a might be zero (SymPy behavior for symbolic coefficients).
   */
  private nonzero(a: Expr, f: Expr, F: () => Expr): R {
    if (this.noConditions || isNum(a) || isNonZero(a) === true || a.freeSymbols().size === 0) return F();
    const factors = (a instanceof Mul ? a.args : [a]).filter((t) => !isNum(t) && !isI(t) && isNonZero(t) !== true);
    const cond = mul(...factors);
    const main = F();
    // with the coefficient 0 the integrand is simpler (a constant or a polynomial): it has an antiderivative
    const rest = defined(this.integrate(subs(f, [[cond, S.Zero]])), 'integral with a zero coefficient');
    return piecewise([main, Ne(cond, 0)], [rest, true]);
  }

  integrate(f: Expr): R {
    if (this.depth > 24) return undefined;
    this.depth++;
    try {
      return this.integrateInner(f);
    } finally {
      this.depth--;
    }
  }

  private integrateInner(f: Expr): R {
    const x = this.x;
    if (this.free(f)) return mul(f, x);
    if (f instanceof Order && (f.args.length === 1 || at(f.args, 1).equals(x)) && f.expr.has(x)) {
      const primitive = this.integrate(f.expr);
      return primitive === undefined ? undefined : O(primitive, x, f.point);
    }
    if (f.key === x.key) return mul(S.Half, pow(x, 2));

    // polynomials in x (coefficients may be symbolic)
    const pc = polyCoefficients(f, x);
    if (pc) {
      return add(...[...pc].map(([k, c]) => mul(c, pow(x, k + 1), Rational.of(1, k + 1))));
    }

    // a rational function as one fraction (SymPy: risch_integrate's base case calls ratint)
    const rat = this.ratint(f);
    if (rat !== undefined) return rat;

    if (f instanceof Add) {
      const parts = f.args.map((t) => this.integrate(t));
      if (parts.every((p): p is Expr => p !== undefined)) return add(...parts);
    }

    if (f instanceof Mul) {
      const consts = f.args.filter((t) => this.free(t));
      if (consts.length > 0) {
        const r = this.integrate(mul(...f.args.filter((t) => !this.free(t))));
        return r === undefined ? undefined : mul(...consts, r);
      }
    }

    return (
      this.table(f) ??
      this.gaussian(f) ??
      this.fresnel(f) ??
      this.derivativeDivides(f) ??
      this.trigPowers(f) ??
      this.trigOtherPowers(f) ??
      this.substitution(f) ??
      this.byParts(f) ??
      this.expImaginary(f) ??
      this.rational(f) ??
      heurischTrig(f, x, (g, t) => new Integrator(t).integrate(g)) ??
      sqrtQuadraticRule(f, x) ??
      this.expanded(f) ??
      this.sqrtQuadratic(f) ??
      this.polyTimesSqrtSquare(f)
    );
  }

  // ---- p(x)*sqrt(a*(x + h)**2): sqrt(Q)/(x + h) is constant where it is defined (SymPy SqrtQuadraticDenomRule) ----

  private polyTimesSqrtSquare(f: Expr): R {
    const x = this.x;
    if (!(f instanceof Mul)) return undefined;
    const root = f.args.find((t) => t instanceof Pow && t.exp instanceof Rational && t.exp.p === 1n && t.exp.q === 2n);
    if (!(root instanceof Pow)) return undefined;
    const pc = polyCoefficients(root.base, x);
    if (!pc || Math.max(...pc.keys()) !== 2) return undefined;
    const [a, b, c] = [getOrThrow(pc, 2), pc.get(1) ?? S.Zero, pc.get(0) ?? S.Zero];
    if (!(a instanceof Rational && b instanceof Rational && c instanceof Rational)) return undefined;
    if (!numAdd(numMul(b, b), numNeg(numMul(Rational.of(4n), numMul(a, c)))).isZero) return undefined;
    const p = mul(...f.args.filter((t) => t !== root));
    if (!polyCoefficients(p, x)) return undefined;
    // x + h with h = b/(2*a): the root of Q
    const shift = add(x, mul(b, pow(mul(2, a), -1)));
    const r = this.integrate(expand(mul(p, shift)));
    // (a polynomial times x + h is a polynomial)
    return mul(root, pow(shift, -1), defined(r, 'integral of a polynomial'));
  }

  // ---- sqrt(a*x**2 + b*x + c) with rational coefficients (SymPy manualintegrate) ----

  private sqrtQuadratic(f: Expr): R {
    const x = this.x;
    if (!(f instanceof Pow && f.exp instanceof Rational && f.exp.p === 1n && f.exp.q === 2n)) return undefined;
    const pc = polyCoefficients(f.base, x);
    if (!pc || Math.max(...pc.keys()) !== 2) return undefined;
    const [a, b, c] = [getOrThrow(pc, 2), pc.get(1) ?? S.Zero, pc.get(0) ?? S.Zero];
    if (isZeroR(b) && isNegativeQ(c) === true) {
      if (a.equals(S.One)) return mul(S.Half, add(mul(x, f), mul(c, log(add(x, f)))));
      if (a.equals(S.NegOne)) return add(mul(S.Half, x, f), mul(S.Half, c, atan(mul(x, pow(f, -1)))));
    }
    if (!(a instanceof Rational && b instanceof Rational && c instanceof Rational)) return undefined;
    // the discriminant b**2 - 4*a*c
    const disc = numAdd(numMul(b, b), numNeg(numMul(Rational.of(4n), numMul(a, c))));
    const u = add(mul(2, a, x), b);
    // integral of sqrt(Q) = (2*a*x + b)/(4*a)*sqrt(Q) - (b**2 - 4*a*c)/(8*a)*integral of 1/sqrt(Q)
    const first = mul(u, pow(mul(4, a), -1), f);
    // a perfect square: (x - x0)*sqrt(Q)/2 (SymPy SqrtQuadraticDenomRule, integrate(sqrt(x**2), x) = x*sqrt(x**2)/2)
    if (disc.isZero) return mul(expand(mul(u, pow(mul(4, a), -1))), f);
    let inv: Expr;
    if (a.isNegative) inv = mul(-1, pow(sqrt(mul(-1, a)), -1), asin(mul(u, pow(sqrt(disc), -1))));
    else if (disc.isNegative) inv = mul(pow(sqrt(a), -1), fnErf('asinh', [mul(u, pow(sqrt(mul(-1, disc)), -1))]));
    else inv = mul(pow(sqrt(a), -1), log(add(f, mul(u, pow(mul(2, sqrt(a)), -1)))));
    return add(first, mul(-1, disc, pow(mul(8, a), -1), inv));
  }

  // ---- Gaussian: exp(A*x**2 + B*x + C) -> erf / erfi ------------------------

  private gaussian(f: Expr): R {
    const x = this.x;
    if (!(f instanceof Pow && f.base instanceof Constant && f.base.name === 'E')) return undefined;
    const pc = polyCoefficients(f.exp, x);
    if (!pc || Math.max(...pc.keys()) !== 2) return undefined;
    const A = getOrThrow(pc, 2);
    const B = pc.get(1) ?? S.Zero;
    const C = pc.get(0) ?? S.Zero;
    const shift = mul(B, pow(mul(2, A), -1));
    const k0 = add(C, mul(-1, pow(B, 2), pow(mul(4, A), -1)));
    const pref = (k: Expr) => mul(sqrt(S.Pi), pow(mul(2, k), -1), exp(k0));
    const neg = isNegativeQ(A);
    if (neg === true || (neg === undefined && !isPositiveQ(A))) {
      const k = sqrt(mul(-1, A));
      const F = mul(pref(k), fnErf('erf', [expand(mul(k, add(x, shift)))]));
      if (neg === true) return F;
      if (B instanceof Rational && B.isZero && C instanceof Rational && C.isZero) {
        const negA = mul(-1, A);
        const factors = (negA instanceof Mul ? negA.args : [negA]).filter((t) => !isNum(t));
        return piecewise([F, Ne(mul(...factors), 0)], [x, true]);
      }
      return undefined;
    }
    const k = sqrt(A);
    return mul(pref(k), fnErf('erfi', [expand(mul(k, add(x, shift)))]));
  }

  // ---- sin(a*x**2), cos(a*x**2) -> Fresnel integrals ------------------------

  private fresnel(f: Expr): R {
    const x = this.x;
    if (!(f instanceof Fn && (f.name === 'sin' || f.name === 'cos'))) return undefined;
    const pc = polyCoefficients(at(f.args, 0), x);
    if (!pc || Math.max(...pc.keys()) !== 2 || pc.has(1) || pc.has(0)) return undefined;
    // (a coefficient of the polynomial is free of x)
    let a = getOrThrow(pc, 2);
    let sign: Expr = S.One;
    if (isNegativeQ(a) === true) {
      a = mul(-1, a);
      if (f.name === 'sin') sign = S.NegOne;
    }
    // integral of cos(a*x**2) = sqrt(pi/(2*a))*fresnelc(sqrt(2*a/pi)*x), likewise sin with fresnels.
    // SymPy (through Meijer G) keeps the factor gamma(1/4)/(4*gamma(5/4)) = 1 (3*gamma(3/4)/(4*gamma(7/4)) for sin)
    const k = mul(sqrt(2), sqrt(a), pow(sqrt(S.Pi), -1));
    const unit =
      f.name === 'sin'
        ? mul(3, fnErf('gamma', [Rational.of(3n, 4n)]), pow(mul(4, fnErf('gamma', [Rational.of(7n, 4n)])), -1))
        : mul(fnErf('gamma', [Rational.of(1n, 4n)]), pow(mul(4, fnErf('gamma', [Rational.of(5n, 4n)])), -1));
    return mul(sign, pow(k, -1), fnErf(f.name === 'sin' ? 'fresnels' : 'fresnelc', [mul(k, x)]), unit);
  }

  // ---- table of elementary antiderivatives ---------------------------------

  private table(f: Expr): R {
    const x = this.x;
    if (f instanceof Pow) {
      const [b, n] = f.args;
      if (b.key === x.key && this.free(n)) {
        if (n instanceof Rational) {
          if (n.p === -1n && n.q === 1n) return log(x);
          return mul(pow(x, numAdd(n, S.One)), numInv(numAdd(n, S.One)));
        }
        if (isNum(n)) return mul(pow(x, add(n, 1)), pow(add(n, 1), -1));
        const generic = mul(pow(x, add(n, 1)), pow(add(n, 1), -1));
        return this.noConditions ? generic : piecewise([generic, Ne(n, -1)], [log(x), true]);
      }
      if (this.free(n) && n instanceof Rational) {
        const lin = this.linear(b);
        if (lin) {
          const [a] = lin;
          if (n.p === -1n && n.q === 1n) return this.nonzero(a, f, () => mul(log(b), pow(a, -1)));
          const n1 = numAdd(n, S.One);
          return this.nonzero(a, f, () => mul(pow(b, n1), pow(mul(a, n1), -1)));
        }
      }
      if (this.free(n) && !(n instanceof Rational)) {
        const lin = this.linear(b);
        if (lin) {
          const a = lin[0], d = add(n, 1);
          return this.nonzero(a, f, () => {
            const value = mul(pow(b, d), pow(mul(a, d), -1));
            return this.noConditions ? value : piecewise([value, Ne(n, -1)], [mul(log(b), pow(a, -1)), true]);
          });
        }
      }
      if (this.free(b)) {
        const lin = this.linear(n);
        if (lin) {
          const [a] = lin;
          if (isE(b)) {
            if (a instanceof Add) {
              const rate = diff(n, x);
              return this.noConditions ? mul(expandFull(f), pow(rate, -1))
                : piecewise([mul(f, pow(rate, -1)), Ne(rate, 0)], [mul(x, exp(lin[1])), true]);
            }
            return this.nonzero(a, f, () => mul(f, pow(a, -1)));
          }
          return this.nonzero(a, f, () => mul(f, pow(mul(a, log(b)), -1)));
        }
      }
      // d[(2*a*x+b)/sqrt(Q)]/dx = (4*a*c-b**2)/(2*Q**(3/2)).
      if (n.equals(Rational.of(-3, 2))) {
        const q = polyCoefficients(b, x);
        if (q !== undefined && Math.max(...q.keys()) === 2) {
          const a = getOrThrow(q, 2), h = q.get(1) ?? S.Zero, c = q.get(0) ?? S.Zero;
          const den = expand(add(mul(4, a, c), mul(-1, pow(h, 2))));
          // The Meijer G primitive keeps a symbolic quadratic scale on its original branch.
          if (this.symbolicBounds && den.freeSymbols().size) {
            const primitive = meijerintIndefinite(f, x);
            if (primitive !== undefined) return primitive;
          }
          if (!isZeroR(den)) return mul(2, add(mul(2, a, x), h), pow(den, -1), pow(b, S.NegHalf));
        }
      }
      if (n.equals(S.NegHalf) && b instanceof Add) {
        const tangent = b.args.find((t): t is Pow => t instanceof Pow && t.exp.equals(S.Two) && t.base instanceof Fn && t.base.name === 'tan');
        if (tangent !== undefined && b.equals(add(1, tangent))) {
          const t = tangent.base, slope = diff(at(t.args, 0), x);
          if (!slope.has(x) && isNonZero(slope) === true) return mul(t, f, pow(slope, -1));
        }
      }
      if (n.equals(Rational.of(-2)) && b instanceof Fn && (b.name === 'cosh' || b.name === 'sinh')) {
        const u = at(b.args, 0), lin = this.linear(u);
        if (lin) return this.nonzero(lin[0], f, () => {
          const twice = exp(mul(2, u));
          if (b.name === 'sinh') return mul(-2, pow(mul(lin[0], add(twice, -1)), -1));
          const t = fnErf('tanh', [mul(S.Half, u)]);
          return mul(2, t, pow(mul(lin[0], add(pow(t, 2), 1)), -1));
        });
      }
      // 1/sqrt(c - k*x**2) -> asin(sqrt(k/c)*x)/sqrt(k)
      if (n instanceof Rational && n.p === -1n && n.q === 2n) {
        const q = polyCoefficients(b, x);
        if (q?.size === 2 && q.has(0) && q.has(2)) {
          const c = getOrThrow(q, 0);
          const k = mul(-1, getOrThrow(q, 2));
          if (isNum(c) && isNum(k) && c.isPositive && k.isPositive) {
            return mul(asin(mul(sqrt(mul(k, pow(c, -1))), x)), pow(sqrt(k), -1));
          }
        }
      }
    }
    if (f instanceof Fn) {
      const u = at(f.args, 0);
      const lin = this.linear(u);
      if (f.name === 'li') {
        const [scale, monomial] = asIndependent(u, [x], { asAdd: false });
        if (monomial instanceof Pow && monomial.base.equals(x) && monomial.exp instanceof Rational && !monomial.exp.isZero) {
          const inverse = numInv(monomial.exp);
          const correction = mul(x, pow(u, numNeg(inverse)), fnErf('Ei', [mul(add(1, inverse), log(u))]));
          if (!monomial.exp.equals(S.NegOne)) return piecewise([add(mul(x, f), mul(-1, correction)), Ne(scale, 0)], [S.Zero, true]);
        }
      }
      if ((f.name === 'sin' || f.name === 'cos') && u instanceof Fn && u.name === 'log') {
        const rate = cancel(mul(x, diff(u, x)));
        if (rate instanceof Rational) {
          const conjugate = f.name === 'sin' ? mul(-1, rate, cos(u)) : mul(rate, sin(u));
          return expand(mul(x, add(f, conjugate), pow(add(1, pow(rate, 2)), -1)));
        }
      }
      if (lin) {
        const [a] = lin;
        const inv = (F: Expr) => this.nonzero(a, f, () => mul(F, pow(a, -1)));
        switch (f.name) {
          case 'sin':
            return inv(mul(-1, cos(u)));
          case 'cos':
            return inv(sin(u));
          case 'tan':
            return inv(mul(-1, log(cos(u))));
          case 'sinh':
            return inv(cosh(u));
          case 'cosh':
            return inv(sinh(u));
          case 'tanh':
            return inv(add(u, mul(-1, log(add(1, f)))));
          case 'sinc':
            return inv(fnErf('Si', [u]));
          case 'LambertW':
            if (f.args.slice(1).every(branch => !branch.has(x))) return inv(add(mul(u, f), mul(-1, u), mul(u, pow(f, -1))));
            break;
          case 'log':
            if (u.key === x.key) return add(mul(x, log(x)), mul(-1, x));
            break;
          case 'li':
          case 'Ei':
          case 'Si':
          case 'Shi':
          case 'erf':
          case 'erfc':
          case 'erfi':
          case 'asin':
          case 'acos':
          case 'atan':
          case 'asinh':
          case 'acot':
            // integration by parts: x*f(x) - Integral(x*f'(x))
            if (u.key === x.key) return add(mul(x, f), defined(SPECIAL_PARTS[f.name], 'special antiderivative')(x));
            break;
          default:
            break;
        }
      }
    }
    return undefined;
  }

  // ---- substitution u = g(x) -------------------------------------------------

  /**
   * f = F(u)*u' for an inner expression u (a function argument or an
   * exponent): integrate F in u and substitute back.
   */
  private substitution(f: Expr): R {
    const x = this.x;
    if (this.depth > 6) return undefined;
    const cands: Expr[] = [];
    const seen = new Set<string>();
    const walk = (e: Expr) => {
      let inner: readonly Expr[] = [];
      if (e instanceof Fn) inner = [...e.args, e];
      else if (isExp(e)) inner = [e.exp];
      else if (e instanceof Pow && isNum(e.base) && e.base.isPositive) inner = [e];
      for (const u of inner) {
        if (u.has(x) && u.key !== x.key && !seen.has(u.key)) {
          seen.add(u.key);
          cands.push(u);
        }
      }
      e.args.forEach(walk);
    };
    walk(f);
    for (const u of cands) {
      const du = diff(u, x);
      if (isZeroR(du)) continue;
      const q = cancel(expandFull(mul(f, pow(du, -1)), { trig: true }));
      const numericPower = u instanceof Pow && isNum(u.base);
      const t = Integrator.substitutionVariable;
      // Algebraic substitution rewrites commensurate exponential powers in t.
      const g = numericPower ? q.subs(u, t) : subs(q, [[u, t]]);
      if (g.has(x)) continue;
      const G = new Integrator(t).integrate(g);
      if (G === undefined) continue;
      return expand(subs(G, [[t, u]]));
    }
    return undefined;
  }

  // ---- derivative divides --------------------------------------------------

  private derivativeDivides(f: Expr): R {
    const x = this.x;
    const factors = f instanceof Mul ? f.args : [f];
    for (const g of factors) {
      // exp(u) * u' -> exp(u)
      if (g instanceof Pow && g.base instanceof Constant && g.base.name === 'E' && !this.free(g.exp)) {
        const du = diff(g.exp, x);
        if (!isZeroR(du)) {
          const q = cancel(mul(...factors.filter((t) => t !== g), pow(du, -1)));
          if (this.free(q)) return mul(q, g);
          // d Ei(u)/dx = exp(u)*u'/u.
          const scale = cancel(mul(q, g.exp));
          if (this.free(scale)) return mul(scale, fnErf('Ei', [g.exp]));
        }
      }
      if (!(g instanceof Pow) && factors.length > 1) {
        const rest = mul(...factors.filter((t) => t !== g));
        if (diff(g, x).equals(rest)) return mul(S.Half, pow(g, 2));
      }
      if (!(g instanceof Pow) || this.free(g.base) || !(g.exp instanceof Rational)) continue;
      const [base, n] = [g.base, g.exp];
      const rest = mul(...factors.filter((t) => t !== g));
      const db = diff(base, x);
      if (isZeroR(db)) continue;
      const q = cancel(mul(rest, pow(db, -1)));
      if (!this.free(q)) continue;
      if (n.p === -1n && n.q === 1n) {
        // SymPy integrates exponential integrands by the Risch algorithm first: its logarithms are of
        // monic polynomials in the exponential (-exp(r)/(2*exp(r) - 4) -> -log(exp(r) - 2)/2)
        const r = some(base, (e) => isExp(e) && e.exp.has(x)) ? risch(f, x) : undefined;
        return r ?? mul(q, log(base));
      }
      const n1 = expectType(numAdd(n, S.One), isRational, 'n + 1');
      if (!n1.isInteger && n1.p > n1.q) {
        // SymPy form: g**(k + r) -> expanded g**k * g**r (e.g. (x**2 + 1)**(3/2) -> x**2*sqrt(x**2 + 1) + sqrt(x**2 + 1))
        const k = n1.p / n1.q;
        const r = Rational.of(n1.p - k * n1.q, n1.q);
        const head = expand(pow(base, Number(k)));
        const parts = head instanceof Add ? head.args : [head];
        return add(...parts.map((t) => mul(q, numInv(n1), t, pow(base, r))));
      }
      return mul(q, pow(base, n1), numInv(n1));
    }
    return undefined;
  }

  // ---- sin^m cos^n ---------------------------------------------------------

  private trigPowers(f: Expr): R {
    if (f instanceof Mul && f.args.length === 2 && f.args.every(t => t instanceof Fn && t.name === 'sin')) {
      const [s, t] = pair(f.args), u = at(s.args, 0), v = at(t.args, 0);
      const a = this.linear(u), b = this.linear(v);
      if (a && b && isZeroR(a[1]) && isZeroR(b[1]) && !a[0].equals(b[0])) {
        const k = a[0], m = b[0], x = this.x, den = pow(add(pow(k, 2), mul(-1, pow(m, 2))), -1);
        const general = add(mul(m, s, cos(v), den), mul(-1, k, t, cos(u), den));
        // At equal frequencies integration by parts reduces the product to sin(v)**2.
        const resonant = add(mul(S.Half, x, pow(t, 2)), mul(S.Half, x, pow(cos(v), 2)), mul(S.NegHalf, t, cos(v), pow(m, -1)));
        return piecewise([S.Zero, and(Eq(k, 0), Eq(m, 0))], [expand(mul(-1, resonant)), Eq(k, mul(-1, m))], [resonant, Eq(k, m)], [general, true]);
      }
    }
    let m = 0;
    let n = 0;
    let u: Expr | undefined;
    for (const t of f instanceof Mul ? f.args : [f]) {
      let base = t;
      let k = 1;
      if (t instanceof Pow && t.exp instanceof Rational && t.exp.isInteger && t.exp.p > 0n) {
        base = t.base;
        k = Number(t.exp.p);
      }
      if (!(base instanceof Fn && (base.name === 'sin' || base.name === 'cos'))) return undefined;
      const arg = at(base.args, 0);
      if (u === undefined) u = arg;
      else if (u.key !== arg.key) return undefined;
      if (base.name === 'sin') m += k;
      else n += k;
    }
    if (u === undefined || m + n < 2) return undefined;
    const lin = this.linear(u);
    if (!lin) {
      if (m + n !== 2 || (m !== 0 && n !== 0)) return undefined;
      const wave = this.fresnel(cos(mul(2, u)));
      return wave === undefined ? undefined : add(mul(S.Half, this.x), mul(n === 2 ? S.Half : S.NegHalf, wave));
    }
    const [a] = lin;
    const s = new Sym('_u');
    const polyInt = (p: Expr): Expr => {
      const pc = defined(polyCoefficients(p, s), 'polynomial coefficients');
      return add(...[...pc].map(([k, c]) => mul(c, pow(s, k + 1), Rational.of(1, k + 1))));
    };
    let F: Expr;
    if (n % 2 === 1) {
      // s = sin(u): sin^m cos^n du = s^m (1 - s^2)^((n-1)/2) ds
      F = subs(polyInt(expand(mul(pow(s, m), pow(add(1, mul(-1, pow(s, 2))), (n - 1) / 2)))), [[s, sin(u)]]);
    } else if (m % 2 === 1) {
      // c = cos(u): sin^m cos^n du = -(1 - c^2)^((m-1)/2) c^n dc
      F = subs(
        polyInt(expand(mul(-1, pow(add(1, mul(-1, pow(s, 2))), (m - 1) / 2), pow(s, n)))),
        [[s, cos(u)]],
      );
    } else if (n === 0 || m === 0) {
      F = this.reduction(m === 0 ? 'cos' : 'sin', m + n, u);
    } else {
      return undefined;
    }
    return this.nonzero(a, f, () => expand(mul(F, pow(a, -1))));
  }

  /** sin(a*x)**n*cos(a*x)**m for the other integer powers (SymPy trigintegrate). */
  private trigOtherPowers(f: Expr): R {
    return trigintegrate(f, this.x);
  }

  /** Reduction formula for sin^k(u) or cos^k(u) (k even), integrated w.r.t. u. */
  private reduction(name: 'sin' | 'cos', k: number, u: Expr): Expr {
    if (k === 0) return u;
    const s = sin(u);
    const c = cos(u);
    const head =
      name === 'sin'
        ? mul(-1, pow(s, k - 1), c, Rational.of(1, k))
        : mul(pow(c, k - 1), s, Rational.of(1, k));
    return add(head, mul(Rational.of(k - 1, k), this.reduction(name, k - 2, u)));
  }

  // ---- integration by parts -----------------------------------------------

  /** Q satisfying Q' + rate*Q = P for a polynomial P and a nonzero constant rate. */
  private exponentialPolynomial(P: Expr, rate: Expr): Expr {
    const terms: Expr[] = [];
    let d = P;
    for (let k = 0; !isZeroR(d); k++) {
      terms.push(mul(k % 2 === 0 ? 1 : -1, d, pow(rate, -(k + 1))));
      d = diff(d, this.x);
    }
    return expand(add(...terms));
  }

  private byParts(f: Expr): R {
    const x = this.x;
    const factors = f instanceof Mul ? [...f.args] : [f];
    const polyPart: Expr[] = [];
    const others: Expr[] = [];
    for (const t of factors) (polyCoefficients(t, x) ? polyPart : others).push(t);
    const P = mul(...polyPart);

    if (others.length === 1) {
      const g = at(others, 0);
      if (g instanceof Fn && g.name === 'acos' && P.equals(x)) {
        const u = at(g.args, 0), linear = this.linear(u);
        if (linear && isNonZero(linear[0]) === true) {
          const [slope, offset] = linear, root = sqrt(add(1, mul(-1, pow(u, 2))));
          // Substitute u = slope*x + offset and integrate u*acos(u) by parts.
          return mul(pow(slope, -2), add(mul(add(mul(S.Half, pow(u, 2)), Rational.of(-1, 4), mul(-1, offset, u)), g),
            mul(add(offset, mul(Rational.of(-1, 4), u)), root)));
        }
      }
      // P * exp(a*x + b)
      if (isExp(g)) {
        const lin = this.linear(g.exp);
        if (lin && polyPart.length > 0) {
          const [a] = lin;
          return this.nonzero(a, f, () => {
            const Q = this.exponentialPolynomial(P, a);
            const [content, prim] = primitive(Q, x);
            return mul(content, prim, g);
          });
        }
      }
      // P * sin/cos(a*x + b)
      if (g instanceof Fn && ['sin', 'cos', 'sinh', 'cosh'].includes(g.name) && polyPart.length > 0) {
        const u = at(g.args, 0);
        const lin = this.linear(u);
        if (lin) {
          const [a] = lin;
          const ia = pow(a, -1);
          if (g.name === 'sinh' || g.name === 'cosh') {
            let primitive: Expr = S.Zero, derivative = P, scale: Expr = ia;
            let kernel = g.name === 'sinh' ? cosh : sinh;
            while (!isZeroR(derivative)) {
              primitive = add(primitive, mul(derivative, scale, kernel(u)));
              derivative = diff(derivative, x);
              scale = mul(-1, scale, ia);
              kernel = kernel === cosh ? sinh : cosh;
            }
            return this.nonzero(a, f, () => primitive);
          }
          const I_sin = (p: Expr): Expr =>
            isZeroR(p) ? S.Zero : add(mul(-1, p, cos(u), ia), mul(ia, I_cos(diff(p, x))));
          const I_cos = (p: Expr): Expr =>
            isZeroR(p) ? S.Zero : add(mul(p, sin(u), ia), mul(-1, ia, I_sin(diff(p, x))));
          return this.nonzero(a, f, () => expand(g.name === 'sin' ? I_sin(P) : I_cos(P)));
        }
      }
    }

    if (others.length === 2 && others.some((t) => t.equals(log(x)))) {
      const power = others.find((t): t is Pow => t instanceof Pow && t.base.equals(x) && !t.exp.has(x));
      if (power !== undefined && !(power.exp instanceof Rational) && !polyPart.length) {
        const d = add(power.exp, 1);
        const F = mul(x, power, add(mul(d, log(x)), -1), pow(d, -2));
        return this.noConditions ? F : piecewise([F, Ne(power.exp, -1)], [mul(S.Half, pow(log(x), 2)), true]);
      }
      const exponential = others.find(isExp);
      if (exponential !== undefined) {
        const lin = this.linear(exponential.exp);
        if (lin && isNonZero(lin[0]) === true) {
          const [rate, shift] = lin;
          const q = this.exponentialPolynomial(P, rate), constant = subs(q, [[x, S.Zero]]);
          const regular = cancel(mul(add(q, mul(-1, constant)), pow(x, -1)));
          return add(mul(exponential, q, log(x)), mul(-1, exponential, this.exponentialPolynomial(regular, rate)),
            mul(-1, constant, exp(shift), fnErf('Ei', [mul(rate, x)])));
        }
      }
    }
    // With u = sqrt(log(x)), x**(-k-1)*sqrt(log(x))*dx becomes 2*u**2*exp(-k*u**2)*du.
    if (f instanceof Mul && f.has(sqrt(log(x)))) {
      const rest = mul(f, pow(log(x), S.NegHalf));
      if (rest instanceof Pow && rest.base.equals(x)) {
        const k = add(-1, mul(-1, rest.exp));
        if (isPositiveQ(k) === true && !k.has(x)) {
          const root = sqrt(log(x));
          return add(mul(-1, pow(x, mul(-1, k)), root, pow(k, -1)),
            mul(S.NegHalf, sqrt(S.Pi), pow(k, Rational.of(-3, 2)), fnErf('erfc', [mul(sqrt(k), root)])));
        }
      }
    }
    // P * log(x)^k
    const logs = others.map((t) => {
      if (t instanceof Fn && t.name === 'log' && at(t.args, 0).key === x.key) return 1;
      if (t instanceof Pow && t.base instanceof Fn && t.base.name === 'log' && at(t.base.args, 0).key === x.key) {
        return t.exp instanceof Rational && t.exp.isInteger && t.exp.p > 0n ? Number(t.exp.p) : 0;
      }
      return 0;
    });
    const k = logs[0];
    if (others.length === 1 && k !== undefined && k > 0) {
      // (beyond the depth limit nothing is integrated)
      const Q = this.integrate(P);
      if (Q === undefined) return undefined;
      const lx = log(x);
      const rest = k === 1 ? mul(Q, pow(x, -1)) : mul(Q, pow(x, -1), pow(lx, k - 1));
      const r = this.integrate(expand(mul(k, rest)));
      if (r === undefined) return undefined;
      return expand(add(mul(Q, pow(lx, k)), mul(-1, r)));
    }

    // exp(a*x + b) * sin/cos(c*x + d)
    if (others.length === 2) {
      const e = others.find(isExp);
      const t = others.find((o): o is Fn => o instanceof Fn && (o.name === 'sin' || o.name === 'cos'));
      if (e && t) {
        const l1 = this.linear(e.exp);
        const u = at(t.args, 0);
        const l2 = this.linear(u);
        if (l1 && l2 && isNum(l1[0]) && isNum(l2[0])) {
          const [a] = l1;
          const [b] = l2;
          const den = pow(add(pow(a, 2), pow(b, 2)), -1);
          let sine: Expr = t.name === 'sin' ? S.One : S.Zero;
          let cosine: Expr = t.name === 'sin' ? S.Zero : S.One;
          const parts: Expr[] = [];
          for (let d = P; !isZeroR(d); d = mul(-1, diff(d, x))) {
            [sine, cosine] = [mul(den, add(mul(a, sine), mul(b, cosine))), mul(den, add(mul(a, cosine), mul(-1, b, sine)))];
            parts.push(mul(d, expand(mul(e, add(mul(sine, sin(u)), mul(cosine, cos(u)))))));
          }
          return add(...parts);
        }
      }
    }
    return undefined;
  }

  // ---- trig combined with complex exponentials ---------------------------------

  private expImaginary(f: Expr): R {
    if (!hasTrigFunctions(f)) return undefined;
    const hasImagExp = (e: Expr): boolean =>
      (isExp(e) && e.exp.has(S.I)) || e.args.some(hasImagExp);
    if (!hasImagExp(f)) return undefined;
    // (the exponential form rewrites the trigonometric functions, so it differs from f)
    return this.integrate(expsimp(f));
  }

  // ---- rational functions ------------------------------------------------------

  /**
   * SymPy's path for a rational function f: the numerator and denominator
   * are expanded and cancelled, the constant factor is taken out, a power of
   * a linear polynomial is integrated by the table and the rest by ratint.
   * Undefined when f is not a rational function (or a polynomial) of x, or
   * when ratint cannot write the logarithmic part.
   */
  private ratint(f: Expr): R {
    const x = this.x;
    if (!isRationalIn(f, x)) return undefined;
    // (a polynomial was integrated before)
    const [n, d] = asNumerDenom(f);
    const [coeff, g] = asIndependent(cancelFraction(n, d, x), [x], { asAdd: false });
    if (g instanceof Pow && this.linear(g.base)) return undefined;
    // isRationalIn above guarantees that the rational integrator accepts g.
    const r = defined(ratint(g, x), 'integral of a rational function');
    // a RootSum where the roots are not found: the partial fractions over the rationals may do better
    if (some(r, (e) => e instanceof RootSumNode)) return undefined;
    // A real quadratic partial-fraction primitive retains arctangent branch corrections
    // in a subsequent tangent substitution. Complex logarithms would lose those corrections.
    if (!g.has(S.I) && r.has(S.I)) {
      const realPrimitive = this.rational(g);
      if (realPrimitive !== undefined) return mul(coeff, realPrimitive);
    }
    return mul(coeff, r);
  }


  private rational(f: Expr): R {
    const x = this.x;
    const [N, D] = fraction(together(f));
    const pn = UPoly.fromExpr(N, x);
    const pd = UPoly.fromExpr(D, x);
    if (!pn || !pd || pd.degree < 1) return undefined;
    const [q, r] = pn.divmod(pd);
    const terms: Expr[] = [];
    if (!q.isZero) {
      // (the quotient is a polynomial)
      terms.push(defined(this.integrate(q.toExpr(x)), 'integral of a polynomial'));
    }
    // (a zero remainder, a polynomial, was integrated by ratint before)
    const { factors } = pd.factor();
    // basis: for each factor f_i^m_i, j = 1..m_i and k < deg f_i: x^k * D / f_i^j
    const unknowns: { f: UPoly; j: number; k: number }[] = [];
    const columns: UPoly[] = [];
    for (const [fi, mi] of factors) {
      for (let j = 1; j <= mi; j++) {
        let fj = new UPoly([S.One]);
        for (let t = 0; t < j; t++) fj = fj.mul(fi);
        const cof = pd.divmod(fj)[0];
        for (let k = 0; k < fi.degree; k++) {
          const xk = new UPoly([...Array.from({ length: k }, () => S.Zero), S.One]);
          unknowns.push({ f: fi, j, k });
          columns.push(cof.mul(xk));
        }
      }
    }
    // the basis has one column per degree of the denominator, and it is a basis (partial fractions exist)
    const n = pd.degree;
    const sol = solveLinear(
      Array.from({ length: n }, (_, row) => columns.map((col) => col.coeffs[row] ?? S.Zero)),
      Array.from({ length: n }, (_, row) => r.coeffs[row] ?? S.Zero),
    );

    // group numerators A_ij(x) = sum_k c_ijk x^k
    const groups = new Map<string, { f: UPoly; j: number; A: Rational[] }>();
    unknowns.forEach(({ f: fi, j, k }, idx) => {
      const key = `${fi.coeffs.map((c) => c.key).join(',')}|${j}`;
      let g = groups.get(key);
      if (!g) {
        g = { f: fi, j, A: Array.from({ length: fi.degree }, () => S.Zero) };
        groups.set(key, g);
      }
      g.A[k] = at(sol, idx);
    });

    for (const { f: fi, j, A } of groups.values()) {
      const fx = fi.toExpr(x);
      if (fi.degree === 1) {
        const alpha = at(A, 0);
        if (alpha.isZero) continue;
        if (j === 1) terms.push(mul(alpha, log(fx)));
        else terms.push(mul(numNeg(alpha), Rational.of(1, j - 1), pow(fx, 1 - j)));
      } else if (fi.degree === 2 && j === 1) {
        const [beta, alpha] = pair(A);
        const b = at(fi.coeffs, 1);
        const c = at(fi.coeffs, 0);
        if (!alpha.isZero) terms.push(mul(numMul(alpha, S.Half), log(fx)));
        const coef = numAdd(beta, numNeg(numMul(alpha, numMul(b, S.Half))));
        if (!coef.isZero) {
          const disc = numAdd(numMul(Rational.of(4), c), numNeg(numMul(b, b))); // 4c - b^2 > 0
          const sd = sqrt(disc);
          terms.push(mul(coef, 2, pow(sd, -1), atan(mul(add(mul(2, x), b), pow(sd, -1)))));
        }
      } else {
        return undefined;
      }
    }
    return add(...terms);
  }

  private expanded(f: Expr): R {
    const g = expand(f);
    if (g.key === f.key) return undefined;
    return this.integrate(g);
  }
}

/** Split a nonzero polynomial expression with rational coefficients into positive content and primitive part. */
function primitive(e: Expr, x: Sym): [Rational, Expr] {
  const cs = [...defined(polyCoefficients(e, x), 'polynomial coefficients').values()];
  if (!cs.every((c): c is Rational => c instanceof Rational)) return [S.One, e];
  let num = 0n;
  let den = 1n;
  for (const c of cs) {
    num = gcd(num, c.p);
    den = lcm(den, c.q);
  }
  const content = Rational.of(num, den);
  if (content.isOne) return [S.One, e];
  return [content, expand(mul(Rational.of(den, num), e))];
}

/** Solve a square nonsingular linear system over the rationals (Gauss-Jordan). */
function solveLinear(A: Rational[][], b: Rational[]): Rational[] {
  const n = b.length;
  const M = A.map((row, i) => [...row, at(b, i)]);
  const rat = (v: Expr): Rational => expectType(v, isRational, 'rational entry');
  for (let col = 0; col < n; col++) {
    // (at() rejects a missing pivot: the system is nonsingular)
    const piv = M.findIndex((row, i) => i >= col && !at(row, col).isZero);
    const pivRow = at(M, piv);
    M[piv] = at(M, col);
    const inv = rat(numInv(at(pivRow, col)));
    const scaled = pivRow.map((v) => rat(numMul(v, inv)));
    M[col] = scaled;
    for (let i = 0; i < n; i++) {
      const row = at(M, i);
      const k = at(row, col);
      if (i === col || k.isZero) continue;
      M[i] = row.map((v, jj) => rat(numAdd(v, numNeg(numMul(k, at(scaled, jj))))));
    }
  }
  return M.map((row) => at(row, n));
}

/**
 * Integrate f with respect to x. With limits [a, b] the definite integral
 * F(b) - F(a) is returned. If no antiderivative is found, an unevaluated
 * `Integral` is returned (like SymPy).
 */
/** Breakpoints of a Piecewise whose conditions are x < c / x <= c (increasing c), last True. */
function piecewiseBreaks(f: Piecewise, x: Sym): [Expr, Expr | undefined][] | undefined {
  const out: [Expr, Expr | undefined][] = [];
  for (const [e, c] of f.pairs) {
    if (c instanceof BoolAtom && c.value) {
      out.push([e, undefined]);
      break;
    }
    if (!(c instanceof Rel) || !(c.op === 'Lt' || c.op === 'Le') || c.lhs.key !== x.key || c.rhs.has(x)) return undefined;
    out.push([e, c.rhs]);
  }
  return out;
}

/** SymPy Piecewise._intervals: split at linear boundaries and use the first matching branch. */
function definitePiecewise(f: Piecewise, x: Sym, a: Expr, b: Expr): Expr | undefined {
  const order = cmpReal(a, b);
  if (order === undefined) return undefined;
  if (order === 0) return S.Zero;
  if (order > 0) {
    const result = definitePiecewise(f, x, b, a);
    return result === undefined ? undefined : mul(-1, result);
  }
  const boundaries = new Map<string, Expr>();
  const collect = (c: Expr): boolean => {
    if (c instanceof BoolAtom) return true;
    if (c instanceof Rel) {
      const coefficients = polyCoefficients(add(c.lhs, mul(-1, c.rhs)), x);
      if (!coefficients || [...coefficients.keys()].some((degree) => degree > 1)) return false;
      const slope = coefficients.get(1);
      if (slope === undefined || isReal(slope) !== true || isNonZero(slope) !== true) return false;
      const point = mul(-1, coefficients.get(0) ?? S.Zero, pow(slope, -1));
      const left = cmpReal(point, a);
      const right = cmpReal(point, b);
      if (left === undefined || right === undefined) return false;
      if (left > 0 && right < 0) boundaries.set(point.key, point);
      return true;
    }
    return c instanceof BoolOp && c.args.every(collect);
  };
  if (!f.pairs.every(([, condition]) => collect(condition))) return undefined;
  const points = [a, ...[...boundaries.values()].sort((p, q) => defined(cmpReal(p, q))), b];
  const terms: Expr[] = [];
  for (let i = 1; i < points.length; i++) {
    const left = at(points, i - 1);
    const right = at(points, i);
    const sample = left.key === S.NegativeInfinity.key
      ? right.key === S.Infinity.key ? S.Zero : add(right, -1)
      : right.key === S.Infinity.key ? add(left, 1) : mul(S.Half, add(left, right));
    let branch: Expr = S.NaN;
    for (const [expression, condition] of f.pairs) {
      const value = expectType(subs(condition, [[x, sample]]), (value): value is BoolAtom => value instanceof BoolAtom);
      if (value.value) {
        branch = expression;
        break;
      }
    }
    if (branch === S.NaN) return S.NaN;
    const term = integrate(branch, x, [left, right]);
    if (term instanceof Integral) return undefined;
    terms.push(term);
  }
  return add(...terms);
}

type PiecewiseInterval = readonly [start: Expr, end: Expr];
type PiecewiseSegment = readonly [start: Expr, end: Expr, branch: number];

/** Find the intervals described by Boolean combinations of affine conditions. */
function conditionIntervals(condition: Expr, x: Sym): PiecewiseInterval[] | undefined {
  const whole = [S.NegativeInfinity, S.Infinity] as const;
  if (condition instanceof BoolAtom) return condition.value ? [whole] : [];
  if (condition instanceof BoolOp && (condition.op === 'And' || condition.op === 'Or')) {
    let intervals: PiecewiseInterval[] = condition.op === 'And' ? [whole] : [];
    for (const term of condition.args) {
      const ranges = conditionIntervals(term, x);
      if (!ranges) return undefined;
      intervals = condition.op === 'Or' ? [...intervals, ...ranges] : intervals.flatMap(([a, b]) =>
        ranges.map(([c, d]) => [Max(a, c), Min(b, d)] as const));
    }
    return intervals;
  }
  if (!(condition instanceof Rel)) return undefined;
  if ((condition.op === 'Eq' || condition.op === 'Ne') && Mod.isApplied(condition.lhs)) {
    const [argument, period] = pair(condition.lhs.args);
    // With a fixed real period, equality to a fixed residue holds only at isolated points.
    if (argument.key === x.key && period instanceof Rational && !condition.rhs.has(x)) {
      return condition.op === 'Eq' ? [] : [whole];
    }
  }
  const difference = expand(add(condition.lhs, mul(-1, condition.rhs)));
  const coeffs = polyCoefficients(difference, x);
  if (!coeffs || [...coeffs.keys()].some((degree) => degree > 1)) return undefined;
  const slope = coeffs.get(1);
  const remainder = coeffs.get(0) ?? S.Zero;
  if (slope === undefined) {
    const value = rel(condition.op, remainder, S.Zero);
    return value === S.true ? [whole] : value === S.false ? [] : undefined;
  }
  const positive = isPositive(slope) === true;
  if (!positive && isNegative(slope) !== true) return undefined;
  const bound = mul(-1, remainder, pow(slope, -1));
  if (condition.op === 'Eq') return [];
  if (condition.op === 'Ne') return [[whole[0], bound], [bound, whole[1]]];
  const upper = (condition.op === 'Lt' || condition.op === 'Le') === positive;
  return upper ? [[whole[0], bound]] : [[bound, whole[1]]];
}

/** Clip the unassigned segments against each branch in evaluation order. */
function piecewiseSegments(f: Piecewise, x: Sym, start: Expr, end: Expr): PiecewiseSegment[] | undefined {
  let segments: PiecewiseSegment[] = [[start, end, -1]];
  for (const [branch, [, condition]] of f.pairs.entries()) {
    if (!segments.some((segment) => segment[2] === -1)) break;
    const ranges = conditionIntervals(condition, x);
    if (!ranges) return undefined;
    for (const [left, right] of ranges) {
      const top = Max(left, right);
      segments = segments.flatMap((segment): PiecewiseSegment[] => {
        const [a, b, current] = segment;
        if (current >= 0 || a.key === b.key) return [segment];
        if (left === S.NegativeInfinity && top === S.Infinity) return [[a, b, branch]];
        const lo = Min(b, Max(a, left));
        const hi = Min(b, Max(a, top));
        if (lo.key === hi.key) return [segment];
        const clipped: PiecewiseSegment[] = [];
        if (a.key !== lo.key) clipped.push([a, lo, -1]);
        clipped.push([lo, hi, branch]);
        if (hi.key !== b.key) clipped.push([hi, b, -1]);
        return clipped;
      });
    }
  }
  return segments.filter(([a, b]) => a.key !== b.key);
}

function symbolicDefinitePiecewise(f: Piecewise, x: Sym, a: Expr, b: Expr): Expr | undefined {
  const order = a === S.NegativeInfinity || b === S.Infinity ? -1
    : a === S.Infinity || b === S.NegativeInfinity ? 1 : cmpSign(a, b);
  const movable = a instanceof Sym ? a : b;
  const fixed = movable === a ? b : a;
  const width = new Dummy('width', { positive: true });
  const orderedIntegral = (start: Expr, end: Expr): Expr | undefined => {
    const segments = piecewiseSegments(f, x, start, end);
    if (!segments) return undefined;
    // Simplify each clipped endpoint under start < end before looking for holes.
    const simplifyBound = (v: Expr): Expr => {
      if (order !== undefined || !(movable instanceof Sym) || fixed.has(movable)) return v;
      const offset = movable === start ? mul(-1, width) : width;
      const ordered = subs(v, [[movable, add(fixed, offset)]]);
      return mapBottomUp(subs(ordered, [[width, add(end, mul(-1, start))]]), (node) =>
        node instanceof Fn && (node.name === 'Min' || node.name === 'Max') ? node.func(...node.args) : node);
    };
    let total: Expr = S.Zero;
    let previous: Expr | undefined;
    for (const [lo, hi, branch] of segments) {
      const left = simplifyBound(lo), right = simplifyBound(hi);
      if (left.equals(right)) continue;
      if (branch < 0) return previous === undefined ? S.NaN : piecewise([total, Le(end, previous)], [S.NaN, true]);
      const result = integrate(at(f.pairs, branch)[0], x, [left, right]);
      if (result instanceof Integral) return undefined;
      total = add(total, result);
      previous = right;
    }
    return total;
  };
  if (order !== undefined) {
    const result = order < 0 ? orderedIntegral(a, b) : orderedIntegral(b, a);
    return result === undefined || order < 0 ? result : mul(-1, result);
  }
  const forward = orderedIntegral(a, b);
  const reverse = orderedIntegral(b, a);
  if (forward === undefined || reverse === undefined) return undefined;
  const backward = mul(-1, reverse);
  return piecewiseFold(a.isComparable
    ? piecewise([backward, Lt(b, a)], [forward, true])
    : piecewise([forward, Lt(a, b)], [backward, true]));
}

/**
 * SymPy Piecewise._handle_irel: the relations of the conditions that do not
 * contain x are replaced by each combination of truth values (all true
 * first), the handler is applied to the resulting expression, and the
 * results are paired with the combinations, with the relations of a single
 * symbol reduced (reduce_inequalities). Undefined when there are no such
 * relations.
 */
function handleIrel(f: Piecewise, x: Sym, handler: (e: Expr) => Expr): Expr | undefined {
  const rels = new Map<string, Expr>();
  const visit = (e: Expr): void => {
    if (e instanceof Rel && !e.has(x)) rels.set(e.key, e);
    e.args.forEach(visit);
  };
  f.pairs.forEach(([, c]) => visit(c));
  const irel = ordered([...rels.values()]);
  if (irel.length === 0) return undefined;
  const conds = new Map<string, [Expr, Expr[]]>();
  const order: Expr[] = [];
  let expr: Expr = S.Zero;
  for (let mask = (1 << irel.length) - 1; mask >= 0; mask--) {
    const truth = irel.map((_, i) => (mask >> (irel.length - 1 - i)) & 1);
    const reps = irel.map((r, i): [Expr, Expr] => [r, truth[i] ? S.true : S.false]);
    let cond: Expr | undefined;
    if (mask !== 0) {
      const andargs = irel.filter((_, i) => truth[i]);
      const free = [...new Set(andargs.flatMap((r) => [...r.freeSymbols()].map((s) => s.key)))];
      const sym = andargs.flatMap((r) => [...r.freeSymbols()]).find((s): s is Sym => s instanceof Sym);
      let c = and(...andargs);
      if (free.length === 1 && sym) {
        try {
          c = reduceInequalities(andargs, [sym]);
        } catch {
          // Conditions independent of the integration variable can be kept symbolically.
        }
      }
      if (c instanceof BoolAtom && !c.value) continue;
      cond = c;
    }
    // (SymPy also merges a result Piecewise((e, c)) of a single pair into the condition; integrate does not
    // return one)
    expr = handler(subs(f, reps));
    if (cond !== undefined) {
      const entry = conds.get(expr.key);
      if (entry) entry[1].push(cond);
      else conds.set(expr.key, [expr, [cond]]);
      if (!order.some((e) => e.key === expr.key)) order.push(expr);
    }
  }
  return piecewise(...order.map((e) => [e, or(...getOrThrow(conds, e.key)[1])] as const), [expr, true]);
}

/** Integrate each piece separately (SymPy piecewise_integrate). */
export function piecewiseIntegrate(f: Piecewise, x: Sym): Expr {
  return piecewise(...f.pairs.map(([e, c]) => [integrate(e, x), c] as const));
}

/** Continuous antiderivative of a Piecewise in x. */
function integratePiecewise(f: Piecewise, x: Sym): Expr | undefined {
  const br = piecewiseBreaks(f, x);
  if (!br || br.some(([, bound], i) => bound !== undefined && i > 0
    && (cmpSign(defined(at(br, i - 1)[1], 'preceding Piecewise interval bound'), bound) ?? 1) > 0)) {
    const segments = piecewiseSegments(f, x, S.NegativeInfinity, S.Infinity);
    if (!segments) return undefined;
    const pieces: [Expr, Expr][] = [];
    let previous: Expr = S.NaN;
    for (const [start, end, index] of segments) {
      const [value, condition] = index < 0 ? [S.NaN, S.false] : at(f.pairs, index);
      let primitive = integrate(value, x);
      if (primitive instanceof Integral) return undefined;
      if (previous !== S.NaN && primitive !== S.NaN) {
        const offset = add(subs(previous, [[x, start]]), mul(-1, subs(primitive, [[x, start]])));
        if (!(offset instanceof Special)) primitive = add(primitive, offset);
      }
      const test = end === S.Infinity ? S.true : subs(condition, [[x, end]]) === S.false ? Lt(x, end) : Le(x, end);
      pieces.push([primitive, test]);
      previous = primitive;
    }
    return piecewise(...pieces);
  }
  const pieces: [Expr, Expr][] = [];
  let prevF: Expr | undefined;
  let prevBreak: Expr | undefined;
  for (const [e, c] of br) {
    let F = new Integrator(x).integrate(e) ?? otherMethods(e, x);
    if (F === undefined) return undefined;
    if (prevF !== undefined && prevBreak !== undefined) {
      // continuity at the previous breakpoint
      const k = add(subs(prevF, [[x, prevBreak]]), mul(-1, subs(F, [[x, prevBreak]])));
      F = add(F, k);
    }
    pieces.push([F, c === undefined ? S.true : at(f.pairs, pieces.length)[1]]);
    prevF = F;
    prevBreak = c;
  }
  return piecewise(...pieces);
}

/**
 * Piecewise conditions under the sign of x on [a, b]: with x > 0 there,
 * u/x < 0 is u < 0 (x is dropped from the relation).
 */
function simplifyConditionsOnInterval(f: Expr, x: Sym, a: Expr, b: Expr): Expr {
  const has = (e: Expr): boolean => e instanceof Piecewise || e.args.some(has);
  if (!has(f)) return f;
  const sa = a.freeSymbols().size === 0 ? Math.sign(a.toNumber()) : 0;
  const sb = b.freeSymbols().size === 0 ? Math.sign(b.toNumber()) : 0;
  if (!sa || sa !== sb) return f;
  const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
  const cond = (c: Expr): Expr => {
    if (!(c instanceof Rel) || !(c.rhs instanceof Rational && c.rhs.isZero) || !(c.lhs instanceof Mul)) return c;
    const xs = c.lhs.args.filter((g) => g.key === x.key || (g instanceof Pow && g.base.key === x.key && g.exp instanceof Rational && g.exp.isInteger));
    if (!xs.length || c.lhs.args.filter((g) => g.has(x)).length !== xs.length) return c;
    const k = xs.reduce((s2, g) => s2 + (g instanceof Pow && g.exp instanceof Rational ? Number(g.exp.p) : 1), 0);
    const rest = mul(...c.lhs.args.filter((g) => !g.has(x)));
    // the sign of x**k on the interval
    const negative = sa < 0 && k % 2 !== 0;
    return new Rel(negative ? flip[c.op] : c.op, rest, S.Zero);
  };
  return mapBottomUpI(f, (e: Expr) => (e instanceof Piecewise ? piecewise(...e.pairs.map(([v, c]) => [v, cond(c)] as const)) : e));
}

/**
 * Piecewise conditions x < c, x > c, ... decided on (a, b): a relation of the
 * integration variable and an infinity always has the same value (x is
 * finite), and one with a constant that is at or beyond an end of the
 * interval holds everywhere or nowhere inside it (an end is a single point,
 * as in SymPy's piecewise integration).
 */
function decideConditionsOnInterval(f: Expr, x: Sym, a0: Expr, b0: Expr): Expr {
  // the interval between the limits, whichever comes first
  const [a, b] = (cmpReal(a0, b0) ?? -1) > 0 ? [b0, a0] : [a0, b0];
  const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
  const decide = (r: Rel): boolean | undefined => {
    const side: [RelOp, Expr] | undefined = r.lhs.key === x.key && !r.rhs.has(x) ? [r.op, r.rhs] : r.rhs.key === x.key && !r.lhs.has(x) ? [flip[r.op], r.lhs] : undefined;
    if (side === undefined) return undefined;
    const [op, c] = side;
    // x = c holds at a single point at most: nowhere for the integral
    if (op === 'Eq' || op === 'Ne') return op === 'Ne';
    const below = op === 'Lt' || op === 'Le';
    // c is at or below the interval (x > c holds inside) or at or above it (x < c holds inside)
    const atOrBelow = c.key === S.NegativeInfinity.key || (cmpReal(c, a) ?? 1) <= 0;
    const atOrAbove = c.key === S.Infinity.key || (cmpReal(c, b) ?? -1) >= 0;
    if (atOrBelow) return !below;
    if (atOrAbove) return below;
    return undefined;
  };
  const cond = (c: Expr): Expr =>
    mapBottomUpI(c, (e) => {
      if (!(e instanceof Rel)) return e;
      const d = decide(e);
      return d === undefined ? e : d ? S.true : S.false;
    });
  return mapBottomUpI(f, (e: Expr) => (e instanceof Piecewise ? piecewise(...e.pairs.map(([v, c]) => [v, cond(c)] as const)) : e));
}

/** The order of two real values, numerically or by the sign the assumptions give their difference. */
function cmpSign(p: Expr, q: Expr): number | undefined {
  const c = cmpReal(p, q);
  if (c !== undefined) return c;
  const d = add(p, mul(-1, q));
  return isPositiveQ(d) === true ? 1 : isNegativeQ(d) === true ? -1 : undefined;
}

/**
 * Heaviside(a*x + b) at x = oo or -oo: 1 or 0 by the sign of a (SymPy's limit
 * of the antiderivative of a DiracDelta at an infinite end).
 * @internal
 */
export function heavisideAtInfinity(F: Expr, x: Sym, p: Expr): Expr {
  if (!(p instanceof Special) || (p.name !== 'oo' && p.name !== '-oo')) return F;
  return mapBottomUpI(F, (e) => {
    if (!isHeaviside(e)) return e;
    const c = polyCoefficients(at(e.args, 0), x);
    // only a linear argument a*x + b
    const a = c !== undefined && Math.max(0, ...c.keys()) <= 1 ? c.get(1) : undefined;
    const sign = a === undefined ? 0 : isPositiveQ(a) === true ? 1 : isNegativeQ(a) === true ? -1 : 0;
    if (sign === 0) return e;
    return sign * (p.name === 'oo' ? 1 : -1) > 0 ? S.One : S.Zero;
  });
}

/** Sign inside a single half-period; an endpoint can be a zero of the function. */
function trigIntervalSign(base: Fn, a: Expr, b: Expr): number {
  const offset = base.name === 'cos' ? S.Half : S.Zero;
  const phase = (v: Expr) => add(mul(v, pow(S.Pi, -1)), offset);
  const k = floor(phase(a));
  if (!(k instanceof Rational) || !k.isInteger) return 0;
  const end = cmpReal(phase(b), add(k, 1));
  return end === undefined || end > 0 ? 0 : k.p % 2n === 0n ? 1 : -1;
}

/** Polynomial singularities of an integrand; undefined means their location is unresolved. */
function singularPoints(f: Expr, x: Sym, a: Expr, b: Expr): Expr[] | undefined {
  // Expr._eval_interval checks interior singularities only between comparable endpoints.
  if (!a.isComparable || !b.isComparable) return [];
  const bases = new Map<string, Expr>();
  const visit = (e: Expr): void => {
    if (e instanceof Pow && e.exp instanceof Rational && e.exp.isNegative && e.base.has(x)) bases.set(e.base.key, e.base);
    if (e instanceof Fn && e.name === 'tan' && e.has(x)) {
      const denominator = cos(at(e.args, 0));
      bases.set(denominator.key, denominator);
    }
    if (e instanceof Fn && e.name === 'log' && at(e.args, 0).has(x)) {
      // exponential factors (and constants) of the argument do not vanish
      const arg = at(e.args, 0);
      const rest = mul(...(arg instanceof Mul ? arg.args : [arg]).filter((g) => g.has(x) && !isExp(g)));
      if (rest.has(x)) bases.set(rest.key, rest);
    }
    e.args.forEach(visit);
  };
  visit(f);
  const points = new Map<string, Expr>();
  for (const base of bases.values()) {
    const realX = new Dummy('x', { real: true });
    const realBase = subs(base, [[x, realX]]);
    if (fact(realBase, 'positive') === true || fact(realBase, 'negative') === true) continue;
    if (base instanceof Fn && (base.name === 'sin' || base.name === 'cos') && at(base.args, 0).equals(x) && cmpReal(a, b) === -1) {
      if (trigIntervalSign(base, a, b) && cmpReal(subs(base, [[x, a]]), S.Zero) && cmpReal(subs(base, [[x, b]]), S.Zero)) continue;
    }
    if (!polyCoefficients(base, x)) {
      // Bound real sine/cosine factors before declaring the poles unresolved:
      // e.g. 2 + cos(x) lies in [1, 3] and never vanishes on the real axis.
      const bounded = mapBottomUpI(base, (e) => e instanceof Fn && (e.name === 'sin' || e.name === 'cos') && isReal(subs(at(e.args, 0), [[x, realX]])) === true ? AccumBounds(-1, 1) : e);
      if (bounded instanceof AccumBounds && (isPositiveQ(bounded.min) === true || isNegativeQ(bounded.max) === true)) continue;
      return undefined;
    }
    try {
      for (const r of roots(base, x)) {
        // Numerical ordering is used only for constant real roots, never for parameters.
        const real = cmpReal(r, S.Zero);
        if (real !== undefined) points.set(r.key, r);
        else if (r.freeSymbols().size !== 0 && (a instanceof Special || b instanceof Special)) {
          // a parametric root: on the real axis when its assumptions say so, off it when they exclude that
          const onAxis = isReal(r);
          if (onAxis === true) points.set(r.key, r);
          else if (onAxis !== false) return undefined;
        }
      }
    } catch {
      // Root isolation failed: do not assert that the interval is regular.
      return undefined;
    }
  }
  return [...points.values()];
}

/**
 * The methods SymPy's Integral._eval_integral tries besides the table and
 * heuristics: deltaintegrate, singularityintegrate and the Risch algorithm
 * for elementary transcendental integrands. Undefined when none applies.
 */
function otherMethods(f: Expr, x: Sym): Expr | undefined {
  // deltaintegrate integrates the parts it does not handle with integrate: not again by these methods
  const key = `${f.key}|${x.key}`;
  if (activeMethods.has(key)) return undefined;
  activeMethods.add(key);
  try {
    if (f instanceof Add) {
      // term by term, each term by the table or by these methods (SymPy integrates the terms separately)
      const parts = f.args.map((g) => new Integrator(x).integrate(g) ?? otherMethods(g, x));
      if (parts.every((p): p is Expr => p !== undefined)) return add(...parts);
    }
    const r = some(f, isDiracDelta) ? deltaIntegral(f, x) : undefined;
    if (r !== undefined) return r;
    const s = some(f, isSingularityFunction) ? singularityIntegral(f, x) : undefined;
    const elementary = s ?? risch(f, x);
    if (elementary !== undefined) return elementary;
    const besselFactor = (t: Expr): boolean => t instanceof Fn && t.name === 'besselj' && at(t.args, 1).equals(x);
    const factors = f instanceof Mul ? f.args : [f];
    if (factors.some((t) => besselFactor(t) || t instanceof Pow && besselFactor(t.base)) &&
        factors.every((t) => !t.has(x) || t.equals(x) || besselFactor(t) || t instanceof Pow && t.exp instanceof Rational && t.exp.isInteger && (t.base.equals(x) || besselFactor(t.base)))) {
      // The pole order determines how many polynomial degrees are needed in
      // the adjacent-order Bessel basis of the heuristic Risch algorithm.
      const denominator = polyCoefficients(asNumerDenom(f)[1], x);
      const degree = Math.max(0, ...denominator?.keys() ?? []);
      const primitive = heurisch(f, x, { degreeOffset: Math.min(2, degree), retries: 0 });
      if (primitive !== undefined) return primitive;
    }
    // Keep inexact coefficient domains on the elementary integration route.
    if (some(f, (e) => e instanceof Float)) return undefined;
    // SymPy tries the manual rules after the elementary algorithms. The active
    // method guard also lets their unresolved subproblems return unevaluated.
    // The parallel Risch algorithm works over towers of exponentials and algebraic logarithmic extensions.
    if (f instanceof Mul && f.args.every(isExp)) return heurischWrapper(f, x, { retries: 0 });
    if (some(f, t => t instanceof Pow && t.exp.equals(S.Half) && t.base.has(log(x)))) {
      const elementary = heurisch(f, x, { retries: 0 });
      if (elementary !== undefined) return elementary;
    }
    const manual = manualintegrate(f, x);
    if (!some(manual, (e) => e instanceof Integral)) return manual;
    if (some(f, t => t instanceof Pow && t.base.equals(x) && !(t.exp instanceof Rational) && !t.exp.has(x))) {
      const result = meijerintIndefinite(f, x);
      return result && isNonZero(x) === true ? expandFull(result) : result;
    }
    return undefined;
  } finally {
    activeMethods.delete(key);
  }
}
const activeMethods = new Set<string>();

/** Integrate the absolute value of an affine sine or cosine by its half-periods. */
function definiteAbsTrig(f: Expr, x: Sym, a: Expr, b: Expr): Expr | undefined {
  if (!(f instanceof Fn) || f.name !== 'abs') return undefined;
  const wave = at(f.args, 0);
  if (!(wave instanceof Fn) || (wave.name !== 'sin' && wave.name !== 'cos')) return undefined;
  const argument = at(wave.args, 0);
  const coefficients = polyCoefficients(argument, x);
  if (coefficients === undefined || [...coefficients.keys()].some((degree) => degree > 1)) return undefined;
  const slope = coefficients.get(1);
  if (slope === undefined || isNonZero(slope) !== true || isReal(slope) !== true) return undefined;
  const u = wave.name === 'cos' ? add(argument, mul(S.Half, S.Pi)) : argument;
  const primitive = (point: Expr): Expr | undefined => {
    const value = subs(u, [[x, point]]);
    if (isReal(value) !== true) return undefined;
    const periods = floor(mul(value, pow(S.Pi, -1)));
    return periods instanceof Rational ? add(mul(2, periods), 1, mul(-1, cos(add(value, mul(-1, periods, S.Pi))))) : undefined;
  };
  const left = primitive(a), right = primitive(b);
  return left === undefined || right === undefined ? undefined : mul(add(right, mul(-1, left)), pow(slope, -1));
}

/**
 * risch_integrate as SymPy's integrate uses it: the elementary part, plus
 * the nonelementary integral when the elementary part is not zero (SymPy
 * then tries the other methods on it; here it is kept unevaluated).
 */
function risch(f: Expr, x: Sym): Expr | undefined {
  let result: Expr;
  let i: Expr;
  try {
    [result, i] = rischIntegrate(f, x, { separateIntegral: true });
  } catch {
    // integrands outside the transcendental elementary cases (trigonometric, algebraic, ...) raise
    // NotImplementedError; like SymPy, integrate then goes on with the other methods
    return undefined;
  }
  // the base case of rational functions in x may be left unevaluated
  if (some(result, (e) => e instanceof Integral)) return undefined;
  if (!(i instanceof NonElementaryIntegral)) return result;
  if (isZeroR(result)) return undefined;
  const rest = new Integrator(x).integrate(i.integrand) ?? manualintegrate(i.integrand, x);
  return add(result, some(rest, e => e instanceof Integral) ? new Integral([i.integrand, x]) : rest);
}

rischHooks.integrate = (f, x) => new Integrator(x).integrate(f) ?? new Integral([f, x]);

/** Construct an unevaluated integral with limits supplied innermost first. */
export function integral(ex: ExprLike, ...limits: readonly (ExprLike | readonly ExprLike[])[]): Expr {
  const f = sympify(ex);
  if (!limits.length) {
    const variables = [...f.freeSymbols()];
    if (variables.length !== 1) throw new RangeError('An integral needs an integration variable');
    return integral(f, at(variables, 0));
  }
  if (f instanceof Rel && f.op === 'Eq') return Eq(integral(f.lhs, ...limits), integral(f.rhs, ...limits));
  const isLimit = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);
  let result = f;
  for (const input of limits) {
    const parts = isLimit(input) ? input.map(sympify) : [sympify(input)];
    const variable = parts[0];
    if (parts.length > 3 || !(variable instanceof Sym || variable instanceof UndefFn || variable instanceof Derivative || variable instanceof ExtensionExpr)) {
      throw new RangeError('Invalid integration limit');
    }
    if (variable instanceof Derivative) diff(S.Zero, variable);
    // SymPy Integral.__new__: an integrand with _eval_Integral (vectors, dyadics, quaternions) integrates itself
    if (result instanceof ExtensionExpr && variable instanceof Sym && parts.length !== 2) {
      const [lower, upper] = parts.slice(1);
      const bounds: [Expr, Expr] | undefined = lower !== undefined && upper !== undefined ? [lower, upper] : undefined;
      const own = result.integrateSelf(variable, bounds, (g) => integrate(g, variable, bounds));
      if (own !== undefined) {
        result = own;
        continue;
      }
    }
    result = new Integral([result, ...parts]);
  }
  return result;
}

/**
 * Integrates an expression: the antiderivative, or the definite integral over a
 * range. Each variable is a symbol `x` (an antiderivative), `x` followed by its
 * range `[a, b]`, or the array `[x, a, b]` (SymPy's tuple `(x, a, b)`); several
 * variables give an iterated integral, the first innermost. An integral that
 * cannot be computed is returned unevaluated as an `Integral`.
 *
 * @param ex - The integrand.
 * @param limits - The variables and their ranges, optionally followed by the
 *   options: `conds: 'none'` drops the convergence conditions of a definite
 *   integral (`'piecewise'`, the default, returns them as a `Piecewise`);
 *   `heurisch: false` skips the heuristic Risch algorithm.
 * @returns The integral.
 * @throws RangeError when no variable is given or a limit has none of the forms.
 * @see SymPy `sympy.integrals.integrals.integrate`
 * @example
 * ```ts
 * import { ex, integrate, oo, symbols } from '@symjs/symjs';
 *
 * const [x, y, a] = symbols('x y a');
 * integrate(ex`x*y`, x); // => x**2*y/2
 * integrate(ex`log(x)`, x); // => x*log(x) - x
 * integrate(ex`log(x)`, x, [1, a]); // => a*log(a) - a + 1
 * integrate(ex`log(x)`, [x, 1, a]); // => a*log(a) - a + 1
 * integrate(ex`sqrt(1 + x)`, x, [0, x]); // => 2*(x + 1)**(3/2)/3 - 2/3
 * integrate(ex`x*y`, x, [0, 1], y, [0, 2]); // => 1
 * integrate(ex`x*y`, x, y); // => x**2*y**2/4
 * integrate(ex`x**a*exp(-x)`, x, [0, oo]); // => Piecewise((gamma(a + 1), re(a) > -1), (Integral(x**a*exp(-x), (x, 0, oo)), True))
 * integrate(ex`x**a*exp(-x)`, x, [0, oo], { conds: 'none' }); // => gamma(a + 1)
 * ```
 */
export function integrate(ex: ExprLike, ...limits: (IntegrateLimitArg | IntegrateOptions | undefined)[]): Expr {
  const given = limits.filter((a) => a !== undefined);
  const last = given[given.length - 1];
  const opts = isOptions(last) ? last : {};
  const variables = integrationLimits(isOptions(last) ? given.slice(0, -1) : given);
  // the first variable is the innermost integral, as in SymPy
  return variables.reduce<Expr>((f, [v, range]) => integrateSym(f, v, range, opts), sympify(ex));
}

/** The options of integrate, as opposed to its limits. */
const isOptions = (v: IntegrateLimitArg | IntegrateOptions | undefined): v is IntegrateOptions => typeof v === 'object' && !(v instanceof Expr) && !Array.isArray(v);

/** The variables of integrate with their ranges (undefined for an antiderivative), innermost first. */
function integrationLimits(args: readonly (IntegrateLimitArg | IntegrateOptions)[]): [Sym, readonly [ExprLike, ExprLike] | undefined][] {
  const usage = 'integrate: each limit is a symbol x, x followed by [a, b], or [x, a, b]; options come last';
  const out: [Sym, readonly [ExprLike, ExprLike] | undefined][] = [];
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a instanceof Sym) {
      const next = args[i + 1];
      const range = Array.isArray(next) && next.length === 2 ? next : undefined;
      if (range) {
        const [lo, hi]: readonly unknown[] = range;
        if (!isExprLike(lo) || !isExprLike(hi)) throw new RangeError(usage);
        out.push([a, [lo, hi]]);
        i++;
      } else out.push([a, undefined]);
      continue;
    }
    // (JavaScript callers may pass any value here)
    const parts: readonly unknown[] = Array.isArray(a) ? a : [];
    const [v, lo, hi] = parts;
    if (parts.length !== 3 || !(v instanceof Sym) || !isExprLike(lo) || !isExprLike(hi)) throw new RangeError(usage);
    out.push([v, [lo, hi]]);
  }
  if (!out.length) throw new RangeError('integrate: the integration variable must be given');
  return out;
}

const isExprLike = (v: unknown): v is ExprLike => v instanceof Expr || typeof v === 'number' || typeof v === 'bigint';

function integrateSym(ex: ExprLike, x: Sym, limits: readonly [ExprLike, ExprLike] | undefined, opts: IntegrateOptions): Expr {
  let f = sympify(ex);
  if (f instanceof Integral && impl.doit) {
    // On an interval with nonnegative endpoints its interior variable is positive.
    // Carry that fact into inner integrals before deciding where their poles lie.
    if (limits && limits.every(v => fact(sympify(v), 'nonnegative') === true) && !f.boundSymbols.some(v => v.equals(x))) {
      const positive = new Dummy(x.name, { positive: true });
      f = subs(impl.doit(subs(f, [[x, positive]])), [[positive, x]]);
    } else f = impl.doit(f);
  }
  if (f instanceof Concrete && f.kind2 === 'Sum') {
    const bounds = f.limits.flat();
    if (bounds.some((v) => v.has(x))) throw new RangeError('A summation limit depends on the integration variable');
    if (bounds.some((v) => v instanceof Special)) return new Integral([f, x, ...(limits ?? []).map(sympify)]);
    const term = integrate(f.function, x, limits, opts);
    const sum = new Concrete('Sum', [term, ...bounds]);
    return impl.doit?.(sum) ?? sum;
  }
  if (f instanceof Rel && f.op === 'Eq') return Eq(integrate(f.lhs, x, limits, opts), integrate(f.rhs, x, limits, opts));
  if (limits && sympify(limits[1]).equals(S.Infinity)) {
    const lower = sympify(limits[0]);
    // The oscillatory Gaussian is the limit of the absolutely convergent
    // Gaussian with an additional factor exp(-epsilon*x**2).
    if (lower.equals(S.NegativeInfinity) && isExp(f)) {
      const rate = cancel(mul(f.exp, S.I, pow(x, -2)));
      if (!rate.has(x) && isPositiveQ(rate) === true) return mul(-1, S.I, sqrt(mul(S.Pi, pow(rate, -1))), exp(mul(S.I, S.Pi, Rational.of(1, 4))));
    }
    // Frullani's cosine difference has endpoint log(b/a) for a,b > 0.
    if (lower.equals(S.Zero) && f instanceof Mul) {
      const numerator = mul(f, x);
      if (numerator instanceof Add && numerator.args.length === 2) {
        const terms = numerator.args.map(t => asIndependent(t, [x], { asAdd: false }));
        if (terms.every(([, t]) => t instanceof Fn && t.name === 'cos')) {
          const [[c, first], [d, second]] = pair(terms);
          const a = cancel(mul(at(first.args, 0), pow(x, -1))), b = cancel(mul(at(second.args, 0), pow(x, -1)));
          if (add(c, d).equals(S.Zero) && !a.has(x) && !b.has(x) && isPositiveQ(a) === true && isPositiveQ(b) === true) return mul(c, add(log(b), mul(-1, log(a))));
        }
      }
    }
  }
  if (limits && f instanceof Fn && f.name === 'sin') {
    const a = sympify(limits[0]), b = sympify(limits[1]), u = at(f.args, 0);
    // sin is bounded on the real axis, including on either side of a removable or oscillatory singularity.
    const positive = new Dummy('p', { positive: true });
    const right = subs(u, [[x, positive]]), left = subs(u, [[x, mul(-1, positive)]]);
    if (a.equals(mul(-1, b)) && fact(b, 'real') === true && isReal(right) === true && add(left, right).equals(S.Zero)) return S.Zero;
  }
  if (limits && f instanceof Pow && f.exp.equals(S.Half) && f.base instanceof Add && hasTrigFunctions(f.base)) {
    const a = sympify(limits[0]), b = sympify(limits[1]);
    if (cmpReal(a, b) === -1) {
      const radicand = mapBottomUp(factor(f.base), (v) => v instanceof Add ? trigsimp(v) : v);
      const factors = radicand instanceof Mul ? radicand.args : [radicand];
      const roots: Expr[] = [];
      for (const v of factors) {
        if (isPositiveQ(v) === true) roots.push(sqrt(v));
        else if (v instanceof Pow && v.exp.equals(S.Two) && v.base instanceof Fn && (v.base.name === 'sin' || v.base.name === 'cos') && v.base.args[0]?.equals(x)) {
          const side = trigIntervalSign(v.base, a, b);
          if (side) roots.push(mul(side, v.base));
        }
      }
      if (roots.length === factors.length) f = mul(...roots);
    }
  }
  if (limits || isReal(x) === true) f = realIntegrand(f, x) ?? f;
  if (limits) {
    const periodic = definiteAbsTrig(f, x, sympify(limits[0]), sympify(limits[1]));
    if (periodic !== undefined) return periodic;
  }
  if (f instanceof ExtensionExpr) {
    const own = f.integrateSelf(x, limits && [sympify(limits[0]), sympify(limits[1])], (g) => integrate(g, x, limits, opts));
    if (own !== undefined) return own;
  }
  // a Piecewise whose conditions contain relations free of x: one integral for each of their truth values
  if (f instanceof Piecewise) {
    const r = handleIrel(f, x, (g) => integrate(g, x, limits, opts));
    if (r !== undefined) return r;
    if (limits) {
      const a = sympify(limits[0]);
      const b = sympify(limits[1]);
      const result = definitePiecewise(f, x, a, b) ?? symbolicDefinitePiecewise(f, x, a, b);
      if (result !== undefined) return result;
    }
  }
  // an integral that stays unevaluated keeps the integrand as given (SymPy returns Integral(p, (x, a, b)))
  const given = f;
  const unevaluatedAsGiven = (result: Expr): Expr => (limits && result instanceof Integral && given !== f ? new Integral([given, x, sympify(limits[0]), sympify(limits[1])]) : result);
  if (limits && some(f, (e) => e instanceof Piecewise)) {
    const [a, b] = [sympify(limits[0]), sympify(limits[1])];
    f = simplifyConditionsOnInterval(decideConditionsOnInterval(f, x, a, b), x, a, b);
  }
  // sums and constant multiples containing a Piecewise: term by term
  const hasPw = (e: Expr): boolean => e instanceof Piecewise || e.args.some(hasPw);
  if (f instanceof Add && f.args.some(hasPw)) {
    const parts = f.args.map((t) => integrate(t, x, limits, opts));
    if (!parts.some((r) => r instanceof Integral)) return add(...parts);
  }
  // a product with a Piecewise factor: one Piecewise (SymPy piecewise_fold)
  if (f instanceof Mul && f.args.some((t) => t instanceof Piecewise)) {
    return integrate(piecewiseFold(f), x, limits, opts);
  }
  if (f instanceof Piecewise && !limits) {
    const r = integratePiecewise(f, x);
    if (r) return r;
  }
  // The mean over a full period of 1/(a+b*exp(I*x)) is its constant Fourier coefficient.
  if (limits && sympify(limits[0]).equals(S.Zero) && sympify(limits[1]).equals(mul(2, S.Pi)) && f instanceof Pow && f.exp.equals(S.NegOne)) {
    const coefficients = polyCoefficients(f.base, exp(mul(S.I, x)));
    const a = coefficients?.get(0), b = coefficients?.get(1);
    if (coefficients?.size === 2 && a instanceof Rational && b instanceof Rational) {
      const sign = cmpReal(pow(a, 2), pow(b, 2));
      if (sign === 1) return mul(2, S.Pi, numInv(a));
      if (sign === -1) return S.Zero;
    }
  }
  const F0 = opts.heurisch ? (opts.conds === 'none' ? heurisch(f, x) : heurischWrapper(f, x))
    : f instanceof Piecewise ? integratePiecewise(f, x) : (new Integrator(x, opts.conds === 'none', limits?.some(v => !sympify(v).isNumber)).integrate(f) ?? otherMethods(f, x));
  if (opts.heurisch && limits && F0 instanceof Piecewise && F0.pairs.every(([, c]) => !c.has(x)) && singularPoints(f, x, sympify(limits[0]), sympify(limits[1]))?.length === 0) {
    return piecewise(...F0.pairs.map(([v, c]): [Expr, Expr] => {
      const condition = c instanceof Rel && c.op === 'Ne' && c.rhs.equals(S.Zero) ? and(Gt(c.lhs, S.NegativeInfinity), Lt(c.lhs, S.Infinity), c) : c;
      return [add(subs(v, [[x, sympify(limits[1])]]), mul(-1, subs(v, [[x, sympify(limits[0])]]))), condition];
    }));
  }
  const F = F0 && continuousAtan(F0);
  if (!limits) return F ?? new Integral([f, x]);
  const a = sympify(limits[0]);
  const b = sympify(limits[1]);
  if (F === undefined) return unevaluatedAsGiven(definiteWithoutAntiderivative(f, x, a, b, opts));
  // Use one-sided limits at each numerical interior singularity.
  if (a.key === b.key) return S.Zero;
  const points = singularPoints(f, x, a, b);
  const unevaluated = new Integral([f, x, a, b]);
  // unresolved singularities: unevaluated, or for an infinite limit as without an antiderivative (SymPy tries the
  // Meijer G-functions first for those)
  if (points === undefined) return f instanceof Add || [a, b].some((e) => e instanceof Special) ? definiteWithoutAntiderivative(f, x, a, b, opts) : unevaluated;
  const order = cmpReal(a, b);
  if (order !== undefined && order > 0) return mul(-1, integrate(f, x, [b, a], opts));
  const interior: Expr[] = [];
  const bad = (e: Expr): boolean => e instanceof Special || impl.accumBounds?.is(e) === true || e.args.some(bad);
  for (const p of points) {
    const left = cmpSign(p, a);
    const right = cmpSign(p, b);
    if (left === undefined || right === undefined) {
      // An integrable singularity with a continuous primitive needs no split,
      // even when the position of a parametric pole is unknown.
      const l = impl.limit(F, x, p, '-');
      const r = impl.limit(F, x, p, '+');
      if (l.key === r.key && !bad(l) && !l.has(x)) continue;
      return definiteWithoutAntiderivative(f, x, a, b, opts);
    }
    if (left > 0 && right < 0) interior.push(p);
  }
  interior.sort((p, q) => defined(cmpReal(p, q), 'constant real singularities'));
  const endpoint = (p: Expr, dir: '+' | '-'): Expr => {
    const v = subs(heavisideAtInfinity(F, x, p), [[x, p]]);
    return bad(v) ? impl.limit(F, x, p, dir) : v;
  };
  const bounds = [a, ...interior, b];
  const parts: Expr[] = [];
  const isInfinity = (v: Expr): boolean => v === S.Infinity || v === S.NegativeInfinity;
  for (let i = 1; i < bounds.length; i++) {
    try {
      const lower = endpoint(at(bounds, i - 1), '+');
      const upper = endpoint(at(bounds, i), '-');
      // an endpoint whose limit is not found: the integral as without an antiderivative (the Meijer G-functions)
      if ([lower, upper].some((v) => some(v, (e) => e.kind === 'Limit'))) return definiteWithoutAntiderivative(f, x, a, b, opts);
      if (isInfinity(upper) && rootIsReal(lower) === true) parts.push(upper);
      else if (isInfinity(lower) && rootIsReal(upper) === true) parts.push(mul(-1, lower));
      else parts.push(add(upper, mul(-1, lower)));
    } catch (error) {
      if (error instanceof NotImplementedError) return unevaluated;
      throw error;
    }
  }
  return add(...parts);
}


/** A definite integral by the Gamma function rule or the Meijer G-function integrator, else unevaluated. */
function definiteWithoutAntiderivative(f: Expr, x: Sym, a: Expr, b: Expr, opts: { conds?: 'piecewise' | 'none' }): Expr {
  if (f instanceof Add && !(a instanceof Special || b instanceof Special)) {
    const terms = f.args.map((t) => {
      const [coefficient, rest] = asIndependent(t, [x], { asAdd: false });
      return mul(coefficient, integrate(rest, x, [a, b], opts));
    });
    if (terms.some((t) => !some(t, (v) => v instanceof Integral || v instanceof Special))
        && !terms.some((t) => some(t, (v) => v instanceof Special))) return add(...terms);
  }
  const unevaluated = new Integral([f, x, a, b]);
  // Fourier coefficients of 1/(c+d*cos(x)) follow from the Poisson kernel.
  if (a.equals(S.Zero) && b.equals(mul(2, S.Pi))) {
    const [numerator, denominator] = asNumerDenom(f);
    if (numerator instanceof Fn && numerator.name === 'cos') {
      const n = cancel(mul(at(numerator.args, 0), pow(x, -1)));
      const coefficients = polyCoefficients(denominator, cos(x));
      if (n instanceof Rational && n.isInteger && coefficients?.size === 2 && coefficients.has(0) && coefficients.has(1)) {
        const c = getOrThrow(coefficients, 0), d = getOrThrow(coefficients, 1);
        const discriminant = add(pow(c, 2), mul(-1, pow(d, 2)));
        if (!c.has(x) && !d.has(x) && isReal(d) === true && isPositiveQ(c) === true && isPositiveQ(discriminant) === true) {
          const h = sqrt(discriminant), ratio = mul(-1, d, pow(add(c, h), -1));
          return mul(2, S.Pi, pow(h, -1), pow(ratio, babs(n.p)));
        }
      }
    }
  }
  if (a instanceof Rational && a.isZero && b instanceof Special && b.name === 'oo') {
    const g = gammaIntegral(f, x);
    if (g) {
      const [val, cond] = g;
      if (cond === true || opts.conds === 'none') return val;
      return piecewise([val, cond], [unevaluated, true]);
    }
  }
  // u = log(x) gives the derivative of Gamma at 1 divided by the rate.
  if (a.equals(S.One) && b.equals(S.Infinity) && f instanceof Mul && f.has(log(log(x)))) {
    const rest = mul(...f.args.filter((v) => !v.equals(log(log(x)))));
    if (rest instanceof Pow && rest.base.equals(x)) {
      const rate = add(-1, mul(-1, rest.exp));
      if (!rate.has(x) && isPositiveQ(rate) === true) return mul(-1, add(S.EulerGamma, log(rate)), pow(rate, -1));
    }
  }
  if (a.equals(S.Zero) && b.equals(S.Infinity) && f instanceof Pow && f.exp.equals(S.NegOne)) {
    if (f.base instanceof Fn && f.base.name === 'cosh') {
      const rate = cancel(mul(at(f.base.args, 0), pow(x, -1)));
      if (!rate.has(x) && isPositiveQ(rate) === true) return mul(S.Pi, pow(mul(2, rate), -1));
    }

  }
  // SymPy's Meijer G-function integrator (not for piecewise integrands)
  const m = some(f, (e) => e instanceof Piecewise) ? undefined : meijerintDefinite(f, x, a, b);
  if (m && !some(m[0], (e) => e instanceof Integral)) {
    const [val, cond] = m;
    if (opts.conds === 'none') return val;
    return piecewise([val, cond], [unevaluated, true]);
  }
  return unevaluated;
}

impl.integrate = (e, ...limits) => integrate(e, ...limits);

/**
 * atan(c*tan(a) + d) jumps where tan(a) has a pole: SymPy's Integral.doit adds
 * sign(c)*pi*floor((a - pi/2)/pi) so that the antiderivative is continuous
 * (and sign(c)*pi*floor(a/pi) for cot(a), which the antiderivatives here
 * do not contain).
 */
function continuousAtan(F: Expr): Expr {
  let G = F;
  const atans = new Map<string, Expr>();
  const visit = (e: Expr): void => {
    if (e instanceof Fn && e.name === 'atan') atans.set(e.key, e);
    e.args.forEach(visit);
  };
  visit(F);
  for (const term of atans.values()) {
    const arg = at(term.args, 0);
    const parts = new Map<string, Fn>();
    const find = (e: Expr): void => {
      if (e instanceof Fn && e.name === 'tan') parts.set(e.key, e);
      e.args.forEach(find);
    };
    find(arg);
    for (const part of parts.values()) {
      const x1 = new Dummy('x1');
      const coeff = diff(subs(arg, [[part, x1]]), x1);
      if (coeff.has(x1)) continue;
      const a = at(part.args, 0);
      const shift = floor(mul(add(a, mul(-1, S.Pi, S.Half)), pow(S.Pi, -1)));
      G = subs(G, [[term, add(term, mul(sign(coeff), S.Pi, shift))]]);
    }
  }
  return G;
}



/** x*f(x) - Integral(f'(x)*x) for special functions (SymPy results). */
const SPECIAL_PARTS: Record<string, (x: Expr) => Expr> = {
  li: (x) => mul(-1, fnErf('Ei', [mul(2, log(x))])),
  Ei: (x) => mul(-1, exp(x)),
  Si: (x) => cos(x),
  Shi: (x) => mul(-1, cosh(x)),
  erf: (x) => mul(exp(mul(-1, pow(x, 2))), pow(sqrt(S.Pi), -1)),
  erfc: (x) => mul(-1, exp(mul(-1, pow(x, 2))), pow(sqrt(S.Pi), -1)),
  erfi: (x) => mul(-1, exp(pow(x, 2)), pow(sqrt(S.Pi), -1)),
  asin: (x) => sqrt(add(1, mul(-1, pow(x, 2)))),
  acos: (x) => mul(-1, sqrt(add(1, mul(-1, pow(x, 2))))),
  atan: (x) => mul(Rational.of(-1, 2), log(add(pow(x, 2), 1))),
  asinh: (x) => mul(-1, sqrt(add(pow(x, 2), 1))),
  acot: (x) => mul(S.Half, log(add(pow(x, 2), 1))),
};


/**
 * Integral(c*x**a*exp(-b*x), (x, 0, oo)) = c*gamma(a + 1)/b**(a + 1) for
 * re(a) > -1 and b > 0 (SymPy's Mellin-transform result). Returns the value
 * and the convergence condition (true when it is known to hold).
 */
function gammaIntegral(f: Expr, x: Sym): [Expr, Expr | true] | undefined {
  const factors = f instanceof Mul ? f.args : [f];
  let a: Expr | undefined;
  let b: Expr | undefined;
  const c: Expr[] = [];
  for (const g of factors) {
    if (!g.has(x)) c.push(g);
    else if (g.key === x.key && a === undefined) a = S.One;
    else if (g instanceof Pow && g.base.key === x.key && !g.exp.has(x) && a === undefined) a = g.exp;
    else if (g instanceof Pow && g.base instanceof Constant && g.base.name === 'E' && b === undefined) {
      const k = cancel(mul(-1, g.exp, pow(x, -1)));
      if (k.has(x)) return undefined;
      b = k;
    } else return undefined;
  }
  // (without one of the factors the integrand has an elementary antiderivative and is not passed here)
  const [A, B] = [defined(a, 'power of x'), defined(b, 'exponential')];
  if (isPositiveQ(B) !== true) return undefined;
  const val = mul(...c, fnErf('gamma', [add(A, 1)]), pow(B, mul(-1, add(A, 1))));
  if (isPositiveQ(add(A, 1)) === true) return [val, true];
  return [val, Gt(fnErf('re', [A]), S.NegOne)];
}

/** A Piecewise agreeing with f on the open real intervals between its polynomial roots. */
export function realIntegrand(f: Expr, x: Sym): Expr | undefined {
  const targets: [Fn, Expr][] = [];
  const points = new Map<string, Expr>();
  for (const e of preorderTraversal(f)) {
    if (!(e instanceof Fn) || !['abs', 'sign', 'Min', 'Max'].includes(e.name) || !e.has(x)) continue;
    const args = e.args;
    if (args.length > 2) return undefined;
    // Exponentiation preserves the order of real arguments.
    const realX = new Dummy('x', { real: true });
    const values = args.length === 2 && args.every(isExp) && args.every(v => isReal(xreplace(v.exp, [[x, realX]])) === true)
      ? args.map(v => v.exp) : args;
    const p = values.length === 1 ? at(values, 0) : add(at(values, 0), mul(-1, at(values, 1)));
    const pc = polyCoefficients(p, x);
    if (pc === undefined || [...pc.keys()].some((k) => k > 3) || fact(xreplace(p, [[x, realX]]), 'extended_real') !== true) return undefined;
    targets.push([e, p]);
    for (const r of roots(p, x)) {
      if (rootIsReal(r) === false) continue;
      points.set(r.key, r);
    }
  }
  if (!targets.length) return undefined;
  const breaks = [...points.values()];
  if (breaks.some((p, i) => breaks.slice(i + 1).some((q) => cmpReal(p, q) === undefined))) return undefined;
  breaks.sort((p, q) => defined(cmpReal(p, q), 'ordered real roots'));
  const pieces: [Expr, Expr][] = [];
  for (let i = 0; i <= breaks.length; i++) {
    const left = breaks[i - 1];
    const right = breaks[i];
    const sample = left === undefined ? right === undefined ? S.Zero : add(right, -1) : right === undefined ? add(left, 1) : mul(S.Half, add(left, right));
    const replacements: [Expr, Expr][] = [];
    for (const [node, p] of targets) {
      const value = xreplace(p, [[x, sample]]).expand();
      const negative = isNegative(value);
      const positive = isPositive(value);
      if (negative !== true && positive !== true) return undefined;
      const a = at(node.args, 0);
      const result = node.name === 'abs' ? mul(negative ? -1 : 1, a)
        : node.name === 'sign' ? negative ? S.NegOne : S.One
        : node.name === 'Min' ? negative ? a : at(node.args, 1)
        : negative ? at(node.args, 1) : a;
      replacements.push([node, result]);
    }
    const branch = mapBottomUp(f, (e) => replacements.find(([node]) => node.key === e.key)?.[1] ?? e);
    const strict = targets.some(([node]) => node.name === 'sign');
    pieces.push([branch, right === undefined ? S.true : strict ? Lt(x, right) : Le(x, right)]);
  }
  return piecewise(...pieces);
}
