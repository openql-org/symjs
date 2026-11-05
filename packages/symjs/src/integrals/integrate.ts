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

import { isNegative as isNegativeQ, isNonZero, isPositive as isPositiveQ, isReal } from '../core/assumptions';
import { AccumBounds } from '../core/accumbounds';
import { Gt, Ne, piecewise } from '../core/logic';
import type {
  Expr,
  ExprLike,
  RelOp } from '../core/nodes';
import {
  Add,
  BoolAtom,
  Constant,
  Dummy,
  ExtensionExpr,
  Fn,
  Integral,
  Mul,
  Piecewise,
  Pow,
  Rational,
  Rel,
  S,
  Special,
  Sym,
  impl,
  isNum,
} from '../core/nodes';
import { cmpReal } from '../sets/sets';
import { numAdd, numInv, numMul, numNeg } from '../core/num';
import { at, defined, expectType, getOrThrow, pair } from '../core/guard';
import { gcd, lcm } from '../core/numbers';
import { add, exp, mul, pow, sqrt, sympify } from '../core/ops';
import { mapBottomUp as mapBottomUpI, piecewiseFold, some, xreplace as subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { asin, atan, cos, cosh, log, sin, sinh } from '../functions/elementary/elementary';
import { UPoly, polyCoefficients, roots } from '../polys/poly';
import { fn as fnErf } from '../functions/elementary/elementary';
import { expand as expandFull, expandMul as expand } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { expsimp, hasTrigFunctions } from '../simplify/trigsimp';
import { meijerintDefinite } from './meijerint';
import { NonElementaryIntegral, rischHooks, rischIntegrate } from './risch';
import { isDiracDelta, isHeaviside, isSingularityFunction } from './transforms/delta';
import { deltaIntegral } from './deltafunctions';
import { singularityIntegral } from './singularityfunctions';
import { cancelFraction, isRationalIn, ratint } from './rationaltools';
import { trigintegrate } from './trigonometry';
import { heurischTrig } from './heurisch';
import { sqrtQuadraticRule } from './manualintegrate';
import { floor, sign } from '../functions/special/special';
import { and, or } from '../core/boolalg';
import { ordered } from '../core/match';
import { reduceInequalities } from '../solvers/inequalities';
import { RootSumNode } from '../polys/rootsum';
import { asIndependent, asNumerDenom } from '../core/methods';

type R = Expr | undefined;

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
const isI = (e: Expr) => e instanceof Constant && e.name === 'I';
const isRational = (v: unknown): v is Rational => v instanceof Rational;
const isExp = (e: Expr): e is Pow => e instanceof Pow && isE(e.base);
const isZeroR = (e: Expr) => e instanceof Rational && e.isZero;

class Integrator {
  private depth = 0;

  constructor(private readonly x: Sym) {}

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
    if (isNum(a) || isNonZero(a) === true || a.freeSymbols().size === 0) return F();
    const factors = (a instanceof Mul ? a.args : [a]).filter((t) => !isNum(t) && !isI(t));
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
        return piecewise([mul(pow(x, add(n, 1)), pow(add(n, 1), -1)), Ne(n, -1)], [log(x), true]);
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
      if (this.free(b)) {
        const lin = this.linear(n);
        if (lin) {
          const [a] = lin;
          if (isE(b)) return this.nonzero(a, f, () => mul(f, pow(a, -1)));
          return this.nonzero(a, f, () => mul(f, pow(mul(a, log(b)), -1)));
        }
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
            return inv(log(cosh(u)));
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
      const inner = e instanceof Fn ? [...e.args, e] : e instanceof Pow && e.base instanceof Constant && e.base.name === 'E' ? [e.exp] : [];
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
      const t = new Sym('_u');
      const g = subs(q, [[u, t]]);
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
        }
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
    if (!lin) return undefined;
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

  private byParts(f: Expr): R {
    const x = this.x;
    const factors = f instanceof Mul ? [...f.args] : [f];
    const polyPart: Expr[] = [];
    const others: Expr[] = [];
    for (const t of factors) (polyCoefficients(t, x) ? polyPart : others).push(t);
    const P = mul(...polyPart);

    if (others.length === 1) {
      const g = at(others, 0);
      // P * exp(a*x + b)
      if (isExp(g)) {
        const lin = this.linear(g.exp);
        if (lin && polyPart.length > 0) {
          const [a] = lin;
          return this.nonzero(a, f, () => {
            const terms: Expr[] = [];
            let d = P;
            for (let k = 0; !isZeroR(d); k++) {
              terms.push(mul(k % 2 === 0 ? 1 : -1, d, pow(a, -(k + 1))));
              d = diff(d, x);
            }
            const Q = expand(add(...terms));
            const [content, prim] = primitive(Q, x);
            return mul(content, prim, g);
          });
        }
      }
      // P * sin/cos(a*x + b)
      if (g instanceof Fn && (g.name === 'sin' || g.name === 'cos') && polyPart.length > 0) {
        const u = at(g.args, 0);
        const lin = this.linear(u);
        if (lin) {
          const [a] = lin;
          const ia = pow(a, -1);
          const I_sin = (p: Expr): Expr =>
            isZeroR(p) ? S.Zero : add(mul(-1, p, cos(u), ia), mul(ia, I_cos(diff(p, x))));
          const I_cos = (p: Expr): Expr =>
            isZeroR(p) ? S.Zero : add(mul(p, sin(u), ia), mul(-1, ia, I_sin(diff(p, x))));
          return this.nonzero(a, f, () => expand(g.name === 'sin' ? I_sin(P) : I_cos(P)));
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
    if (polyPart.length === 0 && others.length === 2) {
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
          const inner =
            t.name === 'sin'
              ? add(mul(a, sin(u)), mul(-1, b, cos(u)))
              : add(mul(a, cos(u)), mul(b, sin(u)));
          return expand(mul(e, inner, den));
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
      continue;
    }
    if (!(c instanceof Rel) || !(c.op === 'Lt' || c.op === 'Le') || c.lhs.key !== x.key || c.rhs.has(x)) return undefined;
    out.push([e, c.rhs]);
  }
  return out;
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
      const c = free.length === 1 && sym ? reduceInequalities(andargs, [sym]) : and(...andargs);
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
  if (!br) return undefined;
  const pieces: [Expr, Expr][] = [];
  let prevF: Expr | undefined;
  let prevBreak: Expr | undefined;
  for (const [e, c] of br) {
    let F = new Integrator(x).integrate(e);
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

/** Polynomial singularities of an integrand; undefined means their location is unresolved. */
function singularPoints(f: Expr, x: Sym): Expr[] | undefined {
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
    if (!polyCoefficients(base, x)) {
      // Bound real sine/cosine factors before declaring the poles unresolved:
      // e.g. 2 + cos(x) lies in [1, 3] and never vanishes on the real axis.
      const realX = new Dummy('x', { real: true });
      const bounded = mapBottomUpI(base, (e) => e instanceof Fn && (e.name === 'sin' || e.name === 'cos') && isReal(subs(at(e.args, 0), [[x, realX]])) === true ? AccumBounds(-1, 1) : e);
      if (bounded instanceof AccumBounds && (isPositiveQ(bounded.min) === true || isNegativeQ(bounded.max) === true)) continue;
      return undefined;
    }
    try {
      for (const r of roots(base, x)) {
        // Numerical ordering is used only for constant real roots, never for parameters.
        const real = cmpReal(r, S.Zero);
        if (real !== undefined) points.set(r.key, r);
        else if (r.freeSymbols().size !== 0) return undefined;
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
    return s ?? risch(f, x);
  } finally {
    activeMethods.delete(key);
  }
}
const activeMethods = new Set<string>();

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
  const rest = new Integrator(x).integrate(i.integrand);
  return add(result, rest ?? new Integral([i.integrand, x]));
}

rischHooks.integrate = (f, x) => new Integrator(x).integrate(f) ?? new Integral([f, x]);

export function integrate(ex: ExprLike, x: Sym, limits?: readonly [ExprLike, ExprLike], opts: { conds?: 'piecewise' | 'none' } = {}): Expr {
  let f = sympify(ex);
  if (f instanceof ExtensionExpr) {
    const own = f.integrateSelf(x, limits && [sympify(limits[0]), sympify(limits[1])], (g) => integrate(g, x, limits, opts));
    if (own !== undefined) return own;
  }
  // a Piecewise whose conditions contain relations free of x: one integral for each of their truth values
  if (f instanceof Piecewise) {
    const r = handleIrel(f, x, (g) => integrate(g, x, limits, opts));
    if (r !== undefined) return r;
  }
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
  const F0 = f instanceof Piecewise ? integratePiecewise(f, x) : (new Integrator(x).integrate(f) ?? otherMethods(f, x));
  const F = F0 && continuousAtan(F0);
  if (!limits) return F ?? new Integral([f, x]);
  const a = sympify(limits[0]);
  const b = sympify(limits[1]);
  if (F === undefined) return definiteWithoutAntiderivative(f, x, a, b, opts);
  // An antiderivative's endpoint difference is valid only between singularities.
  // Evaluate the two sides independently: this is an improper integral, not a principal value.
  if (a.key === b.key) return S.Zero;
  const points = singularPoints(f, x);
  const unevaluated = new Integral([f, x, a, b]);
  // unresolved singularities: unevaluated, or for an infinite limit as without an antiderivative (SymPy tries the
  // Meijer G-functions first for those)
  if (points === undefined) return [a, b].some((e) => e instanceof Special) ? definiteWithoutAntiderivative(f, x, a, b, opts) : unevaluated;
  const order = cmpReal(a, b);
  if (order !== undefined && order > 0) return mul(-1, integrate(f, x, [b, a], opts));
  const interior: Expr[] = [];
  const bad = (e: Expr): boolean => e instanceof Special || e.args.some(bad);
  for (const p of points) {
    const left = cmpSign(p, a);
    const right = cmpSign(p, b);
    if (left === undefined || right === undefined) {
      // An integrable singularity with a continuous primitive needs no split,
      // even when a symbolic endpoint prevents ordering (e.g. integral of log(x)).
      const l = impl.limit(F, x, p, '-');
      const r = impl.limit(F, x, p, '+');
      if (l.key === r.key && !bad(l) && !l.has(x)) continue;
      return unevaluated;
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
  for (let i = 1; i < bounds.length; i++) {
    parts.push(add(endpoint(at(bounds, i), '-'), mul(-1, endpoint(at(bounds, i - 1), '+'))));
  }
  return add(...parts);
}


/** A definite integral by the Gamma function rule or the Meijer G-function integrator, else unevaluated. */
function definiteWithoutAntiderivative(f: Expr, x: Sym, a: Expr, b: Expr, opts: { conds?: 'piecewise' | 'none' }): Expr {
  const unevaluated = new Integral([f, x, a, b]);
  if (a instanceof Rational && a.isZero && b instanceof Special && b.name === 'oo') {
    const g = gammaIntegral(f, x);
    if (g) {
      const [val, cond] = g;
      if (cond === true || opts.conds === 'none') return val;
      return piecewise([val, cond], [unevaluated, true]);
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

impl.integrate = (e, x, limits) => integrate(e, x, limits);

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
