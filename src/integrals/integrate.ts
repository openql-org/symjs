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

import { isNonZero } from '../core/assumptions';
import { Ne, piecewise } from '../core/logic';
import {
  Add,
  Constant,
  Expr,
  ExprLike,
  Fn,
  Integral,
  Mul,
  Pow,
  Rational,
  S,
  Special,
  Sym,
  impl,
  isNum,
} from '../core/nodes';
import { numAdd, numInv, numMul, numNeg } from '../core/num';
import { gcd, lcm } from '../core/numbers';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { asin, atan, cos, cosh, log, sin, sinh } from '../functions/elementary';
import { Poly, polyCoefficients } from '../polys/poly';
import { expand } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { expsimp, hasTrigFunctions } from '../simplify/trigsimp';

type R = Expr | undefined;

const isE = (e: Expr) => e instanceof Constant && e.name === 'E';
const isI = (e: Expr) => e instanceof Constant && e.name === 'I';
const isExp = (e: Expr): boolean => e instanceof Pow && isE(e.base);
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
    if ([...pc.keys()].some((k) => k > 1)) return undefined;
    const a = pc.get(1);
    if (!a) return undefined;
    return [a, pc.get(0) ?? S.Zero];
  }

  /**
   * Return F, or Piecewise((F, Ne(a, 0)), (fallback, True)) when the
   * coefficient a might be zero (SymPy behavior for symbolic coefficients).
   */
  private nonzero(a: Expr, f: Expr, F: () => R): R {
    if (isNum(a) || isNonZero(a) === true || a.freeSymbols().size === 0) return F();
    const factors = (a instanceof Mul ? a.args : [a]).filter((t) => !isNum(t) && !isI(t));
    const cond = mul(...factors);
    const main = F();
    if (main === undefined) return undefined;
    const rest = this.integrate(subs(f, [[cond, S.Zero]]));
    if (rest === undefined) return undefined;
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
      this.derivativeDivides(f) ??
      this.trigPowers(f) ??
      this.byParts(f) ??
      this.expImaginary(f) ??
      this.rational(f) ??
      this.expanded(f)
    );
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
        if (q && q.size === 2 && q.has(0) && q.has(2)) {
          const c = q.get(0)!;
          const k = mul(-1, q.get(2)!);
          if (isNum(c) && isNum(k) && c.isPositive && k.isPositive) {
            return mul(asin(mul(sqrt(mul(k, pow(c, -1))), x)), pow(sqrt(k), -1));
          }
        }
      }
    }
    if (f instanceof Fn) {
      const u = f.args[0]!;
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
          case 'asin':
          case 'acos':
          case 'atan':
            if (u.key === x.key) {
              // integration by parts: x*f(x) - Integral(x*f'(x))
              const r = this.integrate(mul(x, diff(f, x)));
              return r === undefined ? undefined : add(mul(x, f), mul(-1, r));
            }
            break;
          default:
            break;
        }
      }
    }
    return undefined;
  }

  // ---- derivative divides --------------------------------------------------

  private derivativeDivides(f: Expr): R {
    const x = this.x;
    const factors = f instanceof Mul ? f.args : [f];
    for (const g of factors) {
      if (!(g instanceof Pow) || this.free(g.base) || !(g.exp instanceof Rational)) continue;
      const [base, n] = [g.base, g.exp];
      const rest = mul(...factors.filter((t) => t !== g));
      const db = diff(base, x);
      if (isZeroR(db)) continue;
      let q: Expr;
      try {
        q = cancel(mul(rest, pow(db, -1)));
      } catch {
        continue;
      }
      if (!this.free(q)) continue;
      if (n.p === -1n && n.q === 1n) return mul(q, log(base));
      const n1 = numAdd(n, S.One) as Rational;
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
      const arg = base.args[0]!;
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
      const pc = polyCoefficients(p, s)!;
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
      const g = others[0]!;
      // P * exp(a*x + b)
      if (isExp(g)) {
        const lin = this.linear((g as Pow).exp);
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
        const u = g.args[0]!;
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
      if (t instanceof Fn && t.name === 'log' && t.args[0]!.key === x.key) return 1;
      if (t instanceof Pow && t.base instanceof Fn && t.base.name === 'log' && t.base.args[0]!.key === x.key) {
        return t.exp instanceof Rational && t.exp.isInteger && t.exp.p > 0n ? Number(t.exp.p) : 0;
      }
      return 0;
    });
    if (others.length === 1 && logs[0]! > 0) {
      const k = logs[0]!;
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
      const e = others.find(isExp) as Pow | undefined;
      const t = others.find((o) => o instanceof Fn && (o.name === 'sin' || o.name === 'cos')) as Fn | undefined;
      if (e && t) {
        const l1 = this.linear(e.exp);
        const u = t.args[0]!;
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
      (isExp(e) && (e as Pow).exp.has(S.I)) || e.args.some(hasImagExp);
    if (!hasImagExp(f)) return undefined;
    const g = expsimp(f);
    if (g.key === f.key) return undefined;
    return this.integrate(g);
  }

  // ---- rational functions ------------------------------------------------------

  private rational(f: Expr): R {
    const x = this.x;
    let N: Expr;
    let D: Expr;
    try {
      [N, D] = fraction(together(f));
    } catch {
      return undefined;
    }
    const pn = Poly.fromExpr(N, x);
    const pd = Poly.fromExpr(D, x);
    if (!pn || !pd || pd.degree < 1) return undefined;
    const [q, r] = pn.divmod(pd);
    const terms: Expr[] = [];
    if (!q.isZero) {
      const qi = this.integrate(q.toExpr(x));
      if (qi === undefined) return undefined;
      terms.push(qi);
    }
    if (r.isZero) return add(...terms);

    const { factors } = pd.factor();
    // basis: for each factor f_i^m_i, j = 1..m_i and k < deg f_i: x^k * D / f_i^j
    const unknowns: { f: Poly; j: number; k: number }[] = [];
    const columns: Poly[] = [];
    for (const [fi, mi] of factors) {
      for (let j = 1; j <= mi; j++) {
        let fj = new Poly([S.One]);
        for (let t = 0; t < j; t++) fj = fj.mul(fi);
        const cof = pd.divmod(fj)[0];
        for (let k = 0; k < fi.degree; k++) {
          const xk = new Poly([...Array.from({ length: k }, () => S.Zero), S.One]);
          unknowns.push({ f: fi, j, k });
          columns.push(cof.mul(xk));
        }
      }
    }
    const n = pd.degree;
    if (columns.length !== n) return undefined;
    const sol = solveLinear(
      Array.from({ length: n }, (_, row) => columns.map((col) => col.coeffs[row] ?? S.Zero)),
      Array.from({ length: n }, (_, row) => r.coeffs[row] ?? S.Zero),
    );
    if (!sol) return undefined;

    // group numerators A_ij(x) = sum_k c_ijk x^k
    const groups = new Map<string, { f: Poly; j: number; A: Rational[] }>();
    unknowns.forEach(({ f: fi, j, k }, idx) => {
      const key = `${fi.coeffs.map((c) => c.key).join(',')}|${j}`;
      let g = groups.get(key);
      if (!g) {
        g = { f: fi, j, A: Array.from({ length: fi.degree }, () => S.Zero) };
        groups.set(key, g);
      }
      g.A[k] = sol[idx]!;
    });

    for (const { f: fi, j, A } of groups.values()) {
      const fx = fi.toExpr(x);
      if (fi.degree === 1) {
        const alpha = A[0]!;
        if (alpha.isZero) continue;
        if (j === 1) terms.push(mul(alpha, log(fx)));
        else terms.push(mul(numNeg(alpha), Rational.of(1, j - 1), pow(fx, 1 - j)));
      } else if (fi.degree === 2 && j === 1) {
        const [beta, alpha] = [A[0]!, A[1]!];
        const b = fi.coeffs[1]!;
        const c = fi.coeffs[0]!;
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

/** Split a polynomial expression with rational coefficients into positive content and primitive part. */
function primitive(e: Expr, x: Sym): [Rational, Expr] {
  const pc = polyCoefficients(e, x);
  if (!pc) return [S.One, e];
  const cs = [...pc.values()];
  if (!cs.every((c): c is Rational => c instanceof Rational)) return [S.One, e];
  let num = 0n;
  let den = 1n;
  for (const c of cs) {
    num = gcd(num, c.p);
    den = lcm(den, c.q);
  }
  if (num === 0n) return [S.One, e];
  const content = Rational.of(num, den);
  if (content.isOne) return [S.One, e];
  return [content, expand(mul(Rational.of(den, num), e))];
}

/** Solve a square linear system over the rationals (Gauss-Jordan). */
function solveLinear(A: Rational[][], b: Rational[]): Rational[] | undefined {
  const n = b.length;
  const M = A.map((row, i) => [...row, b[i]!]);
  for (let col = 0; col < n; col++) {
    const piv = M.findIndex((row, i) => i >= col && !row[col]!.isZero);
    if (piv < 0) return undefined;
    [M[col], M[piv]] = [M[piv]!, M[col]!];
    const inv = numInv(M[col]![col]!) as Rational;
    M[col] = M[col]!.map((v) => numMul(v, inv) as Rational);
    for (let i = 0; i < n; i++) {
      if (i === col || M[i]![col]!.isZero) continue;
      const k = M[i]![col]!;
      M[i] = M[i]!.map((v, jj) => numAdd(v, numNeg(numMul(k, M[col]![jj]!))) as Rational);
    }
  }
  return M.map((row) => row[n]!);
}

/**
 * Integrate f with respect to x. With limits [a, b] the definite integral
 * F(b) - F(a) is returned. If no antiderivative is found, an unevaluated
 * `Integral` is returned (like SymPy).
 */
export function integrate(ex: ExprLike, x: Sym, limits?: readonly [ExprLike, ExprLike]): Expr {
  const f = sympify(ex);
  const F = new Integrator(x).integrate(f);
  if (!limits) return F ?? new Integral([f, x]);
  const a = sympify(limits[0]);
  const b = sympify(limits[1]);
  if (F === undefined) return new Integral([f, x, a, b]);
  // endpoint values: substitute, or take a one-sided limit at infinities / indeterminate points
  const at = (p: Expr, dir: '+' | '-'): Expr => {
    const v = subs(F, [[x, p]]);
    const bad = (e: Expr): boolean => e instanceof Special || e.args.some(bad);
    return bad(v) ? impl.limit(F, x, p, dir) : v;
  };
  return add(at(b, '-'), mul(-1, at(a, '+')));
}

impl.integrate = (e, x, limits) => integrate(e, x, limits);

