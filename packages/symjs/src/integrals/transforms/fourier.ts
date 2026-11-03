// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Fourier, sine, cosine and Hankel transforms (SymPy
 * fourier_transform, sine_transform, cosine_transform, hankel_transform and
 * their inverses).
 *
 * SymPy evaluates the defining integrals with its Meijer G integrator.
 * symjs evaluates them with a table of the classic integrals over the half
 * line and the real line: powers (Mellin transforms of the kernels),
 * exponentials, Gaussians and Lorentzians times powers of x (obtained by
 * differentiating with respect to the parameter), Heaviside and DiracDelta
 * factors, and the Hankel transforms of exponentials and of powers of
 * x**2 + b**2.
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { Sym } from '../../core/nodes';
import { Add, Constant, Dummy, Fn, Integral, Mul, Pow, Rational, S } from '../../core/nodes';
import { add, exp, mul, neg, pow, sqrt, sub, sympify } from '../../core/ops';
import { isNegative, isPositive } from '../../core/assumptions';

import { mapBottomUp, subs, xreplace } from '../../core/traverse';
import { abs, cos, re, sin } from '../../functions/elementary';
import { gamma } from '../../functions/special';
import { besselj, besselk } from '../../functions/bessel';
import { diff } from '../../calculus/diff';
import { Poly } from '../../polys/sympoly';
import { expand } from '../../simplify/expand';
import { posify, powdenest, powsimp } from '../../simplify/powsimp';
import { simplify as simplifyExpr } from '../../simplify/simplify';
import { rewrite } from '../../simplify/rewrite';
import type { TransformHints, TransformResult } from './base';
import { GenericIntegralTransform, IntegralTransform, IntegralTransformError, addArgs, asSymbolVariable, isPolyIn, matchByName, mget, mulArgs, polyCoeffs as polyCoeffsIn, wild, transformArgs } from './base';
import { at, defined, pair } from '../../core/guard';
import { isDiracDelta, isHeaviside } from './delta';

const isExpPow = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
const expOf = (e: Pow): Expr => e.exp;
const isRat = (e: Expr): e is Rational => e instanceof Rational;
const isNonNegInt = (e: Expr): e is Rational => e instanceof Rational && e.isInteger && !e.isNegative;

/** The kernels of the half-line transforms. */
type Kernel = { kind: 'sin' } | { kind: 'cos' } | { kind: 'besselj'; nu: Expr };

/** Split f into C * x**(mu - 1) * rest with C and mu free of x: returns [C, mu, rest]. */
function splitPower(f: Expr, x: Sym): [Expr, Expr, Expr[]] {
  let C: Expr = S.One;
  let mu: Expr = S.One;
  const rest: Expr[] = [];
  for (const fac of mulArgs(f)) {
    if (!fac.has(x)) C = mul(C, fac);
    else if (fac.key === x.key) mu = add(mu, 1);
    else if (fac instanceof Pow && fac.base.key === x.key && !fac.exp.has(x)) mu = add(mu, fac.exp);
    else rest.push(fac);
  }
  return [C, mu, rest];
}

/** Apply (-d/da)**n to F(a). */
function negDiff(F: Expr, a: Expr, n: number): Expr {
  let r = F;
  for (let i = 0; i < n; i++) r = neg(diff(r, a));
  return r;
}

/** K_nu(z) for half-integer nu in closed form, besselk otherwise. */
function besselkClosed(nu: Expr, z: Expr): Expr {
  if (isRat(nu) && (nu.key === S.Half.key || nu.key === S.NegHalf.key)) return mul(sqrt(mul(S.Pi, pow(mul(2, z), -1))), exp(neg(z)));
  return besselk(nu, z);
}

/** The integral over (0, oo) of x**(mu - 1)*K(k*x) (the Mellin transform of the kernel). */
function powerKernel(mu: Expr, k: Expr, kernel: Kernel): Expr | undefined {
  const num = mu.isNumber ? mu.toNumber() : NaN;
  if (kernel.kind === 'sin') {
    if (!Number.isNaN(num) && !(num > -1 && num < 1)) return undefined;
    return mul(pow(2, sub(mu, 1)), sqrt(S.Pi), gamma(mul(add(1, mu), S.Half)), pow(gamma(sub(1, mul(mu, S.Half))), -1), pow(k, neg(mu)));
  }
  if (kernel.kind === 'cos') {
    if (!Number.isNaN(num) && !(num > 0 && num < 1)) return undefined;
    return mul(pow(2, sub(mu, 1)), sqrt(S.Pi), gamma(mul(mu, S.Half)), pow(gamma(mul(sub(1, mu), S.Half)), -1), pow(k, neg(mu)));
  }
  const nu = kernel.nu;
  return mul(2, pow(2, sub(mu, 2)), gamma(mul(add(nu, mu), S.Half)), pow(gamma(add(mul(sub(nu, mu), S.Half), 1)), -1), pow(k, neg(mu)));
}

/**
 * Write powers (A + k**2)**p with a non-integer p as k**(2*p)*(A/k**2 + 1)**p,
 * the form in which SymPy's hyperexpand returns Hankel transforms.
 */
function hyperexpandForm(e: Expr, k: Expr): Expr {
  const r = mapBottomUp(e, (t) => {
    if (!(t instanceof Pow) || !(t.base instanceof Add) || (isRat(t.exp) && t.exp.isInteger) || t.exp.has(k)) return t;
    const terms = t.base.args;
    const k2 = pow(k, 2);
    if (!terms.some((u) => u.key === k2.key) || terms.length !== 2) return t;
    const A = defined(terms.find((u) => u.key !== k2.key), 'the other term');
    if (A.has(k)) return t;
    return mul(pow(k, mul(2, t.exp)), pow(add(mul(A, pow(k, -2)), 1), t.exp));
  });
  // k**a*k**b = k**(a + b), which symjs keeps apart for symbolic exponents
  return mapBottomUp(r, (t) => {
    if (!(t instanceof Mul)) return t;
    let e: Expr = S.Zero;
    let n = 0;
    const rest: Expr[] = [];
    for (const f of t.args) {
      if (f.key === k.key) {
        e = add(e, 1);
        n++;
      } else if (f instanceof Pow && f.base.key === k.key) {
        e = add(e, f.exp);
        n++;
      } else rest.push(f);
    }
    return n > 1 ? mul(...rest, pow(k, e)) : t;
  });
}

/**
 * Normalize powers of sums that contain negative powers of k (k > 0):
 * (A/k**2 + 1)**p -> (A + k**2)**p*k**(-2*p).
 */
function normalizePositive(e: Expr, k: Expr): Expr {
  return mapBottomUp(e, (t) => {
    if (!(t instanceof Pow) || !(t.base instanceof Add) || t.exp.has(k)) return t;
    const terms = t.base.args;
    const negPow = (u: Expr): number => {
      let d = 0;
      for (const f of mulArgs(u)) if (f instanceof Pow && f.base.key === k.key && isRat(f.exp) && f.exp.isNegative) d = Math.max(d, -f.exp.value);
      return d;
    };
    const d = Math.max(...terms.map(negPow));
    if (d === 0 || !Number.isInteger(d)) return t;
    const nb = expand(mul(t.base, pow(k, d)));
    if (!isPolyIn(nb, k)) return t;
    return mul(pow(nb, t.exp), pow(k, mul(-d, t.exp)));
  });
}

/** The integral over (0, oo) of f(x)*K(k*x), or undefined. */
function halfLineIntegral(f0: Expr, x: Sym, k: Expr, kernel: Kernel): Expr | undefined {
  const kp = new Dummy('k', { positive: true });
  const f = normalizePositive(f0, x);
  const [C, mu, rest] = splitPower(f, x);
  const alpha = wild('alpha', x);
  const beta = wild('beta', x);
  let r: Expr | undefined;
  if (rest.length === 0) {
    r = powerKernel(mu, kp, kernel);
  } else if (rest.length === 1) {
    const g = at(rest, 0);
    const n = sub(mu, 1);
    if (isExpPow(g)) {
      const e = expOf(g);
      const m1 = matchByName(e, mul(-1, alpha, x));
      const m2 = m1 ? undefined : matchByName(e, mul(-1, alpha, pow(x, 2)));
      if (m1 && isNonNegInt(n)) {
        // exp(-a*x): k/(a**2 + k**2), a/(a**2 + k**2), the Hankel form for J_nu
        const a = new Dummy('a');
        const q = sqrt(add(pow(a, 2), pow(kp, 2)));
        let base: Expr;
        if (kernel.kind === 'sin') base = mul(kp, pow(add(pow(a, 2), pow(kp, 2)), -1));
        else if (kernel.kind === 'cos') base = mul(a, pow(add(pow(a, 2), pow(kp, 2)), -1));
        else base = mul(pow(kp, neg(kernel.nu)), pow(sub(q, a), kernel.nu), pow(q, -1));
        r = subs(negDiff(base, a, Number(n.p)), [[a, mget(m1, 'alpha')]]);
      } else if (m1 && kernel.kind === 'besselj' && (mu.key === add(kernel.nu, 2).key || mu.key === add(kernel.nu, 1).key)) {
        // Bateman 8.6 (4.14.7/8): r**(nu + 1)*exp(-a*r) and r**nu*exp(-a*r)
        const nu = kernel.nu;
        const A = mget(m1, 'alpha');
        r =
          mu.key === add(nu, 2).key
            ? mul(pow(2, add(nu, 1)), A, pow(kp, nu), gamma(add(nu, Rational.of(3n, 2n))), pow(sqrt(S.Pi), -1), pow(add(pow(A, 2), pow(kp, 2)), sub(neg(nu), Rational.of(3n, 2n))))
            : mul(pow(2, nu), pow(kp, nu), gamma(add(nu, S.Half)), pow(sqrt(S.Pi), -1), pow(add(pow(A, 2), pow(kp, 2)), sub(neg(nu), S.Half)));
      } else if (m2) {
        const a = new Dummy('a');
        const A = mget(m2, 'alpha');
        if (kernel.kind === 'cos' && isNonNegInt(n) && n.p % 2n === 0n) {
          const base = mul(S.Half, sqrt(mul(S.Pi, pow(a, -1))), exp(mul(-1, pow(kp, 2), pow(mul(4, a), -1))));
          r = subs(negDiff(base, a, Number(n.p / 2n)), [[a, A]]);
        } else if (kernel.kind === 'sin' && isNonNegInt(n) && n.p % 2n === 1n) {
          const base = mul(sqrt(S.Pi), kp, exp(mul(-1, pow(kp, 2), pow(mul(4, a), -1))), pow(mul(4, pow(a, Rational.of(3n, 2n))), -1));
          r = subs(negDiff(base, a, Number((n.p - 1n) / 2n)), [[a, A]]);
        } else if (kernel.kind === 'besselj') {
          const j = mul(sub(n, add(kernel.nu, 1)), S.Half);
          if (isNonNegInt(j)) {
            const base = mul(pow(kp, kernel.nu), pow(pow(mul(2, a), add(kernel.nu, 1)), -1), exp(mul(-1, pow(kp, 2), pow(mul(4, a), -1))));
            r = subs(negDiff(base, a, Number(j.p)), [[a, A]]);
          }
        }
      }
    } else if (g instanceof Pow && g.base instanceof Add && !g.exp.has(x)) {
      const m = matchByName(g.base, add(pow(x, 2), beta));
      if (m) {
        const B = mget(m, 'beta');
        const b = powdenest(sqrt(B), { force: true });
        if (kernel.kind === 'cos' && g.exp.key === S.NegOne.key && mu.key === S.One.key) r = mul(S.Pi, exp(mul(-1, b, kp)), pow(mul(2, b), -1));
        else if (kernel.kind === 'sin' && g.exp.key === S.NegOne.key && mu.key === S.Two.key) r = mul(S.Pi, S.Half, exp(mul(-1, b, kp)));
        else if (kernel.kind === 'besselj' && mu.key === add(kernel.nu, 2).key) {
          const lam = sub(neg(g.exp), 1);
          const nu = kernel.nu;
          r = mul(pow(kp, lam), pow(b, sub(nu, lam)), besselkClosed(sub(nu, lam), mul(b, kp)), pow(mul(pow(2, lam), gamma(add(lam, 1))), -1));
        }
      }
    }
  } else if (rest.length === 2 && kernel.kind === 'cos' && mu.key === S.One.key) {
    // exp(-a*sqrt(x))*cos(a*sqrt(x))
    const ex = rest.find(isExpPow);
    const co = rest.find((u): u is Fn => u instanceof Fn && u.name === 'cos');
    if (ex !== undefined && co !== undefined) {
      const m1 = matchByName(expOf(ex), mul(-1, alpha, sqrt(x)));
      const m2 = matchByName(at(co.args, 0), mul(beta, sqrt(x)));
      if (m1 && m2 && mget(m1, 'alpha').key === mget(m2, 'beta').key) {
        const a = mget(m1, 'alpha');
        r = mul(sqrt(mul(S.Pi, S.Half)), a, exp(mul(-1, pow(a, 2), pow(mul(2, kp), -1))), pow(mul(2, pow(kp, Rational.of(3n, 2n))), -1));
      }
    }
  }
  if (r === undefined) return undefined;
  return xreplace(mul(C, r), [[kp, k]]);
}

/** The integral over the real line of f(x)*exp(I*B*k*x), or undefined. */
function realLineIntegral(f: Expr, x: Sym, Bk: Expr): Expr | undefined {
  const facs = mulArgs(f);
  let C: Expr = S.One;
  let n = 0;
  let E: Expr = S.Zero;
  const rest: Expr[] = [];
  for (const fac of facs) {
    if (!fac.has(x)) C = mul(C, fac);
    else if (fac.key === x.key) n += 1;
    else if (fac instanceof Pow && fac.base.key === x.key && isNonNegInt(fac.exp)) n += Number(fac.exp.p);
    else if (isExpPow(fac)) E = add(E, expOf(fac));
    else rest.push(fac);
  }
  const iBk = mul(S.I, Bk);
  if (rest.length === 0 && isPolyIn(E, x)) {
    const p = Poly.from(expand(E), [x]);
    if (p.degree() !== 2) return undefined;
    const cs = p.allCoeffs();
    const [c2, c1, c0] = [at(cs, 0), at(cs, 1), at(cs, 2)];
    const a = neg(c2);
    if (isPositive(a) === false) return undefined;
    const b = new Dummy('b');
    const base = mul(sqrt(mul(S.Pi, pow(a, -1))), exp(mul(pow(add(b, iBk), 2), pow(mul(4, a), -1))));
    let r = base;
    for (let i = 0; i < n; i++) r = diff(r, b);
    return mul(C, exp(c0), subs(r, [[b, c1]]));
  }
  if (rest.length === 0 && n === 0) {
    // exp(-a*Abs(x))
    const alpha = wild('alpha', x);
    const m = matchByName(E, mul(-1, alpha, abs(x)));
    if (m) {
      const a = mget(m, 'alpha');
      return mul(C, 2, a, pow(sub(pow(a, 2), pow(iBk, 2)), -1));
    }
  }
  if (rest.length === 1 && n === 0) {
    const g = at(rest, 0);
    if (isDiracDelta(g) && g.args.length === 1 && isPolyIn(at(g.args, 0), x) && E.key === S.Zero.key) {
      const p = Poly.from(at(g.args, 0), [x]);
      if (p.degree() === 1) {
        const [s1, s0] = pair(p.allCoeffs());
        const x0 = mul(-1, s0, pow(s1, -1));
        return mul(C, exp(mul(iBk, x0)), pow(abs(s1), -1));
      }
    }
  }
  if (rest.some((g) => isHeaviside(g) && g.args.length === 1 && at(g.args, 0).key === x.key)) {
    // Heaviside(x)*x**n*exp(-c*x)*(sines and cosines): sum of n!/(c - I*B*k)**(n + 1)
    const others = rest.filter((g) => !(isHeaviside(g) && g.args.length === 1 && at(g.args, 0).key === x.key));
    const body = expand(rewrite(mul(pow(x, n), exp(E), ...others), 'exp'));
    const out: Expr[] = [];
    for (const term of addArgs(body)) {
      const parts = mulArgs(powsimp(term, { combine: 'exp' }));
      let c: Expr = S.One;
      let k = 0;
      let e: Expr = S.Zero;
      for (const f of parts) {
        if (!f.has(x)) c = mul(c, f);
        else if (f.key === x.key) k += 1;
        else if (f instanceof Pow && f.base.key === x.key && isNonNegInt(f.exp)) k += Number(f.exp.p);
        else if (isExpPow(f)) e = add(e, expOf(f));
        else return undefined;
      }
      const lin = polyCoeffsIn(e, x);
      if (!lin || lin.length > 2) return undefined;
      const cc = lin.length === 2 ? neg(at(lin, 0)) : S.Zero;
      if (lin.length === 2) c = mul(c, exp(at(lin, 1)));
      else c = mul(c, exp(at(lin, 0)));
      if (cc.key === S.Zero.key || isNegative(re(cc)) === true) return undefined;
      let fact = 1;
      for (let i = 2; i <= k; i++) fact *= i;
      out.push(mul(c, fact, pow(sub(cc, iBk), -(k + 1))));
    }
    return mul(C, add(...out));
  }
  return undefined;
}

/** SymPy transforms._simplify for these transforms. */
function finish(F: Expr, simplify: boolean): Expr {
  if (!simplify) return F;
  // powdenest(polar=True) in SymPy: the symbols are treated as positive
  const [P, back] = posify(F);
  const s1 = simplifyExpr(powsimp(P));
  const s2 = xreplace(s1, [...back].map(([d, v]) => [d, v] as [Expr, Expr]));
  // SymPy's results keep the arguments of gamma functions expanded
  return mapBottomUp(s2, (t) => (t instanceof Fn && t.name === 'gamma' ? gamma(expand(at(t.args, 0))) : t));
}

// ---------------------------------------------------------------------------
// Fourier transforms
// ---------------------------------------------------------------------------

/**
 * Base class of the Fourier-type transforms a*Integral(f*exp(b*I*x*k), (x, -oo, oo))
 * (SymPy FourierTypeTransform).
 */
export abstract class FourierTypeTransform extends GenericIntegralTransform {
  /** The constant factor a. */
  abstract a(): Expr;
  /** The frequency factor b. */
  abstract b(): Expr;
  protected override get defaultNoconds(): boolean {
    return true;
  }
  get asIntegral(): Expr {
    const x = this.functionVariable;
    return new Integral([mul(this.a(), this.function, exp(mul(this.b(), S.I, x, this.transformVariable))), x, S.NegativeInfinity, S.Infinity]);
  }
  protected computeTransform(f: Expr, x: Sym, k: Sym, hints: TransformHints & { simplify: boolean }): TransformResult {
    const r = realLineIntegral(f, x, mul(this.b(), k));
    if (r === undefined) throw new IntegralTransformError(this.transformName, f, 'could not compute integral');
    const F = finish(mul(this.a(), r), hints.simplify);
    return hints.noconds === false ? [F, S.true] : F;
  }
}

/** The unevaluated Fourier transform (SymPy FourierTransform). */
export class FourierTransform extends FourierTypeTransform {
  constructor(f: ExprLike, x: ExprLike, k: ExprLike) {
    super('FourierTransform', [sympify(f), sympify(x), sympify(k)]);
  }
  /** SymPy FourierTransform._name. */
  static readonly transformName = 'Fourier';
  get transformName(): string {
    return 'Fourier';
  }
  protected get latexName(): string {
    return '\\mathcal{F}';
  }
  a(): Expr {
    return S.One;
  }
  b(): Expr {
    return mul(-2, S.Pi);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new FourierTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new FourierTransform(f, this.functionVariable, this.transformVariable);
  }
}

/** The unevaluated inverse Fourier transform (SymPy InverseFourierTransform). */
export class InverseFourierTransform extends FourierTypeTransform {
  constructor(F: ExprLike, k: ExprLike, x: ExprLike) {
    super('InverseFourierTransform', [sympify(F), sympify(k), sympify(x)]);
  }
  /** SymPy InverseFourierTransform._name. */
  static readonly transformName = 'Inverse Fourier';
  get transformName(): string {
    return 'Inverse Fourier';
  }
  protected get latexName(): string {
    return '\\mathcal{F}^{-1}';
  }
  a(): Expr {
    return S.One;
  }
  b(): Expr {
    return mul(2, S.Pi);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new InverseFourierTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new InverseFourierTransform(f, this.functionVariable, this.transformVariable);
  }
}

/**
 * The unitary, ordinary-frequency Fourier transform of f, the integral of
 * f(x)*exp(-2*pi*I*x*k) over the real line (SymPy fourier_transform).
 * Returns F, [F, cond] with `noconds: false`, or an unevaluated
 * FourierTransform.
 *
 * @example
 * fourierTransform(exp(-x**2), x, k)  // sqrt(pi)*exp(-pi**2*k**2)
 */
export function fourierTransform(f: ExprLike, x: Sym, k: ExprLike, hints: TransformHints = {}): TransformResult {
  return new FourierTransform(f, x, k).doit(hints);
}

/**
 * The unitary, ordinary-frequency inverse Fourier transform of F, the
 * integral of F(k)*exp(2*pi*I*x*k) over the real line (SymPy
 * inverse_fourier_transform).
 */
export function inverseFourierTransform(F: ExprLike, k: Sym, x: ExprLike, hints: TransformHints = {}): TransformResult {
  return new InverseFourierTransform(F, k, x).doit(hints);
}

// ---------------------------------------------------------------------------
// Sine and cosine transforms
// ---------------------------------------------------------------------------

/**
 * Base class of the sine and cosine transforms
 * a*Integral(f*K(b*x*k), (x, 0, oo)) (SymPy SineCosineTypeTransform).
 */
export abstract class SineCosineTypeTransform extends GenericIntegralTransform {
  /** The kernel sin or cos. */
  abstract get kernel(): 'sin' | 'cos';
  /** The constant factor a. */
  a(): Expr {
    return mul(sqrt(2), pow(sqrt(S.Pi), -1));
  }
  /** The frequency factor b. */
  b(): Expr {
    return S.One;
  }
  protected override get defaultNoconds(): boolean {
    return true;
  }
  get asIntegral(): Expr {
    const x = this.functionVariable;
    const arg = mul(this.b(), x, this.transformVariable);
    return new Integral([mul(this.a(), this.function, this.kernel === 'sin' ? sin(arg) : cos(arg)), x, S.Zero, S.Infinity]);
  }
  protected computeTransform(f: Expr, x: Sym, k: Sym, hints: TransformHints & { simplify: boolean }): TransformResult {
    const r = halfLineIntegral(f, x, mul(this.b(), k), { kind: this.kernel });
    if (r === undefined) throw new IntegralTransformError(this.transformName, f, 'could not compute integral');
    const F = finish(mul(this.a(), r), hints.simplify);
    return hints.noconds === false ? [F, S.true] : F;
  }
}

/** The unevaluated sine transform (SymPy SineTransform). */
export class SineTransform extends SineCosineTypeTransform {
  constructor(f: ExprLike, x: ExprLike, k: ExprLike) {
    super('SineTransform', [sympify(f), sympify(x), sympify(k)]);
  }
  /** SymPy SineTransform._name. */
  static readonly transformName = 'Sine';
  get transformName(): string {
    return 'Sine';
  }
  protected get latexName(): string {
    return '\\mathcal{SIN}';
  }
  get kernel(): 'sin' {
    return 'sin';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new SineTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new SineTransform(f, this.functionVariable, this.transformVariable);
  }
}

/** The unevaluated inverse sine transform (SymPy InverseSineTransform). */
export class InverseSineTransform extends SineCosineTypeTransform {
  constructor(F: ExprLike, k: ExprLike, x: ExprLike) {
    super('InverseSineTransform', [sympify(F), sympify(k), sympify(x)]);
  }
  /** SymPy InverseSineTransform._name. */
  static readonly transformName = 'Inverse Sine';
  get transformName(): string {
    return 'Inverse Sine';
  }
  protected get latexName(): string {
    return '\\mathcal{SIN}^{-1}';
  }
  get kernel(): 'sin' {
    return 'sin';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new InverseSineTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new InverseSineTransform(f, this.functionVariable, this.transformVariable);
  }
}

/** The unevaluated cosine transform (SymPy CosineTransform). */
export class CosineTransform extends SineCosineTypeTransform {
  constructor(f: ExprLike, x: ExprLike, k: ExprLike) {
    super('CosineTransform', [sympify(f), sympify(x), sympify(k)]);
  }
  /** SymPy CosineTransform._name. */
  static readonly transformName = 'Cosine';
  get transformName(): string {
    return 'Cosine';
  }
  protected get latexName(): string {
    return '\\mathcal{COS}';
  }
  get kernel(): 'cos' {
    return 'cos';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CosineTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new CosineTransform(f, this.functionVariable, this.transformVariable);
  }
}

/** The unevaluated inverse cosine transform (SymPy InverseCosineTransform). */
export class InverseCosineTransform extends SineCosineTypeTransform {
  constructor(F: ExprLike, k: ExprLike, x: ExprLike) {
    super('InverseCosineTransform', [sympify(F), sympify(k), sympify(x)]);
  }
  /** SymPy InverseCosineTransform._name. */
  static readonly transformName = 'Inverse Cosine';
  get transformName(): string {
    return 'Inverse Cosine';
  }
  protected get latexName(): string {
    return '\\mathcal{COS}^{-1}';
  }
  get kernel(): 'cos' {
    return 'cos';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new InverseCosineTransform(...transformArgs(args));
  }
  protected withFunction(f: Expr): IntegralTransform {
    return new InverseCosineTransform(f, this.functionVariable, this.transformVariable);
  }
}

/**
 * The unitary sine transform sqrt(2/pi)*Integral(f(x)*sin(x*k), (x, 0, oo))
 * (SymPy sine_transform).
 *
 * @example
 * sineTransform(x*exp(-a*x**2), x, k)  // sqrt(2)*k*exp(-k**2/(4*a))/(4*a**(3/2))
 */
export function sineTransform(f: ExprLike, x: Sym, k: ExprLike, hints: TransformHints = {}): TransformResult {
  return new SineTransform(f, x, k).doit(hints);
}

/** The inverse sine transform sqrt(2/pi)*Integral(F(k)*sin(x*k), (k, 0, oo)) (SymPy inverse_sine_transform). */
export function inverseSineTransform(F: ExprLike, k: Sym, x: ExprLike, hints: TransformHints = {}): TransformResult {
  return new InverseSineTransform(F, k, x).doit(hints);
}

/**
 * The unitary cosine transform sqrt(2/pi)*Integral(f(x)*cos(x*k), (x, 0, oo))
 * (SymPy cosine_transform).
 *
 * @example
 * cosineTransform(exp(-a*x), x, k)  // sqrt(2)*a/(sqrt(pi)*(a**2 + k**2))
 */
export function cosineTransform(f: ExprLike, x: Sym, k: ExprLike, hints: TransformHints = {}): TransformResult {
  return new CosineTransform(f, x, k).doit(hints);
}

/** The inverse cosine transform sqrt(2/pi)*Integral(F(k)*cos(x*k), (k, 0, oo)) (SymPy inverse_cosine_transform). */
export function inverseCosineTransform(F: ExprLike, k: Sym, x: ExprLike, hints: TransformHints = {}): TransformResult {
  return new InverseCosineTransform(F, k, x).doit(hints);
}

// ---------------------------------------------------------------------------
// Hankel transforms
// ---------------------------------------------------------------------------

/**
 * Base class of the Hankel transforms Integral(f(r)*besselj(nu, k*r)*r, (r, 0, oo))
 * (SymPy HankelTypeTransform). Unlike the other transforms, SymPy raises
 * IntegralTransformError when the integral cannot be computed.
 */
export abstract class HankelTypeTransform extends IntegralTransform {
  /** The order nu of the Bessel function. */
  get nu(): Expr {
    return at(this.args, 3);
  }
  get asIntegral(): Expr {
    const r = this.functionVariable;
    return new Integral([mul(this.function, besselj(this.nu, mul(this.transformVariable, r)), r), r, S.Zero, S.Infinity]);
  }
  /** Evaluate (SymPy doit); throws IntegralTransformError when the integral is not known. */
  doit(hints: TransformHints = {}): TransformResult {
    const f = this.function;
    const r = this.functionVariable;
    if (!(r instanceof Sym)) return this;
    const ks = asSymbolVariable(this.transformVariable);
    const k = ks.sym;
    const v = halfLineIntegral(mul(f, r), r, k, { kind: 'besselj', nu: this.nu });
    if (v === undefined) throw new IntegralTransformError(this.transformName, f, 'could not compute integral');
    const simplify = hints.simplify ?? true;
    const F = ks.back(hyperexpandForm(finish(v, simplify), k));
    return hints.noconds === false ? [F, S.true] : F;
  }
}

/** The unevaluated Hankel transform (SymPy HankelTransform). */
export class HankelTransform extends HankelTypeTransform {
  constructor(f: ExprLike, r: ExprLike, k: ExprLike, nu: ExprLike) {
    super('HankelTransform', [sympify(f), sympify(r), sympify(k), sympify(nu)]);
  }
  /** SymPy HankelTransform._name. */
  static readonly transformName = 'Hankel';
  get transformName(): string {
    return 'Hankel';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new HankelTransform(...transformArgs(args), at(args, 3));
  }
}

/** The unevaluated inverse Hankel transform (SymPy InverseHankelTransform). */
export class InverseHankelTransform extends HankelTypeTransform {
  constructor(F: ExprLike, k: ExprLike, r: ExprLike, nu: ExprLike) {
    super('InverseHankelTransform', [sympify(F), sympify(k), sympify(r), sympify(nu)]);
  }
  /** SymPy InverseHankelTransform._name. */
  static readonly transformName = 'Inverse Hankel';
  get transformName(): string {
    return 'Inverse Hankel';
  }
  withArgs(args: readonly Expr[]): Expr {
    return new InverseHankelTransform(...transformArgs(args), at(args, 3));
  }
}

/**
 * The Hankel transform Integral(f(r)*besselj(nu, k*r)*r, (r, 0, oo))
 * (SymPy hankel_transform). Throws IntegralTransformError when the integral
 * is not known, as SymPy does.
 *
 * @example
 * hankelTransform(exp(-a*r), r, k, 0)  // a/(k**3*(a**2/k**2 + 1)**(3/2))
 */
export function hankelTransform(f: ExprLike, r: Sym, k: ExprLike, nu: ExprLike, hints: TransformHints = {}): TransformResult {
  return new HankelTransform(f, r, k, nu).doit(hints);
}

/** The inverse Hankel transform Integral(F(k)*besselj(nu, k*r)*k, (k, 0, oo)) (SymPy inverse_hankel_transform). */
export function inverseHankelTransform(F: ExprLike, k: Sym, r: ExprLike, nu: ExprLike, hints: TransformHints = {}): TransformResult {
  return new InverseHankelTransform(F, k, r, nu).doit(hints);
}

