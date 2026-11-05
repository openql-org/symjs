// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Equation solving (SymPy-compatible results): single equations,
 * linear and polynomial systems, undetermined coefficients and nsolve.
 */

import { NonInvertibleMatrixError, NotImplementedError } from '../core/errors';
import { solvePolySystem } from './polysys';
import { ask, Q } from '../core/refine';
import type { ExprLike } from '../core/nodes';
import { Expr, Add, Constant, Dummy, Float, Fn, Mul, Pow, Rational, Rel, S, Special, Sym, impl, isNum } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, subs, xreplace, xreplace as xreplaceS } from '../core/traverse';
import type { Truth } from '../core/truth';
import { at, cast, defined, first, getOrThrow } from '../core/guard';
import { evalf } from '../numeric/evalf';
import { evalMp, fromMpc } from '../numeric/mpeval';
import { diff } from '../calculus/diff';
import { acos, asin, atan, cosh, sinh, tanh, log } from '../functions/elementary/elementary';
import { polyCoefficients, roots } from '../polys/poly';
import { Poly } from '../polys/sympoly';
import { linearEqToMatrix, solveAugmented } from '../matrices/linsys';
import { luSolve } from '../matrices/linalg';
import { Matrix } from '../matrices/matrix';
import { ExprMap } from '../core/exprmap';
import { generateBell } from '../utilities/iterables';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand, expandMul, expand_power_exp } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { radsimp } from '../simplify/radsimp';
import { simplify } from '../simplify/simplify';
import { asNumerDenom } from '../core/methods';

const isZeroE = (e: Expr): boolean => {
  if (e instanceof Rational) return e.isZero;
  const s = simplify(e);
  return s instanceof Rational && s.isZero;
};

/** lhs - rhs for an equation given as Eq(lhs, rhs) or an expression (= 0). */
export function asEquation(e: ExprLike): Expr {
  const x = sympify(e);
  if (x instanceof Rel && x.op === 'Eq') return add(x.lhs, mul(-1, x.rhs));
  return x;
}

/**
 * Check a candidate by exact substitution and simplification. A tiny numeric
 * residual is not accepted as zero. An undecidable symbolic residual is unknown.
 */
export function checksol(equation: ExprLike, assignments: ReadonlyMap<Expr, ExprLike>): Truth;
export function checksol(equation: ExprLike, symbol: Expr, value: ExprLike): Truth;
export function checksol(equation: ExprLike, assignments: ReadonlyMap<Expr, ExprLike> | Expr, value?: ExprLike): Truth {
  const reps: [Expr, Expr][] = assignments instanceof Expr
    ? [[assignments, sympify(defined(value, 'solution value'))]]
    : [...assignments].map(([k, v]) => [k, sympify(v)]);
  const residual = simplify(subs(asEquation(equation), reps));
  if (residual instanceof Rational) return residual.isZero;
  if (residual instanceof Special) return false;
  return ask(Q.zero(residual));
}

const sortExprs = (xs: Expr[]): Expr[] =>
  [...new Map(xs.map((x) => [x.key, x])).values()].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

/** Denominators of an expression (factors with negative exponents). */
function denominators(e: Expr): Expr[] {
  const out: Expr[] = [];
  const go = (x: Expr) => {
    if (x instanceof Pow && x.exp instanceof Rational && x.exp.isNegative) out.push(x.base);
    x.args.forEach(go);
  };
  go(e);
  return out;
}

/** Does the candidate solution satisfy the assumptions of x and keep denominators nonzero? */
function checkSolution(f: Expr, x: Sym, v: Expr): boolean {
  const a = x.assumptions;
  // Reject only a proven contradiction; symbolic candidates may remain undecidable.
  for (const name of ['positive', 'negative', 'nonnegative', 'nonpositive', 'real', 'integer', 'zero'] as const) {
    const expected = a[name];
    if (expected !== undefined && ask(Q[name](v)) === !expected) return false;
  }
  for (const d of denominators(f)) {
    const dv = xreplace(d, [[x, v]]);
    if (isZeroE(dv)) return false;
  }
  // the original expression must not be undefined there
  const fv = xreplace(f, [[x, v]]);
  if (fv instanceof Special) return false;
  // a numeric residual must vanish (SymPy checksol), e.g. sqrt(x) + 1 at x = 1
  if (freeSymbols(fv).size === 0 && !hasExtension(fv)) {
    try {
      // at a fixed working precision: the adaptive evalf of an exact zero raises the precision a long way
      const c = fromMpc(evalMp(fv, 200), 200).toComplex();
      if (Number.isFinite(c.re) && Number.isFinite(c.im) && Math.hypot(c.re, c.im) > 1e-12) return false;
    } catch {
      // not evaluable: keep the candidate
    }
  }
  return true;
}

const hasExtension = (e: Expr): boolean => e.kind === 'Extension' || e.args.some(hasExtension);

/** Inverse images of y under a function application f(u) (principal branches like SymPy). */
function invertFn(f: Fn | Pow, y: Expr, x: Sym): [Expr, Expr[]] | undefined {
  if (f instanceof Pow) {
    const [b, n] = f.args;
    if (b instanceof Constant && b.name === 'E') {
      // exp(-u) = y  ->  u = log(1/y), with 1/(-a - b) written as -1/(a + b) like SymPy
      if (couldExtractMinusSign(n)) {
        const iy = pow(y, -1);
        const inv = iy instanceof Pow && iy.base instanceof Add && couldExtractMinusSign(iy.base) ? mul(-1, pow(mul(-1, iy.base), -1)) : iy;
        return [mul(-1, n), [log(inv)]];
      }
      return [n, [log(y)]];
    }
    // b**n = y with n free of x  ->  b = y**(1/n) (SymPy solve(x**y - 2, x) = [2**(1/y)])
    if (!(n instanceof Rational)) return n.has(x) ? undefined : [b, [pow(y, pow(n, -1))]];
    if (n.isInteger) {
      // b**n = y: b is an n-th root of y (b = x itself was solved as a polynomial)
      // (the exponent is positive: f is a factor of a numerator)
      const t = new Dummy('t');
      return [b, roots(add(pow(t, n), mul(-1, y)), t)];
    }
    return [b, [pow(y, Rational.of(n.q, n.p))]];
  }
  // f has x, so it has an argument
  const u = first(f.args);
  switch (f.name) {
    case 'log':
      return [u, [exp(y)]];
    case 'sin':
      return [u, [asin(y), add(S.Pi, mul(-1, asin(y)))]];
    case 'cos':
      return [u, [acos(y), add(mul(2, S.Pi), mul(-1, acos(y)))]];
    case 'tan':
      return [u, [atan(y)]];
    case 'cosh': {
      const r = pow(add(pow(y, 2), -1), S.Half);
      return [u, [log(add(y, mul(-1, r))), log(add(y, r))]];
    }
    case 'sinh': {
      const r = pow(add(pow(y, 2), 1), S.Half);
      return [u, [log(add(y, mul(-1, r))), log(add(y, r))]];
    }
    case 'asinh': return [u, [sinh(y)]];
    case 'acosh': return [u, [cosh(y)]];
    case 'atanh': return [u, [tanh(y)]];
    default:
      return undefined;
  }
}

/** The recursion limit of solveRaw (each nested exp or log is one level). */
const MAX_DEPTH = 40;

/** Solutions of f = 0 for x (without the final check). */
/**
 * Terms sum_i c_i*log(g_i) + b with logarithms of x (c*x counts as c*log(exp(x))) and rational
 * c_i: [prod_i g_i**(L*c_i), L*b] with L the least common denominator of the c_i divided by the
 * gcd of the integers L*c_i.
 */
function logSum(terms: readonly Expr[], x: Sym): [Expr, Expr] | undefined {
  const logs: [Rational, Expr][] = [];
  for (const t of terms.filter((u) => u.has(x))) {
    const fs = t instanceof Mul ? t.args : [t];
    const c = fs.filter((g) => !g.has(x));
    const lf = fs.filter((g) => g.has(x));
    const coeff = mul(...c);
    const g = lf[0];
    if (lf.length !== 1 || !(coeff instanceof Rational)) return undefined;
    // c*x is c*log(exp(x))
    if (g?.key === x.key) logs.push([coeff, exp(x)]);
    else if (g instanceof Fn && g.name === 'log' && g.args.length === 1) logs.push([coeff, first(g.args)]);
    else return undefined;
  }
  const L = logs.reduce((m, [c]) => (m * c.q) / gcdBig(m, c.q), 1n);
  // the integer coefficients L*c_i divided by their gcd: 2*log(u) - 2*log(v) gives u/v, not (u/v)**2
  const G = logs.reduce((m, [c]) => gcdBig(m, ((c.p < 0n ? -c.p : c.p) * L) / c.q), 0n);
  const scale = Rational.of(L, G);
  return [mul(...logs.map(([c, g]) => pow(g, mul(c, scale)))), mul(scale, add(...terms.filter((u) => !u.has(x))))];
}

const gcdBig = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcdBig(b, a % b));

function solveRaw(f0: Expr, x: Sym, depth = 0): Expr[] {
  if (depth > MAX_DEPTH) throw new NotImplementedError('solve: recursion too deep');
  const f = mapBottomUp(f0, (e) => e instanceof Pow && e.base === S.E && e.exp instanceof Add && e.exp.has(x) ? expand_power_exp(e) : e);
  if (!f.has(x)) return [];
  // a single exponential term or 1/x: isolate it before clearing denominators
  if (f instanceof Add) {
    const dep = f.args.filter((t) => t.has(x));
    if (dep.length === 1) {
      const t = first(dep);
      const fs = t instanceof Mul ? t.args : [t];
      const F = fs.filter((g) => g.has(x));
      if (F.length === 1 && F[0] instanceof Pow && F[0].base.key === x.key && F[0].exp instanceof Rational && F[0].exp.p === -1n && F[0].exp.q === 1n) {
        // a/x + b = 0  ->  x = 1/(-b/a)
        const a = mul(...fs.filter((g) => !g.has(x)));
        const y = mul(-1, add(...f.args.filter((u) => !u.has(x))), pow(a, -1));
        return isZeroE(y) ? [] : [pow(y, -1)];
      }
      if (F.length === 1 && F[0] instanceof Pow && F[0].base instanceof Constant && F[0].base.name === 'E' && !isExpPower(F[0])) {
        const a = mul(...fs.filter((g) => !g.has(x)));
        const y = mul(-1, add(...f.args.filter((u) => !u.has(x))), pow(a, -1));
        const inv = defined(invertFn(F[0], y, x), 'inverse of exp');
        return inv[1].flatMap((yy) => solveRaw(add(inv[0], mul(-1, yy)), x, depth + 1));
      }
    }
  }
  // rational function: solve the numerator
  const [num] = fraction(together(f));
  const n = expandMul(num);
  const pc = polyCoefficients(n, x);
  if (pc) {
    const degree = Math.max(...pc.keys());
    const rational = [...pc.values()].every((c) => c instanceof Rational);
    if (noCubics && degree >= 3) {
      // SymPy cubics=False: CRootOf instead of the general formulas
      return rational ? uniqueKeys(Poly.from(n, [x]).allRoots()) : [];
    }
    let rs: Expr[];
    try {
      rs = roots(n, x);
    } catch (err) {
      if (!rational) throw err;
      rs = [];
    }
    if (rational && rs.length < degree) return uniqueKeys(Poly.from(n, [x]).allRoots());
    return rs;
  }
  // products: union of the factors
  if (num instanceof Mul) {
    const sols: Expr[] = [];
    for (const g of num.args) if (g.has(x)) sols.push(...solveRaw(g, x, depth + 1));
    return sols;
  }
  if (num instanceof Pow && num.exp instanceof Rational && num.exp.isPositive) return solveRaw(num.base, x, depth + 1);
  // isolate a single function application: a*F(u) + b = 0
  const terms = num instanceof Add ? num.args : [num];
  const dep = terms.filter((t) => t.has(x));
  if (dep.length === 1) {
    const b = add(...terms.filter((t) => !t.has(x)));
    const t = first(dep);
    const factors = t instanceof Mul ? t.args : [t];
    const fdep = factors.filter((g) => g.has(x));
    if (fdep.length === 1) {
      const a = mul(...factors.filter((g) => !g.has(x)));
      const F = first(fdep);
      const y = mul(-1, b, pow(a, -1));
      if (F instanceof Fn || (F instanceof Pow && !isExpPower(F))) {
        const inv = invertFn(F, y, x);
        if (inv) {
          const [u, ys] = inv;
          return ys.flatMap((yy) => solveRaw(add(u, mul(-1, yy)), x, depth + 1));
        }
      }
    }
  }
  const rad = singleRadical(num, x, depth);
  if (rad) return rad;
  const multi = radicalsOfX(num, x);
  if (multi) return multi;
  const lw = lambertSolve(num, x) ?? tsolveLambert(num, x, depth);
  if (lw) return lw;
  // a*sin(u) + b*cos(u) = 0  ->  tan(u) = -b/a
  const sc = sinCosLinear(num, x);
  if (sc) return sc;
  // sum_i c_i*log(g_i) + b = 0 with rational c_i: prod_i g_i**(L*c_i) = exp(-L*b) (SymPy logcombine with force)
  const lg = logSum(terms, x);
  if (lg) return solveRaw(expandMul(add(lg[0], mul(-1, exp(mul(-1, lg[1]))))), x, depth + 1);
  const gen = singleGenerator(num, x, depth);
  if (gen) return gen;
  throw new NotImplementedError(`solve: cannot solve ${f.toString()} for ${x.name}`);
}

/**
 * SymPy _solve for an equation that is a polynomial in a single generator
 * g(x) (a function application or an exponential, such as cos(x) or
 * tan(x/2)): the polynomial is solved for g, whose inverse images give the
 * solutions. The roots are written over a common denominator with the
 * exponentials expanded, like the rational functions of SymPy's polynomial
 * domains.
 */
function singleGenerator(num: Expr, x: Sym, depth: number): Expr[] | undefined {
  const pg = polynomialInGenerator(num, x);
  if (!pg) return undefined;
  const [g, rs] = pg;
  const t = new Dummy('t');
  // the generators are function applications and exponentials, which invertFn inverts or rejects
  const inv = invertFn(g, t, x);
  if (!inv) return undefined;
  return rs.flatMap((r) => {
    const ys = inv[1].map((yy) => xreplace(yy, [[t, r]]));
    // g(x) itself: the inverse images are the solutions (solving x - y again would expand them)
    return inv[0].key === x.key ? ys : ys.flatMap((yy) => solveRaw(add(inv[0], mul(-1, yy)), x, depth + 1));
  });
}

/**
 * An equation num = 0 that is a polynomial in a single generator g(x): g
 * and the roots of the polynomial (written over a common denominator with
 * the exponentials expanded), or undefined. @internal
 */
export function polynomialInGenerator(num: Expr, x: Sym): [Fn | Pow, Expr[]] | undefined {
  const e = expand(num);
  const gens = new Map<string, Fn | Pow>();
  let ok = true as boolean; // set inside a callback
  const isExpOfX = (u: Expr): u is Pow => u instanceof Pow && u.base instanceof Constant && u.base.name === 'E';
  const walk = (u: Expr) => {
    if (!u.has(x)) return;
    if (u instanceof Add || u instanceof Mul) u.args.forEach(walk);
    else if (u instanceof Pow && u.exp instanceof Rational && u.exp.isInteger) walk(u.base);
    else if (u instanceof Fn || isExpOfX(u)) gens.set(u.key, u);
    else ok = false;
  };
  walk(e);
  if (!ok) return undefined;
  const t = new Dummy('t');
  const reps = expGenerator([...gens.values()], t);
  if (!reps) return undefined;
  const [g, rep] = reps;
  // every occurrence of x is in a power of the generator: the numerator is a polynomial in t
  const [p] = fraction(together(xreplace(e, rep)));
  return [g, uniqueKeys(roots(expandMul(p), t).map((r) => cancel(expand(r))))];
}

/** The rational coefficient of the exponent of exp(c*u) (1 for an exponent without one). */
const expCoeff = (g: Pow): Rational => {
  const c = g.exp instanceof Mul ? first(g.exp.args) : undefined;
  return c instanceof Rational ? c : S.One;
};

/** exp(c*u) with an integer |numerator of c| > 1: a power of exp(u/q), solved as a polynomial (SymPy decompose_power). */
const isExpPower = (g: Pow): boolean => g.base instanceof Constant && g.base.name === 'E' && Math.abs(Number(expCoeff(g).p)) > 1;

/**
 * The generator of single-generator solving and the replacements by powers
 * of t: one function application, or exponentials exp(c_i*u) with rational
 * c_i, which are powers of exp(u/q) with q the lcm of the denominators of the
 * c_i (exp(2*x) and exp(x) are t**2 and t, like SymPy's polynomial generators).
 */
function expGenerator(gens: readonly (Fn | Pow)[], t: Dummy): [Fn | Pow, [Expr, Expr][]] | undefined {
  // x occurs in the equation, so there is a generator
  const g0 = first(gens);
  if (gens.length === 1 && !(g0 instanceof Pow)) return [g0, [[g0, t]]];
  const parts: [Expr, Rational, Expr][] = [];
  for (const g of gens) {
    if (!(g instanceof Pow)) return undefined;
    const c = expCoeff(g);
    parts.push([g, c, mul(g.exp, pow(c, -1))]);
  }
  const u = first(parts)[2];
  if (parts.some(([, , r]) => r.key !== u.key)) return undefined;
  const q = Rational.of(1n, parts.reduce((m, [, c]) => (m * c.q) / gcdBig(m, c.q), 1n));
  const g = cast(exp(mul(q, u)), Pow, 'exponential generator');
  return [g, parts.map(([e, c]) => [e, pow(t, mul(c, pow(q, -1)))])];
}

/**
 * One radical R = g**(p/q) in a*R + b = 0 (a, b free of radicals in x):
 * a**q*g**p = (-b)**q, a polynomial-type equation (SymPy unrad). Spurious
 * candidates are removed by the final check.
 */
function singleRadical(num: Expr, x: Sym, depth: number): Expr[] | undefined {
  const rads = new Map<string, [Pow, Rational]>();
  const find = (e: Expr) => {
    if (e instanceof Pow && e.exp instanceof Rational && !e.exp.isInteger && e.base.has(x)) rads.set(e.key, [e, e.exp]);
    e.args.forEach(find);
  };
  find(num);
  if (rads.size !== 1) return undefined;
  const [R, Rexp] = first([...rads.values()]);
  const terms = num instanceof Add ? num.args : [num];
  const as: Expr[] = [];
  const bs: Expr[] = [];
  for (const t of terms) {
    if (!t.has(R)) {
      bs.push(t);
      continue;
    }
    // R is the only radical in x, so c is free of radicals unless it still contains R
    const c = mul(t, pow(R, -1));
    if (c.has(R)) return undefined;
    as.push(c);
  }
  const a = add(...as);
  const b = add(...bs);
  const p = Rexp.p;
  const q = Rexp.q;
  // num is a numerator, so p > 0; beyond degree 6 (SymPy unrad's limit for the
  // polynomial in x) a linear radicand y = b*x + c is the variable instead
  if (q > 6n) {
    const pc = polyCoefficients(R.base, x);
    if (!pc) return undefined;
    if (Math.max(...pc.keys()) !== 1) {
      // otherwise the polynomial a**q*g**p - (-b)**q, whose roots (CRootOf among them) are
      // checked numerically against the principal branch
      const cands = solveRaw(expandMul(add(mul(pow(a, Rational.of(q)), pow(R.base, Rational.of(p))), mul(-1, pow(mul(-1, b), Rational.of(q))))), x, depth + 1);
      return cands.filter((c) => {
        const v = evalf(xreplace(num, [[x, c]]), 30).toComplex();
        return Math.hypot(v.re, v.im) < 1e-12;
      });
    }
    const b1 = getOrThrow(pc, 1);
    const c1 = pc.get(0) ?? S.Zero;
    const y = new Dummy('y');
    const inY = radicalsOfX(expandMul(xreplace(num, [[x, mul(add(y, mul(-1, c1)), pow(b1, -1))]])), y);
    return inY?.map((r) => mul(add(r, mul(-1, c1)), pow(b1, -1)));
  }
  const eq = add(mul(pow(a, Rational.of(q)), pow(R.base, Rational.of(p))), mul(-1, pow(mul(-1, b), Rational.of(q))));
  return solveRaw(expandMul(eq), x, depth + 1);
}

/**
 * Several radicals of x itself (x**(1/5), x**(1/3)): x = t**L with L the lcm
 * of the denominators gives a polynomial in t; the solutions are root**L for
 * the roots that satisfy the original equation (principal branches).
 */
function radicalsOfX(num: Expr, x: Sym): Expr[] | undefined {
  const dens = new Set<bigint>();
  let ok = true as boolean; // set inside a callback
  const walk = (e: Expr) => {
    if (e instanceof Pow && e.base.key === x.key && e.exp instanceof Rational) {
      if (e.exp.q > 1n) dens.add(e.exp.q);
      return;
    }
    if (e.key === x.key) return;
    if (e.has(x) && !(e instanceof Add || e instanceof Mul)) ok = false;
    e.args.forEach(walk);
  };
  walk(num);
  if (!ok || dens.size < 1) return undefined;
  const g = (a: bigint, b: bigint): bigint => (b === 0n ? a : g(b, a % b));
  const L = [...dens].reduce((l, q) => (l * q) / g(l, q), 1n);
  if (L > 60n) return undefined;
  const t = new Dummy('t');
  // whole powers of x are replaced first (top-down), then x itself
  const powers = new Map<string, Pow>();
  const collectPowers = (e: Expr) => {
    if (e instanceof Pow && e.base.key === x.key) powers.set(e.key, e);
    e.args.forEach(collectPowers);
  };
  collectPowers(num);
  const reps: [Expr, Expr][] = [...powers.values()].map((e) => [e, pow(t, mul(e.exp, Rational.of(L)))]);
  const sub = expandMul(xreplace(xreplace(num, reps), [[x, pow(t, Rational.of(L))]]));
  // the powers of x are nonnegative (num is a numerator), so sub is a polynomial in t
  defined(polyCoefficients(sub, t), 'polynomial in t');
  // a polynomial with rational coefficients in the original variable name (SymPy prints CRootOf in x)
  const [n] = fraction(together(sub));
  const P = Poly.from(expandMul(xreplace(n, [[t, x]])), [x]);
  const out: Expr[] = [];
  for (const r of uniqueKeys(P.allRoots())) {
    const cand = pow(r, Rational.of(L));
    const v = xreplace(num, [[x, cand]]);
    try {
      const c = evalf(v, 30).toComplex();
      if (Math.hypot(c.re, c.im) < 1e-12) out.push(cand);
    } catch {
      // not evaluable
    }
  }
  return out;
}

function sinCosLinear(e: Expr, x: Sym): Expr[] | undefined {
  const terms = e instanceof Add ? e.args : [e];
  let a: Expr = S.Zero;
  let b: Expr = S.Zero;
  let u: Expr | undefined;
  for (const t of terms) {
    const fs = t instanceof Mul ? t.args : [t];
    const trig = fs.filter((g): g is Fn => g instanceof Fn && (g.name === 'sin' || g.name === 'cos') && g.has(x));
    if (trig.length !== 1) return undefined;
    const g = first(trig);
    const arg = first(g.args);
    if (u && u.key !== arg.key) return undefined;
    u = arg;
    const c = mul(...fs.filter((h) => h !== g));
    if (c.has(x)) return undefined;
    if (g.name === 'sin') a = add(a, c);
    else b = add(b, c);
  }
  // a single sin or cos term, or terms with one function, were isolated before: both a and b are nonzero
  return solveRaw(add(defined(u, 'argument'), mul(-1, atan(mul(-1, b, pow(a, -1))))), x);
}

/**
 * Lambert W forms (a, b, c, d, e free of x):
 *   a*x + b + c*exp(d*x + e) = 0   ->  x = -W(c*d/a*exp(e - b*d/a))/d - b/a
 *   (a*x + b)*exp(d*x + e) + c = 0 ->  x = W(-c*d/a*exp(b*d/a - e))/d - b/a
 */
/** LambertW(arg, k) (the implementation is registered by functions/special). */
const lambertW = (arg: Expr, k?: number): Expr => defined(k === undefined ? impl.lambertW?.(arg) : impl.lambertW?.(arg, k), 'LambertW');

/**
 * The solutions sol(k) on the real branches of LambertW: k = 0, and k = -1
 * when the argument is a number in (-1/e, 0) (SymPy bivariate._lambert).
 */
function lambertBranches(arg: Expr, sol: (k?: number) => Expr): Expr[] {
  const out = [sol()];
  if (arg.freeSymbols().size === 0) {
    const v = arg.toComplex();
    if (Math.abs(v.im) < 1e-300 && v.re < 0 && v.re > -Math.exp(-1)) out.push(sol(-1));
  }
  return out;
}

function lambertSolve(num: Expr, x: Sym): Expr[] | undefined {
  const terms = num instanceof Add ? num.args : [num];
  const isExp = (g: Expr): g is Pow => g instanceof Pow && g.base instanceof Constant && g.base.name === 'E';
  let u: Expr | undefined;
  const withExp: Expr[] = [];
  const without: Expr[] = [];
  for (const t of terms) {
    const factors = t instanceof Mul ? t.args : [t];
    // exponentials in a product combine into one
    const ex = factors.filter((g): g is Pow => isExp(g) && g.has(x));
    if (ex.length === 0) {
      without.push(t);
      continue;
    }
    const ue = first(ex).exp;
    if (u && u.key !== ue.key) return undefined;
    u = ue;
    withExp.push(mul(...factors.filter((g) => g !== ex[0])));
  }
  if (!u) return undefined;
  const P = polyCoefficients(add(...withExp), x);
  const Q = polyCoefficients(add(...without), x);
  const U = polyCoefficients(u, x);
  if (!P || !Q || !U) return undefined;
  const deg = (m: Map<number, Expr>) => Math.max(-1, ...[...m.entries()].filter(([, v]) => !(v instanceof Rational && v.isZero)).map(([k]) => k));
  if (deg(U) !== 1) return undefined;
  const d = getOrThrow(U, 1);
  const e = U.get(0) ?? S.Zero;
  const W = lambertW;
  const branches = lambertBranches;
  if (deg(P) === 0 && deg(Q) === 1) {
    const c = getOrThrow(P, 0);
    const a = getOrThrow(Q, 1);
    const ba = mul(Q.get(0) ?? S.Zero, pow(a, -1));
    const arg = mul(c, d, pow(a, -1), exp(add(e, mul(-1, d, ba))));
    return branches(arg, (k) => add(mul(-1, W(arg, k), pow(d, -1)), mul(-1, ba)));
  }
  if (deg(P) === 1 && deg(Q) <= 0) {
    const a = getOrThrow(P, 1);
    const ba = mul(P.get(0) ?? S.Zero, pow(a, -1));
    // together() factors out an exp(u) common to all terms, so some term is free of it
    const c = getOrThrow(Q, 0);
    const arg = mul(-1, c, d, pow(a, -1), exp(add(mul(d, ba), mul(-1, e))));
    return branches(arg, (k) => add(mul(W(arg, k), pow(d, -1)), mul(-1, ba)));
  }
  return undefined;
}

/**
 * SymPy bivariate._lambert: a*log(b*x + c) + d*x + f = 0 (a..f free of x)
 * has the solutions x = -c/b + (a/d)*W(d/(a*b)*exp((c*d - b*f)/(a*b)), k).
 */
function lambertLogForm(eq: Expr, x: Sym): Expr[] | undefined {
  let L: Expr | undefined;
  const as: Expr[] = [];
  const others: Expr[] = [];
  for (const t of eq instanceof Add ? eq.args : [eq]) {
    const fs = t instanceof Mul ? t.args : [t];
    const logs = fs.filter((g) => g instanceof Fn && g.name === 'log' && g.has(x));
    if (logs.length === 0) {
      others.push(t);
      continue;
    }
    const lg = first(logs);
    const coeff = mul(...fs.filter((g) => g !== lg));
    if (logs.length > 1 || coeff.has(x) || (L && L.key !== first(lg.args).key)) return undefined;
    L = first(lg.args);
    as.push(coeff);
  }
  if (!L) return undefined;
  const lin = (e: Expr): [Expr, Expr] | undefined => {
    const pc = polyCoefficients(e, x);
    if (!pc || Math.max(...pc.keys()) > 1) return undefined;
    const c1 = pc.get(1) ?? S.Zero;
    return isZeroE(c1) ? undefined : [c1, pc.get(0) ?? S.Zero];
  };
  const bc = lin(L);
  const df = lin(add(...others));
  if (!bc || !df) return undefined;
  const [b, c] = bc;
  const [d, f] = df;
  const a = add(...as);
  const ab = mul(a, b);
  // exp(A) with A = num/(p*den) is taken as the p roots of t**p = exp(num/den) (SymPy)
  const [nm, dn] = asNumerDenom(mul(add(mul(c, d), mul(-1, b, f)), pow(ab, -1)));
  const p = dn instanceof Mul && first(dn.args) instanceof Rational ? first(dn.args) : dn instanceof Rational ? dn : S.One;
  const e = simplify(exp(mul(nm, pow(mul(dn, pow(p, -1)), -1))));
  const t = new Dummy('t');
  const ts = p.key === S.One.key ? [e] : roots(add(pow(t, p), mul(-1, e)), t);
  return ts.flatMap((tt) => {
    const arg = mul(d, pow(ab, -1), tt);
    return lambertBranches(arg, (k) => add(mul(-1, c, pow(b, -1)), mul(a, pow(d, -1), lambertW(arg, k))));
  });
}

/**
 * a*x*log(x) + d*x + f = 0 (a, d, f free of x): with X = log(x),
 * (a*X + d)*exp(X) = -f, so x = exp(W(-f/a*exp(d/a)) - d/a) (SymPy 1a2 form,
 * B*(b*log(B) + c)**a = R).
 */
function xLogForm(eq: Expr, x: Sym): Expr[] | undefined {
  const L = new Dummy('L');
  const e = expandMul(xreplace(eq, [[log(x), L]]));
  const pc = polyCoefficients(e, x);
  if (!pc || Math.max(...pc.keys()) !== 1) return undefined;
  const c1 = polyCoefficients(getOrThrow(pc, 1), L);
  const f = pc.get(0) ?? S.Zero;
  if (!c1 || Math.max(...c1.keys()) !== 1 || f.has(L)) return undefined;
  const a = getOrThrow(c1, 1);
  const d = c1.get(0) ?? S.Zero;
  const arg = mul(-1, f, pow(a, -1), exp(mul(d, pow(a, -1))));
  return lambertBranches(arg, (k) => exp(add(lambertW(arg, k), mul(-1, d, pow(a, -1)))));
}

/**
 * The Lambert forms SymPy reaches by taking logarithms (bivariate._solve_lambert)
 * of lhs = rhs (rhs free of x and nonzero):
 *   B**B = R                    ->  B = exp(W(log(R)))
 *   a product                   ->  the sum of the logarithms of the factors, x**(2*n) giving
 *                                   2*n*log(x) and 2*n*log(-x)
 *   g*p**u + R(x) = rhs         ->  log(g) + u*log(p) - log(rhs - R(x)) = 0
 * and a*log(b*x + c) + d*x + f = 0 itself.
 */
function tsolveLambert(num: Expr, x: Sym, depth: number): Expr[] | undefined {
  const direct = lambertLogForm(num, x) ?? xLogForm(num, x);
  if (direct) return direct;
  const terms = num instanceof Add ? num.args : [num];
  const rhs = mul(-1, add(...terms.filter((t) => !t.has(x))));
  const lhs = add(...terms.filter((t) => t.has(x)));
  if (isZeroE(rhs)) return undefined;
  // lhs = k*B**B
  const lfs = lhs instanceof Mul ? lhs.args : [lhs];
  const BB = lfs.filter((g) => g.has(x));
  const B0 = first(BB);
  if (BB.length === 1 && B0 instanceof Pow && B0.base.key === B0.exp.key) {
    const B = B0.base;
    const lr = log(mul(rhs, pow(mul(...lfs.filter((g) => !g.has(x))), -1)));
    return lambertBranches(lr, (k) => exp(lambertW(lr, k))).flatMap((v) => solveRaw(add(B, mul(-1, v)), x, depth + 1));
  }
  // the logarithm of a power factor: an exponent free of x times the log of the base, or the exponent times log(p)
  const t = new Dummy('t');
  let evenBase: Expr | undefined;
  const logPow = (g: Expr): Expr => {
    if (g instanceof Pow) {
      const [bs, ex] = g.args;
      if (bs instanceof Constant && bs.name === 'E') return ex;
      if (!bs.has(x)) return mul(ex, log(bs));
      if (!ex.has(x)) {
        // an even power of B: log(B) and log(-B) (one such base is marked with t)
        const even = ex instanceof Rational && ex.isInteger && ex.p % 2n === 0n && (!evenBase || evenBase.key === bs.key);
        if (even) evenBase = bs;
        return mul(ex, log(even ? t : bs));
      }
      return mul(ex, log(bs));
    }
    return log(g);
  };
  const fromLog = (eq: Expr): Expr[] | undefined => {
    const sols: Expr[] = [];
    const B = evenBase ?? x;
    for (const sgn of eq.has(t) ? [-1, 1] : [1]) {
      const e1 = expandMul(xreplace(eq, [[t, mul(sgn, B)]]));
      const r = lambertLogForm(e1, x) ?? xLogForm(e1, x);
      if (!r) return undefined;
      sols.push(...r);
    }
    return sols;
  };
  if (lhs instanceof Mul) return fromLog(add(...lhs.args.map(logPow), mul(-1, log(rhs))));
  if (lhs instanceof Add) {
    const isPowX = (g: Expr) => g instanceof Pow && !g.base.has(x) && g.exp.has(x);
    const exps = lhs.args.filter((u) => (u instanceof Mul ? u.args : [u]).some(isPowX));
    if (exps.length !== 1) return undefined;
    const E = first(exps);
    const rest = add(...lhs.args.filter((u) => u !== E));
    const fs = E instanceof Mul ? E.args : [E];
    return fromLog(add(...fs.map(logPow), mul(-1, log(add(rhs, mul(-1, rest))))));
  }
  return undefined;
}

/**
 * Solutions of the equation e = 0 (or Eq(lhs, rhs)) for x, sorted like
 * SymPy. Solutions violating the assumptions on x or making a denominator
 * vanish are removed unless check is false.
 */
let noCubics = false;
const uniqueKeys = (xs: Expr[]): Expr[] => [...new Map(xs.map((r) => [r.key, r])).values()];

export function solve(e: ExprLike, x?: Sym | Expr, opts: { check?: boolean; cubics?: boolean } = {}): Expr[] {
  if (opts.cubics === false && !noCubics) {
    noCubics = true;
    try {
      return solve(e, x, { ...opts, cubics: undefined });
    } finally {
      noCubics = false;
    }
  }
  if (x !== undefined && !(x instanceof Sym)) {
    // solve for an expression such as f(x), Derivative(f(x), x) or x + 2: treat it as a symbol
    const t = new Dummy('t');
    const target = x;
    const g = replaceTarget(asEquation(e), target, t);
    if (!g.has(t)) return [];
    return solve(g, t, opts).map((r) => xreplaceS(r, [[t, target]]));
  }
  const f = asEquation(e);
  const syms = [...freeSymbols(f)];
  const v = x ?? (syms.length === 1 ? syms[0] : undefined);
  if (v === undefined) {
    if (syms.length === 0) return [];
    throw new TypeError('solve: specify the symbol to solve for');
  }
  const raw0 = solveRaw(f, v);
  // SymPy: high-order root lists (more than two roots) are not simplified
  const raw = raw0.length > 2 ? raw0 : raw0.map((r) => simplifySolution(r));
  const checked = opts.check === false || raw.some((r) => r.kind === 'Extension') ? raw : raw.filter((r) => checkSolution(f, v, r));
  // indexed roots (CRootOf) keep their order
  return raw.some((r) => r.kind === 'Extension') ? checked : sortExprs(checked);
}

/** Replace free occurrences of target (not inside derivatives); a sum target may match part of a sum. */
function replaceTarget(e: Expr, target: Expr, t: Expr): Expr {
  const go = (x: Expr): Expr => {
    if (x.key === target.key) return t;
    if (x.kind === 'Derivative') return x;
    // a sum target matches the terms of a sum up to the numeric term (SymPy Add._eval_subs: (x - 1).subs(x + 1, t) = t - 2)
    if (target instanceof Add && x instanceof Add) {
      const tTerms = target.args.filter((a) => !(a instanceof Rational));
      const tNum = add(...target.args.filter((a) => a instanceof Rational));
      if (tTerms.every((a) => x.args.some((b) => b.key === a.key))) {
        const rest = x.args.filter((b) => !tTerms.some((a) => a.key === b.key));
        return add(t, mul(-1, tNum), ...rest.map(go));
      }
    }
    if (x.args.length === 0) return x;
    const args = x.args.map(go);
    return args.every((a, i) => a === x.args[i]) ? x : xreplaceS(x, x.args.map((a, i): [Expr, Expr] => [a, at(args, i)]).filter(([a, b]) => a !== b));
  };
  return go(e);
}

function simplifySolution(r: Expr): Expr {
  if (r.freeSymbols().size === 0 && !(r instanceof Rational)) {
    const s = simplify(r);
    return s;
  }
  return r;
}

// ---------------------------------------------------------------------------
// systems
// ---------------------------------------------------------------------------

export { linearEqToMatrix, linsolve, solveAugmented } from '../matrices/linsys';

/**
 * Solve a polynomial system by successive elimination: equations that are
 * univariate (after substitution) are solved and their solutions substituted.
 * Returns the list of solution tuples.
 */
export function nonlinsolve(eqs: readonly ExprLike[], syms: readonly Sym[]): Expr[][] {
  const lin = linearEqToMatrix(eqs, syms);
  if (lin) {
    const s = solveAugmented(lin[0].hstack(lin[1]), syms);
    return s ? [s] : [];
  }
  const results: Expr[][] = [];
  const go = (system: Expr[], assigned: Map<string, Expr>) => {
    const pending = system.map((e) => expandMul(e)).filter((e) => !isZeroE(e));
    const unknowns = syms.filter((s) => !assigned.has(s.key));
    if (pending.length === 0) {
      // remaining unknowns are free parameters
      results.push(syms.map((s) => assigned.get(s.key) ?? s));
      return;
    }
    if (unknowns.length === 0) return;
    if (pending.some((e) => freeSymbols(e).size === 0 || !unknowns.some((u) => e.has(u)))) return;
    // prefer an equation that is linear in some unknown with a nonzero constant coefficient
    for (const e of pending) {
      for (const u of unknowns) {
        const pc = polyCoefficients(numerOf(e), u);
        if (pc && Math.max(...pc.keys()) === 1) {
          const c1 = getOrThrow(pc, 1);
          const c0 = pc.get(0) ?? S.Zero;
          // c0 and c1 are free of u, and so is the value; the solutions where a coefficient c1 in the
          // other unknowns vanishes are those of c1 = c0 = 0
          if (unknowns.some((w) => c1.has(w))) go([c1, c0, ...pending.filter((p) => p !== e)], assigned);
          const val = cancel(mul(-1, c0, pow(c1, -1)));
          const next = new Map(assigned);
          for (const [k, w] of next) next.set(k, cancel(xreplace(w, [[u, val]])));
          next.set(u.key, val);
          go(
            pending.filter((p) => p !== e).map((p) => xreplace(p, [[u, val]])),
            next,
          );
          return;
        }
      }
    }
    // a univariate equation
    for (const e of pending) {
      const vars = unknowns.filter((u) => e.has(u));
      if (vars.length !== 1) continue;
      const u = first(vars);
      let sols: Expr[];
      try {
        sols = solve(e, u, { check: false }).filter((v) =>
          denominators(e).every((dd) => !isZeroE(xreplace(dd, [[u, v]]))),
        );
      } catch {
        continue;
      }
      for (const s of sols) {
        const next = new Map(assigned);
        for (const [k, w] of next) next.set(k, simplifyBack(xreplace(w, [[u, s]])));
        // Substitute into previously assigned coordinates only. An indexed root
        // binds the generator of its defining polynomial; substituting into the
        // root itself would corrupt that polynomial.
        next.set(u.key, s);
        go(
          pending.filter((p) => p !== e).map((p) => xreplace(p, [[u, s]])),
          next,
        );
      }
      return;
    }
    // a polynomial system: Groebner basis and back substitution
    const numers = pending.map(numerOf);
    if (numers.every((e) => unknowns.every((u) => polyCoefficients(e, u) !== undefined))) {
      for (const sol of solvePolySystem(numers, unknowns)) {
        const next = new Map(assigned);
        for (const [k, w] of next) next.set(k, simplifyBack(xreplace(w, unknowns.map((u, i): [Expr, Expr] => [u, at(sol, i)]))));
        unknowns.forEach((u, i) => next.set(u.key, at(sol, i)));
        // every unknown is assigned now
        results.push(syms.map((s) => getOrThrow(next, s.key)));
      }
      return;
    }
    throw new NotImplementedError('nonlinsolve: unsupported system');
  };
  const original = eqs.map(asEquation);
  // equations with one radical are squared away (SymPy unrad); spurious solutions are removed below
  const prepared = original.map((e) => unradOnce(e, syms) ?? e);
  go(prepared, new Map());
  // the branches of a vanishing coefficient may meet the others: a solution that is a special case of a family of
  // solutions is dropped
  const unique = [...new Map(results.map((r) => [r.map((x) => x.key).join(','), r])).values()];
  results.splice(0, results.length, ...unique.filter((r) => !unique.some((g) => g !== r && specializes(r, g, syms))));
  if (prepared.every((e, i) => e === original[i])) return results;
  return results.filter((sol) =>
    original.every((e) => {
      const r = xreplace(e, syms.map((s, i): [Expr, Expr] => [s, at(sol, i)]));
      if (freeSymbols(r).size) return true;
      try {
        const c = evalf(r, 30).toComplex();
        return !(Math.hypot(c.re, c.im) > 1e-12);
      } catch {
        return true;
      }
    }),
  );
}

/**
 * The solution r is the family g with values given to its free unknowns
 * (the unknowns that are their own value in g).
 */
function specializes(r: readonly Expr[], g: readonly Expr[], syms: readonly Sym[]): boolean {
  const free = syms.filter((s, i) => at(g, i).key === s.key);
  if (free.length === 0) return false;
  const values = free.map((s): [Expr, Expr] => [s, at(r, syms.indexOf(s))]);
  return g.every((v, i) => xreplace(v, values).key === at(r, i).key);
}

/** a*R + b = 0 with one radical R = g**(p/q) in the unknowns: a**q*g**p - (-b)**q. */
function unradOnce(num: Expr, syms: readonly Sym[]): Expr | undefined {
  const hasVar = (e: Expr) => syms.some((s) => e.has(s));
  const rads = new Map<string, [Pow, Rational]>();
  const find = (e: Expr) => {
    if (e instanceof Pow && e.exp instanceof Rational && !e.exp.isInteger && hasVar(e.base)) rads.set(e.key, [e, e.exp]);
    e.args.forEach(find);
  };
  find(num);
  if (rads.size !== 1) return undefined;
  const [R, Rexp] = first([...rads.values()]);
  const terms = num instanceof Add ? num.args : [num];
  const as: Expr[] = [];
  const bs: Expr[] = [];
  for (const t of terms) {
    if (!t.has(R)) {
      bs.push(t);
      continue;
    }
    const c = mul(t, pow(R, -1));
    if (c.has(R)) return undefined;
    as.push(c);
  }
  const p = Rexp.p;
  const q = Rexp.q;
  if (p < 0n || q > 6n) return undefined;
  return expandMul(add(mul(pow(add(...as), Rational.of(q)), pow(R.base, Rational.of(p))), mul(-1, pow(mul(-1, add(...bs)), Rational.of(q)))));
}

const numerOf = (e: Expr): Expr => expandMul(fraction(together(e))[0]);
const simplifyBack = (e: Expr): Expr => {
  const c = cancel(e);
  if (c.freeSymbols().size > 0) return c;
  // a number: radsimp keeps it free of symbols
  return simplify(expandMul(radsimp(c)));
};

/** SymPy solve_linear: (symbol, value) for an equation linear in one symbol, else (numer, denom). */
export function solveLinear(e: ExprLike, opts: { symbols?: Sym[]; exclude?: Sym[] } = {}): [Expr, Expr] {
  // port of SymPy solve_linear
  const eq = asEquation(e);
  const [n, d] = asNumerDenom(eq);
  if (isZeroE(n)) return [S.Zero, S.One];
  let symbols = [...freeSymbols(n)];
  const { symbols: only, exclude } = opts;
  if (only) symbols = symbols.filter((s) => only.some((t) => t.key === s.key));
  if (exclude) symbols = symbols.filter((s) => !exclude.some((t) => t.key === s.key));
  if (!symbols.length) return [S.Zero, S.One];
  symbols.sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
  // denominators of eq that depend on the symbols (SymPy _simple_dens)
  const dens: Expr[] = [];
  const visit = (t: Expr) => {
    t.args.forEach(visit);
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative && symbols.some((s) => t.base.has(s))) dens.push(t.base);
  };
  visit(eq);
  const symKeys = new Set(symbols.map((s) => s.key));
  let allZero = true;
  for (const xi of symbols) {
    const dn = diff(n, xi);
    if (isZeroE(dn)) continue;
    const free = [...freeSymbols(dn)];
    const ok = !free.length || free.some((s) => !isZeroE(diff(dn, s))) || (free.length === symKeys.size && free.every((s) => symKeys.has(s.key)));
    if (!ok) continue;
    allZero = false;
    if (dn.has(xi)) continue;
    const vi = mul(-1, pow(dn, -1), xreplace(n, [[xi, S.Zero]]));
    const bad = dens.some((di) => {
      const v = xreplace(di, [[xi, vi]]);
      return isZeroE(v) || isZeroE(cancel(v));
    });
    if (!bad) return [xi, expandMul(vi)];
  }
  if (allZero) return [S.Zero, S.One];
  if (n instanceof Sym) return [S.Zero, S.Zero];
  return [n, d];
}

/** Solve for the undetermined coefficients so that eq vanishes identically in the given symbols. */
export function solveUndeterminedCoeffs(e: ExprLike, coeffs: readonly Sym[], syms: readonly Sym[]): Expr[][] {
  const f = expandMul(numerOf(asEquation(e)));
  // collect coefficients of each monomial in syms
  const eqs: Expr[] = [];
  const collect = (expr: Expr, vars: readonly Sym[]) => {
    if (vars.length === 0) {
      eqs.push(expr);
      return;
    }
    // expr is a sum of monomials in the symbols (checked below), so its coefficients are polynomials in the rest
    const pc = defined(polyCoefficients(expr, first(vars)), 'coefficients');
    for (const c of pc.values()) collect(c, vars.slice(1));
  };
  if (syms.every((v) => polyCoefficients(f, v) !== undefined)) collect(f, syms);
  else {
    // other functions of the symbols (x**y, exp(x), ...): group the terms by their part depending on the symbols
    const groups = new Map<string, Expr[]>();
    for (const t of f instanceof Add ? f.args : [f]) {
      const fs = t instanceof Mul ? t.args : [t];
      const dep = mul(...fs.filter((g) => syms.some((v) => g.has(v))));
      const c = mul(...fs.filter((g) => !syms.some((v) => g.has(v))));
      groups.set(dep.key, [...(groups.get(dep.key) ?? []), c]);
    }
    for (const cs of groups.values()) eqs.push(add(...cs));
  }
  return nonlinsolve(eqs, coeffs);
}

const isBracket = (v: ExprLike | readonly [ExprLike, ExprLike]): v is readonly [ExprLike, ExprLike] => Array.isArray(v);

/** Numeric root of f near x0 by Newton's method (complex arithmetic). */
export function nsolve(e: ExprLike, x: Sym, x0: ExprLike | readonly [ExprLike, ExprLike], opts: { prec?: number; solver?: 'newton' | 'bisect' } = {}): Expr {
  // a bracket is narrowed by bisection in double precision, then refined like a starting point
  const r = isBracket(x0) ? nsolveBisect(e, x, x0) : nsolveDouble(e, x, x0);
  // refine with Newton steps in arbitrary precision so that the result is the
  // correctly rounded root (SymPy's mpmath findroot; nsolve(..., prec=n))
  const dps = opts.prec ?? 15;
  const f = asEquation(e);
  const df = diff(f, x);
  const wp = dps + 10;
  // the functions evaluated in double precision above evaluate in any precision
  let z = impl.evalf(r, wp);
  let last = '';
  for (let i = 0; i < 60; i++) {
    const fv = impl.evalf(xreplace(f, [[x, z]]), wp);
    // an exact root (a zero derivative there would give 0/0)
    if (fv.toComplex().re === 0 && fv.toComplex().im === 0) break;
    const dv = impl.evalf(xreplace(df, [[x, z]]), wp);
    z = impl.evalf(add(z, mul(-1, fv, pow(dv, -1))), wp);
    const cur = impl.evalf(z, dps).toString();
    if (cur === last) break;
    last = cur;
  }
  return impl.evalf(z, dps);
}

/** A real root in [a, b] by bisection (SymPy nsolve(f, (a, b), solver='bisect')). */
function nsolveBisect(e: ExprLike, x: Sym, [a0, b0]: readonly [ExprLike, ExprLike]): Expr {
  const f = asEquation(e);
  const val = (t: number) => xreplace(f, [[x, new Float(t)]]).toComplex().re;
  let a = sympify(a0).toNumber();
  let b = sympify(b0).toNumber();
  let fa = val(a);
  if (Math.sign(fa) === Math.sign(val(b))) throw new RangeError('nsolve: no sign change in the interval');
  for (let i = 0; i < 200 && b - a > 0; i++) {
    const m = (a + b) / 2;
    if (m === a || m === b) break;
    const fm = val(m);
    if (fm === 0) return new Float(m);
    if (Math.sign(fm) === Math.sign(fa)) [a, fa] = [m, fm];
    else b = m;
  }
  return new Float((a + b) / 2);
}

function nsolveDouble(e: ExprLike, x: Sym, x0: ExprLike): Expr {
  const f = asEquation(e);
  const df = diff(f, x);
  const z0 = sympify(x0).toComplex();
  let z = z0;
  for (let i = 0; i < 100; i++) {
    const fv = xreplace(f, [[x, cplx(z)]]).toComplex();
    const dv = xreplace(df, [[x, cplx(z)]]).toComplex();
    const den = dv.re * dv.re + dv.im * dv.im;
    if (den === 0) break;
    const step = { re: (fv.re * dv.re + fv.im * dv.im) / den, im: (fv.im * dv.re - fv.re * dv.im) / den };
    z = { re: z.re - step.re, im: z.im - step.im };
    if (Math.hypot(step.re, step.im) < 1e-15 * Math.max(1, Math.hypot(z.re, z.im))) break;
  }
  return impl.evalf(cplx(z));
}

const cplx = (z: { re: number; im: number }): Expr =>
  z.im === 0 ? sympify(z.re) : add(sympify(z.re), mul(sympify(z.im), S.I));


/**
 * SymPy solvers._invert: reduce eq = 0 to lhs = rhs with lhs containing the
 * symbols in its simplest form. Returns [rhs, lhs].
 */
export function invertEquation(eqIn: ExprLike, symbols: readonly Sym[] = [], opts: { integerPower?: boolean } = {}): [Expr, Expr] {
  const eq = sympify(eqIn);
  const syms = symbols.length ? [...symbols] : [...freeSymbols(eq)];
  if (!syms.some((s) => eq.has(s))) return [eq, S.Zero];
  const dep = (e: Expr) => syms.some((s) => e.has(s));
  let lhs = eq;
  let rhs: Expr = S.Zero;
  for (let guard = 0; guard < 50; guard++) {
    const was = lhs;
    for (let g2 = 0; g2 < 50; g2++) {
      if (lhs instanceof Add) {
        const indep = add(...lhs.args.filter((a) => !dep(a)));
        if (indep instanceof Rational && indep.isZero) break;
        lhs = add(...lhs.args.filter(dep));
        rhs = add(rhs, mul(-1, indep));
      } else if (lhs instanceof Mul) {
        const indep = mul(...lhs.args.filter((a) => !dep(a)));
        if (indep instanceof Rational && indep.isOne) break;
        lhs = mul(...lhs.args.filter(dep));
        rhs = mul(rhs, pow(indep, -1));
      } else break;
    }
    if (lhs instanceof Fn && lhs.name === 'log' && lhs.args.length === 1) {
      rhs = exp(rhs);
      lhs = first(lhs.args);
    } else if (lhs instanceof Pow && lhs.base instanceof Constant && lhs.base.name === 'E') {
      rhs = log(rhs);
      lhs = lhs.exp;
    }
    if (!(rhs instanceof Rational && rhs.isZero) && lhs instanceof Pow && lhs.exp instanceof Rational && lhs.exp.isInteger && lhs.exp.isNegative) {
      lhs = pow(lhs, -1);
      rhs = pow(rhs, -1);
    }
    if (lhs instanceof Pow && !(lhs.base instanceof Constant)) {
      const intExp = lhs.exp instanceof Rational && lhs.exp.isInteger;
      const base = lhs.base;
      const multi = syms.length > 1 && syms.filter((s) => base.has(s)).length > 1;
      if ((intExp && opts.integerPower) || (!intExp && multi)) {
        rhs = pow(rhs, pow(lhs.exp, -1));
        lhs = lhs.base;
      }
    }
    if (lhs.key === was.key) break;
  }
  return [rhs, lhs];
}

// ---------------------------------------------------------------------------
// Determinants, inverses and LU solutions of small symbolic matrices (SymPy solvers.py)
// ---------------------------------------------------------------------------

/**
 * SymPy det_perm: the determinant as the sum over the permutations (in the
 * adjacent-transposition order of generate_bell, so the signs alternate).
 */
function detPerm(M: Matrix): Expr {
  const n = M.rows;
  if (n === 0) return S.One;
  const flat = M.flat();
  const terms: Expr[] = [];
  let s = true;
  for (const perm of generateBell(n)) {
    const term = mul(...perm.map((j, i) => at(flat, i * n + j)));
    terms.push(s ? term : mul(-1, term));
    s = !s;
  }
  return add(...terms);
}

/**
 * SymPy det_minor: Laplace expansion along the first row, each product
 * distributed over the terms of the minor's determinant. (SymPy's version
 * gives 0 for a 1 x 1 matrix; here it is the entry.)
 */
function detMinor(M: Matrix): Expr {
  const n = M.rows;
  if (n === 1) return M.get(0, 0);
  if (n === 2) return add(mul(M.get(0, 0), M.get(1, 1)), mul(-1, M.get(1, 0), M.get(0, 1)));
  const terms: Expr[] = [];
  for (let i = 0; i < n; i++) {
    const m = M.get(0, i);
    if (m instanceof Rational && m.isZero) continue;
    const d = detMinor(M.minorSubmatrix(0, i));
    terms.push(mul(i % 2 ? -1 : 1, add(...(d instanceof Add ? d.args : [d]).map((t) => mul(m, t)))));
  }
  return add(...terms);
}

const hasSymbol = (e: Expr): boolean => freeSymbols(e).size > 0;

/**
 * SymPy det_quick(M, method=None): the determinant of a matrix with
 * symbolic entries by permutations (fewer than 8 rows, every entry symbolic)
 * or by minors; a numeric matrix uses det.
 */
export function detQuick(M: Matrix): Expr {
  const entries = M.flat();
  if (entries.some(hasSymbol)) return M.rows < 8 && entries.every(hasSymbol) ? detPerm(M) : detMinor(M);
  return M.det();
}

/**
 * SymPy inv_quick(M): the inverse as cofactors over the determinant (by
 * permutations when no entry is a number, else by minors); a numeric matrix
 * uses inv. SymPy's minors of a 2 x 2 matrix are 0 (its det_minor of a 1 x 1
 * matrix), so it returns the zero matrix for Matrix([[x, 1], [0, x]]); symjs
 * returns the inverse.
 */
export function invQuick(M: Matrix): Matrix {
  const entries = M.flat();
  if (entries.every((e) => isNum(e))) return M.inv();
  const det = entries.some((e) => isNum(e)) ? detMinor : detPerm;
  const n = M.rows;
  const d = det(M);
  if (d instanceof Rational && d.isZero) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible');
  // entry (j, i) is the cofactor of (i, j) over the determinant
  return Matrix.fromFunction(n, n, (j, i) => mul((i + j) % 2 ? -1 : 1, det(M.minorSubmatrix(i, j)), pow(d, -1)));
}

/**
 * SymPy solve_linear_system_LU(matrix, syms): the solution of the system
 * with augmented matrix `matrix` (n rows, n + 1 columns) by LU
 * decomposition, as a map from the symbols to their values.
 */
export function solveLinearSystemLU(matrix: Matrix, syms: readonly Expr[]): ExprMap<Expr> {
  if (matrix.rows !== matrix.cols - 1) throw new RangeError('Rows should be equal to columns - 1');
  const idx = Array.from({ length: matrix.rows }, (_, i) => i);
  const soln = luSolve(matrix.extract(idx, idx), matrix.extract(idx, [matrix.cols - 1]));
  return new ExprMap(idx.map((i): [Expr, Expr] => [at(syms, i), soln.get(i, 0)]));
}
