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
import { Expr, Add, BoolAtom, Constant, Dummy, Float, Fn, Integral, Mul, Piecewise, Pow, Rational, Rel, S, Special, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp, piecewiseFold, rebuild, some, subs, xreplace, xreplace as xreplaceS } from '../core/traverse';
import { and, not, or } from '../core/boolalg';
import { Lt, Ne, piecewise } from '../core/logic';
import type { Truth } from '../core/truth';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { at, cast, defined, first, getOrThrow } from '../core/guard';
import { evalf } from '../numeric/evalf';
import { evalMp, fromMpc } from '../numeric/mpeval';
import { cmp as compareMpf, fromNumber } from '../numeric/mpf';
import { cabs } from '../numeric/mpfun';
import { rationalFromString } from '../core/numberutils';
import { diff } from '../calculus/diff';
import { Concrete } from '../core/concrete';
import { acos, asin, atan, cosh, sinh, tanh, tan, sin, cos, fn, log } from '../functions/elementary/elementary';
import { polyCoefficients, roots } from '../polys/poly';
import '../polys/polyroots';
import { factor, Poly } from '../polys/sympoly';
import { groebner } from '../polys/groebner';
import { CRootOf } from '../polys/rootof';
import { _linsolve } from '../polys/matrices/linsolve';
import { linearEqToMatrix, solveAugmented } from '../matrices/linsys';
import { luSolve } from '../matrices/linalg';
import { Matrix } from '../matrices/matrix';
import { ExprMap } from '../core/exprmap';
import { ordered } from '../core/match';
import { generateBell } from '../utilities/iterables';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expand, expandMul, expand_power_exp, withFactoredDenominators } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { radsimp } from '../simplify/radsimp';
import { simplify } from '../simplify/simplify';
import { factorTerms } from '../simplify/exprtools';
import { asNumerDenom, asRealImag, isConstantTruth, isPolynomial } from '../core/methods';
import { expandFunc } from '../functions/special/special';
import { perfectPower } from '../ntheory/factor';
import { powdenest } from '../simplify/powsimp';

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
 * Check candidates by substitution and simplification, combining equation lists
 * with three-valued conjunction. Exact residuals stay exact; floating residuals
 * use the numeric tolerance of SymPy checksol.
 */
export function checksol(equation: ExprLike | readonly ExprLike[], assignments: ReadonlyMap<Expr, ExprLike>, opts?: { numerical?: boolean }): Truth;
export function checksol(equation: ExprLike | readonly ExprLike[], symbol: Expr, value: ExprLike, opts?: { numerical?: boolean }): Truth;
export function checksol(equation: ExprLike | readonly ExprLike[], assignments: ReadonlyMap<Expr, ExprLike> | Expr, value?: ExprLike | { numerical?: boolean }, opts: { numerical?: boolean } = {}): Truth {
  const options = typeof value === 'object' && !(value instanceof Expr) ? value : opts;
  const reps: [Expr, Expr][] = assignments instanceof Expr
    ? [[assignments, sympify(defined(typeof value === 'object' && !(value instanceof Expr) ? undefined : value, 'solution value'))]]
    : [...assignments].map(([k, v]) => [k, sympify(v)]);
  const sequence = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);
  if (sequence(equation)) {
    if (!equation.length) throw new RangeError('checksol: no equations to check');
    let result: Truth = true;
    for (const e of equation) {
      const checked = checksol(e, new Map(reps), options);
      if (checked === false) return false;
      if (checked === 'unknown') result = 'unknown';
    }
    return result;
  }
  const input = sympify(equation);
  if (input instanceof Rational || input instanceof Float) return input instanceof Rational ? input.isZero : input.toNumber() === 0;
  if (input instanceof BoolAtom) return input.value;
  if (input instanceof Rel && (input.op !== 'Eq' || input.lhs instanceof BoolAtom || input.rhs instanceof BoolAtom)) {
    const lhs = subs(input.lhs, reps), rhs = subs(input.rhs, reps);
    if (lhs instanceof BoolAtom && rhs instanceof BoolAtom) return input.op === 'Ne' ? lhs.value !== rhs.value : lhs.value === rhs.value;
    const checked = subs(input, reps);
    return checked instanceof BoolAtom ? checked.value : 'unknown';
  }
  const residual = simplify(subs(asEquation(input), reps));
  if (residual instanceof Rational) return residual.isZero;
  if (residual instanceof Float) return options.numerical === false ? residual.toNumber() === 0 : Math.abs(residual.toNumber()) < 1e-9;
  if (residual instanceof Special) return false;
  const zero = ask(Q.zero(residual));
  if (zero !== 'unknown') return zero;
  if (residual instanceof Sym) return false;
  const assignedSymbols = reps.map(([key]) => key).filter((key): key is Sym => key instanceof Sym);
  if (assignedSymbols.length && isConstantTruth(residual, assignedSymbols) === false) return false;
  if (residual instanceof Concrete) {
    const evaluated = expandMul(impl.doit?.(residual) ?? residual);
    if (!evaluated.equals(residual) && isPolynomial(evaluated)) return evaluated.equals(S.Zero);
  }
  if (options.numerical !== false && !freeSymbols(residual).size) {
    try {
      return compareMpf(cabs(evalMp(residual, 200), 200), fromNumber(1e-9)) < 0;
    } catch {
      return 'unknown';
    }
  }
  return 'unknown';
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

/** A positive sum or product can be certified term by term. */
function positiveExpression(e: Expr): boolean {
  if (ask(Q.positive(e)) === true) return true;
  if (e instanceof Add) {
    const positive = e.args.map(positiveExpression);
    return positive.some(Boolean) && e.args.every((a, i) => positive[i] === true || ask(Q.nonnegative(a)) === true);
  }
  if (e instanceof Mul) return e.args.every(positiveExpression);
  return e instanceof Pow && positiveExpression(e.base) && ask(Q.real(e.exp)) === true;
}

/** SymPy denoms: unique denominator bases, optionally restricted to symbols. */
export function denoms(expr: ExprLike, ...symbols: Sym[]): Set<Expr> {
  const found = new Map<string, Expr>();
  const visit = (e: Expr): void => {
    const d = asNumerDenom(e)[1];
    const factors = d instanceof Mul ? d.args : [d];
    for (const f of factors) {
      const base = f instanceof Pow ? f.base : f;
      if (!base.equals(S.One) && (!symbols.length || symbols.some((s) => base.has(s)))) found.set(base.key, base);
    }
    e.args.forEach(visit);
  };
  visit(sympify(expr));
  return new Set(found.values());
}

/**
 * Remove rational powers from an equation. The resulting equation can have
 * extraneous roots: candidates must be checked in the original expression.
 * Common-base radicals use a new variable and return its defining equation.
 */
export function unrad(expr: ExprLike, ...symbols: Sym[]): [Expr, Expr[]] | NoMatchResult {
  const e = expandMul(asNumerDenom(powdenest(factorTerms(asEquation(expr), { radical: true, clear: true })))[0]);
  const syms = symbols.length ? symbols : [...e.freeSymbols()].filter((s) => s instanceof Sym);
  const radicals = new Map<string, [Pow, Rational]>();
  const visit = (a: Expr): void => {
    if (a instanceof Pow && a.exp instanceof Rational && !a.exp.isInteger && syms.some((s) => a.base.has(s))) radicals.set(a.key, [a, a.exp]);
    a.args.forEach(visit);
  };
  visit(e);
  if (!radicals.size) return NoMatch;
  const rads = [...radicals.values()];
  const L = rads.reduce((l, [, p]) => l * p.q / gcdBig(l, p.q), 1n);
  const canonical = (a: Expr): Expr => {
    const b = expandMul(a);
    return couldExtractMinusSign(b) ? mul(-1, b) : b;
  };
  const single = unradOnce(e, syms);
  if (single !== undefined) return [canonical(single), []];
  const base = first(rads)[0].base;
  if (base instanceof Sym && rads.every(([r]) => r.base.equals(base))) {
    const p = new Dummy('p');
    const replaced = xreplace(e, rads.map(([r, exponent]): [Expr, Expr] => [r, pow(p, mul(exponent, Rational.of(L)))]));
    return [canonical(xreplace(replaced, [[base, pow(p, Rational.of(L))]])), [p, add(pow(p, Rational.of(L)), mul(-1, base))]];
  }
  const terms = e instanceof Add ? e.args : [e];
  if (terms.length === 2 && terms.every((t) => rads.some(([r]) => t.has(r)))) {
    const [a, b] = [at(sortExprs([...terms]), 1), at(sortExprs([...terms]), 0)];
    const cleared = canonical(add(pow(a, Rational.of(L)), mul(-1, pow(mul(-1, b), Rational.of(L)))));
    radicals.clear();
    visit(cleared);
    if (!radicals.size) return [cleared, []];
  }
  throw new NotImplementedError('unrad: cannot remove these coupled radicals');
}

/** Does the candidate solution satisfy the assumptions of x and keep denominators nonzero? */
function checkSolution(f: Expr, x: Sym, v: Expr): boolean {
  const a = x.assumptions;
  // Reject only a proven contradiction; symbolic candidates may remain undecidable.
  for (const name of ['positive', 'negative', 'nonnegative', 'nonpositive', 'real', 'imaginary', 'integer', 'zero'] as const) {
    const expected = a[name];
    if (expected === undefined) continue;
    const actual = ask(Q[name](v));
    if (actual === !expected) return false;
    if (name === 'real' && expected && actual === 'unknown') {
      const factors = v instanceof Mul ? v.args.filter((a) => !(a instanceof Rational)) : [v];
      const radical = factors[0];
      if (factors.length === 1 && radical instanceof Pow && radical.exp instanceof Rational && radical.exp.q === 2n && positiveExpression(expandMul(mul(-1, radical.base)))) return false;
    }
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
    if (b.equals(S.Zero) && y.equals(S.One)) return [n, [S.Zero]];
    if (y.equals(S.Zero) && b.has(x) && n.has(x)) return [b, [S.Zero]];
    if (b instanceof Constant && b.name === 'E') {
      if (y.equals(S.Zero)) return [n, []];
      // exp(-u) = y  ->  u = log(1/y), with 1/(-a - b) written as -1/(a + b) like SymPy
      if (couldExtractMinusSign(n)) {
        const iy = pow(y, -1);
        const inv = iy instanceof Pow && iy.base instanceof Add && couldExtractMinusSign(iy.base) ? mul(-1, pow(mul(-1, iy.base), -1)) : iy;
        return [mul(-1, n), [log(inv)]];
      }
      return [n, [log(y)]];
    }
    // SymPy _tsolve: a positive constant base is inverted by its real logarithm.
    if (!b.has(x) && n.has(x) && ask(Q.positive(b)) === true) {
      const coeffs = b instanceof Rational ? polyCoefficients(n, x) : undefined;
      const slope = coeffs?.get(1);
      if (coeffs && Math.max(...coeffs.keys()) === 1 && slope instanceof Rational && slope.isInteger && !y.equals(S.Zero)) {
        const count = Math.abs(slope.toNumber());
        if (count > 1 && count <= 100) {
          return [n, Array.from({ length: count }, (_, i) => mul(add(log(y), mul(2 * (i - Math.floor(count / 2)), S.Pi, S.I)), pow(log(b), -1)))];
        }
      }
      return [n, isZeroE(y) ? [] : [mul(log(y), pow(log(b), -1))]];
    }
    // (b**u)**v = b**(u*v) when b is positive, with the resulting
    // candidates checked against the principal power in the original equation.
    if (b instanceof Pow && !b.base.has(x) && ask(Q.positive(b.base)) === true) {
      return [mul(b.exp, n), isZeroE(y) ? [] : [mul(log(y), pow(log(b.base), -1))]];
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
    case 'cot':
      return [u, [isZeroE(y) ? mul(S.Half, S.Pi) : atan(pow(y, -1))]];
    case 'sec':
    case 'csc':
    case 'sech':
    case 'csch': {
      if (isZeroE(y)) return [u, []];
      const reciprocal = { sec: 'cos', csc: 'sin', sech: 'cosh', csch: 'sinh' } as const;
      return invertFn(new Fn(reciprocal[f.name], f.args), pow(y, -1), x);
    }
    case 'tanh':
    case 'coth': {
      if (y.equals(S.One) || y.equals(S.NegOne)) return [u, []];
      const denominator = f.name === 'tanh' ? add(1, mul(-1, y)) : add(y, -1);
      return [u, [mul(S.Half, log(mul(add(y, 1), pow(denominator, -1))))]];
    }

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
    case 'asin': return [u, [sin(y)]];
    case 'acos': return [u, [cos(y)]];
    case 'atan': return [u, [tan(y)]];
    case 'atan2': {
      const second = at(f.args, 1);
      return !second.has(x) && ask(Q.positive(second)) === true ? [u, [mul(second, tan(y))]] : undefined;
    }
    case 'erf': return [u, [fn('erfinv', [y])]];
    case 'erfinv': return [u, [fn('erf', [y])]];
    case 'erfc': return [u, [fn('erfcinv', [y])]];
    case 'erfcinv': return [u, [fn('erfc', [y])]];
    case 'conjugate': return [u, [fn('conjugate', [y])]];
    case 'abs': return isZeroE(y) ? [u, [S.Zero]] : undefined;
    case 'LambertW': return [u, [mul(y, exp(y))]];
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
  const f = mapBottomUp(f0, (e) => e instanceof Fn && e.name === 'binomial' && e.has(x) ? expandFunc(e) : e instanceof Pow && e.base === S.E && e.exp instanceof Add && e.exp.has(x) ? expand_power_exp(e) : e);
  const absolute = (e: Expr): Fn | undefined => e instanceof Fn && e.name === 'abs' && e.has(x) ? e : e.args.map(absolute).find((v) => v !== undefined);
  const a = absolute(f);
  if (a !== undefined && ask(Q.real(x)) === true) {
    const u = first(a.args);
    return [u, mul(-1, u)].flatMap((v) => solveRaw(xreplace(f, [[a, v]]), x, depth + 1)).filter((v) => checkSolution(f, x, v));
  }
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
    const constant = pc.get(0);
    if (degree > 2 && pc.size === 2 && constant instanceof Add && !rational) {
      const ratio = mul(-1, constant, pow(getOrThrow(pc, degree), -1));
      const root = powdenest(pow(factor(ratio), Rational.of(1, degree)), { force: true });
      if (!(root instanceof Pow) || !root.exp.equals(Rational.of(1, degree))) {
        return roots(add(pow(x, degree), -1), x).map((unity) => mul(root, unity));
      }
    }
    let rs: Expr[];
    try {
      rs = roots(n, x, { quintics: true });
    } catch (err) {
      if (!(err instanceof NotImplementedError && (rational || degree === 5))) throw err;
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
  if (dep.length > 1) {
    const factored = factorTerms(add(...dep));
    if (factored instanceof Mul && factored.args.filter((term) => term.has(x)).length === 1) {
      const dependent = first(factored.args.filter((term) => term.has(x)));
      if (dependent instanceof Pow && !dependent.exp.has(x) && !(dependent.exp instanceof Rational && dependent.exp.isInteger)) {
        const independent = add(...terms.filter((term) => !term.has(x)));
        const coefficient = mul(...factored.args.filter((term) => !term.has(x)));
        const y = mul(-1, independent, pow(coefficient, -1));
        return solveRaw(add(dependent.base, mul(-1, pow(y, pow(dependent.exp, -1)))), x, depth + 1);
      }
    }
  }
  if (dep.length === 1) {
    const b = add(...terms.filter((t) => !t.has(x)));
    const t = first(dep);
    const factors = t instanceof Mul ? t.args : [t];
    const fdep = factors.filter((g) => g.has(x));
    if (fdep.length === 1) {
      const a = mul(...factors.filter((g) => !g.has(x)));
      const F = first(fdep);
      const y = mul(-1, b, pow(a, -1));
      if (F instanceof Pow && y.equals(S.One) && F.base.has(x) && F.exp.has(x)) {
        return [F.exp, add(F.base, -1), add(F.base, 1)].flatMap((g) => solveRaw(g, x, depth + 1)).filter((v) => checksol(f, x, v) === true);
      }
      if (F instanceof Fn || (F instanceof Pow && !isExpPower(F))) {
        const inv = invertFn(F, y, x);
        if (inv) {
          const [u, ys] = inv;
          return ys.flatMap((yy) => solveRaw(add(u, mul(-1, yy)), x, depth + 1));
        }
      }
    }
  }
  // SymPy _tsolve takes logarithms when both exponential terms have positive bases.
  if (terms.length === 2) {
    const [firstTerm, secondTerm] = [at(terms, 0), at(terms, 1)];
    for (const [lhs, rhs] of [[firstTerm, mul(-1, secondTerm)], [secondTerm, mul(-1, firstTerm)]] as const) {
      if (lhs instanceof Pow && lhs.base.equals(rhs) && lhs.exp.has(x) === false && rhs.has(x)) {
        return solveRaw(add(pow(rhs, add(lhs.exp, -1)), -1), x, depth + 1);
      }
      if (lhs instanceof UndefFn && rhs instanceof UndefFn && lhs.name === rhs.name && lhs.args.length === 1 && rhs.args.length === 1) {
        return solveRaw(add(first(lhs.args), mul(-1, first(rhs.args))), x, depth + 1);
      }
    }
    const exponential = (term: Expr): [Expr, Expr] | undefined => {
      const factors = term instanceof Mul ? term.args : [term];
      const dependent = factors.filter((a) => a.has(x));
      if (!dependent.length || !dependent.every((a): a is Pow => a instanceof Pow && !a.base.has(x) && ask(Q.positive(a.base)) === true)) return undefined;
      return [mul(...factors.filter((a) => !a.has(x))), add(...dependent.map((a) => mul(a.exp, log(a.base))))];
    };
    const lhs = exponential(at(terms, 0)), rhs = exponential(at(terms, 1));
    if (lhs && rhs) {
      const rewritten = rewriteExponential(num, x);
      if (!rewritten.equals(num)) {
        const solved = singleGenerator(rewritten, x, depth);
        if (solved) return solved;
      }
      const ratio = mul(-1, rhs[0], pow(lhs[0], -1));
      if (ask(Q.positive(ratio)) === true) return solveRaw(add(lhs[1], mul(-1, rhs[1]), mul(-1, log(ratio))), x, depth + 1);
    }
    const powers = terms.map((term) => (term instanceof Mul ? term.args : [term]).filter((a) => a.has(x)));
    const [a] = at(powers, 0), [b] = at(powers, 1);
    if (a instanceof Pow && b instanceof Pow && !a.base.has(x) && !b.base.has(x) && a.exp.equals(b.exp) && ask(Q.integer(a.exp)) === true) {
      const coefficients = terms.map((term) => mul(...(term instanceof Mul ? term.args : [term]).filter((factor) => !factor.has(x))));
      return solveRaw(add(mul(a.exp, log(mul(a.base, pow(b.base, -1)))), mul(-1, log(mul(-1, at(coefficients, 1), pow(at(coefficients, 0), -1))))), x, depth + 1);
    }
    for (const [lhs, rhs] of [[firstTerm, mul(-1, secondTerm)], [secondTerm, mul(-1, firstTerm)]] as const) {
      if (lhs instanceof Pow && lhs.base.equals(x) && lhs.exp instanceof Rational && rhs instanceof Pow && !rhs.base.has(x) && ask(Q.positive(rhs.base)) === true) {
        const solutions = lambertLogForm(add(mul(lhs.exp, log(x)), mul(-1, log(rhs.base), rhs.exp)), x);
        if (solutions) return solutions;
      }
    }
  }
  const rad = singleRadical(num, x, depth);
  if (rad) return rad;
  const multi = radicalsOfX(num, x);
  if (multi) return multi;
  const pair = clearSquareRootPair(num, x);
  if (pair) return solveRaw(pair, x, depth + 1);
  const lw = lambertSolve(num, x) ?? tsolveLambert(num, x, depth);
  if (lw) return lw;
  // sum_i c_i*log(g_i) + b = 0 with rational c_i: prod_i g_i**(L*c_i) = exp(-L*b) (SymPy logcombine with force)
  const lg = logSum(terms, x);
  if (lg) return solveRaw(expandMul(add(lg[0], mul(-1, exp(mul(-1, lg[1]))))), x, depth + 1);
  const gen = singleGenerator(num, x, depth);
  if (gen) return gen;
  const nested = solveInSubexpression(num, x, depth);
  if (nested) return nested;
  const trig = solveTrig(num, x, depth);
  if (trig) return trig;
  const rewritten = rewriteExponential(num, x);
  if (!rewritten.equals(num)) {
    const cancelled = cancel(rewritten);
    return solveRaw(f instanceof Add && f.args.some((term) => term.equals(x)) || polyCoefficients(cancelled, x) ? cancelled : rewritten, x, depth + 1);
  }
  throw new NotImplementedError(`solve: cannot solve ${f.toString()} for ${x.name}`);
}

/** Rewrite powers and hyperbolic functions with compatible exponential generators. */
function rewriteExponential(e: Expr, x: Sym): Expr {
  return mapBottomUp(e, (term) => {
    if (!term.has(x)) return term;
    if (term instanceof Pow && term.base instanceof Rational && term.base.isPositive && term.exp.has(x)) {
      const power = perfectPower(term.base);
      return power === false ? exp(mul(term.exp, log(term.base))) : exp(mul(power[1], term.exp, log(power[0])));
    }
    if (!(term instanceof Fn)) return term;
    const [arg] = term.args;
    if (!arg || !['sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch'].includes(term.name)) return term;
    const positive = exp(arg), negative = exp(mul(-1, arg));
    const sum = add(positive, negative), difference = add(positive, mul(-1, negative));
    switch (term.name) {
      case 'sinh': return mul(S.Half, difference);
      case 'cosh': return mul(S.Half, sum);
      case 'tanh': return mul(difference, pow(sum, -1));
      case 'coth': return mul(sum, pow(difference, -1));
      case 'sech': return mul(2, pow(sum, -1));
      default: return mul(2, pow(difference, -1));
    }
  });
}

/** Reduce an equation to a single repeated expression, including linear logarithmic generators. */
function solveInSubexpression(e: Expr, x: Sym, depth: number): Expr[] | undefined {
  const candidates = new Map<string, Expr>();
  mapBottomUp(e, (term) => {
    if (term instanceof Pow && term.has(x)) {
      for (const part of term.args) if (!part.equals(x) && part.has(x) && part.args.length) candidates.set(part.key, part);
    }
    return term;
  });
  const t = new Dummy('u');
  const logarithm = log(x);
  for (const part of candidates.values()) {
    let transformed = subs(e, [[part, t]]);
    if (transformed.has(x) && part instanceof Add && part.args.some((term) => term.equals(logarithm))) {
      const rest = add(...part.args.filter((term) => !term.equals(logarithm)));
      transformed = expandMul(xreplace(transformed, [[logarithm, add(t, mul(-1, rest))]]));
    }
    if (transformed.has(x) || !transformed.has(t)) continue;
    return solveRaw(transformed, t, depth + 1).flatMap((value) => solveRaw(add(part, mul(-1, value)), x, depth + 1));
  }
  return undefined;
}

/** Clear two square roots occurring in separate terms by isolating their product. */
function clearSquareRootPair(e: Expr, x: Sym): Expr | undefined {
  if (!(e instanceof Add)) return undefined;
  const radicals: [Expr, Pow][] = [];
  const other: Expr[] = [];
  for (const term of e.args) {
    const factors = term instanceof Mul ? term.args : [term];
    const r = factors.find((p): p is Pow => p instanceof Pow && p.exp.equals(S.Half) && p.has(x));
    if (r) radicals.push([mul(...factors.filter((f) => f !== r)), r]);
    else other.push(term);
  }
  if (radicals.length !== 2 || !other.length) return undefined;
  const [a, r] = at(radicals, 0), [b, s] = at(radicals, 1);
  const ar = mul(pow(a, 2), r.base), bs = mul(pow(b, 2), s.base);
  const square = add(pow(add(...other), 2), mul(-1, ar), mul(-1, bs));
  const cleared = expand(add(pow(square, 2), mul(-4, ar, bs)));
  return polyCoefficients(cleared, x) ? cleared : undefined;
}

/** Join sine and cosine generators through the tangent half-angle substitution. */
function solveTrig(e: Expr, x: Sym, depth: number): Expr[] | undefined {
  const functions = new Map<string, Fn>();
  mapBottomUp(e, (term) => {
    if (term instanceof Fn && term.has(x) && ['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(term.name)) functions.set(term.key, term);
    return term;
  });
  if (functions.size < 2) return undefined;
  const nodes = [...functions.values()];
  const args = nodes.map((term) => first(term.args));
  const u = args.find((arg) => args.every((other) => {
    const ratio = cancel(mul(other, pow(arg, -1)));
    return ratio.equals(1) || ratio.equals(2);
  }));
  if (!u) return undefined;
  const sameArgument = args.every((arg) => arg.equals(u));
  const t = new Dummy('tangent');
  if (e instanceof Add && e.args.length === 2 && nodes.length === 2 && sameArgument) {
    const sine = nodes.find((term) => term.name === 'sin'), cosine = nodes.find((term) => term.name === 'cos');
    if (sine && cosine) {
      const s = polyCoefficients(xreplace(e, [[sine, t]]), t);
      const c = polyCoefficients(xreplace(e, [[cosine, t]]), t);
      if (s?.size === 2 && c?.size === 2 && s.has(0) && c.has(0)) {
        const degree = Math.max(...s.keys());
        const a = getOrThrow(s, degree), b = getOrThrow(c, Math.max(...c.keys()));
        if (degree === Math.max(...c.keys()) && !a.has(x) && !b.has(x) && fraction(cancel(mul(a, pow(b, -1))))[1].isNumber) {
          return solveRaw(add(mul(a, pow(tan(u), degree)), b), x, depth + 1);
        }
      }
    }
  }
  // The exponential form retains the poles of tan(u/2) when a tangent and
  // a sine or cosine already share an argument in the input.
  const exponential = sameArgument && nodes.some((term) => term.name === 'tan' || term.name === 'cot');
  const denominator = add(1, pow(t, 2));
  const s = exponential ? mul(S.Half, S.I, add(pow(t, -2), mul(-1, pow(t, 2)))) : mul(2, t, pow(denominator, -1));
  const c = exponential ? mul(S.Half, add(pow(t, 2), pow(t, -2))) : mul(add(1, mul(-1, pow(t, 2))), pow(denominator, -1));
  const replacements: [Expr, Expr][] = nodes.map((term) => {
    const double = !first(term.args).equals(u);
    const sinValue = double ? mul(2, s, c) : s;
    const cosValue = double ? add(pow(c, 2), mul(-1, pow(s, 2))) : c;
    const values: Record<string, Expr> = { sin: sinValue, cos: cosValue, tan: mul(sinValue, pow(cosValue, -1)), cot: mul(cosValue, pow(sinValue, -1)), sec: pow(cosValue, -1), csc: pow(sinValue, -1) };
    return [term, defined(values[term.name], 'trigonometric replacement')];
  });
  const transformed = cancel(xreplace(e, replacements));
  if (transformed.has(x)) return undefined;
  if (isZeroE(transformed)) throw new NotImplementedError('solve: trigonometric identity has infinitely many branches');
  return solveRaw(transformed, t, depth + 1).filter((v) => !exponential || !v.equals(S.Zero)).flatMap((v) => {
    const inverse = exponential ? mul(-2, S.I, log(v)) : mul(2, atan(v));
    return solveRaw(add(u, mul(-1, inverse)), x, depth + 1);
  });
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

export interface SolveOptions {
  check?: boolean;
  cubics?: boolean;
  implicit?: boolean;
  simplify?: boolean;
}

export function solve(e: ExprLike, x?: Expr, opts: SolveOptions = {}): Expr[] {
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
  const syms = [...freeSymbols(f)].filter((s) => s instanceof Sym);
  const numerator = x === undefined && syms.length > 1 ? asNumerDenom(f)[0] : f;
  const variables = numerator === f ? syms : syms.filter((s) => numerator.has(s));
  const v = x ?? (variables.length === 1 ? first(variables) : undefined);
  if (v === undefined) {
    if (!variables.length) return [];
    throw new TypeError('solve: specify the symbol to solve for');
  }
  if (opts.implicit) {
    const hidden: [Expr, Expr][] = [];
    const mask = (term: Expr): Expr => {
      if (!term.has(v) || term.equals(v)) return term;
      if (term instanceof Fn || term instanceof UndefFn || term instanceof Pow) {
        const existing = hidden.find(([, original]) => original.equals(term));
        if (existing) return existing[0];
        const placeholder = new Dummy('implicit');
        hidden.push([placeholder, term]);
        return placeholder;
      }
      return rebuild(term, term.args.map(mask));
    };
    return solve(mask(f), v, { ...opts, implicit: false }).map((root) => xreplace(root, hidden));
  }
  if (v.assumptions.imaginary === true) {
    const real = new Dummy('real', { real: true });
    const substitutions = syms.filter((s) => s.assumptions.imaginary === true && s.key !== v.key).map((s): [Sym, Sym] => [s, new Dummy('real', { real: true })]);
    const result = solve(xreplace(f, [[v, mul(S.I, real)], ...substitutions.map(([s, r]): [Sym, Expr] => [s, mul(S.I, r)])]), real, opts);
    const back = substitutions.map(([s, r]): [Sym, Expr] => [r, mul(-1, S.I, s)]);
    return sortExprs(result.map((r) => mul(S.I, xreplace(r, back))));
  }
  const folded = piecewiseFold(f);
  if (folded instanceof Piecewise && folded.pairs.some(([, condition]) => condition.has(v))) {
    const solutions: Expr[] = [];
    let previous: Expr = S.false;
    for (const [expression, condition] of folded.pairs) {
      const active = and(condition, not(previous));
      previous = or(previous, condition);
      if (active instanceof BoolAtom && !active.value) continue;
      if (isZeroE(expression)) throw new NotImplementedError('solve: Piecewise equation has an interval of solutions');
      for (const candidate of solve(expression, v, opts)) {
        const valid = subs(active, [[v, candidate]]);
        if (valid instanceof BoolAtom) {
          if (valid.value) solutions.push(candidate);
        } else solutions.push(piecewise([candidate, valid], [S.NaN, true]));
      }
    }
    return sortExprs(uniqueKeys(solutions));
  }
  const raw0 = solveRaw(f, v);
  if (opts.check === false && opts.simplify === false && f instanceof Add && f.args.length === 2) {
    const radicands = f.args.map((term) => (term instanceof Mul ? term.args : [term]).find((factor): factor is Pow => factor instanceof Pow && factor.exp.equals(S.Half)));
    if (radicands.every((radical) => radical !== undefined)) {
      // Raw radical elimination can introduce zeros from the denominators of the radicands.
      for (const radical of radicands) {
        for (const denominator of denominators(radical.base)) {
          if (denominator.has(v) && polyCoefficients(denominator, v)) raw0.push(...solveRaw(denominator, v));
        }
      }
    }
  }
  // SymPy: high-order root lists (more than two roots) are not simplified
  const raw = opts.simplify === false || raw0.length > 2 ? raw0 : raw0.map((r) => simplifySolution(r));
  const checked = opts.check === false ? raw : raw.filter((r) => checkSolution(f, v, r) && denominators(sympify(e)).every((d) => !isZeroE(xreplace(d, [[v, r]]))));
  // indexed roots (CRootOf) keep their order
  return raw.some((r) => r.kind === 'Extension') ? checked : sortExprs(checked);
}

/** Solve a univariate relation when a sign or a single excluded value decides it. */
export function solveRelation(relation: Rel, symbol?: Sym): Expr | NoMatchResult {
  const variables = [...freeSymbols(relation)].filter((s) => s instanceof Sym);
  const x = symbol ?? (variables.length === 1 ? first(variables) : undefined);
  if (!x || variables.some((s) => s.key !== x.key)) return NoMatch;
  const lower = Lt(S.NegativeInfinity, x), upper = Lt(x, S.Infinity);
  const difference = add(relation.lhs, mul(-1, relation.rhs));
  if (relation.op === 'Ne' && polyCoefficients(difference, x)?.has(1) && linearEqToMatrix([difference], [x])) {
    return and(lower, upper, ...solve(difference, x).map((root) => Ne(x, root)));
  }
  if (relation.op === 'Eq' || relation.op === 'Ne') return NoMatch;
  const real = x.assumptions.real === true ? x : new Dummy('real', { real: true });
  const expression = xreplace(difference, [[x, real]]);
  const forward = relation.op === 'Gt' || relation.op === 'Ge';
  const ordered = forward ? expression : mul(-1, expression);
  return positiveExpression(ordered) ? and(lower, upper) : NoMatch;
}

/** Solve each independent factor for one of the available variables. */
export function solveForSymbols(equation: ExprLike, symbols: readonly Expr[], opts: SolveOptions = {}): Map<Expr, Expr>[] {
  const f = asEquation(equation);
  if (symbols.every((v) => v instanceof Sym) && symbols.every((v) => v.assumptions.real === true || v.assumptions.imaginary === true) && f.has(S.I)) {
    const parts = asRealImag(f);
    if (parts.every((p) => !p.equals(S.Zero)) && linearEqToMatrix(parts, symbols)) {
      return nonlinsolve(parts, symbols, opts).map((row) => new Map(symbols.map((symbol, i) => [symbol, at(row, i)])));
    }
  }
  const numerator = asNumerDenom(f)[0];
  const factored = numerator instanceof Add ? factorTerms(numerator) : numerator;
  const factors = factored instanceof Mul ? factored.args : [factored];
  const result: Map<Expr, Expr>[] = [];
  for (const factor of factors) {
    let unsupported: NotImplementedError | undefined;
    let handled = false;
    const linear = symbols.filter((symbol) => {
      const coefficients = symbol instanceof Sym ? polyCoefficients(factor, symbol) : undefined;
      return coefficients !== undefined && Math.max(...coefficients.keys()) === 1;
    });
    for (const symbol of [...linear, ...symbols.filter((symbol) => !linear.includes(symbol))]) {
      if (!factor.has(symbol)) continue;
      let roots: Expr[];
      try {
        roots = solve(factor, symbol, opts);
      } catch (error) {
        if (!(error instanceof NotImplementedError)) throw error;
        unsupported = error;
        continue;
      }
      handled = true;
      for (const root of roots) {
        if (opts.check === false || denominators(f).every((d) => !isZeroE(subs(d, [[symbol, root]])))) result.push(new Map([[symbol, root]]));
      }
      if (roots.length) break;
    }
    if (!handled && unsupported) throw unsupported;
  }
  return [...new Map(result.map((row) => [[...row].map(([k, v]) => `${k.key}=${v.key}`).join(','), row])).values()];
}

/** Replace free occurrences of target (not inside derivatives); a sum target may match part of a sum. */
function replaceTarget(e: Expr, target: Expr, t: Expr): Expr {
  const go = (x: Expr): Expr => {
    if (x.key === target.key) return t;
    if (x.kind === 'Derivative') return x;
    if (x instanceof Pow && target instanceof Pow && x.base.key === target.base.key) {
      const replaced = subs(x, [[target, t]]);
      if (replaced.key !== x.key) return replaced;
    }
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
    return args.every((a, i) => a === x.args[i]) ? x : rebuild(x, args);
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

/** Determine the unknowns when solving a system without an explicit variable list. */
export function solveVariables(equations: readonly Expr[]): Expr[] {
  const variables: Expr[] = sortExprs(equations.flatMap((eq) => [...freeSymbols(eq)].filter((symbol) => symbol instanceof Sym)));
  if (variables.length >= equations.length) return variables;
  const functions: Expr[] = [];
  for (const equation of equations) {
    mapBottomUp(equation, (term) => {
      if (term instanceof UndefFn) functions.push(term);
      return term;
    });
  }
  return [...variables, ...sortExprs(functions)];
}

/** Test linearity after treating expression-valued targets as independent unknowns. */
export function isLinearSolveSystem(equations: readonly Expr[], targets: readonly Expr[]): boolean {
  const dummies = targets.map(() => new Dummy('linear'));
  const prepared = equations.map((e) => targets.reduce((f, target, i) => replaceTarget(f, target, at(dummies, i)), e));
  if (linearEqToMatrix(prepared, dummies)) return true;
  const rewritten = prepared.map((e) => dummies.reduce((f, v) => rewriteExponential(f, v), e));
  return rewritten.some((e, i) => !e.equals(at(prepared, i))) && linearEqToMatrix(rewritten.map(numerOf), dummies) !== undefined;
}

/** Solve for the real and imaginary components of a complex unknown. */
export function solveComplexComponents(equations: readonly ExprLike[], target: Sym, opts: SolveOptions = {}): Map<Expr, Expr>[] | NoMatchResult {
  const re = fn('re', [target]), im = fn('im', [target]);
  const original = equations.map(asEquation);
  if (re.equals(target) || im.equals(target) || !original.some((e) => e.has(re)) || !original.some((e) => e.has(im))) return NoMatch;
  const r = new Dummy('real'), i = new Dummy('imaginary');
  const rest = original.map((e) => xreplace(e, [[re, r], [im, i]]));
  if (rest.some((e) => e.has(target))) return NoMatch;
  const cartesian = add(r, mul(S.I, i));
  const rows = original.length === 1
    ? nonlinsolve([...rest, add(cartesian, mul(-1, target))], [r, i], opts)
    : nonlinsolve(rest, [r, i], opts);
  return rows.map((row) => {
    const real = at(row, 0), imaginary = at(row, 1);
    const pairs: [Expr, Expr][] = [[re, real], [im, imaginary]];
    if (original.length > 1) pairs.unshift([target, xreplace(cartesian, [[r, real], [i, imaginary]])]);
    return new Map(pairs);
  });
}

/** Back-substitute an indexed root to keep a large exact eliminant compact. */
function solveIndexedSystem(equations: readonly Expr[], variables: readonly Sym[]): Expr[][] | undefined {
  if (variables.length !== 2 || equations.length !== 2) return undefined;
  const [u, v] = [at(variables, 0), at(variables, 1)];
  const polynomials = equations.map((e) => Poly.from(e, variables));
  const coefficients = polynomials.flatMap((p) => p.coeffs());
  if (!coefficients.every((c) => c instanceof Rational) || !coefficients.some((c) => c instanceof Rational && (c.p > 1_000_000n || c.p < -1_000_000n || c.q > 1_000_000n))) return undefined;
  const basis = groebner(equations, variables).exprs;
  const eliminant = basis.find((e) => e.has(v) && !e.has(u));
  const other = basis.find((e) => e.has(u));
  if (basis.length !== 2 || !eliminant || !other) return undefined;
  const linear = polyCoefficients(other, u);
  const leading = linear?.get(1);
  if (!linear || Math.max(...linear.keys()) !== 1 || !(leading instanceof Rational)) return undefined;
  const [, factors] = Poly.from(eliminant, [v]).factorList();
  if (factors.length !== 1 || first(factors)[0].degree() < 4) return undefined;
  const polynomial = first(factors)[0];
  const solved = mul(-1, linear.get(0) ?? S.Zero, pow(leading, -1));
  return Array.from({ length: polynomial.degree() }, (_, index) => {
    const root = new CRootOf(polynomial.asExpr(), index);
    return [xreplace(solved, [[v, root]]), root];
  });
}

/** Prefer sparse equations and pivots independent of the remaining unknowns in overdetermined systems. */
function linearPivot(equations: readonly Expr[], unknowns: readonly Sym[], preferConstant: boolean) {
  const candidates = [...equations];
  const numerators = new Map<Expr, Expr>();
  if (preferConstant) {
    for (const equation of equations) numerators.set(equation, numerOf(equation));
    const priorities = new Map(ordered([...numerators.values()]).map((numerator, index) => [numerator, index]));
    const countUnknowns = new Map(equations.map((eq) => [eq, unknowns.filter((u) => eq.has(u)).length]));
    candidates.sort((a, b) =>
      getOrThrow(countUnknowns, a) - getOrThrow(countUnknowns, b) ||
      getOrThrow(priorities, getOrThrow(numerators, a)) - getOrThrow(priorities, getOrThrow(numerators, b)),
    );
  }
  let deferred: { equation: Expr; symbol: Sym; c0: Expr; c1: Expr; canVanish: boolean } | undefined;
  for (const equation of candidates) {
    const numerator = numerators.get(equation) ?? numerOf(equation);
    for (const symbol of unknowns) {
      const coefficients = polyCoefficients(numerator, symbol);
      if (!coefficients || Math.max(...coefficients.keys()) !== 1) continue;
      const c1 = getOrThrow(coefficients, 1);
      const canVanish = unknowns.some((u) => c1.has(u));
      const pivot = { equation, symbol, c0: coefficients.get(0) ?? S.Zero, c1, canVanish };
      if (!preferConstant || !canVanish) return pivot;
      deferred ??= pivot;
    }
  }
  return deferred;
}

/**
 * Solve a polynomial system by successive elimination: equations that are
 * univariate (after substitution) are solved and their solutions substituted.
 * Returns the list of solution tuples.
 */
export function nonlinsolve(eqs: readonly ExprLike[], syms: readonly Expr[], opts: { check?: boolean; checkAssumptions?: boolean; manual?: boolean; rational?: boolean } = {}): Expr[][] {
  if (opts.rational && eqs.some((e) => some(sympify(e), (atom) => atom instanceof Float))) {
    const exact = eqs.map((e) => mapBottomUp(sympify(e), (atom) => atom instanceof Float ? rationalFromString(atom.toString()) : atom));
    return nonlinsolve(exact, syms, { ...opts, rational: false });
  }
  if (!syms.every((v) => v instanceof Sym)) {
    const targets = syms.map((v, i): [Expr, Sym] => [v, new Dummy(`t${i}`)]);
    const replaced = eqs.map((e) => targets.reduce((f, [v, d]) => replaceTarget(f, v, d), asEquation(e)));
    const back = targets.map(([v, d]): [Expr, Expr] => [d, v]);
    return nonlinsolve(replaced, targets.map(([, d]) => d), opts).map((row) => row.map((v) => xreplace(v, back)));
  }
  const lin = linearEqToMatrix(eqs, syms);
  if (lin) {
    const s = solveAugmented(lin[0].hstack(lin[1]), syms);
    if (s) return opts.check === false || opts.checkAssumptions === false || syms.every((v, i) => checkSolution(S.Zero, v, at(s, i))) ? [s] : [];
    if (!opts.manual || opts.check !== false) return [];
  }
  if (opts.manual && opts.check === false && syms.length === 1 && eqs.length) {
    const symbol = first(syms);
    return solve(first(eqs), symbol, { check: false }).map((value) => [value]);
  }
  const results: Expr[][] = [];
  const preferConstant = eqs.length > syms.length && opts.manual !== true;
  const go = (system: Expr[], assigned: Map<string, Expr>) => {
    const unchecked = opts.check === false && assigned.size > 0;
    // (the equations keep their denominators factored: the branch bookkeeping compares them in that form)
    const pending = uniqueKeys(system.map((e) => withFactoredDenominators(() => expandMul(e))).filter((e) => !isZeroE(e) && !(unchecked && (e instanceof Special || opts.manual && !syms.some((s) => !assigned.has(s.key) && e.has(s))))));
    const active = syms.filter((s) => !assigned.has(s.key) && pending.some((e) => e.has(s)));
    const unknowns = active.length > pending.length ? [...active].sort((a, b) => compareKeys(sortKey(a), sortKey(b))) : active;
    if (pending.length === 0) {
      // remaining unknowns are free parameters
      results.push(syms.map((s) => assigned.get(s.key) ?? s));
      return;
    }
    if (unknowns.length === 0) return;
    if (opts.check !== false && pending.some((e) => e.has(S.ComplexInfinity) || e.has(S.NaN))) return;
    if (pending.some((e) => freeSymbols(e).size === 0 || !unknowns.some((u) => e.has(u)))) return;
    // Branch on a common factor before linear elimination can divide it out.
    if (active.length > pending.length) {
      for (const equation of pending) {
        const product = factorTerms(equation);
        if (!(product instanceof Mul)) continue;
        const factors = product.args.filter((f) => unknowns.some((u) => f.has(u)));
        if (factors.length < 2 || !factors.some((f) => f instanceof Sym)) continue;
        for (const f of factors) go([f, ...pending.filter((p) => p !== equation)], assigned);
        return;
      }
    }
    // Eliminate a variable local to one equation while leaving shared
    // variables available for the other equations.
    if (!opts.manual && active.length > pending.length && pending.length > 1) {
      for (const e of pending) {
        for (const u of unknowns) {
          if (!e.has(u) || pending.some((p) => p !== e && p.has(u))) continue;
          const coefficients = polyCoefficients(e, u);
          if (!coefficients) continue;
          const degree = Math.max(...coefficients.keys());
          if (degree < 2 || !getOrThrow(coefficients, degree).isNumber) continue;
          for (const value of solve(e, u, { check: false })) {
            const next = new Map(assigned);
            next.set(u.key, value);
            go(pending.filter((p) => p !== e), next);
          }
          return;
        }
      }
    }
    const pivot = linearPivot(pending, unknowns, preferConstant);
    if (pivot) {
      const { equation, symbol, c0, c1, canVanish } = pivot;
      const remaining = pending.filter((e) => e !== equation);
      // The nonzero pivot gives the value of the symbol. Its vanishing branch
      // leaves the symbol free and requires both coefficients to be zero.
      if (canVanish) go([c1, c0, ...remaining], assigned);
      const value = cancel(mul(-1, c0, pow(c1, -1)));
      if (value instanceof Special) {
        if (unchecked) go(remaining, assigned);
        return;
      }
      const next = new Map(assigned);
      for (const [key, old] of next) next.set(key, cancel(xreplace(old, [[symbol, value]])));
      next.set(symbol.key, value);
      go(remaining.map((e) => xreplace(e, [[symbol, value]])), next);
      return;
    }
    // a univariate equation
    for (const e of pending) {
      const vars = unknowns.filter((u) => e.has(u));
      if (vars.length !== 1) continue;
      const u = first(vars);
      let sols: Expr[];
      try {
        sols = solve(e, u, { check: false }).filter((v) =>
          opts.check === false || denominators(e).every((dd) => !isZeroE(xreplace(dd, [[u, v]]))),
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
    // An equation with constant leading coefficient leaves the other coordinates as parameters.
    if (pending.length === 1) {
      const equation = first(pending);
      for (const u of unknowns) {
        const coefficients = polyCoefficients(numerOf(equation), u);
        if (!coefficients || coefficients.size < 2) continue;
        const leading = getOrThrow(coefficients, Math.max(...coefficients.keys()));
        if (unknowns.some((v) => leading.has(v))) go([...coefficients.values()], assigned);
        for (const value of solve(equation, u, { check: false })) {
          const next = new Map(assigned);
          for (const [k, w] of next) next.set(k, simplifyBack(xreplace(w, [[u, value]])));
          next.set(u.key, value);
          go([], next);
        }
        return;
      }
    }
    // Split a factored equation before asking for a zero-dimensional basis.
    const factored = pending.map((e) => factorTerms(e));
    for (const product of factored) {
      if (!(product instanceof Mul)) continue;
      const factors = product.args.filter((f) => unknowns.some((u) => f.has(u)));
      if (factors.length < 2) continue;
      for (const f of factors) go([f, ...pending.filter((_, index) => at(factored, index) !== product)], assigned);
      return;
    }
    // a polynomial system: Groebner basis and back substitution
    const numers = pending.map(numerOf);
    if (numers.every((e) => unknowns.every((u) => polyCoefficients(e, u) !== undefined))) {
      const indexed = opts.check === false ? solveIndexedSystem(numers, unknowns) : undefined;
      for (const sol of indexed ?? solvePolySystem(numers, unknowns)) {
        const next = new Map(assigned);
        for (const [k, w] of next) next.set(k, simplifyBack(xreplace(w, unknowns.map((u, i): [Expr, Expr] => [u, at(sol, i)]))));
        unknowns.forEach((u, i) => next.set(u.key, at(sol, i)));
        // Symbols absent from the remaining equations are free parameters.
        results.push(syms.map((s) => next.get(s.key) ?? s));
      }
      return;
    }
    throw new NotImplementedError('nonlinsolve: unsupported system');
  };
  const original = eqs.map(asEquation);
  // equations with one radical are squared away (SymPy unrad); spurious solutions are removed below
  const prepared = original.map((e) => unradOnce(e, syms) ?? (denominators(e).length ? unradOnce(numerOf(e), syms) : undefined) ?? e);
  go(prepared, new Map());
  if (opts.check !== false) {
    const valid = results.filter((row) => {
      if (opts.checkAssumptions !== false && !syms.every((v, i) => checkSolution(S.Zero, v, at(row, i)))) return false;
      const assignment = syms.map((v, i): [Expr, Expr] => [v, at(row, i)]);
      return original.every((eq) => denominators(eq).every((d) => !isZeroE(xreplace(d, assignment))));
    });
    results.splice(0, results.length, ...valid);
  }
  // the branches of a vanishing coefficient may meet the others: a solution that is a special case of a family of
  // solutions is dropped
  const unique = [...new Map(results.map((r) => [r.map((x) => x.key).join(','), r])).values()];
  results.splice(0, results.length, ...unique.filter((r) => !unique.some((g) => g !== r && specializes(r, g, syms))));
  if (opts.check === false) return results;
  return results.filter((sol) =>
    original.every((e) => {
      const r = xreplace(e, syms.map((s, i): [Expr, Expr] => [s, at(sol, i)]));
      const variables = [...freeSymbols(r)].filter((s) => s instanceof Sym);
      if (variables.length) {
        // A family must satisfy the equations identically in its free parameters.
        const simplified = expandMul(r);
        const exact = (p: Expr, symbols: readonly Sym[]): boolean => {
          if (!symbols.length) return p instanceof Rational && !p.isZero;
          const coefficients = polyCoefficients(p, first(symbols));
          return coefficients !== undefined && [...coefficients.values()].some((c) => exact(c, symbols.slice(1)));
        };
        return !exact(simplified, variables);
      }
      if (hasExtension(r)) return true;
      try {
        const c = fromMpc(evalMp(r, 200), 200).toComplex();
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
  const original = asEquation(e);
  const only = opts.symbols;
  const eq = mapBottomUp(original, (v) => v.kind === 'Derivative' || (v instanceof Integral && (only === undefined || only.some((s) => v.variable.key !== s.key ? v.has(s) : v.args.length === 2 || v.args.slice(2).some((b) => b.has(s))))) ? impl.doit?.(v) ?? v : v);
  const [n, d] = asNumerDenom(eq);
  if (isZeroE(n)) return [S.Zero, S.One];
  let symbols = [...freeSymbols(n)].filter((s) => s instanceof Sym);
  const { exclude } = opts;
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
    const free = [...freeSymbols(dn)].filter((s) => s instanceof Sym);
    const ok = !free.length || free.some((s) => !isZeroE(diff(dn, s))) || (free.length === symKeys.size && free.every((s) => symKeys.has(s.key)));
    if (!ok) continue;
    allZero = false;
    if (dn.has(xi)) continue;
    const vi = mul(-1, pow(dn, -1), subs(n, [[xi, S.Zero]]));
    if (vi instanceof Special && vi.name === 'nan') continue;
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
export function solveUndeterminedCoeffs(e: ExprLike, coeffs: readonly Expr[], symsIn?: readonly Sym[]): Expr[][];
export function solveUndeterminedCoeffs(e: ExprLike, coeffs: readonly Expr[], symsIn: readonly Sym[], options: { strict: true }): Expr[][] | NoMatchResult;
export function solveUndeterminedCoeffs(e: ExprLike, coeffs: readonly Expr[], symsIn: readonly Sym[] = [], options?: { strict: true }): Expr[][] | NoMatchResult {
  if (!coeffs.every((v) => v instanceof Sym)) {
    const targets = coeffs.map((v, i): [Expr, Sym] => [v, new Dummy(`c${i}`)]);
    const replaced = targets.reduce((f, [v, d]) => replaceTarget(f, v, d), asEquation(e));
    const back = targets.map(([v, d]): [Expr, Expr] => [d, v]);
    const variables = targets.map(([, d]) => d);
    const roots = options ? solveUndeterminedCoeffs(replaced, variables, symsIn, options) : solveUndeterminedCoeffs(replaced, variables, symsIn);
    return Array.isArray(roots) ? roots.map((row) => row.map((v) => xreplace(v, back))) : roots;
  }
  const equation = asEquation(e);
  const [numerator, denominator] = asNumerDenom(equation);
  const f = denominator.equals(S.One) ? expandMul(numerator) : numerOf(cancel(equation));
  if (isZeroE(f)) return [];
  const terms = f instanceof Add ? f.args : [f];
  const dependent = terms.filter((t) => coeffs.some((c) => t.has(c)));
  const independent = add(...terms.filter((t) => !coeffs.some((c) => t.has(c))));
  const candidates = [...freeSymbols(add(...dependent))].filter((v): v is Sym => v instanceof Sym && !coeffs.some((c) => c.key === v.key));
  const common = candidates.filter((v) => independent.has(v));
  const syms = symsIn.length ? symsIn : common.length ? common : candidates;
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
      if (coeffs.some((v) => dep.has(v))) return options?.strict ? NoMatch : [];
      const c = mul(...fs.filter((g) => !syms.some((v) => g.has(v))));
      groups.set(dep.key, [...(groups.get(dep.key) ?? []), c]);
    }
    for (const cs of groups.values()) eqs.push(add(...cs));
  }
  const linear = linearEqToMatrix(eqs, coeffs);
  if (linear && [...linear[0].data, ...linear[1].data].every((entry) => entry.isNumber)) {
    const solution = _linsolve(eqs, coeffs);
    return solution instanceof Map ? [coeffs.map((c) => defined(solution.get(c), 'coefficient'))] : [];
  }
  return nonlinsolve(eqs, coeffs);
}

const isBracket = (v: ExprLike | readonly [ExprLike, ExprLike]): v is readonly [ExprLike, ExprLike] => Array.isArray(v);

/** Numeric root of f near x0 by Newton's method (complex arithmetic). */
export function nsolve(e: readonly ExprLike[], x: readonly Sym[], x0: readonly ExprLike[], opts?: { prec?: number; solver?: 'newton' | 'bisect' }): Matrix;
export function nsolve(e: ExprLike, x: Sym, x0: ExprLike | readonly [ExprLike, ExprLike], opts?: { prec?: number; solver?: 'newton' | 'bisect' }): Expr;
export function nsolve(e: ExprLike | readonly ExprLike[], x: Sym | readonly Sym[], x0: ExprLike | readonly ExprLike[], opts: { prec?: number; solver?: 'newton' | 'bisect' } = {}): Expr | Matrix {
  const isOptions = (v: unknown): boolean => typeof v === 'object' && v !== null && !(v instanceof Expr);
  if (!isOptions(opts)) throw new TypeError('nsolve: options must be an object');
  const list = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);
  if (list(e)) {
    if (x instanceof Sym || !list(x0) || !x.length || x0.length !== x.length || e.length !== x.length) throw new RangeError('nsolve: a square system and one starting value per variable are required');
    if (opts.solver === 'bisect') throw new TypeError('nsolve: bisection requires a scalar equation');
    const digits = opts.prec ?? 15;
    const equations = e.map(asEquation);
    const jacobian = Matrix.of(equations.map((f) => x.map((v) => diff(f, v))));
    let point = x0.map((p) => evalf(sympify(p), digits + 15));
    for (let iteration = 0; iteration < 100; iteration++) {
      const replacements = x.map((v, i): [Expr, Expr] => [v, at(point, i)]);
      const evaluate = (f: Expr): Expr => evalf(xreplace(f, replacements), digits + 15);
      const residual = Matrix.col(...equations.map(evaluate));
      if (residual.data.every((v) => Math.hypot(v.toComplex().re, v.toComplex().im) < 10 ** -digits)) return Matrix.col(...point.map((p) => evalf(p, digits)));
      const step = luSolve(jacobian.map(evaluate), residual);
      point = point.map((p, i) => evalf(add(p, mul(-1, step.get(i, 0))), digits + 15));
    }
    throw new RangeError('nsolve: Newton iteration did not converge');
  }
  if (!(x instanceof Sym) || (list(x0) && x0.length !== 2)) throw new TypeError('nsolve: a scalar variable and a starting value or two endpoints are required');
  const initial = list(x0) ? [at(x0, 0), at(x0, 1)] as const : x0;
  // a bracket is narrowed by bisection in double precision, then refined like a starting point
  const original = asEquation(e);
  const equation = impl.doit?.(original) ?? original;
  const r = isBracket(initial) ? nsolveBisect(equation, x, initial) : nsolveDouble(equation, x, initial);
  // refine with Newton steps in arbitrary precision so that the result is the
  // correctly rounded root (SymPy's mpmath findroot; nsolve(..., prec=n))
  const dps = opts.prec ?? 15;
  const f = equation;
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
  const syms = symbols.length ? [...symbols] : [...freeSymbols(eq)].filter((s) => s instanceof Sym);
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
export function detPerm(M: Matrix): Expr {
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
export function detMinor(M: Matrix): Expr {
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
