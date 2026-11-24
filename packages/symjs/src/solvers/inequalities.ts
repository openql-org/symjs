// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Real solution sets: solveset, univariate (polynomial, rational and
 * periodic) inequalities, reduce_inequalities, and the calculus helpers
 * built on them (singularities, stationary points, monotonicity, extrema,
 * convexity, periodicity).
 */

import { NotImplementedError } from '../core/errors';
import type { Expr, ExprLike, FnName, RelOp } from '../core/nodes';
import { Sym } from '../core/nodes';
import { Add, BoolAtom, Constant, Dummy, ExtensionExpr, Fn, Mul, Piecewise, Pow, Rational, Rel, S, Special, impl } from '../core/nodes';
import { at, cast, defined, expectType, first } from '../core/guard';
import { isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from '../core/assumptions';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { isReal as realFact } from '../core/public';
import { asNumerDenom, asRealImag, coeff } from '../core/methods';
import { expand_log, expandMul } from '../simplify/expand';
import { factorTerms, signsimp } from '../simplify/exprtools';
import { BoolOp, and, not as notB, or as orB } from '../core/boolalg';
import { Eq, Ge, Gt, Le, Lt, Ne, piecewise } from '../core/logic';
import { mapBottomUp, piecewiseFold, some, subs, xreplace } from '../core/traverse';
import { fn, log } from '../functions/elementary/elementary';
import { Max, Min } from '../functions/special/special';
import { hessian, isPositiveSemidefinite } from '../matrices/linalg';
import type { Truth } from '../core/truth';
import { diff } from '../calculus/diff';
import { limit } from '../series/limits';
import { factor, Poly } from '../polys/sympoly';
import { CRootOf } from '../polys/rootof';
import { trigsimp } from '../simplify/trigsimp';
import { polyCoefficients } from '../polys/poly';
import { cancel, fraction } from '../simplify/rational';
import { simplify } from '../simplify/simplify';
import { igcdex, integerLog, limitDenominator, rationalFromFloat } from '../core/numberutils';
import { checksol, denoms, polynomialInGenerator, solve } from './solve';
import { compareKeys, sortKey } from '../printing/sortkey';
import {
  SetExpr,
  SetOp,
  ConditionSet,
  imageSet,
  Integers,
  Complexes,
  EmptySet,
  FiniteSet,
  Interval,
  Reals,
  Range,
  asRelational,
  cmpReal,
  complement,
  Contains,
  containsQ,
  finiteSet,
  interval,
  intersection,
  isSubset,
  realValue,
  union,
  UniversalSet,
} from '../sets/sets';

const isRealSym = (e: Expr) => !e.has(S.I);
/** Order of real numbers whose values are known (the zeros returned by realZeros). */
const approximateRoots = (e: Expr): Expr => mapBottomUp(e, (term) => term instanceof CRootOf ? term.evalApprox(20) : term);
const compareEndpoints = (a: Expr, b: Expr): number | undefined => cmpReal(a, b) ?? cmpReal(approximateRoots(a), approximateRoots(b));
const byValue = (a: Expr, b: Expr): number => defined(compareEndpoints(a, b), 'order of real numbers');
const isDefined = <T>(v: T | undefined): v is T => v !== undefined;
const isExprList = (v: readonly ExprLike[] | ExprLike): v is readonly ExprLike[] => Array.isArray(v);
const relFn: Record<RelOp, (a: ExprLike, b: ExprLike) => Expr> = { Eq, Ne, Lt, Le, Gt, Ge };

function holds(op: Exclude<RelOp, 'Eq'>, v: number): boolean {
  switch (op) {
    case 'Lt':
      return v < 0;
    case 'Le':
      return v <= 0;
    case 'Gt':
      return v > 0;
    case 'Ge':
      return v >= 0;
    case 'Ne':
      return v !== 0;
  }
}

/** The real value of f at x = v, undefined where it is not a finite real number (an unevaluable f throws). */
function numAt(f: Expr, x: Sym, v: Expr): number | undefined {
  const value = xreplace(f, [[x, approximateRoots(v)]]);
  const c = impl.toComplex(value);
  if (!Number.isFinite(c.re) || Math.abs(c.im) > 1e-9 * Math.max(1, Math.abs(c.re))) return undefined;
  return c.re;
}

// ---------------------------------------------------------------------------
// periodicity
// ---------------------------------------------------------------------------

const TRIG_PERIOD: Record<string, Expr> = {};
const trigPeriod = (name: string): Expr | undefined => {
  if (['sin', 'cos', 'sec', 'csc'].includes(name)) return mul(2, S.Pi);
  if (['tan', 'cot'].includes(name)) return S.Pi;
  return TRIG_PERIOD[name];
};

/** Least common multiple of rational multiples of a common factor (SymPy lcim). */
function lcim(ps: Expr[]): Expr | undefined {
  const coeffs: Rational[] = [];
  let base: Expr | undefined;
  for (const p of ps) {
    const c = p.has(S.Pi) ? mul(p, pow(S.Pi, -1)) : p;
    const b = p.has(S.Pi) ? S.Pi : S.One;
    if (!(c instanceof Rational)) return undefined;
    if (base && base.key !== b.key) return undefined;
    base = b;
    coeffs.push(c);
  }
  // periods are positive
  const g = (a: bigint, b: bigint): bigint => (b === 0n ? a : g(b, a % b));
  // lcm of p/q = lcm(p)/gcd(q)
  let num = 1n;
  let den = 0n;
  for (const c of coeffs) {
    num = (num / g(num, c.p)) * c.p;
    den = g(den, c.q);
  }
  // lcim is called with at least one period
  return mul(Rational.of(num, den), defined(base, 'period'));
}

/** Period of f in x, 0 when f does not depend on x, undefined when not periodic. */
export function periodicity(fIn: ExprLike, x: Sym): Expr | undefined {
  if (!(x instanceof Sym)) throw new NotImplementedError('periodicity requires a scalar symbol');
  let f = sympify(fIn);
  if (f instanceof Rel) f = add(f.lhs, mul(-1, f.rhs));
  if (!(f instanceof ExtensionExpr && f.name === 'Mod')) f = simplify(mapBottomUp(f, (node) => node instanceof Fn && node.name === 're' && first(node.args).equals(x) ? x : node));
  if (!f.has(x)) return S.Zero;
  const linCoeff = (a: Expr): Expr | undefined => {
    const p = (() => {
      try {
        return Poly.from(a, [x]);
      } catch {
        return undefined;
      }
    })();
    // the leading coefficient of a polynomial in x does not contain x
    return p?.degree() === 1 ? p.LC() : undefined;
  };
  if (f instanceof ExtensionExpr && f.name === 'Mod') {
      const [argument, modulus] = [at(f.args, 0), at(f.args, 1)];
      if (modulus.has(x)) return undefined;
      const coefficient = linCoeff(argument);
      return coefficient === undefined ? periodicity(argument, x) : impl.abs(mul(modulus, pow(coefficient, -1)));
  }
  if (f instanceof Fn) {
    const P = trigPeriod(f.name);
    if (P) {
      const a = linCoeff(first(f.args));
      if (a !== undefined) return mul(P, pow(impl.abs(a), -1));
    }
    if (f.name === 'abs') {
      // SymPy: Abs of sin, cos, sec or csc (recast as sin) may have half the period of its argument
      const a0 = first(f.args);
      const arg = a0 instanceof Fn && ['cos', 'sec', 'csc'].includes(a0.name) ? fn('sin', [first(a0.args)]) : a0;
      const p = periodicity(arg, x);
      if (p !== undefined && arg instanceof Fn && arg.name === 'sin') {
        const absArg = fn('abs', [arg]);
        const half = mul(p, Rational.of(1, 2));
        if (simplify(xreplace(absArg, [[x, add(x, half)]])).key === simplify(absArg).key) return half;
      }
      return p;
    }
    // a function of a periodic argument (SymPy decompogen)
    if (f.args.length === 1) return periodicity(first(f.args), x);
    return undefined;
  }
  if (f instanceof Pow) {
    const isE = f.base instanceof Constant && f.base.name === 'E';
    if (isE) {
      const e = expandMul(f.exp);
      if (!e.has(S.I)) return periodicity(e, x);
      // exp(a + I*b) for real x: the common period of exp(a)*cos(b) and exp(a)*sin(b) (SymPy)
      const terms = e instanceof Add ? e.args : [e];
      const a = add(...terms.filter((t) => !t.has(S.I)));
      const b = add(...terms.filter((t) => t.has(S.I)).map((t) => mul(-1, S.I, t)));
      if (b.has(S.I)) return undefined;
      const ps = [fn('cos', [b]), fn('sin', [b])].map((t) => periodicity(mul(pow(S.E, a), t), x));
      if (!ps.every(isDefined)) return undefined;
      return lcim(ps);
    }
    const bh = f.base.has(x);
    const eh = f.exp.has(x);
    if (bh && !eh) return periodicity(f.base, x);
    if (eh && !bh) return periodicity(f.exp, x);
    const ps = [f.base, f.exp].map((a) => periodicity(a, x));
    if (!ps.every(isDefined)) return undefined;
    return lcim(ps);
  }
  if (f instanceof Mul || f instanceof Add) {
    const dep = f.args.filter((a) => a.has(x));
    const ps = dep.map((a) => periodicity(a, x));
    if (!ps.every(isDefined)) return undefined;
    return lcim(ps.filter((p) => !(p instanceof Rational && p.isZero)));
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// zeros
// ---------------------------------------------------------------------------

/** Real zeros of e in [lo, hi] (sorted, distinct). */
function realZeros(e: Expr, x: Sym, lo: Expr, hi: Expr): Expr[] {
  if (!e.has(x)) return [];
  // a product vanishes where a factor does (exp(x)*(sin(x) + cos(x)) has the periodic zeros of its second factor)
  const ft = factorTerms(e);
  if (ft instanceof Mul) {
    const zs = ft.args.filter((t) => t.has(x) && !(t instanceof Pow && t.base instanceof Constant && t.base.name === 'E')).flatMap((t) => realZeros(t instanceof Pow ? t.base : t, x, lo, hi));
    return [...new Map(zs.map((z) => [z.key, z])).values()].sort(byValue);
  }
  let base: Expr[];
  try {
    const p = Poly.from(e, [x]);
    if (p.domain === 'ZZ' || p.domain === 'QQ') {
      base = p.realRoots();
    } else base = solve(e, x);
  } catch {
    base = solve(e, x);
  }
  base = base.filter(isRealSym);
  // a zero, bound or period that is not a known real number cannot be placed in the domain
  const known = (v: Expr): number => {
    const n = realValue(v);
    if (n === undefined) throw new NotImplementedError('inequalities: zeros with parameters');
    return n;
  };
  const out: Expr[] = [];
  // the period, 0 when the expression is not periodic
  const P = (base.length ? periodicity(e, x) : undefined) ?? S.Zero;
  const pv = known(P);
  if (pv !== 0) {
    const [loV, hiV] = [known(lo), known(hi)];
    if (!(Number.isFinite(loV) && Number.isFinite(hiV))) throw new NotImplementedError('inequalities: infinitely many zeros');
    // zeros may also repeat at fractions of the period (sin(x) + cos(x) vanishes every pi)
    const shifted = base.flatMap((r) => [1, 2, 3].map((q) => add(r, mul(q, P, Rational.of(1, 4)))));
    for (const r of [...base, ...shifted.filter((c) => Math.abs(numAt(e, x, c) ?? 1) < 1e-9)]) {
      const rv = known(r);
      const kmin = Math.ceil((loV - rv) / pv - 1e-9);
      const kmax = Math.floor((hiV - rv) / pv + 1e-9);
      for (let k = kmin; k <= kmax; k++) out.push(add(r, mul(k, P)));
    }
  } else out.push(...base);
  const uniq = new Map<string, Expr>();
  for (const r of out) {
    const [c1, c2] = [compareEndpoints(lo, r), compareEndpoints(r, hi)];
    if (c1 === undefined || c2 === undefined) throw new NotImplementedError('inequalities: zeros with parameters');
    if (c1 <= 0 && c2 <= 0) uniq.set(r.key, r);
  }
  return [...uniq.values()].sort(byValue);
}

/** The whole real line: SymPy's Reals or the equal Interval(-oo, oo). */
function isRealLine(domain: SetExpr): boolean {
  return domain === Reals || domain instanceof Interval && domain.isLeftUnbounded && domain.isRightUnbounded;
}

function bounds(domain: SetExpr): [Expr, Expr, boolean, boolean] {
  if (domain === Reals) return [S.NegativeInfinity, S.Infinity, true, true];
  if (domain instanceof Interval) return [domain.start, domain.end, domain.leftOpen, domain.rightOpen];
  throw new NotImplementedError('inequalities: unsupported domain');
}

function sample(a: Expr, b: Expr): Expr {
  const fa = a instanceof Special;
  const fb = b instanceof Special;
  if (fa && fb) return S.Zero;
  if (fa) return add(b, -1);
  if (fb) return add(a, 1);
  return mul(Rational.of(1, 2), add(a, b));
}

/**
 * Solve f(x) op 0 over a real domain by sign analysis between zeros and
 * poles. Returns the solution set.
 */
/** First Abs(a) in e whose argument depends on x. */
function findAbs(e: Expr, x: Sym): Expr | undefined {
  if (e instanceof Fn && e.name === 'abs' && first(e.args).has(x)) return e;
  for (const a of e.args) {
    const r = findAbs(a, x);
    if (r) return r;
  }
  return undefined;
}

/** The zeros of the denominators of e (where e is undefined). */
function denominatorZeros(e: Expr, x: Sym, domain: SetExpr): SetExpr {
  const dens: Expr[] = [];
  const walk = (u: Expr) => {
    if (u instanceof Pow && u.exp instanceof Rational && u.exp.isNegative && u.base.has(x)) dens.push(u.base);
    u.args.forEach(walk);
  };
  walk(e);
  return union(...dens.map((d) => solveSign(d, 'Eq', x, domain)));
}

function solveSign(input: Expr, op: RelOp, x: Sym, domain: SetExpr): SetExpr {
  const f0 = mapBottomUp(input, (term) => term instanceof Pow && term.exp.equals(S.Half)
    && term.base instanceof Pow && term.base.exp.equals(S.Two)
    && isReal(xreplace(term.base.base, [[x, new Dummy('x', { real: true })]])) === true
    ? fn('abs', [term.base.base]) : term);
  if (domain === EmptySet) return EmptySet;
  if (domain instanceof SetOp && domain.op === 'Union') return union(...domain.args.map((part) => solveSign(f0, op, x, part)));
  if (domain instanceof FiniteSet) return finiteSet(...domain.args.filter((p) => {
    const v = numAt(f0, x, p);
    return v !== undefined && (op === 'Eq' ? v === 0 : holds(op, v));
  }));
  if (domain === Integers || domain instanceof Range) return intersection(solveSign(f0, op, x, Reals), domain);
  // SymPy: solving an inequality with parameters is not implemented
  if ([...f0.freeSymbols()].filter((s) => s instanceof Sym).some((t) => t.key !== x.key)) throw new NotImplementedError('inequalities: the expression has parameters');
  // SymPy restricts an ordered comparison to the zeros of its imaginary part.
  if (op !== 'Eq' && op !== 'Ne' && f0.has(S.I)) {
    const real = new Dummy('real', { real: true });
    const imaginary = xreplace(asRealImag(expandMul(xreplace(f0, [[x, real]])))[1], [[real, x]]);
    if (!imaginary.equals(S.Zero)) {
      if (!imaginary.has(x)) throw new TypeError('Nonreal ordering');
      const [lo, hi] = bounds(domain);
      const candidates = realZeros(imaginary, x, lo, hi);
      return intersection(finiteSet(...candidates.filter((point) => {
        const value = numAt(f0, x, point);
        return value !== undefined && holds(op, value);
      })), domain);
    }
  }
  // a finite real expression plus oo or -oo has the sign of the infinity (SymPy: x < oo is True for a real x)
  if (f0 instanceof Add) {
    const inf = f0.args.find((a) => a instanceof Special);
    if (inf instanceof Special && (inf.name === 'oo' || inf.name === '-oo') && !f0.args.some((a) => a !== inf && some(a, (t) => t instanceof Special))) {
      return op !== 'Eq' && holds(op, inf.name === 'oo' ? Infinity : -Infinity) ? domain : EmptySet;
    }
  }
  const trigParts = f0 instanceof Add ? f0.args : [f0];
  const trigTerms = trigParts.filter((part) => part.has(x));
  if (trigTerms.length === 1) {
    const dependent = first(trigTerms);
    const factors = dependent instanceof Mul ? dependent.args : [dependent];
    const trig = factors.find((a) => a instanceof Fn && (a.name === 'sin' || a.name === 'cos') && a.has(x));
    if (trig && factors.filter((a) => a.has(x)).length === 1) {
      const amplitude = realValue(mul(...factors.filter((a) => a !== trig)));
      const offset = realValue(add(...trigParts.filter((a) => a !== dependent)));
      if (amplitude !== undefined && offset !== undefined && Math.abs(offset) > Math.abs(amplitude)) {
        return op !== 'Eq' && holds(op, offset) ? domain : EmptySet;
      }
    }
  }
  // Abs(a): split into the cases a >= 0 and a < 0 (SymPy reduce_abs_inequality)
  const ab = findAbs(f0, x);
  if (ab) {
    const a = first(ab.args);
    const pos = intersection(solveSign(a, 'Ge', x, domain), solveSign(xreplace(f0, [[ab, a]]), op, x, domain));
    const neg = intersection(solveSign(a, 'Lt', x, domain), solveSign(xreplace(f0, [[ab, mul(-1, a)]]), op, x, domain));
    // the replacement may cancel a denominator (x/Abs(x) is 1 for x >= 0): its zeros stay excluded
    return minus(union(pos, neg), denominatorZeros(f0, x, domain));
  }
  const rational = mapBottomUp(f0, (term) => {
    if (!(term instanceof Fn)) return term;
    const u = first(term.args);
    if (term.name === 'tan') return mul(fn('sin', [u]), pow(fn('cos', [u]), -1));
    if (term.name === 'cot') return mul(fn('cos', [u]), pow(fn('sin', [u]), -1));
    if (term.name === 'sec') return pow(fn('cos', [u]), -1);
    if (term.name === 'csc') return pow(fn('sin', [u]), -1);
    return term;
  });
  const f = cancel(rational);
  const excluded = denominatorZeros(f0, x, domain);
  // a constant (a case of an Abs split, say): the whole domain or nothing
  if (!f.has(x)) {
    const v = realValue(f);
    return v !== undefined && (op === 'Eq' ? v === 0 : holds(op, v)) ? minus(domain, excluded) : EmptySet;
  }
  const [num, den] = fraction(f);
  let dom = domain;
  if (domain === Reals) {
    const P = periodicity(f0, x);
    if (P && !(P instanceof Rational && P.isZero)) dom = interval(0, P, false, true);
  }
  const [lo, hi, lOpen, rOpen] = bounds(dom);
  const zeros = realZeros(num, x, lo, hi);
  const poles = realZeros(den, x, lo, hi);
  const radicands = new Map<string, Expr>();
  const logArguments = new Map<string, Expr>();
  some(f, (term) => {
    if (term instanceof Fn && term.name === 'log' && term.has(x)) {
      const argument = first(term.args);
      logArguments.set(argument.key, argument);
    }
    if (term instanceof Fn && ['asin', 'acos'].includes(term.name) && term.has(x)) {
      const u = first(term.args);
      for (const endpoint of [add(u, -1), add(u, 1)]) radicands.set(endpoint.key, endpoint);
    }
    if (term instanceof Pow && term.exp instanceof Rational && term.exp.q % 2n === 0n && term.base.has(x)) {
      radicands.set(term.base.key, term.base);
    }
    return false;
  });
  for (const argument of logArguments.values()) poles.push(...realZeros(argument, x, lo, hi));
  const boundaries = [...radicands.values()].flatMap((argument) => realZeros(argument, x, lo, hi));
  if (op === 'Eq') return minus(intersection(finiteSet(...zeros.filter((z) => !poles.some((p) => p.key === z.key))), dom), excluded);
  const pts = [...zeros, ...poles, ...boundaries].sort(byValue).filter((p, i, a) => i === 0 || p.key !== at(a, i - 1).key);
  const edges = [lo, ...pts.filter((p) => compareEndpoints(p, lo) !== 0 && compareEndpoints(p, hi) !== 0), hi];
  const parts: SetExpr[] = [];
  for (let i = 0; i + 1 < edges.length; i++) {
    const [l, r] = [at(edges, i), at(edges, i + 1)];
    const v = numAt(f, x, sample(l, r));
    if (v !== undefined && holds(op, v)) parts.push(interval(l, r, true, true));
  }
  // the zeros and the finite ends of the domain (a strict inequality may hold at a closed end)
  for (const z of edges) {
    if (z instanceof Special) continue;
    if (poles.some((p) => p.key === z.key)) continue;
    const v = zeros.some((root) => root.equals(z)) ? 0 : numAt(f, x, z);
    if (v !== undefined && holds(op, Math.abs(v) < 1e-12 ? 0 : v)) parts.push(finiteSet(z));
  }
  const region = union(...parts);
  const res = minus(dom === Reals ? region : intersection(region, interval(lo, hi, lOpen, rOpen)), excluded);
  return dom !== domain && res.equals(dom) ? domain : res;
}

/** Express a single puncture as an excluded point. */
function inequalityAsRelational(set: SetExpr, x: Sym): Expr {
  if (!(set instanceof SetOp) || set.op !== 'Union') return asRelational(set, x);
  if (set.args.length !== 2) return orB(...set.args.map((part) => asRelational(part, x)));
  const [a, b] = [first(set.args), at(set.args, 1)];
  if (!(a instanceof Interval) || !(b instanceof Interval)) return asRelational(set, x);
  if (!a.rightOpen || !b.leftOpen || !a.end.equals(b.start)) return asRelational(set, x);
  const lower = a.leftOpen ? Gt(x, a.start) : Ge(x, a.start);
  const upper = b.rightOpen ? Lt(x, b.end) : Le(x, b.end);
  return and(lower, upper, Ne(x, a.end));
}

/** SymPy solve_univariate_inequality. */
export function solveUnivariateInequality(
  relIn: ExprLike,
  x: Sym,
  opts: { relational?: boolean; domain?: SetExpr } = {},
): Expr {
  const rel = sympify(relIn);
  if (rel instanceof BoolAtom) return opts.relational === false ? rel.value ? opts.domain ?? Reals : EmptySet : rel;
  if (!(rel instanceof Rel)) throw new TypeError('solve_univariate_inequality: relational expected');
  const domain = opts.domain ?? Reals;
  // A sign chart cannot decide the order of an endpoint by a rounded cancellation.
  for (const bound of [rel.lhs, rel.rhs]) {
    if (!(bound instanceof Add) || bound.freeSymbols().size || isZero(bound) !== undefined) continue;
    const magnitude = bound.args.reduce((sum, term) => sum + Math.abs(Number(realValue(term))), 0);
    if (Number.isFinite(magnitude) && Math.abs(Number(realValue(bound))) <= bound.args.length * Number.EPSILON * magnitude) {
      throw new NotImplementedError('inequalities: cannot certify the sign of the constant endpoint');
    }
  }
  const [numerator, denominator] = fraction(rel.lhs);
  if (opts.relational !== false && domain === Reals && denominator.equals(x) && isPositive(x) === true && !numerator.has(x) && rel.rhs instanceof Rational && !rel.rhs.isZero) {
    const endpoint = mul(numerator, pow(rel.rhs, -1));
    const reversed: Record<RelOp, RelOp> = { Gt: 'Lt', Ge: 'Le', Lt: 'Gt', Le: 'Ge', Eq: 'Eq', Ne: 'Ne' };
    return relFn[rel.rhs.isNegative ? reversed[rel.op] : rel.op](endpoint, x);
  }
  const logarithm = rel.lhs;
  if (logarithm instanceof Fn && logarithm.name === 'log' && first(logarithm.args).equals(x) && !rel.rhs.has(x) && isReal(rel.rhs) === true) {
    const endpoint = pow(S.E, rel.rhs);
    const positive = interval(0, S.Infinity, true, true);
    const candidates = rel.op === 'Lt' || rel.op === 'Le' ? interval(0, endpoint, true, rel.op === 'Lt')
      : rel.op === 'Gt' || rel.op === 'Ge' ? interval(endpoint, S.Infinity, rel.op === 'Gt', true)
      : rel.op === 'Eq' ? finiteSet(endpoint) : complement(positive, finiteSet(endpoint));
    const solution = domain === Reals ? candidates : intersection(candidates, domain);
    return opts.relational === false ? solution : asRelational(solution, x);
  }
  const s = minus(solveSign(add(rel.lhs, mul(-1, rel.rhs)), rel.op, x, domain), union(denominatorZeros(rel.lhs, x, Reals), denominatorZeros(rel.rhs, x, Reals)));
  return opts.relational === false ? s : inequalityAsRelational(s, x);
}

/** SymPy solve_poly_inequality: a list of intervals. */
export function solvePolyInequality(poly: Poly, rel: string): SetExpr[] {
  if (poly.isGround) {
    const v = realValue(poly.asExpr());
    if (v === undefined) throw new NotImplementedError('solvePolyInequality: a real coefficient is required');
    const ops: Readonly<Record<string, RelOp | undefined>> = { '==': 'Eq', '!=': 'Ne', '>': 'Gt', '>=': 'Ge', '<': 'Lt', '<=': 'Le' };
    const op = ops[rel];
    if (op === undefined) throw new TypeError(`solve_poly_inequality: '${rel}' is not a valid relation`);
    return [(op === 'Eq' ? v === 0 : holds(op, v)) ? Reals : EmptySet];
  }
  const roots = poly.realRoots();
  const reals: [Expr, number][] = [];
  for (const r of roots) {
    const last = reals[reals.length - 1];
    if (last && last[0].key === r.key) last[1]++;
    else reals.push([r, 1]);
  }
  const out: SetExpr[] = [];
  if (rel === '==') {
    for (const [r] of reals) out.push(finiteSet(r));
    return out;
  }
  if (rel === '!=') {
    let left: Expr = S.NegativeInfinity;
    for (const [right] of [...reals, [S.Infinity, 1] as [Expr, number]]) {
      out.push(interval(left, right, true, true));
      left = right;
    }
    return out;
  }
  const lc = poly.LC();
  let sign = lc instanceof Rational && lc.isPositive ? 1 : -1;
  let eqSign = 0;
  let equal = false;
  if (rel === '>') eqSign = 1;
  else if (rel === '<') eqSign = -1;
  else if (rel === '>=') [eqSign, equal] = [1, true];
  else if (rel === '<=') [eqSign, equal] = [-1, true];
  else throw new TypeError(`solve_poly_inequality: '${rel}' is not a valid relation`);
  let right: Expr = S.Infinity;
  let rightOpen = true;
  for (const [left, m] of [...reals].reverse()) {
    if (m % 2) {
      if (sign === eqSign) out.unshift(interval(left, right, !equal, rightOpen));
      [sign, right, rightOpen] = [-sign, left, !equal];
    } else if (sign === eqSign && !equal) {
      out.unshift(interval(left, right, true, rightOpen));
      [right, rightOpen] = [left, true];
    } else if (sign !== eqSign && equal) out.unshift(interval(left, left));
  }
  if (sign === eqSign) out.unshift(interval(S.NegativeInfinity, right, true, rightOpen));
  return out;
}

/** SymPy solve_rational_inequalities: OR over AND-lists of ((numer, denom), rel). */
export function solveRationalInequalities(eqs: readonly (readonly [[Poly, Poly], string][])[]): SetExpr {
  let result: SetExpr = EmptySet;
  for (const group of eqs) {
    if (!group.length) continue;
    let global: SetExpr[] = [Reals];
    for (const [[numer, denom], rel] of group) {
      const ni = solvePolyInequality(numer.mul(denom), rel);
      const di = solvePolyInequality(denom, '==');
      let next: SetExpr[] = [];
      for (const a of ni) for (const g of global) {
        const i = intersection(a, g);
        if (i !== EmptySet) next.push(i);
      }
      global = next;
      next = [];
      for (let g of global) {
        for (const d of di) g = complement(g, d);
        if (g !== EmptySet) next.push(g);
      }
      global = next;
      if (!global.length) break;
    }
    for (const g of global) result = union(result, g);
  }
  return result;
}

/** Union of the solution sets of polynomial inequalities. */
export function solvePolyInequalities(polys: readonly (readonly [Poly, string])[]): SetExpr {
  return union(...polys.flatMap(([p, r]) => solvePolyInequality(p, r)));
}

/** OR of AND groups of rational inequalities, optionally as a set. */
export function reduceRationalInequalities(exprs: readonly (readonly (ExprLike | readonly [ExprLike, string])[])[], gen: Sym, relational = true): Expr {
  const relation = (e: ExprLike | readonly [ExprLike, string]): Expr => {
    const isPair = (a: ExprLike | readonly [ExprLike, string]): a is readonly [ExprLike, string] => Array.isArray(a);
    if (!isPair(e)) return sympify(e);
    const [f, op] = e;
    const constructors: Readonly<Record<string, (a: ExprLike, b: ExprLike) => Expr>> = { '>': Gt, '>=': Ge, '<': Lt, '<=': Le, '==': Eq, '!=': Ne };
    const make = constructors[op];
    if (make === undefined) throw new TypeError(`reduceRationalInequalities: invalid relation ${op}`);
    return make(f, 0);
  };
  const result = orB(...exprs.map((group) => reduceInequalities(group.map(relation), [gen])));
  return relational ? result : asSet(result);
}

/** SymPy reduce_inequalities: a relational description of the solutions. */
export function reduceInequalities(ineqsIn: readonly ExprLike[] | ExprLike, symbols: readonly Sym[] = []): Expr {
  const ineqs = (isExprList(ineqsIn) ? ineqsIn : [ineqsIn]).map((e) => sympify(e));
  const rels: Expr[] = ineqs.map((e) => (e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp ? e : Eq(e, 0)));
  const gens = symbols.length ? symbols : ([...new Map(rels.flatMap((r) => [...r.freeSymbols()].filter((s) => s instanceof Sym)).map((s) => [s.key, s])).values()] as Sym[]);
  const parts: Expr[] = [];
  const byGen = new Map<string, Rel[]>();
  for (const r of rels) {
    if (!(r instanceof Rel)) {
      parts.push(r);
      continue;
    }
    const fs = [...r.freeSymbols()].filter((s) => s instanceof Sym).filter((s) => gens.some((g) => g.key === s.key));
    if (fs.length !== 1) throw new NotImplementedError('reduce_inequalities: multivariate inequality');
    const g = first(fs);
    const list = byGen.get(g.key);
    if (list) list.push(r);
    else byGen.set(g.key, [r]);
  }
  for (const [k, rs] of byGen) {
    const g = defined(gens.find((s) => s.key === k), 'generator');
    let set: SetExpr = Reals;
    const univariate: Rel[] = [];
    for (const r of rs) {
      if ([...r.freeSymbols()].some((symbol) => symbol instanceof Sym && symbol.key !== g.key)
        || some(r, (term) => term.kind === 'Integral' || term.kind === 'Concrete')) {
        parts.push(linearInequality(r, g));
        continue;
      }
      univariate.push(r);
      const solution = cast(solveUnivariateInequality(r, g, { relational: false }), SetExpr);
      set = set === Reals ? solution : intersection(set, solution);
    }
    if (univariate.length) {
      parts.push(set === Reals && univariate.every((r) => {
        const period = periodicity(add(r.lhs, mul(-1, r.rhs)), g);
        return period !== undefined && !period.equals(S.Zero);
      }) ? S.true : inequalityAsRelational(set, g));
    }
  }
  return and(...parts);
}

/** a*x + b op 0 with symbolic b: x op' -b/a, plus the infinite bound. */
function linearInequality(r: Rel, x: Sym): Expr {
  const f = add(r.lhs, mul(-1, r.rhs));
  const terms = f instanceof Add ? f.args : [f];
  const hasVariable = (term: Expr): boolean => [...term.freeSymbols()].some((symbol) => symbol.equals(x));
  const dependent = terms.filter(hasVariable);
  const p = Poly.from(add(...dependent), [x]);
  if (p.degree() !== 1) throw new NotImplementedError('reduce_inequalities: nonlinear inequality with parameters');
  const a = p.LC();
  const b = add(p.TC(), ...terms.filter((term) => !hasVariable(term)));
  const sol = mul(-1, b, pow(a, -1));
  const av = realValue(a);
  // SymPy leaves the inequality as it is when the sign of the coefficient is unknown
  if (av === undefined) return r;
  const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
  const op = av < 0 ? flip[r.op] : r.op;
  const main = relFn[op](x, sol);
  if (!some(b, (term) => term instanceof ExtensionExpr || term.kind === 'Integral' || term.kind === 'Concrete')) {
    if (op === 'Ge') return and(main, Lt(x, S.Infinity));
    if (op === 'Le') return and(main, Lt(S.NegativeInfinity, x));
  }
  return main;
}

/**
 * Solves an equation or inequality in one variable and returns the set of its
 * solutions in `domain`: a finite set, an interval, a union, an `ImageSet` for
 * periodic solutions, or a `ConditionSet` when the solutions cannot be found.
 *
 * @param fIn - The expression equal to zero, an `Eq`, or a relation.
 * @param symbol - The unknown; by default the only free symbol.
 * @param domain - The set the solutions are taken from (`Complexes` by default).
 * @returns The solution set.
 * @see SymPy `sympy.solvers.solveset.solveset`
 * @example
 * ```ts
 * import { ex, Reals, solveset, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * solveset(ex`x**2 - 1`, x); // => {-1, 1}
 * solveset(ex`exp(x) - 1`, x); // => ImageSet(Lambda(_n, 2*_n*I*pi), Integers)
 * solveset(ex`exp(x) - 1`, x, Reals); // => {0}
 * solveset(ex`x**2 > 4`, x, Reals); // => Union(Interval.open(-oo, -2), Interval.open(2, oo))
 * ```
 */
export function solveset(fIn: ExprLike, symbol?: ExprLike, domain: SetExpr = Complexes): SetExpr {
  const f = sympify(fIn);
  if (!(domain instanceof SetExpr)) throw new TypeError('solveset: a set domain is required');
  if (symbol instanceof SetExpr) throw new TypeError('solveset: expected a scalar unknown');
  const free = [...f.freeSymbols()];
  if (symbol === undefined && free.length > 1) throw new RangeError('solveset: specify an unknown for multivariate expressions');
  const target = symbol === undefined ? free[0] : sympify(symbol);
  if (!(target instanceof Sym)) {
    if (target === undefined) return f === S.true || f.equals(S.Zero) ? domain : EmptySet;
    const variable = new Dummy('x');
    // Number._eval_subs also replaces the additive inverse of a numeric target.
    const recast = target instanceof Rational && !target.isZero ? xreplace(f, [[target, variable], [target.neg(), variable.neg()]]) : subs(f, [[target, variable]]);
    const result = solveset(recast, variable, domain);
    return cast(xreplace(result, [[variable, target]]), SetExpr);
  }
  const x = target;
  // Interval(-oo, oo) equals Reals in SymPy: solve over the real line
  if (domain !== Reals && isRealLine(domain)) return solveset(f, x, Reals);
  // SymPy solves over a real domain with a real dummy for the unknown: the equation is evaluated for a real
  // unknown (sqrt(x**2) is Abs(x))
  if ((domain === Reals || domain instanceof Interval) && isReal(x) !== true && !(f instanceof BoolAtom)) {
    const real = new Dummy('R', { real: true });
    // Keep a symbolic base intact when a real exponent would distribute over its factors.
    if (f instanceof Add && f.args.some((term) => term instanceof Pow && term.base instanceof Mul && term.exp.equals(x) && isPositive(term.base) === true)) {
      const isolated = invertExponential(f, x, domain);
      if (isolated !== undefined) return isolated;
    }
    const evaluated = xreplace(xreplace(f, [[x, real]]), [[real, x]]);
    if (!evaluated.equals(f)) return solveset(evaluated, x, domain);
  }
  // a decided condition holds everywhere or nowhere (SymPy solveset(True, x) is the domain)
  if (f instanceof BoolAtom) return f.value ? domain : EmptySet;
  if (f instanceof Rel && f.op !== 'Eq') {
    // SymPy keeps an inequality or x != a over the complex numbers as a ConditionSet
    // and so does an inequality with parameters
    if ((!(domain instanceof Range) && isSubset(domain, Reals) !== true) || [...f.freeSymbols()].filter((s) => s instanceof Sym).some((t) => t.key !== x.key)) return new ConditionSet(x, f, domain);
    const realDomain = domain === Integers || domain instanceof Range ? Reals : domain;
    const residual = piecewiseFold(add(f.lhs, mul(-1, f.rhs)));
    const solution = residual instanceof Piecewise
      ? solvePiecewise(residual, x, realDomain, (expression, where) => solveSign(expression, f.op, x, where))
      : solveSign(residual, f.op, x, realDomain);
    const excluded = union(denominatorZeros(f.lhs, x, realDomain), denominatorZeros(f.rhs, x, realDomain));
    return intersection(minus(solution, excluded), domain);
  }
  if (domain instanceof SetOp && domain.op === 'Union') return union(...domain.args.map((part) => solveset(f, x, part)));
  if (domain instanceof FiniteSet) {
    const residual = f instanceof Rel ? add(f.lhs, mul(-1, f.rhs)) : f;
    const condition = Eq(residual, 0);
    return union(...domain.args.map((point) => {
      const atPoint = xreplace(condition, [[x, point]]);
      return atPoint === S.true ? finiteSet(point) : atPoint === S.false ? EmptySet : new ConditionSet(x, condition, finiteSet(point));
    }));
  }
  const residual = f instanceof Rel ? add(f.lhs, mul(-1, f.rhs)) : f;
  const g = piecewiseFold(domain === Complexes ? residual : mapBottomUp(residual, (term) => {
    if (!(term instanceof Fn) || (term.name !== 'Min' && term.name !== 'Max') || !term.has(x)) return term;
    const min = term.name === 'Min';
    return piecewise(...term.args.map((argument) => [
      argument,
      and(...term.args.filter((other) => other !== argument).map((other) => min ? Le(argument, other) : Ge(argument, other))),
    ] as const));
  }));
  if (!g.has(x)) return g instanceof Rational && g.isZero ? domain : EmptySet;
  if (domain === Complexes && some(g, (e) => e instanceof Fn && ['abs', 'Min', 'Max'].includes(e.name) && e.has(x))) throw new RangeError('solveset: a real domain is required');
  let algebraic: SetExpr | undefined;
  try {
    // a Piecewise: each piece on the part of the domain where its condition holds first (SymPy _solveset)
    if (g instanceof Piecewise) {
      if (domain === Complexes && g.pairs.some(([, condition]) => some(condition, (a) => a instanceof Rel && a.op !== 'Eq' && a.op !== 'Ne'))) {
        return new ConditionSet(x, Eq(g, 0), domain);
      }
      return solvePiecewise(g, x, domain, (expression, where) => solveset(expression, x, where));
    }
    if (g instanceof Fn && g.name === 'sign') return solveset(first(g.args), x, domain);
    if (g instanceof Mul && !some(g, (factor) => factor instanceof Pow && isNegative(factor.exp) === true)) {
      const dependent = g.args.filter((factor) => factor.has(x));
      if (dependent.length > 1) return union(...dependent.map((factor) => solveset(factor, x, domain)));
    }
    // periodic equations: the solutions in one period plus multiples of the period (SymPy ImageSet)
    if (g instanceof Fn && g.name === 'sin') {
      const argument = first(g.args);
      if (argument instanceof Fn && argument.name === 'abs') return solveset(fn('sin', argument.args), x, domain);
      if (domain === Complexes && argument instanceof Pow && argument.base.equals(S.E) && argument.exp.has(x)) return new ConditionSet(x, Eq(g, 0), domain);
    }
    if (some(g, (e) => e instanceof Fn && (e.name === 'sin' || e.name === 'cos') && e.has(x))) {
      const simplified = trigsimp(g);
      if (!simplified.equals(g)) return solveset(simplified, x, domain);
    }
    if (domain === Reals || domain instanceof Interval) {
      const absolute = invertAbsolute(g, x, domain);
      if (absolute !== undefined) return absolute;
    }
    const modular = solveModular(g, x, domain);
    if (modular !== undefined) return modular;
    if (domain instanceof Interval) {
      const preimage = boundedCosinePreimage(g, x, domain);
      if (preimage !== undefined) return preimage;
    }
    const periodic = periodicSolutions(g, x, domain);
    if (periodic) return periodic;
    if (domain === Complexes) {
      const ex = complexExpSolutions(g, x) ?? complexExpPolynomial(g, x);
      if (ex) return ex;
    }
    algebraic = solvesetAlgebraic(g, x, domain);
    if (algebraic !== EmptySet) return algebraic;
  } catch {
    algebraic = undefined;
  }
  if (domain === Complexes && g instanceof Add && some(g, (term) => term instanceof Fn && term.has(x))) {
    const product = factor(g);
    if (product instanceof Mul && product.args.filter((a) => a.has(x)).length > 1 && !some(product, (a) => a instanceof Pow && isNegative(a.exp) === true)) {
      return union(...product.args.filter((a) => a.has(x)).map((a) => solveset(a, x, domain)));
    }
  }
  const hyperbolicHeads = ['sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch'];
  if (some(g, (term) => term instanceof Fn && hyperbolicHeads.includes(term.name))) {
    const hyperbolic = g.rewrite('exp', { pattern: hyperbolicHeads });
    const solution = solveset(hyperbolic, x, domain);
    if (!(solution instanceof ConditionSet)) return solution;
  }
  if (domain === Reals || domain instanceof Interval) {
    const radicals = solveRadicals(g, x, domain);
    if (radicals !== undefined) return radicals;
  }
  return algebraic ?? new ConditionSet(x, Eq(g, 0), domain);
}

/** Solve an affine integer congruence with a constant modulus and residue. */
function solveModular(g: Expr, x: Sym, domain: SetExpr): SetExpr | undefined {
  if (domain !== Integers && !(domain instanceof Range)) return undefined;
  const terms = g instanceof Add ? g.args : [g];
  const dependent = terms.filter((t) => t.has(x));
  if (dependent.length !== 1) return undefined;
  const term = first(dependent);
  const factors = term instanceof Mul ? term.args : [term];
  const modulusTerm = factors.find((a) => a instanceof ExtensionExpr && a.name === 'Mod' && a.has(x));
  if (!modulusTerm || factors.filter((a) => a.has(x)).length !== 1) return undefined;
  const [argument, modulus] = [first(modulusTerm.args), at(modulusTerm.args, 1)];
  if (!(modulus instanceof Rational) || !modulus.isInteger || modulus.isZero) return undefined;
  const residue = mul(-1, add(...terms.filter((t) => t !== term)), pow(mul(...factors.filter((a) => a !== modulusTerm)), -1));
  const p = Poly.from(argument, [x]);
  const [a, b] = [p.LC(), p.TC()];
  if (p.degree() !== 1 || !(a instanceof Rational) || !a.isInteger || !(b instanceof Rational) || !b.isInteger) return undefined;
  if (!(residue instanceof Rational)) return residue.freeSymbols().size === 0 && isReal(residue) === false ? EmptySet : undefined;
  if (!residue.isInteger || (modulus.p > 0n ? residue.p < 0n || residue.p >= modulus.p : residue.p > 0n || residue.p <= modulus.p)) return EmptySet;
  const [inverse, , gcd] = igcdex(a.p, modulus.p);
  const target = residue.p - b.p;
  if (target % gcd !== 0n) return EmptySet;
  const step = (modulus.p < 0n ? -modulus.p : modulus.p) / gcd;
  const solution = inverse * (target / gcd) % step;
  const n = new Dummy('n', { integer: true });
  return intersection(imageSet(n, add((solution + step) % step, mul(step, n)), Integers), domain);
}

/** Clear real radicals and check the resulting candidates in the input equation. */
function solveRadicals(g: Expr, x: Sym, domain: SetExpr): SetExpr | undefined {
  if ([...g.freeSymbols()].some((symbol) => !symbol.equals(x))) return undefined;
  const radicals = new Map<string, Pow>();
  some(g, (term) => {
    if (term instanceof Pow && term.exp.equals(S.Half) && term.base.has(x)) radicals.set(term.key, term);
    return false;
  });
  const roots = [...radicals.values()];
  if (roots.length < 2 || roots.length > 3 || roots.some((r) => roots.some((s) => r.base.has(s)))) return undefined;
  try {
    const variables = roots.map(() => new Dummy('r'));
    let cleared = xreplace(g, roots.map((r, i): [Expr, Expr] => [r, at(variables, i)]));
    for (const [i, root] of roots.entries()) {
      const variable = at(variables, i);
      const p = Poly.from(cleared, [variable]);
      let even: Expr = S.Zero, odd: Expr = S.Zero;
      for (const [powers, coefficient] of p.terms()) {
        const degree = at(powers, 0);
        const term = mul(coefficient, pow(root.base, Math.floor(degree / 2)));
        if (degree % 2 === 0) even = add(even, term);
        else odd = add(odd, term);
      }
      cleared = expandMul(add(pow(even, 2), mul(-1, root.base, pow(odd, 2))));
    }
    if (cleared.equals(S.Zero)) return new ConditionSet(x, Eq(g, 0), domain);
    const candidates = solve(cleared, x);
    const valid: Expr[] = [];
    for (const point of candidates) {
      if (containsQ(domain, point) !== true) continue;
      const value = xreplace(g, [[x, point]]);
      const numeric = value.equals(S.Zero) ? 0 : realValue(value);
      if (numeric !== undefined && Math.abs(numeric) < 1e-12) valid.push(point);
    }
    return finiteSet(...valid);
  } catch {
    return undefined;
  }
}

/** The set where a condition on x holds. */
function conditionSet(c: Expr, x: Sym, domain: SetExpr): SetExpr {
  if (c instanceof BoolOp && (c.op === 'And' || c.op === 'Or')) {
    const parts = c.args.map((a) => conditionSet(a, x, domain));
    return c.op === 'And' ? intersection(...parts) : union(...parts);
  }
  if (c instanceof Rel && c.op === 'Ne') return complement(domain, solveset(Eq(c.lhs, c.rhs), x, domain));
  return solveset(c, x, domain);
}

/** The zeros of a Piecewise: those of each piece where its condition holds and no earlier one does. */
function solvePiecewise(
  g: Piecewise, x: Sym, domain: SetExpr, solveBranch: (expression: Expr, where: SetExpr) => SetExpr,
): SetExpr {
  let remaining = domain;
  const parts: SetExpr[] = [];
  for (const [e, c] of g.pairs) {
    const where = c === S.true ? remaining : intersection(remaining, conditionSet(c, x, domain));
    if (where !== EmptySet) parts.push(solveBranch(e, where));
    remaining = complement(remaining, where);
  }
  return union(...parts);
}

/** SymPy _invert_real for a function with an inverse (erf -> erfinv): a*f(u) + b = 0 becomes u = f^-1(-b/a), or undefined. */
const INVERSES: Readonly<Record<string, FnName>> = { erf: 'erfinv', erfc: 'erfcinv', erfinv: 'erf', erfcinv: 'erfc', sinh: 'asinh', cosh: 'acosh', tanh: 'atanh', coth: 'acoth', sech: 'asech', csch: 'acsch' };
function invertReal(g: Expr, x: Sym, domain: SetExpr): Expr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dep = terms.filter((t) => t.has(x));
  if (dep.length !== 1) return undefined;
  const t = first(dep);
  const fs = t instanceof Mul ? t.args : [t];
  const f = fs.find((h): h is Fn => h instanceof Fn && (h.name === 'atan2' || h.name in INVERSES) && h.has(x));
  if (!f || fs.filter((h) => h.has(x)).length !== 1) return undefined;
  const a = mul(...fs.filter((h) => h !== f));
  const c = mul(-1, add(...terms.filter((u) => !u.has(x))), pow(a, -1));
  if (f.name === 'atan2') {
    const adjacent = at(f.args, 1);
    if (adjacent.has(x) || isPositive(adjacent) !== true) return undefined;
    const limit = mul(S.Half, S.Pi);
    const valid = containsQ(interval(mul(-1, limit), limit, true, true), c);
    if (valid === undefined) return new ConditionSet(x, Eq(g, 0), domain);
    return valid ? add(first(f.args), mul(-1, adjacent, fn('tan', [c]))) : S.One;
  }
  if (f.name.endsWith('h')) {
    const range = f.name === 'cosh' ? interval(1, S.Infinity) : f.name === 'tanh' ? interval(-1, 1, true, true) : f.name === 'coth' ? union(interval(S.NegativeInfinity, -1, true, true), interval(1, S.Infinity, true, true)) : f.name === 'sech' ? interval(0, 1, true, false) : f.name === 'csch' ? complement(Reals, finiteSet(0)) : Reals;
    const valid = containsQ(range, c);
    if (valid === undefined) return undefined;
    if (!valid) return S.One;
    const inverse = fn(defined(INVERSES[f.name]), [c]);
    const u = first(f.args);
    return f.name === 'cosh' || f.name === 'sech' ? mul(add(u, inverse), add(u, mul(-1, inverse))) : add(u, mul(-1, inverse));
  }
  return add(first(f.args), mul(-1, fn(defined(INVERSES[f.name]), [c])));
}

/** The real roots of a polynomial with parameters: SymPy keeps those known to be real and intersects the others with the Reals. */
function parametricRealRoots(num: Expr, den: Expr, x: Sym, original: Expr): SetExpr {
  const realPart = (xs: readonly Expr[]): SetExpr => {
    const reals = xs.filter((r) => isRealSym(r) && isReal(r) !== false && (isReal(r) === true || r.freeSymbols().size !== 0 || Number.isFinite(realValue(approximateRoots(r)))));
    const unknown = reals.filter((r) => isReal(r) !== true && realFact(r) !== true);
    return union(finiteSet(...reals.filter((r) => !unknown.includes(r))), unknown.length ? new SetOp('Intersection', [finiteSet(...unknown), Reals]) : EmptySet);
  };
  const roots = solve(num, x);
  // A principal Lambert W root does not enumerate all branches of a transcendental equation.
  if (roots.some((r) => some(r, (t) => t instanceof Fn && t.name === 'LambertW'))) return new ConditionSet(x, Eq(original, 0), Reals);
  const poles = den.has(x) ? realPart(solve(den, x)) : EmptySet;
  if (some(original, (term) => term instanceof Pow && term.base.has(x) && term.exp.equals(S.Half.neg()))) {
    return union(...roots.map((root) => {
      const base = realPart([root]);
      const solution = checksol(original, x, root) === true ? base : new ConditionSet(x, Eq(original, 0), base);
      return complement(solution, poles);
    }));
  }
  return complement(realPart(roots), poles);
}

/**
 * SymPy _invert_real for a*B**e + b = 0 with a parameter in c = -b/a and a
 * rational e = p/q:
 *   q even, p odd: B = t**(1/e) for t in {c} & [0, oo), an ImageSet over
 *                  that intersection (sqrt(x) = y gives x = y**2 for y >= 0);
 *   e an odd integer: B = real_root(c, e) = Abs(c)**(1/e)*sign(c).
 * B is then inverted for x; undefined for the other equations.
 */
function invertRealPower(g: Expr, x: Sym): SetExpr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dep = terms.filter((t) => t.has(x));
  if (dep.length !== 1) return undefined;
  const t0 = first(dep);
  const fs = t0 instanceof Mul ? t0.args : [t0];
  const F = fs.find((h) => h.has(x));
  if (!(F instanceof Pow) || !(F.exp instanceof Rational) || fs.filter((h) => h.has(x)).length !== 1) return undefined;
  const e = F.exp;
  const c = mul(-1, add(...terms.filter((u) => !u.has(x))), pow(mul(...fs.filter((h) => h !== F)), -1));
  if (c.freeSymbols().size === 0) return undefined;
  const B = F.base;
  if (e.q % 2n === 0n && e.p % 2n !== 0n) {
    // {c} & [0, oo) is {c} or empty when the sign of c is known
    // (B**k)**e: SymPy gives a ConditionSet with Abs-type solutions, not handled here
    if (B instanceof Pow) return undefined;
    const base = isNonNegative(c) === true ? finiteSet(c) : isNegative(c) === true ? EmptySet : new SetOp('Intersection', [finiteSet(c), interval(0, S.Infinity, false, true)]);
    const t = new Dummy('t');
    const sets = invertTo(B, pow(t, pow(e, -1)), x).map((r) => imageSet(x, xreplace(r, [[t, x]]), base));
    return sets.length === 1 ? first(sets) : new SetOp('Union', sets.sort((u, v) => compareKeys(sortKey(u), sortKey(v))));
  }
  if (B.equals(x) && e.equals(S.Two)) {
    if (isNegative(c) === true) return EmptySet;
    const root = pow(c, S.Half);
    const candidates = finiteSet(root.neg(), root);
    return realFact(root) === true ? candidates : new SetOp('Intersection', [candidates, Reals]);
  }
  if (!e.isInteger || e.p % 2n === 0n) return undefined;
  const sols = invertTo(B, realRoot(c, e.p), x);
  // real_root of a real c is real
  const realC = isReal(c) === true;
  const known = sols.filter((r) => isReal(r) === true || (realC && !r.has(S.I) && [...r.freeSymbols()].filter((s) => s instanceof Sym).every((u) => isReal(u) === true)));
  const unknown = sols.filter((r) => !known.includes(r));
  return union(finiteSet(...known), unknown.length ? new SetOp('Intersection', [finiteSet(...unknown), Reals]) : EmptySet);
}

/**
 * The solutions of B(x) = r by inverting B one operation at a time (SymPy
 * _invert_real for sums, products and powers of x), like x + 1 = r -> r - 1
 * and x**2 + 1 = r -> -sqrt(r - 1), sqrt(r - 1); NotImplementedError for the
 * others (SymPy's ConditionSet).
 */
function invertTo(B: Expr, r: Expr, x: Sym): Expr[] {
  if (B.key === x.key) return [r];
  if (B instanceof Add || B instanceof Mul) {
    const dep = B.args.filter((a) => a.has(x));
    const rest = B.args.filter((a) => !a.has(x));
    if (dep.length === 1 && rest.length) {
      const inner = first(dep);
      return invertTo(inner, B instanceof Add ? add(r, add(...rest).neg()) : mul(r, pow(mul(...rest), -1)), x);
    }
  }
  if (B instanceof Pow && B.exp instanceof Rational && B.exp.isInteger && B.exp.p > 1n) {
    const k = B.exp;
    if (k.p % 2n !== 0n) return invertTo(B.base, realRoot(r, k.p), x);
    const rt = pow(r, Rational.of(1n, k.p));
    return [...invertTo(B.base, rt, x), ...invertTo(B.base, mul(-1, rt), x)];
  }
  // SymPy: a ConditionSet
  throw new NotImplementedError('solveset: the equation is not inverted');
}

/** SymPy real_root(c, n) for an odd n: Abs(c)**(1/n)*sign(c). */
const realRoot = (c: Expr, n: bigint): Expr => mul(pow(fn('abs', [c]), Rational.of(1n, n)), fn('sign', [c]));

/** Enforce the principal branch when exponentiating an equation between logarithms. */
function logarithmicPreimage(equation: Add, x: Sym): SetExpr | undefined {
  const positive = equation.args.find((t): t is Fn => t instanceof Fn && t.name === 'log' && t.has(x));
  if (!positive) return undefined;
  const argument = first(positive.args);
  if (argument instanceof Pow && argument.base.equals(x) && !argument.exp.has(x)) {
    const exponent = mul(argument.exp, log(x));
    if (add(...equation.args.filter((t) => t !== positive), exponent).equals(S.Zero)) {
      const imaginary = fn('im', [exponent]);
      return new ConditionSet(x, and(Lt(S.Pi.neg(), imaginary), Le(imaginary, S.Pi)), complement(Reals, finiteSet(0)));
    }
  }
  const negative = equation.args.find((t) => t instanceof Mul && t.args.length === 2 && t.args.some((a) => a.equals(-1)) && t.args.some((a) => a instanceof Fn && a.name === 'log' && a.has(x)));
  if (!(negative instanceof Mul)) return undefined;
  const offset = add(...equation.args.filter((t) => t !== positive && t !== negative));
  if (!offset.freeSymbols().size || offset.has(x)) return undefined;
  const other = first(cast(defined(negative.args.find((a) => a instanceof Fn)), Fn).args);
  const ratio = cancel(mul(argument, pow(other, -1)));
  const [numerator] = fraction(cancel(add(mul(ratio, pow(S.E, offset)), -1)));
  const candidates = solveset(numerator, x, Reals);
  const excluded = union(...[...denoms(equation, x), other].map((d) => solveset(d, x, Reals)));
  const imaginary = fn('im', [add(log(other), offset.neg())]);
  return new ConditionSet(x, and(Lt(S.Pi.neg(), imaginary), Le(imaginary, S.Pi)), complement(candidates, excluded));
}

/** Intersect the periodic cosine preimages with the monotone image of the interval. */
function boundedCosinePreimage(g: Expr, x: Sym, domain: Interval): SetExpr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dependent = terms.filter((t) => t.has(x));
  const outer = dependent[0];
  if (dependent.length !== 1 || !(outer instanceof Fn) || outer.name !== 'cos') return undefined;
  const inner = first(outer.args);
  if (!(inner instanceof Fn) || inner.name !== 'sinh' || !first(inner.args).equals(x)) return undefined;
  const target = add(...terms.filter((t) => t !== outer)).neg();
  if (containsQ(interval(-1, 1), target) === false) return EmptySet;
  const angle = fn('acos', [target]);
  const numeric = realValue(angle);
  if (numeric === undefined) return new ConditionSet(x, Eq(g, 0), domain);
  const multiple = limitDenominator(rationalFromFloat(numeric / Math.PI), 360n);
  const rational = mul(S.Pi, multiple);
  const offset = Math.abs(multiple.toNumber() * Math.PI - numeric) <= Number.EPSILON * Math.PI && expandMul(fn('cos', [rational])).equals(expandMul(target)) ? rational : angle;
  const n = new Dummy('n', { integer: true });
  const window = interval(fn('sinh', [domain.start]), fn('sinh', [domain.end]), domain.leftOpen, domain.rightOpen);
  const values = union(...[offset, offset.neg()].map((a) => intersection(imageSet(n, add(mul(2, n, S.Pi), a), Integers), window)));
  return imageSet(x, fn('asinh', [x]), values);
}

function solvesetAlgebraic(gIn: Expr, x: Sym, domain: SetExpr): SetExpr {
  const terms = gIn instanceof Add ? gIn.args : [gIn];
  const dependent = terms.filter((t) => t.has(x));
  if (dependent.length === 1) {
    const term = first(dependent);
    const rhs = add(...terms.filter((t) => t !== term)).neg();
    if (domain === Reals && term.equals(x) && fraction(rhs)[1].freeSymbols().size && isNonZero(fraction(rhs)[1]) !== true) {
      return new SetOp('Intersection', [finiteSet(rhs), Reals]);
    }
    const [numerator, denominator] = fraction(term);
    if (domain === Complexes && !numerator.has(x) && denominator instanceof Add && rhs.freeSymbols().size && denominator.has(x)) {
      const values = invertTo(denominator, mul(numerator, pow(rhs, -1)), x);
      return complement(finiteSet(...values), solveset(denominator, x, domain));
    }
  }
  if (domain === Reals || domain instanceof Interval) {
    if (domain === Reals && gIn instanceof Add) {
      const logarithmic = logarithmicPreimage(gIn, x);
      if (logarithmic) return logarithmic;
    }
    let generator: Fn | undefined;
    if (domain === Reals) some(gIn, (f) => {
      if (!(f instanceof Fn) || f.name !== 'coth' || !first(f.args).equals(x)) return false;
      generator = f;
      return true;
    });
    if (generator instanceof Fn && !generator.equals(gIn)) {
      const variable = new Sym('x');
      const polynomial = xreplace(gIn, [[generator, variable]]);
      if (gIn.freeSymbols().size === 1 && !xreplace(gIn, [[generator, S.Zero]]).has(x) && polyCoefficients(polynomial, variable)) {
        const p = Poly.from(polynomial, [variable]);
        const squareFree = p.sqfPart();
        const negative = squareFree.countRoots(S.NegativeInfinity, -1);
        const middle = squareFree.countRoots(S.NegativeInfinity, 1);
        return finiteSet(...squareFree.realRoots().filter((r, i) => i < negative && !r.equals(-1) || i >= middle).map((r) => fn('acoth', [r])));
      }
    }
    if (gIn instanceof Fn && gIn.name === 'arg') {
      const real = new Dummy('x', { real: true });
      const [re, im] = asRealImag(xreplace(first(gIn.args), [[x, real]]));
      return intersection(solveset(xreplace(im, [[real, x]]), x, domain), solveset(Gt(xreplace(re, [[real, x]]), 0), x, domain));
    }
    if (findAbs(gIn, x)) return solveSign(gIn, 'Eq', x, domain);
    const affineExponential = invertExponential(gIn, x, domain);
    if (affineExponential !== undefined) return affineExponential;
    const exponential = realExponential(gIn, x, domain);
    if (exponential !== undefined) return exponential;
    const inv = invertReal(gIn, x, domain);
    if (inv instanceof ConditionSet) return inv;
    if (inv !== undefined) return solveset(inv, x, domain);
    const pw = domain === Reals ? invertRealPower(gIn, x) : undefined;
    if (pw) return pw;
    if (some(gIn, (term) => term instanceof Pow && term.base.has(x) && !term.exp.has(x) && term.exp.freeSymbols().size > 0)) {
      return new ConditionSet(x, Eq(gIn, 0), domain);
    }
    const g = gIn;
    const [lo, hi] = bounds(domain);
    const [num, den] = fraction(cancel(g));
    if (num.equals(S.Zero)) return minus(domain, denominatorZeros(g, x, domain));
    try {
      const zeros = realZeros(num, x, lo, hi);
      if (domain === Reals && zeros.length === 1 && first(zeros) instanceof CRootOf && Poly.from(num, [x]).degree() === 3) {
        return parametricRealRoots(num, den, x, g);
      }
      const zs = zeros.filter((z) => {
        const denominator = xreplace(den, [[x, z]]);
        return !denominator.equals(S.Zero) && !(denominator instanceof Special);
      });
      return intersection(finiteSet(...zs), domain);
    } catch (e) {
      // zeros with parameters (2*x - y = 0): the real ones, kept where the domain contains them
      if (!(e instanceof NotImplementedError)) throw e;
      if (domain === Reals) return parametricRealRoots(num, den, x, g);
      // on an interval: the roots of a polynomial equation, kept where the interval contains them
      if (!polyCoefficients(num, x)) throw e;
      const onDomain = (s: SetExpr): SetExpr => s instanceof SetOp && s.op === 'Union' ? union(...s.args.map(onDomain))
        : intersection(s instanceof SetOp && s.op === 'Intersection' && s.args.includes(Reals) ? intersection(...s.args.filter((a) => a !== Reals)) : s, domain);
      return onDomain(parametricRealRoots(num, den, x, g));
    }
  }
  const g = gIn;
  const [num, den] = fraction(cancel(g));
  let sols: Expr[];
  try {
    sols = Poly.from(num, [x]).allRoots();
  } catch {
    sols = solve(num, x);
  }
  const poles = den.has(x) ? solve(den, x) : [];
  const keep = sols.filter((s) => !poles.some((p) => p.key === s.key));
  return complement(domain === Complexes ? finiteSet(...keep) : intersection(finiteSet(...keep), domain), finiteSet(...poles));
}

/** Invert an isolated absolute value with a known nonnegative right-hand side. */
function invertAbsolute(g: Expr, x: Sym, domain: SetExpr): SetExpr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dependent = terms.filter((t) => t.has(x));
  if (dependent.length !== 1) return undefined;
  const term = first(dependent);
  const factors = term instanceof Mul ? term.args : [term];
  const absolute = factors.find((a) => a instanceof Fn && a.name === 'abs' && a.has(x));
  if (absolute === undefined || factors.filter((a) => a.has(x)).length !== 1) return undefined;
  const rhs = mul(-1, add(...terms.filter((t) => t !== term)), pow(mul(...factors.filter((a) => a !== absolute)), -1));
  if (isNegative(rhs) === true) return EmptySet;
  const argument = first(absolute.args);
  if (isNonNegative(rhs) !== true) {
    // SymPy _invert_abs: a value of unknown sign stays as a condition on the two solutions
    if (domain !== Reals || argument.key !== x.key || rhs.has(x) || rhs.isNumber) return undefined;
    return new ConditionSet(x, new Contains(rhs, interval(S.Zero, S.Infinity)), finiteSet(mul(-1, rhs), rhs));
  }
  const real = new Dummy('x', { real: true });
  if (isReal(xreplace(argument, [[x, real]])) !== true) {
    const [re, im] = asRealImag(xreplace(argument, [[x, real]]));
    return solveset(xreplace(add(pow(re, 2), pow(im, 2), mul(-1, pow(rhs, 2))), [[real, x]]), x, domain);
  }
  return union(solveset(add(argument, rhs), x, domain), solveset(add(argument, mul(-1, rhs)), x, domain));
}

/** Isolate a single exponential before polynomial conversion. */
function invertExponential(g: Expr, x: Sym, domain: SetExpr): SetExpr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dependent = terms.filter((term) => term.has(x));
  if (dependent.length !== 1) return undefined;
  const term = first(dependent);
  const factors = term instanceof Mul ? term.args : [term];
  const variableFactors = factors.filter((factor) => factor.has(x));
  if (variableFactors.length > 1 && variableFactors.every((v) => v instanceof Pow && v.base.equals(S.E))) {
    const exponent = add(...variableFactors.map((v) => cast(v, Pow).exp));
    const [num, den] = asNumerDenom(exponent);
    const rhs = mul(add(...terms.filter((t) => t !== term)).neg(), pow(mul(...factors.filter((v) => !v.has(x))), -1));
    if (den.has(x) && isPositive(rhs) === true && isReal(xreplace(exponent, [[x, new Dummy('r', { real: true })]])) === true) {
      return complement(solveset(add(num, mul(-1, den, log(rhs))), x, domain), solveset(den, x, domain));
    }
  }
  if (variableFactors.length !== 1) return undefined;
  const exponential = first(variableFactors);
  if (!(exponential instanceof Pow) || exponential.base.has(x) || !exponential.exp.has(x)) return undefined;
  const value = mul(-1, add(...terms.filter((part) => part !== term)), pow(mul(...factors.filter((factor) => factor !== exponential)), -1));
  if (exponential.base.equals(S.Zero)) return value.equals(S.One) ? solveset(exponential.exp, x, domain) : value.freeSymbols().size ? undefined : EmptySet;
  if (isPositive(exponential.base) === false || exponential.exp.has(S.I)) return undefined;
  if (value.equals(S.Zero) || isNegative(value) === true) return EmptySet;
  if (exponential.base.equals(S.E)) {
    const [numerator, denominator] = asNumerDenom(exponential.exp);
    if (denominator.has(x)) {
      if (isReal(xreplace(exponential.exp, [[x, new Dummy('r', { real: true })]])) !== true) return undefined;
      return complement(solveset(add(numerator, mul(-1, denominator, log(value))), x, domain), solveset(denominator, x, domain));
    }
    if (numerator instanceof Pow && numerator.base.has(x)) return undefined;
    return solveset(add(exponential.exp, mul(-1, log(value))), x, domain);
  }
  const rhs = mul(log(value), pow(log(exponential.base), -1));
  if (domain === Reals && exponential.exp.equals(x) && !rhs.equals(S.Zero) && exponential.base.freeSymbols().size && isNonZero(log(exponential.base)) !== true) {
    return new SetOp('Intersection', [finiteSet(rhs), Reals]);
  }
  return solveset(add(exponential.exp, rhs.neg()), x, domain);
}

/** Take logarithms of positive exponential factors, or solve in a common exponential generator. */
function realExponential(g: Expr, x: Sym, domain: SetExpr): SetExpr | undefined {
  if (!some(g, (v) => v instanceof Pow && !v.base.has(x) && !v.base.equals(S.E) && v.exp.has(x))) return undefined;
  const terms = g instanceof Add ? g.args : [g];
  const parts: [Expr, Expr][] = [];
  for (const term of terms) {
    const factors = term instanceof Mul ? term.args : [term];
    const coefficient: Expr[] = [], exponents: Expr[] = [];
    for (const factor of factors) {
      if (!factor.has(x)) coefficient.push(factor);
      else if (factor instanceof Pow && !factor.base.has(x) && isPositive(factor.base) === true) {
        if (isReal(xreplace(factor.exp, [[x, new Dummy('x', { real: true })]])) !== true) throw new NotImplementedError('solveset: exponent is not real');
        exponents.push(mul(factor.exp, expand_log(log(factor.base))));
      } else if (factor instanceof Pow && factor.base instanceof Rational && factor.base.isInteger && factor.base.p < -1n && terms.length <= 2) {
        if (terms.length === 1 && factors.every((a) => a === factor || !a.has(x))) return EmptySet;
        const other = terms.find((t) => t !== term);
        if (other === undefined || other.has(x)) return undefined;
        const rhs = mul(-1, other, pow(mul(...factors.filter((a) => a !== factor)), -1));
        if (!(rhs instanceof Rational) || !rhs.isInteger || rhs.isZero) return undefined;
        const [power, exact] = integerLog(rhs.p, factor.base.p);
        return exact ? solveset(add(factor.exp, -power), x, domain) : EmptySet;
      } else return undefined;
    }
    parts.push([mul(...coefficient), add(...exponents)]);
  }
  if (parts.length === 2) {
    const [a, u] = first(parts), [b, v] = at(parts, 1);
    const ratio = mul(-1, b, pow(a, -1));
    if (isNegative(ratio) === true) return EmptySet;
    const residual = add(u, v.neg(), log(ratio).neg());
    if (domain === Reals && a.freeSymbols().size === 0 && b.freeSymbols().size === 0 && u.has(x) && v.has(x)) {
      const slope = coeff(add(u, v.neg()), x);
      if (slope.freeSymbols().size && isNonZero(slope) !== true && expandMul(mul(slope, x)).equals(expandMul(add(u, v.neg())))) {
        return new SetOp('Intersection', [finiteSet(signsimp(mul(log(ratio), pow(slope, -1)))), Reals]);
      }
    }
    return solveset(residual, x, domain);
  }
  const rewritten = add(...parts.map(([a, u]) => mul(a, pow(S.E, expandMul(u)))));
  const polynomial = polynomialInGenerator(rewritten, x);
  if (!polynomial) return undefined;
  const exponent = cast(polynomial[0], Pow, 'exponential generator').exp;
  return union(...polynomial[1].filter((r) => isNonNegative(r) !== false && !r.equals(S.Zero)).map((r) => solveset(add(exponent, mul(-1, log(r))), x, domain)));
}

/** Union of ImageSet(Lambda(n, P*n + s), Integers) over the solutions s in [0, P), or undefined if g is not periodic. */
function periodicSolutions(g: Expr, x: Sym, domain: SetExpr): SetExpr | undefined {
  if (domain !== Reals && domain !== Complexes) return undefined;
  if (!some(g, (t) => t instanceof Fn && ['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(t.name))) return undefined;
  const P = periodicity(g, x);
  if (!P || P instanceof Rational) return undefined;
  // a period with parameters (sin(a*x)) or parametric solutions (sin(x) = a) give a ConditionSet
  const pv = realValue(P);
  if (pv === undefined) throw new NotImplementedError('solveset: period with parameters');
  const base = new Map<string, [Expr, number]>();
  const principal = solve(g, x);
  if (principal.some((s0) => [...s0.freeSymbols()].filter((s) => s instanceof Sym).some((t) => t.key !== x.key))) throw new NotImplementedError('solveset: parametric solutions');
  // shifts by fractions of the period may also solve the equation (e.g. tan-type solutions)
  const cands: Expr[] = [];
  for (const s0 of principal) for (const q of [0, 1, 2, 3]) cands.push(q === 0 ? s0 : add(s0, mul(q, P, Rational.of(1, 4))));
  const vanishes = (s0: Expr) => {
    try {
      const v = xreplace(g, [[x, s0]]).toComplex();
      return Math.hypot(v.re, v.im) < 1e-9;
    } catch {
      return false;
    }
  };
  for (const s0 of cands) {
    if (!principal.includes(s0) && !vanishes(s0)) continue;
    const v = realValue(s0);
    if (v === undefined) continue; // complex principal solutions do not give real ones
    const k = Math.floor(v / pv + 1e-12);
    const s = k === 0 ? s0 : add(s0, mul(-k, P));
    const sv = v - k * pv;
    base.set(s.key, [s, sv]);
  }
  const sols = [...base.values()].sort((a, b) => a[1] - b[1]);
  if (!sols.length) return EmptySet;
  const n = new Dummy('n', { integer: true });
  // Union orders its arguments by sort_key (not by value)
  const sets = sols.map(([s]) => imageSet(n, add(mul(P, n), s), Integers)).sort((a, b) => compareKeys(sortKey(a), sortKey(b)));
  return sets.length === 1 ? first(sets) : new SetOp('Union', sets);
}

/**
 * A polynomial in exp(u) over the complex numbers: the union of the
 * solutions of exp(u) = r for its roots r (SymPy _solve_exponential via
 * _invert_complex).
 */
function complexExpPolynomial(g: Expr, x: Sym): SetExpr | undefined {
  const [num, den] = fraction(cancel(g));
  const pg = den.has(x) ? undefined : polynomialInGenerator(num, x);
  if (!pg || !(pg[0] instanceof Pow)) return undefined;
  const e = pg[0];
  // complexExpSolutions solves exp(u) - r, or raises for a nonlinear u
  // one integer variable for all the image sets (like SymPy's, which compare by their expressions)
  const n = new Dummy('n');
  const sets = pg[1].map((r) => defined(complexExpSolutions(add(e, mul(-1, r)), x, n), 'exp(u) = r'));
  // Union orders its arguments by sort_key
  return sets.length === 1 ? first(sets) : new SetOp('Union', sets.sort((a, b) => compareKeys(sortKey(a), sortKey(b))));
}

/** a*exp(u) + b = 0 with u linear in x over the complex numbers. */
function complexExpSolutions(g: Expr, x: Sym, n: Dummy = new Dummy('n')): SetExpr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dep = terms.filter((t) => t.has(x));
  if (dep.length !== 1) return undefined;
  const t = first(dep);
  const fs = t instanceof Mul ? t.args : [t];
  const e = fs.find((h): h is Pow => h instanceof Pow && h.base instanceof Constant && h.base.name === 'E' && h.has(x));
  if (!e || fs.filter((h) => h.has(x)).length !== 1) return undefined;
  const pc = Poly.from(e.exp, [x]);
  // exp of a nonlinear argument: infinitely many complex solutions (SymPy ConditionSet)
  if (pc.degree() !== 1) throw new NotImplementedError('solveset: exp of a nonlinear argument');
  const a = mul(...fs.filter((h) => h !== e));
  const c = mul(-1, add(...terms.filter((u) => !u.has(x))), pow(a, -1));
  if (c instanceof Rational && c.isZero) return EmptySet;
  const k = pc.LC();
  const rest = add(e.exp, mul(-1, k, x));
  // u = log|c| + I*(2*n*pi + arg(c))
  const u = add(mul(S.I, add(mul(2, n, S.Pi), fn('arg', [c]))), log(fn('abs', [c])));
  let sol = mul(add(u, mul(-1, rest)), pow(k, -1));
  // n ranges over the integers: a negative coefficient of n is flipped (SymPy writes 2*n*I*pi - log(3))
  const coeffN = expandMul(mul(add(sol, mul(-1, xreplace(sol, [[n, S.Zero]]))), pow(n, -1)));
  if (couldExtractMinusSign(coeffN)) sol = xreplace(sol, [[n, mul(-1, n)]]);
  return imageSet(n, sol, Integers);
}

// ---------------------------------------------------------------------------
// calculus utilities
// ---------------------------------------------------------------------------

/** Points where the expression is singular (SymPy singularities). */
export function singularities(eIn: ExprLike, x: Sym, domain?: SetExpr): SetExpr {
  const e = sympify(eIn);
  if (some(e, (node) => node instanceof Pow && (node.exp === S.NegativeInfinity || node.exp === S.Infinity))) throw new NotImplementedError('Singularities of infinite powers are not supported');
  const dom = domain ?? (x.assumptions.real ? Reals : Complexes);
  let sings: SetExpr = EmptySet;
  const visit = (t: Expr) => {
    t.args.forEach(visit);
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative && t.base.has(x)) sings = union(sings, solveset(t.base, x, dom));
    if (t instanceof Fn && ['log', 'asech', 'acsch'].includes(t.name)) sings = union(sings, solveset(first(t.args), x, dom));
    if (t instanceof Fn && ['atanh', 'acoth'].includes(t.name)) sings = union(sings, solveset(add(first(t.args), -1), x, dom), solveset(add(first(t.args), 1), x, dom));
    if (t instanceof Fn && ['tan', 'sec'].includes(t.name)) sings = union(sings, solveset(impl.sympify(cosOf(first(t.args))), x, dom));
    if (t instanceof Fn && ['coth', 'csch'].includes(t.name)) sings = union(sings, solveset(fn('sinh', t.args), x, dom));
    if (t instanceof Fn && ['cot', 'csc'].includes(t.name)) sings = union(sings, solveset(sinOf(first(t.args)), x, dom));
  };
  visit(e);
  return sings;
}
const cosOf = (a: Expr) => impl.sympify(new Fn('cos', [a]));
const sinOf = (a: Expr) => new Fn('sin', [a]);

/** Zeros of the derivative in the domain (SymPy stationary_points). */
export function stationaryPoints(fIn: ExprLike, x: Sym, domain: SetExpr = Reals): SetExpr {
  const f = sympify(fIn);
  return solveset(diff(f, x), x, domain);
}

function monotonic(f: Expr, op: RelOp, iv: SetExpr, x?: Sym): boolean | undefined {
  const free = [...f.freeSymbols()].filter((s) => s instanceof Sym);
  // SymPy: a constant has a dummy variable; several symbols need the symbol to be given
  if (x === undefined && free.length > 1) throw new NotImplementedError('The function has not yet been implemented for all multivariate expressions.');
  const v = x ?? free[0] ?? new Dummy('x');
  // sign(u) = u/Abs(u) away from u = 0 (the derivative of Abs): its zeros and poles are those of a quotient
  let d = mapBottomUp(diff(f, v), (t) => (t instanceof Fn && t.name === 'sign' ? mul(first(t.args), pow(fn('abs', [first(t.args)]), -1)) : t));
  // A nonzero constant factor affects monotonicity only through its sign.
  if (d instanceof Mul) {
    const constant = mul(...d.args.filter((a) => !a.has(v)));
    const sign = fn('sign', [constant]);
    if (sign instanceof Rational) d = mul(sign, ...d.args.filter((a) => a.has(v)));
  }
  // the sign of f' is decided on the interval, or on one period of a periodic f' over the reals
  const dom = iv instanceof Interval ? iv : Reals;
  let ref = iv;
  if (iv === Reals) {
    const P = periodicity(d, v);
    if (P && !(P instanceof Rational && P.isZero)) ref = interval(0, P, false, true);
  }
  // a derivative with parameters has an unknown sign
  if ([...d.freeSymbols()].filter((s) => s instanceof Sym).some((t) => t.key !== v.key)) return undefined;
  const strict = op === 'Gt' || op === 'Lt';
  // strictly monotonic: monotonic with a derivative that vanishes only at isolated points
  // isolated points where f' is undefined but f is not (x + Abs(x) at 0) do not break monotonicity
  const corners = minus(denominatorZeros(d, v, dom), denominatorZeros(f, v, dom));
  const s = union(solveSign(d, strict ? (op === 'Gt' ? 'Ge' : 'Le') : op, v, dom), corners);
  let weak = isSubset(ref, s);
  // f' has the sign only at isolated points while the domain (not a finite set) has interior points
  if (weak === undefined && (s === EmptySet || s instanceof FiniteSet) && !(ref instanceof FiniteSet)) weak = false;
  if (!strict || weak !== true) return weak;
  if (d instanceof Rational && d.isZero) return false;
  const zeros = intersection(solveSign(d, 'Eq', v, dom), ref);
  // f' vanishing on an interval: f is constant there
  return zeros === EmptySet || zeros instanceof FiniteSet;
}

export const isIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): boolean | undefined => monotonic(sympify(f), 'Ge', iv, x);
export const isStrictlyIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): boolean | undefined => monotonic(sympify(f), 'Gt', iv, x);
export const isDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): boolean | undefined => monotonic(sympify(f), 'Le', iv, x);
export const isStrictlyDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym): boolean | undefined => monotonic(sympify(f), 'Lt', iv, x);
export function isMonotonic(f: ExprLike, iv: SetExpr = Reals, x?: Sym): boolean | undefined {
  const inc = isIncreasing(f, iv, x);
  if (inc) return true;
  const dec = isDecreasing(f, iv, x);
  if (dec) return true;
  if (inc === false && dec === false) return false;
  // a derivative free of the variable (f linear in it, with parameters) keeps its sign
  const fe = sympify(f);
  const v = x ?? first([...fe.freeSymbols()].filter((s) => s instanceof Sym));
  return diff(fe, v).has(v) ? undefined : true;
}

/** Convexity on a domain (second derivative nonnegative, no singularities). */
export function isConvex(fIn: ExprLike, x: Sym, domain?: SetExpr): boolean;
export function isConvex(fIn: ExprLike, x: Sym, ...others: Sym[]): Truth;
export function isConvex(fIn: ExprLike, x: Sym, domainOrVariable: SetExpr | Sym = Reals, ...others: Sym[]): Truth {
  if (domainOrVariable instanceof Sym) return isPositiveSemidefinite(hessian(fIn, [x, domainOrVariable, ...others]));
  const domain = domainOrVariable;
  const f = sympify(fIn);
  const sings = singularities(f, x);
  if (sings instanceof FiniteSet && sings.args.some((p) => containsQ(domain, p) === true)) return false;
  const neg = solveSign(diff(diff(f, x), x), 'Lt', x, domain);
  return neg === EmptySet;
}

/** Range of f over a real domain: [min, max] candidates at critical points and ends. */
function extremeValues(f: Expr, x: Sym, domain: SetExpr): Expr[] {
  if (!(x instanceof Sym)) throw new RangeError('The variable must be a symbol');
  if (domain === EmptySet) throw new RangeError('Cannot find extrema on an empty domain');
  if (f instanceof Fn && f.name === 'abs') {
    const values = extremeValues(first(f.args), x, domain);
    const signs = values.map((value) => {
      const sign = cmpReal(value, S.Zero);
      if (sign === undefined) throw new NotImplementedError('Cannot determine whether the absolute value crosses zero');
      return sign;
    });
    const crossesZero = signs.some((sign) => sign <= 0) && signs.some((sign) => sign >= 0);
    return [...values.map((value) => impl.abs(value)), ...(crossesZero ? [S.Zero] : [])];
  }
  let dom = domain;
  if (domain === Reals) {
    const P = periodicity(f, x);
    if (P && !(P instanceof Rational && P.isZero)) dom = interval(0, P);
  }
  const [lo, hi] = bounds(dom);
  // Each side of zero has its own smooth branch of Abs(x).
  const absolute = fn('abs', [x]);
  if (absolute instanceof Fn && f.has(absolute)) {
    const positiveBranch = xreplace(f, [[absolute, x]]);
    const negativeBranch = xreplace(f, [[absolute, x.neg()]]);
    if (isNonNegative(lo) === true) return extremeValues(positiveBranch, x, dom);
    if (isNonNegative(hi.neg()) === true) return extremeValues(negativeBranch, x, dom);
    if (cmpReal(lo, S.Zero) === -1 && cmpReal(hi, S.Zero) === 1) {
      return [...extremeValues(negativeBranch, x, interval(lo, 0)), ...extremeValues(positiveBranch, x, interval(0, hi))];
    }
  }
  const num = fraction(cancel(diff(f, x)))[0];
  let crit: Expr[];
  try {
    crit = realZeros(num, x, lo, hi);
  } catch (err) {
    // e.g. cos(x)**2 - sin(x)**2: retry with the simplified derivative (cos(2*x))
    const simp = simplify(num);
    if (simp.key === num.key) throw err;
    crit = realZeros(simp, x, lo, hi);
  }
  const vals: Expr[] = crit.map((c) => simplify(xreplace(f, [[x, c]])));
  for (const [end, dir] of [
    [lo, '+'],
    [hi, '-'],
  ] as const) {
    vals.push(end instanceof Special ? limit(f, x, end) : simplify(xreplace(f, [[x, end]])));
    void dir;
  }
  return vals;
}

/**
 * The greatest (sign 1) or least (sign -1) of the values; values that do not
 * compare, directly or through their difference, stay in Max / Min.
 */
function extremum(vals: readonly Expr[], sign: 1 | -1): Expr {
  const cmp = (a: Expr, b: Expr) => cmpReal(a, b) ?? cmpReal(simplify(add(a, mul(-1, b))), S.Zero);
  // a value at least as good as v (for the maximum: k >= v)
  const covers = (k: Expr, v: Expr) => {
    const c = cmp(v, k);
    return c !== undefined && c * sign <= 0;
  };
  let kept: Expr[] = [];
  for (const v of vals) {
    if (kept.some((k) => covers(k, v))) continue;
    kept = [...kept.filter((k) => !covers(v, k)), v];
  }
  return kept.length === 1 ? first(kept) : sign === 1 ? Max(...kept) : Min(...kept);
}

export function maximum(fIn: ExprLike, x: Sym, domain: SetExpr = Reals): Expr {
  return extremum(extremeValues(sympify(fIn), x, domain), 1);
}
export function minimum(fIn: ExprLike, x: Sym, domain: SetExpr = Reals): Expr {
  return extremum(extremeValues(sympify(fIn), x, domain), -1);
}



/** a \ b, removing the members of a union one at a time. */
function minus(a: SetExpr, b: SetExpr): SetExpr {
  return b.className === 'Union' ? b.args.reduce<SetExpr>((acc, m) => minus(acc, cast(m, SetExpr, 'Union member')), a) : complement(a, b);
}

/** SymPy Piecewise.as_expr_set_pairs: disjoint real sets for each piece. */
export function asExprSetPairs(p: Expr, domain: SetExpr = Reals): [Expr, SetExpr][] {
  const pairs = cast(p, Piecewise, 'Piecewise').pairs;
  const syms = new Map<string, Sym>();
  for (const [, c] of pairs) for (const s of [...c.freeSymbols()].filter((s) => s instanceof Sym)) syms.set(s.key, s);
  if (syms.size !== 1) throw new NotImplementedError('as_expr_set_pairs: univariate conditions expected');
  const x = first([...syms.values()]);
  let remaining: SetExpr = domain;
  const out: [Expr, SetExpr][] = [];
  const condSet = (c: Expr): SetExpr => {
    if (c instanceof BoolAtom) return c.value ? Reals : EmptySet;
    if (c instanceof BoolOp) {
      const op = c.op;
      const parts = c.args.map(condSet);
      if (op === 'And') return parts.reduce((a, b) => intersection(a, b));
      if (op === 'Or') return parts.reduce((a, b) => union(a, b));
      return complement(Reals, first(parts));
    }
    const r = cast(c, Rel, 'condition');
    return solveSign(add(r.lhs, mul(-1, r.rhs)), r.op, x, Reals);
  };
  for (const [e, c] of pairs) {
    const s: SetExpr = condSet(c);
    const piece = intersection(remaining, s);
    if (piece !== EmptySet) out.push([e, piece]);
    remaining = minus(remaining, s);
  }
  return out;
}

/** A relational for a set of reals in x, written like SymPy's simplified conditions. */
function setToCondition(st: SetExpr, x: Sym): Expr {
  if (st === Reals) return S.true;
  if (st instanceof FiniteSet) return orB(...st.args.map((v) => Eq(x, v)));
  if (st instanceof Interval) {
    const lo = st.start instanceof Special ? undefined : st.leftOpen ? Gt(x, st.start) : Ge(x, st.start);
    const hi = st.end instanceof Special ? undefined : st.rightOpen ? Lt(x, st.end) : Le(x, st.end);
    if (lo && hi) return and(lo, hi);
    // an interval other than Reals has a finite end
    return lo ?? defined(hi, 'finite end');
  }
  // the sets built from the conditions are intervals, finite sets and their unions
  const isUnion = (v: unknown): v is SetOp => v instanceof SetOp && v.op === 'Union';
  return orB(...expectType(st, isUnion, 'set of a condition').args.map((a) => setToCondition(cast(a, SetExpr, 'Union member'), x)).reverse());
}

/** SymPy piecewise_exclusive: make the conditions of a Piecewise mutually exclusive. */
export function piecewiseExclusive(p: Expr, opts: { skipNan?: boolean; deep?: boolean } = {}): Expr {
  // SymPy: every Piecewise of the expression (deep, the default), or the expression itself when it is one
  if (opts.deep !== false) return mapBottomUp(p, (t) => (t instanceof Piecewise ? exclusivePieces(t, opts) : t));
  return p instanceof Piecewise ? exclusivePieces(p, opts) : p;
}

function exclusivePieces(p: Piecewise, opts: { skipNan?: boolean }): Expr {
  const pairs = p.pairs;
  const syms = new Map<string, Sym>();
  for (const [, c] of pairs) for (const t of [...c.freeSymbols()].filter((s) => s instanceof Sym)) syms.set(t.key, t);
  if (syms.size !== 1) return piecewiseExclusiveLogic(pairs, opts.skipNan ?? false);
  const x = first([...syms.values()]);
  const condSet = (c: Expr): SetExpr => {
    if (c instanceof BoolAtom) return c.value ? Reals : EmptySet;
    if (c instanceof BoolOp) {
      const op = c.op;
      const parts = c.args.map(condSet);
      if (op === 'And') return parts.reduce((a, b) => intersection(a, b));
      if (op === 'Or') return parts.reduce((a, b) => union(a, b));
      return complement(Reals, first(parts));
    }
    const r = cast(c, Rel, 'condition');
    return solveSign(add(r.lhs, mul(-1, r.rhs)), r.op, x, Reals);
  };
  let covered: SetExpr = EmptySet;
  const out: Expr[] = [];
  pairs.forEach(([e, c], i) => {
    const sc = condSet(c);
    const own = minus(sc, covered);
    // like SymPy's Piecewise, a piece that can never apply is dropped
    if (own !== EmptySet) out.push(e, i === 0 ? c : setToCondition(own, x));
    covered = union(covered, sc);
  });
  // Piecewise((e, True)) is e
  if (out.length === 2 && out[1] === S.true) return first(out);
  const rest = minus(Reals, covered);
  if (!opts.skipNan && rest !== EmptySet) out.push(S.NaN, setToCondition(rest, x));
  return new Piecewise(out);
}

/** Not(c) with the negation pushed into And and Or (De Morgan) and relations flipped. */
function negate(c: Expr): Expr {
  if (c instanceof BoolOp && c.op === 'And') return orB(...c.args.map(negate));
  if (c instanceof BoolOp && c.op === 'Or') return and(...c.args.map(negate));
  return notB(c);
}

/**
 * SymPy piecewise_exclusive for conditions in several symbols: each condition
 * And-ed with the negation of the earlier ones, NaN where none holds.
 */
function piecewiseExclusiveLogic(pairs: readonly (readonly [Expr, Expr])[], skipNan: boolean): Expr {
  let cum: Expr = S.false;
  const out: Expr[] = [];
  for (const [e, c] of pairs) {
    out.push(e, and(c, negate(cum)));
    cum = orB(c, cum);
  }
  if (!skipNan && cum !== S.true) out.push(S.NaN, negate(cum));
  return new Piecewise(out);
}

/**
 * SymPy not_empty_in: the values of x for which the intersection of a
 * FiniteSet of expressions with an Interval is not empty (over the reals).
 */
export function notEmptyIn(setIn: SetExpr, x: Sym, ...otherSymbols: Sym[]): SetExpr {
  if (otherSymbols.length) throw new NotImplementedError('not_empty_in supports one variable');
  if (!(x instanceof Sym)) throw new RangeError('A symbol must be given');
  if (setIn === EmptySet) return EmptySet;
  if (setIn instanceof SetOp && setIn.op === 'Union') return union(...setIn.args.map((part) => notEmptyIn(part, x)));
  const parts: readonly SetExpr[] = setIn instanceof SetOp && setIn.op === 'Intersection' ? setIn.args : [setIn];
  const fset = parts.find((p): p is FiniteSet => p instanceof FiniteSet);
  if (!fset) throw new NotImplementedError('not_empty_in: FiniteSet intersected with an Interval expected');
  const target = intersection(...parts.filter((part) => part !== fset));
  const targets = target instanceof SetOp && target.op === 'Union' ? target.args : [target];
  const solveRel = (r: Expr): SetExpr => r instanceof BoolAtom ? r.value ? Reals : EmptySet : cast(solveUnivariateInequality(r, x, { relational: false }), SetExpr, 'solution set');
  let out: SetExpr = EmptySet;
  for (const f of fset.args) for (const targetPart of targets) {
    if (targetPart !== Reals && targetPart !== UniversalSet && !(targetPart instanceof Interval)) throw new NotImplementedError('not_empty_in: an interval is required');
    let domain: SetExpr = Reals;
    if (targetPart instanceof Interval) {
      if (!(targetPart.start instanceof Special)) domain = intersection(domain, solveRel(targetPart.leftOpen ? Gt(f, targetPart.start) : Ge(f, targetPart.start)));
      if (!(targetPart.end instanceof Special)) domain = intersection(domain, solveRel(targetPart.rightOpen ? Lt(f, targetPart.end) : Le(f, targetPart.end)));
    }
    out = union(out, complement(domain, denominatorZeros(f, x, Reals)));
  }
  return out;
}

/**
 * SymPy Boolean.as_set(): the set of real values of the one free symbol
 * for which a relation or a boolean combination of relations holds
 * (`(x > 0).as_set()` = Interval.open(0, oo)); true is UniversalSet and
 * false EmptySet.
 */
export function asSet(eIn: ExprLike | boolean): SetExpr {
  const e = typeof eIn === 'boolean' ? (eIn ? S.true : S.false) : sympify(eIn);
  if (e instanceof BoolAtom) return e.value ? UniversalSet : EmptySet;
  const syms = [...e.freeSymbols()].filter((s) => s instanceof Sym);
  if (syms.length !== 1) throw new NotImplementedError('as_set: only expressions with one free symbol are supported');
  const x = first(syms);
  const go = (b: Expr): SetExpr => {
    if (b instanceof Rel) return solveset(b, x, Reals);
    if (b instanceof BoolAtom) return b.value ? Reals : EmptySet;
    if (b instanceof BoolOp) {
      const op = b.op;
      const parts = b.args.map(go);
      if (op === 'And') return intersection(...parts);
      if (op === 'Or') return union(...parts);
      if (op === 'Not') return complement(Reals, first(parts));
    }
    throw new NotImplementedError(`as_set: ${b.toString()}`);
  };
  return go(e);
}

const REL_OPS: Readonly<Record<string, RelOp>> = { '<': 'Lt', '<=': 'Le', '>': 'Gt', '>=': 'Ge', '==': 'Eq', '!=': 'Ne' };

/**
 * SymPy reduce_abs_inequality(expr, rel, gen): the solution of
 * `expr rel 0` (rel one of '<', '<=', '>', '>=', '==', '!=') where expr
 * contains absolute values, by cases on the signs of their arguments.
 */
export function reduceAbsInequality(exprIn: ExprLike, rel: string, gen: Sym): Expr {
  const op = REL_OPS[rel];
  if (op === undefined) throw new RangeError(`Invalid relational operator symbol: '${rel}'`);
  // (SymPy raises TypeError for a gen whose is_extended_real is False; a symjs symbol cannot be declared so)
  // SymPy _bottom_up_scan: the expression without absolute values, with the conditions of each case
  const scan = (e: Expr): [Expr, Expr[]][] => {
    if (e instanceof Add || e instanceof Mul) {
      const build = e instanceof Add ? add : mul;
      return e.args.map(scan).reduce((acc, cur) => acc.flatMap(([a, ca]) => cur.map(([b, cb]): [Expr, Expr[]] => [build(a, b), [...ca, ...cb]])));
    }
    if (e instanceof Pow) {
      const n = e.exp;
      if (!(n instanceof Rational && n.isInteger)) throw new RangeError('Only Integer Powers are allowed on Abs.');
      return scan(e.base).map(([b, c]) => [pow(b, n), c]);
    }
    if (e instanceof Fn && e.name === 'abs') {
      return scan(first(e.args)).flatMap(([a, c]): [Expr, Expr[]][] => [[a, [...c, Ge(a, 0)]], [mul(-1, a), [...c, Lt(a, 0)]]]);
    }
    return [[e, []]];
  };
  // SymPy reduce_rational_inequalities: the union over the cases of the intersections of their conditions
  let set: SetExpr = EmptySet;
  for (const [e, conds] of scan(sympify(exprIn))) {
    let s: SetExpr = solveSign(e, op, gen, Reals);
    for (const c of conds) {
      const r = cast(c, Rel);
      s = intersection(s, solveSign(add(r.lhs, mul(-1, r.rhs)), r.op, gen, Reals));
    }
    set = union(set, s);
  }
  return asRelational(set, gen);
}

/** SymPy reduce_abs_inequalities(exprs, gen): the conjunction of reduce_abs_inequality over [expr, rel] pairs. */
export function reduceAbsInequalities(exprs: readonly (readonly [ExprLike, string])[], gen: Sym): Expr {
  return and(...exprs.map(([e, rel]) => reduceAbsInequality(e, rel, gen)));
}
