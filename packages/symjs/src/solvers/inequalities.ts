// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Real solution sets: solveset, univariate (polynomial, rational and
 * periodic) inequalities, reduce_inequalities, and the calculus helpers
 * built on them (singularities, stationary points, monotonicity, extrema,
 * convexity, periodicity).
 */

import { NotImplementedError } from '../core/errors';
import type { Expr, ExprLike, FnName, RelOp, Sym } from '../core/nodes';
import { Add, BoolAtom, Constant, Dummy, Fn, Mul, Piecewise, Pow, Rational, Rel, S, Special, impl } from '../core/nodes';
import { at, cast, defined, expectType, first } from '../core/guard';
import { isNegative, isNonNegative, isReal } from '../core/assumptions';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { expandMul } from '../simplify/expand';
import { factorTerms } from '../simplify/exprtools';
import { BoolOp, and, not as notB, or as orB } from '../core/boolalg';
import { Eq, Ge, Gt, Le, Lt, Ne } from '../core/logic';
import { mapBottomUp, some, xreplace } from '../core/traverse';
import { fn, log } from '../functions/elementary/elementary';
import { Max, Min } from '../functions/special/special';
import { diff } from '../calculus/diff';
import { limit } from '../series/limits';
import { Poly } from '../polys/sympoly';
import { cancel, fraction } from '../simplify/rational';
import { simplify } from '../simplify/simplify';
import { polynomialInGenerator, solve } from './solve';
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
  asRelational,
  cmpReal,
  complement,
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
const byValue = (a: Expr, b: Expr): number => defined(cmpReal(a, b), 'order of real numbers');
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
  const c = impl.toComplex(xreplace(f, [[x, v]]));
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
  let f = sympify(fIn);
  if (f instanceof Rel) f = add(f.lhs, mul(-1, f.rhs));
  f = simplify(f);
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
    const [c1, c2] = [cmpReal(lo, r), cmpReal(r, hi)];
    if (c1 === undefined || c2 === undefined) throw new NotImplementedError('inequalities: zeros with parameters');
    if (c1 <= 0 && c2 <= 0) uniq.set(r.key, r);
  }
  return [...uniq.values()].sort(byValue);
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

function solveSign(f0: Expr, op: RelOp, x: Sym, domain: SetExpr): SetExpr {
  // SymPy: solving an inequality with parameters is not implemented
  if ([...f0.freeSymbols()].some((t) => t.key !== x.key)) throw new NotImplementedError('inequalities: the expression has parameters');
  // a finite real expression plus oo or -oo has the sign of the infinity (SymPy: x < oo is True for a real x)
  if (f0 instanceof Add) {
    const inf = f0.args.find((a) => a instanceof Special);
    if (inf instanceof Special && (inf.name === 'oo' || inf.name === '-oo') && !f0.args.some((a) => a !== inf && some(a, (t) => t instanceof Special))) {
      return op !== 'Eq' && holds(op, inf.name === 'oo' ? Infinity : -Infinity) ? domain : EmptySet;
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
  const f = cancel(f0);
  // a constant (a case of an Abs split, say): the whole domain or nothing
  if (!f.has(x)) {
    const v = realValue(f);
    return v !== undefined && (op === 'Eq' ? v === 0 : holds(op, v)) ? domain : EmptySet;
  }
  const [num, den] = fraction(f);
  let dom = domain;
  if (domain === Reals) {
    const P = periodicity(f, x);
    if (P && !(P instanceof Rational && P.isZero)) dom = interval(0, P, false, true);
  }
  const [lo, hi, lOpen, rOpen] = bounds(dom);
  const zeros = realZeros(num, x, lo, hi);
  const poles = realZeros(den, x, lo, hi);
  if (op === 'Eq') return intersection(finiteSet(...zeros.filter((z) => !poles.some((p) => p.key === z.key))), dom);
  const pts = [...zeros, ...poles].sort(byValue).filter((p, i, a) => i === 0 || p.key !== at(a, i - 1).key);
  const edges = [lo, ...pts.filter((p) => cmpReal(p, lo) !== 0 && cmpReal(p, hi) !== 0), hi];
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
    const v = numAt(f, x, z);
    if (v !== undefined && holds(op, Math.abs(v) < 1e-12 ? 0 : v)) parts.push(finiteSet(z));
  }
  const res = union(...parts);
  return intersection(res, interval(lo, hi, lOpen, rOpen));
}

/** SymPy solve_univariate_inequality. */
export function solveUnivariateInequality(
  relIn: ExprLike,
  x: Sym,
  opts: { relational?: boolean; domain?: SetExpr } = {},
): Expr {
  const rel = sympify(relIn);
  if (!(rel instanceof Rel)) throw new TypeError('solve_univariate_inequality: relational expected');
  const domain = opts.domain ?? Reals;
  const s = solveSign(add(rel.lhs, mul(-1, rel.rhs)), rel.op, x, domain);
  return opts.relational === false ? s : asRelational(s, x);
}

/** SymPy solve_poly_inequality: a list of intervals. */
export function solvePolyInequality(poly: Poly, rel: string): SetExpr[] {
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

/** SymPy reduce_inequalities: a relational description of the solutions. */
export function reduceInequalities(ineqsIn: readonly ExprLike[] | ExprLike, symbols: readonly Sym[] = []): Expr {
  const ineqs = (isExprList(ineqsIn) ? ineqsIn : [ineqsIn]).map((e) => sympify(e));
  const rels: Expr[] = ineqs.map((e) => (e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp ? e : Eq(e, 0)));
  const gens = symbols.length ? symbols : ([...new Map(rels.flatMap((r) => [...r.freeSymbols()]).map((s) => [s.key, s])).values()] as Sym[]);
  const parts: Expr[] = [];
  const byGen = new Map<string, Rel[]>();
  for (const r of rels) {
    if (!(r instanceof Rel)) {
      parts.push(r);
      continue;
    }
    const fs = [...r.freeSymbols()].filter((s) => gens.some((g) => g.key === s.key));
    if (fs.length !== 1) throw new NotImplementedError('reduce_inequalities: multivariate inequality');
    const g = first(fs);
    const list = byGen.get(g.key);
    if (list) list.push(r);
    else byGen.set(g.key, [r]);
  }
  for (const [k, rs] of byGen) {
    const g = defined(gens.find((s) => s.key === k), 'generator');
    const others = [...new Map(rs.flatMap((r) => [...r.freeSymbols()]).map((s) => [s.key, s])).values()].filter((s) => s.key !== g.key);
    if (others.length) {
      for (const r of rs) parts.push(linearInequality(r, g));
      continue;
    }
    let set: SetExpr = Reals;
    for (const r of rs) set = intersection(set, solveSign(add(r.lhs, mul(-1, r.rhs)), r.op, g, Reals_()));
    // (for a real symbol, -oo < x and x < oo are True already, so SymPy's form needs no clean-up)
    parts.push(asRelational(set, g));
  }
  return and(...parts);
}

const Reals_ = (): SetExpr => Reals;

/** a*x + b op 0 with symbolic b: x op' -b/a, plus the infinite bound. */
function linearInequality(r: Rel, x: Sym): Expr {
  const f = add(r.lhs, mul(-1, r.rhs));
  const p = Poly.from(f, [x]);
  if (p.degree() !== 1) throw new NotImplementedError('reduce_inequalities: nonlinear inequality with parameters');
  const a = p.LC();
  const b = p.TC();
  const sol = mul(-1, b, pow(a, -1));
  const av = realValue(a);
  // SymPy leaves the inequality as it is when the sign of the coefficient is unknown
  if (av === undefined) return r;
  const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
  const op = av < 0 ? flip[r.op] : r.op;
  const main = relFn[op](x, sol);
  // like SymPy, only a non-strict inequality gets the infinite bound
  if (op === 'Ge') return and(main, Lt(x, S.Infinity));
  if (op === 'Le') return and(main, Lt(S.NegativeInfinity, x));
  return main;
}

/** SymPy solveset for equations and inequalities in one variable. */
export function solveset(fIn: ExprLike, x: Sym, domain: SetExpr = Complexes): SetExpr {
  const f = sympify(fIn);
  // a decided condition holds everywhere or nowhere (SymPy solveset(True, x) is the domain)
  if (f instanceof BoolAtom) return f.value ? domain : EmptySet;
  if (f instanceof Rel && f.op !== 'Eq') {
    // SymPy keeps an inequality or x != a over the complex numbers as a ConditionSet
    // and so does an inequality with parameters
    if (domain === Complexes || [...f.freeSymbols()].some((t) => t.key !== x.key)) return new ConditionSet(x, f, domain);
    return solveSign(add(f.lhs, mul(-1, f.rhs)), f.op, x, domain);
  }
  const g = f instanceof Rel ? add(f.lhs, mul(-1, f.rhs)) : f;
  if (!g.has(x)) return g instanceof Rational && g.isZero ? domain : EmptySet;
  try {
    // a Piecewise: each piece on the part of the domain where its condition holds first (SymPy _solveset)
    if (g instanceof Piecewise && domain !== Complexes) return solvePiecewise(g, x, domain);
    // periodic equations: the solutions in one period plus multiples of the period (SymPy ImageSet)
    const periodic = periodicSolutions(g, x, domain);
    if (periodic) return periodic;
    if (domain === Complexes) {
      const ex = complexExpSolutions(g, x) ?? complexExpPolynomial(g, x);
      if (ex) return ex;
    }
    return solvesetAlgebraic(g, x, domain);
  } catch {
    // SymPy: an equation that cannot be solved gives a ConditionSet
    return new ConditionSet(x, Eq(g, 0), domain);
  }
}

/** The set where a condition on x holds. */
function conditionSet(c: Expr, x: Sym, domain: SetExpr): SetExpr {
  if (c instanceof BoolOp && (c.op === 'And' || c.op === 'Or')) {
    const parts = c.args.map((a) => conditionSet(a, x, domain));
    return c.op === 'And' ? intersection(...parts) : union(...parts);
  }
  return solveset(c, x, domain);
}

/** The zeros of a Piecewise: those of each piece where its condition holds and no earlier one does. */
function solvePiecewise(g: Piecewise, x: Sym, domain: SetExpr): SetExpr {
  let remaining = domain;
  const parts: SetExpr[] = [];
  for (const [e, c] of g.pairs) {
    const where = c === S.true ? remaining : intersection(remaining, conditionSet(c, x, domain));
    if (where !== EmptySet) parts.push(solveset(e, x, where));
    remaining = complement(remaining, where);
  }
  return union(...parts);
}

/** SymPy _invert_real for a function with an inverse (erf -> erfinv): a*f(u) + b = 0 becomes u = f^-1(-b/a), or undefined. */
const INVERSES: Readonly<Record<string, FnName>> = { erf: 'erfinv', erfc: 'erfcinv', erfinv: 'erf', erfcinv: 'erfc' };
function invertReal(g: Expr, x: Sym): Expr | undefined {
  const terms = g instanceof Add ? g.args : [g];
  const dep = terms.filter((t) => t.has(x));
  if (dep.length !== 1) return undefined;
  const t = first(dep);
  const fs = t instanceof Mul ? t.args : [t];
  const f = fs.find((h): h is Fn => h instanceof Fn && h.name in INVERSES && h.has(x));
  if (!f || fs.filter((h) => h.has(x)).length !== 1) return undefined;
  const a = mul(...fs.filter((h) => h !== f));
  const c = mul(-1, add(...terms.filter((u) => !u.has(x))), pow(a, -1));
  return add(first(f.args), mul(-1, fn(defined(INVERSES[f.name]), [c])));
}

/** The real roots of a polynomial with parameters: SymPy keeps those known to be real and intersects the others with the Reals. */
function parametricRealRoots(num: Expr, den: Expr, x: Sym): SetExpr {
  const realPart = (xs: readonly Expr[]): SetExpr => {
    const reals = xs.filter(isRealSym);
    const unknown = reals.filter((r) => isReal(r) !== true);
    return union(finiteSet(...reals.filter((r) => isReal(r) === true)), unknown.length ? new SetOp('Intersection', [finiteSet(...unknown), Reals]) : EmptySet);
  };
  const roots = realPart(solve(num, x));
  return den.has(x) ? complement(roots, realPart(solve(den, x))) : roots;
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
  if (!e.isInteger || e.p % 2n === 0n) return undefined;
  const sols = invertTo(B, realRoot(c, e.p), x);
  // real_root of a real c is real
  const realC = isReal(c) === true;
  const known = sols.filter((r) => isReal(r) === true || (realC && !r.has(S.I) && [...r.freeSymbols()].every((u) => isReal(u) === true)));
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
      return invertTo(inner, B instanceof Add ? add(r, mul(-1, ...rest)) : mul(r, pow(mul(...rest), -1)), x);
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

function solvesetAlgebraic(gIn: Expr, x: Sym, domain: SetExpr): SetExpr {
  if (domain === Reals || domain instanceof Interval) {
    const inv = invertReal(gIn, x);
    if (inv !== undefined) return solveset(inv, x, domain);
    const pw = domain === Reals ? invertRealPower(gIn, x) : undefined;
    if (pw) return pw;
    const g = gIn;
    const [lo, hi] = bounds(domain);
    const [num, den] = fraction(cancel(g));
    try {
      const zs = realZeros(num, x, lo, hi).filter((z) => !realZeros(den, x, lo, hi).some((p) => p.key === z.key));
      return intersection(finiteSet(...zs), domain);
    } catch (e) {
      // zeros with parameters (2*x - y = 0): over the whole real line they need not be placed
      if (!(e instanceof NotImplementedError) || domain !== Reals) throw e;
      return parametricRealRoots(num, den, x);
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
  return complement(intersection(finiteSet(...keep), domain === Complexes ? finiteSet(...keep) : domain), EmptySet);
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
  if (principal.some((s0) => [...s0.freeSymbols()].some((t) => t.key !== x.key))) throw new NotImplementedError('solveset: parametric solutions');
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
  const n = new Dummy('n');
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
  const dom = domain ?? (x.assumptions.real ? Reals : Complexes);
  let sings: SetExpr = EmptySet;
  const visit = (t: Expr) => {
    t.args.forEach(visit);
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative && t.base.has(x)) sings = union(sings, solveset(t.base, x, dom));
    if (t instanceof Fn && ['log', 'asech', 'acsch'].includes(t.name)) sings = union(sings, solveset(first(t.args), x, dom));
    if (t instanceof Fn && ['atanh', 'acoth'].includes(t.name)) sings = union(sings, solveset(add(first(t.args), -1), x, dom), solveset(add(first(t.args), 1), x, dom));
    if (t instanceof Fn && ['tan', 'sec'].includes(t.name)) sings = union(sings, solveset(impl.sympify(cosOf(first(t.args))), x, dom));
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
  const free = [...f.freeSymbols()];
  // SymPy: a constant has a dummy variable; several symbols need the symbol to be given
  if (x === undefined && free.length > 1) throw new NotImplementedError('The function has not yet been implemented for all multivariate expressions.');
  const v = x ?? free[0] ?? new Dummy('x');
  // sign(u) = u/Abs(u) away from u = 0 (the derivative of Abs): its zeros and poles are those of a quotient
  const d = mapBottomUp(diff(f, v), (t) => (t instanceof Fn && t.name === 'sign' ? mul(first(t.args), pow(fn('abs', [first(t.args)]), -1)) : t));
  // the sign of f' is decided on the interval, or on one period of a periodic f' over the reals
  const dom = iv instanceof Interval ? iv : Reals;
  let ref = iv;
  if (iv === Reals) {
    const P = periodicity(d, v);
    if (P && !(P instanceof Rational && P.isZero)) ref = interval(0, P, false, true);
  }
  // a derivative with parameters has an unknown sign
  if ([...d.freeSymbols()].some((t) => t.key !== v.key)) return undefined;
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
  const v = x ?? first([...fe.freeSymbols()]);
  return diff(fe, v).has(v) ? undefined : true;
}

/** Convexity on a domain (second derivative nonnegative, no singularities). */
export function isConvex(fIn: ExprLike, x: Sym, domain: SetExpr = Reals): boolean {
  const f = sympify(fIn);
  const sings = singularities(f, x);
  if (sings instanceof FiniteSet && sings.args.some((p) => containsQ(domain, p) === true)) return false;
  const neg = solveSign(diff(diff(f, x), x), 'Lt', x, domain);
  return neg === EmptySet;
}

/** Range of f over a real domain: [min, max] candidates at critical points and ends. */
function extremeValues(f: Expr, x: Sym, domain: SetExpr): Expr[] {
  let dom = domain;
  if (domain === Reals) {
    const P = periodicity(f, x);
    if (P && !(P instanceof Rational && P.isZero)) dom = interval(0, P);
  }
  const [lo, hi] = bounds(dom);
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
  for (const [, c] of pairs) for (const s of c.freeSymbols()) syms.set(s.key, s);
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
export function piecewiseExclusive(p: Expr, opts: { skipNan?: boolean } = {}): Expr {
  const pairs = cast(p, Piecewise, 'Piecewise').pairs;
  const syms = new Map<string, Sym>();
  for (const [, c] of pairs) for (const t of c.freeSymbols()) syms.set(t.key, t);
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
export function notEmptyIn(setIn: SetExpr, x: Sym): SetExpr {
  const parts: readonly Expr[] = setIn.className === 'Intersection' ? setIn.args : [];
  const fset = parts.find((p): p is FiniteSet => p instanceof FiniteSet);
  const ivals = parts.filter((p): p is Interval => p instanceof Interval);
  if (!fset || ivals.length !== 1) throw new NotImplementedError('not_empty_in: FiniteSet intersected with an Interval expected');
  const iv = first(ivals);
  const solveRel = (r: Expr): SetExpr => cast(solveUnivariateInequality(r, x, { relational: false }), SetExpr, 'solution set');
  let out: SetExpr = EmptySet;
  for (const f of fset.args) {
    let s: SetExpr = Reals;
    if (!(iv.start instanceof Special)) s = intersection(s, solveRel(iv.leftOpen ? Gt(f, iv.start) : Ge(f, iv.start)));
    if (!(iv.end instanceof Special)) s = intersection(s, solveRel(iv.rightOpen ? Lt(f, iv.end) : Le(f, iv.end)));
    out = union(out, s);
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
  const syms = [...e.freeSymbols()];
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
