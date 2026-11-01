// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Real solution sets: solveset, univariate (polynomial, rational and
 * periodic) inequalities, reduce_inequalities, and the calculus helpers
 * built on them (singularities, stationary points, monotonicity, extrema,
 * convexity, periodicity).
 */

import { Add, Constant, Expr, ExprLike, Fn, Mul, Pow, Rational, Rel, RelOp, S, Special, Sym, impl } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { and, or as orB } from '../core/boolalg';
import { Eq, Ge, Gt, Le, Lt, Ne } from '../core/logic';
import { xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { limit } from '../series/limits';
import { Poly } from '../polys/sympoly';
import { cancel, fraction } from '../simplify/rational';
import { simplify } from '../simplify/simplify';
import { solve } from './solve';
import {
  Complexes,
  EmptySet,
  FiniteSet,
  Interval,
  Reals,
  SetExpr,
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
} from '../sets/sets';

const isRealSym = (e: Expr) => !e.has(S.I);
const relFn: Record<RelOp, (a: ExprLike, b: ExprLike) => Expr> = { Eq, Ne, Lt, Le, Gt, Ge };

function holds(op: RelOp, v: number): boolean {
  switch (op) {
    case 'Lt':
      return v < 0;
    case 'Le':
      return v <= 0;
    case 'Gt':
      return v > 0;
    case 'Ge':
      return v >= 0;
    case 'Eq':
      return v === 0;
    case 'Ne':
      return v !== 0;
  }
}

function numAt(f: Expr, x: Sym, v: Expr): number | undefined {
  try {
    const c = impl.toComplex(xreplace(f, [[x, v]]));
    if (!Number.isFinite(c.re) || Math.abs(c.im) > 1e-9 * Math.max(1, Math.abs(c.re))) return undefined;
    return c.re;
  } catch {
    return undefined;
  }
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
  const g = (a: bigint, b: bigint): bigint => (b === 0n ? (a < 0n ? -a : a) : g(b, a % b));
  // lcm of p/q = lcm(p)/gcd(q)
  let num = 1n;
  let den = 0n;
  for (const c of coeffs) {
    num = (num / g(num, c.p)) * c.p;
    den = g(den, c.q);
  }
  return mul(Rational.of(num < 0n ? -num : num, den), base ?? S.One);
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
    if (!p || p.degree() !== 1) return undefined;
    const c = p.LC();
    return c.has(x) ? undefined : c;
  };
  if (f instanceof Fn) {
    const P = trigPeriod(f.name);
    if (P) {
      const a = linCoeff(f.args[0]!);
      if (a !== undefined) return mul(P, pow(impl.abs(a), -1));
    }
    if (f.name === 'abs') {
      const p = periodicity(f.args[0]!, x);
      return p;
    }
    if (f.args.length === 1 && !P) return periodicity(f.args[0]!, x);
    return undefined;
  }
  if (f instanceof Pow) {
    const isE = f.base instanceof Constant && f.base.name === 'E';
    if (isE) {
      const e = f.exp;
      if (!e.has(S.I)) return periodicity(e, x);
      return undefined;
    }
    const bh = f.base.has(x);
    const eh = f.exp.has(x);
    if (bh && !eh) return periodicity(f.base, x);
    if (eh && !bh) return periodicity(f.exp, x);
    const ps = [f.base, f.exp].map((a) => periodicity(a, x));
    if (ps.some((p) => p === undefined)) return undefined;
    return lcim(ps as Expr[]);
  }
  if (f instanceof Mul || f instanceof Add) {
    const dep = f.args.filter((a) => a.has(x));
    const ps = dep.map((a) => periodicity(a, x));
    if (ps.some((p) => p === undefined)) return undefined;
    return lcim(ps.filter((p) => !(p instanceof Rational && p.isZero)) as Expr[]);
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// zeros
// ---------------------------------------------------------------------------

/** Real zeros of e in [lo, hi] (sorted, distinct). */
function realZeros(e: Expr, x: Sym, lo: Expr, hi: Expr): Expr[] {
  if (!e.has(x)) return [];
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
  const out: Expr[] = [];
  const P = base.length ? periodicity(e, x) : undefined;
  const loV = realValue(lo)!;
  const hiV = realValue(hi)!;
  for (const r of base) {
    if (P && !(P instanceof Rational && P.isZero) && Number.isFinite(loV) && Number.isFinite(hiV)) {
      const pv = realValue(P)!;
      const rv = realValue(r)!;
      const kmin = Math.ceil((loV - rv) / pv - 1e-9);
      const kmax = Math.floor((hiV - rv) / pv + 1e-9);
      for (let k = kmin; k <= kmax; k++) out.push(add(r, mul(k, P)));
    } else out.push(r);
  }
  const uniq = new Map<string, Expr>();
  for (const r of out) {
    const c1 = cmpReal(lo, r);
    const c2 = cmpReal(r, hi);
    if (c1 !== undefined && c1 <= 0 && c2 !== undefined && c2 <= 0) uniq.set(r.key, r);
  }
  return [...uniq.values()].sort((a, b) => cmpReal(a, b) ?? 0);
}

function bounds(domain: SetExpr): [Expr, Expr, boolean, boolean] {
  if (domain === Reals) return [S.NegativeInfinity, S.Infinity, true, true];
  if (domain instanceof Interval) return [domain.start, domain.end, domain.leftOpen, domain.rightOpen];
  throw new Error('inequalities: unsupported domain');
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
function solveSign(f0: Expr, op: RelOp, x: Sym, domain: SetExpr): SetExpr {
  const f = cancel(f0);
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
  const pts = [...zeros, ...poles].sort((a, b) => cmpReal(a, b) ?? 0).filter((p, i, a) => i === 0 || p.key !== a[i - 1]!.key);
  const edges = [lo, ...pts.filter((p) => cmpReal(p, lo) !== 0 && cmpReal(p, hi) !== 0), hi];
  const parts: SetExpr[] = [];
  for (let i = 0; i + 1 < edges.length; i++) {
    const v = numAt(f, x, sample(edges[i]!, edges[i + 1]!));
    if (v !== undefined && holds(op, v)) parts.push(interval(edges[i]!, edges[i + 1]!, true, true));
  }
  if (op === 'Le' || op === 'Ge' || op === 'Ne') {
    for (const z of edges) {
      if (z instanceof Special) continue;
      if (poles.some((p) => p.key === z.key)) continue;
      const v = numAt(f, x, z);
      if (v !== undefined && holds(op, Math.abs(v) < 1e-12 ? 0 : v)) parts.push(finiteSet(z));
    }
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
  if (!(rel instanceof Rel)) throw new Error('solve_univariate_inequality: relational expected');
  const domain = opts.domain ?? Reals;
  const s = solveSign(add(rel.lhs, mul(-1, rel.rhs)), rel.op, x, domain);
  return opts.relational === false ? s : asRelational(s, x);
}

/** SymPy solve_poly_inequality: a list of intervals. */
export function solvePolyInequality(poly: Poly, rel: string): SetExpr[] {
  const x = poly.gens[0] as Sym;
  const roots = poly.realRoots();
  const reals: [Expr, number][] = [];
  for (const r of roots) {
    const last = reals[reals.length - 1];
    if (last && last[0].key === r.key) last[1]++;
    else reals.push([r, 1]);
  }
  void x;
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
  let sign = (poly.LC() as Rational).isPositive ? 1 : -1;
  let eqSign = 0;
  let equal = false;
  if (rel === '>') eqSign = 1;
  else if (rel === '<') eqSign = -1;
  else if (rel === '>=') [eqSign, equal] = [1, true];
  else if (rel === '<=') [eqSign, equal] = [-1, true];
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
  const ineqs = (Array.isArray(ineqsIn) ? ineqsIn : [ineqsIn]).map((e) => sympify(e as ExprLike));
  const rels: Expr[] = ineqs.map((e) => (e instanceof Rel || e.kind === 'Bool' ? e : Eq(e, 0)));
  const gens = symbols.length ? symbols : ([...new Map(rels.flatMap((r) => [...r.freeSymbols()]).map((s) => [s.key, s])).values()] as Sym[]);
  const parts: Expr[] = [];
  const byGen = new Map<string, Expr[]>();
  for (const r of rels) {
    if (!(r instanceof Rel)) {
      parts.push(r);
      continue;
    }
    const fs = [...r.freeSymbols()].filter((s) => gens.some((g) => g.key === s.key));
    if (fs.length !== 1) throw new Error('reduce_inequalities: multivariate inequality');
    const g = fs[0]!;
    if (!byGen.has(g.key)) byGen.set(g.key, []);
    byGen.get(g.key)!.push(r);
  }
  for (const [k, rs] of byGen) {
    const g = gens.find((s) => s.key === k)!;
    const others = [...new Map(rs.flatMap((r) => [...r.freeSymbols()]).map((s) => [s.key, s])).values()].filter((s) => s.key !== g.key);
    if (others.length) {
      for (const r of rs as Rel[]) parts.push(linearInequality(r, g));
      continue;
    }
    let set: SetExpr = Reals;
    for (const r of rs as Rel[]) set = intersection(set, solveSign(add(r.lhs, mul(-1, r.rhs)), r.op, g, Reals_()));
    parts.push(g.assumptions.real ? dropInfiniteBounds(asRelational(set, g)) : asRelational(set, g));
  }
  return and(...parts);
}

const Reals_ = (): SetExpr => Reals;

/** For a real symbol, -oo < x and x < oo are always true (SymPy omits them). */
function dropInfiniteBounds(e: Expr): Expr {
  const isInfBound = (r: Expr) => r instanceof Rel && (r.lhs instanceof Special || r.rhs instanceof Special) && (r.op === 'Lt' || r.op === 'Gt');
  if (isInfBound(e)) return S.true;
  if (e.kind === 'BoolOp') {
    const op = (e as unknown as { op: string }).op;
    const args = e.args.map(dropInfiniteBounds);
    return op === 'And' ? and(...args) : op === 'Or' ? orB(...args) : e;
  }
  return e;
}

/** a*x + b op 0 with symbolic b: x op' -b/a, plus the infinite bound. */
function linearInequality(r: Rel, x: Sym): Expr {
  const f = add(r.lhs, mul(-1, r.rhs));
  const p = Poly.from(f, [x]);
  if (p.degree() !== 1) throw new Error('reduce_inequalities: nonlinear inequality with parameters');
  const a = p.LC();
  const b = p.TC();
  const sol = mul(-1, b, pow(a, -1));
  const av = realValue(a);
  if (av === undefined) throw new Error('reduce_inequalities: unknown sign of coefficient');
  const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
  const op = av < 0 ? flip[r.op] : r.op;
  const main = relFn[op](x, sol);
  if (op === 'Gt' || op === 'Ge') return and(main, Lt(x, S.Infinity));
  if (op === 'Lt' || op === 'Le') return and(main, Lt(S.NegativeInfinity, x));
  return main;
}

/** SymPy solveset for equations and inequalities in one variable. */
export function solveset(fIn: ExprLike, x: Sym, domain: SetExpr = Complexes): SetExpr {
  const f = sympify(fIn);
  if (f instanceof Rel && f.op !== 'Eq' && f.op !== 'Ne') {
    return solveSign(add(f.lhs, mul(-1, f.rhs)), f.op, x, domain === Complexes ? Reals : domain);
  }
  const g = f instanceof Rel ? add(f.lhs, mul(-1, f.rhs)) : f;
  if (!g.has(x)) return g instanceof Rational && g.isZero ? domain : EmptySet;
  if (domain === Reals || domain instanceof Interval) {
    const [lo, hi] = bounds(domain);
    const [num, den] = fraction(cancel(g));
    const zs = realZeros(num, x, lo, hi).filter((z) => !realZeros(den, x, lo, hi).some((p) => p.key === z.key));
    if (domain === Reals && periodicity(g, x) && !(periodicity(g, x) instanceof Rational)) throw new Error('solveset: periodic solutions (ImageSet) are not supported');
    return intersection(finiteSet(...zs), domain);
  }
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
    if (t instanceof Fn && ['log', 'asech', 'acsch'].includes(t.name)) sings = union(sings, solveset(t.args[0]!, x, dom));
    if (t instanceof Fn && ['atanh', 'acoth'].includes(t.name)) sings = union(sings, solveset(add(t.args[0]!, -1), x, dom), solveset(add(t.args[0]!, 1), x, dom));
    if (t instanceof Fn && ['tan', 'sec'].includes(t.name)) sings = union(sings, solveset(impl.sympify(cosOf(t.args[0]!)), x, dom));
    if (t instanceof Fn && ['cot', 'csc'].includes(t.name)) sings = union(sings, solveset(sinOf(t.args[0]!), x, dom));
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
  const v = x ?? (free.length === 1 ? (free[0] as Sym) : undefined);
  if (!v) throw new Error('monotonicity: specify the symbol');
  const d = diff(f, v);
  const s = solveSign(d, op, v, Reals);
  return isSubset(iv, s);
}

export const isIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym) => monotonic(sympify(f), 'Ge', iv, x);
export const isStrictlyIncreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym) => monotonic(sympify(f), 'Gt', iv, x);
export const isDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym) => monotonic(sympify(f), 'Le', iv, x);
export const isStrictlyDecreasing = (f: ExprLike, iv: SetExpr = Reals, x?: Sym) => monotonic(sympify(f), 'Lt', iv, x);
export function isMonotonic(f: ExprLike, iv: SetExpr = Reals, x?: Sym): boolean | undefined {
  const inc = isIncreasing(f, iv, x);
  if (inc) return true;
  const dec = isDecreasing(f, iv, x);
  if (dec) return true;
  return inc === false && dec === false ? false : undefined;
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
  const crit = realZeros(fraction(cancel(diff(f, x)))[0], x, lo, hi);
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

export function maximum(fIn: ExprLike, x: Sym, domain: SetExpr = Reals): Expr {
  const vals = extremeValues(sympify(fIn), x, domain);
  return vals.reduce((m, v) => ((cmpReal(v, m) ?? -1) > 0 ? v : m));
}
export function minimum(fIn: ExprLike, x: Sym, domain: SetExpr = Reals): Expr {
  const vals = extremeValues(sympify(fIn), x, domain);
  return vals.reduce((m, v) => ((cmpReal(v, m) ?? 1) < 0 ? v : m));
}



/** SymPy Piecewise.as_expr_set_pairs: disjoint real sets for each piece. */
export function asExprSetPairs(p: Expr, domain: SetExpr = Reals): [Expr, SetExpr][] {
  const pairs = (p as unknown as { pairs: [Expr, Expr][] }).pairs;
  const syms = new Map<string, Sym>();
  for (const [, c] of pairs) for (const s of c.freeSymbols()) syms.set(s.key, s);
  if (syms.size !== 1) throw new Error('as_expr_set_pairs: univariate conditions expected');
  const x = [...syms.values()][0]!;
  let remaining: SetExpr = domain;
  const out: [Expr, SetExpr][] = [];
  for (const [e, c] of pairs) {
    const s: SetExpr = c.kind === 'Bool' ? ((c as unknown as { value: boolean }).value ? Reals : EmptySet) : solveSign(add((c as Rel).lhs, mul(-1, (c as Rel).rhs)), (c as Rel).op, x, Reals);
    const piece = intersection(remaining, s);
    if (piece !== EmptySet) out.push([e, piece]);
    remaining = complement(remaining, s);
  }
  return out;
}
