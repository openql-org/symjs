// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The domain of continuity and the range of a real function and the
 * least common multiple of periods (SymPy sympy.calculus.util:
 * continuous_domain, function_range, lcim). Their other functions are in
 * solvers/inequalities.ts.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Fn, Pow, Rational, S, Special } from '../core/nodes';
import { mul, splitCoeff, sympify } from '../core/ops';
import { at, expectType } from '../core/guard';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { Ge, Gt, Le, Lt } from '../core/logic';
import { fraction } from '../simplify/rational';
import { expand } from '../simplify/expand';
import { diff } from '../calculus/diff';
import { subs } from '../core/traverse';
import { SetExpr, EmptySet, FiniteSet, Interval, Reals, SetOp, complement, finiteSet, inf, intersection, interval, isSubset, sup, union } from '../sets/sets';
import { limit } from '../series/limits';
import { factor, lcmList } from '../polys/sympoly';
import { Q, ask } from '../core/refine';
import { NotImplementedError } from '../core/errors';
import { periodicity, singularities, solveUnivariateInequality, solveset } from './inequalities';

/** The function nodes in e (SymPy atoms(Function)). */
function fnAtoms(e: Expr, out: Map<string, Fn> = new Map()): Fn[] {
  if (e instanceof Fn) out.set(e.key, e);
  e.args.forEach((a) => fnAtoms(a, out));
  return [...out.values()];
}
/** The powers in e (SymPy atoms(Pow)). */
function powAtoms(e: Expr, out: Map<string, Pow> = new Map()): Pow[] {
  if (e instanceof Pow) out.set(e.key, e);
  e.args.forEach((a) => powAtoms(a, out));
  return [...out.values()];
}

const IMPLEMENTED = new Set(['exp', 'log', 'Abs', 'frac', 'sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'asin', 'acos', 'atan', 'acot', 'asec', 'acsc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch']);
type Cond = (u: Expr) => Expr;
const CONSTRAINTS: Readonly<Record<string, readonly Cond[]>> = {
  log: [(u) => Gt(u, 0)],
  asin: [(u) => Ge(u, -1), (u) => Le(u, 1)],
  acos: [(u) => Ge(u, -1), (u) => Le(u, 1)],
  acosh: [(u) => Ge(u, 1)],
  atanh: [(u) => Gt(u, -1), (u) => Lt(u, 1)],
  asech: [(u) => Gt(u, 0), (u) => Le(u, 1)],
};
const CONSTRAINTS_UNION: Readonly<Record<string, readonly Cond[]>> = {
  asec: [(u) => Le(u, -1), (u) => Ge(u, 1)],
  acsc: [(u) => Le(u, -1), (u) => Ge(u, 1)],
  acoth: [(u) => Lt(u, -1), (u) => Gt(u, 1)],
};

const solveIneq = (r: Expr, x: Sym): SetExpr => expectType(solveUnivariateInequality(r, x, { relational: false }), (v): v is SetExpr => v instanceof SetExpr, 'set');

/**
 * SymPy continuous_domain: the part of the real domain where f is
 * continuous (powers, exp, log, Abs, frac and the trigonometric and
 * hyperbolic functions and their inverses).
 */
export function continuousDomain(fIn: ExprLike, symbol: Sym, domain: SetExpr): SetExpr {
  const f = sympify(fIn);
  if (isSubset(domain, Reals) !== true) throw new NotImplementedError('Domain must be a subset of S.Reals.');
  const fns = fnAtoms(f).filter((g) => g.has(symbol));
  if (fns.some((g) => !IMPLEMENTED.has(g.name))) throw new NotImplementedError('Unable to determine the domain of the given function.');
  let dom = domain;
  for (const p of powAtoms(f)) {
    // exp(x) is the power E**x; an odd root (or an integer power) is defined everywhere
    if (p.base === S.E) continue;
    const den = fraction(p.exp)[1];
    if (p.exp instanceof Rational && !(den instanceof Rational && den.p % 2n === 0n)) continue;
    dom = intersection(solveIneq(Ge(p.base, 0), symbol), dom);
  }
  for (const g of fnAtoms(f)) {
    const u = at(g.args, 0);
    const cs = CONSTRAINTS[g.name];
    const cu = CONSTRAINTS_UNION[g.name];
    if (cs) for (const c of cs) dom = intersection(solveIneq(c(u), symbol), dom);
    else if (cu) dom = intersection(union(...cu.map((c) => solveIneq(c(u), symbol))), dom);
    else if (g.name === 'acot') dom = complement(dom, solveset(u, symbol, Reals));
  }
  return complement(dom, singularities(f, symbol, domain));
}

/** The intervals and points of a set (a Union of them, or one). */
function pieces(s: SetExpr): SetExpr[] {
  if (s instanceof SetOp && s.op === 'Union') return [...s.args];
  if (s instanceof Interval || s instanceof FiniteSet || s === Reals) return [s];
  throw new NotImplementedError('Unable to find range for the given domain.');
}

/**
 * SymPy function_range: the range of the real function f of symbol on the
 * domain, from its values at the ends of the intervals of continuity and at
 * the critical points.
 */
export function functionRange(fIn: ExprLike, symbol: Sym, domainIn: SetExpr): SetExpr {
  const f = sympify(fIn);
  if (domainIn === EmptySet) return EmptySet;
  const period = periodicity(f, symbol);
  if (period?.equals(S.Zero) === true) return finiteSet(expand(f));
  let domain = domainIn;
  // a periodic function takes its values on one period
  if (period !== undefined) {
    const parts = domain instanceof SetOp && domain.op === 'Union' ? domain.args : [domain];
    if (parts.some((d) => d instanceof Interval && (inf(d) instanceof Special || sup(d) instanceof Special))) domain = interval(0, period);
  }
  let range: SetExpr = EmptySet;
  for (const piece of pieces(continuousDomain(f, symbol, domain))) {
    if (piece instanceof FiniteSet) {
      for (const p of piece.args) range = union(range, finiteSet(subs(f, [[symbol, p]])));
      continue;
    }
    // (the reals are the open interval from -oo to oo)
    const [lo0, hi0, lopen, ropen] = piece instanceof Interval ? [piece.start, piece.end, piece.leftOpen, piece.rightOpen] : [S.NegativeInfinity, S.Infinity, true, true];
    const vals: Expr[] = [];
    const critical: Expr[] = [];
    for (const [open, point, dir] of [[lopen, lo0, '+'], [ropen, hi0, '-']] as const) {
      if (open) {
        const v = limit(f, symbol, point, dir);
        critical.push(v);
        vals.push(v);
      } else vals.push(subs(f, [[symbol, point]]));
    }
    const cps = solveset(diff(f, symbol), symbol, piece);
    if (!(cps instanceof FiniteSet) && cps !== EmptySet) throw new NotImplementedError(`Unable to find critical points for ${f.toString()}`);
    if (cps instanceof FiniteSet) for (const c of cps.args) vals.push(subs(f, [[symbol, c]]));
    const all = finiteSet(...vals);
    const lo = inf(all);
    const hi = sup(all);
    const crit = finiteSet(...critical);
    const leftOpen = critical.length > 0 && inf(crit).equals(lo);
    const rightOpen = critical.length > 0 && sup(crit).equals(hi);
    range = union(range, interval(lo, hi, leftOpen, rightOpen));
  }
  return range;
}

/**
 * SymPy lcim: the least common multiple of rational numbers, or of
 * irrational numbers with a common irrational factor (periods such as 2*pi
 * and 3*pi); NoMatch (SymPy None) otherwise.
 */
export function lcim(numbersIn: readonly ExprLike[]): Expr | NoMatchResult {
  const numbers = numbersIn.map(sympify);
  if (numbers.every((n) => ask(Q.irrational(n)) === true)) {
    const fs = numbers.map((n) => splitCoeff(factor(n)));
    const term = at(fs, 0)[1];
    if (fs.every(([, t]) => t.equals(term))) return mul(lcmList(fs.map(([c]) => c)), term);
    return NoMatch;
  }
  // the lcm of rationals: the lcm of the numerators over the gcd of the denominators
  if (numbers.every((n): n is Rational => n instanceof Rational)) return Rational.of(numbers.reduce((l, n) => ilcm(l, n.p), 1n), numbers.reduce((g, n) => igcd(g, n.q), 0n));
  return NoMatch;
}

