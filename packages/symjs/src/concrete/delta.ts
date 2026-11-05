// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Sums and products of expressions with Kronecker deltas (SymPy
 * sympy.concrete.delta): deltasummation and deltaproduct, which pick the
 * terms where a delta does not vanish.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Fn, Mul, Rational, S } from '../core/nodes';
import { add, mul, sub, sympify } from '../core/ops';
import { at, getOrThrow } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import { ordered } from '../core/match';
import { freeSymbols, piecewiseFold, subs } from '../core/traverse';
import { Lt, piecewise } from '../core/logic';
import { polyCoefficients } from '../polys/poly';
import { factor } from '../polys/sympoly';
import { asRelational, interval } from '../sets/sets';
import { KroneckerDelta } from '../functions/special/hyper';
import { product, summation } from './summations';
import { linsolve } from '../solvers/public';
import { solve } from '../solvers/solve';

/** A limit (k, a, b) of a sum or product. */
export type DeltaLimit = readonly [Sym, ExprLike, ExprLike];

const isDelta = (e: Expr): e is Fn => e instanceof Fn && e.name === 'KroneckerDelta';
const hasDelta = (e: Expr): boolean => isDelta(e) || e.args.some(hasDelta);
const hasSym = (e: Expr, k: Sym): boolean => [...freeSymbols(e)].some((s) => s.key === k.key);

/** The root in index of a KroneckerDelta whose difference of arguments is linear in index (SymPy _is_simple_delta), or undefined. */
function simpleDeltaRoot(e: Expr, index: Sym): Expr | undefined {
  if (!isDelta(e) || !hasSym(e, index)) return undefined;
  const pc = polyCoefficients(sub(at(e.args, 0), at(e.args, 1)), index);
  const c1 = pc?.get(1);
  if (pc === undefined || c1 === undefined || pc.size > 2) return undefined;
  return mul(-1, pc.get(0) ?? S.Zero, c1.pow(-1));
}
const isSimpleDelta = (e: Expr, index: Sym): boolean => simpleDeltaRoot(e, index) !== undefined;

/** SymPy _has_simple_delta: a simple delta in expr, a sum or a product. */
function hasSimpleDelta(e: Expr, index: Sym): boolean {
  if (!hasDelta(e)) return false;
  if (isSimpleDelta(e, index)) return true;
  return (e instanceof Add || e instanceof Mul) && e.args.some((a) => hasSimpleDelta(a, index));
}

/**
 * SymPy _extract_delta: expr = delta*rest for the first simple delta factor
 * of expr, with the root of the delta; undefined when there is none.
 */
function extractDelta(expr: Expr, index: Sym): { root: Expr; rest: Expr } | undefined {
  const factors = expr instanceof Mul ? expr.args : [expr];
  for (let i = 0; i < factors.length; i++) {
    const root = simpleDeltaRoot(at(factors, i), index);
    if (root !== undefined) return { root, rest: mul(...factors.filter((_f, j) => j !== i)) };
  }
  return undefined;
}

/** SymPy _expand_delta: a product with a sum containing a simple delta expanded over that sum. */
function expandDelta(expr: Expr, index: Sym): Expr {
  if (!(expr instanceof Mul)) return expr;
  let expanded = false;
  let terms: Expr[] = [S.One];
  for (const h of expr.args) {
    if (!expanded && h instanceof Add && hasSimpleDelta(h, index)) {
      expanded = true;
      const t0 = at(terms, 0);
      terms = h.args.map((t) => mul(t0, t));
    } else terms = terms.map((t) => mul(t, h));
  }
  return expanded ? add(...terms) : mul(...terms);
}

/** The solution of linear equations for their free symbols (SymPy solve(eqs, dict=True)), or undefined. */
function solveLinear(eqs: readonly Expr[]): Map<Sym, Expr>[] | undefined {
  const free = new Map(eqs.flatMap((e) => [...freeSymbols(e)]).map((s) => [s.key, s] as const));
  // (ordered keeps the symbols, in SymPy's order)
  const syms = ordered([...free.values()]).map((e) => getOrThrow(free, e.key));
  try {
    const sol = linsolve(eqs, syms);
    if (!Array.isArray(sol)) return [];
    // (parameters solve for themselves)
    return [new Map(syms.map((s, i) => [s, at(sol, i)] as const).filter(([s, v]) => s.key !== v.key))];
  } catch {
    return undefined;
  }
}

/** SymPy _remove_multiple_delta: the deltas of each product solved together. */
function removeMultipleDelta(expr: Expr): Expr {
  if (expr instanceof Add) return add(...expr.args.map(removeMultipleDelta));
  if (!(expr instanceof Mul)) return expr;
  const eqs = expr.args.filter(isDelta).map((d) => sub(at(d.args, 0), at(d.args, 1)));
  if (!eqs.length) return expr;
  const sols = solveLinear(eqs);
  if (sols === undefined) return expr;
  const sol = sols[0];
  if (sol === undefined) return S.Zero;
  const expr2 = mul(...expr.args.filter((a) => !isDelta(a)), ...[...sol].map(([k, v]) => KroneckerDelta(k, v)));
  return expr2.key !== expr.key ? removeMultipleDelta(expr2) : expr;
}

/** SymPy _simplify_delta: KroneckerDelta(i, j) as the delta of a symbol and its solution. */
function simplifyDelta(expr: Expr): Expr {
  if (!isDelta(expr)) return expr;
  const eq = sub(at(expr.args, 0), at(expr.args, 1));
  const syms = [...freeSymbols(eq)];
  const s0 = syms[0];
  // one unknown: its solutions (a single one gives a delta)
  if (syms.length === 1 && s0 !== undefined) {
    const sols = solve(eq, s0);
    return sols.length === 1 ? KroneckerDelta(s0, at(sols, 0)) : expr;
  }
  const sol = solveLinear([eq])?.[0];
  if (sol === undefined) return expr;
  return mul(...[...sol].map(([k, v]) => KroneckerDelta(k, v)));
}

const isNegativeRange = (a: Expr, b: Expr): boolean => Lt(sub(b, a), 0) === S.true;

/**
 * SymPy deltasummation: the sum of f over limit = (k, a, b) where f contains
 * Kronecker deltas in k: a delta picks the term at its root, under the
 * condition that the root is in [a, b] (a Piecewise) unless noPiecewise.
 */
export function deltasummation(fIn: ExprLike, limit: DeltaLimit, noPiecewise = false): Expr {
  const f = sympify(fIn);
  const [x, a0, b0] = limit;
  const [a, b] = [sympify(a0), sympify(b0)];
  if (isNegativeRange(a, b)) return S.Zero;
  if (!hasDelta(f)) return summation(f, [x, a, b]);
  const g = expandDelta(f, x);
  if (g instanceof Add) return piecewiseFold(add(...g.args.map((h) => deltasummation(h, [x, a, b], noPiecewise))));
  const d = extractDelta(g, x);
  if (d === undefined) return summation(f, [x, a, b]);
  const value = d.root;
  const term = subs(d.rest, [[x, value]]);
  if (noPiecewise) return term;
  return piecewise([term, asRelational(interval(a, b), value)], [S.Zero, true]);
}

/**
 * SymPy deltaproduct: the product of f over limit = (k, a, b) where f
 * contains Kronecker deltas in k.
 */
export function deltaproduct(fIn: ExprLike, limit: DeltaLimit): Expr {
  const f = sympify(fIn);
  const [x, a0, b0] = limit;
  const [a, b] = [sympify(a0), sympify(b0)];
  if (isNegativeRange(a, b)) return S.One;
  if (!hasDelta(f)) return product(f, [x, a, b]);
  if (f instanceof Add) {
    let delta: Expr | undefined;
    const terms: Expr[] = [];
    for (const arg of ordered([...f.args])) {
      if (delta === undefined && hasSimpleDelta(arg, x)) delta = arg;
      else terms.push(arg);
    }
    if (delta === undefined) throw new NotImplementedError('deltaproduct: no simple delta in the sum');
    const dl = delta;
    const rest = add(...terms);
    const term = (k: Expr): Expr => mul(deltaproduct(rest, [x, a, sub(k, 1)]), subs(dl, [[x, k]]), deltaproduct(rest, [x, add(k, 1), b]));
    let result: Expr;
    if (a instanceof Rational && b instanceof Rational && a.isInteger && b.isInteger) {
      const parts: Expr[] = [];
      for (let ik = a.p; ik <= b.p; ik++) parts.push(term(Rational.of(ik)));
      result = add(deltaproduct(rest, [x, a, b]), ...parts);
    } else {
      const k = new Dummy('kprime', { integer: true });
      result = add(deltaproduct(rest, [x, a, b]), deltasummation(term(k), [k, a, b], hasSimpleDelta(rest, x)));
    }
    return removeMultipleDelta(result);
  }
  if (extractDelta(f, x) === undefined) {
    const g = expandDelta(f, x);
    if (g.key !== f.key) return factor(deltaproduct(g, [x, a, b]));
    return product(f, [x, a, b]);
  }
  return add(removeMultipleDelta(mul(subs(f, [[x, a]]), KroneckerDelta(b, a))), simplifyDelta(KroneckerDelta(b, sub(a, 1))));
}

