// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file radsimp (rationalize denominators) and collect (group terms by powers).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Constant, Derivative, impl, Mul, Pow, Rational, S, UndefFn, Wild } from '../core/nodes';
import { add, asBaseExp, mul, pow, sympify } from '../core/ops';
import { rebuild } from '../core/traverse';
import { at, defined, first } from '../core/guard';

// radsimp is the port of SymPy's algorithm in sqrtdenest.ts (they call each other)
export { radsimp } from './sqrtdenest';

/** Power of pattern p in term factor f: f = p**k with rational k, or undefined. */
function powerOf(f: Expr, p: Expr, exact: boolean): Rational | undefined {
  if (f.key === p.key) return S.One;
  if (exact) return undefined;
  const [fb, fe] = asBaseExp(f);
  const [pb, pe] = asBaseExp(p);
  if (fb.key !== pb.key) return undefined;
  const r = mul(fe, pow(pe, -1));
  if (!(r instanceof Rational)) return undefined;
  if (r.isInteger) return r;
  // exp(x) is not a power of exp(2*x) (SymPy collect parses exp(c*u) as exp(u)**c)
  if (fb instanceof Constant && fb.name === 'E') return undefined;
  // SymPy collect substitutes a dummy for the pattern, which replaces f only when
  // p**r evaluates to f (x is not (x**2)**(1/2) unless x is positive)
  return pow(p, r).key === f.key ? r : undefined;
}

/** Split term = (pattern**k) * rest; returns [k, rest] or undefined. */
/** Does factor f stand for the pattern p as a derivative of the same function? */
function derivativeOf(f: Expr, p: Expr): boolean {
  if (!(f instanceof Derivative)) return false;
  const base = p instanceof Derivative ? p.expr : p;
  return f.expr.key === base.key && (base instanceof UndefFn || base.kind === 'Undef');
}

/** [matched part (a power of p or a derivative of it), remaining coefficient]. */
const hasWild = (e: Expr): boolean => e instanceof Wild || e.args.some(hasWild);

function extractPattern(term: Expr, p: Expr, exact: boolean): [Expr, Expr] | undefined {
  const factors = term instanceof Mul ? [...term.args] : [term];
  if (hasWild(p) && impl.match) {
    // a pattern with Wild symbols: the factor matching it is the key (SymPy collect(..., w**y))
    for (const [i, f] of factors.entries()) {
      if (impl.match(f, p) !== undefined) return [f, mul(...factors.filter((_, j) => j !== i))];
    }
    return undefined;
  }
  if (p instanceof Mul) {
    // SymPy collects by a product through subs(pattern, Dummy): the term must contain
    // pattern**k for an integer k (x**2*y = (x*y)*x); numbers in the pattern match
    // anything (collect(x*y - x/8, -x) = x*(y - 1/8))
    const qs = p.args.filter((q) => !(q instanceof Rational));
    const remaining = [...factors];
    const ratios: bigint[] = [];
    const used: number[] = [];
    for (const q of qs) {
      const i = remaining.findIndex((f, j) => !used.includes(j) && powerOf(f, q, false)?.isInteger === true);
      if (i < 0) return undefined;
      used.push(i);
      ratios.push(defined(powerOf(at(remaining, i), q, false), 'power of the pattern factor').p);
    }
    const pos = ratios.every((r) => r > 0n);
    if (!pos && !ratios.every((r) => r < 0n)) return undefined;
    const k = ratios.reduce((m, r) => (pos ? (r < m ? r : m) : r > m ? r : m));
    if (exact && k !== 1n) return undefined;
    const key = pow(mul(...qs), Rational.of(k));
    return [key, mul(term, pow(key, -1))];
  }
  for (const [i, f] of factors.entries()) {
    // as in SymPy, the key is the matched factor itself (x for the pattern x**2, not sqrt(x**2))
    if (powerOf(f, p, exact) !== undefined) return [f, mul(...factors.filter((_, j) => j !== i))];
    const b = f instanceof Pow ? f.base : f;
    if (!exact && derivativeOf(b, p)) return [f, mul(...factors.filter((_, j) => j !== i))];
  }
  return undefined;
}

/** Array.isArray does not narrow a readonly array union. */
const isExprList = (v: readonly Expr[] | Expr): v is readonly Expr[] => Array.isArray(v);

/**
 * Collect additive terms by powers of the given patterns (SymPy collect):
 * collect(a*x**2 + b*x**2 + a*x - b*x + c, x) = c + x**2*(a + b) + x*(a - b).
 * With several patterns, terms free of the first pattern are collected by the next.
 */
export function collect(ex: ExprLike, syms: readonly Expr[] | Expr, opts: { exact?: boolean | null; func?: (c: Expr) => Expr } = {}): Expr {
  const e = sympify(ex);
  const list = isExprList(syms) ? syms : [syms];
  if (list.length === 0) return e;
  if (opts.exact === null || opts.func) {
    // exact=None (and a coefficient function): group the terms by their whole part depending on the symbols
    if (opts.exact !== null) {
      const c = collect(e, list, { exact: opts.exact });
      return groupByDependent(c, list, opts.func);
    }
    return groupByDependent(e, list, opts.func);
  }
  const p = first(list);
  const rest = list.slice(1);
  const terms = e instanceof Add ? e.args : [e];
  const groups = new Map<string, { k: Expr; coeffs: Expr[] }>();
  const free: Expr[] = [];
  for (const t of terms) {
    const m = extractPattern(t, p, opts.exact === true);
    if (!m) {
      free.push(t);
      continue;
    }
    const [k, c] = m;
    const g = groups.get(k.key);
    if (g) g.coeffs.push(c);
    else groups.set(k.key, { k, coeffs: [c] });
  }
  const parts: Expr[] = [];
  for (const { k, coeffs } of groups.values()) parts.push(mul(add(...coeffs), k));
  const freePart = rest.length ? collect(add(...free), rest, opts) : add(...free);
  return add(freePart, ...parts);
}


/** Terms grouped by the product of their factors containing the symbols; func applied to each coefficient. */
function groupByDependent(e: Expr, syms: readonly Expr[], func?: (c: Expr) => Expr): Expr {
  const groups = new Map<string, [Expr, Expr[]]>();
  for (const t of e instanceof Add ? e.args : [e]) {
    const fs = t instanceof Mul ? t.args : [t];
    const dep = mul(...fs.filter((f) => syms.some((s) => f.has(s))));
    const c = mul(...fs.filter((f) => !syms.some((s) => f.has(s))));
    const g = groups.get(dep.key);
    if (g) g[1].push(c);
    else groups.set(dep.key, [dep, [c]]);
  }
  return add(...[...groups.values()].map(([dep, cs]) => mul(func ? func(add(...cs)) : add(...cs), dep)));
}

impl.collect = (e, syms) => collect(e, syms);

/** SymPy rcollect(expr, *vars): collect recursively, innermost sums first. */
export function rcollect(ex: ExprLike, ...vars: Expr[]): Expr {
  const go = (e: Expr): Expr => {
    if (e.isAtom || !vars.some((v) => e.has(v))) return e;
    const r = rebuild(e, e.args.map(go));
    return r instanceof Add ? collect(r, vars) : r;
  };
  return go(sympify(ex));
}
