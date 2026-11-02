// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file radsimp (rationalize denominators) and collect (group terms by powers).
 */

import { Add, Constant, Derivative, Expr, impl, ExprLike, Mul, Pow, Rational, S, UndefFn } from '../core/nodes';
import { add, asBaseExp, mul, pow, sympify } from '../core/ops';
import { rebuild } from '../core/traverse';

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
  // exp(x) is not a power of exp(2*x) (SymPy collect parses exp(c*u) as exp(u)**c)
  if (fb instanceof Constant && fb.name === 'E' && !r.isInteger) return undefined;
  return r;
}

/** Split term = (pattern**k) * rest; returns [k, rest] or undefined. */
/** Does factor f stand for the pattern p as a derivative of the same function? */
function derivativeOf(f: Expr, p: Expr): boolean {
  if (!(f instanceof Derivative)) return false;
  const base = p instanceof Derivative ? p.expr : p;
  return f.expr.key === base.key && (base instanceof UndefFn || base.kind === 'Undef');
}

/** [matched part (a power of p or a derivative of it), remaining coefficient]. */
function extractPattern(term: Expr, p: Expr, exact: boolean): [Expr, Expr] | undefined {
  const factors = term instanceof Mul ? [...term.args] : [term];
  if (p instanceof Mul) {
    // every factor of the pattern must occur in the term, possibly as a higher integer power
    const pf = p.args;
    const remaining = [...factors];
    for (const q of pf) {
      const i = remaining.findIndex((f) => f.key === q.key);
      if (i >= 0) {
        remaining.splice(i, 1);
        continue;
      }
      if (exact) return undefined;
      const j = remaining.findIndex((f) => {
        const k = powerOf(f, q, false);
        return k !== undefined && k.isInteger && k.p > 1n;
      });
      if (j < 0) return undefined;
      const k = powerOf(remaining[j]!, q, false)!;
      remaining[j] = pow(q, Number(k.p) - 1);
    }
    return [p, mul(...remaining)];
  }
  for (let i = 0; i < factors.length; i++) {
    const f = factors[i]!;
    const k = powerOf(f, p, exact);
    if (k !== undefined) return [pow(p, k), mul(...factors.filter((_, j) => j !== i))];
    const b = f instanceof Pow ? f.base : f;
    if (!exact && derivativeOf(b, p)) return [f, mul(...factors.filter((_, j) => j !== i))];
  }
  return undefined;
}

/**
 * Collect additive terms by powers of the given patterns (SymPy collect):
 * collect(a*x**2 + b*x**2 + a*x - b*x + c, x) = c + x**2*(a + b) + x*(a - b).
 * With several patterns, terms free of the first pattern are collected by the next.
 */
export function collect(ex: ExprLike, syms: readonly Expr[] | Expr, opts: { exact?: boolean } = {}): Expr {
  const e = sympify(ex);
  const list = Array.isArray(syms) ? (syms as readonly Expr[]) : [syms as Expr];
  if (list.length === 0) return e;
  const [p, ...rest] = list as [Expr, ...Expr[]];
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
