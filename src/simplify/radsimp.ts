// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file radsimp (rationalize denominators) and collect (group terms by powers).
 */

import { keepCoeff } from '../core/methods';
import { Add, Expr, impl, ExprLike, Mul, Pow, Rational, S } from '../core/nodes';
import { add, asBaseExp, mul, pow, splitCoeff, sympify } from '../core/ops';
import { expandMul } from './expand';
import { fraction } from './rational';

/** Is t a rational multiple of a square root of a positive rational? */
function sqrtTerm(t: Expr): [Expr, Expr] | undefined {
  const [c, r] = splitCoeff(t);
  if (r instanceof Pow && r.base instanceof Rational && r.exp instanceof Rational && r.exp.p === 1n && r.exp.q === 2n) {
    return [c, r];
  }
  return undefined;
}

/**
 * Rationalize a denominator of the form a + b*sqrt(c) (SymPy radsimp for
 * the common case): 1/(2 + sqrt(2)) -> (2 - sqrt(2))/2.
 */
export function radsimp(ex: ExprLike): Expr {
  const e = sympify(ex);
  const [n, d0] = fraction(e);
  const d = expandMul(d0);
  if (!(d instanceof Add)) return e;
  const rads = d.args.filter((t) => sqrtTerm(t) !== undefined);
  if (rads.length !== 1) return e;
  const rad = rads[0]!;
  const rest = add(...d.args.filter((t) => t !== rad));
  if (rest.has(S.I)) return e;
  const conj = add(rest, mul(-1, rad));
  const den = expandMul(mul(d, conj));
  if (den instanceof Add) return e;
  const num = expandMul(mul(n, conj));
  if (den instanceof Rational) {
    const inv = Rational.of(den.q, den.p);
    // keep (num)/den unevaluated like SymPy, e.g. (2 - sqrt(2))/2
    return num instanceof Add ? keepCoeff(inv, num) : mul(inv, num);
  }
  return mul(num, pow(den, -1));
}

/** Power of pattern p in term factor f: f = p**k with rational k, or undefined. */
function powerOf(f: Expr, p: Expr, exact: boolean): Rational | undefined {
  if (f.key === p.key) return S.One;
  if (exact) return undefined;
  const [fb, fe] = asBaseExp(f);
  const [pb, pe] = asBaseExp(p);
  if (fb.key !== pb.key) return undefined;
  const r = mul(fe, pow(pe, -1));
  return r instanceof Rational ? r : undefined;
}

/** Split term = (pattern**k) * rest; returns [k, rest] or undefined. */
function extractPattern(term: Expr, p: Expr, exact: boolean): [Rational, Expr] | undefined {
  const factors = term instanceof Mul ? [...term.args] : [term];
  if (p instanceof Mul) {
    // every factor of the pattern must occur in the term
    const pf = p.args;
    const remaining = [...factors];
    for (const q of pf) {
      const i = remaining.findIndex((f) => f.key === q.key);
      if (i < 0) return undefined;
      remaining.splice(i, 1);
    }
    return [S.One, mul(...remaining)];
  }
  for (let i = 0; i < factors.length; i++) {
    const k = powerOf(factors[i]!, p, exact);
    if (k !== undefined) {
      return [k, mul(...factors.filter((_, j) => j !== i))];
    }
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
  const groups = new Map<string, { k: Rational; coeffs: Expr[] }>();
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
  for (const { k, coeffs } of groups.values()) {
    const c = add(...coeffs);
    const pk = pow(p, k);
    parts.push(c instanceof Add ? new Mul([c, pk].sort(byKey)) : mul(c, pk));
  }
  const freePart = rest.length ? collect(add(...free), rest, opts) : add(...free);
  return add(freePart, ...parts);
}

const byKey = (a: Expr, b: Expr) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);

impl.collect = (e, syms) => collect(e, syms);
