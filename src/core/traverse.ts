// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Tree traversal utilities: rebuild, substitution, free symbols, size.
 */

import { fn } from '../functions/elementary';
import { piecewise, rel } from './logic';
import { Add, Expr, ExprLike, Fn, Integral, Mul, Piecewise, Pow, Rel, Substitution, Sym, impl } from './nodes';
import { add, mul, pow, sympify } from './ops';

/** Rebuild a node of the same type with new arguments (re-canonicalizing). */
export function rebuild(e: Expr, args: readonly Expr[]): Expr {
  if (e instanceof Add) return add(...args);
  if (e instanceof Mul) return mul(...args);
  if (e instanceof Pow) return pow(args[0]!, args[1]!);
  if (e instanceof Fn) return fn(e.name, args);
  if (e instanceof Rel) return rel(e.op, args[0]!, args[1]!);
  if (e instanceof Piecewise) {
    const pairs: [Expr, Expr][] = [];
    for (let i = 0; i < args.length; i += 2) pairs.push([args[i]!, args[i + 1]!]);
    return piecewise(...pairs);
  }
  if (e instanceof Integral) return new Integral(args);
  return e;
}

/** Apply f bottom-up to every node. */
export function mapBottomUp(e: Expr, f: (e: Expr) => Expr): Expr {
  if (e.args.length === 0) return f(e);
  const args = e.args.map((a) => mapBottomUp(a, f));
  const changed = args.some((a, i) => a !== e.args[i]);
  return f(changed ? rebuild(e, args) : e);
}

type Rule = { match: (e: Expr) => boolean; to: Expr };

function toRules(s: Substitution): Rule[] {
  const rules: Rule[] = [];
  const pushPair = (from: Expr | string, to: ExprLike) => {
    const target = sympify(to);
    if (typeof from === 'string') {
      rules.push({ match: (e) => e instanceof Sym && e.name === from, to: target });
    } else {
      const key = from.key;
      rules.push({ match: (e) => e.key === key, to: target });
    }
  };
  if (s instanceof Map) {
    for (const [k, v] of s) pushPair(k as Expr | string, v as ExprLike);
  } else if (Array.isArray(s)) {
    for (const [k, v] of s as readonly (readonly [Expr, ExprLike])[]) pushPair(k, v);
  } else {
    for (const [k, v] of Object.entries(s as Record<string, ExprLike>)) pushPair(k, v);
  }
  return rules;
}

/**
 * Simultaneous structural substitution.
 * Keys may be expressions or (in a plain object) symbol names.
 */
export function subs(e: Expr, s: Substitution): Expr {
  const rules = toRules(s);
  if (rules.length === 0) return e;
  const go = (x: Expr): Expr => {
    for (const r of rules) if (r.match(x)) return r.to;
    if (x.args.length === 0) return x;
    const args = x.args.map(go);
    return args.some((a, i) => a !== x.args[i]) ? rebuild(x, args) : x;
  };
  return go(e);
}

export function freeSymbols(e: Expr): Set<Sym> {
  const out = new Map<string, Sym>();
  const go = (x: Expr) => {
    if (x instanceof Sym) out.set(x.key, x);
    else x.args.forEach(go);
  };
  go(e);
  return new Set(out.values());
}

/** Number of nodes in the tree, used as a complexity measure. */
export function countOps(e: Expr): number {
  let n = 1;
  for (const a of e.args) n += countOps(a);
  return n;
}

/** Does any node satisfy the predicate? */
export function some(e: Expr, pred: (e: Expr) => boolean): boolean {
  if (pred(e)) return true;
  return e.args.some((a) => some(a, pred));
}

impl.subs = subs;
impl.freeSymbols = freeSymbols;
