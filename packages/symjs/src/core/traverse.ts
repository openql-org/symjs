// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Tree traversal utilities: rebuild, substitution, free symbols, size.
 */

import { fn } from '../functions/elementary';
import { piecewise, rel } from './logic';
import { Concrete } from '../concrete/node';
import { compareKeys, sortKey } from '../printing/sortkey';
import { Add, Derivative, Expr, ExprLike, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rational, Rel, Substitution, Sym, UndefFn, impl } from './nodes';
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
  if (e instanceof Limit) return new Limit(args, e.dir);
  if (e instanceof Order) return new Order(args);
  if (e instanceof UndefFn) return new UndefFn(e.name, args);
  if (e instanceof Concrete) return new Concrete(e.kind2, args);
  if (e instanceof Derivative) {
    const expr = args[0]!;
    // evaluate when the expression no longer contains undefined functions
    const vc: [Expr, number][] = [];
    for (let i = 1; i < args.length; i += 2) vc.push([args[i]!, Number((args[i + 1] as Rational).p)]);
    if (vc.every(([v]) => v instanceof Sym) && !hasUndef(expr)) {
      return vc.reduce((acc, [v, n]) => impl.diff(acc, v, n), expr);
    }
    return new Derivative(args);
  }
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
 * Simultaneous structural substitution (SymPy `xreplace`): only exact
 * subtrees are replaced. Keys may be expressions or (in a plain object)
 * symbol names.
 */
export function xreplace(e: Expr, s: Substitution): Expr {
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

function toPairs(s: Substitution): [Expr, Expr][] {
  const out: [Expr, Expr][] = [];
  const key = (k: Expr | string): Expr => (typeof k === 'string' ? new Sym(k) : k);
  if (s instanceof Map) for (const [k, v] of s) out.push([key(k as Expr | string), sympify(v as ExprLike)]);
  else if (Array.isArray(s)) for (const [k, v] of s as readonly (readonly [Expr, ExprLike])[]) out.push([k, sympify(v)]);
  else for (const [k, v] of Object.entries(s as Record<string, ExprLike>)) out.push([key(k), sympify(v)]);
  return out;
}

/** Base -> exponent map of a product (commutative), with numeric coefficient. */
function powersOf(e: Expr): { coeff: Expr; pows: Map<string, { base: Expr; exp: Expr }> } {
  const pows = new Map<string, { base: Expr; exp: Expr }>();
  let coeff: Expr = Rational.of(1n);
  for (const f of e instanceof Mul ? e.args : [e]) {
    if (f.isNumber) {
      coeff = mul(coeff, f);
      continue;
    }
    const [b, x] = f instanceof Pow ? f.args : [f, Rational.of(1n)];
    const cur = pows.get(b.key);
    pows.set(b.key, { base: b, exp: cur ? add(cur.exp, x) : x });
  }
  return { coeff, pows };
}

/** SymPy `_eval_subs` for Add, Mul and Pow (algebraic substitution). */
function evalSubs(e: Expr, old: Expr, nw: Expr): Expr | undefined {
  if (e instanceof Add && old instanceof Add) {
    const [cs, ts] = splitAddCoeff(e);
    const [co, to] = splitAddCoeff(old);
    if (cs instanceof Rational && co instanceof Rational) {
      if (ts.key === to.key) return add(nw, cs, mul(-1, co));
      const negTo = mul(-1, to);
      if (ts.key === negTo.key) return add(mul(-1, nw), cs, co);
      const selfArgs = ts instanceof Add ? ts.args : [ts];
      for (const [sign, oldTerms] of [
        [1, to instanceof Add ? to.args : [to]],
        [-1, negTo instanceof Add ? negTo.args : [negTo]],
      ] as const) {
        if (oldTerms.length >= selfArgs.length) continue;
        const selfKeys = new Map(selfArgs.map((a) => [a.key, a]));
        if (oldTerms.every((t) => selfKeys.has(t.key))) {
          for (const t of oldTerms) selfKeys.delete(t.key);
          const rest = [...selfKeys.values()].map((a) => subsOne(a, old, nw));
          return sign === 1 ? add(nw, cs, mul(-1, co), ...rest) : add(mul(-1, nw), cs, co, ...rest);
        }
      }
    }
    return undefined;
  }
  if (e instanceof Mul && old instanceof Mul) {
    const se = powersOf(e);
    const so = powersOf(old);
    if (!(so.coeff instanceof Rational && so.coeff.isOne)) return undefined;
    let k: number | undefined;
    for (const [key, { exp }] of so.pows) {
      const mine = se.pows.get(key);
      if (!mine) return undefined;
      const r = mul(mine.exp, pow(exp, -1));
      if (!(r instanceof Rational)) return undefined;
      const q = Math.floor(r.value);
      if (q < 1) return undefined;
      k = k === undefined ? q : Math.min(k, q);
    }
    if (!k) return undefined;
    const rest: Expr[] = [se.coeff];
    for (const [key, { base, exp }] of se.pows) {
      const o = so.pows.get(key);
      rest.push(pow(base, o ? add(exp, mul(-k, o.exp)) : exp));
    }
    return mul(pow(nw, k), ...rest.map((r) => subsOne(r, old, nw)));
  }
  if (e instanceof Pow && old instanceof Pow && e.base.key === old.base.key) {
    const l = mul(e.exp, pow(old.exp, -1));
    if (l instanceof Rational && l.isInteger) return pow(nw, l);
    return undefined;
  }
  return undefined;
}

function splitAddCoeff(e: Expr): [Expr, Expr] {
  if (e instanceof Add && e.args[0]!.isNumber) {
    return [e.args[0]!, e.args.length === 2 ? e.args[1]! : new Add(e.args.slice(1))];
  }
  return [Rational.of(0n), e];
}

/** Variables bound by a definite Integral or a Sum/Product (SymPy bound_symbols). */
export function boundSymbols(e: Expr): Expr[] {
  if (e instanceof Integral && e.args.length === 4) return [e.args[1]!];
  if (e instanceof Concrete) return e.limits.map(([k]) => k);
  return [];
}

function subsOne(e: Expr, old: Expr, nw: Expr): Expr {
  if (e.key === old.key) return nw;
  if (e.args.length === 0) return e;
  // a bound variable is not free: only the limits are substituted
  const bound = boundSymbols(e);
  if (bound.length && bound.some((b) => old.key === b.key)) {
    if (e instanceof Integral) {
      const [f, v, a, b] = e.args as [Expr, Expr, Expr, Expr];
      const a2 = subsOne(a, old, nw);
      const b2 = subsOne(b, old, nw);
      return a2 === a && b2 === b ? e : rebuild(e, [f, v, a2, b2]);
    }
    const args = e.args.map((a, i) => (i === 0 || (i - 1) % 3 === 0 ? a : subsOne(a, old, nw)));
    return args.some((a, i) => a !== e.args[i]) ? rebuild(e, args) : e;
  }
  const r = evalSubs(e, old, nw);
  if (r !== undefined) return r;
  const args = e.args.map((a) => subsOne(a, old, nw));
  return args.some((a, i) => a !== e.args[i]) ? rebuild(e, args) : e;
}

/**
 * Substitution like SymPy `subs`: pairs are applied in order (unless
 * `simultaneous`), and sums, products and powers are matched algebraically,
 * e.g. (x + y + z).subs(x + y, 1) = z + 1 and (x**4).subs(x**2, y) = y**2.
 */
export function subs(e: Expr, s: Substitution, opts: { simultaneous?: boolean } = {}): Expr {
  let pairs = toPairs(s);
  if (!Array.isArray(s)) {
    // unordered mapping (SymPy dict): more complex keys first, then by sort key
    pairs = [...pairs].sort((a, b) => {
      const d = countOps(b[0]) - countOps(a[0]);
      return d !== 0 ? d : compareKeys(sortKey(a[0]), sortKey(b[0]));
    });
  }
  if (opts.simultaneous) {
    const dummies = pairs.map((_, i) => new Sym(`_subs${i}`));
    let r = e;
    pairs.forEach(([o], i) => (r = subsOne(r, o, dummies[i]!)));
    return xreplace(r, pairs.map(([, n], i) => [dummies[i]!, n] as const));
  }
  let r = e;
  for (const [o, n] of pairs) r = subsOne(r, o, n);
  return r;
}

const hasUndef = (e: Expr): boolean => e instanceof UndefFn || e instanceof Derivative || e.args.some(hasUndef);

export function freeSymbols(e: Expr): Set<Sym> {
  const out = new Map<string, Sym>();
  const go = (x: Expr) => {
    if (x instanceof Sym) out.set(x.key, x);
    else if (x instanceof Integral && x.args.length === 4) {
      // the integration variable of a definite integral is bound
      const v = x.args[1]!;
      for (const s of freeSymbols(x.args[0]!)) if (s.key !== v.key) out.set(s.key, s);
      go(x.args[2]!);
      go(x.args[3]!);
    } else if (x instanceof Concrete) {
      // bound summation variables are not free
      const bound = new Set(x.limits.map(([k]) => k.key));
      for (const s of freeSymbols(x.function)) if (!bound.has(s.key)) out.set(s.key, s);
      for (const [, a, b] of x.limits) {
        go(a);
        go(b);
      }
    } else x.args.forEach(go);
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

impl.subs = (e, s) => subs(e, s);
impl.freeSymbols = freeSymbols;
