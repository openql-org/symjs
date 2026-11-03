// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Pattern matching with Wild symbols (a port of SymPy's
 * Basic.matches / AssocOp._matches_commutative / Pow.matches), plus
 * replace, find and SymPy's count_ops.
 */

import type { ExprLike } from './nodes';
import { Add, Constant, Dummy, Derivative, Expr, ExtensionExpr, Float, Fn, Integral, Mul, Pow, Rational, S, Special, Sym, UndefFn, Wild, WildFunction, impl } from './nodes';
import { Concrete } from './concrete';
import { add, mul, pow, splitCoeff, sympify } from './ops';
import { rebuild, xreplace } from './traverse';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at, defined, first } from './guard';

/** Match result: wild key -> [wild, value]. */
type Dict = Map<string, readonly [Sym, Expr]>;

const isExpPow = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** The `kind2` (Sum/Product) and `op` (relations, connectives) discriminators of a node, if it has them. */
const kind2Of = (e: Expr): unknown => ('kind2' in e ? e.kind2 : undefined);
const opOf = (e: Expr): unknown => ('op' in e ? e.op : undefined);

/** SymPy _node_count (Floats count 1/2, exp(x) is one node). */
function nodeCount(e: Expr): number {
  if (e instanceof Float) return 0.5;
  if (e instanceof Pow && isExpPow(e)) return 1 + nodeCount(e.exp);
  let n = 1;
  for (const a of e.args) n += nodeCount(a);
  return n;
}

/** SymPy ordered(): by node count, then default_sort_key. */
export function ordered(xs: readonly Expr[]): Expr[] {
  return [...xs].sort((a, b) => nodeCount(a) - nodeCount(b) || compareKeys(sortKey(a), sortKey(b)));
}

const hasWild = (e: Expr): boolean => e instanceof Wild || e.args.some(hasWild);
const applyD = (p: Expr, d: Dict): Expr => (d.size ? xreplace(p, [...d.values()]) : p);
const copy = (d: Dict): Dict => new Map(d);

function wildMatches(w: Wild, e: Expr, d: Dict): Dict | undefined {
  if (w instanceof WildFunction) {
    const isFn = e instanceof Fn || e instanceof UndefFn || isExpPow(e) || e instanceof WildFunction;
    if (!isFn) return undefined;
    const n = e instanceof WildFunction ? 0 : isExpPow(e) ? 1 : e.args.length;
    if (w.nargs && !w.nargs.includes(n)) return undefined;
    const out = copy(d);
    out.set(w.key, [w, e]);
    return out;
  }
  if (w.exclude.some((x) => e.has(x))) return undefined;
  if (!w.properties.every((f) => f(e))) return undefined;
  const out = copy(d);
  out.set(w.key, [w, e]);
  return out;
}

/** Structural Basic.matches. */
function basicMatches(p: Expr, e: Expr, d: Dict, old: boolean): Dict | undefined {
  if (p.key === e.key) return copy(d);
  if (p.args.length === 0 || e.args.length === 0) return undefined;
  if (p.kind !== e.kind) return undefined;
  if (p instanceof Fn && !(e instanceof Fn && e.name === p.name)) return undefined;
  if (p instanceof UndefFn && !(e instanceof UndefFn && e.name === p.name)) return undefined;
  if (isExpPow(p) !== isExpPow(e)) return undefined;
  if (kind2Of(p) !== kind2Of(e)) return undefined;
  // extension nodes of different classes (Heaviside and DiracDelta), And and Or, Lt and Gt do not match
  if (p instanceof ExtensionExpr && (e.constructor !== p.constructor || !(e instanceof ExtensionExpr) || e.name !== p.name)) return undefined;
  if (opOf(p) !== opOf(e)) return undefined;
  if (p.args.length !== e.args.length) return undefined;
  let out: Dict | undefined = copy(d);
  for (let i = 0; i < p.args.length; i++) {
    const a = at(p.args, i);
    const b = at(e.args, i);
    if (a.key === b.key) continue;
    out = matchesImpl(applyD(a, out), b, out, old);
    if (!out) return undefined;
  }
  return out;
}

function powMatches(p: Pow, e: Expr, d: Dict, old: boolean): Dict | undefined {
  if (e instanceof Rational && e.isOne) {
    const r = matchesImpl(p.exp, S.Zero, d, old);
    if (r) return r;
  }
  const [b, ex] = e instanceof Pow ? [e.base, e.exp] : [e, S.One];
  const sb = p.base;
  const se = p.exp;
  if (sb instanceof Sym && se instanceof Rational && se.isInteger && !(e instanceof Rational && e.isZero)) {
    if (ex instanceof Rational) return matchesImpl(sb, pow(b, mul(ex, pow(se, -1))), d, old);
    return matchesImpl(sb, pow(e, pow(se, -1)), d, old);
  }
  let r = matchesImpl(p.base, b, copy(d), old);
  if (!r) return undefined;
  const r2 = matchesImpl(applyD(p.exp, r), ex, r, old);
  if (!r2) return basicMatches(p, e, d, old);
  r = r2;
  return r;
}

function asPowersDict(e: Expr): Map<string, [Expr, Expr]> {
  const out = new Map<string, [Expr, Expr]>();
  for (const t of e instanceof Mul ? e.args : [e]) {
    const [b, x] = t instanceof Pow && !isExpPow(t) ? [t.base, t.exp] : [t, S.One];
    const cur = out.get(b.key);
    out.set(b.key, [b, cur ? add(cur[1], x) : x]);
  }
  return out;
}

function mulCombineInverse(lhsIn: Expr, rhsIn: Expr): Expr {
  let lhs = lhsIn;
  let rhs = rhsIn;
  if (lhs.key === rhs.key) return S.One;
  if ([lhs, rhs].some((i) => i instanceof Pow || i instanceof Mul)) {
    const a = asPowersDict(lhs);
    const b = asPowersDict(rhs);
    const blen = b.size;
    for (const [k, [, v]] of [...b]) {
      const av = a.get(k);
      if (av) {
        const nv = add(av[1], mul(-1, v));
        b.delete(k);
        if (nv instanceof Rational && nv.isZero) a.delete(k);
        else a.set(k, [av[0], nv]);
      }
    }
    if (b.size !== blen) {
      lhs = mul(...[...a.values()].map(([k, v]) => pow(k, v)));
      rhs = mul(...[...b.values()].map(([k, v]) => pow(k, v)));
    }
  }
  return mul(lhs, pow(rhs, -1));
}

const addCombineInverse = (lhs: Expr, rhs: Expr): Expr => (lhs.key === rhs.key ? S.Zero : add(lhs, mul(-1, rhs)));

const makeArgs = (isAdd: boolean, e: Expr): readonly Expr[] => (isAdd ? (e instanceof Add ? e.args : [e]) : e instanceof Mul ? e.args : [e]);
const newRaw = (isAdd: boolean, xs: Expr[]): Expr =>
  xs.length === 0 ? (isAdd ? S.Zero : S.One) : xs.length === 1 ? first(xs) : isAdd ? new Add(xs) : new Mul(xs);

function coeffIsNeg(e: Expr): boolean {
  if (e instanceof Rational || e instanceof Float) return e.isNegative;
  if (e instanceof Mul) {
    const c = first(e.args);
    return (c instanceof Rational || c instanceof Float) && c.isNegative;
  }
  return false;
}

function numberSortKey(x: Expr): number {
  if (x instanceof Mul) {
    const c = first(x.args);
    if (c instanceof Rational || c instanceof Float) return c.value;
  }
  return 0;
}

function commutativeMatches(p: Add | Mul, e: Expr, d: Dict, old: boolean): Dict | undefined {
  const isAdd = p instanceof Add;
  if (p.key === e.key) return copy(d);
  // _matches_simple
  if (isAdd) {
    // a number plus one term (an Add has at least two arguments, so a single term needs a numeric coefficient)
    const [c, term] = p.args;
    if (p.args.length === 2 && (c instanceof Rational || c instanceof Float) && term !== undefined) {
      const r = matchesImpl(term, add(e, mul(-1, c)), d, old);
      if (r) return r;
    }
  } else {
    const [c, rest] = splitCoeff(p);
    const terms = rest instanceof Mul ? rest.args : [rest];
    if (terms.length === 1) {
      const r = matchesImpl(first(terms), mulCombineInverse(e, c), d, old);
      if (r) return r;
    }
  }
  // eliminate the exact part of the pattern
  const wildPart: Expr[] = [];
  const exactPart: Expr[] = [];
  for (const a of p.args) (hasWild(a) && !e.has(a) ? wildPart : exactPart).push(a);
  let wild = wildPart;
  if (exactPart.length) {
    const exact = newRaw(isAdd, exactPart);
    const free = e.freeSymbols();
    if (free.size) {
      for (const s of exact.freeSymbols()) if (![...free].some((f) => f.key === s.key)) return undefined;
    }
    const newexpr = isAdd ? addCombineInverse(e, exact) : mulCombineInverse(e, exact);
    if (!old && (e instanceof Add || e instanceof Mul)) {
      if (countOps(newexpr) > countOps(e)) return undefined;
    }
    return matchesImpl(newRaw(isAdd, wild), newexpr, d, old);
  }
  wild = ordered(wild);
  if (isAdd) wild = [...wild].sort((a, b) => numberSortKey(a) - numberSortKey(b));

  let i = 0;
  const saw = new Set<string>();
  let expr = e;
  while (!saw.has(expr.key)) {
    saw.add(expr.key);
    let args = ordered(makeArgs(isAdd, expr));
    if (isAdd && expr instanceof Add) args = [...args].sort((a, b) => numberSortKey(a) - numberSortKey(b));
    const exprList = [isAdd ? S.Zero : S.One, ...args];
    for (const lastOp of [...exprList].reverse()) {
      for (const w of [...wild].reverse()) {
        const d1 = matchesImpl(w, lastOp, d, old);
        if (d1) {
          const d2 = matchesImpl(applyD(p, d1), expr, d1, old);
          if (d2) return d2;
        }
      }
    }
    if (i === 0) {
      if (!isAdd) {
        if (expr instanceof Pow && expr.exp instanceof Rational && expr.exp.isInteger && !isExpPow(expr)) {
          const b = expr.base;
          expr = expr.exp.isPositive ? new Mul([b, pow(b, add(expr.exp, -1))]) : new Mul([pow(b, -1), pow(b, add(expr.exp, 1))]);
          i += 1;
          continue;
        }
      } else {
        const [c, r] = splitCoeff(expr);
        const cv = c.value;
        if (Math.abs(cv) > 1) {
          expr = cv > 0 ? new Add([r, mul(add(c, -1), r)]) : new Add([mul(-1, r), mul(add(c, 1), r)]);
          i += 1;
          continue;
        }
        // try collection on non-Wild symbols
        const was = expr;
        const did = new Set<string>();
        for (const w of [...wild].reverse()) {
          // every term of wild contains a Wild: only the exact factors of a product are collected on
          const cpart = w instanceof Mul ? mul(...w.args.filter((a) => !hasWild(a))) : S.One;
          const free = [...cpart.freeSymbols()].filter((s) => !did.has(s.key));
          if (free.length) {
            free.forEach((s) => did.add(s.key));
            expr = defined(impl.collect?.(expr, free), 'collect');
          }
        }
        if (expr.key !== was.key) continue;
      }
      break;
    }
    break;
  }
  return undefined;
}

function matchesImpl(p: Expr, e: Expr, d: Dict, old: boolean): Dict | undefined {
  if (p instanceof Wild) return wildMatches(p, e, d);
  if (p instanceof Add || p instanceof Mul) return commutativeMatches(p, e, d, old);
  if (p instanceof Pow && !isExpPow(p)) return powMatches(p, e, d, old);
  if (p.args.length === 0) return p.key === e.key ? copy(d) : undefined;
  return basicMatches(p, e, d, old);
}

/** Collect the Wild atoms of a pattern. */
function wilds(p: Expr, out = new Map<string, Wild>()): Map<string, Wild> {
  if (p instanceof Wild) out.set(p.key, p);
  p.args.forEach((a) => wilds(a, out));
  return out;
}

/**
 * Match `expr` against `pattern` (SymPy Basic.match). Returns a map from
 * each Wild to its value, or undefined when there is no match.
 */
export function match(exprIn: ExprLike, patternIn: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | undefined {
  const expr = sympify(exprIn);
  const pattern = sympify(patternIn);
  const old = opts.old ?? false;
  // SymPy 1.14 Basic.match is pattern.matches(expr): Wilds that the match does not need stay unassigned
  const m = matchesImpl(pattern, expr, new Map(), old);
  if (!m) return undefined;
  return new Map([...m.values()].map(([k, v]) => [k, v] as const));
}

// ---------------------------------------------------------------------------
// replace / find
// ---------------------------------------------------------------------------

/** A query for replace/find/atoms: a function name, a node class name, a pattern or a predicate. */
export type Query = { fn: string } | { type: string } | Expr | ((e: Expr) => boolean);
/** The replacement: a function name, a node class name, an expression or a callback. */
export type Replacement = { fn: string } | { type: string } | Expr | ((...args: Expr[]) => Expr);

/** SymPy class name test (isinstance) for a few core classes. */
export function isInstance(e: Expr, type: string): boolean {
  switch (type) {
    case 'Add':
      return e instanceof Add;
    case 'Mul':
      return e instanceof Mul;
    case 'Pow':
      return e instanceof Pow && !isExpPow(e);
    case 'Symbol':
      return e instanceof Sym && !(e instanceof Wild);
    case 'Wild':
      return e instanceof Wild;
    case 'Dummy':
      return e instanceof Dummy;
    case 'Number':
      return e instanceof Rational || e instanceof Float || e instanceof Special;
    case 'Integer':
      return e instanceof Rational && e.isInteger;
    case 'Rational':
      return e instanceof Rational;
    case 'Float':
      return e instanceof Float;
    case 'NumberSymbol':
      return e instanceof Constant && e.name !== 'I';
    case 'ImaginaryUnit':
    case 'I':
      return e instanceof Constant && e.name === 'I';
    case 'Function':
      return e instanceof Fn || e instanceof UndefFn || isExpPow(e);
    case 'AppliedUndef':
      return e instanceof UndefFn;
    case 'Derivative':
      return e instanceof Derivative;
    case 'Atom':
      return e.args.length === 0;
    case 'Expr':
    case 'Basic':
      return true;
    case 'exp':
      return isExpPow(e);
  }
  return e.kind === type;
}

/** Does the node apply the named function (SymPy FunctionClass)? */
export function isFunctionOf(e: Expr, name: string): boolean {
  if (name === 'exp') return isExpPow(e);
  if (name === 'sqrt') return e instanceof Pow && e.exp instanceof Rational && e.exp.p === 1n && e.exp.q === 2n;
  const n = name === 'Abs' ? 'abs' : name;
  return (e instanceof Fn && e.name === n) || (e instanceof UndefFn && e.name === name);
}

function fnArgs(e: Expr): Expr[] {
  return e instanceof Pow && isExpPow(e) ? [e.exp] : [...e.args];
}

function walk(e: Expr, f: (e: Expr) => Expr): Expr {
  let rv = e;
  if (rv.args.length) {
    const newargs = rv.args.map((a) => walk(a, f));
    if (newargs.some((a, i) => a !== rv.args[i] && a.key !== at(rv.args, i).key)) rv = rebuild(rv, newargs);
  }
  return f(rv);
}

/**
 * Replace matching subexpressions (SymPy Basic.replace), bottom-up.
 * With `map` returns the replaced subexpressions as well.
 */
export function replace(
  exprIn: ExprLike,
  query: Query,
  value: Replacement,
  opts: { exact?: boolean; map?: boolean; apply?: (name: string, args: Expr[]) => Expr; applyType?: (type: string, args: Expr[]) => Expr } = {},
): Expr | [Expr, Map<Expr, Expr>] {
  const expr = sympify(exprIn);
  const callFn = (name: string, args: Expr[]): Expr => {
    if (!opts.apply) throw new TypeError('replace: no function constructor');
    return opts.apply(name, args);
  };
  const callType = (type: string, args: Expr[]): Expr => {
    if (type === 'Add') return add(...args);
    if (type === 'Mul') return mul(...args);
    if (type === 'Pow') return pow(at(args, 0), at(args, 1));
    if (!opts.applyType) throw new TypeError('replace: no type constructor');
    return opts.applyType(type, args);
  };
  // the rule gives the replacement of a node, or undefined when the query does not select it
  let rule: (e: Expr) => Expr | undefined;
  if (query instanceof Expr) {
    // pattern query: the replacement sees the values of the Wilds
    const exact = opts.exact ?? wilds(query).size > 1;
    const allNonZero = (r: Map<Sym, Expr>) => [...r.values()].every((x) => !(x instanceof Rational && x.isZero));
    let v: (m: Map<Sym, Expr>) => Expr;
    if (value instanceof Expr) v = (m) => impl.subs(value, new Map([...m]));
    else if (typeof value === 'function') {
      // keyword call: values ordered like the Wilds in the pattern (a Wild the match leaves unassigned gets 0)
      const order = [...wilds(query).values()];
      v = (m) => value(...order.map((w) => [...m].find(([k]) => k.key === w.key)?.[1] ?? S.Zero));
    } else throw new TypeError('replace: unsupported replacement');
    rule = (e) => {
      const m = match(e, query);
      if (!m) return undefined;
      return exact && !allNonZero(m) ? e : v(m);
    };
  } else {
    let test: (e: Expr) => boolean;
    let v: (e: Expr) => Expr;
    if (typeof query === 'function') {
      // predicate query: the replacement sees the node
      test = query;
      if (typeof value === 'function') v = (e) => value(e);
      else if (value instanceof Expr) v = () => value;
      else throw new TypeError('replace: unsupported replacement');
    } else {
      // class query: the replacement is applied to the arguments
      test = 'fn' in query ? (e) => isFunctionOf(e, query.fn) : (e) => isInstance(e, query.type);
      if (value instanceof Expr) v = () => value;
      else if (typeof value === 'function') v = (e) => value(...fnArgs(e));
      else if ('fn' in value) v = (e) => callFn(value.fn, fnArgs(e));
      else v = (e) => callType(value.type, fnArgs(e));
    }
    rule = (e) => (test(e) ? v(e) : undefined);
  }
  const mapping = new Map<Expr, Expr>();
  const rv = walk(expr, (e) => {
    const nv = rule(e);
    if (nv !== undefined && nv.key !== e.key) {
      if (opts.map) mapping.set(e, nv);
      return nv;
    }
    return e;
  });
  return opts.map ? [rv, mapping] : rv;
}

/** All subexpressions satisfying the query (SymPy Basic.find). */
/** SymPy Basic.count(query): the number of subexpressions (with repetition) matching the query. */
export function count(exprIn: ExprLike, query: Query): number {
  const expr = sympify(exprIn);
  const q: (e: Expr) => boolean =
    typeof query === 'function'
      ? query
      : query instanceof Expr
        ? (e) => match(e, query) !== undefined
        : 'fn' in query
          ? (e) => isFunctionOf(e, query.fn)
          : (e) => isInstance(e, query.type);
  let n = 0;
  const walk = (e: Expr) => {
    if (q(e)) n++;
    e.args.forEach(walk);
  };
  walk(expr);
  return n;
}

export function find(exprIn: ExprLike, query: Query): Expr[] {
  const expr = sympify(exprIn);
  const q: (e: Expr) => boolean =
    typeof query === 'function'
      ? query
      : query instanceof Expr
        ? (e) => match(e, query) !== undefined
        : 'fn' in query
          ? (e) => isFunctionOf(e, query.fn)
          : (e) => isInstance(e, query.type);
  const out = new Map<string, Expr>();
  const go = (e: Expr) => {
    if (q(e)) out.set(e.key, e);
    e.args.forEach(go);
  };
  go(expr);
  return [...out.values()];
}

// ---------------------------------------------------------------------------
// count_ops
// ---------------------------------------------------------------------------

/** Operation counts by SymPy name (ADD, MUL, POW, NEG, DIV, SUB, SIN, ...). */
export function countOpsMap(exprIn: ExprLike): Map<string, number> {
  const ops = new Map<string, number>();
  const bump = (k: string, n = 1) => ops.set(k, (ops.get(k) ?? 0) + n);
  const args: Expr[] = [sympify(exprIn)];
  while (args.length) {
    let a = defined(args.pop());
    if (a instanceof Rational) {
      if (!a.isOne) {
        if (a.p < 0n) bump('NEG');
        if (a.q !== 1n) bump('DIV');
      }
      continue;
    }
    if (a instanceof Mul) {
      if (coeffIsNeg(a)) {
        bump('NEG');
        a = a.args[0] instanceof Rational && a.args[0].p === -1n && a.args[0].q === 1n ? newRaw(false, a.args.slice(1)) : mul(-1, a);
      }
      const [n, dd] = defined(impl.fraction?.(a), 'fraction');
      // a negative numerator was made positive above (the coefficient of a product carries the sign)
      if (n instanceof Rational && n.isInteger) {
        bump('DIV');
        args.push(dd);
        continue;
      } else if (!(dd instanceof Rational && dd.isOne)) {
        if (!(dd instanceof Rational && dd.isInteger)) args.push(dd);
        bump('DIV');
        args.push(n);
        continue;
      }
    } else if (a instanceof Add) {
      let negs = 0;
      a.args.forEach((ai, i) => {
        if (coeffIsNeg(ai)) {
          negs++;
          args.push(mul(-1, ai));
          if (i > 0) bump('SUB');
        } else {
          args.push(ai);
          if (i > 0) bump('ADD');
        }
      });
      if (negs === a.args.length) bump('NEG');
      else if (coeffIsNeg(first(a.args))) {
        bump('SUB');
        bump('ADD', -1);
      }
      continue;
    }
    if (a instanceof Pow && a.exp instanceof Rational && a.exp.p === -1n && a.exp.q === 1n) {
      bump('DIV');
      args.push(a.base);
      continue;
    }
    if (a instanceof Constant && a.name === 'E') {
      bump('EXP');
      continue;
    }
    if (a instanceof Pow && isExpPow(a)) {
      bump('EXP');
      args.push(a.exp);
      continue;
    }
    // SymPy counts a Mul or a LatticeOp (Max, Min) once per argument after the first
    if (a instanceof Mul) bump('MUL', a.args.length - 1);
    else if (a instanceof Fn && (a.name === 'Max' || a.name === 'Min')) bump(a.name.toUpperCase(), a.args.length - 1);
    // and a Pow, a function, a Derivative, an Integral or a Sum (not a Product) once
    else if (a.args.length && (a instanceof Pow || a instanceof Fn || a instanceof UndefFn || a instanceof Derivative || a instanceof Integral || (a instanceof Concrete && a.kind2 === 'Sum'))) {
      const name =
        a instanceof Pow
          ? 'POW'
          : a instanceof Fn
            ? sympyName(a.name).toUpperCase()
            : a instanceof UndefFn
              ? `FUNC_${a.name.toUpperCase()}`
              : a instanceof Derivative
                ? 'DERIVATIVE'
                : a instanceof Integral
                  ? 'INTEGRAL'
                  : 'SUM';
      bump(name);
    }
    if (!(a instanceof Sym)) args.push(...a.args);
  }
  for (const [k, n] of [...ops]) if (n === 0) ops.delete(k);
  return ops;
}

const sympyName = (n: string): string => ({ abs: 'Abs', ff: 'FallingFactorial', rf: 'RisingFactorial' })[n] ?? n;

/**
 * SymPy count_ops(expr): the total number of operations; with
 * `{ visual: true }` the operations as an expression such as 2*ADD + SIN.
 */
export function countOps(exprIn: ExprLike, opts?: { visual?: false }): number;
export function countOps(exprIn: ExprLike, opts: { visual: true }): Expr;
export function countOps(exprIn: ExprLike, opts: { visual?: boolean } = {}): number | Expr {
  if (opts.visual) return countOpsVisual(exprIn);
  let n = 0;
  for (const v of countOpsMap(exprIn).values()) n += v;
  return n;
}

/** SymPy count_ops(expr, visual=True): e.g. 2*ADD + SIN. */
export function countOpsVisual(exprIn: ExprLike): Expr {
  const terms = [...countOpsMap(exprIn)].map(([k, v]) => mul(v, new Sym(k)));
  return add(...terms);
}
impl.ordered = ordered;
impl.compareSortKey = (a, b) => compareKeys(sortKey(a), sortKey(b));
impl.match = (e, pattern) => match(e, pattern);
