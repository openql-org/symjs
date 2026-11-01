// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Harness that replays SymPy doctest cases (compat/corpus.json) against symjs.
 *
 * Each case is a call `f(args, **kwargs)` or `obj.m(args, **kwargs)` with
 * serialized arguments and SymPy's `str()` of the result. An adapter maps the
 * SymPy API name to symjs; the result is formatted like Python's `str()` and
 * compared with the expected string.
 */

import * as sj from '../src';
import { Expr, Integral, Matrix, S, Sym } from '../src';

// ---------------------------------------------------------------------------
// Python-like containers for formatting results
// ---------------------------------------------------------------------------

export class PyList {
  constructor(readonly items: readonly unknown[]) {}
}
export class PyTuple {
  constructor(readonly items: readonly unknown[]) {}
}
export class PyDict {
  constructor(readonly entries: readonly (readonly [unknown, unknown])[]) {}
}
export class PySet {
  constructor(readonly items: readonly unknown[]) {}
}

export class Unsupported extends Error {}

export function fmt(v: unknown): string {
  if (v instanceof Expr) return sj.str(v);
  if (v instanceof Matrix) return v.toString();
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  if (v === null || v === undefined) return 'None';
  if (typeof v === 'number' || typeof v === 'bigint') return String(v);
  if (typeof v === 'string') return `'${v}'`;
  if (v instanceof PyList) return `[${v.items.map(fmt).join(', ')}]`;
  if (v instanceof PyTuple) return v.items.length === 1 ? `(${fmt(v.items[0])},)` : `(${v.items.map(fmt).join(', ')})`;
  if (v instanceof PyDict) return `{${v.entries.map(([k, x]) => `${fmt(k)}: ${fmt(x)}`).join(', ')}}`;
  if (v instanceof PySet) return v.items.length === 0 ? 'set()' : `{${v.items.map(fmt).join(', ')}}`;
  throw new Unsupported(`cannot format ${String(v)}`);
}

/** Split the top level of "{a, b: c, ...}" into items (bracket aware). */
function topLevelItems(s: string): string[] {
  const inner = s.slice(1, -1);
  const out: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of inner) {
    if ('([{'.includes(ch)) depth++;
    if (')]}'.includes(ch)) depth--;
    if (ch === ',' && depth === 0) {
      out.push(cur.trim());
      cur = '';
    } else cur += ch;
  }
  if (cur.trim()) out.push(cur.trim());
  return out;
}

/** Compare with Python's str(); dict and set item order is ignored. */
export function matches(v: unknown, expected: string): boolean {
  const got = fmt(v);
  if (got === expected) return true;
  if ((v instanceof PyDict || v instanceof PySet) && expected.startsWith('{')) {
    const a = topLevelItems(got).sort();
    const b = topLevelItems(expected).sort();
    return a.length === b.length && a.every((x, i) => x === b[i]);
  }
  return false;
}

// ---------------------------------------------------------------------------
// Deserialization of SymPy objects
// ---------------------------------------------------------------------------

type Tree = { t: string; [k: string]: unknown };

const REL_OPS: Record<string, sj.RelOp> = {
  Equality: 'Eq',
  Unequality: 'Ne',
  StrictLessThan: 'Lt',
  LessThan: 'Le',
  StrictGreaterThan: 'Gt',
  GreaterThan: 'Ge',
};

const FUNCTIONS: Record<string, (args: Expr[]) => Expr> = {
  exp: ([a]) => sj.exp(a!),
  Abs: ([a]) => sj.abs(a!),
  ...Object.fromEntries(
    (['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 're', 'im', 'arg', 'conjugate'] as const).map(
      (n) => [n, (args: Expr[]) => sj.fn(n, args)],
    ),
  ),
  Integral: ([f, lim]) => {
    if (lim instanceof Sym) return new Integral([f!, lim]);
    throw new Unsupported('Integral limits');
  },
};

export function deserialize(tree: Tree): unknown {
  switch (tree.t) {
    case 'Py':
      return tree['v'];
    case 'Str':
      return tree['v'];
    case 'Rational':
      return sj.Rational.of(BigInt(tree['p'] as string), BigInt(tree['q'] as string));
    case 'Float':
      return new sj.Float(tree['v'] as number);
    case 'Symbol': {
      const a = tree['assume'] as Record<string, boolean>;
      for (const k of Object.keys(a)) {
        if (!['real', 'positive', 'nonnegative', 'integer'].includes(k)) throw new Unsupported(`assumption ${k}`);
      }
      return new Sym(tree['name'] as string, a);
    }
    case 'Const': {
      const m: Record<string, Expr> = {
        pi: S.Pi,
        E: S.E,
        I: S.I,
        oo: S.Infinity,
        '-oo': S.NegativeInfinity,
        zoo: S.ComplexInfinity,
        nan: S.NaN,
      };
      return m[tree['name'] as string];
    }
    case 'Add':
      return sj.add(...(tree['args'] as Tree[]).map((a) => deserialize(a) as Expr));
    case 'Mul':
      return sj.mul(...(tree['args'] as Tree[]).map((a) => deserialize(a) as Expr));
    case 'Pow': {
      const [b, e] = (tree['args'] as Tree[]).map((a) => deserialize(a) as Expr);
      return sj.pow(b!, e!);
    }
    case 'Rel': {
      const op = REL_OPS[tree['op'] as string];
      if (!op) throw new Unsupported(`relation ${tree['op']}`);
      const [a, b] = (tree['args'] as Tree[]).map((x) => deserialize(x) as Expr);
      return sj.rel(op, a!, b!);
    }
    case 'Fn': {
      const f = FUNCTIONS[tree['name'] as string];
      if (!f) throw new Unsupported(`function ${tree['name']}`);
      return f((tree['args'] as Tree[]).map((a) => deserialize(a) as Expr));
    }
    case 'Tuple':
      return new PyTuple((tree['items'] as Tree[]).map(deserialize));
    case 'Dict':
      return new PyDict((tree['items'] as [Tree, Tree][]).map(([k, v]) => [deserialize(k), deserialize(v)] as const));
    case 'Matrix':
      return Matrix.of((tree['rows'] as Tree[][]).map((r) => r.map((x) => deserialize(x) as Expr)));
    default:
      throw new Unsupported(`type ${tree.t}`);
  }
}

// ---------------------------------------------------------------------------
// Adapters: SymPy API name -> symjs
// ---------------------------------------------------------------------------

export type Adapter = (args: unknown[], kwargs: Record<string, unknown>, self?: unknown) => unknown;

const asExpr = (v: unknown): Expr => {
  if (v instanceof Expr) return v;
  if (typeof v === 'number') return sj.sympify(v);
  if (typeof v === 'boolean') return v ? S.true : S.false;
  throw new Unsupported(`expected an expression, got ${fmt(v)}`);
};
const asSym = (v: unknown): Sym => {
  if (v instanceof Sym) return v;
  throw new Unsupported('expected a symbol');
};
const noKw = (kw: Record<string, unknown>) => {
  const keys = Object.keys(kw);
  if (keys.length) throw new Unsupported(`kwargs ${keys.join(',')}`);
};
const exprFn =
  (f: (e: Expr) => unknown): Adapter =>
  (args, kw) => {
    noKw(kw);
    if (args.length !== 1) throw new Unsupported('arity');
    return f(asExpr(args[0]));
  };
const exprMethod =
  (f: (e: Expr) => unknown): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    if (args.length !== 0) throw new Unsupported('arity');
    return f(asExpr(self));
  };
const matrixMethod =
  (f: (m: Matrix, args: unknown[]) => unknown): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof Matrix)) throw new Unsupported('expected a Matrix');
    return f(self, args);
  };

/** Python str() of a list of roots with multiplicity -> SymPy dict {root: multiplicity}. */
function rootsDict(rs: Expr[]): PyDict {
  const m = new Map<string, [Expr, number]>();
  for (const r of rs) {
    const e = m.get(r.key);
    if (e) e[1]++;
    else m.set(r.key, [r, 1]);
  }
  return new PyDict([...m.values()].map(([r, k]) => [r, k] as const));
}

function diffArgs(e: Expr, rest: unknown[]): Expr {
  let out = e;
  for (let i = 0; i < rest.length; i++) {
    const v = asSym(rest[i]);
    const n = rest[i + 1];
    if (n instanceof sj.Rational && n.isInteger) {
      out = sj.diff(out, v, Number(n.p));
      i++;
    } else out = sj.diff(out, v);
  }
  return out;
}

function subsArgs(e: Expr, args: unknown[]): Expr {
  if (args.length === 2) return e.subs(asExpr(args[0]), asExpr(args[1]));
  const a = args[0];
  if (a instanceof PyDict) return e.subs(a.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
  if (a instanceof PyTuple) {
    // sequential substitution like SymPy
    let out = e;
    for (const p of a.items) {
      if (!(p instanceof PyTuple)) throw new Unsupported('subs pair');
      out = out.subs(asExpr(p.items[0]), asExpr(p.items[1]));
    }
    return out;
  }
  throw new Unsupported('subs arguments');
}

const FN_NAMES = ['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 're', 'im', 'arg', 'conjugate'] as const;

export const ADAPTERS: Record<string, Adapter> = {
  // ---- core constructors
  symbols: (args, kw) => {
    const names = String(args[0]);
    if (/[:]/.test(names)) throw new Unsupported('symbol ranges');
    const a: Record<string, boolean> = {};
    for (const [k, v] of Object.entries(kw)) {
      if (!['real', 'positive', 'nonnegative', 'integer'].includes(k) || v !== true) throw new Unsupported(`symbols ${k}`);
      a[k] = true;
    }
    const syms = names
      .split(/[\s,]+/)
      .filter(Boolean)
      .map((n) => new Sym(n, a));
    return syms.length === 1 && !names.includes(',') ? syms[0] : new PyTuple(syms);
  },
  Symbol: (args, kw) => {
    const a: Record<string, boolean> = {};
    for (const [k, v] of Object.entries(kw)) {
      if (!['real', 'positive', 'nonnegative', 'integer'].includes(k) || v !== true) throw new Unsupported(`Symbol ${k}`);
      a[k] = true;
    }
    return new Sym(String(args[0]), a);
  },
  sympify: (args, kw) => {
    noKw(kw);
    const v = args[0];
    if (typeof v === 'string') return sj.parse(v);
    return asExpr(v);
  },
  S: (args, kw) => ADAPTERS['sympify']!(args, kw),
  Rational: (args, kw) => {
    noKw(kw);
    const [p, q] = args.map(asExpr);
    return q ? sj.div(p!, q) : p;
  },
  Integer: (args, kw) => {
    noKw(kw);
    const v = asExpr(args[0]);
    if (!(v instanceof sj.Rational && v.isInteger)) throw new Unsupported('Integer');
    return v;
  },
  Add: (args, kw) => (noKw(kw), sj.add(...args.map(asExpr))),
  Mul: (args, kw) => (noKw(kw), sj.mul(...args.map(asExpr))),
  Pow: (args, kw) => (noKw(kw), sj.pow(asExpr(args[0]), asExpr(args[1]))),
  sqrt: exprFn(sj.sqrt),
  exp: exprFn(sj.exp),
  Abs: exprFn(sj.abs),
  ...Object.fromEntries(FN_NAMES.map((n) => [n, exprFn((e) => sj.fn(n, [e]))])),
  Eq: (args, kw) => (noKw(kw), sj.Eq(asExpr(args[0]), asExpr(args[1] ?? 0))),
  Ne: (args, kw) => (noKw(kw), sj.Ne(asExpr(args[0]), asExpr(args[1]))),
  Lt: (args, kw) => (noKw(kw), sj.Lt(asExpr(args[0]), asExpr(args[1]))),
  Le: (args, kw) => (noKw(kw), sj.Le(asExpr(args[0]), asExpr(args[1]))),
  Gt: (args, kw) => (noKw(kw), sj.Gt(asExpr(args[0]), asExpr(args[1]))),
  Ge: (args, kw) => (noKw(kw), sj.Ge(asExpr(args[0]), asExpr(args[1]))),

  // ---- manipulation
  expand: exprFn(sj.expand),
  simplify: exprFn(sj.simplify),
  factor: exprFn(sj.factor),
  together: exprFn(sj.together),
  cancel: exprFn(sj.cancel),
  trigsimp: exprFn(sj.trigsimp),
  fraction: exprFn((e) => new PyTuple(sj.fraction(e))),
  diff: (args, kw) => (noKw(kw), diffArgs(asExpr(args[0]), args.slice(1))),
  integrate: (args, kw) => {
    noKw(kw);
    const f = asExpr(args[0]);
    if (args.length !== 2) throw new Unsupported('integrate arity');
    const v = args[1];
    if (v instanceof Sym) return sj.integrate(f, v);
    if (v instanceof PyTuple && v.items.length === 3) {
      return sj.integrate(f, asSym(v.items[0]), [asExpr(v.items[1]), asExpr(v.items[2])]);
    }
    throw new Unsupported('integrate limits');
  },
  roots: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    const syms = [...sj.freeSymbols(e)];
    const x = args[1] ? asSym(args[1]) : syms.length === 1 ? syms[0]! : undefined;
    if (!x) throw new Unsupported('roots generator');
    return rootsDict(sj.roots(e, x));
  },
  solve: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    const syms = [...sj.freeSymbols(e)];
    const x = args[1] instanceof Sym ? args[1] : args.length === 1 && syms.length === 1 ? syms[0]! : undefined;
    if (!x || args.length > 2) throw new Unsupported('solve form');
    return new PyList(sj.solve(e, x));
  },
  Matrix: (args, kw) => {
    noKw(kw);
    const a = args[0];
    if (a instanceof Matrix) return a;
    if (a instanceof PyTuple && a.items.every((r) => r instanceof PyTuple)) {
      return Matrix.of(a.items.map((r) => (r as PyTuple).items.map(asExpr)));
    }
    if (a instanceof PyTuple) return Matrix.col(...a.items.map(asExpr));
    throw new Unsupported('Matrix constructor');
  },
  eye: (args, kw) => (noKw(kw), Matrix.eye(Number((args[0] as sj.Rational).p))),
  zeros: (args, kw) => {
    noKw(kw);
    const [r, c] = args.map((a) => Number((a as sj.Rational).p));
    return Matrix.zeros(r!, c ?? r!);
  },
  diag: (args, kw) => (noKw(kw), Matrix.diag(...args.map(asExpr))),
  det: (args, kw) => {
    noKw(kw);
    if (!(args[0] instanceof Matrix)) throw new Unsupported('det');
    return args[0].det();
  },

  // ---- Expr methods
  '.expand': exprMethod(sj.expand),
  '.simplify': exprMethod(sj.simplify),
  '.factor': exprMethod(sj.factor),
  '.together': exprMethod(sj.together),
  '.cancel': exprMethod(sj.cancel),
  '.trigsimp': exprMethod(sj.trigsimp),
  '.conjugate': exprMethod(sj.conjugate),
  '.subs': (args, kw, self) => {
    noKw(kw);
    if (self instanceof Matrix) {
      if (args.length !== 2) throw new Unsupported('Matrix.subs');
      return self.subs(asExpr(args[0]), asExpr(args[1]));
    }
    return subsArgs(asExpr(self), args);
  },
  '.diff': (args, kw, self) => {
    noKw(kw);
    if (self instanceof Matrix) {
      return self.map((e) => diffArgs(e, args));
    }
    return diffArgs(asExpr(self), args);
  },
  '.integrate': (args, kw, self) => ADAPTERS['integrate']!([self, ...args], kw),
  '.evalf': (args, kw, self) => {
    noKw(kw);
    if (args.length) throw new Unsupported('evalf precision');
    return asExpr(self).evalf();
  },
  '.n': (args, kw, self) => ADAPTERS['.evalf']!(args, kw, self),
  '.has': (args, kw, self) => {
    noKw(kw);
    const e = self instanceof Matrix ? self.data : [asExpr(self)];
    return args.some((a) => e.some((x) => x.has(asExpr(a))));
  },

  // ---- Matrix methods
  '.det': matrixMethod((m) => m.det()),
  '.inv': matrixMethod((m) => m.inv()),
  '.transpose': matrixMethod((m) => m.transpose()),
  '.adjugate': matrixMethod((m) => m.adjugate()),
  '.trace': matrixMethod((m) => m.trace()),
  '.eigenvals': matrixMethod((m) => rootsDict(m.eigenvals())),
  '.is_symmetric': matrixMethod((m) => m.isSquare && m.equals(m.transpose())),
  '.tolist': matrixMethod((m) => new PyList(m.toArray().map((r) => new PyList(r)))),
};

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

export interface Case {
  fn: string;
  category: string;
  module: string;
  src: string;
  expected: string;
  args?: Tree[];
  kwargs?: Record<string, Tree>;
  self?: Tree;
  unsupportedArg?: string;
}

export type Outcome = { status: 'pass' } | { status: 'fail'; got: string } | { status: 'unsupported'; reason: string } | {
  status: 'error';
  reason: string;
};

export function runCase(c: Case): Outcome {
  if (c.unsupportedArg) return { status: 'unsupported', reason: `argument type ${c.unsupportedArg}` };
  const adapter = ADAPTERS[c.fn];
  if (!adapter) return { status: 'unsupported', reason: `no adapter for ${c.fn}` };
  try {
    const args = (c.args ?? []).map(deserialize);
    const kwargs = Object.fromEntries(Object.entries(c.kwargs ?? {}).map(([k, v]) => [k, deserialize(v)]));
    const self = c.self ? deserialize(c.self) : undefined;
    const v = adapter(args, kwargs, self);
    return matches(v, c.expected) ? { status: 'pass' } : { status: 'fail', got: fmt(v) };
  } catch (e) {
    if (e instanceof Unsupported) return { status: 'unsupported', reason: e.message };
    return { status: 'error', reason: e instanceof Error ? e.message : String(e) };
  }
}
