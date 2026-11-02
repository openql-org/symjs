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

import * as sj from '../packages/symjs/src';
import { Expr, ExprLike, Integral, Matrix, S, Sym } from '../packages/symjs/src';

// ---------------------------------------------------------------------------
// Python-like containers for formatting results
// ---------------------------------------------------------------------------

export class PyList {
  constructor(readonly items: readonly unknown[]) {}
}
export class PyTuple {
  constructor(
    readonly items: readonly unknown[],
    /** the Python value was a list */
    readonly isList = false,
  ) {}
}
export class PyDict {
  constructor(readonly entries: readonly (readonly [unknown, unknown])[]) {}
}
export class PyDefaultDict {
  constructor(readonly entries: readonly (readonly [unknown, unknown])[]) {}
}
export class PySet {
  constructor(readonly items: readonly unknown[]) {}
}

export class Unsupported extends Error {}

/** An undefined function class (SymPy `Function('f')` itself, not applied). */
export class UFnClass {
  constructor(readonly name: string) {}
}

/** A built-in SymPy function class such as `sin`. */
export class FnClass {
  constructor(readonly name: string) {}
}

/** A SymPy class object such as `Mul` or `Symbol`. */
export class TypeRef {
  constructor(readonly name: string) {}
}

export function fmt(v: unknown): string {
  if (v instanceof Expr) return sj.str(v);
  if (v instanceof Matrix) return v.toString();
  if (v instanceof sj.Poly) return v.toString();
  if (v instanceof sj.GroebnerBasis) return v.toString();
  if (v === -Infinity) return '-oo';
  if (typeof v === 'boolean') return v ? 'True' : 'False';
  if (v === null || v === undefined) return 'None';
  if (typeof v === 'number' || typeof v === 'bigint') return String(v);
  if (v === 'EmptySet') return 'EmptySet';
  if (typeof v === 'string') return `'${v}'`;
  if (v instanceof PyList) return `[${v.items.map(fmt).join(', ')}]`;
  if (v instanceof PyTuple) return v.items.length === 1 ? `(${fmt(v.items[0])},)` : `(${v.items.map(fmt).join(', ')})`;
  if (v instanceof PyDefaultDict) return `defaultdict(<class 'int'>, ${fmt(new PyDict(v.entries))})`;
  if (v instanceof PyDict) return `{${v.entries.map(([k, x]) => `${fmt(k)}: ${fmt(x)}`).join(', ')}}`;
  if (v instanceof PySet) return v.items.length === 0 ? 'set()' : `{${v.items.map(fmt).join(', ')}}`;
  if (v instanceof UFnClass || v instanceof FnClass) return v.name;
  if (v instanceof TypeRef) return `<class 'sympy.${v.name}'>`;
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
  const ddPrefix = "defaultdict(<class 'int'>, ";
  if (v instanceof PyDefaultDict && expected.startsWith(ddPrefix)) return matches(new PyDict(v.entries), expected.slice(ddPrefix.length, -1));
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

const SPECIAL_NAMES = ['bernoulli', 'euler', 'genocchi', 'bell', 'fibonacci', 'lucas', 'tribonacci', 'partition', 'totient', 'reduced_totient', 'mobius', 'divisor_sigma', 'primenu', 'primeomega', 'primepi', 'multigamma', 'factorial', 'factorial2', 'binomial', 'ff', 'rf', 'subfactorial', 'harmonic', 'catalan', 'gamma', 'loggamma', 'polygamma', 'lowergamma', 'uppergamma', 'beta', 'zeta', 'erf', 'erfc', 'erfi', 'erf2', 'erfinv', 'erfcinv', 'erf2inv', 'Ei', 'li', 'Li', 'Si', 'Ci', 'Shi', 'Chi', 'expint', 'fresnels', 'fresnelc', 'sign', 'floor', 'ceiling', 'atan2', 'Min', 'Max'] as const;

const FUNCTIONS: Record<string, (args: Expr[]) => Expr> = {
  ...Object.fromEntries(SPECIAL_NAMES.map((n) => [n, (args: Expr[]) => sj.fn(n, args)])),
  RisingFactorial: (args) => sj.fn('rf', args),
  FallingFactorial: (args) => sj.fn('ff', args),
  exp: ([a]) => sj.exp(a!),
  Abs: ([a]) => sj.abs(a!),
  ...Object.fromEntries(
    (['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 're', 'im', 'arg', 'conjugate', 'cot', 'sec', 'csc', 'acot', 'asec', 'acsc', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch', 'sinc', 'exp_polar', 'polar_lift', 'periodic_argument', 'principal_branch'] as const).map(
      (n) => [n, (args: Expr[]) => sj.fn(n, args)],
    ),
  ),
  Piecewise: (args) =>
    sj.piecewise(
      ...(args as unknown as PyTuple[]).map((t) => {
        const [e, c] = t.items;
        return [asExpr(e), typeof c === 'boolean' ? c : asExpr(c)] as const;
      }),
    ),
  Integral: (args) => integralNode(args),
  Sum: (args) => concreteNode('Sum', args),
  Product: (args) => concreteNode('Product', args),
  Limit: (args) => new sj.Limit(args as Expr[]),
  Order: ([e, ...rest]) => orderNode(e!, rest),
};

function integralNode(args: unknown[]): Expr {
  const [f, lim] = args;
  if (lim instanceof Sym) return new Integral([f as Expr, lim]);
  if (lim instanceof PyTuple && lim.items.length === 3) return new Integral([f as Expr, ...(lim.items as Expr[])]);
  if (lim instanceof PyTuple && lim.items.length === 1) return new Integral([f as Expr, lim.items[0] as Expr]);
  throw new Unsupported('Integral limits');
}

const concreteDoit = (e: Expr): Expr => (e instanceof sj.Concrete ? sj.doitConcrete(e) : e);

function concreteNode(kind: 'Sum' | 'Product', args: unknown[]): Expr {
  const [f, ...lims] = args;
  const ls = lims.map((l) => {
    if (!(l instanceof PyTuple) || l.items.length !== 3) throw new Unsupported('limits');
    return l.items as [Sym, Expr, Expr];
  });
  return kind === 'Sum' ? sj.Sum(f as Expr, ...ls) : sj.Product(f as Expr, ...ls);
}

function orderNode(e: unknown, rest: unknown[]): Expr {
  const r = rest[0];
  if (r === undefined) return sj.O(e as Expr);
  if (r instanceof PyTuple && r.items.length === 2) return sj.O(e as Expr, r.items[0] as Sym, r.items[1] as Expr);
  if (r instanceof Sym) return sj.O(e as Expr, r);
  throw new Unsupported('Order arguments');
}

export function deserialize(tree: Tree): unknown {
  switch (tree.t) {
    case 'Py':
      return tree['v'];
    case 'Str':
      return tree['v'];
    case 'Rational':
      return sj.Rational.of(BigInt(tree['p'] as string), BigInt(tree['q'] as string));
    case 'Float':
      if (tree['man'] !== undefined) {
        return new sj.Float({ man: BigInt(tree['man'] as string), exp: tree['exp'] as number }, tree['prec'] as number);
      }
      return new sj.Float(tree['v'] as number);
    case 'Symbol': {
      const a = tree['assume'] as Record<string, boolean>;
      for (const k of Object.keys(a)) {
        if (!['real', 'positive', 'nonnegative', 'integer', 'negative', 'nonpositive', 'commutative'].includes(k)) throw new Unsupported(`assumption ${k}`);
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
        EulerGamma: S.EulerGamma,
        Catalan: S.Catalan,
        GoldenRatio: S.GoldenRatio,
        TribonacciConstant: S.TribonacciConstant,
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
      return f((tree['args'] as Tree[]).map((a) => deserialize(a)) as Expr[]);
    }
    case 'Tuple':
      return new PyTuple((tree['items'] as Tree[]).map(deserialize), Boolean(tree['list']));
    case 'Poly':
      return sj.Poly.from(
        deserialize(tree['expr'] as Tree) as Expr,
        (tree['gens'] as Tree[]).map((g) => deserialize(g) as Expr),
        { domain: tree['domain'] as string, pure: Boolean(tree['pure']) },
      );
    case 'UFnClass':
      return new UFnClass(tree['name'] as string);
    case 'FnClass':
      return new FnClass(tree['name'] as string);
    case 'Interval':
      return sj.interval(deserialize(tree['a'] as Tree) as Expr, deserialize(tree['b'] as Tree) as Expr, tree['lo'] as boolean, tree['ro'] as boolean);
    case 'FiniteSet':
      return sj.finiteSet(...(tree['items'] as Tree[]).map((x) => deserialize(x) as Expr));
    case 'NamedSet':
      return ({ Reals: sj.Reals, Integers: sj.Integers, Naturals: sj.Naturals, Naturals0: sj.Naturals0, Complexes: sj.Complexes, EmptySet: sj.EmptySet } as Record<string, sj.SetExpr>)[tree['name'] as string];
    case 'SetOp': {
      const xs = (tree['args'] as Tree[]).map((x) => deserialize(x) as sj.SetExpr);
      if (tree['op'] === 'Union') return sj.union(...xs);
      if (tree['op'] === 'Intersection') return sj.intersection(...xs);
      return sj.complement(xs[0]!, xs[1]!);
    }
    case 'Groebner':
      return new sj.GroebnerBasis(
        (tree['exprs'] as Tree[]).map((e) => deserialize(e) as Expr),
        (tree['gens'] as Tree[]).map((g) => deserialize(g) as Sym),
        'ZZ',
        tree['order'] as sj.MonomialOrder,
      );
    case 'PySet':
      return new PySet((tree['items'] as Tree[]).map(deserialize));
    case 'BoolOp': {
      const xs = (tree['args'] as Tree[]).map((x) => deserialize(x) as Expr);
      return tree['op'] === 'And' ? sj.and(...xs) : sj.or(...xs);
    }
    case 'Type':
      return new TypeRef(tree['name'] as string);
    case 'Wild': {
      const a = tree['assume'] as Record<string, boolean>;
      return new sj.Wild(tree['name'] as string, { exclude: (tree['exclude'] as Tree[]).map((x) => deserialize(x) as Expr), ...a });
    }
    case 'WildFunction':
      return new sj.WildFunction(tree['name'] as string, (tree['nargs'] as number[] | null) ?? undefined);
    case 'Dummy': {
      const a = tree['assume'] as Record<string, boolean>;
      return new sj.Dummy(tree['name'] as string, a, 1_000_000 + (tree['index'] as number));
    }
    case 'UFn':
      return sj.Function(tree['name'] as string)(...(tree['args'] as Tree[]).map((a) => deserialize(a) as Expr));
    case 'Derivative':
      return sj.derivative(
        deserialize(tree['expr'] as Tree) as Expr,
        (tree['vc'] as [Tree, number][]).map(([v, n]) => [deserialize(v) as Expr, n] as [Expr, number]),
      );
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
const asExprOrPoly = (v: unknown): Expr => (v instanceof sj.Poly ? v.asExpr() : asExpr(v));
const asPoly = (v: unknown): sj.Poly => {
  if (v instanceof sj.Poly) return v;
  throw new Unsupported('expected a Poly');
};
const polyOf = (args: unknown[]): sj.Poly =>
  args[0] instanceof sj.Poly ? args[0] : sj.Poly.from(asExpr(args[0]), args.slice(1).map(asExpr));
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
  if (!rest.length) {
    const fs = [...sj.freeSymbols(e)];
    if (fs.length !== 1) throw new Unsupported('diff variable');
    return sj.diff(e, fs[0]!);
  }
  let out = e;
  for (let i = 0; i < rest.length; i++) {
    const v = asExpr(rest[i]);
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
  if (a instanceof PyDict) return sj.subs(e, new Map(a.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const)));
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

const HINTS = ['deep', 'mul', 'multinomial', 'power_exp', 'power_base', 'log', 'complex', 'trig', 'force', 'func'];
function expandHints(kw: Record<string, unknown>): sj.ExpandHints {
  for (const k of Object.keys(kw)) if (!HINTS.includes(k)) throw new Unsupported(`expand hint ${k}`);
  return Object.fromEntries(Object.entries(kw).map(([k, v]) => [k, Boolean(v)])) as sj.ExpandHints;
}

function asOrdered(e: Expr): Expr[] {
  return sj.orderedTerms(e);
}

function allSymbols(eqs: Expr[]): Sym[] {
  const m = new Map<string, Sym>();
  for (const e of eqs) for (const s of sj.freeSymbols(e)) m.set(s.key, s);
  return [...m.values()].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

function solveAug(aug: Matrix, syms: Sym[]): Expr[] | undefined {
  const n = syms.length;
  const [R, pivots] = sj.rref(aug);
  if (pivots.includes(n)) return undefined;
  const sol: Expr[] = syms.map((s) => s);
  pivots.forEach((pc, i) => {
    let v: Expr = R.get(i, n);
    for (let j = 0; j < n; j++) if (j !== pc && !pivots.includes(j)) v = sj.add(v, sj.mul(-1, R.get(i, j), syms[j]!));
    sol[pc] = sj.cancel(v);
  });
  return sol;
}

function idxList(v: unknown): (number | boolean)[] {
  if (!(v instanceof PyTuple)) throw new Unsupported('index list');
  return v.items.map((x) => (typeof x === 'boolean' ? x : Number((x as sj.Rational).p)));
}

function intArg(v: unknown): number {
  if (v instanceof sj.Rational && v.isInteger) return Number(v.p);
  if (typeof v === 'number' && Number.isInteger(v)) return v;
  throw new Unsupported('integer argument');
}

const asSet = (v: unknown): sj.SetExpr => {
  if (v instanceof sj.SetExpr) return v;
  throw new Unsupported('expected a set');
};
const typeMethod = (self: unknown, type: string, f: () => unknown, kw: Record<string, unknown>): unknown => {
  noKw(kw);
  if (!(self instanceof TypeRef && self.name === type)) throw new Unsupported(`classmethod of ${type}`);
  return f();
};
const monoAdapter =
  (f: (e: Expr, iv?: sj.SetExpr, x?: Sym) => boolean | undefined): Adapter =>
  (args, kw) => {
    noKw(kw);
    return f(asExpr(args[0]), (args[1] as sj.SetExpr | undefined) ?? sj.Reals, args[2] === undefined ? undefined : asSym(args[2])) ?? null;
  };
const autoKw = (kw: Record<string, unknown>): boolean => {
  for (const k of Object.keys(kw)) if (k !== 'auto') throw new Unsupported(`kwargs ${k}`);
  return kw['auto'] === undefined ? true : Boolean(kw['auto']);
};
const polyArg = (v: unknown): sj.Poly | Expr => (v instanceof sj.Poly ? v : asExpr(v));
const polyM =
  (f: (p: sj.Poly, args: unknown[]) => unknown): Adapter =>
  (args, kw, self) => {
    noKw(kw);
    return f(asPoly(self), args);
  };

function evalfAdapter(self: unknown, args: unknown[], kw: Record<string, unknown>): unknown {
  for (const k of Object.keys(kw)) if (!['subs', 'n', 'chop'].includes(k)) throw new Unsupported(`evalf kwarg ${k}`);
  const n = args.length ? intArg(args[0]) : kw['n'] !== undefined ? intArg(kw['n']) : 15;
  if (args.length > 1) throw new Unsupported('evalf args');
  const opts: sj.EvalfOptions = {};
  const subs = kw['subs'];
  if (subs !== undefined) {
    if (!(subs instanceof PyDict)) throw new Unsupported('evalf subs');
    opts.subs = new Map(subs.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
  }
  const chop = kw['chop'];
  if (chop !== undefined) opts.chop = typeof chop === "boolean" ? chop : asExpr(chop).toNumber();
  if (self instanceof Matrix) return self.evalf(n, opts);
  return asExpr(self).evalf(n, opts);
}

function toQuery(v: unknown): sj.Query {
  if (v instanceof FnClass && ['Function', 'AppliedUndef'].includes(v.name)) return { type: v.name };
  if (v instanceof FnClass || v instanceof UFnClass) return { fn: v.name };
  if (v instanceof TypeRef) return { type: v.name };
  if (v instanceof Expr) return v;
  throw new Unsupported('query');
}

function applyFn(name: string, args: Expr[]): Expr {
  const f = FUNCTIONS[name];
  if (f) return f(args);
  return sj.Function(name)(...args);
}

function matchDict(m: Map<Sym, Expr> | undefined): unknown {
  return m ? new PyDict([...m]) : null;
}

const FN_NAMES = ['sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'log', 're', 'im', 'arg', 'conjugate', 'cot', 'sec', 'csc', 'acot', 'asec', 'acsc', 'coth', 'sech', 'csch', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch', 'sinc'] as const;

export const ADAPTERS: Record<string, Adapter> = {
  N: (args, kw) => evalfAdapter(args[0], args.slice(1), kw),
  Float: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['dps', 'precision'].includes(k)) throw new Unsupported(`Float kwarg ${k}`);
    let num = args[0];
    if (num instanceof PyTuple) {
      const [sg, man, ex] = num.items.map((x) => (x as sj.Rational).p);
      if (num.items.length !== 3) throw new Unsupported('Float tuple');
      return new sj.Float({ man: sg ? -man! : man!, exp: Number(ex) }, 53);
    }
    const d = args[1] ?? kw['dps'];
    const dps = d === undefined ? undefined : typeof d === 'string' ? (d as '') : intArg(d);
    const precision = kw['precision'] !== undefined ? intArg(kw['precision']) : undefined;
    if (typeof num === 'string' || num instanceof Expr) return sj.float(num, dps, precision);
    throw new Unsupported('Float argument');
  },
  // ---- core constructors
  Function: (args, kw) => {
    noKw(kw);
    return new UFnClass(String(args[0]));
  },
  Derivative: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === true) {
      let e = asExpr(args[0]);
      for (const a of args.slice(1)) {
        if (a instanceof PyTuple) e = sj.diff(e, asExpr(a.items[0]), Number((a.items[1] as sj.Rational).p));
        else e = sj.diff(e, asExpr(a));
      }
      return e;
    }
    const e = asExpr(args[0]);
    const vc: [Expr, number][] = [];
    for (const a of args.slice(1)) {
      if (a instanceof PyTuple) vc.push([asExpr(a.items[0]), Number((a.items[1] as sj.Rational).p)]);
      else vc.push([asExpr(a), 1]);
    }
    return sj.derivative(e, vc);
  },
  symbols: (args, kw) => {
    const a: Record<string, boolean> = {};
    let seq = false;
    for (const [k, v] of Object.entries(kw)) {
      if (k === 'seq') {
        seq = Boolean(v);
        continue;
      }
      if (k === 'commutative' && v === false) {
        a[k] = false;
        continue;
      }
      if (!['real', 'positive', 'nonnegative', 'integer', 'negative', 'nonpositive'].includes(k) || v !== true) throw new Unsupported(`symbols ${k}`);
      a[k] = true;
    }
    const one = (spec: string): unknown => {
      const names = sj.expandSymbolNames(spec);
      const syms = names.map((n) => new Sym(n, a));
      const isSeq = seq || spec.includes(',') || spec.trim().includes(' ') || spec.includes(':');
      return syms.length === 1 && !isSeq ? syms[0] : new PyTuple(syms);
    };
    const first = args[0];
    if (first instanceof PyList || (first instanceof PyTuple && first.isList)) return new PyList((first as PyTuple).items.map((s) => one(String(s))));
    if (first instanceof PyTuple) return new PyTuple(first.items.map((s) => one(String(s))));
    return one(String(first));
  },
  Rel: (args, kw) => {
    noKw(kw);
    const op = args[2] === undefined || args[2] === null ? '==' : String(args[2]);
    const map: Record<string, sj.RelOp> = {
      '==': 'Eq', eq: 'Eq', '!=': 'Ne', ne: 'Ne', '<>': 'Ne', '<': 'Lt', lt: 'Lt', '<=': 'Le', le: 'Le', '>': 'Gt', gt: 'Gt', '>=': 'Ge', ge: 'Ge',
    };
    const o = map[op];
    if (!o) throw new Unsupported(`Rel op ${op}`);
    return sj.rel(o, asExpr(args[0]), asExpr(args[1]));
  },
  integer_log: (args, kw) => {
    noKw(kw);
    const [e, t] = sj.integerLog((asExpr(args[0]) as sj.Rational).p, (asExpr(args[1]) as sj.Rational).p);
    return new PyTuple([sj.Rational.of(e), t]);
  },
  Symbol: (args, kw) => {
    const a: Record<string, boolean> = {};
    for (const [k, v] of Object.entries(kw)) {
      if (!['real', 'positive', 'nonnegative', 'integer', 'negative', 'nonpositive', 'commutative'].includes(k) || v !== true) throw new Unsupported(`Symbol ${k}`);
      a[k] = true;
    }
    return new Sym(String(args[0]), a);
  },
  sympify: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'rational' && !(k === 'evaluate' && kw[k] === true)) throw new Unsupported(`kwargs ${k}`);
    const v = args[0];
    if (typeof v === 'string') {
      if (kw['rational'] === true) {
        // decimal literals become exact rationals
        return sj.parse(v.replace(/\d*\.\d+(?:[eE][+-]?\d+)?/g, (m) => `(${sj.str(sj.rationalFromString(m))})`));
      }
      return sj.parse(v);
    }
    if (v instanceof PyTuple) return new PyList(v.items.map((i) => (typeof i === 'string' ? sj.parse(i) : asExpr(i))));
    return asExpr(v);
  },
  S: (args, kw) => ADAPTERS['sympify']!(args, kw),
  Rational: (args, kw) => {
    noKw(kw);
    const conv = (v: unknown): Expr =>
      typeof v === 'string' ? sj.rationalFromString(v) : v instanceof sj.Float ? sj.rationalFromFloat(v.value) : asExpr(v);
    const [p, q] = args.map(conv);
    return q ? sj.div(p!, q) : p;
  },
  Integer: (args, kw) => {
    noKw(kw);
    const v = args[0];
    if (typeof v === 'string') return sj.Rational.of(BigInt(v));
    const e = asExpr(v);
    if (e instanceof sj.Float) return sj.Rational.of(BigInt(Math.trunc(e.value)));
    if (!(e instanceof sj.Rational && e.isInteger)) throw new Unsupported('Integer');
    return e;
  },
  Add: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === false) return new sj.Add(args.map(asExpr));
    return sj.add(...args.map(asExpr));
  },
  Mul: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === false) {
      if (args.every((a) => a instanceof sj.Rational)) throw new Unsupported('unevaluated numeric product');
      return new sj.Mul(args.map(asExpr));
    }
    return sj.mul(...args.map(asExpr));
  },
  Interval: (args, kw) => (noKw(kw), sj.interval(asExpr(args[0]), asExpr(args[1]), Boolean(args[2]), Boolean(args[3]))),
  FiniteSet: (args, kw) => (noKw(kw), sj.finiteSet(...args.map(asExpr))),
  Union: (args, kw) => (noKw(kw), sj.union(...args.map(asSet))),
  Intersection: (args, kw) => (noKw(kw), sj.intersection(...args.map(asSet))),
  Complement: (args, kw) => (noKw(kw), sj.complement(asSet(args[0]), asSet(args[1]))),
  '.open': (args, kw, self) => typeMethod(self, 'Interval', () => sj.interval(asExpr(args[0]), asExpr(args[1]), true, true), kw),
  '.Lopen': (args, kw, self) => typeMethod(self, 'Interval', () => sj.interval(asExpr(args[0]), asExpr(args[1]), true, false), kw),
  '.Ropen': (args, kw, self) => typeMethod(self, 'Interval', () => sj.interval(asExpr(args[0]), asExpr(args[1]), false, true), kw),
  '.contains': (args, kw, self) => (noKw(kw), self instanceof sj.GroebnerBasis ? self.contains(asExpr(args[0])) : sj.contains(asSet(self), asExpr(args[0]))),
  '.intersect': (args, kw, self) => (noKw(kw), sj.intersection(asSet(self), asSet(args[0]))),
  '.union': (args, kw, self) => (noKw(kw), sj.union(asSet(self), asSet(args[0]))),
  '.is_subset': (args, kw, self) => (noKw(kw), sj.isSubset(asSet(self), asSet(args[0])) ?? null),
  '.as_relational': (args, kw, self) => (noKw(kw), sj.asRelational(asSet(self), asExpr(args[0]))),
  solveset: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    const dom = (kw['domain'] ?? args[2]) as sj.SetExpr | undefined;
    const f = asExpr(args[0]);
    const x = args[1] ? asSym(args[1]) : (sj.freeSymbols(f).values().next().value as Sym);
    return sj.solveset(f, x, dom ?? sj.Complexes);
  },
  solve_univariate_inequality: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['relational', 'domain'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const rel = kw['relational'] ?? args[2];
    const dom = (kw['domain'] ?? args[3]) as sj.SetExpr | undefined;
    return sj.solveUnivariateInequality(asExpr(args[0]), asSym(args[1]), { relational: rel === undefined ? true : Boolean(rel), domain: dom });
  },
  solve_poly_inequality: (args, kw) => (noKw(kw), new PyList(sj.solvePolyInequality(asPoly(args[0]), args[1] as string))),
  solve_rational_inequalities: (args, kw) => {
    noKw(kw);
    const groups = (args[0] as PyList).items.map((g) =>
      (g as PyList).items.map((it) => {
        const [nd, rel] = (it as PyTuple).items as [PyTuple, string];
        return [[asPoly(nd.items[0]), asPoly(nd.items[1])], rel] as [[sj.Poly, sj.Poly], string];
      }),
    );
    return sj.solveRationalInequalities(groups);
  },
  reduce_inequalities: (args, kw) => {
    noKw(kw);
    const a = args[0];
    const ineqs = a instanceof PyList || a instanceof PyTuple ? a.items.map(asExpr) : [asExpr(a)];
    const syms = args[1] instanceof PyList || args[1] instanceof PyTuple ? args[1].items.map(asSym) : [];
    return sj.reduceInequalities(ineqs, syms);
  },
  periodicity: (args, kw) => (noKw(kw), sj.periodicity(asExpr(args[0]), asSym(args[1])) ?? null),
  singularities: (args, kw) => (noKw(kw), sj.singularities(asExpr(args[0]), asSym(args[1]), args[2] as sj.SetExpr | undefined)),
  stationary_points: (args, kw) => (noKw(kw), sj.stationaryPoints(asExpr(args[0]), asSym(args[1]), (args[2] as sj.SetExpr | undefined) ?? sj.Reals)),
  maximum: (args, kw) => (noKw(kw), sj.maximum(asExpr(args[0]), asSym(args[1]), (args[2] as sj.SetExpr | undefined) ?? sj.Reals)),
  minimum: (args, kw) => (noKw(kw), sj.minimum(asExpr(args[0]), asSym(args[1]), (args[2] as sj.SetExpr | undefined) ?? sj.Reals)),
  is_increasing: monoAdapter(sj.isIncreasing),
  is_strictly_increasing: monoAdapter(sj.isStrictlyIncreasing),
  is_decreasing: monoAdapter(sj.isDecreasing),
  is_strictly_decreasing: monoAdapter(sj.isStrictlyDecreasing),
  is_monotonic: monoAdapter(sj.isMonotonic),
  is_convex: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    if (args.length > 2) throw new Unsupported('multivariate convexity');
    return sj.isConvex(asExpr(args[0]), asSym(args[1]), (kw['domain'] as sj.SetExpr | undefined) ?? sj.Reals);
  },
  isprime: (args, kw) => (noKw(kw), sj.isprime(asExpr(args[0]))),
  jacobi_symbol: (args, kw) => (noKw(kw), sj.jacobiSymbol((args[0] as sj.Rational).p, (args[1] as sj.Rational).p)),
  kronecker_symbol: (args, kw) => (noKw(kw), sj.kroneckerSymbol((args[0] as sj.Rational).p, (args[1] as sj.Rational).p)),
  '.piecewise_integrate': (args, kw, self) => (noKw(kw), sj.piecewiseIntegrate(self as sj.Piecewise, asSym(args[0]))),
  '.as_expr_set_pairs': (args, kw, self) =>
    (noKw(kw), new PyList(sj.asExprSetPairs(asExpr(self), (args[0] as sj.SetExpr | undefined) ?? sj.Reals).map(([e, st]) => new PyTuple([e, st])))),
  piecewise_fold: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    const fold = (x: Expr): Expr => {
      const a = x.args.map(fold);
      const y = a.every((v, i) => v === x.args[i]) ? x : sj.rebuild(x, a);
      if ((y instanceof sj.Add || y instanceof sj.Mul) && y.args.filter((t) => t instanceof sj.Piecewise).length === 1) {
        const pw = y.args.find((t) => t instanceof sj.Piecewise) as sj.Piecewise;
        const others = y.args.filter((t) => t !== pw);
        const op = y instanceof sj.Add ? sj.add : sj.mul;
        return sj.piecewise(...pw.pairs.map(([v, c]) => [op(...others, v), c] as const));
      }
      return y;
    };
    return fold(e);
  },
  invert: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'integer_power') throw new Unsupported(`kwargs ${k}`);
    const syms = args.slice(1).filter((a) => a instanceof Sym) as Sym[];
    if (args.length === 2 && !(args[1] instanceof Sym)) {
      const f = asExpr(args[0]);
      const g = asExpr(args[1]);
      const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]);
      return sj.Poly.from(f, gens).invert(sj.Poly.from(g, gens)).asExpr();
    }
    return new PyTuple(sj.invertEquation(asExpr(args[0]), syms, { integerPower: Boolean(kw['integer_power']) }));
  },
  '.invert': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Rational && args[0] instanceof sj.Rational) return sj.modInverse(self, args[0]);
    if (self instanceof sj.Poly) return self.invert(args[0] as sj.Poly);
    throw new Unsupported('invert');
  },
  groebner: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['order', 'method'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const F = (args[0] as PyList).items.map(asExpr);
    const gens = args.slice(1).map(asSym);
    return sj.groebner(F, gens.length ? gens : (sj.sortGens([...sj.freeSymbols(sj.add(...F))]) as Sym[]), (kw['order'] as sj.MonomialOrder | undefined) ?? 'lex');
  },
  '.reduce': (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.GroebnerBasis)) throw new Unsupported('reduce');
    const isPoly = args[0] instanceof sj.Poly;
    const [qs, r] = self.reduce(isPoly ? (args[0] as sj.Poly).asExpr() : asExpr(args[0]));
    const wrap = (e: Expr) => (isPoly ? sj.Poly.from(e, self.gens, { domain: 'ZZ' }) : e);
    return new PyTuple([new PyList(qs.map(wrap)), wrap(r)]);
  },
  symmetrize: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'formal') throw new Unsupported(`kwargs ${k}`);
    const gens = args.slice(1).map(asSym);
    if (kw['formal']) {
      const [s, r, m] = sj.symmetrize(asExpr(args[0]), gens);
      return new PyTuple([s, r, new PyList(m.map(([a, b]) => new PyTuple([a, b])))]);
    }
    return new PyTuple(sj.symmetrizeExpr(asExpr(args[0]), gens));
  },
  separatevars: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['symbols', 'dict', 'force'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const symsArg = kw['symbols'] ?? args[1];
    const symbols = symsArg instanceof PyTuple || symsArg instanceof PyList ? symsArg.items.map(asSym) : [];
    const r = sj.separatevars(asExpr(args[0]), { symbols, dict: Boolean(kw['dict']), force: Boolean(kw['force']) });
    if (r === undefined) return null;
    if (r instanceof Map) return new PyDict([...r].map(([k, v]) => [k, v] as const));
    return r;
  },
  apart: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'full' || kw[k]) throw new Unsupported(`kwargs ${k}`);
    return sj.apart(asExpr(args[0]), args[1] === undefined ? undefined : asSym(args[1]));
  },
  exp_polar: (args, kw) => (noKw(kw), sj.expPolar(asExpr(args[0]))),
  polar_lift: (args, kw) => (noKw(kw), sj.polarLift(asExpr(args[0]))),
  periodic_argument: (args, kw) => (noKw(kw), sj.periodicArgument(asExpr(args[0]), asExpr(args[1]))),
  principal_branch: (args, kw) => (noKw(kw), sj.principalBranch(asExpr(args[0]), asExpr(args[1]))),
  unbranched_argument: (args, kw) => (noKw(kw), sj.unbranchedArgument(asExpr(args[0]))),
  unpolarify: (args, kw) => (noKw(kw), sj.unpolarify(asExpr(args[0]))),
  '.extract_branch_factor': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'allow_half') throw new Unsupported(`kwargs ${k}`);
    return new PyTuple(sj.extractBranchFactor(asExpr(self), Boolean(kw['allow_half'])));
  },
  frac: exprFn(sj.frac),
  nsimplify: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['tolerance', 'rational', 'rational_conversion'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (args.length > 1) throw new Unsupported('nsimplify constants');
    return sj.nsimplify(asExpr(args[0]), {
      tolerance: kw['tolerance'] === undefined ? undefined : asExpr(kw['tolerance']).toNumber(),
      rational: kw['rational'] as boolean | undefined,
      rationalConversion: kw['rational_conversion'] as 'base10' | 'exact' | undefined,
    });
  },
  sqrtdenest: exprFn(sj.sqrtdenest),
  '.extract_leading_order': (args, kw, self) =>
    (noKw(kw), new PyTuple(sj.extractLeadingOrder(asExpr(self), asSym(args[0])).map(([a, b]) => new PyTuple([a, b])))),
  '.as_finite_difference': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (!['points', 'x0', 'wrt'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (!(self instanceof sj.Derivative)) throw new Unsupported('as_finite_difference');
    const pts = kw['points'] ?? args[0];
    const points = pts === undefined ? 1 : pts instanceof PyList || pts instanceof PyTuple ? pts.items.map(asExpr) : asExpr(pts);
    const x0 = kw['x0'] ?? args[1];
    return sj.asFiniteDifference(self, points, x0 === undefined ? undefined : asExpr(x0), kw['wrt'] === undefined ? undefined : asSym(kw['wrt']));
  },
  '.pinv_solve': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'arbitrary_matrix') throw new Unsupported(`kwargs ${k}`);
    return sj.pinvSolve(self as Matrix, args[0] as Matrix, kw['arbitrary_matrix'] as Matrix | undefined);
  },
  '.is_meromorphic': (args, kw, self) => (noKw(kw), sj.isMeromorphic(asExpr(self), asExpr(args[0]), asExpr(args[1])) ?? null),
  ratsimp: exprFn(sj.ratsimp),
  primitive: (args, kw) => {
    noKw(kw);
    const p = polyOf(args);
    const [c, q] = p.primitive();
    return new PyTuple([c, q.asExpr()]);
  },
  content: (args, kw) => (noKw(kw), polyOf(args).content()),
  pquo: (args, kw) => {
    noKw(kw);
    const f = asExpr(args[0]);
    const g = asExpr(args[1]);
    const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]);
    return sj.Poly.from(f, gens).pquo(sj.Poly.from(g, gens)).asExpr();
  },
  exquo: (args, kw) => {
    noKw(kw);
    const f = asExpr(args[0]);
    const g = asExpr(args[1]);
    const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]);
    return sj.Poly.from(f, gens).exquo(sj.Poly.from(g, gens)).asExpr();
  },
  cofactors: (args, kw) => {
    noKw(kw);
    const f = asExpr(args[0]);
    const g = asExpr(args[1]);
    const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]);
    return new PyTuple(sj.Poly.from(f, gens).cofactors(sj.Poly.from(g, gens)).map((p) => p.asExpr()));
  },
  compose: (args, kw) => {
    noKw(kw);
    const f = asExpr(args[0]);
    const g = asExpr(args[1]);
    const gens = sj.sortGens([...sj.freeSymbols(sj.add(f, g))]);
    return sj.Poly.from(f, gens).compose(sj.Poly.from(g, gens)).asExpr();
  },
  decompose: (args, kw) => (noKw(kw), new PyList(polyOf(args).decompose().map((p) => p.asExpr()))),
  '.decompose': polyM((p) => new PyList(p.decompose())),
  degree_list: (args, kw) => (noKw(kw), new PyTuple(polyOf(args).degreeList())),
  '.retract': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'field') throw new Unsupported(`kwargs ${k}`);
    return asPoly(self).retract(Boolean(kw['field']));
  },
  nroots: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'n') throw new Unsupported(`kwargs ${k}`);
    const n = kw['n'] ?? args[1];
    return new PyList(sj.nroots(args[0] instanceof sj.Poly ? args[0] : asExpr(args[0]), n === undefined ? 15 : intArg(n)));
  },
  '.nroots': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'n') throw new Unsupported(`kwargs ${k}`);
    const n = kw['n'] ?? args[0];
    return new PyList(sj.nroots(asPoly(self), n === undefined ? 15 : intArg(n)));
  },
  '.is_convergent': (_args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.Concrete)) throw new Unsupported('is_convergent');
    return sj.sumIsConvergent(self) ?? null;
  },
  '.is_absolutely_convergent': (_args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.Concrete)) throw new Unsupported('is_absolutely_convergent');
    return sj.sumIsAbsolutelyConvergent(self) ?? null;
  },
  '.as_sum': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'method') throw new Unsupported(`kwargs ${k}`);
    if (!(self instanceof Integral) || !self.limits) throw new Unsupported('as_sum');
    const n = args[0];
    if (!(n instanceof sj.Rational)) throw new Unsupported('symbolic as_sum');
    const method = (kw['method'] ?? args[1] ?? 'midpoint') as string;
    const [a, b] = self.limits as [Expr, Expr];
    const dx = sj.mul(sj.add(b, sj.mul(-1, a)), sj.pow(n, -1));
    const terms: Expr[] = [];
    const N = Number(n.p);
    for (let i = 0; i < N; i++) {
      let pt: Expr;
      if (method === 'left') pt = sj.add(a, sj.mul(i, dx));
      else if (method === 'right') pt = sj.add(a, sj.mul(i + 1, dx));
      else if (method === 'midpoint') pt = sj.add(a, sj.mul(sj.Rational.of(2 * i + 1, 2), dx));
      else throw new Unsupported(`as_sum method ${method}`);
      terms.push(sj.xreplace(self.integrand, [[self.variable, pt]]));
    }
    return sj.mul(dx, sj.add(...terms));
  },
  igcd: (args, kw) => (noKw(kw), sj.Rational.of(sj.igcd(...args.map((a) => (a as sj.Rational).p)))),
  ilcm: (args, kw) => (noKw(kw), sj.Rational.of(sj.ilcm(...args.map((a) => (a as sj.Rational).p)))),
  integer_nthroot: (args, kw) => {
    noKw(kw);
    const [r, ok] = sj.integerNthroot((args[0] as sj.Rational).p, intArg(args[1]));
    return new PyTuple([sj.Rational.of(r), ok]);
  },
  trailing: (args, kw) => (noKw(kw), sj.trailing((args[0] as sj.Rational).p)),
  num_digits: (args, kw) => (noKw(kw), sj.numDigits((args[0] as sj.Rational).p, args[1] === undefined ? 10 : intArg(args[1]))),
  mod_inverse: (args, kw) => (noKw(kw), sj.modInverse(args[0] as sj.Rational, args[1] as sj.Rational)),
  prod: (args, kw) => {
    noKw(kw);
    const xs = args[0] instanceof PyList || args[0] instanceof PyTuple ? args[0].items.map(asExpr) : [];
    return sj.mul(args[1] === undefined ? 1 : asExpr(args[1]), ...xs);
  },
  nfloat: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['n', 'exponent'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.nfloat(asExpr(args[0]), kw['n'] === undefined ? 15 : intArg(kw['n']), Boolean(kw['exponent']));
  },
  comp: (args, kw) => {
    noKw(kw);
    const tol = args[2] === undefined ? undefined : args[2] === '' ? ('' as const) : asExpr(args[2]).toNumber();
    return sj.comp(asExpr(args[0]), asExpr(args[1]), tol);
  },
  var: (args, kw) => ADAPTERS['symbols']!(args, kw),
  '.limit_denominator': (args, kw, self) => (noKw(kw), sj.limitDenominator(self as sj.Rational, (args[0] as sj.Rational).p)),
  '.as_two_terms': exprMethod((e) => new PyTuple(sj.asTwoTerms(e))),
  '.has_xfree': (args, kw, self) => (noKw(kw), sj.hasXfree(asExpr(self), (args[0] as PySet).items.filter((i) => !(i instanceof UFnClass)).map(asExpr))),
  '.is_algebraic_expr': (args, kw, self) => (noKw(kw), sj.isAlgebraicExpr(asExpr(self), args.map(asExpr))),
  '.dummy_eq': (args, kw, self) => (noKw(kw), sj.dummyEq(asExpr(self), asExpr(args[0]), args[1] === undefined ? undefined : asExpr(args[1]))),
  '.compare': (args, kw, self) => (noKw(kw), Math.sign(sj.compareKeys(sj.sortKey(asExpr(self)), sj.sortKey(asExpr(args[0]))))),
  '.could_extract_minus_sign': exprMethod((e) => sj.couldExtractMinusSign(e)),
  '.as_ordered_factors': exprMethod((e) => new PyList(sj.orderedFactors ? sj.orderedFactors(e) : [e])),
  '.leadterm': (args, kw, self) => (noKw(kw), new PyTuple(sj.leadterm(asExpr(self), asSym(args[0])))),
  '.as_leading_term': (args, kw, self) => (noKw(kw), sj.asLeadingTerm(asExpr(self), asSym(args[0]))),
  '.getn': exprMethod((e) => sj.getn(e) ?? null),
  '.nseries': (args, kw, self) => {
    noKw(kw);
    return sj.series(asExpr(self), asSym(args[0]), args[1] === undefined ? 0 : asExpr(args[1]), args[2] === undefined ? 6 : intArg(args[2]));
  },
  root: (args, kw) => (noKw(kw), sj.root(asExpr(args[0]), asExpr(args[1]), args[2] === undefined ? 0 : asExpr(args[2]))),
  cbrt: exprFn(sj.cbrt),
  real_root: (args, kw) => (noKw(kw), sj.realRoot(asExpr(args[0]), asExpr(args[1]))),
  '.has_free': (args, kw, self) => {
    noKw(kw);
    return sj.hasFree(asExpr(self), ...args.map((a) => (a instanceof UFnClass ? { fn: a.name } : asExpr(a))));
  },
  '.as_coefficients_dict': (args, kw, self) => {
    noKw(kw);
    return new PyDefaultDict(sj.asCoefficientsDict(asExpr(self), args.map(asExpr)));
  },
  Pow: (args, kw) => (noKw(kw), sj.pow(asExpr(args[0]), asExpr(args[1]))),
  sqrt: exprFn(sj.sqrt),
  ...Object.fromEntries(
    SPECIAL_NAMES.map((n) => [
      n,
      ((args, kw) => {
        noKw(kw);
        return sj.fn(n, args.flatMap((a) => (a instanceof PyTuple ? a.items.map(asExpr) : [asExpr(a)])));
      }) as Adapter,
    ]),
  ),
  digamma: exprFn(sj.digamma),
  trigamma: exprFn(sj.trigamma),
  E1: exprFn(sj.E1),
  RisingFactorial: (args, kw) => (noKw(kw), sj.rf(asExpr(args[0]), asExpr(args[1]))),
  FallingFactorial: (args, kw) => (noKw(kw), sj.ff(asExpr(args[0]), asExpr(args[1]))),
  expand_func: exprFn(sj.expandFunc),
  conjugate: exprFn(sj.conjugate),
  exp: exprFn(sj.exp),
  Abs: exprFn(sj.abs),
  ...Object.fromEntries(FN_NAMES.map((n) => [n, exprFn((e) => sj.fn(n, [e]))])),
  Eq: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    if (kw['evaluate'] === false) return new sj.Rel('Eq', asExpr(args[0]), asExpr(args[1] ?? 0));
    return sj.Eq(asExpr(args[0]), asExpr(args[1] ?? 0));
  },
  StrictGreaterThan: (args, kw) => (noKw(kw), sj.Gt(asExpr(args[0]), asExpr(args[1]))),
  GreaterThan: (args, kw) => (noKw(kw), sj.Ge(asExpr(args[0]), asExpr(args[1]))),
  StrictLessThan: (args, kw) => (noKw(kw), sj.Lt(asExpr(args[0]), asExpr(args[1]))),
  LessThan: (args, kw) => (noKw(kw), sj.Le(asExpr(args[0]), asExpr(args[1]))),
  Ne: (args, kw) => (noKw(kw), sj.Ne(asExpr(args[0]), asExpr(args[1]))),
  Lt: (args, kw) => (noKw(kw), sj.Lt(asExpr(args[0]), asExpr(args[1]))),
  Le: (args, kw) => (noKw(kw), sj.Le(asExpr(args[0]), asExpr(args[1]))),
  Gt: (args, kw) => (noKw(kw), sj.Gt(asExpr(args[0]), asExpr(args[1]))),
  Ge: (args, kw) => (noKw(kw), sj.Ge(asExpr(args[0]), asExpr(args[1]))),

  // ---- manipulation
  expand: (args, kw) => {
    if (args.length !== 1) throw new Unsupported('arity');
    return sj.expand(asExpr(args[0]), expandHints(kw));
  },
  expand_mul: exprFn(sj.expand_mul),
  expand_multinomial: exprFn(sj.expand_multinomial),
  expand_log: (args, kw) => sj.expand_log(asExpr(args[0]), Boolean(kw['force'])),
  expand_power_exp: exprFn((e) => sj.expand_power_exp(e)),
  expand_power_base: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'force' && k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    return sj.expand_power_base(asExpr(args[0]), kw as { force?: boolean; deep?: boolean });
  },
  expand_trig: exprFn(sj.expand_trig),
  expand_complex: exprFn(sj.expand_complex),
  simplify: exprFn(sj.simplify),
  factor: exprFn(sj.factor),
  together: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    return sj.together(asExpr(args[0]), { deep: Boolean(kw['deep']) });
  },
  cancel: exprFn(sj.cancel),
  trigsimp: exprFn(sj.trigsimp),
  powsimp: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['deep', 'combine', 'force'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.powsimp(asExpr(args[0]), {
      deep: (kw['deep'] ?? args[1]) as boolean | undefined,
      combine: kw['combine'] as 'all' | 'exp' | 'base' | undefined,
      force: kw['force'] as boolean | undefined,
    });
  },
  powdenest: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'force') throw new Unsupported(`kwargs ${k}`);
    return sj.powdenest(asExpr(args[0]), { force: Boolean(kw['force'] ?? args[1]) });
  },
  logcombine: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'force') throw new Unsupported(`kwargs ${k}`);
    return sj.logcombine(asExpr(args[0]), { force: Boolean(kw['force'] ?? args[1]) });
  },
  posify: (args, kw) => {
    noKw(kw);
    const [e, m] = sj.posify(asExpr(args[0]));
    return new PyTuple([e, new PyDict([...m])]);
  },
  radsimp: exprFn(sj.radsimp),
  collect: (args, kw) => {
    const exact = kw['exact'];
    for (const k of Object.keys(kw)) if (k !== 'exact') throw new Unsupported(`kwargs ${k}`);
    if (args.length !== 2) throw new Unsupported('collect arity');
    const syms = args[1] instanceof PyTuple ? args[1].items.map(asExpr) : [asExpr(args[1])];
    return sj.collect(asExpr(args[0]), syms, exact === undefined ? {} : { exact: Boolean(exact) });
  },
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
    const e = asExprOrPoly(args[0]);
    const syms = [...sj.freeSymbols(e)];
    const x = args[1] ? asSym(args[1]) : args[0] instanceof sj.Poly ? (args[0].gens[0] as Sym) : syms.length === 1 ? syms[0]! : undefined;
    if (!x) throw new Unsupported('roots generator');
    return rootsDict(sj.roots(e, x, { skipQuintic: true }));
  },
  solve: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'check') throw new Unsupported(`kwargs ${k}`);
    const check = kw['check'] === undefined ? undefined : Boolean(kw['check']);
    const first = args[0];
    // systems of equations
    if (first instanceof PyTuple) {
      const eqs = first.items.map(asExpr);
      const syms = args[1] instanceof PyTuple ? args[1].items.map(asSym) : args.slice(1).map(asSym);
      const vars = syms.length ? syms : allSymbols(eqs);
      if (sj.linearEqToMatrix(eqs, vars)) {
        const s = sj.linsolve(eqs, vars);
        if (!s) return new PyList([]);
        // underdetermined: SymPy lists only the solved (pivot) symbols
        return new PyDict(vars.map((v, i) => [v, s[i]!] as const).filter(([v, e]) => v.key !== e.key));
      }
      const sols = sj.nonlinsolve(eqs, vars);
      return new PyList(sols.map((t) => new PyDict(vars.map((v, i) => [v, t[i]!] as const))));
    }
    if (first instanceof PyList && first.items.some((i) => i instanceof sj.Rel && i.op !== 'Eq')) {
      const syms = args.slice(1).filter((a) => a instanceof Sym) as Sym[];
      if (first.items.some((i) => !(i instanceof sj.Rel) || i.op === 'Eq')) throw new Unsupported('mixed system');
      return sj.reduceInequalities(first.items.map(asExpr), syms);
    }
    const e = first instanceof sj.Poly ? first.asExpr() : asExpr(first);
    if (e instanceof sj.Rel && e.op !== 'Eq' && e.op !== 'Ne') {
      return sj.reduceInequalities([e], args[1] instanceof Sym ? [args[1]] : []);
    }
    if (args[1] instanceof PyTuple) {
      // a single equation in several unknowns with other free symbols: undetermined coefficients
      const coeffs = args[1].items.map(asSym);
      const others = [...sj.freeSymbols(e)].filter((s) => !coeffs.some((c) => c.key === s.key));
      if (!others.length) throw new Unsupported('solve for several symbols');
      const sols = sj.solveUndeterminedCoeffs(e, coeffs, others as Sym[]);
      if (sols.length !== 1) throw new Unsupported('solve for several symbols');
      return new PyDict(coeffs.map((c, i) => [c, sols[0]![i]!] as const));
    }
    const syms = [...sj.freeSymbols(e)];
    const x =
      args[1] instanceof Sym
        ? args[1]
        : args[1] instanceof Expr && !(args[1] instanceof sj.Rational)
          ? (args[1] as Sym)
          : args.length === 1 && syms.length === 1
            ? syms[0]!
            : undefined;
    if (args.length === 1 && syms.length === 0) return new PyList([]);
    if (!x || args.length > 2) throw new Unsupported('solve form');
    return new PyList(sj.solve(e, x, check === undefined ? {} : { check }));
  },
  checksol: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    let reps: [Expr, Expr][];
    if (args[1] instanceof PyDict) reps = args[1].entries.map(([k, v]) => [asExpr(k), asExpr(v)]);
    else reps = [[asExpr(args[1]), asExpr(args[2])]];
    const v = sj.simplify(sj.subs(e, new Map(reps)));
    if (v instanceof sj.Rational) return v.isZero;
    if (v.freeSymbols().size === 0) {
      const c = v.toComplex();
      return Math.abs(c.re) < 1e-12 && Math.abs(c.im) < 1e-12;
    }
    return null;
  },
  linsolve: (args, kw) => {
    noKw(kw);
    const first = args[0];
    const syms = args[1] instanceof PyTuple ? args[1].items.map(asSym) : args.slice(1).map(asSym);
    let sol: Expr[] | undefined;
    if (first instanceof PyTuple && first.items.length === 2 && first.items[0] instanceof Matrix) {
      const [A, b] = first.items as [Matrix, Matrix];
      if (!syms.length) throw new Unsupported('linsolve without symbols');
      sol = solveAug(A.hstack(b), syms);
    } else if (first instanceof Matrix) {
      sol = solveAug(first, syms);
    } else if (first instanceof PyTuple) {
      if (first.items.length === 0) return 'EmptySet';
      sol = sj.linsolve(first.items.map(asExpr), syms);
    } else throw new Unsupported('linsolve form');
    return sol ? new PySet([new PyTuple(sol)]) : 'EmptySet';
  },
  nonlinsolve: (args, kw) => {
    noKw(kw);
    const eqs = (args[0] as PyTuple).items.map(asExpr);
    const syms = (args[1] as PyTuple).items.map(asSym);
    const sols = sj.nonlinsolve(eqs, syms);
    return sols.length ? new PySet(sols.map((t) => new PyTuple(t))) : 'EmptySet';
  },
  solve_linear: (args, kw) => {
    const opts: { symbols?: Sym[]; exclude?: Sym[] } = {};
    if (kw['symbols']) opts.symbols = (kw['symbols'] as PyTuple).items.map(asSym);
    if (kw['exclude']) opts.exclude = (kw['exclude'] as PyTuple).items.map(asSym);
    if (args.length > 1) opts.symbols = args.slice(1).map(asSym);
    return new PyTuple(sj.solveLinear(asExpr(args[0]), opts));
  },
  solve_linear_system: (args, kw) => {
    noKw(kw);
    const syms = args.slice(1).map(asSym);
    const s = solveAug(args[0] as Matrix, syms);
    return s ? new PyDict(syms.map((v, i) => [v, s[i]!] as const)) : null;
  },
  solve_undetermined_coeffs: (args, kw) => {
    const dict = Boolean(kw['dict']);
    for (const k of Object.keys(kw)) if (k !== 'dict') throw new Unsupported(`kwargs ${k}`);
    const coeffs = (args[1] as PyTuple).items.map(asSym);
    const syms = args[2] === undefined ? [] : args[2] instanceof PyTuple ? args[2].items.map(asSym) : [asSym(args[2])];
    const sols = sj.solveUndeterminedCoeffs(asExpr(args[0]), coeffs, syms);
    const dicts = sols.map((t) => new PyDict(coeffs.map((v, i) => [v, t[i]!] as const)));
    if (dict) return new PyList(dicts);
    return dicts.length === 1 ? dicts[0] : new PyList(dicts);
  },
  nsolve: (args, kw) => {
    noKw(kw);
    const e = asExpr(args[0]);
    if (args.length === 3) return sj.nsolve(e, asSym(args[1]), asExpr(args[2]));
    const syms = [...sj.freeSymbols(e)];
    if (syms.length !== 1) throw new Unsupported('nsolve form');
    return sj.nsolve(e, syms[0]!, asExpr(args[1]));
  },
  Matrix: (args, kw) => {
    noKw(kw);
    const a = args[0];
    if (a instanceof Matrix) return a;
    if (a instanceof PyTuple && a.items.every((r) => r instanceof PyTuple)) {
      return Matrix.of(a.items.map((r) => (r as PyTuple).items.map(asExpr)));
    }
    if (a instanceof PyTuple) return Matrix.col(...a.items.map(asExpr));
    if (a === undefined) return Matrix.zeros(0, 0);
    if (a instanceof sj.Rational && args[1] instanceof sj.Rational && args[2] instanceof PyTuple) {
      const r = Number(a.p);
      const c = Number(args[1].p);
      const items = (args[2] as PyTuple).items.map(asExpr);
      return Matrix.fromFunction(r, c, (i, j) => items[i * c + j]!);
    }
    throw new Unsupported('Matrix constructor');
  },
  SparseMatrix: (args, kw) => ADAPTERS['Matrix']!(args, kw),
  jordan_cell: (args, kw) => (noKw(kw), sj.jordanBlock(intArg(args[1]), asExpr(args[0]))),
  matrix_multiply_elementwise: (args, kw) => (noKw(kw), sj.multiplyElementwise(args[0] as Matrix, args[1] as Matrix)),
  '.diag': (args, kw, self) => {
    if (!(self instanceof TypeRef)) throw new Unsupported('diag on instance');
    return ADAPTERS['diag']!(args, kw);
  },
  '.hstack': (args, kw, self) => typeMethod(self, 'Matrix', () => (args[0] as Matrix).hstack(...(args.slice(1) as Matrix[])), kw),
  '.vstack': (args, kw, self) => typeMethod(self, 'Matrix', () => (args[0] as Matrix).vstack(...(args.slice(1) as Matrix[])), kw),
  '.jordan_block': (args, kw, self) => {
    if (!(self instanceof TypeRef)) throw new Unsupported('jordan_block');
    for (const k of Object.keys(kw)) if (!['size', 'eigenvalue', 'band'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const size = intArg(kw['size'] ?? args[0]);
    const ev = asExpr(kw['eigenvalue'] ?? args[1]);
    return sj.jordanBlock(size, ev, (kw['band'] as 'upper' | 'lower' | undefined) ?? 'upper');
  },
  '.companion': (args, kw, self) => typeMethod(self, 'Matrix', () => {
    const p = asPoly(args[0]);
    const m = p.monic();
    return sj.companion(m.allCoeffs());
  }, kw),
  '.from_dok': (args, kw, self) => typeMethod(self, 'Matrix', () => {
    const r = intArg(args[0]);
    const c = intArg(args[1]);
    const d = args[2] as PyDict;
    const m = new Map(d.entries.map(([k, v]) => [(k as PyTuple).items.map(intArg).join(','), asExpr(v)] as const));
    return Matrix.fromFunction(r, c, (i, j) => m.get(`${i},${j}`) ?? 0);
  }, kw),
  '.copy': matrixMethod((m) => m),
  '.flat': matrixMethod((m) => new PyList(m.data)),
  '.values': matrixMethod((m) => new PyList(m.data.filter((x) => !(x instanceof sj.Rational && x.isZero)))),
  '.is_symbolic': matrixMethod((m) => m.data.some((x) => sj.freeSymbols(x).size > 0)),
  '.hat': matrixMethod((m) => {
    const [a, b, c] = m.data as Expr[];
    return Matrix.of([[0, sj.mul(-1, c!), b!], [c!, 0, sj.mul(-1, a!)], [sj.mul(-1, b!), a!, 0]]);
  }),
  '.vee': matrixMethod((m) => Matrix.col(m.get(2, 1), m.get(0, 2), m.get(1, 0))),
  '.per': matrixMethod((m) => sj.permanent(m)),
  '.charpoly': matrixMethod((m, a) => {
    const lam = a[0] instanceof Sym ? a[0] : new Sym('lambda');
    return sj.Poly.from(m.charpoly(lam), [lam], { pure: true });
  }),
  '.todok': matrixMethod((m) => {
    const out: (readonly [unknown, unknown])[] = [];
    const [r, c] = m.shape;
    for (let i = 0; i < r; i++) for (let j = 0; j < c; j++) {
      const v = m.get(i, j);
      if (!(v instanceof sj.Rational && v.isZero)) out.push([new PyTuple([i, j]), v]);
    }
    return new PyDict(out);
  }),
  '.todod': matrixMethod((m) => {
    const out: (readonly [unknown, unknown])[] = [];
    const [r, c] = m.shape;
    for (let i = 0; i < r; i++) {
      const row: (readonly [unknown, unknown])[] = [];
      for (let j = 0; j < c; j++) {
        const v = m.get(i, j);
        if (!(v instanceof sj.Rational && v.isZero)) row.push([j, v]);
      }
      if (row.length) out.push([i, new PyDict(row)]);
    }
    return new PyDict(out);
  }),
  '.connected_components': matrixMethod((m) => new PyList(sj.connectedComponents(m).map((c) => new PyList(c)))),
  '.strongly_connected_components': matrixMethod((m) => new PyList(sj.stronglyConnectedComponents(m).map((c) => new PyList(c)))),
  '.condition_number': matrixMethod((m) => {
    const sv = sj.singularValues(m);
    return sj.mul(sj.Max(...sv), sj.pow(sj.Min(...sv), -1));
  }),
  '.left_eigenvects': matrixMethod((m) => new PyList(sj.eigenvects(m.transpose()).map(([v, k, vs]) => new PyTuple([v, k, new PyList(vs.map((x) => x.transpose()))])))),
  eye: (args, kw) => (noKw(kw), Matrix.eye(Number((args[0] as sj.Rational).p))),
  zeros: (args, kw) => {
    noKw(kw);
    const [r, c] = args.map((a) => Number((a as sj.Rational).p));
    return Matrix.zeros(r!, c ?? r!);
  },
  diag: (args, kw) => {
    const unpack = Boolean(kw['unpack']);
    const blocks: (Matrix | Expr)[] = [];
    for (const a of args) {
      if (a instanceof Matrix) blocks.push(a);
      else if (a instanceof PyTuple) {
        if (unpack && args.length === 1) a.items.forEach((x) => blocks.push(asExpr(x)));
        else if (a.items.every((r) => r instanceof PyTuple)) blocks.push(Matrix.of(a.items.map((r) => (r as PyTuple).items.map(asExpr))));
        else blocks.push(Matrix.col(...a.items.map(asExpr)));
      } else blocks.push(asExpr(a));
    }
    return sj.blockDiag(...blocks);
  },
  limit: (args, kw) => {
    const dir = (kw['dir'] as string | undefined) ?? (typeof args[3] === 'string' ? (args[3] as string) : '+');
    for (const k of Object.keys(kw)) if (k !== 'dir') throw new Unsupported(`kwargs ${k}`);
    return sj.limit(asExpr(args[0]), asSym(args[1]), asExpr(args[2]), dir as '+' | '-' | '+-');
  },
  Limit: (args, kw) => {
    const dir = (kw['dir'] as string | undefined) ?? '+';
    return new sj.Limit([asExpr(args[0]), asSym(args[1]), asExpr(args[2])], dir as '+' | '-' | '+-');
  },
  series: (args, kw) => {
    const x0 = kw['x0'] ?? args[2] ?? 0;
    const n = kw['n'] ?? args[3] ?? 6;
    const dir = (kw['dir'] ?? args[4] ?? '+') as '+' | '-';
    for (const k of Object.keys(kw)) if (!['x0', 'n', 'dir'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const e = asExpr(args[0]);
    const syms = [...sj.freeSymbols(e)];
    const x = args[1] ? asSym(args[1]) : syms.length === 1 ? syms[0]! : undefined;
    if (!x) throw new Unsupported('series variable');
    return sj.series(e, x, asExpr(x0), Number((asExpr(n) as sj.Rational).p), dir);
  },
  O: (args, kw) => (noKw(kw), orderNode(asExpr(args[0]), args.slice(1))),
  Sum: (args, kw) => (noKw(kw), concreteNode('Sum', [asExpr(args[0]), ...args.slice(1)])),
  Product: (args, kw) => (noKw(kw), concreteNode('Product', [asExpr(args[0]), ...args.slice(1)])),
  summation: (args, kw) => (noKw(kw), concreteDoit(concreteNode('Sum', [asExpr(args[0]), ...args.slice(1)]))),
  product: (args, kw) => (noKw(kw), concreteDoit(concreteNode('Product', [asExpr(args[0]), ...args.slice(1)]))),
  '.reverse_order': (args, kw, self) => {
    noKw(kw);
    if (!(self instanceof sj.Concrete)) throw new Unsupported('reverse_order');
    return sj.reverseOrder(self, ...args.map((a) => (a instanceof Sym ? a : Number((a as sj.Rational).p))));
  },
  Order: (args, kw) => (noKw(kw), orderNode(asExpr(args[0]), args.slice(1))),
  Integral: (args, kw) => (noKw(kw), integralNode([asExpr(args[0]), ...args.slice(1)])),
  det: (args, kw) => {
    noKw(kw);
    if (!(args[0] instanceof Matrix)) throw new Unsupported('det');
    return args[0].det();
  },

  // ---- Expr methods
  '.expand': (args, kw, self) => {
    if (args.length) throw new Unsupported('expand args');
    return sj.expand(asExpr(self), expandHints(kw));
  },
  // Matrix.simplify() works in place in SymPy and returns None
  '.simplify': (_args, _kw, self) => (self instanceof Matrix ? null : sj.simplify(asExpr(self))),
  '.factor': exprMethod(sj.factor),
  '.together': exprMethod(sj.together),
  '.cancel': exprMethod(sj.cancel),
  '.trigsimp': exprMethod(sj.trigsimp),
  '.conjugate': exprMethod(sj.conjugate),
  '.subs': (args, kw, self) => {
    const simultaneous = Boolean(kw['simultaneous']);
    for (const k of Object.keys(kw)) if (k !== 'simultaneous') throw new Unsupported(`kwargs ${k}`);
    if (simultaneous) {
      const a = args[0];
      const pairs = a instanceof PyDict ? a.entries : a instanceof PyTuple ? a.items.map((p) => (p as PyTuple).items) : undefined;
      if (!pairs) throw new Unsupported('subs simultaneous');
      return sj.subs(asExpr(self), pairs.map(([k, v]) => [asExpr(k), asExpr(v)] as const), { simultaneous: true });
    }
    if (self instanceof Matrix) {
      if (args.length !== 2) throw new Unsupported('Matrix.subs');
      return self.subs(asExpr(args[0]), asExpr(args[1]));
    }
    return subsArgs(asExpr(self), args);
  },
  '.diff': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Poly) return self.diff(args[0] === undefined ? undefined : asExpr(args[0]));
    if (self instanceof Matrix) {
      return self.map((e) => diffArgs(e, args));
    }
    return diffArgs(asExpr(self), args);
  },
  '.integrate': (args, kw, self) => ADAPTERS['integrate']!([self, ...args], kw),
  '.series': (args, kw, self) => ADAPTERS['series']!([self, ...args], kw),
  '.limit': (args, kw, self) => ADAPTERS['limit']!([self, ...args], kw),
  '.removeO': exprMethod((e) => (e instanceof sj.Add ? sj.add(...e.args.filter((a) => !(a instanceof sj.Order))) : e instanceof sj.Order ? S.Zero : e)),
  '.doit': (args, kw, self) => {
    noKw(kw);
    if (args.length) throw new Unsupported('doit args');
    const e = asExpr(self);
    const doit = (x: Expr): Expr => {
      const y = x.args.length ? sj.rebuild(x, x.args.map(doit)) : x;
      if (y instanceof Integral) {
        const [f, v, a, b] = y.args;
        return a && b ? sj.integrate(f!, v as Sym, [a, b]) : sj.integrate(f!, v as Sym);
      }
      if (y instanceof sj.Limit) return sj.limit(y.args[0]!, y.args[1] as Sym, y.args[2]!, y.dir);
      if (y instanceof sj.Concrete) return sj.doitConcrete(y);
      return y;
    };
    return doit(e);
  },
  '.evalf': (args, kw, self) => evalfAdapter(self, args, kw),
  '.n': (args, kw, self) => evalfAdapter(self, args, kw),
  '.round': (args, kw, self) => {
    noKw(kw);
    return sj.round(asExpr(self), args.length ? intArg(args[0]) : undefined);
  },
  '.has': (args, kw, self) => {
    noKw(kw);
    const e = self instanceof Matrix ? self.data : [asExpr(self)];
    return args.some((a) =>
      a instanceof FnClass || a instanceof TypeRef || a instanceof UFnClass
        ? e.some((x) => sj.find(x, toQuery(a)).length > 0)
        : e.some((x) => x.has(asExpr(a))),
    );
  },
  '.match': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'old') throw new Unsupported(`kwargs ${k}`);
    return matchDict(sj.match(asExpr(self), asExpr(args[0]), { old: Boolean(kw['old']) }));
  },
  '.replace': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (!['exact', 'map'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    const q = toQuery(args[0]);
    const v = args[1];
    const value: sj.Replacement = v instanceof FnClass || v instanceof UFnClass ? { fn: v.name } : v instanceof TypeRef ? { type: v.name } : asExpr(v);
    const r = sj.replace(asExpr(self), q, value, {
      exact: kw['exact'] === undefined ? undefined : Boolean(kw['exact']),
      map: Boolean(kw['map']),
      apply: applyFn,
    });
    if (Array.isArray(r)) return new PyTuple([r[0], new PyDict([...r[1]])]);
    return r;
  },
  gcd_terms: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['clear', 'fraction', 'isprimitive'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    return sj.gcdTerms(asExpr(args[0]), { clear: kw['clear'] as boolean | undefined, fraction: kw['fraction'] as boolean | undefined, isprimitive: kw['isprimitive'] as boolean | undefined });
  },
  factor_terms: (args, kw) => {
    for (const k of Object.keys(kw)) if (!['clear', 'fraction', 'sign', 'radical'].includes(k)) throw new Unsupported(`kwargs ${k}`);
    if (kw['radical']) throw new Unsupported('radical');
    return sj.factorTerms(asExpr(args[0]), { clear: kw['clear'] as boolean | undefined, fraction: kw['fraction'] as boolean | undefined, sign: kw['sign'] as boolean | undefined });
  },
  collect_const: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'Numbers') throw new Unsupported(`kwargs ${k}`);
    return sj.collectConst(asExpr(args[0]), args.slice(1).map(asExpr), { numbers: kw['Numbers'] === undefined ? true : Boolean(kw['Numbers']) });
  },
  signsimp: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'evaluate') throw new Unsupported(`kwargs ${k}`);
    return sj.signsimp(asExpr(args[0]), kw['evaluate'] === undefined ? true : Boolean(kw['evaluate']));
  },
  '.rewrite': (args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'deep') throw new Unsupported(`kwargs ${k}`);
    const name = (v: unknown): string => {
      if (v instanceof FnClass || v instanceof UFnClass || v instanceof TypeRef) return v.name;
      if (typeof v === 'string') return v;
      throw new Unsupported('rewrite target');
    };
    if (!args.length) return asExpr(self);
    const target = name(args[args.length - 1]);
    let pattern = args.slice(0, -1);
    if (pattern.length === 1 && (pattern[0] instanceof PyList || pattern[0] instanceof PyTuple)) pattern = [...(pattern[0] as PyList).items];
    return sj.rewrite(asExpr(self), target, { pattern: pattern.map(name), deep: kw['deep'] === undefined ? true : Boolean(kw['deep']) });
  },
  '.find': (args, kw, self) => {
    noKw(kw);
    return new PySet(sj.find(asExpr(self), toQuery(args[0])));
  },
  count_ops: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'visual') throw new Unsupported(`kwargs ${k}`);
    const visual = Boolean(kw['visual'] ?? args[1]);
    if (args[0] instanceof PyList || args[0] instanceof PyTuple) {
      const items = (args[0] as PyList).items.map(asExpr);
      return visual ? sj.add(...items.map(sj.countOpsVisual)) : items.reduce((n, e) => n + sj.countOps(e), 0);
    }
    return visual ? sj.countOpsVisual(asExpr(args[0])) : sj.countOps(asExpr(args[0]));
  },
  '.count_ops': (args, kw, self) => ADAPTERS['count_ops']!([self, ...args], kw),

  '.coeff': (args, kw, self) => {
    noKw(kw);
    const n = args[1] instanceof sj.Rational ? Number(args[1].p) : 1;
    return sj.coeff(asExpr(self), asExpr(args[0]), n);
  },
  '.as_independent': (args, kw, self) => {
    const asAdd = kw['as_Add'];
    for (const k of Object.keys(kw)) if (k !== 'as_Add') throw new Unsupported(`kwargs ${k}`);
    const opts = asAdd === undefined ? {} : { asAdd: Boolean(asAdd) };
    return new PyTuple(sj.asIndependent(asExpr(self), args.map(asExpr), opts));
  },
  '.as_coeff_add': (args, kw, self) => {
    noKw(kw);
    const [c, t] = sj.asCoeffAdd(asExpr(self), args.map(asExpr));
    return new PyTuple([c, new PyTuple(t)]);
  },
  '.as_coeff_mul': (args, kw, self) => {
    noKw(kw);
    const [c, t] = sj.asCoeffMul(asExpr(self), args.map(asExpr));
    return new PyTuple([c, new PyTuple(t)]);
  },
  '.as_coeff_Mul': exprMethod((e) => new PyTuple(sj.splitCoeff(e))),
  '.primitive': (_a, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Poly) return new PyTuple(self.primitive());
    return new PyTuple(sj.primitive(asExpr(self)));
  },
  '.degree': (args, kw, self) => {
    noKw(kw);
    return asPoly(self).degree(args[0] === undefined ? undefined : asExpr(args[0]));
  },
  '.as_content_primitive': (args, kw, self) => {
    const clear = kw['clear'];
    for (const k of Object.keys(kw)) if (k !== 'clear') throw new Unsupported(`kwargs ${k}`);
    if (args.length) throw new Unsupported('arity');
    return new PyTuple(sj.asContentPrimitive(asExpr(self), clear === undefined ? {} : { clear: Boolean(clear) }));
  },
  '.extract_multiplicatively': (args, kw, self) => (noKw(kw), sj.extractMultiplicatively(asExpr(self), asExpr(args[0])) ?? null),
  '.extract_additively': (args, kw, self) => (noKw(kw), sj.extractAdditively(asExpr(self), asExpr(args[0])) ?? null),
  '.as_coefficient': (args, kw, self) => (noKw(kw), sj.asCoefficient(asExpr(self), asExpr(args[0])) ?? null),
  '.is_polynomial': (args, kw, self) => (noKw(kw), sj.isPolynomial(asExpr(self), args.map(asExpr))),
  '.is_rational_function': (args, kw, self) => (noKw(kw), sj.isRationalFunction(asExpr(self), args.map(asExpr))),
  '.is_constant': (args, kw, self) => {
    noKw(kw);
    return sj.isConstant(asExpr(self), args.map(asSym));
  },
  '.as_real_imag': exprMethod((e) => new PyTuple(sj.asRealImag(e))),
  '.as_numer_denom': exprMethod((e) => new PyTuple(sj.asNumerDenom(e))),
  '.as_base_exp': exprMethod((e) => new PyTuple(sj.asBaseExp(e))),
  '.args_cnc': (args, kw, self) => {
    const split1 = kw['split_1'];
    for (const k of Object.keys(kw)) if (k !== 'split_1') throw new Unsupported(`kwargs ${k}`);
    if (args.length) throw new Unsupported('arity');
    const [c, nc] = sj.argsCncSplit(asExpr(self), split1 === undefined ? true : Boolean(split1));
    return new PyList([new PyList(c), new PyList(nc)]);
  },
  '.xreplace': (args, kw, self) => {
    noKw(kw);
    const d = args[0];
    if (!(d instanceof PyDict)) throw new Unsupported('xreplace mapping');
    return sj.xreplace(asExpr(self), d.entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
  },
  '.atoms': (args, kw, self) => {
    noKw(kw);
    const preds = args.map((a) => {
      if (a instanceof FnClass || a instanceof TypeRef || a instanceof UFnClass) {
        const q = toQuery(a);
        return (x: Expr) => ('fn' in (q as object) ? sj.find(x, q).some((y) => y.key === x.key) : sj.isInstance(x, (q as { type: string }).type));
      }
      const t = asExpr(a);
      if (t instanceof Sym) return (x: Expr) => x instanceof Sym;
      if (t instanceof sj.Rational && t.isOne) return (x: Expr) => x instanceof sj.Rational && x.isOne;
      if (t instanceof sj.Rational && t.isInteger) return (x: Expr) => x instanceof sj.Rational && x.isInteger;
      if (t instanceof sj.Rational) return (x: Expr) => x instanceof sj.Rational;
      return (x: Expr) => x.key === t.key;
    });
    const pred = preds.length ? (x: Expr) => preds.some((p) => p(x)) : () => true;
    if (args.some((a) => a instanceof FnClass || a instanceof TypeRef || a instanceof UFnClass)) {
      return new PySet(sj.find(asExpr(self), pred));
    }
    return new PySet(sj.atoms(asExpr(self), pred));
  },
  '.as_ordered_terms': exprMethod((e) => new PyList(e instanceof sj.Add ? asOrdered(e) : [e])),

  // ---- ODEs
  dsolve: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'ics') throw new Unsupported(`kwargs ${k}`);
    const ics = kw['ics'] instanceof PyDict ? (kw['ics'] as PyDict).entries.map(([k, v]) => [asExpr(k), asExpr(v)] as [Expr, Expr]) : undefined;
    return sj.dsolve(asExpr(args[0]), asExpr(args[1]), ics ? { ics } : {});
  },

  // ---- polynomials
  Poly: (args, kw) => {
    for (const k of Object.keys(kw)) if (k !== 'domain') throw new Unsupported(`kwargs ${k}`);
    const [e, ...gens] = args;
    const p = sj.Poly.from(asExprOrPoly(e), gens.map(asExpr));
    if (kw['domain'] !== undefined) throw new Unsupported('explicit domain');
    return p;
  },
  degree: (args, kw) => {
    noKw(kw);
    const f = args[0] instanceof sj.Poly ? args[0] : asExpr(args[0]);
    return sj.degree(f, args[1] === undefined ? undefined : asExpr(args[1]));
  },
  total_degree: (args, kw) => {
    noKw(kw);
    const e = asExprOrPoly(args[0]);
    const gens = args.slice(1).map(asExpr);
    return sj.Poly.from(e, gens).totalDegree();
  },
  LC: (args, kw) => (noKw(kw), polyOf(args).LC()),
  LM: (args, kw) => (noKw(kw), polyOf(args).LM()),
  LT: (args, kw) => {
    noKw(kw);
    const p = polyOf(args);
    return sj.mul(p.LC(), p.LM());
  },
  gcd: (args, kw) => {
    noKw(kw);
    if (args.length !== 2) throw new Unsupported('gcd arity');
    const r = sj.gcd(asExprOrPoly(args[0]), asExprOrPoly(args[1]));
    return args[0] instanceof sj.Poly ? sj.Poly.from(r, (args[0] as sj.Poly).gens) : r;
  },
  lcm: (args, kw) => {
    noKw(kw);
    if (args.length !== 2) throw new Unsupported('lcm arity');
    const r = sj.lcm(asExprOrPoly(args[0]), asExprOrPoly(args[1]));
    return args[0] instanceof sj.Poly ? sj.Poly.from(r, (args[0] as sj.Poly).gens) : r;
  },
  div: (args, kw) => {
    noKw(kw);
    if (args[0] instanceof sj.Poly) return new PyTuple(args[0].div(args[1] as sj.Poly));
    return new PyTuple(sj.polyDiv(asExpr(args[0]), asExpr(args[1])));
  },
  rem: (args, kw) => (noKw(kw), args[0] instanceof sj.Poly ? args[0].rem(args[1] as sj.Poly) : sj.polyDiv(asExpr(args[0]), asExpr(args[1]))[1]),
  quo: (args, kw) => (noKw(kw), args[0] instanceof sj.Poly ? args[0].quo(args[1] as sj.Poly) : sj.polyDiv(asExpr(args[0]), asExpr(args[1]))[0]),
  factor_list: (args, kw) => {
    noKw(kw);
    const [c, fs] = sj.factorList(asExprOrPoly(args[0]));
    return new PyTuple([c, new PyList(fs.map(([f, k]) => new PyTuple([f, k])))]);
  },
  terms_gcd: (args, kw) => {
    const opts: { expand?: boolean; deep?: boolean; clear?: boolean } = {};
    for (const k of Object.keys(kw)) {
      if (k !== 'expand' && k !== 'deep' && k !== 'clear') throw new Unsupported(`kwargs ${k}`);
      opts[k] = kw[k] === true;
    }
    return sj.termsGcd(asExpr(args[0]), ...args.slice(1).map(asSym), opts);
  },
  horner: (args, kw) => (noKw(kw), sj.horner(asExpr(args[0]), args[1] ? asSym(args[1]) : undefined)),
  interpolate: (args, kw) => {
    noKw(kw);
    const data = args[0] as PyTuple;
    const pts = data.items.map((d) => (d instanceof PyTuple ? ([asExpr(d.items[0]), asExpr(d.items[1])] as const) : asExpr(d)));
    return sj.interpolate(pts as never, asSym(args[1]));
  },
  resultant: (args, kw) => {
    noKw(kw);
    const f = asExprOrPoly(args[0]);
    const g = asExprOrPoly(args[1]);
    const x = args[2] ? asSym(args[2]) : (sj.sortGens([...sj.freeSymbols(f), ...sj.freeSymbols(g)])[0] as Sym);
    return sj.resultant(f, g, x);
  },
  discriminant: (args, kw) => {
    noKw(kw);
    const f = asExprOrPoly(args[0]);
    const x = args[1] ? asSym(args[1]) : (sj.sortGens([...sj.freeSymbols(f)])[0] as Sym);
    return sj.discriminant(f, x);
  },
  '.as_expr': (args, kw, self) => {
    noKw(kw);
    if (self instanceof sj.Poly) {
      if (!args.length) return self.asExpr();
      if (args[0] instanceof PyDict) return self.asExprAt(args[0].entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
      return self.asExprAt(args.map(asExpr));
    }
    if (self instanceof Expr) return self;
    throw new Unsupported('as_expr');
  },
  '.total_degree': (_a, kw, self) => (noKw(kw), asPoly(self).totalDegree()),
  '.LC': (_a, kw, self) => (noKw(kw), asPoly(self).LC()),
  '.coeffs': (_a, kw, self) => (noKw(kw), new PyList(asPoly(self).coeffs())),
  '.all_coeffs': (_a, kw, self) => (noKw(kw), new PyList(asPoly(self).allCoeffs())),
  '.monoms': (_a, kw, self) => (noKw(kw), new PyList(asPoly(self).monoms().map((m) => new PyTuple(m)))),
  '.terms': (_a, kw, self) => (noKw(kw), new PyList(asPoly(self).terms().map(([m, c]) => new PyTuple([new PyTuple(m), c])))),
  '.coeff_monomial': (args, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    const m = args[0];
    if (m instanceof PyTuple) return p.coeffMonomial(m.items.map((x) => Number((x as sj.Rational).p)));
    const mono = sj.Poly.from(asExpr(m), p.gens);
    return p.coeffMonomial(mono.monoms()[0]!);
  },
  '.eval': (args, kw, self) => {
    noKw(kw);
    const p = asPoly(self);
    if (args[0] instanceof PyDict) return p.evalMany(args[0].entries.map(([k, v]) => [asExpr(k), asExpr(v)] as const));
    if (args[0] instanceof PyTuple) return p.evalMany(args[0].items.map((v, i) => [p.gens[i]!, asExpr(v)] as const));
    if (args.length === 1) return p.eval(asExpr(args[0]));
    return p.eval(asExpr(args[1]), asExpr(args[0]));
  },
  '.monic': (_a, kw, self) => (noKw(kw), asPoly(self).monic()),
  '.gcd': (args, kw, self) => (noKw(kw), asPoly(self).gcd(args[0] as sj.Poly)),
  '.lcm': (args, kw, self) => (noKw(kw), asPoly(self).lcm(args[0] as sj.Poly)),
  '.div': (args, kw, self) => new PyTuple(asPoly(self).divAuto(args[0] as sj.Poly, autoKw(kw))),
  '.rem': (args, kw, self) => asPoly(self).rem(args[0] as sj.Poly, autoKw(kw)),
  '.quo': (args, kw, self) => asPoly(self).quo(args[0] as sj.Poly, autoKw(kw)),
  '.abs': polyM((p) => p.abs()),
  '.neg': polyM((p) => p.neg()),
  '.sqr': polyM((p) => p.sqr()),
  '.add': polyM((p, a) => p.add(polyArg(a[0]))),
  '.sub': polyM((p, a) => p.sub(polyArg(a[0]))),
  '.mul': polyM((p, a) => p.mul(polyArg(a[0]))),
  '.pow': polyM((p, a) => p.pow(intArg(a[0]))),
  '.add_ground': polyM((p, a) => p.addGround(asExpr(a[0]))),
  '.sub_ground': polyM((p, a) => p.subGround(asExpr(a[0]))),
  '.mul_ground': polyM((p, a) => p.mulGround(asExpr(a[0]))),
  '.quo_ground': polyM((p, a) => p.quoGround(asExpr(a[0]))),
  '.exquo_ground': polyM((p, a) => p.exquoGround(asExpr(a[0]))),
  '.all_monoms': polyM((p) => new PyList(p.allMonoms().map((m) => new PyTuple(m)))),
  '.all_terms': polyM((p) => new PyList(p.allTerms().map(([m, c]) => new PyTuple([new PyTuple(m), c])))),
  '.as_dict': polyM((p) => new PyDict(p.asDict().map(([m, c]) => [new PyTuple(m), c] as const))),
  '.cofactors': polyM((p, a) => new PyTuple(p.cofactors(a[0] as sj.Poly))),
  '.compose': polyM((p, a) => p.compose(a[0] as sj.Poly)),
  '.degree_list': polyM((p) => new PyTuple(p.degreeList())),
  '.discriminant': polyM((p) => p.discriminant()),
  '.resultant': polyM((p, a) => p.resultant(a[0] as sj.Poly)),
  '.EC': polyM((p) => p.EC()),
  '.TC': polyM((p) => p.TC()),
  '.nth': polyM((p, a) => p.nth(...a.map(intArg))),
  '.length': polyM((p) => p.length()),
  '.l1_norm': polyM((p) => p.l1Norm()),
  '.max_norm': polyM((p) => p.maxNorm()),
  '.exclude': polyM((p) => p.exclude()),
  '.has_only_gens': polyM((p, a) => p.hasOnlyGens(...a.map(asExpr))),
  '.homogeneous_order': polyM((p) => p.homogeneousOrder() ?? null),
  '.homogenize': polyM((p, a) => p.homogenize(asExpr(a[0]))),
  '.ltrim': polyM((p, a) => p.ltrim(a[0] instanceof sj.Rational ? Number(a[0].p) : asExpr(a[0]))),
  '.reorder': polyM((p, a) => p.reorder(...a.map(asExpr))),
  '.pdiv': polyM((p, a) => new PyTuple(p.pdiv(a[0] as sj.Poly))),
  '.pexquo': polyM((p, a) => p.pexquo(a[0] as sj.Poly)),
  '.shift': polyM((p, a) => p.shift(asExpr(a[0]))),
  '.sqf_part': polyM((p) => p.sqfPart()),
  '.terms_gcd': polyM((p) => {
    const [m, q] = p.termsGcd();
    return new PyTuple([new PyTuple(m), q]);
  }),
  '.deflate': polyM((p) => {
    const [m, q] = p.deflate();
    return new PyTuple([new PyTuple(m), q]);
  }),
  '.to_field': polyM((p) => p.toField()),
  '.to_ring': polyM((p) => p.toRing()),
  '.to_exact': polyM((p) => p.toExact()),
  '.transform': polyM((p, a) => p.transform(a[0] as sj.Poly, a[1] as sj.Poly)),
  '.trunc': polyM((p, a) => p.trunc(asExpr(a[0]))),
  '.clear_denoms': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'convert') throw new Unsupported(`kwargs ${k}`);
    return new PyTuple(asPoly(self).clearDenoms(Boolean(kw['convert'])));
  },
  '.gcdex': polyM((p, a) => new PyTuple(p.gcdex(a[0] as sj.Poly))),
  '.half_gcdex': polyM((p, a) => new PyTuple(p.halfGcdex(a[0] as sj.Poly))),
  '.sturm': polyM((p) => new PyList(p.sturm())),
  '.count_roots': polyM((p, a) => {
    if (a.some((v) => v instanceof Expr && v.has(sj.I))) throw new Unsupported('complex count_roots');
    return p.countRoots(a[0] === undefined ? undefined : asExpr(a[0]), a[1] === undefined ? undefined : asExpr(a[1]));
  }),
  '.ground_roots': polyM((p) => new PyDict(p.groundRoots())),
  '.revert': polyM((p, a) => p.revert(intArg(a[0]))),
  '.nth_power_roots_poly': polyM((p, a) => p.nthPowerRootsPoly(intArg(a[0]))),
  '.real_roots': polyM((p) => new PyList(p.realRoots())),
  '.all_roots': polyM((p) => new PyList(p.allRoots())),
  '.root': polyM((p, a) => p.root(intArg(a[0]))),
  '.which_real_roots': polyM((p, a) => new PyList(p.whichRealRoots((a[0] as PyList).items.map(asExpr)))),
  '.which_all_roots': polyM((p, a) => new PyList(p.whichAllRoots((a[0] as PyList).items.map(asExpr)))),
  '.factor_list_include': polyM((p) => new PyList(p.factorListInclude().map(([f, k]) => new PyTuple([f, k])))),
  '.sqf_list_include': (_args, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'all') throw new Unsupported(`kwargs ${k}`);
    return new PyList(asPoly(self).sqfListInclude(Boolean(kw['all'])).map(([f, k]) => new PyTuple([f, k])));
  },
  ground_roots: (args, kw) => (noKw(kw), new PyDict(polyOf(args).groundRoots())),
  real_roots: (args, kw) => (noKw(kw), new PyList(polyOf(args).realRoots())),
  all_roots: (args, kw) => (noKw(kw), new PyList(polyOf(args).allRoots())),
  count_roots: (args, kw) => {
    noKw(kw);
    const p = args[0] instanceof sj.Poly ? args[0] : sj.Poly.from(asExpr(args[0]));
    if (args.slice(1).some((v) => v instanceof Expr && v.has(sj.I))) throw new Unsupported('complex count_roots');
    return p.countRoots(args[1] === undefined ? undefined : asExpr(args[1]), args[2] === undefined ? undefined : asExpr(args[2]));
  },
  '.pquo': (args, kw, self) => (noKw(kw), asPoly(self).pquo(args[0] as sj.Poly)),
  '.prem': (args, kw, self) => (noKw(kw), asPoly(self).prem(args[0] as sj.Poly)),
  '.exquo': (args, kw, self) => (noKw(kw), asPoly(self).exquo(args[0] as sj.Poly)),
  '.factor_list': (_a, kw, self) => {
    noKw(kw);
    const [c, fs] = asPoly(self).factorList();
    return new PyTuple([c, new PyList(fs.map(([f, k]) => new PyTuple([f, k])))]);
  },
  '.sqf_list': (_a, kw, self) => {
    for (const k of Object.keys(kw)) if (k !== 'all') throw new Unsupported(`kwargs ${k}`);
    const [c, fs] = asPoly(self).sqfListAll(Boolean(kw['all']));
    return new PyTuple([c, new PyList(fs.map(([f, k]) => new PyTuple([f, k])))]);
  },
  '.content': (_a, kw, self) => (noKw(kw), asPoly(self).content()),

  // ---- Matrix methods (linear algebra)
  '.rref': matrixMethod((m) => {
    const [r, p] = sj.rref(m);
    return new PyTuple([r, new PyTuple(p)]);
  }),
  '.echelon_form': matrixMethod((m) => sj.echelonForm(m)),
  '.rank': matrixMethod((m) => sj.rank(m)),
  '.nullspace': matrixMethod((m) => new PyList(sj.nullspace(m))),
  '.columnspace': matrixMethod((m) => new PyList(sj.columnspace(m))),
  '.rowspace': matrixMethod((m) => new PyList(sj.rowspace(m))),
  '.eigenvects': matrixMethod((m) => new PyList(sj.eigenvects(m).map(([v, k, vs]) => new PyTuple([v, k, new PyList(vs)])))),
  '.diagonalize': matrixMethod((m) => new PyTuple(sj.diagonalize(m))),
  '.is_diagonalizable': (_args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return sj.isDiagonalizable(self, Boolean(kw['reals_only']));
  },
  '.cholesky': (_args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return sj.cholesky(self, kw['hermitian'] === undefined ? true : Boolean(kw['hermitian']));
  },
  '.LDLdecomposition': matrixMethod((m) => new PyTuple(sj.ldl(m))),
  '.LUdecomposition': matrixMethod((m) => {
    const [L, U, p] = sj.luDecomposition(m);
    return new PyTuple([L, U, new PyList(p.map((x) => new PyList(x)))]);
  }),
  '.QRdecomposition': matrixMethod((m) => new PyTuple(sj.qrDecomposition(m))),
  '.dot': (args, kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    const b = args[0] instanceof Matrix ? args[0] : args[0] instanceof PyTuple ? Matrix.col(...args[0].items.map(asExpr)) : undefined;
    if (!b) throw new Unsupported('dot argument');
    const conv = (kw['conjugate_convention'] as string | undefined) ?? 'maths';
    return sj.dot(self, b, Boolean(kw['hermitian']), conv === 'physics' || conv === 'right' ? 'physics' : 'maths');
  },
  '.cross': matrixMethod((m, [b]) => sj.cross(m, b as Matrix)),
  '.norm': matrixMethod((m, [o]) => sj.norm(m, o as ExprLike | undefined)),
  '.singular_values': matrixMethod((m) => new PyList(sj.singularValues(m))),
  '.pinv': matrixMethod((m) => sj.pinv(m)),
  '.jacobian': matrixMethod((m, [y]) => sj.jacobian(m, y instanceof Matrix ? y : (y as PyTuple).items.map(asExpr))),
  '.exp': matrixMethod((m) => sj.matrixExp(m)),
  '.upper_triangular': matrixMethod((m, [k]) => sj.linalg.upperTriangular(m, k ? Number((k as sj.Rational).p) : 0)),
  '.lower_triangular': matrixMethod((m, [k]) => sj.linalg.lowerTriangular(m, k ? Number((k as sj.Rational).p) : 0)),
  '.diagonal': matrixMethod((m, [k]) => sj.linalg.diagonal(m, k ? Number((k as sj.Rational).p) : 0)),
  '.extract': matrixMethod((m, [r, c]) =>
    sj.linalg.extract(m, idxList(r), idxList(c)),
  ),
  '.reshape': matrixMethod((m, [r, c]) => sj.linalg.reshape(m, Number((r as sj.Rational).p), Number((c as sj.Rational).p))),
  '.rot90': matrixMethod((m, [k]) => sj.linalg.rot90(m, k ? Number((k as sj.Rational).p) : 1)),
  '.vech': (_args, kw, self) => sj.linalg.vech(self as Matrix, kw['diagonal'] === undefined ? true : Boolean(kw['diagonal'])),
  '.vec': matrixMethod((m) => sj.linalg.vec(m)),
  '.minor': matrixMethod((m, [i, j]) => sj.linalg.minorDet(m, Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.minor_submatrix': matrixMethod((m, [i, j]) => m.minor(Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.cofactor': matrixMethod((m, [i, j]) => sj.linalg.cofactor(m, Number((i as sj.Rational).p), Number((j as sj.Rational).p))),
  '.cofactor_matrix': matrixMethod((m) => m.cofactorMatrix()),
  '.is_anti_symmetric': (_args, _kw, self) => sj.linalg.isAntiSymmetric(self as Matrix),
  '.is_diagonal': matrixMethod((m) => sj.linalg.isDiagonal(m)),
  '.is_upper': matrixMethod((m) => sj.linalg.isUpper(m)),
  '.is_lower': matrixMethod((m) => sj.linalg.isLower(m)),
  '.is_nilpotent': matrixMethod((m) => sj.linalg.isNilpotent(m)),
  '.multiply_elementwise': matrixMethod((m, [b]) => sj.linalg.multiplyElementwise(m, b as Matrix)),
  '.project': matrixMethod((m, [b]) => sj.linalg.project(m, b as Matrix)),
  '.col_join': matrixMethod((m, [b]) => m.vstack(b as Matrix)),
  '.row_join': matrixMethod((m, [b]) => m.hstack(b as Matrix)),
  '.col_insert': matrixMethod((m, [p, b]) => sj.linalg.colInsert(m, Number((p as sj.Rational).p), b as Matrix)),
  '.row_insert': matrixMethod((m, [p, b]) => sj.linalg.rowInsert(m, Number((p as sj.Rational).p), b as Matrix)),
  '.col': matrixMethod((m, [j]) => m.col(Number((j as sj.Rational).p))),
  '.row': matrixMethod((m, [i]) => m.row(Number((i as sj.Rational).p))),
  '.applyfunc': matrixMethod(() => {
    throw new Unsupported('applyfunc');
  }),
  rot_axis1: exprFn(sj.rotAxis1),
  rot_axis2: exprFn(sj.rotAxis2),
  rot_axis3: exprFn(sj.rotAxis3),
  rot_ccw_axis1: exprFn(sj.rotCcwAxis1),
  rot_ccw_axis2: exprFn(sj.rotCcwAxis2),
  rot_ccw_axis3: exprFn(sj.rotCcwAxis3),
  rot_givens: (args, kw) => {
    const dim = kw['dim'] ? Number((kw['dim'] as sj.Rational).p) : 3;
    return sj.rotGivens(Number((args[0] as sj.Rational).p), Number((args[1] as sj.Rational).p), asExpr(args[2]), dim);
  },

  // ---- Matrix methods
  '.det': (_args, _kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return self.det();
  },
  '.inv': (_args, _kw, self) => {
    if (!(self instanceof Matrix)) throw new Unsupported('Matrix');
    return self.inv();
  },
  '.transpose': matrixMethod((m) => m.transpose()),
  '.adjugate': matrixMethod((m) => m.adjugate()),
  '.trace': matrixMethod((m) => m.trace()),
  '.eigenvals': matrixMethod((m) => rootsDict(m.eigenvals())),
  '.is_symmetric': (_args, _kw, self) => sj.linalg.isSymmetric(self as Matrix),
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
