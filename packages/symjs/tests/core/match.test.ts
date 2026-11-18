// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/match.ts.
// Pattern matching, replace / find / count and count_ops. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { MatMulNode } from '../../src/matrices/expressions/matexpr';
import { impl } from '../../src/core/nodes';
import {
  Derivative,
  Dummy,
  E,
  type Expr,
  Float,
  I,
  Integral,
  Max,
  Min,
  NoMatchResult,
  Product,
  Sum,
  SymFunction,
  Wild,
  WildFunction,
  abs,
  add,
  cos,
  count,
  countOps,
  exp,
  find,
  isInstance,
  log,
  match,
  mul,
  oo,
  parse,
  pi,
  pow,
  rational,
  replace,
  sin,
  sqrt,
  sstr,
  str,
  symbols,
  tan,
} from '../../src';

const [x, y, z, n] = symbols('x y z n');

const f = SymFunction('f');
const g = SymFunction('g');
const a = new Wild('a');
const b = new Wild('b');
const p = new Wild('p');
const q = new Wild('q');

const fmt = (m: unknown): string =>
  !(m instanceof Map)
    ? 'None'
    : `{${[...m]
        .map(([k, v]) => `${str(k as Expr)}: ${str(v as Expr)}`)
        .sort()
        .join(', ')}}`;

const s = (e: unknown): string => str(e as Expr);

const fmt2 = (m: Map<unknown, unknown> | NoMatchResult) =>
  !(m instanceof Map)
    ? 'None'
    : `{${[...m]
        .map(([k, v]) => `${str(k as never)}: ${str(v as never)}`)
        .sort()
        .join(', ')}}`;

describe('match: a product pattern that leaves no factor for the wild', () => {
  it('(x*y).match(x*y*a_) = {a_: 1}', () => {
    const w = new sj.Wild('a');
    const m = sj.match(sj.mul(x, y), sj.mul(x, y, w));
    expect(m instanceof Map ? String(m.get(w)) : String(m)).toBe('1');
  });
  it('an expression containing the wild matches itself with no bindings: (a_*x).match(a_*x) = {}', () => {
    const w = new sj.Wild('a');
    const m = sj.match(sj.mul(w, x), sj.mul(w, x));
    expect(m instanceof Map ? m.size : String(m)).toBe(0);
  });
  it('a pattern whose factors are all exact leaves 1 to match the rest: (a_*x*y).match(a_*x) is None', () => {
    const w = new sj.Wild('a');
    expect(sj.match(sj.mul(w, x, y), sj.mul(w, x)) instanceof Map).toBe(false);
    expect(sj.match(sj.mul(w, x, 2), sj.mul(w, x)) instanceof Map).toBe(false);
  });
});

describe('match (SymPy Basic.match)', () => {
  it('leaves Wilds the match does not need unassigned', () => {
    // S(0).match(a*b) -> {b_: 0}
    expect(fmt(match(0, mul(a, b)))).toBe('{b_: 0}');
  });
  it('matches the exact part of a sum first', () => {
    expect(fmt(match(add(x, y, z), add(x, y)))).toBe('None');
    expect(fmt(match(add(x, y, z), add(a, x, y)))).toBe('{a_: z}');
  });
  it('matches WildFunction', () => {
    const F = new WildFunction('F');
    const G = new WildFunction('G', [2]);
    expect(fmt(match(f(x), F))).toBe('{F_: f(x)}');
    expect(fmt(match(sin(x), F))).toBe('{F_: sin(x)}');
    expect(fmt(match(exp(x), F))).toBe('{F_: exp(x)}');
    expect(fmt(match(x, F))).toBe('None');
    expect(fmt(match(f(x), G))).toBe('None');
    expect(fmt(match(exp(x), G))).toBe('None');
    expect(fmt(match(f(x, y), G))).toBe('{G_: f(x, y)}');
    // G.match(F): a WildFunction is itself a function with no arguments
    expect(fmt(match(G, F))).toBe('{F_: G_}');
  });
  it('checks the properties of a Wild', () => {
    const neg = new Wild('c', { properties: [(e) => e.isNumber && e.toNumber() < 0] });
    expect(fmt(match(4, neg))).toBe('None');
    expect(fmt(match(-4, neg))).toBe('{c_: -4}');
  });
  it('matches structurally', () => {
    expect(fmt(match(sin(x), sin(x)))).toBe('{}');
    expect(fmt(match(f(x), g(a)))).toBe('None');
    expect(fmt(match(f(x, y), f(a)))).toBe('None');
    expect(fmt(match(Sum(x, [x, 1, n]), Product(a, [x, 1, n])))).toBe('None');
    expect(fmt(match(Sum(x, [x, 1, n]), Sum(a, [x, 1, n])))).toBe('{a_: x}');
  });
  it('matches powers', () => {
    expect(fmt(match(0, pow(a, 2)))).toBe('None');
    expect(fmt(match(pow(x, y), pow(a, 2)))).toBe('{a_: sqrt(x**y)}');
    expect(fmt(match(pow(x, 3), pow(a, 3)))).toBe('{a_: x}');
  });
  it('matches products by splitting a power', () => {
    expect(fmt(match(pow(x, 3), mul(a, b)))).toBe('{a_: 1, b_: x**3}');
    expect(fmt(match(pow(x, 3), mul(a, x)))).toBe('{a_: x**2}');
    expect(fmt(match(pow(x, -3), mul(a, x)))).toBe('{a_: x**(-4)}');
    expect(fmt(match(mul(pow(x, 3), y), mul(a, x, y)))).toBe('{a_: x**2}');
    expect(fmt(match(add(mul(x, y), mul(x, z)), mul(p, x)))).toBe('None');
  });
  it('splits a power into an unevaluated product when nothing else matches', () => {
    // Wilds that refuse powers: SymPy returns the unevaluated product x*x**2
    const notPow = (e: Expr) => !isInstance(e, 'Pow');
    const an = new Wild('a', { properties: [notPow] });
    const bn = new Wild('b', { properties: [notPow] });
    expect(fmt(match(pow(x, 3), mul(an, bn)))).toBe('{a_: x*x**2, b_: 1}');
  });
  it('matches sums with Wilds excluding the variable', () => {
    const qx = new Wild('q', { exclude: [x] });
    const r = new Wild('r', { exclude: [x] });
    expect(fmt(match(add(mul(x, y), mul(x, z)), add(mul(p, x), qx)))).toBe('{p_: y + z, q_: 0}');
    expect(fmt(match(add(mul(x, y), mul(x, z), y), add(mul(p, x), qx)))).toBe('{p_: y + z, q_: y}');
    expect(fmt(match(add(mul(x, y), mul(2, x, z), y), add(mul(p, x), qx)))).toBe('{p_: y + 2*z, q_: y}');
    expect(fmt(match(add(mul(x, y), mul(x, z)), add(mul(r, x), qx)))).toBe('{q_: 0, r_: y + z}');
    expect(fmt(match(add(mul(3, x), mul(3, y)), add(mul(r, x), qx)))).toBe('{q_: 3*y, r_: 3}');
    expect(fmt(match(add(mul(x, y), mul(x, z), 3), add(mul(r, x), qx)))).toBe('{q_: 3, r_: y + z}');
  });
  it('matches sums by collecting on the exact factors', () => {
    expect(fmt(match(add(mul(2, x), mul(3, x, y), 4), add(mul(p, x), q)))).toBe('{p_: 3*y, q_: 2*x + 4}');
    expect(fmt(match(add(mul(x, y), mul(x, z), 3), add(mul(p, x), q)))).toBe('{p_: z, q_: x*y + 3}');
    expect(fmt(match(add(mul(x, y), mul(x, z), mul(y, z)), add(mul(p, x), q)))).toBe('{p_: z, q_: x*y + y*z}');
    expect(fmt(match(add(mul(2, x), mul(2, y)), add(mul(a, x), mul(a, y))))).toBe('{a_: 2}');
    expect(fmt(match(add(mul(3, x), mul(3, y), mul(3, z)), add(mul(p, add(x, y)), q)))).toBe('{p_: 0, q_: 3*x + 3*y + 3*z}');
  });
});

describe('isInstance', () => {
  const d = new Dummy('d');
  it('tests the SymPy classes', () => {
    const cases: [Expr, string, boolean][] = [
      [add(x, y), 'Add', true],
      [mul(2, x), 'Mul', true],
      [pow(x, 2), 'Pow', true],
      [exp(x), 'Pow', false],
      [x, 'Symbol', true],
      [a, 'Symbol', false],
      [a, 'Wild', true],
      [d, 'Dummy', true],
      [x, 'Dummy', false],
      [rational(1, 2), 'Number', true],
      [new Float(1.5), 'Number', true],
      [oo, 'Number', true],
      [pi, 'Number', false],
      [rational(2), 'Integer', true],
      [rational(1, 2), 'Integer', false],
      [rational(1, 2), 'Rational', true],
      [new Float(1.5), 'Float', true],
      [pi, 'NumberSymbol', true],
      [I, 'NumberSymbol', false],
      [I, 'ImaginaryUnit', true],
      [I, 'I', true],
      [sin(x), 'Function', true],
      [f(x), 'Function', true],
      [exp(x), 'Function', true],
      [x, 'Function', false],
      [f(x), 'AppliedUndef', true],
      [sin(x), 'AppliedUndef', false],
      [x, 'Atom', true],
      [sin(x), 'Atom', false],
      [sin(x), 'Expr', true],
      [sin(x), 'Basic', true],
      [exp(x), 'exp', true],
      [E, 'exp', false],
      [new Integral([x, x]), 'Integral', true],
      [Derivative(f(x), x), 'Derivative', true],
      [f(x), 'Derivative', false],
    ];
    for (const [e, t, want] of cases) expect([s(e), t, isInstance(e, t)]).toEqual([s(e), t, want]);
  });
});

describe('find / count', () => {
  const e = add(exp(x), sqrt(x), abs(y), f(x), mul(2, sin(x)), sin(y));
  it('finds by function name', () => {
    expect(find(e, { fn: 'exp' }).map(s)).toEqual(['exp(x)']);
    expect(find(e, { fn: 'sqrt' }).map(s)).toEqual(['sqrt(x)']);
    expect(find(e, { fn: 'Abs' }).map(s)).toEqual(['Abs(y)']);
    expect(find(e, { fn: 'f' }).map(s)).toEqual(['f(x)']);
    expect(find(e, { fn: 'cos' }).map(s)).toEqual([]);
  });
  it('finds by class, pattern and predicate', () => {
    expect(find(e, { type: 'AppliedUndef' }).map(s)).toEqual(['f(x)']);
    expect(find(e, sin(a)).map(s).sort()).toEqual(['sin(x)', 'sin(y)']);
    expect(find(e, (t) => t.key === y.key).map(s)).toEqual(['y']);
  });
  it('counts with repetition', () => {
    // (sin(x) + sin(x)*cos(x)).count(sin) -> 2
    const t = add(sin(x), mul(sin(x), cos(x)));
    expect(count(t, { fn: 'sin' })).toBe(2);
    expect(count(t, { type: 'Symbol' })).toBe(3);
    expect(count(t, sin(a))).toBe(2);
    expect(count(t, (u) => u.key === x.key)).toBe(3);
  });
});

describe('replace (SymPy Basic.replace)', () => {
  const e = add(sin(x), mul(2, cos(y)));
  it('replaces a class with a class', () => {
    expect(s(replace(e, { fn: 'sin' }, { fn: 'cos' }, { apply: (_n, args) => cos(args[0] as Expr) }))).toBe('cos(x) + 2*cos(y)');
    expect(() => replace(e, { fn: 'sin' }, { fn: 'cos' })).toThrow(TypeError);
    // sin(x).replace(sin, Add) etc.: the arguments are passed to the class
    expect(s(replace(add(f(x, y), 1), { fn: 'f' }, { type: 'Add' }))).toBe('x + y + 1');
    expect(s(replace(add(f(x, y), 1), { fn: 'f' }, { type: 'Mul' }))).toBe('x*y + 1');
    expect(s(replace(add(f(x, y), 1), { fn: 'f' }, { type: 'Pow' }))).toBe('x**y + 1');
    expect(s(replace(add(f(x, y), 1), { fn: 'f' }, { type: 'Max' }, { applyType: (_t, args) => Max(...args) }))).toBe('Max(x, y) + 1');
    expect(() => replace(add(f(x, y), 1), { fn: 'f' }, { type: 'Max' })).toThrow(TypeError);
    // exp(x).replace(exp, sin): exp has the single argument x
    expect(s(replace(exp(x), { type: 'exp' }, (u: Expr) => sin(u)))).toBe('sin(x)');
    // a constant replacement for a class query (SymPy raises TypeError: it expects a type or a callable)
    expect(s(replace(e, { type: 'Symbol' }, z))).toBe('sin(z) + 2*cos(z)');
  });
  it('replaces a pattern', () => {
    expect(s(replace(e, sin(a), a))).toBe('x + 2*cos(y)');
    expect(s(replace(e, sin(a), (t: Expr) => cos(t)))).toBe('cos(x) + 2*cos(y)');
    // two Wilds: exact, so a match with a zero value is not replaced (sin(x).replace(a*sin(b), b) keeps 0*... out)
    expect(s(replace(mul(2, sin(x)), mul(a, sin(b)), mul(b, a)))).toBe('2*x');
    // bottom-up: sin(x) itself matches with a = 1 and becomes x + 1 first
    expect(s(replace(mul(2, sin(x)), mul(a, sin(b)), (u: Expr, v: Expr) => add(u, v)))).toBe('2*x + 2');
    expect(s(replace(sin(x), add(a, sin(b)), b))).toBe('sin(x)');
    expect(s(replace(sin(x), add(a, sin(b)), (_u: Expr, v: Expr) => v))).toBe('sin(x)');
    expect(s(replace(sin(x), add(a, sin(b)), b, { exact: false }))).toBe('x');
    // a Wild the match leaves unassigned is passed as 0
    // (SymPy calls the function with the assigned Wilds only, as keywords)
    expect(s(replace(0, mul(a, b), (u: Expr, v: Expr) => add(u, v, 1), { exact: false }))).toBe('1');
    expect(() => replace(e, sin(a), { fn: 'cos' })).toThrow(TypeError);
  });
  it('replaces by a predicate', () => {
    const isSin = (t: Expr) => isInstance(t, 'Function') && s(t).startsWith('sin');
    expect(s(replace(e, isSin, (t: Expr) => mul(2, t)))).toBe('2*sin(x) + 2*cos(y)');
    // a constant replacement for a predicate (SymPy raises TypeError: it expects a callable)
    expect(s(replace(e, isSin, z))).toBe('z + 2*cos(y)');
    expect(() => replace(e, isSin, { fn: 'cos' })).toThrow(TypeError);
  });
  it('returns the mapping with map', () => {
    const [rv, mapping] = replace(e, sin(a), cos(a), { map: true }) as [Expr, Map<Expr, Expr>];
    expect(s(rv)).toBe('cos(x) + 2*cos(y)');
    expect([...mapping].map(([k, v]) => `${s(k)} -> ${s(v)}`)).toEqual(['sin(x) -> cos(x)']);
    // a replacement equal to the node is not recorded
    const [rv2, m2] = replace(e, sin(a), sin(a), { map: true }) as [Expr, Map<Expr, Expr>];
    expect(s(rv2)).toBe(s(e));
    expect(m2.size).toBe(0);
  });
});

describe('count_ops', () => {
  it('counts Sum, Integral and lattice operations like SymPy', () => {
    expect(countOps(Sum(x, [x, 1, n]))).toBe(1);
    expect(s(countOps(Sum(x, [x, 1, n]), { visual: true }))).toBe('SUM');
    // SymPy counts Derivative, Integral and Sum but not Product
    expect(countOps(Product(x, [x, 1, n]))).toBe(0);
    expect(s(countOps(new Integral([x, x]), { visual: true }))).toBe('INTEGRAL');
    expect(s(countOps(Max(x, y, z), { visual: true }))).toBe('2*MAX');
    expect(s(countOps(Min(x, y), { visual: true }))).toBe('MIN');
  });
});

describe('match (SymPy Basic.match)', () => {
  const a = new Wild('a');
  const b = new Wild('b', { exclude: [x] });
  const p = new Wild('p');
  const q = new Wild('q');
  const r = new Wild('r');
  it('matches products and powers', () => {
    expect(fmt2(match(mul(3, pow(x, 2)), mul(a, x)))).toBe('{a_: 3*x}');
    expect(fmt2(match(mul(3, pow(x, 2)), mul(b, x)))).toBe('None');
    expect(fmt2(match(mul(4, pow(x, 2)), mul(p, pow(q, r))))).toBe('{p_: 4, q_: x, r_: 2}');
    expect(fmt2(match(pow(add(x, y), add(x, y)), pow(p, p)))).toBe('{p_: x + y}');
  });
  it('matches sums', () => {
    expect(fmt2(match(add(2, mul(3, y)), add(mul(a, x), mul(b, y))))).toBe('{a_: 2/x, b_: 3}');
  });
});

describe('replace / find / count_ops', () => {
  const a = new Wild('a');
  const f = add(log(sin(x)), tan(sin(pow(x, 2))));
  it('replaces functions and patterns', () => {
    expect(str(replace(f, { fn: 'sin' }, { fn: 'cos' }, { apply: (_n, args) => cos(args[0]!) }) as never)).toBe('log(cos(x)) + tan(cos(x**2))');
    expect(str(replace(f, sin(a), tan(a)) as never)).toBe('log(tan(x)) + tan(tan(x**2))');
    expect(str(replace(f, sin(a), a) as never)).toBe('log(x) + tan(x**2)');
    expect(str(replace(mul(x, y), mul(a, x), a) as never)).toBe('y');
  });
  it('finds and counts', () => {
    expect(find(f, { fn: 'sin' }).map(str).sort()).toEqual(['sin(x)', 'sin(x**2)']);
    expect(countOps(add(x, mul(2, y), sin(z)))).toBe(4);
  });
});

describe('small core functions', () => {
  it('match SymPy', async () => {
    const { count, asCoeffExponent, asPowersDict, Rem } = await import('../../src');
    const [x, y] = symbols('x y');
    expect(count(parse('x*sin(x) + x'), x)).toBe(3);
    expect(asCoeffExponent(parse('x**3*y'), x).map((e) => sstr(e))).toEqual(['y', '3']);
    expect([...asPowersDict(parse('x**2*y'))].map(([b, e]) => `${sstr(b)}:${sstr(e)}`).sort()).toEqual(['x:2', 'y:1']);
    expect(sstr(Rem(-7, 3))).toBe('-1');
    expect(sstr(Rem(parse('x**3'), y))).toBe('Rem(x**3, y)');
    expect(sstr(Rem(parse('x**3'), y).subs([[x, -5], [y, 3]] as never))).toBe('-2');
  });
});

it('finds symbols by name while preserving dummy identity', () => {
  const x = symbols('x')[0]!, d = new Dummy('x');
  expect(find('x', x)).toBe(x);
  expect(find('x', d)).toBe(d);
  expect(() => find('y', x)).toThrow('could not find');
  expect(() => find('x', add(x,d))).toThrow('ambiguous');
  expect(() => Reflect.apply(find, undefined, ['x', {fn:'sin'}])).toThrow(TypeError);
});

describe('relational classes in queries (SymPy Basic.has(Le))', () => {
  it('finds relations by their SymPy class', () => {
    const [a, b] = sj.symbols('a b');
    const e = sj.and(sj.Le(a, b), sj.Eq(a, 1));
    expect(sj.find(e, { type: 'Relational' })).toHaveLength(2);
    expect(sj.find(e, { type: 'LessThan' })).toHaveLength(1);
    expect(sj.find(e, { type: 'StrictLessThan' })).toHaveLength(0);
    expect(sj.find(e, { type: 'Equality' })).toHaveLength(1);
    expect(sj.find(sj.add(a, 1), { type: 'GreaterThan' })).toHaveLength(0);
  });
});

it('matches noncommutative products in order with contiguous wildcard ranges', () => {
  const [A, B, C] = sj.symbols('A B C', { commutative: false });
  const [x, y] = sj.symbols('x y');
  const u = new Wild('u'), w = new Wild('w', { commutative: false });
  const z = new Wild('z', { commutative: false });
  const render = (e: sj.Expr, p: sj.Expr) => {
    const result = sj.match(e, p);
    return result instanceof Map ? new Map([...result].map(([k, v]) => [k.toString(), v.toString()])) : undefined;
  };
  expect(render(sj.mul(x, y, A, B), sj.mul(u, w))).toEqual(new Map([['u_', 'x*y'], ['w_', 'A*B']]));
  expect(render(sj.mul(A, B), sj.mul(w, z))).toEqual(new Map([['w_', 'A'], ['z_', 'B']]));
  expect(render(sj.mul(A, C, B, A, C), sj.mul(w, B, w))).toEqual(new Map([['w_', 'A*C']]));
  expect(render(sj.mul(A, B), new sj.Mul([w, w]))).toBeUndefined();
  expect(render(A, sj.mul(w, z))).toBeUndefined();
  expect(render(sj.mul(x, A), sj.mul(y, w))).toBeUndefined();
  expect(render(sj.mul(x, A), sj.mul(u, x))).toBeUndefined();
  expect(render(x, sj.mul(u, w))).toBeUndefined();
  expect(render(A, u)).toEqual(new Map([['u_', 'A']]));
  expect(render(sj.mul(A, B), sj.mul(w, A))).toBeUndefined();
  expect(render(sj.mul(sj.pow(A, 2), B), sj.mul(A, w))).toEqual(new Map([['w_', 'A*B']]));
  expect(render(sj.mul(sj.pow(A, -1), B), sj.mul(w, B))).toEqual(new Map([['w_', 'A**(-1)']]));
});

it('preserves structural discriminators and constrained associative matches', () => {
  const [x, y] = sj.symbols('x y');
  const w = new Wild('w'), n = new Wild('n');
  const rawMatch = (e: sj.Expr, p: sj.Expr) => {
    const result = sj.match(e, p);
    return result instanceof Map ? new Map([...result].map(([k, v]) => [String(k), String(v)])) : undefined;
  };
  expect(rawMatch(sj.pow(x, 2), sj.exp(w))).toBeUndefined();
  expect(rawMatch(sj.Ne(x, y), sj.Eq(w, y))).toBeUndefined();
  expect(rawMatch(sj.Tuple(x), sj.Dict([[w, y]]))).toBeUndefined();
  expect(rawMatch(sj.rational(1), sj.pow(w, n))).toEqual(new Map([['n_', '0']]));
  expect(rawMatch(sj.rational(3), new sj.Add([sj.rational(1), w]))).toEqual(new Map([['w_', '2']]));
  expect(rawMatch(sj.mul(2, x), new sj.Add([w, w]))).toEqual(new Map([['w_', 'x']]));
  expect(rawMatch(sj.mul(-2, x), new sj.Add([w, w]))).toEqual(new Map([['w_', '-x']]));
  expect(rawMatch(sj.pow(x, -2), new sj.Mul([w, w]))).toBeUndefined();
  const cancelled = sj.match(sj.mul(x, sj.sin(y)), new sj.Mul([x, y, w]), { old: true });
  expect(cancelled instanceof Map ? String(cancelled.get(w)) : '').toBe('sin(y)/y');
  expect(countOps(sj.E)).toBe(1);
});

it('honors extension pattern hooks for find and replace', () => {
  class Pattern extends sj.ExtensionExpr {
    constructor(readonly accept: boolean) { super('Pattern', []); }
    withArgs(): sj.Expr { return this; }
    override matchesSelf(e: sj.Expr): ReadonlyMap<sj.Expr, sj.Expr> | false { return this.accept ? new Map([[x, e]]) : false; }
  }
  const [x] = sj.symbols('x');
  expect(sj.find(x, new Pattern(false))).toEqual([]);
  expect(sj.find(x, new Pattern(true))).toEqual([x]);
});

it('distinguishes names of extension calls sharing a node class', () => {
  class Call extends sj.ExtensionExpr {
    constructor(name: string, args: readonly sj.Expr[]) { super(name, args); }
    withArgs(args: readonly sj.Expr[]): sj.Expr { return new Call(this.name, args); }
  }
  const x = sj.symbol('x'), w = new Wild('w');
  expect(sj.match(new Call('g', [x]), new Call('f', [w]))).toBeInstanceOf(sj.NoMatchResult);
  const result = sj.match(new Call('f', [x]), new Call('f', [w]));
  expect(result instanceof Map ? String(result.get(w)) : '').toBe('x');
});

it('controls rematching of a child exposed by rebuilding', () => {
  const [x, y] = sj.symbols('x y');
  const original = sj.mul(y, sj.sin(x));
  const reduce = (arg: sj.Expr) => sj.sin(arg).div(y);
  const [value, mapping] = sj.replace(original, { fn: 'sin' }, reduce, { map: true }) as [sj.Expr, Map<sj.Expr, sj.Expr>];
  expect(value.key).toBe(sj.sin(x).key);
  expect(mapping.size).toBe(1);
  expect((sj.replace(original, { fn: 'sin' }, reduce, { simultaneous: false }) as sj.Expr).key).toBe(reduce(x).key);
  const order = sj.O(x.sub(1).pow(3), x, 1);
  expect(sj.replace(order, { type: 'Pow' }, (base, exponent) => base.pow(exponent).div(exponent))).toBeInstanceOf(sj.Order);
});

it('counts operations in a matrix product and matches through the registered hook', () => {
  const x = sj.symbol('x');
  const a = sj.MatrixSymbol('A', 2, 2), b = sj.MatrixSymbol('B', 2, 2);
  expect(impl.match?.(x, x)).toEqual(new Map());
  expect(String(sj.countOps(new MatMulNode([sj.S.NegOne, a]), { visual: true }))).toBe('NEG');
  expect(String(sj.countOps(new MatMulNode([sj.S.NegOne, a, b]), { visual: true }))).toBe('MATMUL + NEG');
  expect(String(sj.countOps(new MatMulNode([a, b]), { visual: true }))).toBe('MATMUL');
});
