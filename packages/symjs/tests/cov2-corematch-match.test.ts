// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Pattern matching, replace / find / count and count_ops (core/match.ts).
// Expected values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import {
  Derivative,
  Dummy,
  E,
  Float,
  I,
  Integral,
  Max,
  Min,
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
  match,
  mul,
  oo,
  pi,
  pow,
  rational,
  replace,
  sin,
  sqrt,
  str,
  symbols,
} from '../src';
import type { Expr } from '../src';

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
