// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/unify/usympy.ts (SymPy sympy/unify/usympy.py).
// Cases from sympy/unify/tests/test_sympy.py and the doctests; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Add, And, Basic, BasicNode, FiniteSet, Gt, Interval, Lt, MatrixSymbol, Max, Mul, Not, Rational, Union, add, cos, mul, pow, sin, str, symbols } from '../../src';
import type { Expr } from '../../src';
import { Str } from '../../src/matrices';
import * as unifyEntry from '../../src/unify';
import { BoolOp } from '../../src/core/boolalg';
import { Fn, Limit, Pow } from '../../src/core/nodes';
import { Compound, CondVariable, Variable, termEquals } from '../../src/unify/core';
import { ExprOp, construct, deconstruct, isAssociative, isCommutative, mkMatchtype, rebuild, unify } from '../../src/unify/usympy';

const [x, y, z, n, p, q, a, b, c, d] = symbols('x y z n p q a b c d');
const N = (v: number): Expr => Rational.of(v);
const op = (e: Expr): ExprOp => new ExprOp(e);

/** A substitution printed with sorted entries, as SymPy prints a dict. */
const show = (m: ReadonlyMap<Expr, Expr>): string => `{${[...m].map(([k, v]) => `${str(k)}: ${str(v)}`).sort().join(', ')}}`;
const showAll = (ms: Iterable<ReadonlyMap<Expr, Expr>>): string[] => [...ms].map(show);
/** SymPy iterdicteq: the same number of results, each one expected. */
const iterdicteq = (got: Iterable<ReadonlyMap<Expr, Expr>>, expected: string[]): void => {
  const g = showAll(got);
  expect(g.length).toBe(expected.length);
  for (const s of g) expect(expected).toContain(s);
};

describe('deconstruct and construct', () => {
  it('deconstruct', () => {
    const expr = Basic(1, 2, 3);
    expect(termEquals(deconstruct(expr), new Compound(op(Basic()), [N(1), N(2), N(3)]))).toBe(true);
    expect(deconstruct(1)).toBe(1);
    expect(deconstruct(x)).toBe(x);
    expect(termEquals(deconstruct(x, [x]), new Variable(x))).toBe(true);
    expect(termEquals(deconstruct(new Add([N(1), x])), new Compound(op(add(x, y)), [N(1), x]))).toBe(true);
    expect(termEquals(deconstruct(new Add([N(1), x]), [x]), new Compound(op(add(x, y)), [N(1), new Variable(x)]))).toBe(true);
    const v = new CondVariable(x, () => true);
    expect(deconstruct(v)).toBe(v);
  });

  it('construct', () => {
    const expr = new Compound(op(Basic()), [N(1), N(2), N(3)]);
    expect(str(construct(expr) as Expr)).toBe('Basic(1, 2, 3)');
    expect(construct(new Variable(x))).toBe(x);
    expect(construct('leaf')).toBe('leaf');
    // a Compound of another kind is left as it is
    const other = new Compound('Add', [1]);
    expect(construct(other)).toBe(other);
    // sums, products, powers, And/Or and Min/Max are built without evaluation
    expect(str(construct(new Compound(op(add(x, y)), [N(1), N(2)])) as Expr)).toBe('1 + 2');
    expect(construct(new Compound(op(pow(x, y)), [N(2), N(3)]))).toBeInstanceOf(Pow);
    expect(construct(new Compound(op(And(x, y)), [x, x]))).toBeInstanceOf(BoolOp);
    expect(construct(new Compound(op(Max(x, y)), [N(1), N(2)]))).toBeInstanceOf(Fn);
    // other nodes are rebuilt with evaluation
    expect(str(construct(new Compound(op(sin(x)), [N(0)])) as Expr)).toBe('0');
    expect(() => construct(new Compound(op(sin(x)), ['s']))).toThrow(TypeError);
  });

  it('nested', () => {
    const expr = Basic(1, Basic(2), 3);
    const cmpd = new Compound(op(Basic()), [N(1), new Compound(op(Basic()), [N(2)]), N(3)]);
    expect(termEquals(deconstruct(expr), cmpd)).toBe(true);
    expect((construct(cmpd) as Expr).key).toBe(expr.key);
  });

  it('non frankenAdds', () => {
    // the is_commutative property used to fail because of Basic.__new__
    const rebuilt = construct(deconstruct(add(x, mul(y, 2)))) as Expr;
    expect(str(rebuilt)).toBe('x + 2*y');
    expect(rebuilt.isCommutative).toBe(true);
    expect(str(rebuild(add(x, mul(y, 2))))).toBe('x + 2*y');
  });

  it('rebuild (SymPy sympy.unify.rebuild)', () => {
    // SymPy: rebuild(Basic.__new__(Add, S(1), S(2))) is 1 + 2 with args (1, 2), Mul likewise 2*3;
    // other classes are rebuilt with evaluation: rebuild(Basic.__new__(sin, S(0))) == 0
    const s1 = rebuild(new Add([N(1), N(2)]));
    expect(str(s1)).toBe('1 + 2');
    expect(s1.args).toEqual([N(1), N(2)]);
    expect(rebuild(new Mul([N(2), N(3)])).args).toEqual([N(2), N(3)]);
    expect(str(rebuild(new Fn('sin', [N(0)])))).toBe('0');
    // the unify entry does not export the core rebuild (which evaluates) under this name
    expect(Object.keys(unifyEntry)).not.toContain('rebuild');
    expect(unifyEntry.usympy.rebuild).toBe(rebuild);
  });

  it('ExprOp', () => {
    expect(String(op(sin(x)))).toBe('sin');
    expect(op(sin(x)).unifyKey).toBe(op(sin(y)).unifyKey);
    expect(op(sin(x)).unifyKey).not.toBe(op(cos(x)).unifyKey);
    // a limit from the left is another operator than one from the right
    expect(op(new Limit([x, x, N(0)], '-')).unifyKey).not.toBe(op(new Limit([x, x, N(0)], '+')).unifyKey);
  });
});

describe('class properties', () => {
  it('is_commutative and is_associative', () => {
    expect(isAssociative(deconstruct(new Add([a, c])))).toBe(true);
    expect(isCommutative(deconstruct(new Add([a, c])))).toBe(true);
    expect(isCommutative(deconstruct(add(x, y)))).toBe(true);
    expect(isCommutative(deconstruct(mul(x, y)))).toBe(true);
    expect(isCommutative(deconstruct(pow(x, y)))).toBe(false);
    expect(isCommutative(x)).toBe(false);
    expect(isAssociative(x)).toBe(false);
    // And and Or are associative but not commutative for the unifier (SymPy LatticeOp)
    expect(isAssociative(deconstruct(And(x, y)))).toBe(true);
    expect(isCommutative(deconstruct(And(x, y)))).toBe(false);
    expect(isAssociative(deconstruct(Not(x)))).toBe(false);
    expect(isAssociative(deconstruct(Max(x, y)))).toBe(true);
    expect(isAssociative(deconstruct(sin(x)))).toBe(false);
    // a product of noncommutative factors is not commutative
    const [A, B] = symbols('A B', { commutative: false });
    expect(isCommutative(deconstruct(mul(A, B)))).toBe(false);
    // matrix sums and products, unions, intersections and finite sets
    const X = MatrixSymbol('X', 2, 2);
    const Y = MatrixSymbol('Y', 2, 2);
    expect(isAssociative(deconstruct(X.add(Y)))).toBe(true);
    expect(isCommutative(deconstruct(X.add(Y)))).toBe(true);
    expect(isAssociative(deconstruct(X.mul(Y)))).toBe(true);
    expect(isCommutative(deconstruct(X.mul(Y)))).toBe(false);
    expect(isAssociative(deconstruct(X))).toBe(false);
    expect(isCommutative(deconstruct(X))).toBe(false);
    expect(isCommutative(deconstruct(FiniteSet.of(x, y)))).toBe(true);
    expect(isAssociative(deconstruct(Interval.of(x, y)))).toBe(false);
    expect(isCommutative(deconstruct(Interval.of(x, y)))).toBe(false);
  });

  it('mk_matchtype', () => {
    const isSin = mkMatchtype('sin');
    expect(isSin(sin(x))).toBe(true);
    expect(isSin(deconstruct(sin(x)))).toBe(true);
    expect(isSin(cos(x))).toBe(false);
    expect(isSin('sin')).toBe(false);
  });
});

describe('unify', () => {
  it('unify', () => {
    const expr = Basic(1, 2, 3);
    const pattern = Basic(a, b, c);
    expect(showAll(unify(expr, pattern, new Map(), [a, b, c]))).toEqual(['{a: 1, b: 2, c: 3}']);
    expect(showAll(unify(expr, pattern, null, [a, b, c]))).toEqual(['{a: 1, b: 2, c: 3}']);
  });

  it('variables', () => {
    expect(showAll(unify(Basic(1, 2), Basic(1, x), new Map(), [x]))).toEqual(['{x: 2}']);
  });

  it('s input', () => {
    const expr = Basic(1, 2);
    const pattern = Basic(a, b);
    expect(showAll(unify(expr, pattern, new Map(), [a, b]))).toEqual(['{a: 1, b: 2}']);
    expect(showAll(unify(expr, pattern, new Map([[a, 5]]), [a, b]))).toEqual([]);
    expect(showAll(unify(expr, pattern, new Map([[a, 1]]), [a, b]))).toEqual(['{a: 1, b: 2}']);
  });

  it('commutative', () => {
    const expr = new Add([N(1), N(2), N(3)]);
    const pattern = new Add([a, b, c]);
    iterdicteq(unify(expr, pattern, new Map(), [a, b, c]), [
      '{a: 1, b: 2, c: 3}',
      '{a: 1, b: 3, c: 2}',
      '{a: 2, b: 1, c: 3}',
      '{a: 2, b: 3, c: 1}',
      '{a: 3, b: 1, c: 2}',
      '{a: 3, b: 2, c: 1}',
    ]);
  });

  it('iter', () => {
    const expr = new Add([N(1), N(2), N(3)]);
    const pattern = new Add([a, c]);
    // SymPy 1.14 yields these 12 substitutions in this order (sums unevaluated)
    expect(showAll(unify(expr, pattern, new Map(), [a, c]))).toEqual([
      '{a: 1, c: 2 + 3}',
      '{a: 1 + 2, c: 3}',
      '{a: 1, c: 2 + 3}',
      '{a: 1 + 3, c: 2}',
      '{a: 2, c: 1 + 3}',
      '{a: 1 + 2, c: 3}',
      '{a: 2, c: 1 + 3}',
      '{a: 2 + 3, c: 1}',
      '{a: 3, c: 1 + 2}',
      '{a: 1 + 3, c: 2}',
      '{a: 3, c: 1 + 2}',
      '{a: 2 + 3, c: 1}',
    ]);
  });

  it('doctests', () => {
    expect(show(unify(Basic(1, 2), Basic(1, x), null, [x]).next().value as ReadonlyMap<Expr, Expr>)).toBe('{x: 2}');
    expect(show(unify(add(mul(2, x), y, z), add(mul(2, p), q), new Map(), [p, q]).next().value as ReadonlyMap<Expr, Expr>)).toBe('{p: x, q: y + z}');
    expect([...unify(add(x, y, z), add(p, q), new Map(), [p, q])].length).toBe(12);
    expect(show(unify(add(mul(x, y, z), 3), add(mul(x, y), 3), new Map(), [x, y]).next().value as ReadonlyMap<Expr, Expr>)).toBe('{x: y, y: x*z}');
    expect(show(unify(add(mul(x, y), 3), add(p, 3), new Map(), [p]).next().value as ReadonlyMap<Expr, Expr>)).toBe('{p: x*y}');
  });

  it('hard match', () => {
    const expr = add(sin(x), pow(cos(x), 2));
    const pattern = add(sin(p), pow(cos(p), 2));
    expect(showAll(unify(expr, pattern, new Map(), [p, q]))).toEqual(['{p: x}']);
  });

  it('matrix', () => {
    const X = MatrixSymbol('X', n, n);
    const Y = MatrixSymbol('Y', 2, 2);
    const Z = MatrixSymbol('Z', 2, 3);
    expect(showAll(unify(X, Y, new Map(), [n, new Str('X')]))).toEqual(['{X: Y, n: 2}']);
    expect(showAll(unify(X, Z, new Map(), [n, new Str('X')]))).toEqual([]);
  });

  it('FiniteSet commutativity', () => {
    const s = FiniteSet.of(a, b, c);
    const t = FiniteSet.of(x, y);
    expect(showAll(unify(s, t, null, [x, y]))).toContain('{x: {a, c}, y: b}');
  });

  it('FiniteSet complex', () => {
    const expr = FiniteSet.of(Basic(1, x), y, Basic(x, z));
    const pattern = FiniteSet.of(a, Basic(x, b));
    const expected = ['{a: {y, Basic(x, z)}, b: 1}', '{a: {y, Basic(1, x)}, b: z}'];
    for (const s of showAll(unify(expr, pattern, null, [a, b]))) expect(expected).toContain(s);
  });

  it('And', () => {
    iterdicteq(unify(And(Gt(z, 0), Lt(n, 3)), And(x, y), null, [x, y]), ['{x: z > 0, y: n < 3}']);
  });

  it('Union', () => {
    // SymPy: [{Interval(12, 13): Interval(10, 11)}]
    const got = showAll(unify(Union(Interval.of(0, 1), Interval.of(10, 11)), Union(Interval.of(0, 1), Interval.of(12, 13)), null, [Interval.of(12, 13)]));
    expect(got).toEqual(['{Interval(12, 13): Interval(10, 11)}']);
  });

  it('commutative in commutative', () => {
    const eq = add(mul(sin(3), sin(4), sin(5)), mul(4, cos(3), cos(4)));
    const pat = add(mul(a, cos(b), cos(c)), mul(d, sin(b), sin(c)));
    const first = unify(eq, pat, null, [a, b, c, d]).next();
    expect(first.done).toBe(false);
    // SymPy: {a: 4, b: 3, c: 4, d: sin(5)}
    expect(show(first.value as ReadonlyMap<Expr, Expr>)).toBe('{a: 4, b: 3, c: 4, d: sin(5)}');
  });

  it('unevaluated arguments', () => {
    expect(showAll(unify(new Mul([N(2), x]), new Mul([N(2), p]), null, [p]))).toEqual(['{p: x}']);
    expect(str(new BasicNode([x], 'T'))).toBe('T(x)');
  });
});
