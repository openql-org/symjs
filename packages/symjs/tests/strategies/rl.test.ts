// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/rl.ts (SymPy sympy/strategies/rl.py).
// Cases from sympy/strategies/tests/test_rl.py and the doctests; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Add, Basic, BasicNode, Mul, Or, And, Rational, add, asCoeffMul, mul, str, symbols } from '../../src';
import type { Expr } from '../../src';
import { distribute, flatten, glom, rebuild, rmId, sort, unpack } from '../../src/strategies';
import { subs } from '../../src/strategies/rl';
import { exprFns } from '../../src/strategies/util';
import * as utilities from '../../src/utilities';
import * as core from '../../src/core';

const [x, y] = symbols('x y');
const n = (v: number): Expr => Rational.of(v);
const eq = (a: Expr, b: Expr): void => expect(a.key).toBe(b.key);

describe('rules', () => {
  it('rm_id', () => {
    const rmzeros = rmId((e) => e.equals(0));
    eq(rmzeros(Basic(0, 1)), Basic(1));
    eq(rmzeros(Basic(0, 0)), Basic(0));
    eq(rmzeros(Basic(2, 1)), Basic(2, 1));
    // doctest: remove_zeros(Basic(S(1), S(0), S(2))) == Basic(1, 2)
    expect(str(rmzeros(Basic(1, 0, 2)))).toBe('Basic(1, 2)');
    // the node is rebuilt without evaluation: Mul(1, x, 1, evaluate=False) -> Mul(x) with args (x,)
    const r = rmId((e) => e.equals(1))(new Mul([n(1), x, n(1)]));
    expect(r).toBeInstanceOf(Mul);
    expect(r.args).toEqual([x]);
    // or with the given constructor
    eq(rmId((e) => e.equals(1), exprFns.new)(new Mul([n(1), x, n(1)])), x);
  });

  it('glom', () => {
    const key = (e: Expr): Expr => mul(...asCoeffMul(e)[1]);
    const count = (e: Expr): Expr => asCoeffMul(e)[0];
    const combine = (cnt: Expr, arg: Expr): Expr => mul(cnt, arg);
    const rl = glom(key, count, combine);
    const result = rl(new Add([x, mul(-1, x), mul(3, x), n(2), n(3)]));
    // SymPy: 3*x + 5 (as the set of arguments of Add(3*x, 5))
    expect(new Set(result.args.map(str))).toEqual(new Set(['3*x', '5']));
    expect(str(result)).toBe('3*x + 5');
    // nothing to gather: the node itself
    const e = new Add([x, n(2)]);
    expect(rl(e)).toBe(e);
  });

  it('flatten', () => {
    eq(flatten(Basic(1, 2, Basic(3, 4))), Basic(1, 2, 3, 4));
    // only arguments of the same class are spliced in
    const t = (...args: Expr[]) => new BasicNode(args, 'T');
    expect(str(flatten(t(n(1), Basic(2, 3), t(n(4)))))).toBe('T(1, Basic(2, 3), 4)');
    // Add(x, Add(y, 2, evaluate=False), evaluate=False) -> args (x, y, 2)
    expect(flatten(new Add([x, new Add([y, n(2)])])).args).toEqual([x, y, n(2)]);
    // with evaluation
    expect(str(flatten(new Add([x, new Add([x, n(2)])]), exprFns.new))).toBe('2*x + 2');
    // one definition: the flatten of the iterable utilities
    expect(flatten).toBe(utilities.flatten);
    expect(utilities.flatten([1, [2, [3]]])).toEqual([1, 2, 3]);
    expect(utilities.flatten([1, [2, [3]]], { levels: 1 })).toEqual([1, 2, [3]]);
    // a constructor goes only with an expression
    expect(() => (utilities.flatten as (a: unknown, b: unknown) => unknown)([1], exprFns.new)).toThrow(TypeError);
  });

  it('unpack', () => {
    eq(unpack(Basic(2)), n(2));
    eq(unpack(Basic(2, 3)), Basic(2, 3));
  });

  it('sort', () => {
    eq(sort(str)(Basic(3, 1, 2)), Basic(1, 2, 3));
    expect(str(sort((e) => -Number(str(e)), exprFns.new)(Basic(3, 1, 2)))).toBe('Basic(3, 2, 1)');
  });

  it('distribute', () => {
    const T1 = (...args: Expr[]) => new BasicNode(args, 'T1');
    const T2 = (...args: Expr[]) => new BasicNode(args, 'T2');
    const distributeT12 = distribute('T1', 'T2');
    eq(distributeT12(T1(n(1), n(2), T2(n(3), n(4)), n(5))), T2(T1(n(1), n(2), n(3), n(5)), T1(n(1), n(2), n(4), n(5))));
    eq(distributeT12(T1(n(1), n(2), n(3))), T1(n(1), n(2), n(3)));
    // a node of another class is rebuilt as an A, as in SymPy: distribute(T1, T2)(T2(T2(S(1)))) == T2(T1(1))
    eq(distributeT12(T2(T2(n(1)))), T2(T1(n(1))));
    // with the constructor of the class given
    const dist = distribute({ name: 'T1', construct: (args) => T1(...args, n(0)) }, 'T2');
    eq(dist(Basic(T2(n(1)))), T2(T1(n(1), n(0))));
    eq(distribute({ name: 'T1', construct: (args) => T1(...args) }, { name: 'T2', construct: (args) => T2(...args) })(T1(T2(n(1), n(2)))), T2(T1(n(1)), T1(n(2))));
  });

  it('distribute Mul over Add', () => {
    const expr = new Mul([n(2), add(x, y)]);
    expect(str(expr)).toBe('2*(x + y)');
    const r = distribute('Mul', 'Add')(expr);
    eq(r, add(mul(2, x), mul(2, y)));
    expect(str(r)).toBe('2*x + 2*y');
    // SymPy values: distribute(Mul, Add)(Basic(S(2), x + y)) == 2*x + 2*y,
    // distribute(Add, Mul)(Basic(S(2), Mul(3, x, evaluate=False))) == 5*x + 10,
    // distribute(And, Or)(Basic(x, Or(x, y))) == x | (x & y), distribute(Pow, Add)(Basic(x + y, S(2))) == x**2 + y**2
    expect(str(distribute('Mul', 'Add')(Basic(2, add(x, y))))).toBe('2*x + 2*y');
    expect(str(distribute('Add', 'Mul')(Basic(2, new Mul([n(3), x]))))).toBe('5*x + 10');
    expect(str(distribute('And', 'Or')(Basic(x, Or(x, y))))).toBe('x | (x & y)');
    expect(str(distribute('Pow', 'Add')(Basic(add(x, y), 2)))).toBe('x**2 + y**2');
    // distribute(Or, And)(Basic(x, And(x, y))) == x & (x | y)
    expect(str(distribute('Or', 'And')(Basic(x, And(x, y))))).toBe('x & (x | y)');
  });

  it('subs', () => {
    const rl = subs(1, 2);
    expect(rl(1)).toBe(2);
    expect(rl(3)).toBe(3);
    eq(subs<Expr>(x, y)(x), y);
  });

  it('rebuild', () => {
    eq(rebuild(new Add([n(1), n(2)])), n(3));
    // one definition: the rebuild of the core
    expect(rebuild).toBe(core.rebuild);
  });
});
