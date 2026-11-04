// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/tree.ts (SymPy sympy/strategies/tree.py).
// Cases from sympy/strategies/tests/test_tree.py and the doctests; expected values are SymPy 1.14's.
// A Python tuple of a strategic tree is a TreeTuple, a list an array.

import { describe, expect, it } from 'vitest';
import { chain, minimize, tree } from '../../src/strategies';
import type { Rule, StrategyTree } from '../../src/strategies';

const { TreeTuple, allresults, brute, greedy, treeapply } = tree;
const T = (...items: unknown[]) => new TreeTuple(...items);
/** A tuple of a strategic tree of rules on numbers. */
const R = (...items: StrategyTree<Rule<number>>[]) => new TreeTuple(...items);
/** A join table: container types to functions. */
const J = (...pairs: [tree.TreeContainer, tree.TreeFunction][]) => new Map(pairs);

const inc = (x: number): number => x + 1;
const dec = (x: number): number => x - 1;
const double = (x: number): number => 2 * x;
const square = (x: number): number => x ** 2;
const add = (...args: number[]): number => args.reduce((s, v) => s + v, 0);
const mul = (...args: number[]): number => args.reduce((s, v) => s * v, 1);
const min = (...args: number[]): number => Math.min(...args);
const max = (...args: number[]): number => Math.max(...args);

describe('treeapply', () => {
  it('applies functions onto a tree', () => {
    const t = T([3, 3], [4, 1], 2);
    expect(treeapply(t, J([Array, min], [TreeTuple, max]))).toBe(3);
    expect(treeapply(t, J([Array, add], [TreeTuple, mul]))).toBe(60);
    // doctests
    const t2 = [T(3, 2), T(4, 1)];
    expect(treeapply(t2, J([Array, max], [TreeTuple, min]))).toBe(2);
    expect(treeapply(t2, J([Array, mul], [TreeTuple, add]))).toBe(25);
  });

  it('maps the leaves', () => {
    expect(treeapply(3, new Map(), (x: number) => x ** 2)).toBe(9);
    const t = T([3, 3], [4, 1], 2);
    const tp1 = T([4, 4], [5, 2], 3);
    const join = J([Array, min], [TreeTuple, max]);
    expect(treeapply(t, join, (x: number) => x + 1)).toBe(treeapply(tp1, join));
  });

  it('builds strategies', () => {
    const join = J([Array, chain], [TreeTuple, minimize]);
    expect(treeapply(inc, join)).toBe(inc);
    expect((treeapply(R(inc, dec), join) as Rule<number>)(5)).toBe(minimize(inc, dec)(5));
    expect((treeapply([inc, dec], join) as Rule<number>)(5)).toBe(chain(inc, dec)(5));
    const t = R(inc, [dec, double]); // either inc or dec-then-double
    expect((treeapply(t, join) as Rule<number>)(5)).toBe(6);
    expect((treeapply(t, join) as Rule<number>)(1)).toBe(0);

    const maximize = (...rules: Rule<number>[]) => minimize(...rules, { objective: (x: number) => -x });
    const fn = treeapply(t, J([Array, chain], [TreeTuple, maximize])) as Rule<number>;
    expect(fn(4)).toBe(6); // highest value comes from the dec then double
    expect(fn(1)).toBe(2); // highest value comes from the inc
  });

  it('rejects a container type that is not iterable', () => {
    class Box {}
    expect(() => treeapply(new Box(), J([Box, add]))).toThrow(TypeError);
  });
});

describe('executing strategic trees', () => {
  it('greedy', () => {
    const t = [inc, R(dec, double)]; // either inc or dec-then-double
    const fn = greedy(t, (x) => -x);
    expect(fn(4)).toBe(6);
    expect(fn(1)).toBe(2);
    // doctests: the lowest value
    expect(greedy(t)(4)).toBe(5);
    expect(greedy(t)(1)).toBe(0);

    const t2 = [inc, dec, [inc, dec, [R(inc, inc), R(dec, dec)]]];
    expect(greedy(t2)(10)).toBe(8);
    expect(greedy(t2, (x) => -x)(10)).toBe(12);
  });

  it('allresults', () => {
    expect(new Set(allresults(inc)(3))).toEqual(new Set([inc(3)]));
    expect(new Set(allresults([inc, dec])(3))).toEqual(new Set([2, 4]));
    expect(new Set(allresults(R(inc, dec))(3))).toEqual(new Set([3]));
    expect(new Set(allresults([inc, R(dec, double)])(4))).toEqual(new Set([5, 6]));
  });

  it('brute', () => {
    const t = R([inc, dec], square);
    const fn = brute(t, (x) => -x);
    expect(fn(2)).toBe((2 + 1) ** 2);
    expect(fn(-2)).toBe((-2 - 1) ** 2);
    expect(brute(inc)(1)).toBe(2);
    // a leaf that yields nothing leaves no result
    expect(() => brute(inc, (x) => x, () => function* () {})(1)).toThrow(RangeError);
  });

  it('TreeTuple is iterable', () => {
    expect([...T(1, 2)]).toEqual([1, 2]);
  });
});
