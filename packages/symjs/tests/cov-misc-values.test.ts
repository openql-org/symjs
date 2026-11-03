// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Coverage of the value helpers behind the iterables utilities:
 * expected values are SymPy 1.14 `default_sort_key`, `_nodes` and
 * `ordered`, and Python's comparison of the corresponding values.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Derivative, Float, Rational } from '../src/core/nodes';
import { ValueMap, compareValues, defaultSortKeyOf, nodesOf, orderedValues, valueEquals, valueKey } from '../src/utilities/values';

const [x, y, n] = sj.symbols('x y n');
const f = sj.SymFunction('f');
const ONE: unknown = [[1, 0, 'Number'], [0, []], [], 1];
const num = (k: number): unknown => [[1, 0, 'Number'], [0, []], [], k];

describe('default_sort_key of containers', () => {
  it('{2, 1}', () => {
    expect(defaultSortKeyOf(new Set([2, 1]))).toEqual([[10, 0, 'set'], [2, [num(1), num(2)]], ONE, 1]);
  });
  it('{x: 1}', () => {
    const xk = [[2, 0, 'Symbol'], [1, ['x']], ONE, 1];
    expect(defaultSortKeyOf(new Map([[x, 1]]))).toEqual([[10, 0, 'dict'], [1, [[[10, 0, 'tuple'], [2, [xk, num(1)]], ONE, 1]]], ONE, 1]);
  });
  it('[1, "a"]', () => {
    expect(defaultSortKeyOf([1, 'a'])).toEqual([[10, 0, 'list'], [2, [num(1), [[0, 0, 'str'], [1, ['a']], ONE, 1]]], ONE, 1]);
  });
});

describe('_nodes', () => {
  it('counts', () => {
    expect(nodesOf(new Derivative([f(x), x, n]))).toBe(3);
    expect(nodesOf(new Derivative([f(x), x, Rational.of(3n)]))).toBe(5);
    expect(nodesOf(new Float(1.5))).toBe(0.5);
    expect(nodesOf(sj.add(x, new Float(1.5)))).toBe(2.5);
    expect(nodesOf([x, new Map([[y, 1]])])).toBe(5);
    expect(nodesOf(new Map([[1, 2]]))).toBe(3);
  });
});

describe('ordered', () => {
  it('with a key and no default keys', () => {
    expect(orderedValues([[1, 2], [1], [2]], (a) => a.length, false)).toEqual([[1], [2], [1, 2]]);
  });
  it('with a key and the default keys', () => {
    expect(orderedValues([[2], [1, 2], [1]], (a) => a.length)).toEqual([[1], [2], [1, 2]]);
  });
  it('short sequences', () => {
    expect(orderedValues([3])).toEqual([3]);
    expect(orderedValues([] as number[][], (a) => a.length)).toEqual([]);
  });
});

describe('Python comparison and value keys', () => {
  it('compares like Python', () => {
    // True < 2, [1, 2] < [1, 3], [1] < [1, 2]
    expect(compareValues(true, 2)).toBeLessThan(0);
    expect(compareValues([1, 2], [1, 3])).toBeLessThan(0);
    expect(compareValues([1], [1, 2])).toBeLessThan(0);
    expect(compareValues(Rational.of(2n), 3n)).toBeLessThan(0);
    expect(compareValues(true, Rational.of(0n))).toBeGreaterThan(0);
    // '<' not supported between instances of 'int' and 'str'
    expect(() => compareValues(1, 'a')).toThrow(TypeError);
    expect(() => compareValues(null, [1])).toThrow("'<' not supported between null and list");
    expect(() => compareValues(new Map(), 1)).toThrow("'<' not supported between Map and number");
  });
  it('value keys of JavaScript values', () => {
    expect(valueKey(-0)).toBe(valueKey(0));
    expect(valueKey(2n)).toBe(valueKey(2));
    expect(valueKey(Symbol('s'))).toBe('ys');
    expect(valueKey(null)).toBe('N');
    expect(valueKey(undefined)).toBe('u');
    expect(valueEquals(new Map([[1, 'a']]), new Map([[1, 'a']]))).toBe(true);
    expect(valueEquals(new Set([1, 2]), new Set([2, 1]))).toBe(true);
    const o = {};
    expect(valueKey(o)).toBe(valueKey(o));
    expect(valueEquals({}, {})).toBe(false);
    const fn = (): number => 1;
    expect(valueKey(fn)).toBe(valueKey(fn));
  });
  it('ValueMap', () => {
    const m = new ValueMap<unknown, number>([[[1, 2], 1]]);
    expect(m.get([1, 2])).toBe(1);
    expect(m.has([1, 2])).toBe(true);
    m.set([1, 2], 3);
    expect(m.get([1, 2])).toBe(3);
    expect(m.delete([3])).toBe(false);
    expect(m.delete([1, 2])).toBe(true);
    m.set('a', 1);
    m.clear();
    expect(m.size).toBe(0);
    expect(m.get('a')).toBe(undefined);
  });
});
