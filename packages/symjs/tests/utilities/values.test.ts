// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/utilities/values.ts.
// Value and ordering helpers of the utilities. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Expr, Sym, add, mul, pow } from '../../src';
import * as I from '../../src/utilities';
import { ValueMap } from '../../src/utilities';
import { Derivative, Float, Rational } from '../../src/core/nodes';
import { compareValues, defaultSortKeyOf, nodesOf, orderedValues, valueEquals, valueKey } from '../../src/utilities/values';

// Port of the doctests of sympy.utilities.iterables (SymPy 1.14), plus a
// table of further reference outputs computed with SymPy.

const [, x, y] = ['w', 'x', 'y', 'z'].map((n) => new Sym(n)) as [Sym, Sym, Sym, Sym];
const str = (v: unknown): unknown => (Array.isArray(v) ? v.map(str) : v instanceof Map ? [...v].map(([k, u]) => [str(k), str(u)]) : v instanceof Set ? new Set([...v].map(str)) : v instanceof Expr ? v.toString() : v);

describe('ValueMap', () => {
  it('compares keys by value', () => {
    const m = new ValueMap<unknown, number>([[[1, 2], 1]]);
    m.set([1, 2], 3);
    m.set(add(x, 1), 4);
    expect(m.size).toBe(2);
    expect(m.get([1, 2])).toBe(3);
    expect(m.get(add(1, new Sym('x')))).toBe(4);
    expect(m.delete([1, 2])).toBe(true);
    expect(m.delete([1, 2])).toBe(false);
    m.clear();
    expect(m.has(add(x, 1))).toBe(false);
  });
});

describe('value semantics', () => {
  it('orderedValues follows SymPy ordered', () => {
    const s3 = new Set([3]);
    const d = new Map([[1, 2]]);
    const got = I.orderedValues<unknown>([[2, 1], 'b', 3, x, d, s3, 2.5, 'a']);
    expect(got).toEqual(['a', 'b', 2.5, 3, x, s3, d, [2, 1]]);
    expect(str(I.orderedValues([pow(x, 2), y, x], (e) => -String(e).length))).toEqual(['x**2', 'x', 'y']);
    expect(I.orderedValues([3, 1, 2], [(v) => v % 2], false)).toEqual([2, 3, 1]);
    expect(I.orderedValues([3, 1, 2], [(v) => v % 2])).toEqual([2, 1, 3]);
  });
  it('compareValues and valueEquals', () => {
    expect(I.compareValues(1, 2n)).toBeLessThan(0);
    expect(I.compareValues(true, 0)).toBeGreaterThan(0);
    expect(I.compareValues([1, 2], [1, 3])).toBeLessThan(0);
    expect(I.compareValues([1, 2], [1])).toBeGreaterThan(0);
    expect(I.compareValues(add(x, 0), 2)).toBeGreaterThan(0);
    expect(I.compareValues(1, mul(1, 3))).toBeLessThan(0);
    expect(I.compareValues(x, y)).toBeLessThan(0);
    expect(() => I.compareValues('a', 1)).toThrow(TypeError);
    expect(() => I.compareValues({}, null)).toThrow(TypeError);
    expect(I.valueEquals(new Set([1, 2]), new Set([2, 1]))).toBe(true);
    expect(I.valueEquals(-0, 0)).toBe(true);
    expect(I.valueEquals({}, {})).toBe(false);
    expect(I.valueEquals(undefined, null)).toBe(false);
    expect(I.valueEquals(Symbol.for('a'), Symbol.for('a'))).toBe(true);
    expect(I.valueKey(true)).not.toBe(I.valueKey(false));
    expect(I.defaultSortKeyOf(true)).toEqual(I.defaultSortKeyOf(true));
  });
});


const [n] = sj.symbols('n');
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


describe('values', () => {
  it('compareValues of mixed values (Python <)', () => {
    expect(compareValues(1, true)).toBe(0);
    expect(compareValues('a', 'a')).toBe(0);
    expect(compareValues(sj.sympify(2), sj.sympify(2))).toBe(0);
    expect(compareValues(sj.sympify(1), true)).toBe(0);
    expect(compareValues(sj.sympify(2), false)).toBe(1);
    // JavaScript only: an object without a constructor
    expect(() => compareValues(Object.create(null), 1)).toThrow("'<' not supported between object and number");
  });

  it('defaultSortKeyOf of other iterables and primitives (JavaScript only)', () => {
    const gen = (function* () {
      yield 1;
    })();
    expect(JSON.stringify(defaultSortKeyOf(gen)).startsWith('[[10,0,""]')).toBe(true);
    expect(JSON.stringify(defaultSortKeyOf(null))).toContain('"null"');
  });

  it('ordered with no keys', () => {
    // SymPy ordered([3, 1, 2], []) is [1, 2, 3]; with default=False: ValueError
    expect(orderedValues([3, 1, 2], [])).toEqual([1, 2, 3]);
    expect(() => orderedValues([3, 1, 2], [], false)).toThrow('if default=False then keys must be provided');
    expect(() => orderedValues([3, 1, 2], null, false)).toThrow(RangeError);
  });
});
