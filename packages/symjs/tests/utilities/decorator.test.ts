// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/utilities/decorator.ts (SymPy threaded, xthreaded and memoize_property).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import type { Expr, Sym } from '../../src/core/nodes';
import { markPublic, memoizeProperty, threaded, xthreaded } from '../../src/utilities/decorator';

const [x, y] = sj.symbols('x y') as [Sym, Sym];
const square = (e: Expr): Expr => sj.pow(e, 2);

describe('threaded and xthreaded', () => {
  it('the terms of a sum (threaded) or the sum whole (xthreaded)', () => {
    // SymPy: threaded(f)(x + y) is x**2 + y**2; xthreaded(f)(x + y) is (x + y)**2
    expect(String(threaded(square)(sj.add(x, y)))).toBe('x**2 + y**2');
    expect(String(xthreaded(square)(sj.add(x, y)))).toBe('(x + y)**2');
  });
  it('the sides of a relation, the entries of a matrix, the items of an array or a set', () => {
    expect(String(threaded((e: Expr) => sj.expand(e))(sj.Eq(sj.pow(sj.add(x, 1), 2), y)))).toBe('Eq(x**2 + 2*x + 1, y)');
    expect(String(threaded(square)(sj.Matrix.of([[x, y]])))).toBe('Matrix([[x**2, y**2]])');
    expect(threaded(square)([x, 2]).map(String)).toEqual(['x**2', '4']);
    expect([...threaded(square)(new Set([x]))].map(String)).toEqual(['x**2']);
    expect(String(xthreaded(square)(x))).toBe('x**2');
  });
  it('the other arguments are passed on', () => {
    expect(String(threaded((e: Expr, n: number) => sj.pow(e, n))(sj.add(x, y), 3))).toBe('x**3 + y**3');
  });
  it('a sum, relation or matrix needs expressions back; nested containers are not threaded', () => {
    expect(() => threaded(() => 1)(sj.add(x, y))).toThrow(TypeError);
    expect(() => threaded(square)([[x]])).toThrow(TypeError);
  });
});

describe('memoizeProperty', () => {
  it('computes once per object', () => {
    let calls = 0;
    const area = memoizeProperty((s: { side: number }) => {
      calls++;
      return s.side ** 2;
    });
    const a = { side: 3 };
    expect(area(a)).toBe(9);
    expect(area(a)).toBe(9);
    expect(area({ side: 2 })).toBe(4);
    expect(calls).toBe(2);
  });
});

describe('public', () => {
  it('appends the name of a function or a class to the public names and returns it', () => {
    // SymPy: @public def some_function(): pass  makes __all__ == ['some_function']
    const all: string[] = [];
    function someFunction(): number {
      return 1;
    }
    class SomeClass {}
    expect(markPublic(someFunction, all)).toBe(someFunction);
    expect(markPublic(SomeClass, all)).toBe(SomeClass);
    expect(all).toEqual(['someFunction', 'SomeClass']);
    // exported under SymPy's name, a reserved word
    expect(sj.public).toBe(markPublic);
  });
  it('an anonymous function has no name to make public', () => {
    expect(() => markPublic((() => () => 1)(), [])).toThrow(TypeError);
  });
});
