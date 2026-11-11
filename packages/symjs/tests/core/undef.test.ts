// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/undef.ts.
// Undefined functions. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y');

describe('small core nodes', () => {
  it('creates undefined functions and Subs', () => {
    // SymPy: symbols('f g', cls=Function) = (f, g)
    expect(sj.functions('f g').map((f) => String(f(x)))).toEqual(['f(x)', 'g(x)']);
    expect(() => sj.SymFunction('1f')).toThrow(SyntaxError);
    // SymPy: Subs(x, [], []) = x; mismatched lengths raise ValueError
    expect(String(sj.Subs(x, [], []))).toBe('x');
    expect(() => sj.Subs(x, [x, y], [1])).toThrow(RangeError);
  });
});

it('validates and enforces declared function arities', () => {
  const f = sj.SymFunction('f',{nargs:1}), g = sj.SymFunction('g',{nargs:[2,1,2]});
  expect(String(f(x!))).toBe('f(x)');
  expect(g.arity).toEqual([1,2]);
  expect(String(g(x!,y!))).toBe('g(x, y)');
  expect(() => f()).toThrow(TypeError);
  expect(() => f(x!,y!)).toThrow(TypeError);
  expect(() => sj.SymFunction('f',{nargs:-1})).toThrow(RangeError);
  expect(() => sj.SymFunction('f',{nargs:0.5})).toThrow(RangeError);
  expect(String(sj.SymFunction('z',{nargs:0})())).toBe('z()');
});
