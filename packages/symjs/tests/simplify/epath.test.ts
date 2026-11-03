// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/epath.ts (SymPy sympy/simplify/epathtools.py).

// Expected values are the str() forms printed by SymPy 1.14 (sympy/simplify/tests/test_epathtools.py
// and epath runs of SymPy) unless a comment says otherwise. Python tuples and lists are arrays, and
// Python ints are JavaScript numbers.

import { describe, expect, it } from 'vitest';
import { E, EPath, Eq, Expr, NotImplementedError, O, add, cos, epath, exp, mul, parse, pow, sin, str, symbols } from '../../src';

const [x, y, z, t] = symbols('x y z t');

/** Python str() of a value: tuples print with parentheses (one-element tuples do not occur here). */
const py = (v: unknown, list = true): string => {
  if (v instanceof Expr) return str(v);
  if (Array.isArray(v)) return list ? `[${v.map((u) => py(u, false)).join(', ')}]` : `(${v.map((u) => py(u, false)).join(', ')})`;
  return String(v);
};

describe('epath (test_epathtools.py)', () => {
  const expr = [[[x, 1, t], 2], [[3, y, 4], z]];

  it('select', () => {
    const cases: [string, string][] = [
      ['/*', '[((x, 1, t), 2), ((3, y, 4), z)]'],
      ['/*/*', '[(x, 1, t), 2, (3, y, 4), z]'],
      ['/*/*/*', '[x, 1, t, 3, y, 4]'],
      ['/*/*/*/*', '[]'],
      ['/[:]', '[((x, 1, t), 2), ((3, y, 4), z)]'],
      ['/[:]/[:]', '[(x, 1, t), 2, (3, y, 4), z]'],
      ['/[:]/[:]/[:]', '[x, 1, t, 3, y, 4]'],
      ['/[:]/[:]/[:]/[:]', '[]'],
      ['/*/[:]', '[(x, 1, t), 2, (3, y, 4), z]'],
      ['/*/[0]', '[(x, 1, t), (3, y, 4)]'],
      ['/*/[1]', '[2, z]'],
      ['/*/[2]', '[]'],
      ['/*/int', '[2]'],
      ['/*/Symbol', '[z]'],
      ['/*/tuple', '[(x, 1, t), (3, y, 4)]'],
      ['/*/__iter__?', '[(x, 1, t), (3, y, 4)]'],
      ['/*/int|tuple', '[(x, 1, t), 2, (3, y, 4)]'],
      ['/*/Symbol|tuple', '[(x, 1, t), (3, y, 4), z]'],
      ['/*/int|Symbol|tuple', '[(x, 1, t), 2, (3, y, 4), z]'],
      ['/*/int|__iter__?', '[(x, 1, t), 2, (3, y, 4)]'],
      ['/*/Symbol|__iter__?', '[(x, 1, t), (3, y, 4), z]'],
      ['/*/int|Symbol|__iter__?', '[(x, 1, t), 2, (3, y, 4), z]'],
      ['/*/[0]/int', '[1, 3, 4]'],
      ['/*/[0]/Symbol', '[x, t, y]'],
      ['/*/[0]/int[1:]', '[1, 4]'],
      ['/*/[0]/Symbol[1:]', '[t, y]'],
    ];
    for (const [path, expected] of cases) expect(py(epath(path, expr)), path).toBe(expected);
    expect(py(epath('/Symbol', parse('x + y + z + 1')))).toBe('[x, y, z]');
    expect(py(epath('/*/*/Symbol', add(t, sin(add(x, 1)), cos(add(x, y, E)))))).toBe('[x, x, y]');
  });

  it('apply', () => {
    const func = (e: Expr | number): unknown => (typeof e === 'number' ? e ** 2 : pow(e, 2));
    const list = (e: unknown[]): unknown[] => [...e];
    // list() turns a tuple into a list
    expect(epath('/*', expr, list)).toEqual(expr);
    expect(py(epath('/*/[1]', expr, func))).toBe('[((x, 1, t), 4), ((3, y, 4), z**2)]');
    expect(epath('/*/[2]', expr, list)).toEqual(expr);
    expect(py(epath('/*/[0]/int', expr, func))).toBe('[((x, 1, t), 2), ((9, y, 16), z)]');
    expect(py(epath('/*/[0]/Symbol', expr, func))).toBe('[((x**2, 1, t**2), 2), ((3, y**2, 4), z)]');
    expect(py(epath('/*/[0]/int[1:]', expr, func))).toBe('[((x, 1, t), 2), ((3, y, 16), z)]');
    expect(py(epath('/*/[0]/Symbol[1:]', expr, func))).toBe('[((x, 1, t**2), 2), ((3, y**2, 4), z)]');
    expect(py(epath('/Symbol', parse('x + y + z + 1'), func))).toBe('x**2 + y**2 + z**2 + 1');
    expect(py(epath('/*/*/Symbol', add(t, sin(add(x, 1)), cos(add(x, y, E))), func))).toBe('t + sin(x**2 + 1) + cos(x**2 + y**2 + E)');
    // the doctests
    expect(py(epath('/*/[0]/Symbol', [[[x, 1], 2], [[3, y], z]], func))).toBe('[((x**2, 1), 2), ((3, y**2), z)]');
    expect(py(epath('/*/*/Symbol', add(t, sin(add(x, 1)), cos(add(x, y, E))), (e: Expr) => mul(2, e)))).toBe('t + sin(2*x + 1) + cos(2*x + 2*y + E)');
  });

  it('EPath', () => {
    expect(new EPath('/*/[0]').path).toBe('/*/[0]');
    expect(new EPath(new EPath('/*/[0]')).path).toBe('/*/[0]');
    expect(epath('/*/[0]')).toBeInstanceOf(EPath);
    expect(String(new EPath('/*/[0]'))).toBe("EPath('/*/[0]')");
    for (const p of ['', '/', '/|x', '/[', '/[0]%']) expect(() => new EPath(p), p).toThrow(RangeError);
    expect(() => new EPath('Symbol')).toThrow(NotImplementedError);
    // a compiled path is reused
    const path = new EPath('/*/[0]/Symbol');
    expect(py(path.select([[[x, 1], 2], [[3, y], z]]))).toBe('[x, y]');
    expect(py(epath(path, [[[x, 1], 2], [[3, y], z]]))).toBe('[x, y]');
  });
});

describe('epath: more SymPy results', () => {
  const e = parse('2*x*sin(y)*exp(z)*y**3');
  const inc = (u: Expr): Expr => add(u, 1);

  it('indices, slices, types and attributes on a product', () => {
    const cases: [string, string, string][] = [
      ['/*', '[2, x, y**3, exp(z), sin(y)]', '3*(x + 1)*(y**3 + 1)*(exp(z) + 1)*(sin(y) + 1)'],
      ['/[0]', '[2]', '3*x*y**3*exp(z)*sin(y)'],
      ['/[-1]', '[sin(y)]', '2*x*y**3*(sin(y) + 1)*exp(z)'],
      ['/[::-1]', '[sin(y), exp(z), y**3, x, 2]', '3*(x + 1)*(y**3 + 1)*(exp(z) + 1)*(sin(y) + 1)'],
      ['/[1::2]', '[x, exp(z)]', '2*y**3*(x + 1)*(exp(z) + 1)*sin(y)'],
      ['/[-2:]', '[exp(z), sin(y)]', '2*x*y**3*(exp(z) + 1)*(sin(y) + 1)'],
      ['/[5]', '[]', '2*x*y**3*exp(z)*sin(y)'],
      ['/Pow', '[y**3]', '2*x*(y**3 + 1)*exp(z)*sin(y)'],
      ['/exp', '[exp(z)]', '2*x*y**3*(exp(z) + 1)*sin(y)'],
      ['/exp/*', '[z]', '2*x*y**3*exp(z + 1)*sin(y)'],
      ['/Function', '[exp(z), sin(y)]', '2*x*y**3*(exp(z) + 1)*(sin(y) + 1)'],
      ['/Number', '[2]', '3*x*y**3*exp(z)*sin(y)'],
      ['/Integer', '[2]', '3*x*y**3*exp(z)*sin(y)'],
      ['/Atom', '[2, x]', '3*y**3*(x + 1)*exp(z)*sin(y)'],
      ['/is_Symbol?', '[2, x, y**3, exp(z), sin(y)]', '3*(x + 1)*(y**3 + 1)*(exp(z) + 1)*(sin(y) + 1)'],
      ['/Pow/[1]', '[3]', '2*x*y**4*exp(z)*sin(y)'],
      ['/sin|Symbol', '[x, sin(y)]', '2*y**3*(x + 1)*(sin(y) + 1)*exp(z)'],
      ['/*/Symbol', '[y, z, y]', '2*x*(y + 1)**3*exp(z + 1)*sin(y + 1)'],
      ['/[:-1:2]', '[2, y**3]', '3*x*(y**3 + 1)*exp(z)*sin(y)'],
      ['/[10:]', '[]', '2*x*y**3*exp(z)*sin(y)'],
      ['/[-10]', '[]', '2*x*y**3*exp(z)*sin(y)'],
    ];
    for (const [path, sel, app] of cases) {
      expect(py(epath(path, e)), path).toBe(sel);
      expect(py(epath(path, e, inc)), path).toBe(app);
    }
  });

  it('other nodes and values', () => {
    expect(py(epath('/*', exp(add(x, 1)), (u: Expr) => mul(u, 2)))).toBe('exp(2*x + 2)');
    expect(py(epath('/*/*', [[x, 1], 3], (u: Expr | number) => (typeof u === 'number' ? u * 2 : mul(u, 2))))).toBe('[(2*x, 2), 3]');
    expect(py(epath('/*', Eq(x, y), inc))).toBe('Eq(x + 1, y + 1)');
    expect(py(epath('/[0]', parse('x + y + z')))).toBe('[x]');
    expect(py(epath('/[0]', parse('x*y*z')))).toBe('[x]');
    expect(py(epath('/[0]', parse('1 - x**2')))).toBe('[1]');
    expect(py(epath('/*', parse('x - 1')))).toBe('[x, -1]');
    expect(py(epath('/Order', add(x, O(pow(x, 2)))))).toBe('[O(x**2)]');
    expect(py(epath('/[ 1 ]', [1, 2, 3]))).toBe('[2]');
    expect(py(epath('/ * ', [1, 2]))).toBe('[1, 2]');
    expect(epath('/str', ['a', 1])).toEqual(['a']);
    expect(epath('/float', [1.5, 1])).toEqual([1.5]);
    expect(epath('/int', [2n, true])).toEqual([2n]);
    expect(epath('/bool', [2n, true])).toEqual([true]);
    expect(epath('/*', 5)).toEqual([]);
    expect(epath('/*', 5, (u: number) => u)).toBe(5);
    // an atom is kept
    expect(epath('/*', x, inc)).toBe(x);
    // extra arguments of func
    expect(py(epath('/Symbol', parse('x + y'), (u: Expr, k: number) => mul(u, k), [3]))).toBe('3*x + 3*y');
    // camelCase attributes and the JavaScript class names of other objects also select
    expect(py(epath('/Sym', parse('x + 2')))).toBe('[]');
    expect(py(epath('/is_commutative?', parse('x + 2')))).toBe('[x, 2]');
    expect(epath('/Map', [new Map(), 1])).toEqual([new Map()]);
    expect(epath('/my_attr?', [{ myAttr: 1 }, 2])).toEqual([{ myAttr: 1 }]);
    // an object without a constructor has no class name
    expect(epath('/Object', [Object.create(Object.create(null) as object) as object])).toEqual([]);
    expect(py(epath('/name?', [x, 1, 'a']))).toBe('[x]');
    expect(py(epath('/__iter__?', ['ab', 1]))).toBe('[ab]');
    // a bigint result becomes an Integer (x is replaced by 5)
    expect(py(epath('/[0]', parse('x + 2'), () => 5n))).toBe('7');
    expect(py(epath('/[1]', parse('x + 2'), () => 5))).toBe('x + 5');
  });

  it('errors', () => {
    expect(() => new EPath('/[1:2:3:4]')).toThrow(TypeError);
    expect(() => new EPath('/[a]')).toThrow(RangeError);
    expect(() => epath('/[::0]', [1, 2])).toThrow(RangeError);
    expect(() => epath('/[0]', parse('x + 2'), () => [1])).toThrow(TypeError);
  });
});
