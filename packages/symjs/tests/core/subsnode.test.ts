// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/subsnode.ts.
// Subs (SymPy Subs). Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Derivative, Subs, SymFunction, diff, doit, freeSymbols, latex, parse, sstr, symbols } from '../../src';

const [x, y, z] = symbols('x y z');

const f = SymFunction('f');

describe('Subs (SymPy Subs)', () => {
  it('compares evaluated derivatives up to bound-variable renaming', () => {
    const point = parse('2*x + 3');
    expect(diff(f(point), x).equals(Subs(diff(f(y), y), y, point).mul(2))).toBe(true);
    expect(Subs(diff(f(x), x), x, z).equals(Subs(diff(f(y), y), y, z))).toBe(true);
    expect(Subs(f(x, y), [x, y], [1, 2]).equals(Subs(f(y, x), [y, x], [1, 2]))).toBe(true);
    expect(Subs(f(x, y), [x, y], [1, 2]).equals(Subs(f(y, x), [x, y], [1, 2]))).toBe(false);
    expect(Subs(f(x, z), x, y).equals(Subs(f(z, y), z, y))).toBe(false);
    expect(Subs(f(x), y, 0).equals(Subs(f(x), z, 0))).toBe(false);
    expect(Subs(Subs(f(x), x, y), y, z).equals(Subs(Subs(f(y), y, x), x, z))).toBe(true);
    expect(Subs(f(x), x, y).add(Subs(f(z), z, y)).equals(Subs(f(x), x, y).mul(2))).toBe(true);
  });
  it('derivative at a point', () => {
    const s = diff(f(x), x).subs(x, 0 as never);
    expect(s).toBeInstanceOf(Subs);
    expect(sstr(s)).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(latex(s)).toBe('\\left. \\frac{d}{d x} f{\\left(x \\right)} \\right|_{\\substack{ x=0 }}');
    expect(freeSymbols(s).size).toBe(0);
    expect(sstr(diff(s, x))).toBe('0');
    expect(sstr(doit(s))).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(sstr(diff(f(x), x).subs(x, y))).toBe('Derivative(f(y), y)');
    expect(sstr(Derivative(f(x, y), x).subs(x, parse('y + 1')))).toBe('Subs(Derivative(f(x, y), x), x, y + 1)');
  });

  it('several variables, substitution and evaluation', () => {
    const s = Subs(parse('f(x)*sin(y) + z'), [x, y], [0, 1]);
    expect(sstr(s)).toBe('Subs(z + f(x)*sin(y), (x, y), (0, 1))');
    expect(latex(s)).toBe('\\left. z + f{\\left(x \\right)} \\sin{\\left(y \\right)} \\right|_{\\substack{ x=0\\\\ y=1 }}');
    expect([...freeSymbols(s)].map(String)).toEqual(['z']);
    expect(sstr(s.subs(x, 3 as never))).toBe(sstr(s));
    expect(sstr(s.subs(z, 3 as never))).toBe('Subs(f(x)*sin(y) + 3, (x, y), (0, 1))');
    expect(sstr(doit(s))).toBe('z + f(0)*sin(1)');
    expect(sstr(diff(Subs(parse('x**2'), x, parse('y + 1')), y))).toBe('2*y + 2');
    expect(sstr(diff(Subs(f(x), x, y), y))).toBe('Derivative(f(y), y)');
  });
});

it('evaluates substitutions before numerical approximation and preserves a formal derivative', () => {
  expect(Subs(x, x, 3).evalf().toNumber()).toBe(3);
  const formal = Subs(diff(f(x), x), x, 0);
  expect(formal.evalf().key).toBe(formal.key);
  expect(() => Subs(x, [x, x], [1, 2])).toThrow(RangeError);
  expect(() => Subs(x, [x, y], [1])).toThrow(RangeError);
  expect(Subs(x, [], []).key).toBe(x.key);
});
