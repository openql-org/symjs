// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/containers.ts. Expected values are SymPy 1.14's str() and latex().

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = [sj.symbol('x'), sj.symbol('y')];
const one = sj.symbol('one');

describe('Tuple and Dict (SymPy sympy.core.containers)', () => {
  it('Tuple', () => {
    const t = sj.Tuple(x, y, 1);
    expect([t, sj.Tuple(x), sj.Tuple(), sj.subs(sj.Tuple(x, y), [[x, 2]])].map(String)).toEqual(['(x, y, 1)', '(x,)', '()', '(2, y)']);
    expect([sj.latex(t), sj.latex(sj.Tuple(x))]).toEqual(['\\left( x, \\  y, \\  1\\right)', '\\left( x,\\right)']);
    expect([t.count(x), t.count(3), t.index(y), t.length]).toEqual([1, 0, 1, 3]);
    expect(() => t.index(3)).toThrow(RangeError);
    expect([t.at(-1), t.at(0), t.concat(sj.Tuple(2)), t.concat([3])].map(String)).toEqual(['1', 'x', '(x, y, 1, 2)', '(x, y, 1, 3)']);
    expect([...t].map(String)).toEqual(['x', 'y', '1']);
    expect(t.toArray().length).toBe(3);
    expect(t instanceof sj.TupleNode).toBe(true);
  });
  it('Dict', () => {
    const d = sj.Dict(new Map<sj.ExprLike, sj.ExprLike>([[1, one], [2, x]]));
    expect(String(d)).toBe('{1: one, 2: x}');
    expect([d.get(1), d.get(3, sj.sympify(5))].map(String)).toEqual(['one', '5']);
    expect(() => d.get(3)).toThrow(RangeError);
    expect([d.containsKey(1), d.containsKey(3), d.size, d.has(one)]).toEqual([true, false, 2, true]);
    expect([d.keys(), d.values()].map((v) => v.map(String))).toEqual([
      ['1', '2'],
      ['one', 'x'],
    ]);
    expect(d.items().map(([k, v]) => `${String(k)}:${String(v)}`)).toEqual(['1:one', '2:x']);
    expect(d.toMap().size).toBe(2);
    expect(sj.latex(d)).toBe('\\left\\{ 1 : one, \\  2 : x\\right\\}');
    expect(String(sj.Dict([[y, 1], [x, 2]]))).toBe('{x: 2, y: 1}');
    expect([sj.subs(d, [[x, 3]]), sj.subs(sj.Dict([[x, 1]]), [[x, 2]])].map(String)).toEqual(['{1: one, 2: 3}', '{2: 1}']);
    // a repeated key keeps the last value (Python dict)
    expect(String(sj.Dict([[x, 1], [x, 2]]))).toBe('{x: 2}');
  });
});
