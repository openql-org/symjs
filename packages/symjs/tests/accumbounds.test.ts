// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** AccumBounds (SymPy AccumulationBounds); expected values are SymPy 1.14 output. */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const A = sj.AccumBounds;
const x = new sj.Sym('x');
const s = (e: unknown) => sj.str(e as sj.Expr);
const R = (p: number, q: number) => sj.Rational.of(BigInt(p), BigInt(q));

describe('AccumBounds', () => {
  it('interval arithmetic', () => {
    expect(s(sj.add(A(1, 3), A(2, 5)))).toBe('AccumBounds(3, 8)');
    expect(s(sj.add(A(1, 3), 2))).toBe('AccumBounds(3, 5)');
    expect(s(sj.mul(A(1, 3), -2))).toBe('AccumBounds(-6, -2)');
    expect(s(sj.mul(A(-1, 2), A(-3, 1)))).toBe('AccumBounds(-6, 3)');
    expect(s(sj.pow(A(-1, 2), 2))).toBe('AccumBounds(0, 4)');
    expect(s(sj.pow(A(1, 2), -1))).toBe('AccumBounds(1/2, 1)');
    expect(s(sj.pow(A(-1, 2), -1))).toBe('AccumBounds(-oo, oo)');
    expect(s(sj.pow(A(1, 4), R(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s(sj.sub(A(1, 2), A(1, 2)))).toBe('AccumBounds(-1, 1)');
    expect(s(sj.add(x, A(1, 2)))).toBe('x + AccumBounds(1, 2)');
    expect(s(A(2, 2))).toBe('2');
    expect(() => A(3, 1)).toThrow(RangeError);
    expect(() => A(x, 1)).toThrow(TypeError);
  });
  it('functions and substitution', () => {
    expect(s(sj.sin(A(0, sj.pi)))).toBe('AccumBounds(0, 1)');
    expect(s(sj.cos(A(0, sj.pi)))).toBe('AccumBounds(-1, 1)');
    expect(s(sj.sin(A(sj.mul(sj.pi, R(1, 6)), sj.mul(sj.pi, R(1, 3)))))).toBe('AccumBounds(1/2, sqrt(3)/2)');
    expect(s(sj.sin(A(0, sj.mul(4, sj.pi))))).toBe('AccumBounds(-1, 1)');
    expect(s(sj.exp(A(0, 1)))).toBe('AccumBounds(1, E)');
    expect(s(sj.log(A(1, sj.E)))).toBe('AccumBounds(0, 1)');
    expect(s(sj.tan(A(0, 1)))).toBe('AccumBounds(0, tan(1))');
    expect(s(sj.subs(sj.parse('x**2 + 2*x + 1'), [[x, A(-1, 1)]]))).toBe('AccumBounds(-1, 4)');
    expect(s(sj.subs(sj.parse('(x + 1)**2'), [[x, A(-1, 1)]]))).toBe('AccumBounds(0, 4)');
    expect(sj.latex(A(-1, 1))).toBe('\\left\\langle -1, 1\\right\\rangle');
  });
  it('properties and set operations', () => {
    const a = A(1, 3) as sj.AccumBoundsNode;
    expect([s(a.min), s(a.max), s(a.delta), s(a.mid), a.contains(2), a.contains(4)]).toEqual(['1', '3', '2', '2', true, false]);
    expect(s(a.intersection(A(2, 4)))).toBe('AccumBounds(2, 3)');
    expect(s(a.intersection(A(4, 6)))).toBe('EmptySet');
    expect(s((A(1, 4) as sj.AccumBoundsNode).intersection(sj.finiteSet(1, 2, 5)))).toBe('{1, 2}');
    expect(s(a.union(A(2, 5) as sj.AccumBoundsNode))).toBe('AccumBounds(1, 5)');
    expect(() => a.union(A(4, 5) as sj.AccumBoundsNode)).toThrow(RangeError);
  });
});
