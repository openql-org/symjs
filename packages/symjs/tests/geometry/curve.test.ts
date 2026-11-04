// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/curve.ts (SymPy sympy/geometry/curve.py and
// sympy/geometry/tests/test_curve.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational, S, Sym, Tuple, parse, pi, symbols } from '../../src';
import { Circle, Curve, Ellipse, Line, Point, Polygon, Ray, RegularPolygon, Segment } from '../../src/geometry';
import type { GeometryEntity } from '../../src/geometry';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : e instanceof Map ? `{${[...e].map(([k, v]) => `${s(k)}: ${s(v)}`).join(', ')}}` : String(e));
const fs = (e: GeometryEntity): string => [...e.freeSymbols()].map((x) => x.name).sort().join(',');

describe('Curve (SymPy test_curve)', () => {
  const x = new Sym('x', { real: true });
  const [sv, z] = [new Sym('s'), new Sym('z')];

  it('parameters and arbitrary points', () => {
    let c = Curve([sv.mul(2), sv.pow(2)], [z, 0, 2]);
    expect(s(c.parameter)).toBe('z');
    expect(s(c.functions)).toBe('(2*s, s**2)');
    expect(s(c.limits)).toBe('(z, 0, 2)');
    expect(s(c.arbitraryPoint())).toBe('Point2D(2*s, s**2)');
    expect(s(c.arbitraryPoint(z))).toBe('Point2D(2*s, s**2)');
    c = Curve([sv.mul(2), sv.pow(2)], [sv, 0, 2]);
    const t = new Sym('t', { real: true });
    expect(c.arbitraryPoint().key).toBe(Point(t.mul(2), t.pow(2)).key);
    expect(c.arbitraryPoint().key === Point(new Sym('t').mul(2), new Sym('t').pow(2)).key).toBe(false);
    expect(s(c.arbitraryPoint(z))).toBe('Point2D(2*z, z**2)');
    expect(s(c.arbitraryPoint(c.parameter))).toBe('Point2D(2*s, s**2)');
    expect(s(c.arbitraryPoint(null))).toBe('Point2D(2*s, s**2)');
    expect(s(c.arbitraryPoint('s'))).toBe('Point2D(2*s, s**2)');
    expect(s(c.plotInterval())).toBe('[t, 0, 2]');
    expect(s(c.plotInterval(z))).toBe('[z, 0, 2]');
    expect(c.ambientDimension).toBe(2);
    const tt = new Sym('t');
    expect(() => Curve([sv, sv.add(tt)], [sv, 1, 2]).arbitraryPoint()).toThrow('Symbol t already appears in object and cannot be used as a parameter.');
    expect(() => Curve([sv, sv.add(tt)], [tt, 1, 2]).arbitraryPoint(sv)).toThrow(RangeError);
    expect(() => Curve([sv] as never, [sv, 1, 2])).toThrow('Function argument should be (x(t), y(t)) but got');
    expect(() => Curve([x, x.mul(2)], [1, x] as never)).toThrow('Limit argument should be (t, tmin, tmax) but got');
    expect(() => Curve(x as never, [x, 1, 2])).toThrow(RangeError);
    expect(() => Curve([x, x], x as never)).toThrow(RangeError);
    expect(s(Curve(Tuple(x, x), Tuple(x, 0, 1)))).toBe('Curve((x, x), (x, 0, 1))');
    // SymPy C(2) (Curve.__call__)
    const [tq, sq] = symbols('t s') as [Sym, Sym];
    expect(s(Curve([tq, tq.pow(2)], [tq, 0, 10]).at(2))).toBe('Point2D(2, 4)');
    expect(s(Curve([sq.mul(2), sq.pow(2)], [sq, 0, 2]).at(1))).toBe('Point2D(2, 1)');
  });

  it('transformations (SymPy test_transform)', () => {
    const y = new Sym('y', { real: true });
    expect(s(Curve([x, x], [x, 0, 1]).rotate(pi.div(2)))).toBe('Curve((-x, x), (x, 0, 1))');
    expect(s(Curve([x, x], [x, 0, 1]).rotate(pi.div(2), [1, 2]).scale(2, 3).translate(1, 3).arbitraryPoint(sv))).toBe('Point2D(7 - 2*s, 3*s + 6)');
    expect(s(Line([0, 0], [1, 1]).rotate(pi.div(2), [1, 2]).scale(2, 3).translate(1, 3).arbitraryPoint(sv))).toBe('Point2D(7 - 2*s, 3*s + 6)');
    const c = Curve([x, x.pow(2)], [x, 0, 1]);
    const cout = Curve([x.mul(2).sub(4), x.pow(2).mul(3).sub(10)], [x, 0, 1]);
    expect(s(c.scale(2, 3, [4, 5]))).toBe(s(cout));
    expect(s(c.scale(2))).toBe('Curve((2*x, x**2), (x, 0, 1))');
    expect(s([0, 1, 2].map((xi) => c.subs(x, Rational.of(BigInt(xi), 2n))))).toBe('[Point2D(0, 0), Point2D(1/2, 1/4), Point2D(1, 1)]');
    expect(s(Curve([x.add(y), x.mul(3)], [x, 0, 1]).subs(y, S.Half))).toBe('Curve((x + 1/2, 3*x), (x, 0, 1))');
    expect(s(Curve([x, x.mul(3)], [x, 0, 1]).translate(4, 5))).toBe('Curve((x + 4, 3*x + 5), (x, 0, 1))');
    expect(s(Curve([x, x], [x, 0, 1]).translate())).toBe('Curve((x, x), (x, 0, 1))');
    expect(s(Curve([pi.mul(new Sym('t')), pi], [new Sym('t'), 0, pi]).n(2))).toBe('Curve((3.1*t, 3.1), (t, 0, 3.1))');
  });

  it('lengths and parameter values (SymPy test_length, test_parameter_value)', () => {
    const t = new Sym('t', { real: true });
    expect(s(Curve([t, 0], [t, 0, 1]).length)).toBe('1');
    expect(s(Curve([t, t], [t, 0, 1]).length)).toBe('sqrt(2)');
    expect(s(Curve([t.pow(2), t], [t, 2, 5]).length)).toBe('-sqrt(17) - asinh(4)/4 + asinh(10)/4 + 5*sqrt(101)/2');
    const tt = new Sym('t');
    const C = Curve([tt.mul(2), tt.pow(2)], [tt, 0, 2]);
    expect(s(C.parameterValue([2, 1], tt))).toBe('{t: 1}');
    expect(() => C.parameterValue([2, 0], tt)).toThrow(RangeError);
  });

  it('free symbols (SymPy test_free_symbols)', () => {
    const [a, b, c, d, e, f, q] = symbols('a b c d e f s') as Sym[];
    const A = a as Sym;
    const B = b as Sym;
    const Cc = c as Sym;
    const D = d as Sym;
    const Ee = e as Sym;
    const F = f as Sym;
    const Q = q as Sym;
    expect(fs(Point(A, B))).toBe('a,b');
    expect(fs(Line([A, B], [Cc, D]))).toBe('a,b,c,d');
    expect(fs(Ray([A, B], { angle: Cc }))).toBe('a,b,c');
    expect(fs(Segment([A, B], [Cc, D]))).toBe('a,b,c,d');
    expect(fs(Line([A, B], { slope: Cc }))).toBe('a,b,c');
    expect(fs(Curve([A.mul(Q), B.mul(Q)], [Q, Cc, D]))).toBe('a,b,c,d');
    expect(fs(Ellipse([A, B], Cc, D))).toBe('a,b,c,d');
    expect(fs(Circle([A, B], Cc))).toBe('a,b,c');
    expect(fs(Circle([A, B], [Cc, D], [Ee, F]))).toBe('a,b,c,d,e,f');
    expect(fs(Polygon([A, B], [Cc, D], [Ee, F]))).toBe('a,b,c,d,e,f');
    expect(fs(RegularPolygon([A, B], Cc, D, Ee))).toBe('a,b,c,d,e');
    expect(fs(Curve([parse('a*s'), B], [Q, 0, 1]))).toBe('a,b');
  });
});
