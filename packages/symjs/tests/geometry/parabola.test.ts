// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/parabola.ts (SymPy sympy/geometry/parabola.py and
// sympy/geometry/tests/test_parabola.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { S, Sym, sqrt, symbols } from '../../src';
import { Circle, Ellipse, Line, Parabola, Point, Point2D, Ray2D, Segment2D } from '../../src/geometry';
import type { LinearEntity } from '../../src/geometry';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : String(e));

describe('Parabola (SymPy test_parabola_geom)', () => {
  const [a, b] = symbols('a b') as [Sym, Sym];
  const [p1, p2, p3, p4, p5] = [Point(0, 0), Point(3, 7), Point(0, 4), Point(6, 0), Point(a, a)];
  const d1 = Line(Point(4, 0), Point(4, 9));
  const d2 = Line(Point(7, 6), Point(3, 6));
  const d3 = Line(Point(4, 0), { slope: S.Infinity });
  const d4 = Line(Point(7, 6), { slope: 0 });
  const d5 = Line(Point(b, a), { slope: S.Infinity });
  const d6 = Line(Point(a, b), { slope: 0 });
  const half = S.Half;

  it('properties', () => {
    const pa1 = Parabola(undefined, d2);
    const pa2 = Parabola(undefined, d1);
    const pa3 = Parabola(p1, d1);
    const pa4 = Parabola(p2, d2);
    const pa5 = Parabola(p2, d4);
    const pa6 = Parabola(p3, d2);
    const pa7 = Parabola(p2, d1);
    const pa8 = Parabola(p4, d1);
    const pa9 = Parabola(p4, d3);
    const pa10 = Parabola(p5, d5);
    const pa11 = Parabola(p5, d6);
    const d = Line(Point(3, 7), Point(2, 9));
    const pa12 = Parabola(Point(7, 8), d);
    const pa12r = Parabola(Point(7, 8).reflect(d as never) as never, d);
    expect(() => Parabola(Point(7, 8, 9), Line(Point(6, 7), Point(7, 7)))).toThrow(RangeError);
    expect(() => Parabola(Point(0, 2), Line(Point(7, 2), Point(6, 2)))).toThrow('The focus must not be a point of directrix');
    expect(() => Parabola(Point(7, 8), Point(3, 8) as unknown as LinearEntity)).toThrow(TypeError);
    expect(s(pa1.focus)).toBe('Point2D(0, 0)');
    expect(pa1.ambientDimension).toBe(2);
    expect(s(pa2)).toBe(s(pa3));
    expect(pa4.key === pa7.key).toBe(false);
    expect(s(pa6.focus)).toBe('Point2D(0, 4)');
    expect([pa6.focalLength, pa6.pParameter, pa6.vertex, pa6.eccentricity].map(s)).toEqual(['1', '-1', 'Point2D(0, 5)', '1']);
    expect([pa7.focalLength, pa7.pParameter, pa7.vertex].map(s)).toEqual(['1/2', '-1/2', 'Point2D(7/2, 7)']);
    expect([pa4.focalLength, pa4.pParameter, pa4.vertex].map(s)).toEqual(['1/2', '1/2', 'Point2D(3, 13/2)']);
    expect([pa8.focalLength, pa8.pParameter, pa8.vertex].map(s)).toEqual(['1', '1', 'Point2D(5, 0)']);
    expect(s(pa4.equation())).toBe(s(pa5.equation()));
    expect(s(pa8.equation())).toBe(s(pa9.equation()));
    expect(s(pa8.equation())).toBe('4*x - y**2 - 20');
    expect(s(pa10.focalLength)).toBe('sqrt((a - b)**2)/2');
    expect(s(pa11.focalLength)).toBe('sqrt((a - b)**2)/2');
    expect(s(pa11.vertex)).toBe('Point2D(a, a - sqrt((a - b)**2)*sign(a - b)/2)');
    expect(s(pa10.vertex)).toBe('Point2D(a - sqrt((a - b)**2)*sign(a - b)/2, a)');
    expect(s(pa12.axisOfSymmetry)).toBe(s(Line(Point(7, 8), Point(5, 7))));
    expect(s(pa12.directrix)).toBe(s(Line(Point(3, 7), Point(2, 9))));
    expect(s(pa12.directrix.angleBetween(pa12.axisOfSymmetry))).toBe('pi/2');
    const [x, y] = [new Sym('x'), new Sym('y')];
    expect(s(pa12.equation(x, y))).toBe('(x - 7)**2 + (y - 8)**2 - (-2*x - y + 13)**2/5');
    expect(s(pa12.equation('f'))).toBe('(f - 7)**2 + (y - 8)**2 - (-2*f - y + 13)**2/5');
    expect([pa12.focalLength, pa12.pParameter, pa12.vertex].map(s)).toEqual(['9*sqrt(5)/10', '9*sqrt(5)/10', 'Point2D(26/5, 71/10)']);
    expect([pa12r.focalLength, pa12r.focus, pa12r.pParameter, pa12r.vertex].map(s)).toEqual(['9*sqrt(5)/10', 'Point2D(-1/5, 22/5)', '-9*sqrt(5)/10', 'Point2D(8/5, 53/10)']);
    expect(s(pa3.subs(S.Zero, 1))).toBe('Parabola(Point2D(1, 1), Line2D(Point2D(4, 1), Point2D(4, 9)))');
    expect(s(Parabola([0, 0], Line([-1, -2], [1, -2])).equation('x', 'z'))).toBe('-x**2 + 4*z + 4');
  });

  it('intersections (SymPy test_parabola_intersection)', () => {
    const l1 = Line(Point(1, -2), Point(-1, -2));
    const l2 = Line(Point(1, 2), Point(-1, 2));
    const l3 = Line(Point(1, 0), Point(-1, 0));
    const pa = Parabola(Point(0, 0), l1);
    expect(s(pa.intersection(pa))).toBe(s([pa]));
    expect(s(pa.intersection(Parabola(Point(0, 0), l2)))).toBe('[Point2D(-2, 0), Point2D(2, 0)]');
    expect(s(pa.intersection(Parabola(Point(0, -2), l3)))).toBe('[Point2D(0, -1)]');
    expect(s(pa.intersection(Parabola(Point(16, 0), l1)))).toBe('[Point2D(8, 15)]');
    expect(s(pa.intersection(Parabola(Point(0, 16), l1)))).toBe('[Point2D(-6, 8), Point2D(6, 8)]');
    expect(s(pa.intersection(Parabola(Point(120, -12), l3)))).toBe('[]');
    expect(s(pa.intersection(Point(0, 0)))).toBe('[]');
    expect(s(pa.intersection(Point2D(0, -1)))).toBe('[Point2D(0, -1)]');
    expect(s(pa.intersection(Point2D(4, 3)))).toBe('[Point2D(4, 3)]');
    expect(s(pa.intersection(Line(Point2D(-7, 3), Point(12, 3))))).toBe('[Point2D(-4, 3), Point2D(4, 3)]');
    expect(s(pa.intersection(Line(Point(-4, -1), Point(4, -1))))).toBe('[Point2D(0, -1)]');
    expect(s(pa.intersection(Line(Point(2, 0), Point(0, -2))))).toBe('[Point2D(2, 0)]');
    expect(() => pa.intersection(Line(Point(0, 0, 0), Point(1, 1, 1)))).toThrow('Entity must be two dimensional, not three dimensional');
    expect(s(pa.intersection(Segment2D([-4, -5], [4, 3])))).toBe('[Point2D(0, -1), Point2D(4, 3)]');
    expect(s(pa.intersection(Segment2D([0, -5], [0, 6])))).toBe('[Point2D(0, -1)]');
    expect(s(pa.intersection(Segment2D([-12, -65], [14, -68])))).toBe('[]');
    expect(s(pa.intersection(Ray2D([-4, -5], [4, 3])))).toBe('[Point2D(0, -1), Point2D(4, 3)]');
    expect(s(pa.intersection(Ray2D([0, 7], [1, 14])))).toBe(s([Point2D(sqrt(57).mul(2).add(14), sqrt(57).mul(14).add(105))]));
    expect(s(pa.intersection(Ray2D([0, 7], [0, 14])))).toBe('[]');
    expect(s(pa.intersection(Circle(Point(0, 0), 2)))).toBe('[Point2D(-2, 0), Point2D(2, 0)]');
    expect(s(pa.intersection(Circle(Point(0, -2), 1)))).toBe('[Point2D(0, -1)]');
    expect(s(pa.intersection(Ellipse(Point(0, -2), 2, 1)))).toBe('[Point2D(0, -1)]');
    expect(s(pa.intersection(Ellipse(Point(0, 19), 5, 7)))).toBe('[]');
    expect(s(pa.intersection(Ellipse([0, 3], 12, 4)))).toBe('[Point2D(0, -1), Point2D(-4*sqrt(17)/3, 59/9), Point2D(4*sqrt(17)/3, 59/9)]');
    expect(() => pa.intersection(2)).toThrow('Wrong type of argument were put');
    // the vertex of a parabola with a slanted directrix (SymPy Parabola.vertex)
    expect(s(Parabola(Point(0, 0), Line(Point(0, -2), Point(2, 0))).vertex)).toBe('Point2D(1/2, -1/2)');
    expect(s(Parabola(Point(0, 0), Line(Point(-2, 0), Point(0, 2))).pParameter)).toBe('sqrt(2)/2');
    expect(half.key).toBe(S.Half.key);
  });
});
