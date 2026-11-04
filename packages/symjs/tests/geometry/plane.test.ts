// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/geometry/plane.ts (SymPy sympy/geometry/plane.py and
// sympy/geometry/tests/test_plane.py). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Dummy, Expr, Rational, Sym, parse, pi, sqrt, symbols } from '../../src';
import { Circle, Line, Line3D, Plane, Point, Point3D, Ray, Ray3D, Segment, Segment3D, areCoplanar } from '../../src/geometry';
import type { GeometryEntity, PlaneNode } from '../../src/geometry';

const s = (e: unknown): string => (Array.isArray(e) ? `[${e.map(s).join(', ')}]` : e instanceof Map ? `{${[...e].map(([k, v]) => `${s(k)}: ${s(v)}`).join(', ')}}` : String(e));
const R = (p: bigint, q = 1n): Expr => Rational.of(p, q);

describe('Plane (SymPy test_plane)', () => {
  const [x, y, z, u, v] = symbols('x y z u v', { real: true }) as [Sym, Sym, Sym, Sym, Sym];
  const p1 = Point3D(0, 0, 0);
  const p2 = Point3D(1, 1, 1);
  const p3 = Point3D(1, 2, 3);
  const pl3 = Plane(p1, p2, p3);
  const pl4 = Plane(p1, { normalVector: [1, 1, 1] });
  const pl4b = Plane(p1, p2);
  const pl5 = Plane(p3, { normalVector: [1, 2, 3] });
  const pl6 = Plane(Point3D(2, 3, 7), { normalVector: [2, 2, 2] });
  const pl7 = Plane(Point3D(1, -5, -6), { normalVector: [1, -2, 1] });
  const pl8 = Plane(p1, { normalVector: [0, 0, 1] });
  const pl9 = Plane(p1, { normalVector: [0, 12, 0] });
  const pl10 = Plane(p1, { normalVector: [-2, 0, 0] });
  const pl11 = Plane(p2, { normalVector: [0, 0, 1] });
  const l1 = Line3D(Point3D(5, 0, 0), Point3D(1, -1, 1));
  const l2 = Line3D(Point3D(0, -2, 0), Point3D(3, 1, 1));
  const l3 = Line3D(Point3D(0, -1, 0), Point3D(5, -1, 9));

  it('construction and equality', () => {
    expect(() => Plane(p1, p1, p1)).toThrow('Enter three non-collinear points');
    expect(() => Plane([1, 2, 3], { normalVector: [0, 0, 0] })).toThrow('Normal vector cannot be zero vector');
    expect(() => Plane([1, 2, 3], { normalVector: [0, 1] })).toThrow('Either provide 3 3D points');
    expect(() => Plane([1, 2, 3])).toThrow('Either provide 3 3D points');
    expect(() => (Plane as unknown as () => PlaneNode)()).toThrow('Plane requires a point');
    expect(s(Plane(Point3D(1, 1, 1), Point3D(2, 3, 4), Point3D(2, 2, 2)))).toBe('Plane(Point3D(1, 1, 1), (-1, 2, -1))');
    expect(s(Plane([1, 1, 1], [2, 3, 4], [2, 2, 2]))).toBe('Plane(Point3D(1, 1, 1), (-1, 2, -1))');
    expect(s(Plane(Point3D(1, 1, 1), { normalVector: [1, 4, 7] }))).toBe('Plane(Point3D(1, 1, 1), (1, 4, 7))');
    expect(s(Plane(Point3D(1, 1, 1), { normalVector: [0.5, 1, 1] }))).toBe('Plane(Point3D(1, 1, 1), (1/2, 1, 1))');
    expect(s(Plane(Point3D(1, 1, 1), { normalVector: [0.5, 1, 1], evaluate: false }))).toBe('Plane(Point3D(1, 1, 1), (0.5, 1, 1))');
    expect(pl3.key === Plane(p1, p3, p2).key).toBe(false);
    expect(s(pl3)).toBe(s(Plane(Point3D(0, 0, 0), { normalVector: [1, -2, 1] })));
    expect(s(pl4)).toBe(s(pl4b));
    expect(s(pl5.equation(x, y, z))).toBe('x + 2*y + 3*z - 14');
    expect(s(pl3.equation(x, y, z))).toBe('x - 2*y + z');
    expect(s(pl3.equation())).toBe('x - 2*y + z');
    expect(s(pl3.equation('a', 'b', 'c'))).toBe('a - 2*b + c');
    expect(s(pl4.normalVector)).toBe('(1, 1, 1)');
    expect(pl3.ambientDimension).toBe(3);
    expect(s(pl3.subs(z, 1))).toBe(s(pl3));
    expect(s(Plane([0, 0, x], { normalVector: [1, 1, 1] }).subs(x, 1))).toBe('Plane(Point3D(0, 0, 1), (1, 1, 1))');
    expect(s(Plane([0, pi, 0], { normalVector: [0, 0, pi] }).n(2))).toBe('Plane(Point3D(0, 3.1, 0), (0, 0, 3.1))');
    expect(pl8.equals(Plane(p1, { normalVector: [0, 12, 0] }))).toBe(false);
    expect(pl8.equals(pl8)).toBe(true);
    expect(pl8.equals(Plane(p1, { normalVector: [0, 0, -12] }))).toBe(true);
    expect(pl8.equals(Plane(p1, { normalVector: [0, 0, sqrt(3).mul(-12)] }))).toBe(true);
    expect(pl8.equals(p1)).toBe(false);
  });

  it('membership and coplanarity', () => {
    expect(pl3.contains(p1)).toBe(true);
    expect(pl5.contains(p3)).toBe(true);
    expect(pl5.contains([1, 2, 3])).toBe(true);
    expect(pl5.contains(Circle([0, 0], 1))).toBe(false);
    expect(pl5.contains('a')).toBe(false);
    expect(pl5.contains([1, 2, 3, 4])).toBe(false);
    expect(pl8.contains(Line3D([0, 0, 0], [1, 1, 0]))).toBe(true);
    expect(pl3.isCoplanar(Plane(p1, p3, p2))).toBe(true);
    expect(pl3.isCoplanar(pl6)).toBe(false);
    expect(pl3.isCoplanar(p1)).toBe(true);
    expect(pl8.isCoplanar(Line3D([0, 0, 0], [1, 1, 0]))).toBe(true);
    expect(pl3.isCoplanar(Circle(p1, 1))).toBe(false);
    expect(Plane(p1, { normalVector: [0, 0, 1] }).isCoplanar(Circle(p1, 1))).toBe(true);
    expect(areCoplanar(l1, l2, l3)).toBe(false);
    expect(areCoplanar(l1)).toBe(false);
    expect(areCoplanar(Point3D(2, 7, 2), Point3D(0, 0, 2), Point3D(1, 1, 2), Point3D(1, 2, 2))).toBe(true);
    expect(areCoplanar(Plane(p1, p2, p3), Plane(p1, p3, p2))).toBe(true);
  });

  it('projections and perpendiculars', () => {
    expect(s(pl3.projection(Point(0, 0)))).toBe('Point3D(0, 0, 0)');
    const p = pl3.projection(Point3D(1, 1, 0));
    expect(s(p)).toBe('Point3D(7/6, 2/3, 1/6)');
    expect(pl3.contains(p)).toBe(true);
    const l = pl3.projectionLine(Line(Point(0, 0), Point(1, 1)));
    expect(s(l)).toBe('Line3D(Point3D(0, 0, 0), Point3D(7/6, 2/3, 1/6))');
    expect(pl3.contains(l)).toBe(true);
    const t = new Dummy('t');
    const r = pl3.randomPoint();
    expect(pl3.contains(r)).toBe(true);
    const a = pl3.perpendicularLine(r).arbitraryPoint(t);
    const sg = Segment3D(a.subs(t, 1), a.subs(t, 2)) as GeometryEntity;
    expect(pl3.projectionLine(sg).equals(r)).toBe(true);
    expect(s(pl3.projectionLine(Segment(Point(1, 0), Point(1, 1))))).toBe('Segment3D(Point3D(5/6, 1/3, -1/6), Point3D(7/6, 2/3, 1/6))');
    expect(s(pl6.projectionLine(Ray(Point(1, 0), Point(1, 1))))).toBe('Ray3D(Point3D(14/3, 11/3, 11/3), Point3D(13/3, 13/3, 10/3))');
    expect(() => pl6.projectionLine(p1)).toThrow('Enter a linear entity only');
    expect(s(pl3.perpendicularLine(r.args))).toBe(s(pl3.perpendicularLine(r)));
    expect(s(pl3.parallelPlane(Point3D(1, 2, 5)))).toBe(s(Plane(Point3D(1, 2, 5), { normalVector: [1, -2, 1] })));
    expect(s(Plane(Point3D(1, 1, 2), { normalVector: [1, 1, 1] }).projection(Point(1, 1)))).toBe('Point3D(5/3, 5/3, 2/3)');
    expect(s(pl3.randomPoint(1))).toBe(s(pl3.randomPoint(1)));
    expect(pl3.contains(pl3.randomPoint(1))).toBe(true);
  });

  it('parallel, perpendicular and angles', () => {
    expect(pl3.isParallel(pl6)).toBe(false);
    expect(pl4.isParallel(pl6)).toBe(true);
    expect(pl3.isParallel(Line(p1, p2))).toBe(true);
    expect(pl6.isParallel(l1)).toBe(false);
    expect(pl6.isParallel(Circle([0, 0], 1))).toBe(false);
    expect(pl3.isPerpendicular(pl6)).toBe(true);
    expect(pl4.isPerpendicular(pl7)).toBe(true);
    expect(pl6.isPerpendicular(pl4)).toBe(false);
    expect(pl6.isPerpendicular(l1)).toBe(false);
    expect(pl6.isPerpendicular(Line([0, 0, 0], [1, 1, 1]))).toBe(true);
    expect(pl6.isPerpendicular(Point(1, 1))).toBe(false);
    expect(s(pl6.angleBetween(pl3))).toBe('pi/2');
    expect(s(pl6.angleBetween(pl6))).toBe('0');
    expect(s(pl6.angleBetween(pl4))).toBe('0');
    expect(s(pl7.angleBetween(Line3D(Point3D(2, 3, 5), Point3D(2, 4, 6))))).toBe('-asin(sqrt(3)/6)');
    expect(s(pl6.angleBetween(Ray3D(Point3D(2, 4, 1), Point3D(6, 5, 3))))).toBe('asin(sqrt(7)/3)');
    expect(s(pl7.angleBetween(Segment3D(Point3D(5, 6, 1), Point3D(1, 2, 4))))).toBe('asin(7*sqrt(246)/246)');
    expect(() => pl7.angleBetween(p1)).toThrow(TypeError);
  });

  it('arbitrary points and distances', () => {
    const t = new Dummy('t');
    expect(s(pl6.distance(pl6.arbitraryPoint(u, v)))).toBe('0');
    expect(s(pl7.distance(pl7.arbitraryPoint(t)))).toBe('0');
    expect(s(pl6.p1.distance(pl6.arbitraryPoint(t)).simplify())).toBe('1');
    expect(s(pl3.arbitraryPoint(t))).toBe(s(Point3D(parse('-sqrt(30)*sin(t)/30 + 2*sqrt(5)*cos(t)/5').subs(new Sym('t'), t), parse('sqrt(30)*sin(t)/15 + sqrt(5)*cos(t)/5').subs(new Sym('t'), t), parse('sqrt(30)*sin(t)/6').subs(new Sym('t'), t))));
    expect(s(pl3.arbitraryPoint(u, v))).toBe('Point3D(2*u - v, u + 2*v, 5*v)');
    expect(s(pl8.arbitraryPoint())).toBe('Point3D(cos(t), sin(t), 0)');
    expect(s(pl8.arbitraryPoint(undefined, 'w'))).toBe('Point3D(u, w, 0)');
    expect(s(Plane([1, 1, 1], [2, 3, 4], [2, 2, 2], { evaluate: false }))).toBe('Plane(Point3D(1, 1, 1), (-1, 2, -1))');
    expect(s(pl7.distance(Point3D(1, 3, 5)))).toBe('5*sqrt(6)/6');
    expect(s(pl6.distance(Point3D(0, 0, 0)))).toBe('4*sqrt(3)');
    expect(s(pl6.distance([0, 0, 0]))).toBe('4*sqrt(3)');
    expect(s(pl6.distance(pl6.p1))).toBe('0');
    expect(s(pl7.distance(pl6))).toBe('0');
    expect(s(pl7.distance(l1))).toBe('0');
    expect(s(pl6.distance(Segment3D(Point3D(2, 3, 1), Point3D(1, 3, 4))))).toBe('4*sqrt(3)/3');
    expect(s(pl6.distance(Segment3D(Point3D(1, 3, 4), Point3D(0, 3, 7))))).toBe('2*sqrt(3)/3');
    expect(s(pl6.distance(Segment3D(Point3D(0, 3, 7), Point3D(-1, 3, 10))))).toBe('0');
    expect(s(pl6.distance(Segment3D(Point3D(-2, 3, 13), Point3D(-3, 3, 16))))).toBe('2*sqrt(3)/3');
    expect(s(pl6.distance(Plane(Point3D(5, 5, 5), { normalVector: [8, 8, 8] })))).toBe('sqrt(3)');
    expect(s(pl6.distance(Ray3D(Point3D(1, 3, 4), { directionRatio: [1, 0, -3] })))).toBe('4*sqrt(3)/3');
    expect(s(pl6.distance(Ray3D(Point3D(2, 3, 1), { directionRatio: [-1, 0, 3] })))).toBe('0');
    expect(s(pl6.distance(Line3D(Point3D(1, 3, 4), { directionRatio: [1, -1, 0] })))).toBe('4*sqrt(3)/3');
  });

  it('concurrency and perpendicular planes', () => {
    expect(Plane.areConcurrent(pl3, pl4, pl5)).toBe(false);
    expect(Plane.areConcurrent(pl6)).toBe(false);
    expect(Plane.areConcurrent(pl8, pl9, Plane(p1, { normalVector: [0, 1, 1] }))).toBe(true);
    expect(Plane.areConcurrent(pl8, pl9, pl10)).toBe(false);
    expect(Plane.areConcurrent(pl8, pl11)).toBe(false);
    expect(() => Plane.areConcurrent(Point3D(0, 0, 0) as never)).toThrow('All objects should be Planes');
    let p = Plane([0, 0, 0], [1, 0, 0]);
    expect(s(p.perpendicularPlane())).toBe(s(Plane(Point3D(0, 0, 0), [0, 1, 0])));
    expect(s(p.perpendicularPlane(Point3D(1, 0, 1)))).toBe(s(Plane(Point3D(1, 0, 1), [0, 1, 0])));
    expect(s(p.perpendicularPlane([1, 0, 1], [1, 1, 1]))).toBe(s(Plane(Point3D(1, 0, 1), [0, 0, -1])));
    expect(() => p.perpendicularPlane([1, 0, 1], [1, 1, 1], [1, 1, 0])).toThrow('No more than 2 pts should be provided.');
    const [a, b] = [Point3D(0, 0, 0), Point3D(0, 1, 0)];
    const Z = [0, 0, 1];
    p = Plane(a, { normalVector: Z });
    expect(s(p.perpendicularPlane(a, b))).toBe(s(Plane(a, [1, 0, 0])));
    const n = Point3D(...Z);
    expect(s(p.perpendicularPlane(a, n))).toBe(s(Plane(a, [-1, 0, 0])));
    expect(s(Plane(a, { normalVector: b.args }).perpendicularPlane(a, a.add(b)))).toBe(s(Plane(Point3D(0, 0, 0), [1, 0, 0])));
    expect(s(Plane(b, { normalVector: Z }).perpendicularPlane(b, b.add(n)))).toBe(s(Plane(Point3D(0, 1, 0), [-1, 0, 0])));
    expect(s(Plane(b, { normalVector: b.args }).perpendicularPlane(n, n.add(b)))).toBe(s(Plane(Point3D(0, 0, 1), [1, 0, 0])));
    expect(s(Plane(a, { normalVector: [0, 0, 1] }).perpendicularPlane())).toBe(s(Plane(a, { normalVector: [1, 0, 0] })));
    expect(s(Plane(Point(0, 0), { normalVector: Z }).perpendicularPlane(Point(0, 0), Point3D(0, 1)))).toBe(s(Plane(Point3D(0, 0, 0), [1, 0, 0])));
  });

  it('intersections', () => {
    expect(s(pl6.intersection(pl6))).toBe(s([pl6]));
    expect(s(pl4.intersection(pl4.p1))).toBe('[Point3D(0, 0, 0)]');
    expect(s(pl4.intersection([1, 1, 1]))).toBe('[]');
    expect(s(pl3.intersection(pl6))).toBe('[Line3D(Point3D(8, 4, 0), Point3D(2, 4, 6))]');
    expect(s(pl3.intersection(Line3D(Point3D(1, 2, 4), Point3D(4, 4, 2))))).toBe('[Point3D(2, 8/3, 10/3)]');
    expect(s(pl3.intersection(Plane(Point3D(6, 0, 0), { normalVector: [2, -5, 3] })))).toBe('[Line3D(Point3D(-24, -12, 0), Point3D(-25, -13, -1))]');
    expect(s(pl6.intersection(Ray3D(Point3D(2, 3, 1), Point3D(1, 3, 4))))).toBe('[Point3D(-1, 3, 10)]');
    expect(s(pl6.intersection(Segment3D(Point3D(2, 3, 1), Point3D(1, 3, 4))))).toBe('[]');
    expect(s(pl7.intersection(Line(Point(2, 3), Point(4, 2))))).toBe('[Point3D(13/2, 3/4, 0)]');
    expect(s(Plane([1, 2, 0], { normalVector: [0, 0, 1] }).intersection(Ray(Point(2, 3), Point(4, 2))))).toBe('[Ray3D(Point3D(2, 3, 0), Point3D(4, 2, 0))]');
    expect(s(pl9.intersection(pl8))).toBe('[Line3D(Point3D(0, 0, 0), Point3D(12, 0, 0))]');
    expect(s(pl10.intersection(pl11))).toBe('[Line3D(Point3D(0, 0, 1), Point3D(0, 2, 1))]');
    expect(s(pl4.intersection(pl8))).toBe('[Line3D(Point3D(0, 0, 0), Point3D(1, -1, 0))]');
    expect(s(pl11.intersection(pl8))).toBe('[]');
    expect(s(pl9.intersection(pl11))).toBe('[Line3D(Point3D(0, 0, 1), Point3D(12, 0, 1))]');
    expect(s(pl9.intersection(pl4))).toBe('[Line3D(Point3D(0, 0, 0), Point3D(12, 0, -12))]');
    const q8 = Plane([1, 2, 0], { normalVector: [0, 0, 1] });
    expect(q8.intersection(Line3D(p1, [1, 12, 0]))[0]?.equals(Line([0, 0, 0], [0.1, 1.2, 0]))).toBe(true);
    expect(q8.intersection(Segment3D(p1, [21, 1, 0]))[0]?.equals(Segment3D(p1, [21, 1, 0]))).toBe(true);
    expect(q8.intersection(Plane(p1, { normalVector: [0, 12, 0] }))[0]?.equals(Line3D(p1, { directionRatio: [pi.mul(112), 0, 0] }))).toBe(true);
    expect(q8.intersection(Plane(p1, { normalVector: [-1, -1, -11] }))[0]?.equals(Line3D(p1, { directionRatio: [1, -1, 0] }))).toBe(true);
    expect(q8.intersection(Ray3D(Point3D(0, 2, 3), Point3D(1, 0, 3))).length).toBe(0);
    expect(s(Plane([1, 2, 1], [2, 1, 0], [3, 1, 2]).intersection([2, 1]))).toBe('[Point3D(2, 1, 0)]');
    expect(() => pl3.intersection(Circle([0, 0], 1))).toThrow(TypeError);
    // SymPy issue 8570
    const ll = Line3D(
      Point3D(R(50000004459633n, 5000000000000n), R(-891926590718643n, 1000000000000000n), R(231800966893633n, 100000000000000n)),
      Point3D(R(50000004459633n, 50000000000000n), R(-222981647679771n, 250000000000000n), R(231800966893633n, 100000000000000n)),
    );
    const pp = Plane(Point3D(R(402775636372767n, 100000000000000n), R(-97224357654973n, 100000000000000n), R(216793600814789n, 100000000000000n)), [
      parse('-9.00000087501922'),
      parse('-4.81170658872543e-13'),
      parse('0.0'),
    ]);
    expect(s(pp.intersection(ll).map((i) => i.n(2)))).toBe('[Point3D(4.0, -0.89, 2.3)]');
  });

  it('parameter values (SymPy test_parameter_value)', () => {
    const [t, uu, vv] = symbols('t u v') as [Sym, Sym, Sym];
    const p = Plane(Point(0, 0, 0), Point(0, 0, 1), Point(0, 1, 0));
    expect(s(p.parameterValue([0, -3, 2], t))).toBe('{t: asin(2*sqrt(13)/13)}');
    expect(s(p.parameterValue([0, -3, 2], uu, vv))).toBe('{u: 3, v: 2}');
    expect(s(p.parameterValue(Point(0, 0, 0), t))).toBe('Point3D(0, 0, 0)');
    expect(() => p.parameterValue([1, 0, 0], t)).toThrow('Given point is not on Plane');
    expect(() => p.parameterValue(Line(Point(0, 0), Point(1, 1)), t)).toThrow('other must be a point');
    expect(() => p.parameterValue([0, -3, 2], t, 1)).toThrow('expecting 1 or 2 symbols');
    const on = Point3D(1, parse('1 + sqrt(2)/2'), parse('1 + sqrt(2)/2'));
    const q = Plane([1, 1, 1], { normalVector: [1, 0, 0] });
    expect(s(q.parameterValue(on, t))).toBe('{t: pi/4}');
  });
});
