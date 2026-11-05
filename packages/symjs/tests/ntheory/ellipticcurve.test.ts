// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/ellipticcurve.ts; the docstrings of SymPy 1.14's sympy/ntheory/elliptic_curve.py and
// expected values computed with SymPy 1.14.
import { describe, expect, it } from 'vitest';
import { EllipticCurve, EllipticCurvePoint, NotImplementedError, Rational, S } from '../../src';

const R = (p: number, q = 1) => Rational.of(BigInt(p), BigInt(q));
const pts = (s: Set<{ toString(): string }>) => [...s].map(String).sort();

describe('EllipticCurve', () => {
  it('prints the homogeneous polynomial like SymPy', () => {
    expect(String(new EllipticCurve(1, 1, 1, 1, 1, 5))).toBe('Poly(-x**3 - x**2*z + x*y*z - x*z**2 + y**2*z + y*z**2 - z**3, x, y, z, modulus=5)');
    expect(String(new EllipticCurve(R(1, 2), R(1, 3)))).toBe("Poly(-x**3 - 1/2*x*z**2 + y**2*z - 1/3*z**3, x, y, z, domain='QQ')");
    expect(String(new EllipticCurve(-10, -20, 0, -1, 1).minimal())).toBe("Poly(-x**3 + 13392*x*z**2 + y**2*z + 1080432*z**3, x, y, z, domain='QQ')");
    expect(String(new EllipticCurve(1, 1, 1, 1, 1, 5).minimal())).toBe('Poly(-x**3 + x*z**2 + y**2*z, x, y, z, modulus=5)');
    expect(String(new EllipticCurve(1, 1, 0, 0, 0, 3).minimal())).toBe('Poly(-x**3 - x*z**2 + y**2*z - z**3, x, y, z, modulus=3)');
    const e2 = new EllipticCurve(1, 1, 0, 0, 0, 2);
    expect(e2.minimal()).toBe(e2);
    expect(String(e2)).toBe('Poly(x**3 + x*z**2 + y**2*z + z**3, x, y, z, modulus=2)');
    expect(String(new EllipticCurve(0, 0))).toBe("Poly(-x**3 + y**2*z, x, y, z, domain='QQ')");
  });

  it('computes the invariants', () => {
    expect(new EllipticCurve(0, 17).discriminant).toBe(-124848n);
    expect(new EllipticCurve(-43, 166).discriminant).toBe(-6815744n);
    expect(new EllipticCurve(-43, 166).characteristic).toBe(0n);
    expect(String(new EllipticCurve(-2, 0, 0, 1, 1).jInvariant)).toBe('1404928/389');
    expect(String(new EllipticCurve(R(1, 2), R(1, 3)).jInvariant)).toBe('1728/7');
    expect(new EllipticCurve(R(1, 2), R(1, 3)).discriminant).toBe(-56n);
    const e5 = new EllipticCurve(1, 1, 1, 1, 1, 5);
    expect([e5.discriminant, String(e5.jInvariant), e5.order]).toEqual([4n, '-2', 7]);
    expect(new EllipticCurve(1, 0, 0, 0, 0, 19).order).toBe(19);
    expect(new EllipticCurve(1, 0, 0, 0, 0, 19).rank).toBe(0);
    expect(new EllipticCurve(0, 1).isSingular).toBe(false);
    expect(new EllipticCurve(0, 0).isSingular).toBe(true);
    expect(() => new EllipticCurve(0, 1).order).toThrow(NotImplementedError);
    expect(() => new EllipticCurve(0, 1).rank).toThrow(NotImplementedError);
    expect(() => new EllipticCurve(R(1, 2), 0, 0, 0, 0, 2)).toThrow(RangeError);
    expect(() => new EllipticCurve(0.5, 0)).toThrow(TypeError);
  });

  it('lists points', () => {
    expect(pts(new EllipticCurve(1, 1, 1, 1, 1, 5).points())).toEqual(['(0, 2)', '(1, 4)', '(2, 0)', '(2, 2)', '(3, 0)', '(3, 1)', '(4, 0)']);
    expect(pts(new EllipticCurve(1, 1, 0, 0, 0, 7).points())).toEqual(['(0, 1)', '(0, 6)', '(2, 2)', '(2, 5)']);
    expect(pts(new EllipticCurve(0, 0, 0, 0, 0, 5).points())).toEqual(['(0, 0)', '(1, 1)', '(1, 4)', '(4, 2)', '(4, 3)']);
    expect(() => new EllipticCurve(0, 1).points()).toThrow('Infinitely many points');
    expect(new EllipticCurve(1, 1, 1, 1, 1, 5).pointsX(2).map(String)).toEqual(['(2, 0)', '(2, 2)']);
    // SymPy returns the solutions of its polynomial in y and z here; symjs the rational points
    expect(new EllipticCurve(-17, 16).pointsX(0).map(String)).toEqual(['(0, -4)', '(0, 4)']);
    expect(new EllipticCurve(-1, 0).pointsX(1).map(String)).toEqual(['(1, 0)']);
    expect(new EllipticCurve(-1, 0).pointsX(2).map(String)).toEqual([]);
    expect(new EllipticCurve(0, 1).pointsX(-2).map(String)).toEqual([]);
  });

  it('finds torsion points', () => {
    const sortKey = (p: EllipticCurvePoint) => (p.toString() === 'O' ? -Infinity : Number(p.x.p) / Number(p.x.q) + Number(p.y.p) / Number(p.y.q) / 1e6);
    const sorted = (ps: EllipticCurvePoint[]) => [...ps].sort((a, b) => sortKey(a) - sortKey(b)).map(String);
    expect(sorted(new EllipticCurve(-43, 166).torsionPoints())).toEqual(['O', '(-5, -16)', '(-5, 16)', '(3, -8)', '(3, 8)', '(11, -32)', '(11, 32)']);
    expect(new EllipticCurve(0, 1).torsionPoints().map(String)).toEqual(['O', '(-1, 0)', '(0, 1)', '(0, -1)', '(2, 3)', '(2, -3)']);
    expect(new EllipticCurve(-1, 0).torsionPoints().map(String)).toEqual(['O', '(-1, 0)', '(0, 0)', '(1, 0)']);
    // integral points with y**2 dividing the discriminant but of infinite order
    expect(new EllipticCurve(0, 17).torsionPoints().map(String)).toEqual(['O']);
    expect(() => new EllipticCurve(0, 1, 0, 0, 0, 5).torsionPoints()).toThrow('No torsion point for Finite Field.');
  });

  it('checks membership', () => {
    const e = new EllipticCurve(0, 1);
    expect(e.has([1, 2])).toBe(false);
    expect(e.has([2, 3, 1])).toBe(true);
    expect(e.has([0, 1, 0])).toBe(true);
    expect(e.has(e.call(2, 3))).toBe(true);
    expect(new EllipticCurve(0, 1, 0, 0, 0, 5).has([2, 2])).toBe(true);
    expect(new EllipticCurve(0, 1, 0, 0, 0, 5).has([2, 1])).toBe(false);
    expect(() => e.has([1])).toThrow('Invalid point.');
  });
});

describe('EllipticCurvePoint', () => {
  it('adds and multiplies like the SymPy docstring', () => {
    const e1 = new EllipticCurve(-17, 16);
    expect(String(e1.call(0, -4, 1).add(e1.call(1, 0)))).toBe('(15, -56)');
    const e3 = new EllipticCurve(-1, 9);
    expect(String(e3.call(1, -3).mul(3))).toBe('(664/169, 17811/2197)');
    expect(e3.call(1, -3).mul(3).order()).toBe(S.Infinity);
    const e2 = new EllipticCurve(-2, 0, 0, 1, 1);
    const [p, q] = [e2.call(-1, 1), e2.call(0, -1)];
    expect([p.add(q), p.sub(q), p.mul(3).sub(q.mul(5)), p.neg(), p.mul(0), p.mul(-2)].map(String)).toEqual(['(4, 8)', '(1, 0)', '(328/361, -2800/6859)', '(-1, -2)', 'O', '(10/9, 8/27)']);
    const o = EllipticCurvePoint.pointAtInfinity(e2);
    expect(o.add(p)).toBe(p);
    expect(p.add(o)).toBe(p);
    expect(p.equals(e2.call(-1, 1))).toBe(true);
    expect(p.equals(q)).toBe(false);
    expect([String(p.x), String(p.y), String(p.z)]).toEqual(['-1', '1', '1']);
    expect(() => e1.call(1, 1)).toThrow('The curve does not contain this point');
  });

  it('computes orders', () => {
    const e = new EllipticCurve(-43, 166);
    expect(String(e.call(3, 8).order())).toBe('7');
    expect(String(e.call(3, 8).mul(2))).toBe('(-5, -16)');
    expect(String(e.call(3, 8).mul(-1))).toBe('(3, -8)');
    const c = new EllipticCurve(0, 1);
    expect([c.call(-1, 0), c.call(0, 1), c.call(2, 3), EllipticCurvePoint.pointAtInfinity(c)].map((p) => String(p.order()))).toEqual(['2', '3', '6', '1']);
    expect(String(new EllipticCurve(1, 1, 0, 0, 0, 7).call(0, 1).order())).toBe('5');
    expect(String(new EllipticCurve(2, 3, 0, 0, 0, 97).call(3, 6).order())).toBe('5');
    expect(String(new EllipticCurve(1, 1, 1, 1, 1, 5).call(4, 0).order())).toBe('2');
    expect(String(new EllipticCurve(1, 1, 0, 0, 0, 7).call(0, 6))).toBe('(0, -1)');
    const p31 = new EllipticCurve(1, 1, 1, 1, 1, 5).call(3, 1);
    expect(String(p31.add(p31))).toBe('(0, 2)');
    // SymPy raises NotInvertible on the doubling of a point with 2*y + a1*x + a3 = 0 in __mul__
    expect(() => new EllipticCurve(1, 1, 1, 1, 1, 5).call(3, 1).order()).toThrow('zero divisor');
    // a point of infinite order over Q
    expect(new EllipticCurve(-2, 0, 0, 1, 1).call(-1, 1).order()).toBe(S.Infinity);
  });
});
