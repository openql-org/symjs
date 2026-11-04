// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/orienters.ts (SymPy sympy/vector/orienters.py and
// test_orienters of sympy/vector/tests/test_coordsysrect.py). Expected
// values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, mul, str, symbol } from '../../src';
import { AxisOrienter, BodyOrienter, CoordSys3D, QuaternionOrienter, SpaceOrienter } from '../../src/vector';

const [a, b, c] = [symbol('a'), symbol('b'), symbol('c')];
const [q1, q2, q3, q4] = [symbol('q1'), symbol('q2'), symbol('q3'), symbol('q4')];

describe('orienters (SymPy test_orienters)', () => {
  const A = CoordSys3D('A');

  it('rotation matrices', () => {
    expect(AxisOrienter(a, A.k).rotationMatrix(A).toString()).toBe('Matrix([[cos(a), sin(a), 0], [-sin(a), cos(a), 0], [0, 0, 1]])');
    expect(BodyOrienter(a, b, c, '123').rotationMatrix().toString()).toBe(
      'Matrix([[cos(b)*cos(c), sin(a)*sin(b)*cos(c) + sin(c)*cos(a), sin(a)*sin(c) - sin(b)*cos(a)*cos(c)], [-sin(c)*cos(b), -sin(a)*sin(b)*sin(c) + cos(a)*cos(c), sin(a)*cos(c) + sin(b)*sin(c)*cos(a)], [sin(b), -sin(a)*cos(b), cos(a)*cos(b)]])',
    );
    expect(SpaceOrienter(a, b, c, '123').rotationMatrix().toString()).toBe(
      'Matrix([[cos(b)*cos(c), sin(c)*cos(b), -sin(b)], [sin(a)*sin(b)*cos(c) - sin(c)*cos(a), sin(a)*sin(b)*sin(c) + cos(a)*cos(c), sin(a)*cos(b)], [sin(a)*sin(c) + sin(b)*cos(a)*cos(c), -sin(a)*cos(c) + sin(b)*sin(c)*cos(a), cos(a)*cos(b)]])',
    );
    expect(QuaternionOrienter(q1, q2, q3, q4).rotationMatrix().toString()).toBe(
      'Matrix([[q1**2 + q2**2 - q3**2 - q4**2, 2*q1*q4 + 2*q2*q3, -2*q1*q3 + 2*q2*q4], [-2*q1*q4 + 2*q2*q3, q1**2 - q2**2 + q3**2 - q4**2, 2*q1*q2 + 2*q3*q4], [2*q1*q3 + 2*q2*q4, -2*q1*q2 + 2*q3*q4, q1**2 - q2**2 - q3**2 + q4**2]])',
    );
    expect(BodyOrienter(0, 0, a, 'ZXZ').rotationMatrix().toString()).toBe('Matrix([[cos(a), sin(a), 0], [-sin(a), cos(a), 0], [0, 0, 1]])');
  });

  it('attributes, printing and arguments', () => {
    const ax = AxisOrienter(q1, add(A.i, mul(2, A.j)));
    expect(str(ax)).toBe('AxisOrienter(q1, A.i + 2*A.j)');
    expect(ax.angle).toBe(q1);
    expect(str(ax.axis)).toBe('A.i + 2*A.j');
    expect(ax.withArgs(ax.args).key).toBe(ax.key);
    const bo = BodyOrienter(1, 2, 3, 'XYZ');
    expect(str(bo)).toBe('BodyOrienter(1, 2, 3, 123)');
    expect(bo.rotOrder).toBe('XYZ');
    expect([bo.angle1, bo.angle2, bo.angle3].map(str)).toEqual(['1', '2', '3']);
    expect(bo.withArgs(bo.args).key).toBe(bo.key);
    expect(BodyOrienter(1, 2, 3, '123').key).not.toBe(BodyOrienter(1, 2, 3, '121').key);
    const so = SpaceOrienter(q1, q2, q3, '312');
    expect(so.withArgs(so.args).key).toBe(so.key);
    const qo = QuaternionOrienter(1, 2, 3, 4);
    expect(str(qo)).toBe('QuaternionOrienter(1, 2, 3, 4)');
    expect([qo.q0, qo.q1, qo.q2, qo.q3].map(str)).toEqual(['1', '2', '3', '4']);
    expect(qo.withArgs(qo.args).key).toBe(qo.key);
    expect(() => AxisOrienter(q1, A.x)).toThrow('axis should be a Vector');
    expect(() => ax.rotationMatrix()).toThrow('needs the coordinate system');
    expect(() => BodyOrienter(1, 2, 3, '12')).toThrow('rot_order should be a str of length 3');
    expect(() => BodyOrienter(1, 2, 3, '112')).toThrow('Invalid rot_type parameter');
  });
});
