// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/point.ts (SymPy sympy/vector/point.py and the Point
// cases of sympy/vector/tests/test_coordsysrect.py). Expected values are
// those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, latex, mul, str } from '../../src';
import { CoordSys3D, Vector, VectorPoint } from '../../src/vector';
import { treePath } from '../../src/vector/point';

const N = CoordSys3D('N');

describe('Point of sympy.vector', () => {
  it('locates points', () => {
    const p1 = N.origin.locateNew('p1', mul(10, N.i));
    expect(str(N.origin.positionWrt(p1))).toBe('(-10)*N.i');
    expect(str(p1.positionWrt(N.origin))).toBe('10*N.i');
    const p2 = p1.locateNew('p2', mul(5, N.j));
    expect(p2.expressCoordinates(N).map(str)).toEqual(['10', '5', '0']);
    expect(str(p2)).toBe('p2');
    expect(latex(p2)).toBe('p2');
    expect(p2.parent).toBe(p1);
    expect(p2.root).toBe(N.origin);
    expect(p2.position.key).toBe(mul(5, N.j).key);
    expect(str(p2.positionWrt(N.origin.locateNew('q', N.k)))).toBe('10*N.i + 5*N.j + (-1)*N.k');
    expect(p2.withArgs(p2.args).key).toBe(p2.key);
    expect(VectorPoint('r').positionWrt(VectorPoint('r'))).toBe(Vector.zero);
    expect(str(VectorPoint('s', add(N.i, N.j)).withArgs([N.k]))).toBe('s');
    expect(N.origin.withArgs(N.origin.args).key).toBe(N.origin.key);
  });

  it('checks its arguments', () => {
    expect(() => VectorPoint('p', N.x)).toThrow('position should be an instance of Vector');
    expect(() => VectorPoint('p', N.i, N.i as never)).toThrow('parent_point should be an instance of Point');
    expect(() => N.origin.positionWrt(N.i as never)).toThrow('is not a Point or CoordSys3D');
    expect(() => VectorPoint('p').positionWrt(VectorPoint('q'))).toThrow('No connecting path found between p and q');
  });

  it('finds paths in trees', () => {
    const A = CoordSys3D('A');
    const B = A.locateNew('B', A.i);
    const C = B.locateNew('C', A.j);
    const D = A.locateNew('D', A.k);
    const parent = (s: InstanceType<typeof CoordSys3D>) => s.parentSystem;
    const root = (s: InstanceType<typeof CoordSys3D>) => s.rootSystem;
    const [i, path] = treePath(C, D, parent, root);
    expect(i).toBe(2);
    expect(path.map(str)).toEqual(['C', 'B', 'A', 'D']);
  });
});
