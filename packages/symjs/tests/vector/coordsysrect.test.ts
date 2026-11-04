// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/coordsysrect.ts (SymPy sympy/vector/coordsysrect.py and
// sympy/vector/tests/test_coordsysrect.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Lambda, Matrix, S, Tuple, acos, add, atan2, cos, cosh, expand, latex, mul, pi, pow, simplify, sin, sinh, sqrt, str, symbol } from '../../src';
import type { Expr, Sym } from '../../src';
import { AxisOrienter, BaseScalar, BodyOrienter, CoordSys3D, QuaternionOrienter, SpaceOrienter, Vector, VectorPoint, express } from '../../src/vector';
import { checkOrthogonality, rotationTransEquations } from '../../src/vector/coordsysrect';

const [x, y, z] = [symbol('x'), symbol('y'), symbol('z')];
const [a, b, c, q] = [symbol('a'), symbol('b'), symbol('c'), symbol('q')];
const [q1, q2, q3, q4] = [symbol('q1'), symbol('q2'), symbol('q3'), symbol('q4')];
const eq = (u: Expr, v: Expr): boolean => u.key === v.key;
const map = (m: Map<Expr, Expr>): string[] => [...m].map(([k, v]) => `${str(k)}: ${str(v)}`);
const tuple = (xs: readonly Expr[]): string => `(${xs.map(str).join(', ')})`;

describe('CoordSys3D (SymPy test_coordsysrect)', () => {
  it('rebuilds from its arguments', () => {
    const A = CoordSys3D('A');
    const v = add(mul(A.x, A.i), mul(A.y, A.j), mul(A.z, A.k));
    expect(eq((v as Vector).withArgs(v.args), v)).toBe(true);
    expect(eq(A.origin.withArgs(A.origin.args), A.origin)).toBe(true);
    expect(eq(A.withArgs(A.args), A)).toBe(true);
    const B = A.orientNewAxis('B', q, A.k, add(A.i, A.j));
    expect(eq(B.withArgs(B.args), B)).toBe(true);
    const S1 = A.createNew('S', 'spherical');
    expect(eq(S1.withArgs(S1.args), S1)).toBe(true);
    const L = CoordSys3D('L', (u: Expr, w: Expr, t: Expr) => [u, w, t]);
    expect(eq(L.withArgs(L.args), L)).toBe(true);
  });

  it('equivalence', () => {
    expect(eq(CoordSys3D('A'), CoordSys3D('A'))).toBe(true);
    expect(eq(CoordSys3D('A'), CoordSys3D('B'))).toBe(false);
    expect(str(CoordSys3D('A'))).toBe('A');
    expect(latex(CoordSys3D('A'))).toBe('A');
  });

  it('coordinate variables', () => {
    const A = CoordSys3D('A');
    expect(eq(BaseScalar(0, A, 'A_x', '\\mathbf{{x}_{A}}'), A.x)).toBe(true);
    expect(eq(BaseScalar(1, A), A.y)).toBe(true);
    expect(A.x).toBeInstanceOf(BaseScalar);
    expect(eq(mul(A.x, A.y), mul(A.y, A.x))).toBe(true);
    expect(map(A.scalarMap(A))).toEqual(['A.x: A.x', 'A.y: A.y', 'A.z: A.z']);
    expect(A.x.system).toBe(A);
    expect(A.x.diff(A.x)).toBe(S.One);
    const B = A.orientNewAxis('B', q, A.k);
    expect(map(B.scalarMap(A))).toEqual(['B.x: A.x*cos(q) + A.y*sin(q)', 'B.y: -A.x*sin(q) + A.y*cos(q)', 'B.z: A.z']);
    expect(map(A.scalarMap(B))).toEqual(['A.x: B.x*cos(q) - B.y*sin(q)', 'A.y: B.x*sin(q) + B.y*cos(q)', 'A.z: B.z']);
    expect(str(express(B.x, A, undefined, { variables: true }))).toBe('A.x*cos(q) + A.y*sin(q)');
    expect(str(express(B.z, A, undefined, { variables: true }))).toBe('A.z');
    expect(eq(expand(express(mul(B.x, B.y, B.z), A, undefined, { variables: true })), expand(mul(A.z, add(mul(-1, A.x, sin(q)), mul(A.y, cos(q))), add(mul(A.x, cos(q)), mul(A.y, sin(q))))))).toBe(true);
    expect(str(express(add(mul(B.x, B.i), mul(B.y, B.j), mul(B.z, B.k)), A))).toBe('(B.x*cos(q) - B.y*sin(q))*A.i + (B.x*sin(q) + B.y*cos(q))*A.j + B.z*A.k');
    expect(str(simplify(express(add(mul(B.x, B.i), mul(B.y, B.j), mul(B.z, B.k)), A, undefined, { variables: true })))).toBe('A.x*A.i + A.y*A.j + A.z*A.k');
    expect(str(express(add(mul(A.x, A.i), mul(A.y, A.j), mul(A.z, A.k)), B))).toBe('(A.x*cos(q) + A.y*sin(q))*B.i + (-A.x*sin(q) + A.y*cos(q))*B.j + A.z*B.k');
    const N = B.orientNewAxis('N', mul(-1, q), B.k);
    expect(map(N.scalarMap(A))).toEqual(['N.x: A.x', 'N.y: A.y', 'N.z: A.z']);
    const D = A.locateNew('D', add(mul(a, A.i), mul(b, A.j), mul(c, A.k)));
    expect(map(D.scalarMap(A))).toEqual(['D.x: A.x - a', 'D.y: A.y - b', 'D.z: A.z - c']);
    const E = A.orientNewAxis('E', a, A.k, add(mul(a, A.i), mul(b, A.j), mul(c, A.k)));
    expect(map(A.scalarMap(E))).toEqual(['A.x: E.x*cos(a) - E.y*sin(a) + a', 'A.y: E.x*sin(a) + E.y*cos(a) + b', 'A.z: E.z + c']);
    expect(map(E.scalarMap(A))).toEqual(['E.x: (A.x - a)*cos(a) + (A.y - b)*sin(a)', 'E.y: (-A.x + a)*sin(a) + (A.y - b)*cos(a)', 'E.z: A.z - c']);
    const F = A.locateNew('F', Vector.zero);
    expect(map(A.scalarMap(F))).toEqual(['A.x: F.x', 'A.y: F.y', 'A.z: F.z']);
  });

  it('rotation matrix', () => {
    const N = CoordSys3D('N');
    const A = N.orientNewAxis('A', q1, N.k);
    const B = A.orientNewAxis('B', q2, A.i);
    const C = B.orientNewAxis('C', q3, B.j);
    const D = N.orientNewAxis('D', q4, N.j);
    const E = N.orientNewSpace('E', q1, q2, q3, '123');
    const F = N.orientNewQuaternion('F', q1, q2, q3, q4);
    const G = N.orientNewBody('G', q1, q2, q3, '123');
    expect(N.rotationMatrix(C).toString()).toBe(
      'Matrix([[-sin(q1)*sin(q2)*sin(q3) + cos(q1)*cos(q3), -sin(q1)*cos(q2), sin(q1)*sin(q2)*cos(q3) + sin(q3)*cos(q1)], [sin(q1)*cos(q3) + sin(q2)*sin(q3)*cos(q1), cos(q1)*cos(q2), sin(q1)*sin(q3) - sin(q2)*cos(q1)*cos(q3)], [-sin(q3)*cos(q2), sin(q2), cos(q2)*cos(q3)]])',
    );
    const m = D.rotationMatrix(C);
    const expected = Matrix.of([
      [add(mul(cos(q1), cos(q3), cos(q4)), mul(-1, sin(q3), add(mul(-1, sin(q4), cos(q2)), mul(sin(q1), sin(q2), cos(q4))))), add(mul(-1, sin(q2), sin(q4)), mul(-1, sin(q1), cos(q2), cos(q4))), add(mul(sin(q3), cos(q1), cos(q4)), mul(cos(q3), add(mul(-1, sin(q4), cos(q2)), mul(sin(q1), sin(q2), cos(q4)))))],
      [add(mul(sin(q1), cos(q3)), mul(sin(q2), sin(q3), cos(q1))), mul(cos(q1), cos(q2)), add(mul(sin(q1), sin(q3)), mul(-1, sin(q2), cos(q1), cos(q3)))],
      [add(mul(sin(q4), cos(q1), cos(q3)), mul(-1, sin(q3), add(mul(cos(q2), cos(q4)), mul(sin(q1), sin(q2), sin(q4))))), add(mul(sin(q2), cos(q4)), mul(-1, sin(q1), sin(q4), cos(q2))), add(mul(sin(q3), sin(q4), cos(q1)), mul(cos(q3), add(mul(cos(q2), cos(q4)), mul(sin(q1), sin(q2), sin(q4)))))],
    ]);
    m.sub(expected).data.forEach((e) => expect(str(expand(e))).toBe('0'));
    expect(E.rotationMatrix(N).toString()).toBe(
      'Matrix([[cos(q2)*cos(q3), sin(q3)*cos(q2), -sin(q2)], [sin(q1)*sin(q2)*cos(q3) - sin(q3)*cos(q1), sin(q1)*sin(q2)*sin(q3) + cos(q1)*cos(q3), sin(q1)*cos(q2)], [sin(q1)*sin(q3) + sin(q2)*cos(q1)*cos(q3), -sin(q1)*cos(q3) + sin(q2)*sin(q3)*cos(q1), cos(q1)*cos(q2)]])',
    );
    expect(F.rotationMatrix(N).toString()).toBe(
      'Matrix([[q1**2 + q2**2 - q3**2 - q4**2, 2*q1*q4 + 2*q2*q3, -2*q1*q3 + 2*q2*q4], [-2*q1*q4 + 2*q2*q3, q1**2 - q2**2 + q3**2 - q4**2, 2*q1*q2 + 2*q3*q4], [2*q1*q3 + 2*q2*q4, -2*q1*q2 + 2*q3*q4, q1**2 - q2**2 - q3**2 + q4**2]])',
    );
    expect(G.rotationMatrix(N).toString()).toBe(
      'Matrix([[cos(q2)*cos(q3), sin(q1)*sin(q2)*cos(q3) + sin(q3)*cos(q1), sin(q1)*sin(q3) - sin(q2)*cos(q1)*cos(q3)], [-sin(q3)*cos(q2), -sin(q1)*sin(q2)*sin(q3) + cos(q1)*cos(q3), sin(q1)*cos(q3) + sin(q2)*sin(q3)*cos(q1)], [sin(q2), -sin(q1)*cos(q2), cos(q1)*cos(q2)]])',
    );
    expect(N.rotationMatrix(A).toString()).toBe('Matrix([[cos(q1), -sin(q1), 0], [sin(q1), cos(q1), 0], [0, 0, 1]])');
    expect(A.rotationMatrix(N).toString()).toBe('Matrix([[cos(q1), sin(q1), 0], [-sin(q1), cos(q1), 0], [0, 0, 1]])');
    expect(() => N.rotationMatrix(CoordSys3D('X'))).toThrow('No connecting path found between N and X');
    expect(() => N.rotationMatrix(Vector.zero as never)).toThrow('is not a CoordSys3D');
  });

  it('vectors in oriented systems', () => {
    const N = CoordSys3D('N');
    const A = N.orientNewAxis('A', q1, N.k);
    const B = A.orientNewAxis('B', q2, A.i);
    const C = B.orientNewAxis('C', q3, B.j);
    const v1 = add(mul(a, N.i), mul(b, N.j), mul(c, N.k)) as Vector;
    expect(v1.toMatrix(A).toString()).toBe('Matrix([[a*cos(q1) + b*sin(q1)], [-a*sin(q1) + b*cos(q1)], [c]])');
    expect(str(N.i.dot(A.j))).toBe('-sin(q1)');
    expect(str(N.i.dot(A.k))).toBe('0');
    expect(str(N.i.dot(add(A.i, A.j)))).toBe('-sin(q1) + cos(q1)');
    expect(str((add(A.i, A.j) as Vector).dot(N.i))).toBe('-sin(q1) + cos(q1)');
    expect(str(A.j.dot(C.i))).toBe('sin(q2)*sin(q3)');
    expect(str(A.k.dot(C.i))).toBe('-sin(q3)*cos(q2)');
    expect(str(N.i.cross(A.i))).toBe('(sin(q1))*A.k');
    expect(str(N.i.cross(A.k))).toBe('(-sin(q1))*A.i + (-cos(q1))*A.j');
    expect(str(N.j.cross(A.k))).toBe('(cos(q1))*A.i + (-sin(q1))*A.j');
    expect(N.k.cross(A.i)).toBe(A.j);
    expect(N.k.cross(A.k)).toBe(Vector.zero);
    expect(str(N.i.cross(add(A.i, A.j)))).toBe('(sin(q1) + cos(q1))*A.k');
    expect(str((add(A.i, A.j) as Vector).cross(N.i))).toBe('(-sin(q1) - cos(q1))*N.k');
    expect(str(A.i.cross(C.j))).toBe('(-sin(q3))*C.i + (cos(q3))*C.k');
    expect(str(C.i.cross(A.i))).toBe('(-sin(q3)*cos(q2))*A.j + (-sin(q2)*sin(q3))*A.k');
    expect(str((express(C.k.cross(A.i), C) as Vector).trigsimp())).toBe('(cos(q3))*C.j');
  });

  it('orient_new with orienters', () => {
    const N = CoordSys3D('N');
    const D = N.orientNew('D', [AxisOrienter(q4, N.j)]);
    const E = N.orientNew('E', [SpaceOrienter(q1, q2, q3, '123')]);
    const F = N.orientNew('F', [QuaternionOrienter(q1, q2, q3, q4)]);
    const G = N.orientNew('G', [BodyOrienter(q1, q2, q3, '123')]);
    expect(eq(D, N.orientNewAxis('D', q4, N.j))).toBe(true);
    expect(eq(E, N.orientNewSpace('E', q1, q2, q3, '123'))).toBe(true);
    expect(eq(F, N.orientNewQuaternion('F', q1, q2, q3, q4))).toBe(true);
    expect(eq(G, N.orientNewBody('G', q1, q2, q3, '123'))).toBe(true);
    const H = N.orientNew('H', BodyOrienter(q1, 0, 0, 'XYZ'), undefined, { vectorNames: ['u', 'v', 'w'], variableNames: ['r', 's', 't'] });
    expect(str(H.attr('u'))).toBe('H.u');
    expect(str(H.attr('t'))).toBe('H.t');
  });

  it('locate_new and points', () => {
    const A = CoordSys3D('A');
    expect(A.origin).toBeInstanceOf(VectorPoint);
    const v = add(mul(a, A.i), mul(b, A.j), mul(c, A.k));
    const C = A.locateNew('C', v);
    for (const p of [C.origin.positionWrt(A), C.positionWrt(A), C.origin.positionWrt(A.origin)]) expect(eq(p, v)).toBe(true);
    for (const p of [A.origin.positionWrt(C), A.positionWrt(C), A.origin.positionWrt(C.origin)]) expect(eq(p, mul(-1, v))).toBe(true);
    expect(tuple(A.origin.expressCoordinates(C))).toBe('(-a, -b, -c)');
    const p = A.origin.locateNew('p', mul(-1, v));
    expect(tuple(p.expressCoordinates(A))).toBe('(-a, -b, -c)');
    expect(eq(p.positionWrt(C.origin), mul(-2, v))).toBe(true);
    expect(eq(p.positionWrt(C), mul(-2, v))).toBe(true);
    const p1 = p.locateNew('p1', mul(2, v));
    expect(p1.positionWrt(C.origin)).toBe(Vector.zero);
    expect(tuple(p1.expressCoordinates(C))).toBe('(0, 0, 0)');
    const p2 = p.locateNew('p2', A.i);
    expect(eq(p1.positionWrt(p2), mul(2, v).sub(A.i))).toBe(true);
    expect(tuple(p2.expressCoordinates(C))).toBe('(1 - 2*a, -2*b, -2*c)');
    expect(() => C.positionWrt(S.One)).toThrow('is not a Point or CoordSys3D');
  });

  it('create_new and transformations', () => {
    const A = CoordSys3D('a');
    const C = A.createNew('c', 'spherical');
    expect(C.parentSystem).toBe(A);
    expect(tuple(C.transformationToParent())).toBe('(c.r*sin(c.theta)*cos(c.phi), c.r*sin(c.phi)*sin(c.theta), c.r*cos(c.theta))');
    expect(tuple(C.transformationFromParent())).toBe('(sqrt(a.x**2 + a.y**2 + a.z**2), acos(a.z/sqrt(a.x**2 + a.y**2 + a.z**2)), atan2(a.y, a.x))');
    expect(() => A.transformationFromParent()).toThrow('no parent coordinate system');
    expect(() => C.createNew('d', 'spherical')).toThrow('Parent for pre-defined coordinate system should be Cartesian.');
    expect(C.rootSystem).toBe(A);
    expect(C.transformation).toBe('spherical');
  });

  it('evalf', () => {
    const A = CoordSys3D('A');
    const v = add(mul(3, A.i), mul(4, A.j), mul(a, A.k));
    expect(eq(v.n(), v.evalf())).toBe(true);
    expect(eq(v.evalf(15, { subs: { a: 1 } }), v.subs(a, 1).evalf())).toBe(true);
  });

  it('lame coefficients', () => {
    const s = CoordSys3D('a', 'spherical');
    expect(tuple(s.lameCoefficients())).toBe('(1, a.r, a.r*sin(a.theta))');
    expect(tuple(CoordSys3D('a').lameCoefficients())).toBe('(1, 1, 1)');
    expect(tuple(CoordSys3D('a', 'cartesian').lameCoefficients())).toBe('(1, 1, 1)');
    expect(tuple(CoordSys3D('a', 'cylindrical').lameCoefficients())).toBe('(1, a.r, 1)');
    expect(() => CoordSys3D('a', 'polar')).toThrow('Wrong set of parameters');
  });

  it('transformation equations', () => {
    let A = CoordSys3D('a', { transformation: 'spherical', variableNames: ['r', 'theta', 'phi'] });
    const [r, theta] = A.baseScalars();
    expect(A.attr('r')).toBe(r);
    expect(A.attr('theta')).toBe(theta);
    expect(() => A.x).toThrow(TypeError);
    expect(() => A.attr('w')).toThrow("'CoordSys3D' object has no attribute 'w'");
    expect(tuple(A.transformationToParent())).toBe('(a.r*sin(a.theta)*cos(a.phi), a.r*sin(a.phi)*sin(a.theta), a.r*cos(a.theta))');
    expect(tuple(A.lameCoefficients())).toBe('(1, a.r, a.r*sin(a.theta))');
    expect(tuple(A.transformationFromParentFunction()(x, y, z))).toBe(tuple([sqrt(add(pow(x, 2), pow(y, 2), pow(z, 2))), acos(mul(z, pow(sqrt(add(pow(x, 2), pow(y, 2), pow(z, 2))), -1))), atan2(y, x)]));
    A = CoordSys3D('a', { transformation: 'cylindrical', variableNames: ['r', 'theta', 'z'] });
    expect(tuple(A.transformationToParent())).toBe('(a.r*cos(a.theta), a.r*sin(a.theta), a.z)');
    expect(tuple(A.transformationFromParentFunction()(x, y, z))).toBe('(sqrt(x**2 + y**2), atan2(y, x), z)');
    A = CoordSys3D('a', 'cartesian');
    expect(tuple(A.transformationToParent())).toBe('(a.x, a.y, a.z)');
    expect(tuple(A.transformationFromParentFunction()(x, y, z))).toBe('(x, y, z)');
    // Cartesian with an equation tuple
    A = CoordSys3D('a', [
      [x, y, z],
      [x, y, z],
    ]);
    expect(tuple(A.transformationToParent())).toBe('(a.x1, a.x2, a.x3)');
    expect(tuple(A.lameCoefficients())).toBe('(1, 1, 1)');
    expect(tuple(A.transformationFromParentFunction()(x, y, z))).toBe('(x, y, z)');
    const [R, T, Z] = [symbol('r'), symbol('theta'), symbol('z')];
    A = CoordSys3D('a', [Tuple(R, T, Z), Tuple(mul(R, cos(T)), mul(R, sin(T)), Z)], { variableNames: ['r', 'theta', 'z'] });
    expect(tuple(A.transformationToParent())).toBe('(a.r*cos(a.theta), a.r*sin(a.theta), a.z)');
    expect(tuple(A.lameCoefficients())).toBe('(sqrt(sin(a.theta)**2 + cos(a.theta)**2), sqrt(a.r**2*sin(a.theta)**2 + a.r**2*cos(a.theta)**2), 1)');
    // definitions with a function
    A = CoordSys3D('a', (u: Expr, v: Expr, w: Expr) => [u, v, w]);
    expect(tuple(A.transformationToParent())).toBe('(a.x1, a.x2, a.x3)');
    expect(tuple(A.lameCoefficients())).toBe('(1, 1, 1)');
    expect(tuple(A.transformationFromParentFunction()(x, y, z))).toBe('(x, y, z)');
    A = CoordSys3D('a', (u: Expr, v: Expr, w: Expr) => [mul(u, sin(v), cos(w)), mul(u, sin(v), sin(w)), mul(u, cos(v))], { variableNames: ['r', 'theta', 'phi'] });
    expect(tuple(A.transformationToParent())).toBe('(a.r*sin(a.theta)*cos(a.phi), a.r*sin(a.phi)*sin(a.theta), a.r*cos(a.theta))');
    expect(tuple(A.lameCoefficients())).toBe(
      '(sqrt(sin(a.phi)**2*sin(a.theta)**2 + sin(a.theta)**2*cos(a.phi)**2 + cos(a.theta)**2), sqrt(a.r**2*sin(a.phi)**2*cos(a.theta)**2 + a.r**2*sin(a.theta)**2 + a.r**2*cos(a.phi)**2*cos(a.theta)**2), sqrt(a.r**2*sin(a.phi)**2*sin(a.theta)**2 + a.r**2*sin(a.theta)**2*cos(a.phi)**2))',
    );
    const lam = Lambda([R, T, Z], Tuple(mul(R, cos(T)), mul(R, sin(T)), Z));
    A = CoordSys3D('a', lam, { variableNames: ['r', 'theta', 'z'] });
    expect(tuple(A.transformationToParent())).toBe('(a.r*cos(a.theta), a.r*sin(a.theta), a.z)');
    expect(() => CoordSys3D('a', { transformation: new Map() as never })).toThrow('transformation: wrong type');
    expect(() => CoordSys3D('a', { transformation: 'spherical', location: CoordSys3D('b').i })).toThrow('specify either');
  });

  it('orthogonality of the transformation', () => {
    const [u, v] = [symbol('u'), symbol('v')];
    const lam = (vars: Sym[], eqs: Expr[]) => Lambda(vars, Tuple(...eqs));
    expect(checkOrthogonality(lam([x, y, z], [mul(x, sin(y), cos(z)), mul(x, sin(y), sin(z)), mul(x, cos(y))]))).toBe(true);
    expect(checkOrthogonality(lam([x, y, z], [mul(x, cos(y)), mul(x, sin(y)), z]))).toBe(true);
    expect(checkOrthogonality(lam([u, v, z], [mul(cosh(u), cos(v)), mul(sinh(u), sin(v)), z]))).toBe(true);
    expect(() => CoordSys3D('a', [
      [x, y, z],
      [x, x, z],
    ])).toThrow('The transformation equation does not create orthogonal coordinate system');
    expect(() => CoordSys3D('a', [
      [x, y, z],
      [mul(x, sin(mul(y, S.Half)), cos(z)), mul(x, sin(y), sin(z)), mul(x, cos(y))],
    ])).toThrow('orthogonal');
    expect(checkOrthogonality(lam([x, y, z], [add(x, y), mul(-1, y), z]))).toBe(false);
  });

  it('rotation transformation equations', () => {
    const A = CoordSys3D('a');
    const q0 = symbol('q0');
    expect(tuple(rotationTransEquations(A.parentRotationMatrix, A.baseScalars()))).toBe('(a.x, a.y, a.z)');
    expect(tuple(rotationTransEquations(A.inverseRotationMatrix(), A.baseScalars()))).toBe('(a.x, a.y, a.z)');
    const B = A.orientNewAxis('b', 0, mul(-1, A.k));
    expect(tuple(rotationTransEquations(B.parentRotationMatrix, B.baseScalars()))).toBe('(b.x, b.y, b.z)');
    const C = A.orientNewAxis('c', q0, mul(-1, A.k));
    expect(tuple(rotationTransEquations(C.parentRotationMatrix, C.baseScalars()))).toBe('(c.x*cos(q0) - c.y*sin(q0), c.x*sin(q0) + c.y*cos(q0), c.z)');
    expect(tuple(rotationTransEquations(C.inverseRotationMatrix(), C.baseScalars()))).toBe('(c.x*cos(q0) + c.y*sin(q0), -c.x*sin(q0) + c.y*cos(q0), c.z)');
  });

  it('custom names (SymPy test_printing)', () => {
    const A = CoordSys3D('A', { vectorNames: ['x', 'y', 'z'], variableNames: ['i', 'j', 'k'] });
    expect(str(A.attr('i'))).toBe('A.i');
    expect(str(A.attr('x'))).toBe('A.x');
    expect((A.attr('i') as InstanceType<typeof BaseScalar>).prettyForm).toBe('i_A');
    expect((A.attr('x') as InstanceType<typeof Vector>).toLatex()).toBe('\\mathbf{\\hat{x}_{A}}');
    expect((A.attr('i') as InstanceType<typeof BaseScalar>).latexForm).toBe('\\mathbf{{i}_{A}}');
    expect(() => A.i).toThrow('i of A is a base scalar');
    expect(() => CoordSys3D('A', { vectorNames: ['x', 'y'] })).toThrow('vector_names must be an iterable of 3 string-types');
    expect(() => CoordSys3D('A', { variableNames: ['x', 'y', 3 as never] })).toThrow(TypeError);
    expect([...A].map(str)).toEqual(['A.x', 'A.y', 'A.z']);
  });

  it('checks the arguments', () => {
    const A = CoordSys3D('A');
    expect(() => CoordSys3D('B', { parent: A, location: S.One })).toThrow('location should be a Vector');
    expect(() => CoordSys3D('B', { parent: A, location: mul(A.x, A.i) })).toThrow('location should not contain BaseScalars');
    expect(() => CoordSys3D('B', { parent: S.One as never })).toThrow('parent should be a CoordSys3D/None');
    expect(() => CoordSys3D('B', { rotationMatrix: S.One as never })).toThrow('rotation_matrix should be an ImmutableMatrix instance');
    expect(str(CoordSys3D('B', { location: A.i }).origin.positionWrt(CoordSys3D('B')))).toBe('0');
    expect(eq(CoordSys3D('B', [Matrix.eye(3), Vector.zero]), CoordSys3D('B'))).toBe(true);
    expect(pi).toBeDefined();
  });

  it('transformations of located systems', () => {
    const A = CoordSys3D('A');
    const B = A.locateNew('B', A.i);
    expect(tuple(B.transformationFromParent())).toBe('(A.x - 1, A.y, A.z)');
    expect(tuple(B.transformationToParent())).toBe('(B.x + 1, B.y, B.z)');
    expect(str(B.transformation as Expr)).toBe('((1, 0, 0, 0, 1, 0, 0, 0, 1), A.i)');
    const L = CoordSys3D('L', (u: Expr, w: Expr, t: Expr) => [u, w, t]);
    expect(L.transformation).toBeInstanceOf(Lambda);
    const V = CoordSys3D('V', { vectorNames: ['x', 'y', 'z'] });
    expect(() => V.x).toThrow('x of V is a base vector');
  });
});
