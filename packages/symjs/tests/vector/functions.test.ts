// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/functions.ts (SymPy sympy/vector/functions.py and
// sympy/vector/tests/test_functions.py, test_field_functions.py). Expected
// values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Matrix, S, add, cos, expand, mul, pow, simplify, sin, sqrt, str, symbol } from '../../src';
import type { Expr } from '../../src';
import {
  CoordSys3D,
  Dyadic,
  Vector,
  curl,
  directionalDerivative,
  express,
  gradient,
  isConservative,
  isSolenoidal,
  laplacian,
  matrixToVector,
  orthogonalize,
  scalarPotential,
  scalarPotentialDifference,
} from '../../src/vector';

const eq = (u: Expr, v: Expr): boolean => u.key === v.key;
const N = CoordSys3D('N');
const [q1, q2, q3] = [symbol('q1'), symbol('q2'), symbol('q3')];
const A = N.orientNewAxis('A', q1, N.k);
const B = A.orientNewAxis('B', q2, A.i);
const C = B.orientNewAxis('C', q3, B.j);

describe('express (SymPy test_functions)', () => {
  it('re-expresses base vectors', () => {
    expect(express(Vector.zero, N)).toBe(Vector.zero);
    expect(str(express(S.Zero, N))).toBe('0');
    expect(str(express(A.i, C))).toBe('(cos(q3))*C.i + (sin(q3))*C.k');
    expect(str(express(A.j, C))).toBe('(sin(q2)*sin(q3))*C.i + (cos(q2))*C.j + (-sin(q2)*cos(q3))*C.k');
    expect(str(express(A.k, C))).toBe('(-sin(q3)*cos(q2))*C.i + (sin(q2))*C.j + (cos(q2)*cos(q3))*C.k');
    expect(str(express(A.i, N))).toBe('(cos(q1))*N.i + (sin(q1))*N.j');
    expect(express(A.k, N)).toBe(N.k);
    expect(express(A.i, A)).toBe(A.i);
    expect(express(A.i, B)).toBe(B.i);
    expect(str(express(N.i, B))).toBe('(cos(q1))*B.i + (-sin(q1)*cos(q2))*B.j + (sin(q1)*sin(q2))*B.k');
    expect(str(express(N.i, C))).toBe('(-sin(q1)*sin(q2)*sin(q3) + cos(q1)*cos(q3))*C.i + (-sin(q1)*cos(q2))*C.j + (sin(q1)*sin(q2)*cos(q3) + sin(q3)*cos(q1))*C.k');
    expect(str(express(C.i, N))).toBe('(-sin(q1)*sin(q2)*sin(q3) + cos(q1)*cos(q3))*N.i + (sin(q1)*cos(q3) + sin(q2)*sin(q3)*cos(q1))*N.j + (-sin(q3)*cos(q2))*N.k');
    expect(str(express(C.i, B))).toBe('(cos(q3))*B.i + (-sin(q3))*B.k');
    expect(express(C.j, B)).toBe(B.j);
  });

  it('expresses vectors back as base vectors', () => {
    expect(simplify(express(add(mul(cos(q1), A.i), mul(-1, sin(q1), A.j)), N))).toBe(N.i);
    expect(simplify(express(add(mul(sin(q1), A.i), mul(cos(q1), A.j)), N))).toBe(N.j);
    expect(simplify(express(add(mul(cos(q1), B.i), mul(-1, sin(q1), cos(q2), B.j), mul(sin(q1), sin(q2), B.k)), N))).toBe(N.i);
    expect(simplify(express(add(mul(sin(q2), B.j), mul(cos(q2), B.k)), N))).toBe(N.k);
    expect(simplify(express(add(mul(cos(q3), C.i), mul(sin(q3), C.k)), A))).toBe(A.i);
    expect(simplify(express(add(mul(-1, sin(q3), cos(q2), C.i), mul(sin(q2), C.j), mul(cos(q2), cos(q3), C.k)), A))).toBe(A.k);
  });

  it('expresses scalars and checks the arguments', () => {
    const q = symbol('q');
    const P = N.orientNewAxis('P', q, N.k);
    expect(str(express(mul(N.x, N.i), P, undefined, { variables: true }))).toBe('((P.x*cos(q) - P.y*sin(q))*cos(q))*P.i + (-(P.x*cos(q) - P.y*sin(q))*sin(q))*P.j');
    expect(str(express(P.x, N, undefined, { variables: true }))).toBe('N.x*cos(q) + N.y*sin(q)');
    expect(express(N.x, N)).toBe(N.x);
    expect(str(express(5, P))).toBe('5');
    expect(() => express(N.i, S.One as never)).toThrow('system should be a CoordSys3D instance');
    expect(() => express(N.i, P, N)).toThrow('system2 should not be provided for Vectors');
    expect(() => express(N.x, P, N)).toThrow('system2 should not be provided');
    expect(() => express(N.i.outer(N.j), P, S.One as never)).toThrow('system2 should be a CoordSys3D instance');
    expect(express(Dyadic.zero, P)).toBe(Dyadic.zero);
    expect(str(express(mul(N.x, N.i.outer(N.j)), N, P, { variables: true }))).toBe('(N.x*sin(q))*(N.i|P.i) + (N.x*cos(q))*(N.i|P.j)');
  });

  it('matrix_to_vector', () => {
    expect(str(matrixToVector(Matrix.col(1, 2, 3), C))).toBe('C.i + 2*C.j + 3*C.k');
    expect(matrixToVector(Matrix.col(0, 0, 0), N)).toBe(Vector.zero);
    expect(str(matrixToVector(Matrix.col(q1, q2, q3), N))).toBe('q1*N.i + q2*N.j + q3*N.k');
  });

  it('orthogonalize', () => {
    const D = CoordSys3D('C');
    const [a, b] = [symbol('a', { integer: true }), symbol('b', { integer: true })];
    const [i, j] = D.baseVectors();
    const v1 = add(i, mul(2, j));
    const v2 = add(mul(2, i), mul(3, j));
    expect(orthogonalize(v1, v2).map(str)).toEqual(['C.i + 2*C.j', '2/5*C.i + (-1/5)*C.j']);
    expect(orthogonalize(add(mul(3, i), j), add(mul(2, i), mul(2, j)), { orthonormal: true }).map(str)).toEqual([
      '(3*sqrt(10)/10)*C.i + (sqrt(10)/10)*C.j',
      '(-sqrt(10)/10)*C.i + (3*sqrt(10)/10)*C.j',
    ]);
    expect(() => orthogonalize(v1, v2, add(mul(3, i), mul(5, j)))).toThrow('Vector set not linearly independent');
    expect(() => orthogonalize(add(mul(a, i), mul(b, j)), add(mul(4, a, i), mul(4, b, j)))).toThrow(RangeError);
    expect(() => orthogonalize(v1, D.x)).toThrow('Each element must be of Type Vector');
    expect(sqrt(2)).toBeDefined();
  });
});

describe('field functions (SymPy test_field_functions)', () => {
  const P0 = CoordSys3D('C');
  const [i, j, k] = P0.baseVectors();
  const [x, y, z] = P0.baseScalars();
  const q = symbol('q');
  const P = P0.orientNewAxis('P', q, P0.k);
  const scalarField = mul(2, pow(x, 2), y, z);
  const gradField = gradient(scalarField);
  const vectorField = add(mul(pow(y, 2), i), mul(3, x, j), mul(5, y, z, k));
  const curlField = curl(vectorField);

  it('laplacian', () => {
    expect(str(laplacian(mul(x, y, z)))).toBe('0');
    expect(str(laplacian(pow(x, 2)))).toBe('2');
    expect(eq(laplacian(mul(pow(x, 2), pow(y, 2), pow(z, 2))), add(mul(2, pow(y, 2), pow(z, 2)), mul(2, pow(x, 2), pow(z, 2)), mul(2, pow(x, 2), pow(y, 2))))).toBe(true);
    const As = CoordSys3D('A', { transformation: 'spherical', variableNames: ['r', 'theta', 'phi'] });
    const Bc = CoordSys3D('B', { transformation: 'cylindrical', variableNames: ['r', 'theta', 'z'] });
    expect(str(laplacian(add(...As.baseScalars())))).toBe('2/A.r + cos(A.theta)/(A.r**2*sin(A.theta))');
    expect(str(laplacian(add(...Bc.baseScalars())))).toBe('1/B.r');
    expect(laplacian(mul(x, y, z, add(i, j, k)))).toBe(Vector.zero);
    expect(str(laplacian(mul(x, pow(y, 2), z, add(i, j, k))))).toBe('2*C.x*C.z*C.i + 2*C.x*C.z*C.j + 2*C.x*C.z*C.k');
  });

  it('is_conservative', () => {
    expect(isConservative(Vector.zero)).toBe(true);
    expect(isConservative(i)).toBe(true);
    expect(isConservative(add(mul(2, i), mul(3, j), mul(4, k)))).toBe(true);
    expect(isConservative(add(mul(y, z, i), mul(x, z, j), mul(x, y, k)))).toBe(true);
    expect(isConservative(mul(x, j))).toBe(false);
    expect(isConservative(gradField)).toBe(true);
    expect(isConservative(curlField)).toBe(false);
    expect(isConservative(add(mul(4, x, y, z, i), mul(2, pow(x, 2), z, j)))).toBe(false);
    expect(isConservative(add(mul(z, P.i), mul(P.x, k)))).toBe(true);
    expect(() => isConservative(x)).toThrow('field should be a Vector');
  });

  it('is_solenoidal', () => {
    expect(isSolenoidal(Vector.zero)).toBe(true);
    expect(isSolenoidal(i)).toBe(true);
    expect(isSolenoidal(add(mul(y, z, i), mul(x, z, j), mul(x, y, k)))).toBe(true);
    expect(isSolenoidal(mul(y, j))).toBe(false);
    expect(isSolenoidal(gradField)).toBe(false);
    expect(isSolenoidal(curlField)).toBe(true);
    expect(isSolenoidal(mul(add(mul(-2, y), 3), k))).toBe(true);
    expect(isSolenoidal(add(mul(cos(q), i), mul(sin(q), j), mul(cos(q), P.k)))).toBe(true);
    expect(isSolenoidal(add(mul(z, P.i), mul(P.x, k)))).toBe(true);
    expect(() => isSolenoidal(x)).toThrow('field should be a Vector');
  });

  it('directional_derivative', () => {
    const v = add(mul(3, P0.i), mul(4, P0.j), P0.k);
    expect(str(directionalDerivative(mul(x, y, z), v))).toBe('C.x*C.y + 4*C.x*C.z + 3*C.y*C.z');
    expect(str(directionalDerivative(mul(5, pow(x, 2), z), v))).toBe('5*C.x**2 + 30*C.x*C.z');
    expect(str(directionalDerivative(mul(5, pow(x, 2), z), mul(4, P0.j)))).toBe('0');
    const D = CoordSys3D('D', { transformation: 'spherical', variableNames: ['r', 'theta', 'phi'], vectorNames: ['e_r', 'e_theta', 'e_phi'] });
    const [r, , phi] = D.baseScalars();
    const [er, eth, eph] = D.baseVectors();
    expect(str(directionalDerivative(mul(pow(r, 2), er), er))).toBe('2*D.r*D.e_r');
    expect(str(directionalDerivative(mul(5, pow(r, 2), phi), add(mul(3, er), mul(4, eth), eph)))).toBe('30*D.phi*D.r + 5*D.r**2');
    expect(str(directionalDerivative(symbol('a'), er))).toBe('0');
    expect(directionalDerivative(Vector.zero, er)).toBe(Vector.zero);
    expect(directionalDerivative(i, er)).toBe(Vector.zero);
  });

  it('scalar_potential', () => {
    expect(str(scalarPotential(Vector.zero, P0))).toBe('0');
    expect(scalarPotential(i, P0)).toBe(x);
    expect(scalarPotential(k, P0)).toBe(z);
    expect(eq(scalarPotential(add(mul(y, z, i), mul(x, z, j), mul(x, y, k)), P0), mul(x, y, z))).toBe(true);
    expect(eq(scalarPotential(gradField, P0), scalarField)).toBe(true);
    expect(str(scalarPotential(add(mul(z, P.i), mul(P.x, k)), P0))).toBe('C.x*C.z*cos(q) + C.y*C.z*sin(q)');
    expect(str(scalarPotential(add(mul(z, P.i), mul(P.x, k)), P))).toBe('P.x*P.z');
    expect(() => scalarPotential(mul(x, j), P0)).toThrow('Field is not conservative');
    expect(() => scalarPotential(i, S.One as never)).toThrow('coord_sys must be a CoordSys3D');
  });

  it('scalar_potential_difference', () => {
    const point1 = P0.origin.locateNew('P1', add(i, mul(2, j), mul(3, k)));
    const point2 = P0.origin.locateNew('P2', add(mul(4, i), mul(5, j), mul(6, k)));
    const genericC = P0.origin.locateNew('RP', add(mul(x, i), mul(y, j), mul(z, k)));
    const genericP = P.origin.locateNew('PP', add(mul(P.x, P.i), mul(P.y, P.j), mul(P.z, P.k)));
    expect(str(scalarPotentialDifference(S.Zero, P0, point1, point2))).toBe('0');
    expect(eq(scalarPotentialDifference(scalarField, P0, P0.origin, genericC), scalarField)).toBe(true);
    expect(eq(scalarPotentialDifference(gradField, P0, P0.origin, genericC), scalarField)).toBe(true);
    expect(str(scalarPotentialDifference(gradField, P0, point1, point2))).toBe('948');
    expect(str(scalarPotentialDifference(add(mul(y, z, i), mul(x, z, j), mul(x, y, k)), P0, point1, genericC))).toBe('C.x*C.y*C.z - 6');
    const expected = mul(2, P.z, add(mul(P.x, sin(q)), mul(P.y, cos(q))), pow(add(mul(P.x, cos(q)), mul(-1, P.y, sin(q))), 2));
    expect(str(expand(simplify(scalarPotentialDifference(gradField, P, P.origin, genericP)).sub(expected)))).toBe('0');
    expect(() => scalarPotentialDifference(i, S.One as never, point1, point2)).toThrow('coord_sys must be a CoordSys3D');
  });
});
