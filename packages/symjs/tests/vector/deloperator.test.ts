// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/deloperator.ts (SymPy sympy/vector/deloperator.py and
// test_del_operator of sympy/vector/tests/test_field_functions.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { S, add, doit, latex, mul, pow, simplify, str, symbol } from '../../src';
import { CoordSys3D, Del, Vector, curl, divergence, gradient } from '../../src/vector';

const C = CoordSys3D('C');
const [i, j, k] = C.baseVectors();
const [x, y, z] = C.baseScalars();
const delop = Del();

describe('Del (SymPy test_del_operator)', () => {
  it('prints delop', () => {
    expect(str(delop)).toBe('delop');
    expect(latex(delop)).toBe('delop');
    expect(delop.withArgs()).toBe(delop);
  });

  it('cross: the curl', () => {
    expect(delop.cross(Vector.zero)).toBe(Vector.zero);
    expect(doit(delop.cross(i))).toBe(Vector.zero);
    expect(delop.cross(mul(2, pow(y, 2), j), { doit: true })).toBe(Vector.zero);
    const v = mul(x, y, z, add(i, j, k));
    expect(str(doit(delop.cross(v)))).toBe('(-C.x*C.y + C.x*C.z)*C.i + (C.x*C.y - C.y*C.z)*C.j + (-C.x*C.z + C.y*C.z)*C.k');
    expect(doit(delop.cross(v)).key).toBe(curl(v).key);
    expect(str(delop.cross(mul(2, pow(x, 2), j)))).toBe(
      '(Derivative(0, C.y) - Derivative(2*C.x**2, C.z))*C.i + (-Derivative(0, C.x) + Derivative(0, C.z))*C.j + (-Derivative(0, C.y) + Derivative(2*C.x**2, C.x))*C.k',
    );
    expect(str(delop.cross(mul(2, pow(x, 2), j), { doit: true }))).toBe('4*C.x*C.k');
  });

  it('dot: the divergence', () => {
    expect(str(delop.dot(Vector.zero))).toBe('0');
    expect(str(doit(delop.dot(i)))).toBe('0');
    expect(str(doit(delop.dot(mul(pow(x, 2), i))))).toBe('2*C.x');
    const v = mul(x, y, z, add(i, j, k));
    expect(str(delop.dot(v, { doit: true }))).toBe('C.x*C.y + C.x*C.z + C.y*C.z');
    expect(divergence(v).key).toBe(delop.dot(v, { doit: true }).key);
    expect(str(delop.dot(mul(pow(mul(x, y, z), -1), add(i, j, k)), { doit: true }))).toBe('-1/(C.x*C.y*C.z**2) - 1/(C.x*C.y**2*C.z) - 1/(C.x**2*C.y*C.z)');
    const w = add(mul(x, i), mul(y, j), mul(z, k));
    expect(str(delop.dot(w))).toBe('Derivative(C.x, C.x) + Derivative(C.y, C.y) + Derivative(C.z, C.z)');
    expect(str(delop.dot(w, { doit: true }))).toBe('3');
    expect(str(simplify(doit(delop.dot(w))))).toBe('3');
  });

  it('gradient', () => {
    expect(delop.gradient(0, { doit: true })).toBe(Vector.zero);
    expect(delop.gradient(0)).toBe(Vector.zero);
    expect(str(delop.gradient(x))).toBe('(Derivative(C.x, C.x))*C.i + (Derivative(C.x, C.y))*C.j + (Derivative(C.x, C.z))*C.k');
    expect(doit(delop.gradient(x))).toBe(i);
    expect(gradient(x)).toBe(i);
    expect(str(delop.gradient(mul(x, y, z), { doit: true }))).toBe('C.y*C.z*C.i + C.x*C.z*C.j + C.x*C.y*C.k');
    expect(str(doit(delop.gradient(mul(2, pow(x, 2)))))).toBe('4*C.x*C.i');
  });

  it('directional derivative (v & delop)', () => {
    const v = add(mul(x, i), mul(y, j), mul(z, k));
    expect(str(Vector.zero.dot(delop)(symbol('a')))).toBe('0');
    expect(str(doit(i.dot(delop)(x)))).toBe('1');
    expect(str(doit(i.dot(delop)(mul(x, y, z))))).toBe('C.y*C.z');
    expect(str((v as Vector).dot(delop)(x))).toBe('C.x');
    expect(str((v as Vector).dot(delop)(mul(x, y, z)))).toBe('3*C.x*C.y*C.z');
    expect(str((v as Vector).dot(delop)(add(x, y, z)))).toBe('C.x + C.y + C.z');
    expect((v as Vector).dot(delop)(v).key).toBe(v.key);
    expect(i.dot(delop)(v)).toBe(i);
    expect((v as Vector).dot(delop)(Vector.zero)).toBe(Vector.zero);
    expect(str((v as Vector).dot(delop)(S.Zero))).toBe('0');
  });
});
