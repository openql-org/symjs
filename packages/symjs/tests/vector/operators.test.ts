// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/operators.ts (SymPy sympy/vector/operators.py and
// sympy/vector/tests/test_operators.py, test_field_functions.py). Expected
// values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Derivative, S, add, cos, doit, latex, mul, pow, pretty, sin, str, symbol } from '../../src';
import type { Expr } from '../../src';
import { CoordSys3D, Cross, Curl, Divergence, Dot, Gradient, Laplacian, Vector, VectorZero, curl, divergence, gradient } from '../../src/vector';

const R = CoordSys3D('R');
const s1 = mul(R.x, R.y, R.z);
const s2 = add(R.x, mul(3, pow(R.y, 2)));
const s3 = add(pow(R.x, 2), pow(R.y, 2), pow(R.z, 2));
const v1 = add(mul(R.x, R.i), mul(R.z, R.z, R.j));
const v2 = add(mul(R.x, R.i), mul(R.y, R.j), mul(R.z, R.k));
const v3 = add(mul(pow(R.x, 2), R.i), mul(pow(R.y, 2), R.j), mul(pow(R.z, 2), R.k));
const eq = (u: Expr, v: Expr): boolean => u.key === v.key;

describe('the unevaluated operators (SymPy test_operators)', () => {
  it('Gradient', () => {
    expect(eq(Gradient(s1), Gradient(mul(R.x, R.y, R.z)))).toBe(true);
    expect(str(doit(Gradient(s1)))).toBe('R.y*R.z*R.i + R.x*R.z*R.j + R.x*R.y*R.k');
    expect(str(doit(Gradient(s2)))).toBe('R.i + 6*R.y*R.j');
    expect(Gradient(s1).isScalar).toBe(false);
    expect(str(Gradient(s1).withArgs([R.x]))).toBe('Gradient(R.x)');
    expect(Gradient(s1).expr).toBe(s1);
  });

  it('Divergence', () => {
    expect(eq(Divergence(v1), Divergence(add(mul(R.x, R.i), mul(R.z, R.z, R.j))))).toBe(true);
    expect(str(doit(Divergence(v1)))).toBe('1');
    expect(str(doit(Divergence(v2)))).toBe('3');
    // issue 22384
    const Rc = CoordSys3D('R', 'cylindrical');
    expect(str(doit(Divergence(Rc.i)))).toBe('1/R.r');
    expect(str(Divergence(v1).withArgs([v2]))).toBe('Divergence(R.x*R.i + R.y*R.j + R.z*R.k)');
  });

  it('Curl', () => {
    expect(eq(Curl(v1), Curl(add(mul(R.x, R.i), mul(R.z, R.z, R.j))))).toBe(true);
    expect(str(doit(Curl(v1)))).toBe('(-2*R.z)*R.i');
    expect(doit(Curl(v2))).toBe(VectorZero());
    expect(Curl(v1).isScalar).toBe(false);
    expect(str(Curl(v1).withArgs([v2]))).toBe('Curl(R.x*R.i + R.y*R.j + R.z*R.k)');
  });

  it('Laplacian', () => {
    expect(eq(Laplacian(s3), Laplacian(add(pow(R.x, 2), pow(R.y, 2), pow(R.z, 2))))).toBe(true);
    expect(str(doit(Laplacian(s3)))).toBe('6');
    expect(str(doit(Laplacian(v3)))).toBe('2*R.i + 2*R.j + 2*R.k');
    expect(str(Laplacian(s3).withArgs([R.x]))).toBe('Laplacian(R.x)');
  });

  it('prints like SymPy', () => {
    expect(latex(Gradient(R.x))).toBe('\\nabla \\mathbf{{x}_{R}}');
    expect(latex(Divergence(v2))).toBe('\\nabla\\cdot \\left(\\left(\\mathbf{{x}_{R}}\\right)\\mathbf{\\hat{i}_{R}} + \\left(\\mathbf{{y}_{R}}\\right)\\mathbf{\\hat{j}_{R}} + \\left(\\mathbf{{z}_{R}}\\right)\\mathbf{\\hat{k}_{R}}\\right)');
    expect(latex(Curl(R.i))).toBe('\\nabla\\times \\mathbf{\\hat{i}_{R}}');
    expect(latex(Laplacian(add(R.x, R.y)))).toBe('\\Delta \\left(\\mathbf{{x}_{R}} + \\mathbf{{y}_{R}}\\right)');
    const up = (e: Expr): string => pretty(e, { useUnicode: true });
    expect(up(Gradient(R.x))).toBe('∇(x_R)');
    expect(up(Divergence(R.i))).toBe('∇⋅(i_R)');
    expect(up(Curl(R.i))).toBe('∇×(i_R)');
    expect(up(Laplacian(R.x))).toBe('∆(x_R)');
  });
});

describe('gradient, divergence and curl (SymPy test_field_functions)', () => {
  const C = CoordSys3D('C');
  const [i, j, k] = C.baseVectors();
  const [x, y, z] = C.baseScalars();

  it('curl', () => {
    expect(curl(Vector.zero)).toBe(Vector.zero);
    expect(curl(i)).toBe(Vector.zero);
    expect(curl(mul(2, pow(y, 2), j))).toBe(Vector.zero);
    const v = mul(x, y, z, add(i, j, k));
    expect(str(curl(v))).toBe('(-C.x*C.y + C.x*C.z)*C.i + (C.x*C.y - C.y*C.z)*C.j + (-C.x*C.z + C.y*C.z)*C.k');
    expect(str(curl(mul(2, pow(x, 2), j), { doit: false }))).toBe(
      '(Derivative(0, C.y) - Derivative(2*C.x**2, C.z))*C.i + (-Derivative(0, C.x) + Derivative(0, C.z))*C.j + (-Derivative(0, C.y) + Derivative(2*C.x**2, C.x))*C.k',
    );
    expect(str(curl(mul(2, pow(x, 2), j)))).toBe('4*C.x*C.k');
    expect(curl(S.One)).toBe(Vector.zero);
  });

  it('divergence', () => {
    expect(str(divergence(Vector.zero))).toBe('0');
    expect(str(divergence(i))).toBe('0');
    expect(str(divergence(mul(pow(x, 2), i)))).toBe('2*C.x');
    expect(str(divergence(mul(x, y, z, add(i, j, k))))).toBe('C.x*C.y + C.x*C.z + C.y*C.z');
    expect(str(divergence(mul(pow(mul(x, y, z), -1), add(i, j, k))))).toBe('-1/(C.x*C.y*C.z**2) - 1/(C.x*C.y**2*C.z) - 1/(C.x**2*C.y*C.z)');
    expect(str(divergence(add(mul(x, i), mul(y, j), mul(z, k)), { doit: false }))).toBe('Derivative(C.x, C.x) + Derivative(C.y, C.y) + Derivative(C.z, C.z)');
    expect(str(divergence(Cross(i, mul(x, j))))).toBe('Divergence(Cross(C.i, C.x*C.j))');
  });

  it('gradient', () => {
    expect(gradient(0)).toBe(Vector.zero);
    expect(str(gradient(x, { doit: false }))).toBe('(Derivative(C.x, C.x))*C.i + (Derivative(C.x, C.y))*C.j + (Derivative(C.x, C.z))*C.k');
    expect(gradient(x)).toBe(i);
    expect(str(gradient(mul(x, y, z)))).toBe('C.y*C.z*C.i + C.x*C.z*C.j + C.x*C.y*C.k');
    expect(str(gradient(mul(2, pow(x, 2))))).toBe('4*C.x*C.i');
    const a = symbol('a');
    expect(str(gradient(mul(a, sin(y), pow(x, -1))))).toBe('(-a*sin(C.y)/C.x**2)*C.i + (a*cos(C.y)/C.x)*C.j');
  });

  it('curvilinear systems', () => {
    const A = CoordSys3D('A', { transformation: 'spherical', variableNames: ['r', 'theta', 'phi'] });
    const B = CoordSys3D('B', { transformation: 'cylindrical', variableNames: ['r', 'theta', 'z'] });
    const [r, th, ph] = A.baseScalars();
    expect(str(gradient(add(mul(3, r), mul(4, th))))).toBe('3*A.i + 4/A.r*A.j');
    expect(str(gradient(add(mul(3, r, ph), mul(4, th))))).toBe('3*A.phi*A.i + 4/A.r*A.j + (3/sin(A.theta))*A.k');
    expect(gradient(add(mul(0, r), mul(0, th), mul(0, ph)))).toBe(Vector.zero);
    expect(str(gradient(mul(r, th, ph)))).toBe('A.phi*A.theta*A.i + A.phi*A.j + (A.theta/sin(A.theta))*A.k');
    expect(eq(divergence(add(mul(r, A.i), mul(th, A.j), mul(ph, A.k))), add(mul(add(mul(sin(th), r), mul(cos(th), r, th)), pow(mul(sin(th), pow(r, 2)), -1)), 3, pow(mul(sin(th), r), -1)))).toBe(true);
    expect(str(divergence(add(mul(0, A.i), mul(0, A.j), mul(0, A.k))))).toBe('0');
    expect(str(curl(add(mul(r, A.i), mul(th, A.j), mul(ph, A.k))))).toBe('(A.phi*cos(A.theta)/(A.r*sin(A.theta)))*A.i + (-A.phi/A.r)*A.j + A.theta/A.r*A.k');
    expect(str(curl(add(mul(r, A.j), mul(ph, A.k))))).toBe('(A.phi*cos(A.theta)/(A.r*sin(A.theta)))*A.i + (-A.phi/A.r)*A.j + 2*A.k');
    expect(str(gradient(mul(B.attr('r'), B.attr('theta'), B.z)))).toBe('B.theta*B.z*B.i + B.z*B.j + B.r*B.theta*B.k');
    expect(str(gradient(mul(2, B.attr('theta'))))).toBe('2/B.r*B.j');
    expect(str(divergence(add(mul(B.attr('r'), B.i), mul(B.attr('theta'), B.j), mul(B.z, B.k))))).toBe('3 + 1/B.r');
    expect(str(curl(add(mul(B.attr('r'), B.j), mul(B.z, B.k))))).toBe('2*B.k');
    expect(curl(add(mul(3, B.i), mul(2, pow(B.attr('r'), -1), B.j), mul(4, B.k)))).toBe(Vector.zero);
  });

  it('mixed coordinate systems', () => {
    const a = CoordSys3D('a');
    const b = CoordSys3D('b');
    const c = CoordSys3D('c');
    const q = symbol('q');
    expect(str(gradient(mul(a.x, b.y)))).toBe('b.y*a.i + a.x*b.j');
    expect(str(gradient(add(mul(3, cos(q), a.x, b.x), mul(a.y, add(a.x, cos(q), b.x)))))).toBe('(a.y + 3*b.x*cos(q))*a.i + (a.x + b.x + cos(q))*a.j + (3*a.x*cos(q) + a.y)*b.i');
    expect(eq(gradient(pow(a.x, b.y)), Gradient(pow(a.x, b.y)))).toBe(true);
    expect(eq(gradient(cos(mul(a.x, b.y))), Gradient(cos(mul(a.x, b.y))))).toBe(true);
    const all = add(mul(a.i, a.x), mul(a.j, a.y), mul(a.z, a.k), mul(b.i, b.x), mul(b.j, b.y), mul(b.z, b.k), mul(c.i, c.x), mul(c.j, c.y), mul(c.z, c.k));
    expect(str(divergence(all))).toBe('9');
    expect(eq(divergence(add(mul(3, a.i, a.x, a.z), mul(b.j, b.x, c.z), mul(3, a.j, a.z, a.y))), add(mul(6, a.z), mul(b.x, Dot(b.j, c.k))))).toBe(true);
    const cr = Cross(mul(a.x, a.i), mul(a.y, b.j));
    expect(
      eq(
        divergence(mul(a.x, b.x, c.x, cr)),
        add(mul(a.x, b.x, c.x, Divergence(cr)), mul(b.x, c.x, Dot(cr, a.i)), mul(a.x, c.x, Dot(cr, b.i)), mul(a.x, b.x, Dot(cr, c.i))),
      ),
    ).toBe(true);
    expect(str(curl(add(mul(a.x, a.j), mul(b.x, b.k))))).toBe('a.k + (-1)*b.j');
    const d = a.orientNewAxis('d', q, a.k);
    expect(str(curl(mul(a.y, d.x, a.k)))).toBe('d.x*a.i + (-a.y)*d.j');
    expect(str(curl(mul(a.y, d.x, a.k), { doit: false }))).toBe(
      '(a.y*d.x*(-Derivative(0, a.z) + Derivative(1, a.y)) + d.x)*a.i + (a.y*d.x*(Derivative(0, a.z) - Derivative(1, a.x)))*a.j + (a.y*d.x*(Derivative(0, a.x) - Derivative(0, a.y)))*a.k + (-a.y)*d.j',
    );
    expect(str(divergence(mul(a.y, d.x, d.k)))).toBe('0');
    expect(str(divergence(mul(a.y, d.x, d.k), { doit: false }))).toBe('a.y*d.x*Derivative(1, d.z) + Dot(d.k, d.x*a.j + a.y*d.i)');
    expect(str(curl(cr))).toBe('Curl(Cross(a.x*a.i, a.y*b.j))');
    // SymPy crashes (AttributeError: 'Mul' object has no attribute 'components') on the product of unconnected systems
    expect(() => curl(mul(a.y, b.x, a.k))).toThrow(TypeError);
    // SymPy: AttributeError ('BaseScalar' object has no attribute 'dot')
    expect(() => curl(add(a.x, b.y))).toThrow(TypeError);
    expect(() => curl(Derivative(add(a.x, b.y), a.x))).toThrow('Invalid argument for curl');
    expect(() => divergence(Derivative(add(a.x, b.y), a.x))).toThrow('Invalid argument for divergence');
  });
});
