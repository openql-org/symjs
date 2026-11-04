// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/vector.ts (SymPy sympy/vector/vector.py and
// sympy/vector/tests/test_vector.py, test_printing.py). Expected values are
// those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Derivative, Float, I, Integral, Matrix, Mul, NumberKind, Rational, S, SymFunction, add, cos, diff, doit, integrate, kindOf, latex, mul, pi, pow, pretty, simplify, sin, sqrt, str, symbol, trigsimp } from '../../src';
import type { Expr } from '../../src';
import { BaseVector, CoordSys3D, Cross, Dot, Gradient, Vector, VectorAdd, VectorKind, VectorMul, VectorZero, cross, dot } from '../../src/vector';
import { coordSystems, mulStr, projections, outer } from '../../src/vector/vector';

const C = CoordSys3D('C');
const [i, j, k] = C.baseVectors();
const [a, b, c] = [symbol('a'), symbol('b'), symbol('c')];
const same = (u: Expr, v: Expr): void => expect(str(u)).toBe(str(v)) as unknown as void;
const eq = (u: Expr, v: Expr): boolean => u.key === v.key;
const asV = (e: Expr): Vector => {
  if (!(e instanceof Vector)) throw new TypeError('not a vector');
  return e;
};

describe('Vector (SymPy test_vector)', () => {
  it('cross', () => {
    const v1 = add(mul(C.x, i), mul(C.z, C.z, j));
    const v2 = add(mul(C.x, i), mul(C.y, j), mul(C.z, k));
    expect(str(Cross(v1, v2))).toBe('Cross(C.x*C.i + C.z**2*C.j, C.x*C.i + C.y*C.j + C.z*C.k)');
    const r = add(mul(pow(C.z, 3), C.i), mul(mul(-1, C.x, C.z), C.j), mul(add(mul(C.x, C.y), mul(-1, C.x, pow(C.z, 2))), C.k));
    expect(eq(doit(Cross(v1, v2)), r)).toBe(true);
    expect(eq(cross(v1, v2), r)).toBe(true);
    expect(eq(Cross(v1, v2), mul(-1, Cross(v2, v1)))).toBe(true);
    expect(cross(v1, v2).add(cross(v2, v1))).toBe(Vector.zero);
    // SymPy cannot add unevaluated products (XFAIL test_cross_xfail expects Vector.zero); symjs adds them as
    // scalar terms, and Cross(v2, v1) is -Cross(v1, v2)
    expect(str(add(Cross(v1, v2), Cross(v2, v1)))).toBe('0');
    expect(str(Cross(i, mul(C.x, j)).neg())).toBe('-Cross(C.i, C.x*C.j)');
  });

  it('dot', () => {
    const v1 = add(mul(C.x, i), mul(C.z, C.z, j));
    const v2 = add(mul(C.x, i), mul(C.y, j), mul(C.z, k));
    expect(str(Dot(v1, v2))).toBe('Dot(C.x*C.i + C.z**2*C.j, C.x*C.i + C.y*C.j + C.z*C.k)');
    expect(str(doit(Dot(v1, v2)))).toBe('C.x**2 + C.y*C.z**2');
    expect(str(doit(Dot(v2, v1)))).toBe('C.x**2 + C.y*C.z**2');
    expect(eq(Dot(v1, v2), Dot(v2, v1))).toBe(true);
    expect(latex(Dot(v1, C.i))).toBe('\\mathbf{\\hat{i}_{C}} \\cdot \\left(\\left(\\mathbf{{x}_{C}}\\right)\\mathbf{\\hat{i}_{C}} + \\left(\\mathbf{{z}_{C}}^{2}\\right)\\mathbf{\\hat{j}_{C}}\\right)');
    expect(latex(Cross(C.i, C.j))).toBe('\\mathbf{\\hat{i}_{C}} \\times \\mathbf{\\hat{j}_{C}}');
  });

  it('follows the hashing and equality of SymPy', () => {
    const v1 = mul(3, j);
    expect(eq(v1, mul(j, 3))).toBe(true);
    expect([...asV(v1).components]).toEqual([[j, S.One.mul(3)]]);
    const v2 = add(mul(3, i), mul(4, j), mul(5, k));
    const v3 = add(mul(2, i), mul(4, j), i, mul(4, k), k);
    expect(eq(v3, v2)).toBe(true);
  });

  it('kind', () => {
    expect(kindOf(C.i)).toBe(VectorKind(NumberKind));
    expect(kindOf(C.x)).toBe(NumberKind);
    expect(kindOf(mul(2, C.i))).toBe(VectorKind(NumberKind));
    const v1 = add(mul(C.x, i), mul(C.z, C.z, j));
    const v2 = add(mul(C.x, i), mul(C.y, j), mul(C.z, k));
    expect(kindOf(add(v1, v2))).toBe(VectorKind(NumberKind));
    expect(kindOf(doit(Cross(v1, v2)))).toBe(VectorKind(NumberKind));
    expect(kindOf(VectorZero())).toBe(VectorKind(NumberKind));
    expect(kindOf(asV(v1).projection(v2))).toBe(VectorKind());
  });

  it('VectorAdd', () => {
    expect(add(C.i, C.j)).toBeInstanceOf(VectorAdd);
    // https://github.com/sympy/sympy/issues/26121
    const E = Matrix.of([[C.i, C.j, C.k]]);
    const av = E.mul(Matrix.col(1, 2, 3));
    expect(av.get(0, 0)).toBeInstanceOf(VectorAdd);
    expect(str(av.get(0, 0))).toBe('C.i + 2*C.j + 3*C.k');
    expect(kindOf(av.get(0, 0))).toBe(VectorKind());
  });

  it('vector', () => {
    expect(i).toBeInstanceOf(BaseVector);
    expect(eq(i, j)).toBe(false);
    expect(i.sub(i)).toBe(Vector.zero);
    expect(i.add(Vector.zero)).toBe(i);
    expect(i.sub(Vector.zero)).toBe(i);
    expect(eq(Vector.zero, S.Zero)).toBe(false);
    expect(Vector.zero.neg()).toBe(Vector.zero);
    const v1 = add(mul(a, i), mul(b, j), mul(c, k));
    const v2 = add(mul(pow(a, 2), i), mul(pow(b, 2), j), mul(pow(c, 2), k));
    const v3 = add(v1, v2);
    const v4 = mul(2, v1);
    const v5 = mul(a, i);
    expect(v1).toBeInstanceOf(VectorAdd);
    expect(v1.sub(v1)).toBe(Vector.zero);
    expect(eq(v1.add(Vector.zero), v1)).toBe(true);
    expect(asV(v1).dot(i)).toBe(a);
    expect(eq(i.dot(v2), pow(a, 2))).toBe(true);
    same(asV(v3).dot(i), add(pow(a, 2), a));
    expect(eq(add(v1, v2), add(v2, v1))).toBe(true);
    expect(eq(v1.sub(v2), mul(-1, v2.sub(v1)))).toBe(true);
    expect(eq(mul(a, v1), mul(v1, a))).toBe(true);
    expect(v5).toBeInstanceOf(VectorMul);
    const m = v5 as InstanceType<typeof VectorMul>;
    expect(m.baseVector).toBe(i);
    expect(m.measureNumber).toBe(a);
    expect(v4).toBeInstanceOf(VectorAdd);
    expect(Vector.zero).toBeInstanceOf(VectorZero);
    expect(mul(v1, 0)).toBe(Vector.zero);
    expect(asV(v1).toMatrix(C).equals(Matrix.col(a, b, c))).toBe(true);
    expect([...i.components]).toEqual([[i, S.One]]);
    expect(eq(VectorAdd(v1, Vector.zero), v1)).toBe(true);
    expect(eq(VectorMul(a, v1), mul(v1, a))).toBe(true);
    expect(VectorMul(1, i)).toBe(i);
    expect(VectorMul(0, Vector.zero)).toBe(Vector.zero);
    expect(str(VectorMul(2, a))).toBe('2*a');
    expect(() => asV(v1).outer(S.One)).toThrow(TypeError);
    expect(() => asV(v1).dot(S.One)).toThrow(TypeError);
    // VectorMul(1, i) and products of vectors
    expect(() => mul(i, j)).toThrow('Invalid multiplication');
    expect(() => mul(Cross(i, mul(C.x, j)), i)).toThrow('Invalid multiplication');
    expect(() => VectorAdd(i, 1)).toThrow('1 cannot be interpreted correctly');
    // SymPy's Add(C.i, x) drops x; symjs does not
    expect(() => add(i, a)).toThrow(TypeError);
    expect(add(0, i)).toBe(i);
    expect(str(VectorAdd(new Mul([S.One.mul(2), i]), add(j, k)))).toBe('2*C.i + C.j + C.k');
    expect(() => VectorAdd(new Mul([a, b]))).toThrow('a*b cannot be interpreted correctly');
  });

  it('magnitude and normalize', () => {
    expect(str(Vector.zero.magnitude())).toBe('0');
    expect(Vector.zero.normalize()).toBe(Vector.zero);
    expect(i.magnitude()).toBe(S.One);
    expect(i.normalize()).toBe(i);
    const v1 = asV(mul(a, i));
    same(v1.normalize(), mul(mul(a, pow(sqrt(pow(a, 2)), -1)), i));
    same(v1.magnitude(), sqrt(pow(a, 2)));
    const v2 = asV(add(mul(a, i), mul(b, j), mul(c, k)));
    same(v2.magnitude(), sqrt(add(pow(a, 2), pow(b, 2), pow(c, 2))));
    same(v2.normalize(), v2.div(v2.magnitude()));
    same(asV(add(i, j)).normalize(), add(mul(sqrt(2), S.Half, C.i), mul(sqrt(2), S.Half, C.j)));
  });

  it('simplify and trigsimp', () => {
    const t1 = mul(add(pow(a, -1), pow(b, -1)), i);
    expect(eq(asV(t1).dot(i), mul(add(a, b), pow(mul(a, b), -1)))).toBe(false);
    const s1 = simplify(t1);
    // SymPy: (a + b)/(a*b); symjs simplify keeps 1/a + 1/b (the same value)
    expect(str(simplify(asV(s1).dot(i).sub(mul(add(a, b), pow(mul(a, b), -1)))))).toBe('0');
    expect(eq(s1.simplify(), simplify(s1))).toBe(true);
    const t3 = simplify(mul(mul(add(4, mul(4, a), mul(-2, add(2, mul(2, a)))), pow(add(2, mul(2, a)), -1)), i));
    expect(t3).toBe(Vector.zero);
    const t4 = simplify(mul(mul(add(mul(-4, a, pow(b, 2)), mul(-2, pow(b, 3)), mul(-2, pow(a, 2), b)), pow(add(a, b), -2)), i));
    same(asV(t4).dot(i), mul(-2, b));
    const v = asV(add(mul(pow(add(sin(a), cos(a)), 2), i), mul(-1, j)));
    same(trigsimp(v), add(mul(mul(2, pow(sin(add(a, mul(pi, Rational.of(1, 4)))), 2)), i), mul(-1, j)));
    same(v.trigsimp(), trigsimp(v));
    expect(simplify(Vector.zero)).toBe(Vector.zero);
  });

  it('equals', () => {
    expect(asV(mul(2, i)).equals(j)).toBe(false);
    expect(i.equals(i)).toBe(true);
    // https://github.com/sympy/sympy/issues/25915
    const A = mul(add(sqrt(2), sqrt(6)), pow(sqrt(add(sqrt(3), 2)), -1));
    expect(asV(mul(A, i)).equals(mul(2, i))).toBe(true);
    expect(asV(mul(A, i)).equals(mul(3, i))).toBe(false);
    const D = C.orientNewAxis('D', mul(pi, S.Half), C.k);
    expect(D.i.equals(C.j)).toBe(true);
    expect(D.i.equals(C.i)).toBe(false);
  });

  it('conjugate', () => {
    // https://github.com/sympy/sympy/issues/27094
    const v = add(mul(I, i), mul(add(1, I), j), mul(2, k));
    expect(eq(v.conjugate(), add(mul(mul(-1, I), i), mul(add(1, mul(-1, I)), j), mul(2, k)))).toBe(true);
    expect(i.conjugate()).toBe(i);
  });

  it('dot and cross of base vectors', () => {
    expect(str(i.dot(Vector.zero))).toBe('0');
    expect(str(Vector.zero.dot(i))).toBe('0');
    for (const [u, v, d] of [
      [i, i, 1],
      [i, j, 0],
      [j, k, 0],
      [k, k, 1],
    ] as const) {
      expect(str(u.dot(v))).toBe(String(d));
    }
    expect(() => k.dot(S.One)).toThrow(TypeError);
    expect(i.cross(Vector.zero)).toBe(Vector.zero);
    expect(Vector.zero.cross(i)).toBe(Vector.zero);
    expect(i.cross(i)).toBe(Vector.zero);
    expect(i.cross(j)).toBe(k);
    same(i.cross(k), mul(-1, j));
    same(j.cross(i), mul(-1, k));
    expect(j.cross(k)).toBe(i);
    expect(k.cross(i)).toBe(j);
    same(k.cross(j), mul(-1, i));
    // SymPy: k.cross(1) == Cross(k, 1)
    expect(eq(k.cross(S.One), Cross(k, 1))).toBe(true);
  });

  it('projection', () => {
    const v1 = asV(add(i, j, k));
    const v2 = add(mul(3, i), mul(4, j));
    const v3 = asV(add(mul(0, i), mul(0, j)));
    same(v1.projection(v1), add(i, j, k));
    expect(str(v1.projection(v2))).toBe('7/3*C.i + 7/3*C.j + 7/3*C.k');
    expect(str(v1.projection(v1, { scalar: true }))).toBe('1');
    expect(str(v1.projection(v2, { scalar: true }))).toBe('7/3');
    expect(v3.projection(v1)).toBe(Vector.zero);
    expect(str(v3.projection(v1, { scalar: true }))).toBe('0');
  });

  it('diff and integrate', () => {
    const f = SymFunction('f');
    const v = add(mul(f(a), C.i), mul(pow(a, 2), C.j), mul(-1, C.k));
    expect(str(Derivative(v, a))).toBe('Derivative((f(a))*C.i + a**2*C.j + (-1)*C.k, a)');
    expect(str(diff(v, a))).toBe('(Derivative(f(a), a))*C.i + 2*a*C.j');
    expect(eq(diff(v, a), v.diff(a))).toBe(true);
    expect(str(integrate(v, symbol('a')))).toBe('(Integral(f(a), a))*C.i + (Integral(a**2, a))*C.j + (Integral(-1, a))*C.k');
    expect(str(integrate(v, symbol('a'), [0, 1]))).toBe('(Integral(f(a), (a, 0, 1)))*C.i + (Integral(a**2, (a, 0, 1)))*C.j + (Integral(-1, (a, 0, 1)))*C.k');
    expect(str(doit(new Integral([v, symbol('a')])))).toBe('(Integral(f(a), a))*C.i + (Integral(a**2, a))*C.j + (Integral(-1, a))*C.k');
    // SymPy raises TypeError for a vector as the variable; symjs keeps the derivative unevaluated
    expect(str(diff(v, C.i))).toBe('Derivative((f(a))*C.i + a**2*C.j + (-1)*C.k, C.i)');
    expect(() => asV(v).diffSelf(C.i, diff)).toThrow('Invalid arg for differentiation');
  });

  it('checks the arguments of BaseVector', () => {
    expect(() => BaseVector(3, C)).toThrow(RangeError);
    expect(() => BaseVector(0, Vector.zero as never)).toThrow(TypeError);
    const v = BaseVector(1, C);
    expect(v.prettyForm).toBe('x1');
    expect(v.latexForm).toBe('x_1');
    expect(str(v)).toBe('C.j');
    expect(v.withArgs()).toBe(v);
    expect(eq(v, C.j)).toBe(true);
  });

  it('is_Vector and is_scalar', () => {
    const v1 = asV(add(mul(3, C.i), mul(4, C.j), mul(5, C.k)));
    const v2 = add(mul(3, C.i), mul(-4, C.j), mul(5, C.k));
    expect(v1.isVector).toBe(true);
    expect(v1.isScalar).toBe(false);
    expect(asV(v1.cross(v2)).isScalar).toBe(false);
  });
});

describe('Vector methods', () => {
  it('separate, components and evalf', () => {
    const R1 = CoordSys3D('R1');
    const R2 = CoordSys3D('R2');
    const v = asV(add(R1.i, R2.i));
    expect([...v.separate()].map(([s, p]) => `${str(s)}: ${str(p)}`)).toEqual(['R1: R1.i', 'R2: R2.i']);
    expect(str(add(R2.i, R1.j, mul(a, R2.k)))).toBe('R1.j + R2.i + a*R2.k');
    const w = add(mul(3, C.i), mul(4, C.j), mul(a, C.k));
    expect(str(w.evalf())).toBe('3.0*C.i + 4.0*C.j + a*C.k');
    expect(eq(w.evalf(15, { subs: { a: 1 } }), w.subs(a, 1).evalf())).toBe(true);
    expect(str(asV(w).factor())).toBe(str(w));
    expect(asV(w).asNumerDenom()).toEqual([w, S.One]);
    expect(asV(w).asCoeffMul()).toEqual([S.One, w]);
    expect(asV(w).asCoeffAdd()[1].map(str).sort()).toEqual(['3*C.i', '4*C.j', 'a*C.k']);
    expect(str(asV(mul(Derivative(C.x, C.x), C.i)).doit())).toBe('C.i');
  });

  it('division', () => {
    expect(str(C.i.div(2))).toBe('1/2*C.i');
    expect(() => C.i.div(0)).toThrow('Cannot divide a vector by zero');
    expect(() => C.i.div(C.j)).toThrow('Cannot divide two vectors');
    expect(() => pow(C.i, -1)).toThrow(TypeError);
    expect(() => pow(2, C.i)).toThrow(TypeError);
    expect(pow(C.i, 1)).toBe(C.i);
  });

  it('cross and dot across systems', () => {
    const q = symbol('q');
    const B = C.orientNewAxis('B', q, C.k);
    expect(str(cross(C.i, B.i))).toBe('(sin(q))*B.k');
    expect(str(dot(C.i, B.i))).toBe('cos(q)');
    const E = CoordSys3D('E');
    expect(str(cross(C.i, E.i))).toBe('Cross(C.i, E.i)');
    expect(str(dot(C.i, E.i))).toBe('Dot(C.i, E.i)');
    expect(str(dot(mul(2, C.i), add(C.i, C.j)))).toBe('2');
    expect(str(dot(add(C.i, C.j), mul(2, C.j)))).toBe('2');
    expect(str(dot(Vector.zero, C.i))).toBe('0');
    expect(str(dot(C.i, Vector.zero))).toBe('0');
    expect(str(cross(C.i, mul(2, C.j)))).toBe('2*C.k');
    expect(str(dot(C.i, Cross(C.j, E.i)))).toBe('Dot(C.i, Cross(C.j, E.i))');
    expect(str(cross(C.i, Cross(C.j, E.i)))).toBe('Cross(C.i, Cross(C.j, E.i))');
    expect(str(Cross(E.i, C.i))).toBe('-Cross(C.i, E.i)');
  });

  it('outer and projections', () => {
    expect(str(outer(C.i, add(C.j, mul(2, C.k))))).toBe('(C.i|C.j) + 2*(C.i|C.k)');
    expect(str(outer(Vector.zero, C.i))).toBe('0');
    expect(() => outer(C.x, C.i)).toThrow('Invalid operand for outer product');
    expect(projections(add(mul(3, C.i), mul(4, C.j), mul(5, C.k))).map(str)).toEqual(['3', '4', '5']);
    expect(projections(mul(C.x, C.y, C.z, C.i)).map(str)).toEqual(['C.x*C.y*C.z', '0', '0']);
    expect(projections(Vector.zero).map(str)).toEqual(['0', '0', '0']);
    expect(coordSystems(mul(C.x, C.i)).map(str)).toEqual(['C']);
    expect(coordSystems(C).map(str)).toEqual(['C']);
    expect(mulStr(S.NegOne, C.i, str)).toBe('(-1)*C.i');
  });
});

describe('printing of vectors (SymPy test_printing)', () => {
  const N = CoordSys3D('N');
  const P = N.orientNewAxis('C', a, N.k);
  const f = SymFunction('f');
  const ib = new Integral([f(b), symbol('b')]);
  const v = [
    Vector.zero,
    N.i,
    mul(-1, N.i),
    add(N.i, N.j),
    mul(a, N.i),
    add(mul(a, N.i), mul(-1, b, N.j)),
    add(mul(add(pow(a, 2), N.x), N.i), N.k),
    add(mul(add(pow(a, 2), b), N.i), mul(3, add(P.y, mul(-1, c)), N.k)),
    add(N.j, mul(-1, add(ib, mul(-1, pow(P.x, 2))), N.k)),
    add(N.i, P.k),
  ];
  const up = (e: Expr): string => pretty(e, { useUnicode: true, wrapLine: false });

  it('str', () => {
    expect(v.map(str).slice(0, 4)).toEqual(['0', 'N.i', '(-1)*N.i', 'N.i + N.j']);
    expect(str(v[8]!)).toBe('N.j + (C.x**2 - Integral(f(b), b))*N.k');
    expect(str(v[9]!)).toBe('C.k + N.i');
    expect(str(mul(3, pow(N.x, 2), P.y))).toBe('3*C.y*N.x**2');
  });

  it('latex', () => {
    expect(latex(v[0]!)).toBe('\\mathbf{\\hat{0}}');
    expect(latex(v[1]!)).toBe('\\mathbf{\\hat{i}_{N}}');
    expect(latex(v[2]!)).toBe('- \\mathbf{\\hat{i}_{N}}');
    expect(latex(v[5]!)).toBe('\\left(a\\right)\\mathbf{\\hat{i}_{N}} + \\left(- b\\right)\\mathbf{\\hat{j}_{N}}');
    expect(latex(v[6]!)).toBe('\\left(\\mathbf{{x}_{N}} + a^{2}\\right)\\mathbf{\\hat{i}_{N}} + \\mathbf{\\hat{k}_{N}}');
    expect(latex(v[8]!)).toBe('\\mathbf{\\hat{j}_{N}} + \\left(\\mathbf{{x}_{C}}^{2} - \\int f{\\left(b \\right)}\\, db\\right)\\mathbf{\\hat{k}_{N}}');
    expect(latex(mul(3, pow(N.x, 2), P.y))).toBe('3 \\mathbf{{y}_{C}} \\mathbf{{x}_{N}}^{2}');
  });

  it('unicode pretty form', () => {
    expect(up(v[0]!)).toBe('0');
    expect(up(v[1]!)).toBe('i_N');
    expect(up(v[5]!)).toBe('(a) i_N + (-b) j_N');
    expect(up(v[2]!)).toBe('(-1) i_N');
    expect(up(v[8]!)).toBe('      ⎛   2   ⌠        ⎞    \nj_N + ⎜x_C  - ⎮ f(b) db⎟ k_N\n      ⎝       ⌡        ⎠    ');
    const v11 = add(mul(add(pow(a, 2), b), N.i), mul(ib, N.k));
    expect(up(v11)).toBe('⎛ 2    ⎞        ⎛⌠        ⎞    \n⎝a  + b⎠ i_N  + ⎜⎮ f(b) db⎟ k_N\n                ⎝⌡        ⎠    ');
    expect(up(mul(3, pow(N.x, 2), P.y))).toBe('         2\n3⋅y_C⋅x_N ');
    expect(() => pretty(v[1]!, { useUnicode: false })).toThrow('ASCII pretty printing of BasisDependent is not implemented');
    expect(up(Cross(N.i, N.j))).toBe('(i_N)×(j_N)');
    expect(up(Dot(N.i, N.j))).toBe('(i_N)⋅(j_N)');
  });

  it('issue 23058', () => {
    const CC = CoordSys3D('C');
    const t = symbol('t');
    const ten = symbol('10', { positive: true });
    const bx = mul(2, pow(ten, -4), cos(mul(pow(ten, 5), t)), sin(mul(pow(ten, -3), CC.y)));
    expect(up(mul(bx, CC.i))).toBe(
      '⎛     ⎛y_C⎞    ⎛  5  ⎞⎞    \n⎜2⋅sin⎜───⎟⋅cos⎝10 ⋅t⎠⎟ i_C\n⎜     ⎜  3⎟           ⎟    \n⎜     ⎝10 ⎠           ⎟    \n⎜─────────────────────⎟    \n⎜           4         ⎟    \n⎝         10          ⎠    ',
    );
  });

  it('unevaluated products', () => {
    const E = CoordSys3D('E');
    const cr = Cross(C.i, E.i) as InstanceType<typeof Cross>;
    expect(str(cr.subs(C.x, 1))).toBe('Cross(C.i, E.i)');
    expect(str(cr.withArgs([C.j, E.j]))).toBe('Cross(C.j, E.j)');
    expect(() => cr.components).toThrow('Cross has no components');
    expect(() => diff(Cross(mul(a, C.i), E.i), a)).toThrow();
    // SymPy raises AttributeError (a Cross has no components); symjs simplifies the operands
    expect(str(simplify(Cross(mul(add(a, a), C.i), E.i)))).toBe('-Cross(E.i, 2*a*C.i)');
    expect(str(Cross(mul(a, C.i), E.i).conjugate())).toBe('-conjugate(Cross(E.i, a*C.i))');
    expect(str(Cross(mul(new Float(0.5), C.i), E.i).evalf())).toBe('-Cross(E.i, 0.5*C.i)');
    expect(cr.simplifySelf()).toBeUndefined();
    expect(cr.integrateSelf()).toBeUndefined();
    expect(str(integrate(Cross(mul(a, C.i), E.i), symbol('a')))).toBe('Integral(-Cross(E.i, a*C.i), a)');
    const dt = Dot(C.i, E.i) as InstanceType<typeof Dot>;
    expect(str(dt.withArgs([C.j, E.j]))).toBe('Dot(C.j, E.j)');
    expect(Vector.zero.withArgs()).toBe(Vector.zero);
    expect(str(add(mul(a, C.i), C.j).subs(a, 0))).toBe('C.j');
    expect(() => VectorAdd(add(a, b))).toThrow('a cannot be interpreted correctly');
    expect(() => mul(Gradient(C.x), C.i)).toThrow('Invalid multiplication');
    expect(() => mul(C.i, C.i.outer(C.j))).toThrow('Invalid multiplication');
  });
});
