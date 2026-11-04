// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/dyadic.ts (SymPy sympy/vector/dyadic.py and
// sympy/vector/tests/test_dyadic.py, test_printing.py). Expected values are
// those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Float, Matrix, S, add, cos, latex, mul, pi, pow, pretty, simplify, sin, str, symbol } from '../../src';
import type { Expr } from '../../src';
import { BaseDyadic, CoordSys3D, Dyadic, DyadicAdd, DyadicMul, DyadicZero, Vector, express } from '../../src/vector';

const A = CoordSys3D('A');
const [a, b, q] = [symbol('a'), symbol('b'), symbol('q')];
const eq = (u: Expr, v: Expr): boolean => u.key === v.key;
const asD = (e: Expr): Dyadic => {
  if (!(e instanceof Dyadic)) throw new TypeError('not a dyadic');
  return e;
};
const isZero = (e: Expr): boolean => simplify(e) === Dyadic.zero;

describe('Dyadic (SymPy test_dyadic)', () => {
  it('constructs and combines dyadics', () => {
    expect(eq(Dyadic.zero, S.Zero)).toBe(false);
    expect(Dyadic.zero).toBeInstanceOf(DyadicZero);
    expect(DyadicZero()).toBe(Dyadic.zero);
    expect(eq(BaseDyadic(A.i, A.j), BaseDyadic(A.j, A.i))).toBe(false);
    expect(BaseDyadic(Vector.zero, A.i)).toBe(Dyadic.zero);
    expect(BaseDyadic(A.i, Vector.zero)).toBe(Dyadic.zero);
    expect(() => BaseDyadic(mul(2, A.i), A.j)).toThrow('BaseDyadic cannot be composed of non-base vectors');
    const d1 = A.i.outer(A.i);
    const d2 = A.j.outer(A.j);
    const d3 = A.i.outer(A.j);
    expect(d1).toBeInstanceOf(BaseDyadic);
    const dMul = mul(a, d1);
    expect(dMul).toBeInstanceOf(DyadicMul);
    const m = dMul as InstanceType<typeof DyadicMul>;
    expect(m.baseDyadic).toBe(d1);
    expect(m.measureNumber).toBe(a);
    expect(add(mul(a, d1), mul(b, d3))).toBeInstanceOf(DyadicAdd);
    expect(eq(d3, BaseDyadic(A.i, A.j))).toBe(true);
    const v1 = add(mul(a, A.i), mul(-1, A.k));
    const v2 = add(A.i, mul(b, A.j));
    const o = (v1 as Vector).outer(v2);
    expect(eq(o, add(mul(a, BaseDyadic(A.i, A.i)), mul(a, b, BaseDyadic(A.i, A.j)), mul(-1, BaseDyadic(A.k, A.i)), mul(-1, b, BaseDyadic(A.k, A.j))))).toBe(true);
    expect(str(o)).toBe('a*(A.i|A.i) + a*b*(A.i|A.j) + (-1)*(A.k|A.i) + (-b)*(A.k|A.j)');
    expect(mul(d1, 0)).toBe(Dyadic.zero);
    expect(eq(mul(d1, 2), mul(2, d1))).toBe(true);
    expect(eq(d1.div(new Float(2)), mul(new Float(0.5), d1))).toBe(true);
    expect(() => d1.div(d2)).toThrow('Cannot divide two dyadics');
    expect(str(DyadicAdd(d1, d1))).toBe('2*(A.i|A.i)');
    expect(str(DyadicMul(3, d1))).toBe('3*(A.i|A.i)');
    expect((d1 as Dyadic).withArgs([A.i, A.i]).key).toBe(d1.key);
    expect(str(add(mul(a, d1), d2).subs(a, 2))).toBe('2*(A.i|A.i) + (A.j|A.j)');
    expect((Dyadic.zero as Dyadic).withArgs([])).toBe(Dyadic.zero);
    expect((mul(2, d1) as Dyadic).prettyForm).toBe('2*(A.i|A.i)');
  });

  it('dot and cross', () => {
    const d1 = asD(A.i.outer(A.i));
    const d2 = asD(A.j.outer(A.j));
    const d3 = asD(A.i.outer(A.j));
    expect(d1.dot(mul(0, d1))).toBe(Vector.zero);
    expect(d1.dot(d2)).toBe(Dyadic.zero);
    expect(d1.dot(A.i)).toBe(A.i);
    expect(d1.cross(Vector.zero)).toBe(Dyadic.zero);
    expect(d1.cross(A.i)).toBe(Dyadic.zero);
    expect(eq(d1.cross(A.k), mul(-1, A.i.outer(A.j)))).toBe(true);
    expect(eq(d2.cross(A.i), mul(-1, A.j.outer(A.k)))).toBe(true);
    expect(A.i.cross(d1)).toBe(Dyadic.zero);
    expect(eq(A.j.cross(d1), mul(-1, A.k.outer(A.i)))).toBe(true);
    expect(Vector.zero.cross(d1)).toBe(Dyadic.zero);
    expect(eq(A.k.cross(d1), A.j.outer(A.i))).toBe(true);
    expect(A.i.dot(d1)).toBe(A.i);
    expect(A.j.dot(d1)).toBe(Vector.zero);
    expect(Vector.zero.dot(d1)).toBe(Vector.zero);
    expect(A.j.dot(d2)).toBe(A.j);
    expect(eq(d1.dot(d3), d3)).toBe(true);
    expect(d3.dot(d1)).toBe(Dyadic.zero);
    expect(() => d1.dot(S.One)).toThrow('Inner product is not defined for 1 and Dyadics.');
    expect(() => d1.cross(d2)).toThrow('not supported for cross with dyadics');
  });

  it('express and to_matrix', () => {
    const d1 = asD(A.i.outer(A.i));
    const B = A.orientNewAxis('B', q, A.k);
    expect(eq(express(d1, B), express(d1, B, B))).toBe(true);
    const expr1 = add(mul(pow(cos(q), 2), B.i.outer(B.i)), mul(mul(-1, sin(q), cos(q)), B.i.outer(B.j)), mul(mul(-1, sin(q), cos(q)), B.j.outer(B.i)), mul(pow(sin(q), 2), B.j.outer(B.j)));
    expect(isZero(express(d1, B).sub(expr1))).toBe(true);
    const expr2 = add(mul(cos(q), B.i.outer(A.i)), mul(mul(-1, sin(q)), B.j.outer(A.i)));
    expect(isZero(express(d1, B, A).sub(expr2))).toBe(true);
    const expr3 = add(mul(cos(q), A.i.outer(B.i)), mul(mul(-1, sin(q)), A.i.outer(B.j)));
    expect(isZero(express(d1, A, B).sub(expr3))).toBe(true);
    expect(d1.toMatrix(A).equals(Matrix.of([[1, 0, 0], [0, 0, 0], [0, 0, 0]]))).toBe(true);
    expect(d1.toMatrix(A, B).equals(Matrix.of([[cos(q), mul(-1, sin(q)), 0], [0, 0, 0], [0, 0, 0]]))).toBe(true);
    expect(asD(A.i.outer(A.j)).toMatrix(A).equals(Matrix.of([[0, 1, 0], [0, 0, 0], [0, 0, 0]]))).toBe(true);
    const [c, d, e, f] = ['c', 'd', 'e', 'f'].map((n) => symbol(n));
    const v1 = add(mul(a, A.i), mul(b, A.j), mul(c!, A.k)) as Vector;
    const v2 = add(mul(d!, A.i), mul(e!, A.j), mul(f!, A.k));
    const d4 = asD(v1.outer(v2));
    expect(d4.toMatrix(A).equals(Matrix.of([[mul(a, d!), mul(a, e!), mul(a, f!)], [mul(b, d!), mul(b, e!), mul(b, f!)], [mul(c!, d!), mul(c!, e!), mul(c!, f!)]]))).toBe(true);
    const d5 = asD(v1.outer(v1));
    const C = A.orientNewAxis('C', q, A.i);
    const expected = C.rotationMatrix(A).mul(d5.toMatrix(A)).mul(C.rotationMatrix(A).T);
    expected.sub(d5.toMatrix(C)).data.forEach((x) => expect(str(simplify(x))).toBe('0'));
    expect(express(Dyadic.zero, A)).toBe(Dyadic.zero);
    expect(str((DyadicMul(2, A.i.outer(A.j)) as Dyadic).doit())).toBe('2*(A.i|A.j)');
  });

  it('simplify (SymPy test_dyadic_simplify)', () => {
    const [x, y] = [symbol('x'), symbol('y')];
    const N = CoordSys3D('N');
    const dy = N.i.outer(N.i);
    const t1 = asD(mul(add(pow(x, -1), pow(y, -1)), dy));
    const s1 = asD(t1.simplify());
    expect(eq(s1.simplify(), simplify(s1))).toBe(true);
    // SymPy: (x + y)/(x*y); symjs simplify keeps 1/x + 1/y (the same value)
    expect(str(simplify(N.i.dot(s1.dot(N.i)).sub(mul(add(x, y), pow(mul(x, y), -1)))))).toBe('0');
    const t4 = asD(simplify(mul(mul(add(mul(-4, x, pow(y, 2)), mul(-2, pow(y, 3)), mul(-2, pow(x, 2), y)), pow(add(x, y), -2)), dy)));
    expect(str(N.i.dot(t4.dot(N.i)))).toBe('-2*y');
  });

  it('prints like SymPy', () => {
    const N = CoordSys3D('N');
    const C = N.orientNewAxis('C', a, N.k);
    const up = (e: Expr): string => pretty(e, { useUnicode: true, wrapLine: false });
    expect(str(Dyadic.zero)).toBe('0');
    expect(str(N.i.outer(N.k))).toBe('(N.i|N.k)');
    expect(str(mul(a, N.i.outer(N.k)))).toBe('a*(N.i|N.k)');
    const d5 = add(mul(a, N.i), mul(-1, b, N.j)) as Vector;
    expect(str(d5.outer(N.k))).toBe('a*(N.i|N.k) + (-b)*(N.j|N.k)');
    expect(latex(Dyadic.zero)).toBe('(\\mathbf{\\hat{0}}|\\mathbf{\\hat{0}})');
    expect(latex(mul(a, N.i.outer(N.k)))).toBe('\\left(a\\right)\\left(\\mathbf{\\hat{i}_{N}}{\\middle|}\\mathbf{\\hat{k}_{N}}\\right)');
    expect(latex(add(N.i, C.k) as Vector).length).toBeGreaterThan(0);
    expect(latex((add(N.i, C.k) as Vector).outer(N.k))).toBe(
      '\\left(\\mathbf{\\hat{k}_{C}}{\\middle|}\\mathbf{\\hat{k}_{N}}\\right) + \\left(\\mathbf{\\hat{i}_{N}}{\\middle|}\\mathbf{\\hat{k}_{N}}\\right)',
    );
    expect(up(Dyadic.zero)).toBe('(0|0)');
    expect(up(d5.outer(N.k))).toBe('(a) (i_N|k_N) + (-b) (j_N|k_N)');
    const v7 = add(mul(add(pow(a, 2), b), N.i), mul(3, add(C.y, mul(-1, symbol('c'))), N.k)) as Vector;
    expect(up(v7.outer(N.k))).toBe('⎛ 2    ⎞                                     \n⎝a  + b⎠ (i_N|k_N)  + (3⋅y_C - 3⋅c) (k_N|k_N)');
    expect(up((express(N.i, C) as Vector).outer(N.k))).toBe('(cos(a)) (i_C|k_N) + (-sin(a)) (j_C|k_N)');
    expect(up(N.i.outer(N.k))).toBe('(i_N|k_N)');
    expect(up(mul(-1, N.i.outer(N.k)))).toBe('(-1) (i_N|k_N)');
    expect(() => up(pi.mul(N.i.outer(N.k)).div(0))).toThrow('Cannot divide a dyadic by zero');
  });
});
