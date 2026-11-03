// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of sympy.matrices.expressions.matexpr (and special): indexing,
 * explicit matrices, MatrixElement, the special matrices, MatAdd, MatMul,
 * MatPow, Inverse, Transpose, Adjoint, MatrixSlice, Trace, Determinant,
 * Permanent and ElementwiseApplyFunction. Expected values from SymPy 1.14
 * (str form, explicit matrices on one line).
 */

import { describe, expect, it } from 'vitest';
import { I as ImagUnit, Matrix, cos, diff, latex, sin, sstr, symbols } from '../src';
import type { Expr } from '../src';
import {
  GenericIdentity,
  GenericZeroMatrix,
  Identity,
  ImmutableMatrix,
  Inverse,
  MatPow,
  MatrixElement,
  MatrixSymbol,
  OneMatrix,
  Determinant,
  Trace,
  ZeroMatrix,
} from '../src/matrices/expressions';
import type { MatrixExpr } from '../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const [x, y, n] = symbols('x y n');
const X = MatrixSymbol('X', 2, 2);
const A = MatrixSymbol('A', 2, 3);
const Y = MatrixSymbol('Y', n, n);

describe('MatrixExpr indexing', () => {
  it('det and single indices', () => {
    expect(s(X.det())).toBe('Determinant(X)');
    expect(s(X.at(1))).toBe('X[0, 1]');
    expect(s(X.at(-1))).toBe('X[-1, 1]');
    expect(() => X.at(5)).toThrow('Invalid index 5');
    expect(() => Y.at(1)).toThrow('Single indexing is only supported when the number of columns is known.');
    expect(() => X.at(x)).toThrow('Only integers may be used');
    expect(() => X.at(3, 0)).toThrow('Invalid indices (3, 0)');
  });
  it('equalsExplicit', () => {
    expect(X.equalsExplicit(X)).toBe(true);
    expect(X.equalsExplicit(1)).toBe(false);
    expect(X.equalsExplicit(A)).toBe(false);
    expect(ImmutableMatrix([[1, 2]]).equalsExplicit(ImmutableMatrix([[1], [2]]))).toBe(false);
  });
});

describe('ImmutableMatrix', () => {
  const Mx = ImmutableMatrix([
    [1, x],
    [ImagUnit, 2],
  ]);
  it('adjoint, conjugate, inverse and powers', () => {
    expect(s(Mx.adjoint())).toBe('Matrix([[1, -I], [conjugate(x), 2]])');
    expect(s(Mx.conjugate())).toBe('Matrix([[1, conjugate(x)], [-I, 2]])');
    // SymPy prints Matrix([[2*I/(x + 2*I), -I*x/(x + 2*I)], [1/(x + 2*I), I/(x + 2*I)]]), the same entries
    const inv = ImmutableMatrix([
      [ImagUnit.mul(2).div(x.add(ImagUnit.mul(2))), ImagUnit.mul(x).neg().div(x.add(ImagUnit.mul(2)))],
      [x.add(ImagUnit.mul(2)).pow(-1), ImagUnit.div(x.add(ImagUnit.mul(2)))],
    ]);
    expect(M(Mx.inv()).equalsExplicit(inv)).toBe(true);
    expect(M(Mx.pow(-1)).equalsExplicit(inv)).toBe(true);
    // SymPy: Matrix([[(-I*x - 4)/(x**2 + 4*I*x - 4), 3*x/(x**2 + 4*I*x - 4)], [3*I/(x**2 + 4*I*x - 4), (-I*x - 1)/(x**2 + 4*I*x - 4)]])
    const d = x.pow(2).add(ImagUnit.mul(4).mul(x)).sub(4);
    const inv2 = ImmutableMatrix([
      [ImagUnit.mul(x).neg().sub(4).div(d), x.mul(3).div(d)],
      [ImagUnit.mul(3).div(d), ImagUnit.mul(x).neg().sub(1).div(d)],
    ]);
    expect(M(M(MatPow(Mx, -2)).doit()).equalsExplicit(inv2)).toBe(true);
  });
  it('simplify, expand and diff', () => {
    expect(s(ImmutableMatrix([[sin(x).pow(2).add(cos(x).pow(2))]]).simplify())).toBe('Matrix([[1]])');
    expect(s(ImmutableMatrix([[x.add(1).pow(2)]]).expand())).toBe('Matrix([[x**2 + 2*x + 1]])');
    expect(s(diff(ImmutableMatrix([[x.pow(2), x]]), x))).toBe('Matrix([[2*x, 1]])');
  });
});

describe('MatrixElement', () => {
  it('indices, doit and diff', () => {
    const e = MatrixElement(X, 0, 1);
    expect((e as never as { indices: Expr[] }).indices.map(s)).toEqual(['0', '1']);
    expect(s(M(X).at(0, 1))).toBe('X[0, 1]');
    expect(s(diff(MatrixElement(X, x, y), x))).toBe('0');
    expect(s(diff(X.at(0, 1), MatrixSymbol('B', 2, 2).at(0, 0) as never))).toBe('0');
    expect(s(diff(M(X.mul(A)).at(0, 1), X.at(0, 0) as never))).toBe('A[0, 1]');
    expect(() => MatrixElement(1, 0, 0)).toThrow('First argument of MatrixElement should be a matrix');
    expect(() => MatrixElement(X, 5, 0)).toThrow('indices out of range');
  });
});

describe('special matrices', () => {
  it('Identity, GenericIdentity and GenericZeroMatrix', () => {
    const I3 = Identity(3);
    expect(s(I3.conjugate())).toBe('I');
    expect(s(diff(I3, x))).toBe('0');
    expect(s(I3.adjoint())).toBe('I');
    expect(s(GenericIdentity())).toBe('I');
    expect(s(GenericZeroMatrix())).toBe('0');
    expect(latex(GenericIdentity())).toBe('\\mathbb{I}');
    expect(() => GenericIdentity().shape).toThrow('GenericIdentity does not have a specified shape');
    expect(() => GenericZeroMatrix().shape).toThrow('GenericZeroMatrix does not have a specified shape');
  });
  it('ZeroMatrix', () => {
    const Z = ZeroMatrix(2, 3);
    expect(s(Z.adjoint())).toBe('0');
    expect(s(Trace(ZeroMatrix(2, 2)).doit())).toBe('0');
    expect(s(Determinant(ZeroMatrix(2, 2)).doit())).toBe('0');
    expect(s(Z.conjugate())).toBe('0');
    expect(s(Z.at(0, 1))).toBe('0');
    expect(s(diff(Z, x))).toBe('0');
    expect(s(M(MatPow(ZeroMatrix(2, 2), 2)).doit())).toBe('0');
    expect(() => M(MatPow(ZeroMatrix(2, 2), -1)).doit()).toThrow('Matrix det == 0; not invertible');
  });
  it('OneMatrix', () => {
    const O = OneMatrix(2, 3);
    const O2 = OneMatrix(2, 2);
    expect(String(O.asExplicit())).toBe('Matrix([[1, 1, 1], [1, 1, 1]])');
    expect(s(O.adjoint())).toBe('1');
    expect(s(O.conjugate())).toBe('1');
    expect(s(O.at(0, 0))).toBe('1');
    expect(s(diff(O, x))).toBe('0');
    expect(s(M(MatPow(O2, 3)).doit())).toBe('4*1');
    expect(s(M(MatPow(O2, x)).doit())).toBe('1**x');
    expect(s(Determinant(O2).doit())).toBe('0');
    expect(s(Determinant(OneMatrix(n, n)).doit())).toBe('Determinant(1)');
    expect(s(Inverse(OneMatrix(n, n)).doit())).toBe('1**(-1)');
    expect(s(M(MatPow(OneMatrix(1, 1), 5)).doit())).toBe('I');
    expect(s(OneMatrix(1, n).T)).toBe('1');
    expect(() => OneMatrix(n, 2).asExplicit()).toThrow(RangeError);
    expect(() => M(MatPow(O2, -1)).doit()).toThrow('Matrix det == 0; not invertible');
    expect(() => O2.inverse()).toThrow('Matrix det == 0; not invertible');
  });
});

void Matrix;
