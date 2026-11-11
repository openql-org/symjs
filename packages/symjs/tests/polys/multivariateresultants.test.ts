// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { DixonResultant, MacaulayResultant, Matrix, Poly, Sym, parseExpr as p } from '../../src';
const x = new Sym('x'), y = new Sym('y'), z = new Sym('z');
it('constructs the divided-difference polynomial and Dixon matrix', () => {
  const d = new DixonResultant([p('x+y'), p('x**2+y**3'), p('x**2+y')], [x,y]);
  expect([d.n, d.m]).toEqual([2,3]);
  const polynomial = d.getDixonPolynomial();
  expect(String(d.getDixonMatrix(polynomial))).toBe('Matrix([[0, 0, -1, 0, -1], [0, -1, 0, -1, 0], [-1, 0, 1, 0, 0], [0, -1, 0, 0, 1], [-1, 0, 0, 1, 0]])');
  expect(d.getDixonMatrix(polynomial).det().equals(0)).toBe(true);
  const linears = new DixonResultant([x.add(1), x.mul(2).add(3)], [x]);
  expect(String(linears.getDixonMatrix(linears.getDixonPolynomial()))).toBe('Matrix([[1]])');
  expect(() => new DixonResultant([], [])).toThrow(RangeError);
  expect(() => new DixonResultant([x], [x]).getDixonPolynomial()).toThrow(RangeError);
  expect(d.getMaxDegrees(Poly.from(0, d.dummyVariables))).toEqual([0,0]);
});
it('constructs Macaulay numerator and denominator matrices in lexicographic order', () => {
  const mac = new MacaulayResultant([p('a_0*y-a_1*x+a_2*z'), p('b_1*x**2+b_0*y**2-b_2*z**2'), p('c_0*y*z**2-c_1*x**3+c_2*x**2*z-c_3*x*z**2+c_4*z**3')], [x,y,z]);
  expect(mac.getSize()).toBe(15); expect(mac.degreeM).toBe(4);
  expect(mac.monomialSet.map(String)).toEqual(['x**4','x**3*y','x**3*z','x**2*y**2','x**2*y*z','x**2*z**2','x*y**3','x*y**2*z','x*y*z**2','x*z**3','y**4','y**3*z','y**2*z**2','y*z**3','z**4']);
  expect(String(mac.getSubmatrix(mac.getMatrix()))).toBe('Matrix([[-a_1, a_0, a_2, 0], [0, -a_1, 0, 0], [0, 0, -a_1, 0], [0, 0, 0, -a_1]])');
  expect(mac.getMonomialsOfCertainDegree(1).map(String)).toEqual(['x','y','z']);
  expect(() => mac.getMonomialsOfCertainDegree(-1)).toThrow(RangeError);
  expect(() => mac.getSubmatrix(Matrix.eye(2))).toThrow(RangeError);
  expect(() => new MacaulayResultant([], [])).toThrow(RangeError);
  expect(() => new MacaulayResultant([x], [x,y])).toThrow(RangeError);
  expect(() => new MacaulayResultant([x.add(1)], [x])).toThrow(RangeError);
  expect(() => new MacaulayResultant([0], [x])).toThrow(RangeError);
});
it('uses two pure-power divisors for nonreduced monomials in every dimension', () => {
  // SymPy 1.14 uses n-1 divisors, producing an incorrect denominator for n=2.
  const binary = new MacaulayResultant([x.pow(2).add(y.pow(2)), x.mul(y).add(y.pow(2))], [x,y]);
  expect(binary.getReducedNonreduced()).toEqual([[0,1,2,3],[]]);
  expect(binary.getSubmatrix(binary.getMatrix()).det().equals(1)).toBe(true);
  expect(binary.getMatrix().det().equals(2)).toBe(true);
  // Equal numerical coefficients must not affect row selection.
  const ternary = new MacaulayResultant([x, y.pow(2), z.pow(3)], [x,y,z]);
  expect(ternary.getSubmatrix(ternary.getMatrix()).det().equals(1)).toBe(true);
});
