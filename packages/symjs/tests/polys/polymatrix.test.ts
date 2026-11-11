// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Matrix, Poly, PolyMatrix, QQ, ZZ, Sym, parseExpr as p } from '../../src';
const x = new Sym('x');
it('unifies coefficient rings for rectangular matrix products', () => {
  const A = new PolyMatrix([[Poly.from(p('x**2'), [x]), Poly.from(x.neg(), [x])], [Poly.from(p('x**3'), [x]), Poly.from(x.sub(1), [x])]]);
  const B = new PolyMatrix([[1, 0], [-1, 0]], x);
  expect(String(A.ring)).toBe('ZZ[x]');
  expect(String(B.domain)).toBe('QQ');
  expect(B.gens).toEqual([x]);
  expect(A.shape).toEqual([2, 2]);
  expect(String(A.mul(B))).toBe('PolyMatrix([\n[    x**2 + x, 0],\n[x**3 - x + 1, 0]], ring=QQ[x])');
  expect(String(B.mul(A))).toBe('PolyMatrix([\n[ x**2, -x],\n[-x**2,  x]], ring=QQ[x])');
  expect(B.transpose().toMatrix().equals(Matrix.of([[1, -1], [0, 0]]))).toBe(true);
  expect(A.add(B).sub(B).toMatrix().equals(A.toMatrix())).toBe(true);
  expect(A.neg().add(A).toMatrix().equals(Matrix.zeros(2))).toBe(true);
  expect(A.mul(2).get(0, 0).asExpr().equals(p('2*x**2'))).toBe(true);
  expect(A.mul(QQ.fromSympy(p('1/2'))).ring.toString()).toBe('QQ[x]');
  expect(B.div(2).mul(2).equals(B)).toBe(true);
  expect(B.div(Poly.from(2, [x])).mul(2).equals(B)).toBe(true);
  expect(B.equals(A)).toBe(false);
});
it('constructs vectors and explicit rings and validates entries', () => {
  const v = new PolyMatrix([1, x]);
  expect(String(v.ring)).toBe('QQ[x]');
  v.set(0, 0, Poly.from(x.add(1), [x]));
  v.set(1, 0, 3);
  expect(v.get(0).asExpr().equals(x.add(1))).toBe(true);
  expect(v.get(1).asExpr().equals(3)).toBe(true);
  expect(() => v.set(5, 0, 1)).toThrow(RangeError);
  expect(() => new PolyMatrix([[1], [1, 2]], x)).toThrow(RangeError);
  expect(() => new PolyMatrix([p('1/2')], { ring: ZZ.polyRing(x) })).toThrow();
  expect(String(new PolyMatrix([[x]], { ring: 'QQ[x]' }))).toBe('PolyMatrix([[x]], ring=QQ[x])');
  expect(String(new PolyMatrix([], { ring: QQ.polyRing(x) }))).toBe('PolyMatrix(0, 0, [], ring=QQ[x])');
  expect(String(new PolyMatrix())).toBe('PolyMatrix(0, 0, [], ring=QQ[])');
  expect(() => new PolyMatrix([Poly.from(p('sin(x)'), [p('sin(x)')])])).toThrow(TypeError);
});
