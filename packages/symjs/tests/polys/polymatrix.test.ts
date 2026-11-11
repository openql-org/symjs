// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { CoercionFailed, DomainMatrix, Matrix, Poly, PolyMatrix, PolyMatrixRing, QQ, ZZ, Sym, parseExpr as p } from '../../src';
const x = new Sym('x'), y = new Sym('y');
const ring = (M: PolyMatrix): string => M.ring.toString();

it('unifies coefficient rings for rectangular matrix products', () => {
  const A = new PolyMatrix([[Poly.from(p('x**2'), [x]), Poly.from(x.neg(), [x])], [Poly.from(p('x**3'), [x]), Poly.from(x.sub(1), [x])]]);
  const B = new PolyMatrix([[1, 0], [-1, 0]], x);
  expect(ring(A)).toBe('ZZ[x]');
  expect(String(B.domain)).toBe('QQ');
  expect(B.gens).toEqual([x]);
  expect(A.shape).toEqual([2, 2]);
  expect(String(A.mul(B))).toBe('PolyMatrix([\n[    x**2 + x, 0],\n[x**3 - x + 1, 0]], ring=QQ[x])');
  expect(String(B.mul(A))).toBe('PolyMatrix([\n[ x**2, -x],\n[-x**2,  x]], ring=QQ[x])');
  expect(B.transpose().toMatrix().equals(Matrix.of([[1, -1], [0, 0]]))).toBe(true);
  expect(A.add(B).sub(B).toMatrix().equals(A.toMatrix())).toBe(true);
  expect(A.neg().add(A).toMatrix().equals(Matrix.zeros(2))).toBe(true);
  expect(A.mul(2).get(0, 0).asExpr().equals(p('2*x**2'))).toBe(true);
  expect(ring(A.mul(2))).toBe('ZZ[x]');
  expect(ring(A.mul(p('1/2')))).toBe('QQ[x]');
  expect(ring(A.mul(y))).toBe('ZZ[x,y]');
  expect(ring(A.mul(2n))).toBe('ZZ[x]');
  expect(B.div(2).mul(2).equals(B)).toBe(true);
  expect(B.div(Poly.from(2, [x])).mul(2).equals(B)).toBe(true);
  expect(B.div(2n).equals(B.div(2))).toBe(true);
  expect(B.equals(A)).toBe(false);
  expect(B.equals(B.toMatrix())).toBe(false);
  expect(B.equals(new PolyMatrix([[1, 0]], x))).toBe(false);
  expect(B.equals(new PolyMatrix([[1, 0], [-1, 1]], x))).toBe(false);
  expect(() => A.mul(new PolyMatrix([1, 2, 3], x))).toThrow(RangeError);
  expect(() => A.add(new PolyMatrix([1, 2], x))).toThrow(RangeError);
  expect(() => A.add(1 as never)).toThrow(TypeError);
  expect(() => A.sub([] as never)).toThrow(TypeError);
  expect(() => A.mul([] as never)).toThrow(TypeError);
  expect(() => A.div([] as never)).toThrow(TypeError);
  expect(() => B.div(x)).toThrow(CoercionFailed);
});

it('constructs from rows, columns, shapes, entry functions and rings', () => {
  const M1 = new PolyMatrix([[x, y]], { ring: QQ.polyRing(x, y) });
  expect([ring(M1), String(M1.domain), M1.gens, M1.shape, M1.rows, M1.cols, M1.length]).toEqual(['QQ[x,y]', 'QQ', [x, y], [1, 2], 1, 2, 2]);
  expect([...M1].map(String)).toEqual(["Poly(x, x, y, domain='QQ')", "Poly(y, x, y, domain='QQ')"]);
  const M2 = new PolyMatrix([[x, y]], { ring: new PolyMatrixRing(QQ.polyRing(x), y) });
  expect([ring(M2), String(M2.domain), M2.gens]).toEqual(['QQ[x][y]', 'QQ[x]', [y]]);
  expect(M2.flat().map(String)).toEqual(["Poly(x, y, domain='QQ[x]')", "Poly(y, y, domain='QQ[x]')"]);
  expect(ring(new PolyMatrix([[x, y]], y))).toBe('ZZ(x)[y]');
  expect(new PolyMatrix([[x, y]], { ring: 'ZZ[x,y]' }).equals(new PolyMatrix([[x, y]], { ring: ZZ.polyRing(x, y) }))).toBe(true);
  expect(ring(new PolyMatrix([[x, y]], { ring: 'QQ[x][y]' }))).toBe('QQ[x][y]');
  expect(new PolyMatrix([[x, y]], [x, y]).equals(new PolyMatrix([[x, y]], x, y))).toBe(true);
  expect(String(new PolyMatrix([x, y]))).toBe('PolyMatrix([\n[x],\n[y]], ring=QQ[x,y])');
  expect(new PolyMatrix(1, 2, [x, y]).equals(new PolyMatrix([[x, y]]))).toBe(true);
  expect(String(new PolyMatrix([[x, y]]))).toBe('PolyMatrix([[x, y]], ring=QQ[x,y])');
  expect(new PolyMatrix(1, 2, (_i, j) => [x, y][j] ?? 0).equals(new PolyMatrix([[x, y]]))).toBe(true);
  expect(new PolyMatrix(0, 2, [], x, y).shape).toEqual([0, 2]);
  expect(String(new PolyMatrix([[], []], x, y))).toBe('PolyMatrix(2, 0, [], ring=QQ[x,y])');
  expect(String(new PolyMatrix({ ring: QQ.polyRing(x, y) }))).toBe('PolyMatrix(0, 0, [], ring=QQ[x,y])');
  expect(new PolyMatrix([], { ring: 'QQ[x,y]' }).equals(new PolyMatrix({ ring: 'QQ[x,y]' }))).toBe(true);
  expect(String(new PolyMatrix(0, 2, [], x))).toBe('PolyMatrix(0, 2, [], ring=QQ[x])');
  expect(ring(new PolyMatrix([Poly.from(x), Poly.from(y)]))).toBe('ZZ[x,y]');
  expect(new PolyMatrix([Poly.from(y, [x]), 1]).equals(new PolyMatrix([[y], [1]], { ring: QQ.polyRing(y) }))).toBe(true);
  expect(() => new PolyMatrix()).toThrow(TypeError);
  expect(() => new PolyMatrix(1)).toThrow(TypeError);
  expect(() => new PolyMatrix([[1], [1, 2]], x)).toThrow(RangeError);
  expect(() => new PolyMatrix(1, 2, [x], x)).toThrow(RangeError);
  expect(() => new PolyMatrix([x, [y]] as never, x)).toThrow(TypeError);
  expect(() => new PolyMatrix([x], 1 as never)).toThrow(TypeError);
  expect(() => new PolyMatrix([p('1/2')], { ring: ZZ.polyRing(x) })).toThrow(CoercionFailed);
  expect(() => new PolyMatrix([x], { ring: 'QQ' })).toThrow(TypeError);
  expect(() => new PolyMatrix([x], { ring: QQ })).toThrow(TypeError);
  expect(() => new PolyMatrix([x], { ring: QQ.fracField(x) })).toThrow(TypeError);
});

it('converts from and to matrices and domain matrices', () => {
  expect(PolyMatrix.fromMatrix(Matrix.of([[1], [2]]), x).equals(new PolyMatrix([1, 2], x, { ring: 'QQ[x]' }))).toBe(true);
  expect(PolyMatrix.fromMatrix(Matrix.of([[1]]), { ring: 'QQ[x]' }).equals(new PolyMatrix([1], x))).toBe(true);
  const pmx = PolyMatrix.fromMatrix(Matrix.of([[1], [2]]), x);
  expect(pmx.setGens(y).equals(PolyMatrix.fromMatrix(Matrix.of([[1], [2]]), y))).toBe(true);
  expect(pmx.equals(pmx.setGens(y))).toBe(false);
  expect(PolyMatrix.fromDm(new DomainMatrix([[x, p('1')]], [1, 2], QQ.polyRing(x))).equals(new PolyMatrix([[x, 1]], x))).toBe(true);
  expect(() => PolyMatrix.fromDm(new DomainMatrix([[p('1')]], [1, 1], QQ))).toThrow(TypeError);
  expect(PolyMatrix.zeros(1, 2, x).equals(new PolyMatrix([[0, 0]], x))).toBe(true);
  expect(PolyMatrix.eye(2, [x]).equals(new PolyMatrix([[1, 0], [0, 1]], x))).toBe(true);
  expect(() => PolyMatrix.eye(2, p('sin(x)'))).toThrow(TypeError);
  expect(PolyMatrix.fromList(1, 1, [x], [], 'ZZ[x]').equals(new PolyMatrix([[x]], { ring: 'ZZ[x]' }))).toBe(true);
});

it('indexes, joins and maps entries', () => {
  const M = new PolyMatrix([[1, 2], [3, 4]], x);
  expect(M.extract([0, 1], [0, 1]).equals(M)).toBe(true);
  expect(M.extract([0], [0, 1]).equals(new PolyMatrix([[1, 2]], x))).toBe(true);
  expect(M.get(0, 0).equals(Poly.from(1, [x], { domain: 'QQ' }))).toBe(true);
  expect(M.get(-1, -1).asExpr().equals(4)).toBe(true);
  expect(M.get(1).asExpr().equals(2)).toBe(true);
  expect(M.get(-1).asExpr().equals(4)).toBe(true);
  expect(() => M.get(4)).toThrow(RangeError);
  expect(() => M.get(-5)).toThrow(RangeError);
  expect(() => M.get(0.5)).toThrow(RangeError);
  expect(() => M.get(2, 0)).toThrow(RangeError);
  expect(() => M.get(0, 2)).toThrow(RangeError);
  expect(() => M.get(-3, 0)).toThrow(RangeError);
  expect(() => M.get(0, -3)).toThrow(RangeError);
  expect(() => M.get(0.5, 0)).toThrow(RangeError);
  expect(() => M.get(0, 0.5)).toThrow(RangeError);
  const N = new PolyMatrix([[5, 6], [7, 8]], x);
  expect(M.rowJoin(N).equals(new PolyMatrix([[1, 2, 5, 6], [3, 4, 7, 8]], x))).toBe(true);
  expect(M.colJoin(N).equals(new PolyMatrix([[1, 2], [3, 4], [5, 6], [7, 8]], x))).toBe(true);
  expect(() => M.rowJoin(new PolyMatrix([1], x))).toThrow(RangeError);
  expect(() => M.colJoin(new PolyMatrix([1], x))).toThrow(RangeError);
  expect(M.applyfunc((e) => e.mul(2)).equals(new PolyMatrix([[2, 4], [6, 8]], x))).toBe(true);
});

it('computes rref, nullspace and rank over the coefficient field', () => {
  const M = new PolyMatrix([[1, 2], [3, 4]], x);
  const [R, pivots] = M.rref();
  expect(R.equals(PolyMatrix.eye(2, x))).toBe(true);
  expect(pivots).toEqual([0, 1]);
  expect(() => new PolyMatrix([1, 2], { ring: 'ZZ[x]' }).rref()).toThrow(RangeError);
  expect(() => new PolyMatrix([1, x], { ring: 'QQ[x]' }).rref()).toThrow(RangeError);
  const S2 = new PolyMatrix([[1, 2], [2, 4]], x);
  const [basis] = S2.nullspace();
  expect(basis?.equals(new PolyMatrix([-2, 1], x))).toBe(true);
  expect(S2.rank()).toBe(1);
  expect(() => new PolyMatrix([1, 2], { ring: 'ZZ[x]' }).nullspace()).toThrow(RangeError);
});

it('unifies and compares rings', () => {
  const R = PolyMatrixRing.of('QQ[x]');
  expect(PolyMatrixRing.of(R)).toBe(R);
  expect(R.unify(QQ.polyRing(y)).toString()).toBe('QQ[x,y]');
  expect(R.unify(new PolyMatrixRing(ZZ, [x, y])).toString()).toBe('QQ[x,y]');
  expect(R.unify(ZZ).toString()).toBe('QQ[x]');
  expect(R.unify(QQ.fracField(y)).toString()).toBe('QQ(y)[x]');
  expect(R.equals(PolyMatrixRing.of('QQ[x]'))).toBe(true);
  expect(R.equals('QQ[x]')).toBe(false);
  expect(() => PolyMatrixRing.of('QQ')).toThrow(TypeError);
});
