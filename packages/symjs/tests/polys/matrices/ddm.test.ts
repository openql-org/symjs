// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/ddm.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational } from '../../../src/core';
import { QQ, ZZ } from '../../../src/polys/domains';
import { DDM, sliceIndices } from '../../../src/polys/matrices/ddm';
import '../../../src/polys/matrices/sdm';
import { DMBadInputError, DMDomainError, DMNonSquareMatrixError, DMShapeError } from '../../../src/polys/matrices/exceptions';

const q = (p: number, d = 1) => Rational.of(BigInt(p), BigInt(d));
const s = (v: unknown): string => (Array.isArray(v) ? `[${v.map(s).join(', ')}]` : String(v));
const A = () => new DDM([[q(1), q(2)], [q(3), q(4)]], [2, 2], QQ);
const Z = () => new DDM([[q(0), q(1)], [q(0), q(0)]], [2, 2], ZZ);

describe('DDM', () => {
  it('constructs, prints and converts', () => {
    expect(A().repr()).toBe('DDM([[MPQ(1,1), MPQ(2,1)], [MPQ(3,1), MPQ(4,1)]], (2, 2), QQ)');
    expect(String(A())).toBe('[[1, 2], [3, 4]]');
    expect(() => new DDM([[q(1)]], [1, 2], ZZ)).toThrow(DMBadInputError);
    expect(String(DDM.fromList([[q(1)]], [1, 1], ZZ))).toBe('[[1]]');
    expect(DDM.fromDdm(A()).equals(A())).toBe(true);
    expect(String(DDM.fromListFlat([q(1), q(2)], [2, 1], ZZ))).toBe('[[1], [2]]');
    expect(() => DDM.fromListFlat([q(1)], [2, 1], ZZ)).toThrow(DMBadInputError);
    expect(s(A().flat())).toBe('[1, 2, 3, 4]');
    const [els, data] = Z().toFlatNz();
    expect(String(DDM.fromFlatNz(els, data, ZZ))).toBe('[[0, 1], [0, 0]]');
    expect(String(DDM.fromDod(Z().toDod(), [2, 2], ZZ))).toBe('[[0, 1], [0, 0]]');
    expect(String(DDM.fromDok(Z().toDok(), [2, 2], ZZ))).toBe('[[0, 1], [0, 0]]');
    expect(s(Z().iterValues())).toBe('[1]');
    expect(Z().iterItems().length).toBe(1);
    expect(Z().toDdm().toDfmOrDdm().rows).toBe(2);
    expect(String(Z().toSdm())).toBe('{0: {1: 1}}');
    expect(String(Z().convertTo(QQ).domain)).toBe('QQ');
    expect(Z().convertTo(ZZ).equals(Z())).toBe(true);
    expect([A().equals(Z()), A().equals(1), A().equals(A().extract([0], [0, 1]))]).toEqual([false, false, false]);
    expect(String(DDM.ones([1, 2], ZZ))).toBe('[[1, 1]]');
    expect(String(DDM.eye([2, 3], ZZ))).toBe('[[1, 0, 0], [0, 1, 0]]');
    expect(String(DDM.eye(1, ZZ))).toBe('[[1]]');
    expect(String(DDM.diag([q(1), q(2)], ZZ))).toBe('[[1, 0], [0, 2]]');
    expect(String(new DDM([], [0, 2], ZZ).transpose().shape)).toBe('2,0');
    expect(sliceIndices([-1, null], 3)).toEqual([2]);
    expect(sliceIndices([2, 1], 3)).toEqual([]);
  });
  it('indexes and does arithmetic', () => {
    const a = A();
    expect(String(a.getitem(-1, -1))).toBe('4');
    a.setitem(0, -1, q(5));
    expect(String(a)).toBe('[[1, 5], [3, 4]]');
    expect(String(A().extractSlice([1, null], [null, 1]))).toBe('[[3]]');
    expect(String(A().transpose())).toBe('[[1, 3], [2, 4]]');
    expect(String(A().add(A()))).toBe('[[2, 4], [6, 8]]');
    expect(String(A().sub(A()))).toBe('[[0, 0], [0, 0]]');
    expect(() => A().add(Z())).toThrow(DMDomainError);
    expect(() => A().add(A().extract([0], [0, 1]))).toThrow(DMShapeError);
    expect(String(A().neg())).toBe('[[-1, -2], [-3, -4]]');
    expect(String(A().mul(q(2)))).toBe('[[2, 4], [6, 8]]');
    expect(String(A().rmul(q(2)))).toBe('[[2, 4], [6, 8]]');
    expect(String(A().matmul(A()))).toBe('[[7, 10], [15, 22]]');
    expect(String(A().mulElementwise(A()))).toBe('[[1, 4], [9, 16]]');
    expect(String(A().hstack(A()))).toBe('[[1, 2, 1, 2], [3, 4, 3, 4]]');
    expect(String(A().vstack(A()))).toBe('[[1, 2], [3, 4], [1, 2], [3, 4]]');
    expect(String(A().applyfunc((e) => e, ZZ).domain)).toBe('ZZ');
    expect(A().nnz()).toBe(4);
    expect(Z().scc()).toEqual([[1], [0]]);
    expect([Z().isZeroMatrix(), Z().isUpper(), Z().isLower(), Z().isDiagonal(), DDM.zeros([1, 1], ZZ).isZeroMatrix()]).toEqual([false, true, false, false, true]);
    expect(s(new DDM([[q(1), q(2), q(3)]], [1, 3], ZZ).diagonal())).toBe('[1]');
  });
  it('does linear algebra', () => {
    const a = A();
    expect(a.rref().map(String)).toEqual(['[[1, 0], [0, 1]]', '0,1']);
    expect(a.rrefDen().map(String)).toEqual(['[[-2, 0], [0, -2]]', '-2', '0,1']);
    expect(a.nullspace()[0].shape).toEqual([0, 2]);
    expect(String(a.inv())).toBe('[[-2, 1], [3/2, -1/2]]');
    expect(() => new DDM([[q(1), q(2)]], [1, 2], QQ).inv()).toThrow(DMNonSquareMatrixError);
    expect(() => new DDM([[q(1), q(2)]], [1, 2], QQ).det()).toThrow(DMNonSquareMatrixError);
    expect(() => new DDM([[q(1), q(2)]], [1, 2], QQ).charpoly()).toThrow(DMNonSquareMatrixError);
    expect(a.lu().map(String)).toEqual(['[[1, 0], [3, 1]]', '[[1, 2], [0, -2]]', '']);
    expect(String(a.det())).toBe('-2');
    expect(s(a.charpoly())).toBe('[1, -5, -2]');
    expect(a.qr().map(String)).toEqual(['[[1, 3/5], [3, -1/5]]', '[[1, 7/5], [0, 1]]']);
    expect(() => Z().qr()).toThrow(DMDomainError);
    expect(a.fflu().map(String)).toEqual(['[[1, 0], [0, 1]]', '[[1, 0], [3, -2]]', '[[1, 0], [0, -2]]', '[[1, 2], [0, -2]]']);
    expect(Z().fflu().map(String)).toEqual(['[[1, 0], [0, 1]]', '[[1, 0], [0, 1]]', '[[1, 0], [0, 1]]', '[[0, 1], [0, 0]]']);
    expect(new DDM([[q(0), q(1)], [q(1), q(0)]], [2, 2], ZZ).fflu().map(String)[0]).toBe('[[0, 1], [1, 0]]');
    expect(Z().nullspaceFromRref().map(String)).toEqual(['[[1, 0]]', '0']);
    expect(DDM.zeros([1, 2], ZZ).nullspaceFromRref().map(String)).toEqual(['[[1, 0], [0, 1]]', '0,1']);
    const P = new DDM([[q(1), q(2), q(3)], [q(0), q(0), q(0)]], [2, 3], QQ);
    expect(String(P.particular())).toBe('[[3, 0]]');
    expect(P.nullspace().map(String)).toEqual(['[[-2, 1, 0], [-3, 0, 1]]', '1,2']);
    expect(String(a.luSolve(new DDM([[q(1)], [q(2)]], [2, 1], QQ)))).toBe('[[0], [1/2]]');
    expect(() => Z().luSolve(Z())).toThrow(DMDomainError);
    expect(() => a.luSolve(new DDM([[q(1)]], [1, 1], QQ))).toThrow(DMShapeError);
  });
  it('covers the remaining branches of fflu and qr', () => {
    const M = new DDM([[q(1), q(2), q(3)], [q(4), q(5), q(6)], [q(7), q(8), q(10)]], [3, 3], ZZ);
    expect(M.fflu().map(String)).toEqual(['[[1, 0, 0], [0, 1, 0], [0, 0, 1]]', '[[1, 0, 0], [4, -3, 0], [7, -6, -3]]', '[[1, 0, 0], [0, -3, 0], [0, 0, 9]]', '[[1, 2, 3], [0, -3, -6], [0, 0, -3]]']);
    expect(new DDM([], [0, 0], ZZ).fflu().map(String)).toEqual(['[]', '[]', '[]', '[]']);
    expect(new DDM([[q(0), q(1)], [q(0), q(1)]], [2, 2], QQ).qr().map(String)).toEqual(['[[0, 1], [0, 1]]', '[[0, 0], [0, 1]]']);
    expect(new DDM([[q(1), q(0)], [q(1), q(0)]], [2, 2], QQ).qr().map(String)).toEqual(['[[1, 0], [1, 0]]', '[[1, 0], [0, 0]]']);
    expect(new DDM([[q(1), q(2)]], [1, 2], QQ).qr().map(String)).toEqual(['[[1]]', '[[1, 2]]']);
  });
});
