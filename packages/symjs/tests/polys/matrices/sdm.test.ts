// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/sdm.ts. Expected values are those of SymPy 1.14
// (dicts compared after sorting, as their order is an implementation detail).

import { describe, expect, it } from 'vitest';
import { Float, Rational } from '../../../src/core';
import type { Domain } from '../../../src/polys/domains';
import { QQ, RR, ZZ } from '../../../src/polys/domains';
import { SDM, sdmBerk } from '../../../src/polys/matrices/sdm';
import { DDM } from '../../../src/polys/matrices/ddm';
import { DMBadInputError, DMDomainError, DMShapeError } from '../../../src/polys/matrices/exceptions';

const q = (p: number, d = 1) => Rational.of(BigInt(p), BigInt(d));
const s = (v: unknown): string => (Array.isArray(v) ? `[${v.map(s).join(', ')}]` : v instanceof Map ? `{${[...v].sort(([a], [b]) => a - b).map(([k, w]) => `${k}: ${s(w)}`).join(', ')}}` : String(v));
const S = (d: Record<number, Record<number, number>>, shape: [number, number], K: Domain = QQ) =>
  new SDM(new Map(Object.entries(d).map(([i, r]) => [Number(i), new Map(Object.entries(r).map(([j, e]) => [Number(j), q(e)] as const))] as const)), shape, K);
const ss = (m: SDM): string => s(m.data);
const A = () => S({ 0: { 1: 2 }, 1: { 0: 1 } }, [2, 2]);

describe('SDM', () => {
  it('constructs, prints and converts', () => {
    expect(A().repr()).toBe('SDM({0: {1: MPQ(2,1)}, 1: {0: MPQ(1,1)}}, (2, 2), QQ)');
    expect(String(A())).toBe('{0: {1: 2}, 1: {0: 1}}');
    expect(() => S({ 3: { 0: 1 } }, [2, 2])).toThrow(DMBadInputError);
    expect(() => S({ 0: { 3: 1 } }, [2, 2])).toThrow(DMBadInputError);
    expect(String(SDM.new(new Map(), [1, 1], ZZ))).toBe('{}');
    expect(() => SDM.fromList([[q(1)]], [1, 2], ZZ)).toThrow(DMBadInputError);
    expect(s(A().toListFlat())).toBe('[0, 2, 1, 0]');
    expect(ss(SDM.fromListFlat([q(0), q(2), q(1), q(0)], [2, 2], QQ))).toBe(ss(A()));
    expect(() => SDM.fromListFlat([q(1)], [2, 2], QQ)).toThrow(DMBadInputError);
    const [els, data] = A().toFlatNz();
    expect(ss(SDM.fromFlatNz(els, data, QQ))).toBe(ss(A()));
    expect(ss(SDM.fromDod(new Map([[0, new Map([[0, q(0)], [1, q(3)]])]]), [1, 2], QQ))).toBe('{0: {1: 3}}');
    expect(ss(SDM.fromDok(new Map([[[0, 0] as const, q(0)], [[0, 1] as const, q(3)], [[0, 0] as const, q(1)]]), [1, 2], QQ))).toBe('{0: {0: 1, 1: 3}}');
    expect(s(A().iterValues())).toBe('[2, 1]');
    expect(A().iterItems().length).toBe(2);
    expect(A().toSdm().toDfmOrDdm()).toBeInstanceOf(DDM);
    expect(ss(SDM.ones([1, 2], ZZ))).toBe('{0: {0: 1, 1: 1}}');
    expect(ss(SDM.eye(2, ZZ))).toBe('{0: {0: 1}, 1: {1: 1}}');
    expect(ss(SDM.diag([q(1), q(0)], ZZ, [2, 3]))).toBe('{0: {0: 1}}');
    expect(ss(A().convertTo(ZZ))).toBe(ss(A()));
    expect(ss(A().convertTo(QQ))).toBe(ss(A()));
    expect(ss(A().applyfunc((e) => e, ZZ))).toBe(ss(A()));
    expect([A().equals(A()), A().equals(A().neg()), A().equals(1), A().equals(S({ 0: { 1: 2 } }, [2, 2]))]).toEqual([true, false, false, false]);
  });
  it('indexes and extracts', () => {
    const a = A();
    expect(String(a.getitem(-2, -1))).toBe('2');
    expect(String(a.getitem(0, 0))).toBe('0');
    expect(() => a.getitem(2, 0)).toThrow(RangeError);
    a.setitem(0, 0, q(5));
    a.setitem(1, 1, q(6));
    a.setitem(1, -2, q(0));
    a.setitem(1, 1, q(0));
    a.setitem(0, 0, q(0));
    expect(ss(a)).toBe('{0: {1: 2}}');
    expect(() => a.setitem(5, 0, q(1))).toThrow(RangeError);
    expect(ss(A().extractSlice([0, 1], [null, null]))).toBe('{0: {1: 2}}');
    expect(ss(A().extract([0, 0, -1], [1, -1]))).toBe('{0: {0: 2, 1: 2}, 1: {0: 2, 1: 2}}');
    expect(ss(A().extract([], [0]))).toBe('{}');
    expect(() => A().extract([5], [0])).toThrow(RangeError);
    expect(() => A().extract([0], [5])).toThrow(RangeError);
    expect(s(A().diagonal())).toBe('[0, 0]');
    expect([A().isZeroMatrix(), A().isUpper(), A().isLower(), A().isDiagonal(), SDM.eye(2, ZZ).isDiagonal()]).toEqual([false, false, false, false, true]);
    expect(SDM.eye(2, ZZ).isUpper() && SDM.eye(2, ZZ).isLower()).toBe(true);
  });
  it('does arithmetic', () => {
    const a = A();
    const b = S({ 0: { 0: 3, 1: -2 }, 1: { 1: 4 } }, [2, 2]);
    expect(ss(a.add(b))).toBe('{0: {0: 3}, 1: {0: 1, 1: 4}}');
    expect(ss(a.sub(b))).toBe('{0: {0: -3, 1: 4}, 1: {0: 1, 1: -4}}');
    expect(ss(S({ 1: { 0: 1 } }, [2, 2]).sub(S({ 0: { 0: 1 } }, [2, 2])))).toBe('{0: {0: -1}, 1: {0: 1}}');
    expect(ss(a.neg())).toBe('{0: {1: -2}, 1: {0: -1}}');
    expect(ss(a.mul(q(3)))).toBe('{0: {1: 6}, 1: {0: 3}}');
    expect(ss(a.rmul(q(3)))).toBe('{0: {1: 6}, 1: {0: 3}}');
    expect(ss(a.matmul(b))).toBe('{0: {1: 8}, 1: {0: 3, 1: -2}}');
    expect(ss(S({ 0: { 0: 1, 1: 1 } }, [1, 2]).matmul(S({ 0: { 0: 1 }, 1: { 0: -1 } }, [2, 1])))).toBe('{}');
    expect(() => a.matmul(S({}, [2, 2], ZZ))).toThrow(DMDomainError);
    expect(() => a.matmul(S({}, [3, 2]))).toThrow(DMShapeError);
    expect(ss(a.mulElementwise(b))).toBe('{0: {1: -4}}');
    expect(() => a.mulElementwise(S({}, [2, 2], ZZ))).toThrow(DMDomainError);
    expect(() => a.mulElementwise(S({}, [3, 2]))).toThrow(DMShapeError);
    expect(ss(a.transpose())).toBe('{0: {1: 1}, 1: {0: 2}}');
    expect(ss(a.hstack(b))).toBe('{0: {1: 2, 2: 3, 3: -2}, 1: {0: 1, 3: 4}}');
    expect(ss(S({}, [2, 1]).hstack(b))).toBe('{0: {1: 3, 2: -2}, 1: {2: 4}}');
    expect(ss(a.vstack(b))).toBe('{0: {1: 2}, 1: {0: 1}, 2: {0: 3, 1: -2}, 3: {1: 4}}');
    expect(() => a.hstack(S({}, [3, 2]))).toThrow(DMShapeError);
    expect(() => a.vstack(S({}, [2, 2], ZZ))).toThrow(DMDomainError);
    expect(a.nnz()).toBe(2);
    expect(a.scc()).toEqual([[0, 1]]);
  });
  it('does linear algebra', () => {
    const a = A();
    expect(ss(a.rref()[0])).toBe('{0: {0: 1}, 1: {1: 1}}');
    expect(a.rrefDen().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: 2}, 1: {1: 2}}', '2', '0,1']);
    expect(String(a.nullspace()[0].shape)).toBe('0,2');
    expect(ss(a.inv())).toBe('{0: {1: 1}, 1: {0: 1/2}}');
    expect(String(a.det())).toBe('-2');
    expect(a.lu().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: 1}, 1: {1: 1}}', '{0: {0: 1}, 1: {1: 2}}', '0,1']);
    expect(a.qr().map(ss)).toEqual(['{0: {1: 2}, 1: {0: 1}}', '{0: {0: 1}, 1: {1: 1}}']);
    expect(a.fflu().map(ss)).toEqual(['{0: {1: 1}, 1: {0: 1}}', '{0: {0: 1}, 1: {1: 2}}', '{0: {0: 1}, 1: {1: 2}}', '{0: {0: 1}, 1: {1: 2}}']);
    expect(ss(a.luSolve(S({ 0: { 0: 1 } }, [2, 1])))).toBe('{1: {0: 1/2}}');
    expect(ss(S({ 0: { 0: 1, 2: 3 }, 1: { 1: 1, 2: 4 } }, [2, 3]).particular())).toBe('{0: {0: 3, 1: 4}}');
    expect(ss(S({ 0: { 0: 1 } }, [1, 2]).particular())).toBe('{}');
    expect(s(a.charpoly())).toBe('[1, 0, -2]');
    expect(ss(S({ 0: { 0: 1, 1: 1 }, 1: { 0: 1, 1: 1 } }, [2, 2]).rref()[0])).toBe('{0: {0: 1, 1: 1}}');
    expect(ss(S({ 0: { 0: 1, 1: 2, 2: 1 }, 1: { 1: 1, 2: 1 }, 2: { 0: 1, 2: 5 } }, [3, 3]).rref()[0])).toBe('{0: {0: 1}, 1: {1: 1}, 2: {2: 1}}');
    const N = S({ 0: { 0: 1, 1: 2, 2: 3 }, 1: { 0: 2, 1: 4, 2: 6 } }, [2, 3]);
    expect(N.nullspace().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: -2, 1: 1}, 1: {0: -3, 2: 1}}', '1,2']);
    expect(ss(N.rref()[0].nullspaceFromRref()[0])).toBe('{0: {0: -2, 1: 1}, 1: {0: -3, 2: 1}}');
    expect(ss(S({}, [1, 2]).nullspaceFromRref()[0])).toBe('{0: {0: 1}, 1: {1: 1}}');
    expect(String(SDM.eye(2, QQ).nullspaceFromRref()[0].shape)).toBe('0,2');
    const T = S({ 0: { 0: 2, 1: 4 }, 1: { 0: 1, 1: 3 }, 2: { 0: 1, 1: 2 } }, [3, 2], ZZ);
    expect(T.rrefDen().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: 2}, 1: {1: 2}}', '2', '0,1']);
    const U = S({ 0: { 0: 1, 1: 2, 2: 3 }, 1: { 0: 2, 1: 4, 2: 7 }, 2: { 1: 1 } }, [3, 3], ZZ);
    expect(U.rrefDen().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: 1}, 1: {1: 1}, 2: {2: 1}}', '1', '0,1,2']);
    expect(S({}, [1, 1]).rrefDen().map(String)).toEqual(['{}', '1', '']);
    expect(S({ 0: { 1: 3 } }, [1, 2]).rrefDen().map(String)).toEqual(['{0: {1: 3}}', '3', '1']);
    expect(S({ 0: { 0: 1, 1: 1 }, 1: { 0: 1, 1: 1 } }, [2, 2], ZZ).rrefDen().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: 1, 1: 1}}', '1', '0']);
    expect(S({ 0: { 0: 2, 1: 1 }, 1: { 0: 4, 1: 3 } }, [2, 2]).rrefDen().map((v) => (v instanceof SDM ? ss(v) : String(v)))).toEqual(['{0: {0: 2}, 1: {1: 2}}', '2', '0,1']);
  });
  it('sdm_berk', () => {
    const m = (d: Record<number, Record<number, number>>) => S(d, [3, 3], ZZ).data;
    expect(s(sdmBerk(m({ 0: { 0: 1, 2: 2 }, 1: { 1: 3 }, 2: { 0: 4, 2: 5 } }), 3, ZZ))).toBe('{0: 1, 1: -9, 2: 15, 3: 9}');
    expect(s(sdmBerk(new Map(), 1, ZZ))).toBe('{0: 1}');
    expect(s(sdmBerk(new Map([[0, new Map([[0, 2]])]]), 1, ZZ))).toBe('{0: 1, 1: -2}');
    expect(s(sdmBerk(m({ 1: { 0: 1 }, 2: { 1: 1 } }), 3, ZZ))).toBe('{0: 1}');
    expect(s(sdmBerk(new Map(), 0, ZZ))).toBe('{0: 1}');
  });
  it('covers the sparse elimination branches', () => {
    const dense = (m: SDM) => String(m.toDdm());
    const cases: [number[][], string, string, string, string][] = [
      [[[0, 1, 2, 3], [1, 0, 1, 0], [1, 1, 0, 1], [2, 3, 1, 0]], '[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]', '0,1,2,3', '[[13, 0, 0, 0], [0, 13, 0, 0], [0, 0, 13, 0], [0, 0, 0, 13]]', '13'],
      [[[1, 2, 0, 1], [0, 0, 1, 1], [1, 2, 1, 0], [0, 0, 0, 1]], '[[1, 2, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 0, 0]]', '0,2,3', '[[2, 4, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2], [0, 0, 0, 0]]', '2'],
      [[[0, 0, 1], [0, 1, 1], [1, 1, 1]], '[[1, 0, 0], [0, 1, 0], [0, 0, 1]]', '0,1,2', '[[1, 0, 0], [0, 1, 0], [0, 0, 1]]', '1'],
      [[[1, 1, 0], [1, 1, 1], [0, 1, 1]], '[[1, 0, 0], [0, 1, 0], [0, 0, 1]]', '0,1,2', '[[1, 0, 0], [0, 1, 0], [0, 0, 1]]', '1'],
      [[[2, 0, 1, 0], [0, 0, 1, 3], [4, 0, 3, 3]], '[[1, 0, 0, -3/2], [0, 0, 1, 3], [0, 0, 0, 0]]', '0,2', '[[2, 0, 0, -3], [0, 0, 2, 6], [0, 0, 0, 0]]', '2'],
      [[[0, 2, 2, 0, 1], [2, -1, 2, 0, 2], [0, -1, 1, 2, 0], [0, -1, 2, 2, -1]], '[[1, 0, 0, 0, 11/4], [0, 1, 0, 0, 3/2], [0, 0, 1, 0, -1], [0, 0, 0, 1, 5/4]]', '0,1,2,3', '[[-8, 0, 0, 0, -22], [0, -8, 0, 0, -12], [0, 0, -8, 0, 8], [0, 0, 0, -8, -10]]', '-8'],
      [[[-1, 0, 0, 0, 2], [-1, 0, 0, 0, 2], [0, 1, 0, 1, -1], [2, -1, -1, -1, 2]], '[[1, 0, 0, 0, -2], [0, 1, 0, 1, -1], [0, 0, 1, 0, -5], [0, 0, 0, 0, 0]]', '0,1,2', '[[-1, 0, 0, 0, 2], [0, -1, 0, -1, 1], [0, 0, -1, 0, 5], [0, 0, 0, 0, 0]]', '-1'],
      [[[-1, 0, 1, 0, 0], [0, -1, 0, 1, -1], [1, -1, 2, -1, 2], [1, 2, 2, -1, 2]], '[[1, 0, 0, 0, 1/3], [0, 1, 0, 0, 0], [0, 0, 1, 0, 1/3], [0, 0, 0, 1, -1]]', '0,1,2,3', '[[9, 0, 0, 0, 3], [0, 9, 0, 0, 0], [0, 0, 9, 0, 3], [0, 0, 0, 9, -9]]', '9'],
      [[[0, 1, 0, 1, 2], [0, 1, 2, 2, 2], [0, 0, 2, 1, 1], [0, 0, -1, -1, 0]], '[[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]', '1,2,3,4', '[[0, -1, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, -1, 0], [0, 0, 0, 0, -1]]', '-1'],
      [[[1, 0, -1, 0, 0], [1, -1, -1, 0, 0], [2, 2, 0, -1, 2], [1, 2, 1, 2, 0]], '[[1, 0, 0, 0, 2/3], [0, 1, 0, 0, 0], [0, 0, 1, 0, 2/3], [0, 0, 0, 1, -2/3]]', '0,1,2,3', '[[-6, 0, 0, 0, -4], [0, -6, 0, 0, 0], [0, 0, -6, 0, -4], [0, 0, 0, -6, 4]]', '-6'],
      [[[0, 1, 0, 0, 0], [2, 2, 0, 0, -1], [1, 2, 1, 0, 0], [1, 1, 1, 0, -1]], '[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1]]', '0,1,2,4', '[[-2, 0, 0, 0, 0], [0, -2, 0, 0, 0], [0, 0, -2, 0, 0], [0, 0, 0, 0, -2]]', '-2'],
      [[[-1, -1, 2, -1, 2], [2, 0, 2, 2, 1], [-1, 0, 1, -1, 1], [2, 1, 2, 1, 0]], '[[1, 0, 0, 0, -1], [0, 1, 0, 0, -1/4], [0, 0, 1, 0, 3/4], [0, 0, 0, 1, 3/4]]', '0,1,2,3', '[[-4, 0, 0, 0, 4], [0, -4, 0, 0, 1], [0, 0, -4, 0, -3], [0, 0, 0, -4, -3]]', '-4'],
      [[[-1, 2, 1, 0, -1], [2, 2, 0, 0, 1], [-1, 1, 1, 2, 1], [-1, 0, 2, 0, 0]], '[[1, 0, 0, 0, 4/5], [0, 1, 0, 0, -3/10], [0, 0, 1, 0, 2/5], [0, 0, 0, 1, 17/20]]', '0,1,2,3', '[[20, 0, 0, 0, 16], [0, 20, 0, 0, -6], [0, 0, 20, 0, 8], [0, 0, 0, 20, 17]]', '20'],
    ];
    for (const [m, r, p, rd, d] of cases) {
      const shape: [number, number] = [m.length, m[0]?.length ?? 0];
      const dict = (K: Domain) => SDM.fromList(m.map((row) => row.map((e) => q(e))), shape, K);
      const [R, P] = dict(QQ).rref();
      expect([dense(R), String(P)]).toEqual([r, p]);
      const [RD, D, PD] = dict(ZZ).rrefDen();
      expect([dense(RD), String(D), String(PD)]).toEqual([rd, d, p]);
    }
    expect(ss(S({ 0: { 0: 2, 1: 1 }, 1: { 1: 2 } }, [2, 3]).nullspace()[0])).toBe('{0: {2: 1}}');
    expect(ss(S({ 0: { 0: 1 } }, [1, 3]).nullspaceFromRref([0])[0])).toBe('{0: {1: 1}, 1: {2: 1}}');
    const a = S({}, [2, 2]);
    a.setitem(1, 1, q(3));
    expect(ss(a)).toBe('{1: {1: 3}}');
    expect(ss(S({ 0: { 0: 1, 2: 2 }, 1: { 2: 3 } }, [2, 3]).extractSlice([null, null], [0, 2]))).toBe('{0: {0: 1}}');
    expect(ss(A().sub(A()))).toBe('{}');
    expect(ss(S({ 1: { 0: 1 } }, [2, 2]).mulElementwise(S({ 0: { 0: 1 } }, [2, 2])))).toBe('{}');
    expect(ss(A().mul(q(0)))).toBe('{}');
    expect(ss(S({ 0: { 0: 1 }, 1: { 0: 1 } }, [2, 1]).transpose())).toBe('{0: {0: 1, 1: 1}}');
    expect(ss(S({ 0: { 1: 1 } }, [1, 2]).matmul(S({ 0: { 0: 1 } }, [2, 1])))).toBe('{}');
    expect(s(sdmBerk(S({ 1: { 0: 1 } }, [3, 3], ZZ).data, 3, ZZ))).toBe('{0: 1}');
    const [RR0, d0] = new SDM(new Map([[0, new Map([[0, new Float(1)], [1, new Float(2)]])], [1, new Map([[1, new Float(4)]])]]), [2, 2], RR).rrefDen();
    expect([RR0.nnz(), (d0 as Float).value]).toEqual([2, 4]);
  });
});
