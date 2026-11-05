// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/dense.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import type { Expr, ExprLike } from '../../../src/core';
import { Float, Rational } from '../../../src/core';
import { QQ, RR, ZZ } from '../../../src/polys/domains';
import { ddmBerk, ddmIadd, ddmIdet, ddmIinv, ddmIlu, ddmIluSolve, ddmIluSplit, ddmImatmul, ddmImul, ddmIneg, ddmIrmul, ddmIrref, ddmIrrefDen, ddmIsub, ddmTranspose, opsOf, usePartialPivot } from '../../../src/polys/matrices/dense';
import { DMDomainError, DMNonInvertibleMatrixError, DMNonSquareMatrixError, DMShapeError } from '../../../src/polys/matrices/exceptions';

const s = (v: unknown): string => (Array.isArray(v) ? `[${v.map(s).join(', ')}]` : String(v));
const m = (): ExprLike[][] => [[1, 2], [3, 4]];

describe('dense', () => {
  it('in-place arithmetic with and without a domain', () => {
    const a = m();
    ddmIadd(a, [[1, 1], [1, 1]], QQ);
    expect(s(a)).toBe('[[2, 3], [4, 5]]');
    ddmIsub(a, [[1, 1], [1, 1]]);
    expect(s(a)).toBe('[[1, 2], [3, 4]]');
    ddmIneg(a);
    ddmImul(a, 2);
    ddmIrmul(a, -1, ZZ);
    expect(s(a)).toBe('[[2, 4], [6, 8]]');
    const r: ExprLike[][] = [[0, 0], [0, 0]];
    ddmImatmul(r, m(), [[-2, 1], [Rational.of(3n, 2n), Rational.of(-1n, 2n)]]);
    expect(s(r)).toBe('[[1, 0], [0, 1]]');
    expect(s(ddmTranspose([[1, 2, 3]]))).toBe('[[1], [2], [3]]');
    expect(ddmTranspose([])).toEqual([]);
    expect(opsOf().isZero(new Float(0))).toBe(true);
    expect([usePartialPivot(RR), usePartialPivot(QQ)]).toEqual([true, false]);
  });
  it('elimination, determinant and inverse', () => {
    const a: ExprLike[][] = [[0, 1], [0, 2]];
    expect(ddmIrref(a)).toEqual([1]);
    expect(s(a)).toBe('[[0, 1], [0, 0]]');
    expect(ddmIrref([])).toEqual([]);
    const f: ExprLike[][] = [[1, new Float(2)], [new Float(3), 4]];
    expect(ddmIrref(f, true, RR)).toEqual([0, 1]);
    const b: ExprLike[][] = [[0, 1, 2], [0, 2, 5]];
    expect(s(ddmIrrefDen(b, ZZ))).toBe('[1, [1, 2]]');
    expect(s(b)).toBe('[[0, 1, 0], [0, 0, 1]]');
    expect(s(ddmIrrefDen([], ZZ))).toBe('[1, []]');
    expect(s(ddmIrrefDen([[0, 0]], ZZ))).toBe('[1, []]');
    expect(s(ddmIrrefDen([[2, 1, 3], [4, 2, 7]], ZZ))).toBe(s([2, [0, 2]]));
    expect(s(ddmIdet([[0, 1], [1, 0]], ZZ))).toBe('-1');
    expect(s(ddmIdet([[0, 1], [0, 2]], ZZ))).toBe('0');
    expect(s(ddmIdet([], ZZ))).toBe('1');
    expect(s(ddmIdet([[1, 2, 3], [4, 5, 6], [7, 8, 9]], ZZ))).toBe('0');
    const inv: ExprLike[][] = [];
    ddmIinv(inv, m(), QQ);
    expect(s(inv)).toBe('[[-2, 1], [3/2, -1/2]]');
    ddmIinv(inv, [], QQ);
    expect(() => ddmIinv(inv, m(), ZZ)).toThrow(DMDomainError);
    expect(() => ddmIinv(inv, [[1, 2]], QQ)).toThrow(DMNonSquareMatrixError);
    expect(() => ddmIinv(inv, [[1, 2], [2, 4]], QQ)).toThrow(DMNonInvertibleMatrixError);
    expect(() => ddmIinv(inv, [[0, 1], [0, 0]], QQ)).toThrow(DMNonInvertibleMatrixError);
  });
  it('LU decomposition and solving', () => {
    const a: ExprLike[][] = [[0, 2], [1, 4]];
    expect(ddmIlu(a, QQ)).toEqual([[0, 1]]);
    expect(s(a)).toBe('[[1, 4], [0, 2]]');
    const z: ExprLike[][] = [[0, 0], [0, 4]];
    expect(ddmIlu(z)).toEqual([]);
    expect(ddmIlu([])).toEqual([]);
    expect(ddmIluSplit([], [], QQ)).toEqual([]);
    const L: ExprLike[][] = [[1, 0], [0, 1]];
    const U = m();
    ddmIluSplit(L, U, QQ);
    expect([s(L), s(U)]).toEqual(['[[1, 0], [3, 1]]', '[[1, 2], [0, -2]]']);
    const x: unknown[][] = [[null], [null]];
    ddmIluSolve(x, L, U, [[0, 1]], [[5], [6]], QQ);
    expect(s(x)).toBe('[[-7], [13/2]]');
    ddmIluSolve([], [], [], [], [[1]]);
    expect(() => ddmIluSolve(x, L, U, [], [])).toThrow(DMShapeError);
    expect(() => ddmIluSolve(x, L, U, [], [[1]])).toThrow(DMShapeError);
    expect(() => ddmIluSolve(x, [[1]], [[1, 2]], [], [[1]])).toThrow(DMShapeError);
    expect(() => ddmIluSolve(x, [[1, 0], [0, 1]], [[1, 2], [0, 0]], [], [[1], [1]])).toThrow(DMNonInvertibleMatrixError);
    expect(() => ddmIluSolve(x, [[1, 0, 0], [0, 1, 0], [0, 0, 1]], [[1, 2], [0, 1], [0, 0]], [], [[1], [1], [1]])).toThrow(DMNonInvertibleMatrixError);
    const y: unknown[][] = [[null], [null]];
    ddmIluSolve(y, [[1, 0, 0], [0, 1, 0], [0, 0, 1]], [[1, 2], [0, 1], [0, 0]], [], [[1], [1], [0]]);
    expect(s(y)).toBe('[[-1], [1]]');
  });
  it('Berkowitz', () => {
    expect(s(ddmBerk([[1, 2, 3], [4, 5, 6], [7, 8, 10]], ZZ))).toBe('[[1], [-16], [-12], [3]]');
    expect(s(ddmBerk([], ZZ))).toBe('[[1]]');
    expect(() => ddmBerk([[1, 2]], ZZ)).toThrow(DMShapeError);
    const e: Expr[] = ddmBerk([[2]], ZZ).flat();
    expect(s(e)).toBe('[1, -2]');
  });
  it('covers pivoting branches', () => {
    const r: ExprLike[][] = [[0, new Float(1)], [new Float(3), new Float(2)]];
    expect(ddmIrref(r, true, RR)).toEqual([0, 1]);
    const t: ExprLike[][] = [[new Float(3), new Float(1)], [new Float(1), new Float(2)]];
    expect(ddmIrref(t, true, RR)).toEqual([0, 1]);
    expect(s(ddmIrrefDen([[0, 1], [2, 3]], ZZ))).toBe('[2, [0, 1]]');
  });
});
