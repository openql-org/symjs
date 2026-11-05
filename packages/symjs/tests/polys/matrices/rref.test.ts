// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/rref.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational } from '../../../src/core';
import { EX, QQ, ZZ } from '../../../src/polys/domains';
import { DM } from '../../../src/polys/matrices/domainmatrix';
import { dmRrefChooseMethod } from '../../../src/polys/matrices/rref';

const q = (p: bigint, d = 1n) => Rational.of(p, d);
const s = (v: unknown): string => (Array.isArray(v) ? `[${v.map(s).join(', ')}]` : String(v));
const I3 = 'DomainMatrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]], (3, 3), QQ)';

describe('rref', () => {
  const A = () => DM([[q(1n, 2n), 2, 3], [4, 5, 6], [7, 8, q(1n, 3n)]], QQ);
  it('chooses the methods as SymPy does', () => {
    const full = (e: Rational) => DM(Array.from({ length: 6 }, () => Array.from({ length: 6 }, () => e)), QQ);
    expect(dmRrefChooseMethod(full(q(1n, 2n ** 60n)), 'auto', false)).toEqual(['GJ', 'sparse']);
    expect(dmRrefChooseMethod(full(q(1n, 3n)), 'auto', false)).toEqual(['CD', 'sparse']);
    expect(dmRrefChooseMethod(full(q(2n ** 80n)), 'auto', false)).toEqual(['CD', 'sparse']);
    expect(dmRrefChooseMethod(full(q(1n, 2n ** 55n * 3n ** 0n)).sub(full(q(0n))), 'auto', false)).toEqual(['GJ', 'sparse']);
    expect(dmRrefChooseMethod(A(), 'FF_dense', false)).toEqual(['FF', 'dense']);
    const big = (rows: number, cols: number, f: (i: number, j: number) => number) => DM(Array.from({ length: rows }, (_, i) => Array.from({ length: cols }, (__, j) => f(i, j))), ZZ);
    expect(dmRrefChooseMethod(big(12, 12, (i, j) => (i === j ? 1 : 0)), 'auto', false)[0]).toBe('GJ');
    expect(dmRrefChooseMethod(big(12, 12, () => 1), 'auto', false)[0]).toBe('GJ');
    expect(dmRrefChooseMethod(big(12, 1200, () => 1), 'auto', false)[0]).toBe('FF');
    expect(dmRrefChooseMethod(big(12, 12, () => 2 ** 40), 'auto', false)[0]).toBe('FF');
    expect(dmRrefChooseMethod(DM([[1]], ZZ.polyRing()), 'auto', true)[0]).toBe('FF');
  });
  it('gives the same rref with every method', () => {
    expect(s(A().rref())).toBe(`[${I3}, [0, 1, 2]]`);
    expect(s(A().rrefDen())).toBe(`[${I3}, 1, [0, 1, 2]]`);
    expect(s(A().rrefDen({ keepDomain: false }))).toBe('[DomainMatrix([[295, 0, 0], [0, 295, 0], [0, 0, 295]], (3, 3), ZZ), 295, [0, 1, 2]]');
    expect(s(A().rref({ method: 'FF' }))).toBe(`[${I3}, [0, 1, 2]]`);
    expect(s(A().rrefDen({ method: 'GJ' }))).toBe(`[${I3}, 1, [0, 1, 2]]`);
    expect(s(A().rrefDen({ method: 'GJ', keepDomain: false }))).toBe(`[${I3}, 1, [0, 1, 2]]`);
    expect(s(A().toSparse().rref({ method: 'GJ_dense' })[0].toDense())).toBe(I3);
    expect(s(A().rrefDen({ method: 'CD_dense' }))).toBe(`[${I3}, 1, [0, 1, 2]]`);
    const B = DM([[1, 2], [3, 4]], ZZ);
    expect(s(B.rrefDen({ method: 'GJ' }))).toBe('[DomainMatrix([[1, 0], [0, 1]], (2, 2), ZZ), 1, [0, 1]]');
    expect(s(B.rrefDen({ method: 'CD' }))).toBe('[DomainMatrix([[-2, 0], [0, -2]], (2, 2), ZZ), -2, [0, 1]]');
    expect(s(DM([[0, 0]], ZZ).rrefDen({ method: 'GJ' }))).toBe('[DomainMatrix([[0, 0]], (1, 2), ZZ), 1, []]');
    expect(s(DM([[0, 0]], ZZ).rrefDen({ method: 'CD' }))).toBe('[DomainMatrix([[0, 0]], (1, 2), ZZ), 1, []]');
    expect(s(B.rref({ method: 'CD' }))).toBe('[DomainMatrix([[1, 0], [0, 1]], (2, 2), QQ), [0, 1]]');
  });
  it('covers the remaining method choices', () => {
    expect(s(DM([[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], QQ).rref()[1])).toBe('[0]');
    expect(s(DM([[1, 0, 0]], ZZ).rref())).toBe('[DomainMatrix([[1, 0, 0]], (1, 3), QQ), [0]]');
    expect(s(DM([[0, 0]], ZZ).rref())).toBe('[DomainMatrix([[0, 0]], (1, 2), QQ), []]');
    expect(s(DM([[1, 1], [1, 2]], EX).rref()[1])).toBe('[0, 1]');
    const full = DM(Array.from({ length: 6 }, () => Array.from({ length: 6 }, () => Rational.of(2n ** 80n, 3n ** 35n))), QQ);
    expect(dmRrefChooseMethod(full, 'auto', false)[0]).toBe('FF');
  });
});
