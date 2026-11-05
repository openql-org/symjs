// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/domainmatrix.ts.
//
// DomainMatrix and its dense and sparse representations. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { toDM } from '../../src/matrices';
import { Matrix } from '../../src/matrices/matrix';

const M = (rows: sj.ExprLike[][]): Matrix => Matrix.of(rows);
const [x] = sj.symbols('x y');

describe('matrices', () => {
  it('DomainMatrix leaves out a zero row', () => {
    expect(String(toDM(sj.Matrix.of([[0, 0], [1, 2]])))).toBe('DomainMatrix({1: {0: 1, 1: 2}}, (2, 2), ZZ)');
    // SymPy: Matrix([[sqrt(2)]]).to_DM().domain is EXRAW
    expect(String(toDM(sj.Matrix.of([[sj.sqrt(2)]])).domain)).toBe('EXRAW');
    // SymPy: Matrix([[1, 2]]).to_DM(domain=QQ)
    expect(String(toDM(sj.Matrix.of([[1, 2]]), { domain: sj.QQ }))).toBe('DomainMatrix({0: {0: 1, 1: 2}}, (1, 2), QQ)');
  });
});

describe('matrices/linalg, linsys, domainmatrix, mutable', () => {

  it('to_DM domains', () => {
    const cases: [Matrix, string, string][] = [
      [M([[1, sj.I]]), 'QQ_I', 'ZZ_I'],
      [M([[sj.Rational.of(1n, 2n)]]), 'QQ', 'QQ'],
      [M([[new sj.Float(1.5)]]), 'RR', 'RR'],
      [M([[x, new sj.Float(1.5)]]), 'RR(x)', 'RR[x]'],
      [M([[x, 2]]), 'ZZ(x)', 'ZZ[x]'],
    ];
    for (const [A, f, d] of cases) expect([String(toDM(A, { field: true }).domain), String(toDM(A).domain)]).toEqual([f, d]);
  });
});
