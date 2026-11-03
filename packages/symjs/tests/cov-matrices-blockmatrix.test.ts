// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of sympy.matrices.expressions.blockmatrix: construction errors,
 * block arithmetic, decompositions, entries and block_collapse rules, with
 * the expected values of SymPy 1.14 (explicit matrices on one line).
 */

import { describe, expect, it } from 'vitest';
import { sstr, symbols } from '../src';
import type { Expr } from '../src';
import {
  BlockDiagMatrix,
  BlockMatrix,
  Identity,
  MatMul,
  MatPow,
  MatrixSymbol,
  Trace,
  Transpose,
  ZeroMatrix,
  blockCollapse,
  deblock,
  det,
  reblock2x2,
  trace,
} from '../src/matrices/expressions';
import type { MatrixExpr } from '../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const O = (r: number, c: number): MatrixExpr => ZeroMatrix(r, c);
const A = MatrixSymbol('A', 2, 2);
const B = MatrixSymbol('B', 2, 3);
const C = MatrixSymbol('C', 3, 2);
const D = MatrixSymbol('D', 3, 3);
const E = MatrixSymbol('E', 2, 2);
const Y = MatrixSymbol('Y', 5, 5);
const BM = BlockMatrix([
  [A, B],
  [C, D],
]);
const ZB = BlockMatrix([
  [O(2, 2), B],
  [C, O(3, 3)],
]);
const NS = BlockMatrix([
  [MatrixSymbol('P', 2, 3), MatrixSymbol('Q', 2, 2)],
  [MatrixSymbol('R', 3, 3), MatrixSymbol('S', 3, 2)],
]);

describe('BlockMatrix construction', () => {
  it('accepts a flat row and rejects bad rows', () => {
    expect(s(BlockMatrix([A, E]))).toBe('Matrix([[A, E]])');
    expect(() => BlockMatrix([[1]])).toThrow(RangeError);
    expect(() => BlockMatrix([])).toThrow('expecting a sequence of 1 or more rows containing Matrices.');
    expect(() => BlockMatrix([[A, MatrixSymbol('F', 3, 2)]])).toThrow("When there are not the same number of rows in each row's matrices");
    expect(() => BlockMatrix([[A, A], [MatrixSymbol('G', 2, 4)]])).toThrow("When there are not the same number of rows in each row's matrices");
  });
  it('substitutes into the blocks', () => {
    expect(s(BM.subs(A, Identity(2)))).toBe('Matrix([[I, B], [C, D]])');
    expect(s(BlockDiagMatrix(A, D).subs(A, Identity(2)))).toBe('Matrix([[I, 0], [0, D]])');
  });
});

describe('BlockMatrix operations', () => {
  it('_blockmul and _blockadd', () => {
    expect(s(BM.blockmul(Y))).toBe('Matrix([[A, B], [C, D]])*Y');
    expect(s(BM.blockadd(Y))).toBe('Matrix([[A, B], [C, D]]) + Y');
    expect(s(BM.blockadd(BM))).toBe('Matrix([[2*A, 2*B], [2*C, 2*D]])');
  });
  it('trace of a block matrix that is not structurally symmetric', () => {
    expect(s(trace(NS))).toBe('Trace(Matrix([[P, Q], [R, S]]))');
    expect(s(M(Trace(NS)).doit())).toBe('Trace(Matrix([[P, Q], [R, S]]))');
  });
  it('determinants', () => {
    expect(s(det(BlockMatrix([[D]])))).toBe('Determinant(D)');
    expect(s(det(ZB))).toBe('Determinant(Matrix([[0, B], [C, 0]]))');
    const u = MatrixSymbol('u', 1, 1);
    const b3 = BlockMatrix([
      [A, O(2, 3), O(2, 1)],
      [O(3, 2), D, O(3, 1)],
      [O(1, 2), O(1, 3), u],
    ]);
    expect(s(det(b3))).toBe('Determinant(Matrix([[A, 0, 0], [0, D, 0], [0, 0, u]]))');
  });
  it('schur complements', () => {
    expect(() => ZB.schur()).toThrow('The given matrix is not invertible. Please set generalized=True');
    expect(() => BM.schur('B')).toThrow('Inverse of non-square matrix');
    expect(s(BM.schur('B', true))).toBe('C - D*(B.T*B)**(-1)*B.T*A');
    expect(() => BM.schur('C')).toThrow('Inverse of non-square matrix');
  });
  it('decompositions of singular or non 2x2 block matrices', () => {
    expect(() => ZB.LDUdecomposition()).toThrow('Block LDU decomposition cannot be calculated when "A" is singular');
    expect(() => ZB.UDLdecomposition()).toThrow('Block UDL decomposition cannot be calculated when "D" is singular');
    expect(() => ZB.LUdecomposition()).toThrow('Block LU decomposition cannot be calculated when "A" is singular');
    expect(() => BlockMatrix([[A]]).LDUdecomposition()).toThrow('Block LDU decomposition is supported only for 2x2 block matrices');
    expect(() => BlockMatrix([[A]]).UDLdecomposition()).toThrow('Block UDL decomposition is supported only for 2x2 block matrices');
    expect(() => BlockMatrix([[A]]).LUdecomposition()).toThrow('Block LU decomposition is supported only for 2x2 block matrices');
    expect(() => BM.LDUdecomposition()).not.toThrow();
  });
  it('entries with symbolic indices', () => {
    const [n, m, i, j] = symbols('n m i j', { integer: true, nonnegative: true });
    const An = MatrixSymbol('A', n, n);
    const Bn = MatrixSymbol('B', n, m);
    const Cn = MatrixSymbol('C', m, n);
    const Dn = MatrixSymbol('D', m, m);
    const BN = BlockMatrix([
      [An, Bn],
      [Cn, Dn],
    ]);
    expect(s(BN.at(i, j))).toBe('Matrix([[A, B], [C, D]])[i, j]');
    expect(s(BN.at(n, 0))).toBe('Matrix([[A, B], [C, D]])[n, 0]');
    expect(s(BN.at(0, n))).toBe('Matrix([[A, B], [C, D]])[0, n]');
    expect(s(BN.at(n.add(1), n.add(2)))).toBe('D[1, 2]');
    expect(s(BM.at(3, 4))).toBe('D[1, 2]');
    expect(s(BlockMatrix([[An], [Cn]]).at(n.add(i), 0))).toBe('C[i, 0]');
    expect(s(BlockMatrix([[An, Bn]]).at(0, n.add(j)))).toBe('B[0, j]');
  });
  it('equals', () => {
    expect(BM.equalsExplicit(BM)).toBe(true);
    expect(
      BM.equalsExplicit(
        BlockMatrix([
          [A, B],
          [C, D],
        ]),
      ),
    ).toBe(true);
  });
});

describe('BlockDiagMatrix', () => {
  const BD = BlockDiagMatrix(B, C);
  it('non-square blocks', () => {
    expect(s(det(BD))).toBe('0');
    expect(() => BD.inverse()).toThrow('Matrix det == 0; not invertible.');
  });
  it('_blockmul and _blockadd', () => {
    expect(s(BD.blockmul(BlockDiagMatrix(C, B)))).toBe('Matrix([[B*C, 0], [0, C*B]])');
    expect(s(BlockDiagMatrix(A, D).blockmul(BlockDiagMatrix(B, C)))).toBe('Matrix([[A*B, 0], [0, D*C]])');
    expect(s(BlockDiagMatrix(A, D).blockadd(BlockDiagMatrix(D, A)))).toBe('Matrix([[A, 0], [0, D]]) + Matrix([[D, 0], [0, A]])');
    expect(s(BlockDiagMatrix(A, D).blockadd(BM))).toBe('Matrix([[2*A, B], [C, 2*D]])');
  });
});

describe('block_collapse rules', () => {
  it('sums and products with plain matrices', () => {
    expect(s(blockCollapse(BM.add(Y)))).toBe('Matrix([[A, B], [C, D]]) + Y');
    expect(s(blockCollapse(BM.mul(Y)))).toBe('Matrix([[A, B], [C, D]])*Matrix([[Y]])');
    expect(s(blockCollapse(Y.mul(BM)))).toBe('Matrix([[Y]])*Matrix([[A, B], [C, D]])');
    expect(s(blockCollapse(BlockDiagMatrix(A, D).mul(2)))).toBe('Matrix([[2*A, 0], [0, 2*D]])');
    const bd = BlockMatrix([
      [A, O(2, 3)],
      [O(3, 2), D],
    ]);
    expect(s(blockCollapse(M(bd.add(Identity(5))).add(Y)))).toBe('Matrix([[I + A, 0], [0, I + D]]) + Y');
    expect(s(blockCollapse(NS.add(Identity(5))))).toBe('Matrix([[P, Q], [R, S]]) + I');
  });
  it('powers', () => {
    const [n, m] = symbols('n m', { integer: true, nonnegative: true });
    const BN = BlockMatrix([
      [MatrixSymbol('A', n, n), MatrixSymbol('B', n, m)],
      [MatrixSymbol('C', m, n), MatrixSymbol('D', m, m)],
    ]);
    expect(s(blockCollapse(MatPow(BM, -1)))).toBe('Matrix([[A, B], [C, D]])**(-1)');
    expect(s(blockCollapse(MatPow(BN, n)))).toBe('Matrix([[A, B], [C, D]])**n');
    expect(s(blockCollapse(MatPow(BM, 0)))).toBe('I');
  });
  it('inverses', () => {
    expect(s(blockCollapse(ZB.I))).toBe('Matrix([[0, B], [C, 0]])**(-1)');
    const allZero = BlockMatrix([
      [O(2, 2), O(2, 3)],
      [O(3, 2), O(3, 3)],
    ]);
    expect(s(blockCollapse(allZero.I))).toBe('Matrix([[0, 0], [0, 0]])**(-1)');
    const swap = BlockMatrix([
      [O(2, 2), Identity(2)],
      [Identity(2), O(2, 2)],
    ]);
    expect(s(blockCollapse(swap.I))).toBe('Matrix([[0, I], [I, 0]])');
    const lower = BlockMatrix([
      [O(2, 2), O(2, 2)],
      [Identity(2), O(2, 2)],
    ]);
    expect(() => blockCollapse(lower.I)).toThrow('Matrix det == 0; not invertible.');
    const EF = BlockMatrix([
      [O(2, 2), E],
      [MatrixSymbol('F', 2, 2), O(2, 2)],
    ]);
    expect(s(blockCollapse(EF.I))).toBe('Matrix([[0, F**(-1)], [E**(-1), 0]])');
    const u = MatrixSymbol('u', 1, 1);
    const b3 = BlockMatrix([
      [A, O(2, 3), O(2, 1)],
      [O(3, 2), D, O(3, 1)],
      [O(1, 2), O(1, 3), u],
    ]);
    expect(s(blockCollapse(b3.I))).toBe('Matrix([[A**(-1), 0, 0], [0, D**(-1), 0], [0, 0, u**(-1)]])');
  });
  it('deblock and reblock_2x2 that do not apply', () => {
    const G1 = MatrixSymbol('G', 4, 1);
    const d1 = BlockMatrix([[BlockMatrix([[A], [E]]), BlockMatrix([[G1]])]]);
    expect(s(deblock(d1))).toBe('Matrix([[Matrix([[A], [E]]), Matrix([[G]])]])');
    const d2 = BlockMatrix([[BlockMatrix([[A, E]])], [BlockMatrix([[MatrixSymbol('G', 3, 4)]])]]);
    expect(s(deblock(d2))).toBe('Matrix([[Matrix([[A, E]])], [Matrix([[G]])]])');
    const z = BlockMatrix([
      [O(2, 3), O(2, 3), O(2, 3)],
      [O(3, 3), O(3, 3), O(3, 3)],
      [O(4, 3), O(4, 3), O(4, 3)],
    ]);
    expect(s(reblock2x2(z))).toBe('Matrix([[0, Matrix([[0, 0]])], [Matrix([[0], [0]]), Matrix([[0, 0], [0, 0]])]])');
  });
});

describe('BlockMatrix remaining rules (SymPy 1.14)', () => {
  const Y5 = MatrixSymbol('Y', 5, 5);
  it('decompositions with non-square blocks', () => {
    expect(() => NS.LDUdecomposition()).toThrow('Inverse of non-square matrix');
    expect(() => NS.UDLdecomposition()).toThrow('Inverse of non-square matrix');
    expect(() => NS.LUdecomposition()).toThrow('Power of non-square matrix P');
  });
  it('equals across block matrix kinds', () => {
    const full = BlockMatrix([
      [A, O(2, 3)],
      [O(3, 2), D],
    ]);
    expect(BlockDiagMatrix(A, D).equalsExplicit(full)).toBe(true);
    // SymPy gives None (not known to be equal)
    expect(BM.equalsExplicit(Y5)).toBe(false);
  });
  it('BlockDiagMatrix with other block matrices', () => {
    expect(s(BlockDiagMatrix(A, D).blockmul(BM))).toBe('Matrix([[A**2, A*B], [D*C, D**2]])');
    expect(s(BlockDiagMatrix(A, D).blockadd(BlockDiagMatrix(E, D)))).toBe('Matrix([[A + E, 0], [0, 2*D]])');
  });
  it('block_collapse of nested and partial blocks', () => {
    expect(s(blockCollapse(Y5.add(BM.mul(Y5))))).toBe('Matrix([[A, B], [C, D]])*Matrix([[Y]]) + Y');
    expect(s(blockCollapse(MatMul(2, Y5, ZB.I)))).toBe('2*Y*Matrix([[0, B], [C, 0]])**(-1)');
    expect(s(blockCollapse(MatMul(Y5, Y5.T, BM)))).toBe('Matrix([[Y*Y.T]])*Matrix([[A, B], [C, D]])');
    const u = MatrixSymbol('u', 2, 1);
    const v = MatrixSymbol('v', 2, 1);
    expect(s(blockCollapse(BlockMatrix([[u, v]]).I))).toBe('Matrix([[u, v]])**(-1)');
    const c = BlockMatrix([
      [O(2, 2), E],
      [Identity(2), O(2, 2)],
    ]);
    expect(s(blockCollapse(c.I))).toBe('Matrix([[0, I], [E**(-1), 0]])');
    expect(s(blockCollapse(Trace(BM).add(1)))).toBe('Trace(A) + Trace(D) + 1');
    expect(s(blockCollapse(Trace(Transpose(BM)).add(1)))).toBe('Trace(A) + Trace(D) + 1');
  });
});
