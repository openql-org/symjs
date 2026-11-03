// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/blockmatrix.ts.
//
// BlockMatrix and BlockDiagMatrix: construction errors, block arithmetic, decompositions, entries and
// the block_collapse rules. Expected values are SymPy 1.14 results (explicit matrices printed on one
// line).

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { type Expr, latex, Matrix, sstr, symbols } from '../../../src';
import { irregular } from '../../../src/matrices/linalg';
import { Adjoint, blockCollapse, blockcut, BlockDiagMatrix, BlockMatrix, bounds, deblock, det, Determinant, Identity, ImmutableMatrix, Inverse, MatMul, MatPow, MatrixSymbol, reblock2x2, Trace, trace, Transpose, ZeroMatrix } from '../../../src/matrices/expressions';
import { cast } from '../../../src/core/guard';
import { MatrixExpr } from '../../../src/matrices/expressions/matexpr';
import { NonInvertibleMatrixError } from '../../../src/core/errors';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const ones = (r: number, c = r): Matrix => Matrix.fromFunction(r, c, () => 1);
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
const toStr = (e: unknown): string => String(e);

describe('blockmatrix', () => {
  const [n, m] = symbols('n m');
  const X = MatrixSymbol('X', n, n);
  const Y = MatrixSymbol('Y', m, m);
  const Z = MatrixSymbol('Z', n, m);
  const B = BlockMatrix([
    [X, Z],
    [ZeroMatrix(m, n), Y],
  ]);
  const C = BlockMatrix([[Identity(n), Z]]);
  it('BlockMatrix and block_collapse', () => {
    expect(s(B)).toBe('Matrix([[X, Z], [0, Y]])');
    expect(s(C)).toBe('Matrix([[I, Z]])');
    expect(s(blockCollapse(C.mul(B)))).toBe('Matrix([[X, Z + Z*Y]])');
    expect(L(B)).toBe('\\left[\\begin{matrix}X & Z\\\\0 & Y\\end{matrix}\\right]');
  });
  it('rejects blocks that do not fill the matrix', () => {
    const dat = [
      [ones(3, 2), ones(3, 3).scale(2)],
      [ones(2, 3).scale(3), ones(2, 2).scale(4)],
    ];
    expect(() => BlockMatrix(dat)).toThrow('the blocks do not fill the matrix in a size-symmetric fashion');
    expect(String(irregular(2, ones(3, 2), ones(3, 3).scale(2), ones(2, 3).scale(3), ones(2, 2).scale(4)))).toBe(
      'Matrix([[1, 1, 2, 2, 2], [1, 1, 2, 2, 2], [1, 1, 2, 2, 2], [3, 3, 3, 4, 4], [3, 3, 3, 4, 4]])',
    );
  });
  const A2 = MatrixSymbol('A', n, n);
  const B2 = MatrixSymbol('B', n, m);
  const C2 = MatrixSymbol('C', m, n);
  const D2 = MatrixSymbol('D', m, m);
  const X2 = BlockMatrix([
    [A2, B2],
    [C2, D2],
  ]);
  it('LDU, UDL and LU decompositions', () => {
    const [L1, D1, U1] = X2.LDUdecomposition();
    expect(s(blockCollapse(M(M(L1).mul(D1)).mul(U1)))).toBe('Matrix([[A, B], [C, D]])');
    expect(s(L1)).toBe('Matrix([[I, 0], [C*A**(-1), I]])');
    expect(s(D1)).toBe('Matrix([[A, 0], [0, -C*A**(-1)*B + D]])');
    expect(s(U1)).toBe('Matrix([[I, A**(-1)*B], [0, I]])');
    const [U2, D3, L2] = X2.UDLdecomposition();
    expect(s(blockCollapse(M(M(U2).mul(D3)).mul(L2)))).toBe('Matrix([[A, B], [C, D]])');
    const [L3, U3] = X2.LUdecomposition();
    expect(s(blockCollapse(M(L3).mul(U3)))).toBe('Matrix([[A, B], [C, D]])');
    expect(s(L3)).toBe('Matrix([[A**(1/2), 0], [C*A**(-1/2), (-C*A**(-1)*B + D)**(1/2)]])');
  });
  it('schur', () => {
    expect(s(X2.schur())).toBe('-C*A**(-1)*B + D');
    expect(s(X2.schur('D'))).toBe('A - B*D**(-1)*C');
    expect(s(X2.schur('B', true))).toBe('C - D*(B.T*B)**(-1)*B.T*A');
    expect(s(X2.schur('C', true))).toBe('-A*(C.T*C)**(-1)*C.T*D + B');
    expect(s(X2.schur('B'))).toBe('C - D*B**(-1)*A');
    expect(s(X2.schur('C'))).toBe('-A*C**(-1)*D + B');
    expect(() => C.schur()).toThrow('Schur Complement can only be calculated for 2x2 block matrices');
  });
  it('transpose', () => {
    expect(s(B.transpose())).toBe('Matrix([[X.T, 0], [Z.T, Y.T]])');
    expect(s(M(B.transpose()).transpose())).toBe('Matrix([[X, Z], [0, Y]])');
  });
  it('blockcut and bounds', () => {
    const Mx = ImmutableMatrix(4, 4, Array.from({ length: 16 }, (_, k) => k));
    const Bc = blockcut(Mx, [1, 3], [1, 3]);
    expect(Bc.name).toBe('BlockMatrix');
    expect(String(M(Bc.blocks.get(0, 1)).asExplicit())).toBe('Matrix([[1, 2, 3]])');
    expect(bounds([1, 10, 50])).toEqual([
      [0, 1],
      [1, 11],
      [11, 61],
    ]);
  });
  it('BlockDiagMatrix', () => {
    expect(s(BlockDiagMatrix(X, Y))).toBe('Matrix([[X, 0], [0, Y]])');
    const D = BlockDiagMatrix(Matrix.of([[1, 2], [3, 4]]), Matrix.of([[5, 6], [7, 8]]));
    const blocks = D.getDiagBlocks();
    expect(s(blocks[0])).toBe('Matrix([[1, 2], [3, 4]])');
    expect(s(blocks[1])).toBe('Matrix([[5, 6], [7, 8]])');
  });
  it('block algebra like SymPy', () => {
    const A = MatrixSymbol('A', n, n);
    const Bm = MatrixSymbol('B', m, m);
    const Cm = MatrixSymbol('C', m, n);
    const Dm = MatrixSymbol('D', n, m);
    const bd = BlockDiagMatrix(A, Bm);
    const Xb = BlockMatrix([
      [A, Dm],
      [Cm, Bm],
    ]);
    expect(s(bd.I)).toBe('Matrix([[A**(-1), 0], [0, B**(-1)]])');
    expect(s(blockCollapse(Inverse(bd)))).toBe('Matrix([[A**(-1), 0], [0, B**(-1)]])');
    expect(s(blockCollapse(Xb.I))).toBe(
      'Matrix([[A**(-1) + A**(-1)*D*(B - C*A**(-1)*D)**(-1)*C*A**(-1), -A**(-1)*D*(B - C*A**(-1)*D)**(-1)], [-(B - C*A**(-1)*D)**(-1)*C*A**(-1), (B - C*A**(-1)*D)**(-1)]])',
    );
    expect(s(blockCollapse(Xb.mul(Xb)))).toBe('Matrix([[A**2 + D*C, A*D + D*B], [B*C + C*A, B**2 + C*D]])');
    expect(s(blockCollapse(Xb.T))).toBe('Matrix([[A.T, C.T], [D.T, B.T]])');
    expect(s(blockCollapse(Transpose(Xb)))).toBe('Matrix([[A.T, C.T], [D.T, B.T]])');
    expect(s(blockCollapse(Xb.add(Xb)))).toBe('Matrix([[2*A, 2*D], [2*C, 2*B]])');
    expect(s(blockCollapse(MatMul(2, Xb)))).toBe('Matrix([[2*A, 2*D], [2*C, 2*B]])');
    expect(s(blockCollapse(Xb.add(Identity(n.add(m)))))).toBe('Matrix([[I + A, D], [C, I + B]])');
    expect(s(blockCollapse(BlockMatrix([[A]]).I))).toBe('A**(-1)');
    expect(s(blockCollapse(MatPow(Xb, 2)))).toBe('Matrix([[A**2 + D*C, A*D + D*B], [B*C + C*A, B**2 + C*D]])');
    expect(s(bd.mul(bd))).toBe('Matrix([[A, 0], [0, B]])**2');
    expect(s(blockCollapse(bd.mul(bd)))).toBe('Matrix([[A**2, 0], [0, B**2]])');
    expect(s(blockCollapse(bd.add(bd)))).toBe('Matrix([[2*A, 0], [0, 2*B]])');
    expect(s(bd.T)).toBe('Matrix([[A.T, 0], [0, B.T]])');
    expect(s(det(bd))).toBe('Determinant(A)*Determinant(B)');
    expect(s(trace(bd))).toBe('Trace(A) + Trace(B)');
    expect(s(trace(Xb))).toBe('Trace(A) + Trace(B)');
    expect(s(det(Xb))).toBe('Determinant(Matrix([[A, D], [C, B]]))');
    expect(L(Determinant(Xb))).toBe('\\left|{\\begin{matrix}A & D\\\\C & B\\end{matrix}}\\right|');
    expect(Xb.shape.map(s)).toEqual(['m + n', 'm + n']);
    expect(Xb.blockshape).toEqual([2, 2]);
    expect(Xb.rowblocksizes.map(s)).toEqual(['n', 'm']);
    expect(s(Xb.at(0, 0))).toBe('Matrix([[A, D], [C, B]])[0, 0]');
    expect(s(Xb.at(n, n))).toBe('Matrix([[A, D], [C, B]])[n, n]');
    const Pb = BlockMatrix([[MatrixSymbol('P', 2, 2), MatrixSymbol('Q', 2, 1)]]);
    expect(String(Pb.asExplicit())).toBe('Matrix([[P[0, 0], P[0, 1], Q[0, 0]], [P[1, 0], P[1, 1], Q[1, 0]]])');
    expect(s(Pb.at(1, 2))).toBe('Q[1, 0]');
    expect(Xb.equals(Xb)).toBe(true);
    expect(Xb.equalsExplicit(Xb)).toBe(true);
    expect(s(M(Transpose(Xb)).doit())).toBe('Matrix([[A.T, C.T], [D.T, B.T]])');
    expect(s(M(Adjoint(Xb)).doit())).toBe('Matrix([[Adjoint(A), Adjoint(C)], [Adjoint(D), Adjoint(B)]])');
    expect(s(Xb.conjugate())).toBe('Adjoint(Matrix([[A, D], [C, B]]).T)');
    expect(L(Transpose(Xb))).toBe('\\left[\\begin{matrix}A & D\\\\C & B\\end{matrix}\\right]^{T}');
    expect(BlockMatrix([[Identity(n), ZeroMatrix(n, m)], [ZeroMatrix(m, n), Identity(m)]]).isIdentity).toBe(true);
  });
});

describe('more SymPy cases', () => {
  const [n, m, k] = symbols('n m k');
  const A = MatrixSymbol('A', n, n);
  const B = MatrixSymbol('B', n, m);
  const C = MatrixSymbol('C', m, n);
  const D = MatrixSymbol('D', m, m);
  const [P, Q, R] = [MatrixSymbol('P', k, k), MatrixSymbol('Q', k, k), MatrixSymbol('R', k, k)];
  it('block inversion formulas and determinants', () => {
    expect(s(blockCollapse(BlockMatrix([[A, B], [C, Identity(m)]]).I))).toBe('Matrix([[(A - B*C)**(-1), -(A - B*C)**(-1)*B], [-C*(A - B*C)**(-1), I + C*(A - B*C)**(-1)*B]])');
    expect(s(blockCollapse(BlockMatrix([[ZeroMatrix(n, n), B], [C, D]]).I))).toBe(
      'Matrix([[(-B*D**(-1)*C)**(-1), -(-B*D**(-1)*C)**(-1)*B*D**(-1)], [-D**(-1)*C*(-B*D**(-1)*C)**(-1), D**(-1) + D**(-1)*C*(-B*D**(-1)*C)**(-1)*B*D**(-1)]])',
    );
    expect(s(det(BlockMatrix([[Identity(n), B], [C, D]])))).toBe('Determinant(-C*B + D)');
    expect(s(det(BlockMatrix([[A, B], [C, Identity(m)]])))).toBe('Determinant(A - B*C)');
  });
  it('deblock and reblock_2x2', () => {
    const bb = BlockMatrix([[BlockMatrix([[P, Q]]), R]]);
    expect(s(deblock(bb))).toBe('Matrix([[P, Q, R]])');
    expect(s(blockCollapse(bb))).toBe('Matrix([[P, Q, R]])');
    const X3 = BlockMatrix([
      [P, Q, R],
      [Q, R, P],
      [R, P, Q],
    ]);
    const rb = reblock2x2(X3) as BlockMatrix;
    expect(rb.blockshape).toEqual([2, 2]);
    expect(s(rb)).toBe('Matrix([[P, Matrix([[Q, R]])], [Matrix([[Q], [R]]), Matrix([[R, P], [P, Q]])]])');
  });
});

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

describe('matrix expressions', () => {
  it('a singular explicit block in a product: no inverse to cancel', () => {
    const X = sj.MatrixSymbol('X', 4, 4);
    const Y = sj.MatrixSymbol('Y', 2, 2);
    const B = sj.BlockDiagMatrix(sj.ImmutableMatrix([[1, 1], [1, 1]]), Y);
    expect(toStr(cast(sj.MatMul(X, B), MatrixExpr).doit())).toBe('X*Matrix([[Matrix([[1, 1], [1, 1]]), 0], [0, Y]])');
    // SymPy: NonInvertibleMatrixError Matrix det == 0; not invertible.
    expect(() => sj.ImmutableMatrix([[1, 1], [1, 1]]).inverse()).toThrow(NonInvertibleMatrixError);
    expect(() => B.inverse()).toThrow(NonInvertibleMatrixError);
  });
});
