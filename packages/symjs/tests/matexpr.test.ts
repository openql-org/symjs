// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Matrix expressions (sympy.matrices.expressions): every doctest example of
 * the SymPy 1.14 modules, plus printing (str and LaTeX) and evaluation
 * cases, with the expected values produced by SymPy. Explicit matrices are
 * printed on one line (SymPy's str with the line breaks removed).
 */

import { describe, expect, it } from 'vitest';
import { Dummy, Eq, Function as UFunction, KroneckerDelta, Lambda, Matrix, Poly, Reals, Rational, S, Sum, adjoint, exp, latex, matrixExp, mul, sin, sstr, symbol, symbols, transpose } from '../src';
import { irregular } from '../src/matrices/linalg';
import type { MatrixExpr } from '../src/matrices/expressions';
import {
  Adjoint,
  BlockDiagMatrix,
  deblock,
  reblock2x2,
  BlockMatrix,
  CompanionMatrix,
  DFT,
  Determinant,
  DiagMatrix,
  DiagonalMatrix,
  DiagonalOf,
  DotProduct,
  ElementwiseApplyFunction,
  FunctionMatrix,
  HadamardPower,
  HadamardProduct,
  IDFT,
  Identity,
  ImmutableMatrix,
  Inverse,
  KroneckerProduct,
  MatAdd,
  MatMul,
  MatPow,
  MatrixElement,
  MatrixPermute,
  MatrixQ,
  MatrixSet,
  MatrixSlice,
  MatrixSymbol,
  OneMatrix,
  Permanent,
  PermutationMatrix,
  PermutationNode,
  ShapeError,
  Trace,
  Transpose,
  ZeroMatrix,
  askMatrix,
  blockCollapse,
  blockcut,
  bounds,
  canonicalize,
  combineKronecker,
  det,
  diagonalizeVector,
  eig,
  fromIndexSummation,
  hadamardPower,
  hadamardProduct,
  isMataddValid,
  isMatmulValid,
  isSquare,
  kroneckerProduct,
  lu,
  matrixKroneckerProduct,
  matrixSymbols,
  mergeExplicitMatAdd,
  mergeExplicitMatMul,
  per,
  qr,
  refineMatrix,
  svd,
  trace,
} from '../src/matrices/expressions';
import type { Expr } from '../src';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const eye = (n: number): Matrix => Matrix.eye(n);
const ones = (r: number, c = r): Matrix => Matrix.fromFunction(r, c, () => 1);
const mats3 = (r: Expr | number, c: Expr | number): [MatrixExpr, MatrixExpr, MatrixExpr] => [MatrixSymbol('A', r, c), MatrixSymbol('B', r, c), MatrixSymbol('C', r, c)];

describe('_shape', () => {
  const [m, n, p, q] = symbols('m n p q');
  const A = MatrixSymbol('A', m, n);
  const B = MatrixSymbol('B', p, q);
  it('is_matadd_valid, is_matmul_valid, is_square', () => {
    expect(s(isMataddValid(A, B))).toBe('Eq(m, p) & Eq(n, q)');
    expect(s(isMatmulValid(A, B))).toBe('Eq(n, p)');
    expect(s(isSquare(A))).toBe('Eq(m, n)');
  });
  it('validates integer shapes like SymPy', () => {
    const A3 = MatrixSymbol('A', 3, 4);
    const C = MatrixSymbol('C', 4, 3);
    expect(s(MatAdd(A3, MatrixSymbol('B', 3, 4)))).toBe('A + B');
    expect(() => MatAdd(A3, C)).toThrow(ShapeError);
    expect(() => MatAdd(A3, C)).toThrow('Matrices have mismatching shape: (3, 4)');
    expect(() => A3.mul(A3)).toThrow('Matrices are not aligned');
    expect(() => MatPow(A3, 2)).toThrow('Power of non-square matrix A');
    expect(() => Trace(A3)).toThrow('Trace of a non-square matrix');
    expect(() => A3.I).toThrow('Inverse of non-square matrix');
    expect(() => HadamardProduct(A3, C)).toThrow('Matrices have mismatching shape: (3, 4)');
    expect(() => MatAdd(A3, 2)).toThrow('Mix of Matrix and Scalar symbols');
    expect(() => MatrixSymbol('A', -1, 2)).toThrow('should be a nonnegative integer');
    expect(() => MatrixSymbol('A', Rational.of(1, 2), 2)).toThrow(RangeError);
  });
});

describe('adjoint', () => {
  it('Adjoint and adjoint', () => {
    const A = MatrixSymbol('A', 3, 5);
    const B = MatrixSymbol('B', 5, 3);
    const AB = A.mul(B);
    expect(s(Adjoint(AB))).toBe('Adjoint(A*B)');
    expect(s(adjoint(AB))).toBe('Adjoint(B)*Adjoint(A)');
    expect(adjoint(AB).equals(Adjoint(AB))).toBe(false);
    expect(adjoint(AB).equals(M(Adjoint(AB)).doit())).toBe(true);
    expect(M(adjoint(AB)).equalsExplicit(Adjoint(AB))).toBe(true);
    expect(s(M(Adjoint(AB)).doit())).toBe('Adjoint(B)*Adjoint(A)');
    expect(L(Adjoint(A))).toBe('A^{\\dagger}');
    expect(L(Adjoint(AB))).toBe('\\left(A B\\right)^{\\dagger}');
    expect(s(A.H)).toBe('Adjoint(A)');
  });
});

describe('applyfunc', () => {
  it('ElementwiseApplyFunction', () => {
    const X = MatrixSymbol('X', 3, 3);
    expect(s(X.applyfunc(exp))).toBe('Lambda(_d, exp(_d)).(X)');
    const expr = ElementwiseApplyFunction(exp, eye(3));
    expect(s(expr)).toBe('Lambda(_d, exp(_d)).(Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]]))');
    expect(s(M(expr).doit())).toBe('Matrix([[E, 1, 1], [1, E, 1], [1, 1, E]])');
    expect(String(matrixExp(eye(3)))).toBe('Matrix([[E, 0, 0], [0, E, 0], [0, 0, E]])');
    expect(s(M(X.applyfunc(exp)).T)).toBe('Lambda(_d, exp(_d)).(X.T)');
    expect(s(M(X.applyfunc(exp)).at(0, 1))).toBe('exp(X[0, 1])');
    expect(s(M(M(X.applyfunc(sin)).applyfunc(exp)).doit())).toBe('Lambda(_d, exp(sin(_d))).(X)');
    expect(L(X.applyfunc(exp))).toBe('{\\left( d \\mapsto e^{d} \\right)}_{\\circ}\\left({X}\\right)');
  });
});

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

describe('companion', () => {
  it('CompanionMatrix', () => {
    const x = symbol('x');
    const c = symbols('c0 c1 c2 c3 c4');
    const p = Poly.from(c[0]!.add(c[1]!.mul(x)).add(c[2]!.mul(x.pow(2))).add(c[3]!.mul(x.pow(3))).add(c[4]!.mul(x.pow(4))).add(x.pow(5)), [x]);
    expect(s(CompanionMatrix(p))).toBe("CompanionMatrix(Poly(x**5 + c4*x**4 + c3*x**3 + c2*x**2 + c1*x + c0, x, domain='ZZ[c0,c1,c2,c3,c4]'))");
    const C = CompanionMatrix(Poly.from(x.pow(2).add(x.mul(2)).add(3), [x]));
    expect(String(C.asExplicit())).toBe('Matrix([[0, -3], [1, -2]])');
    expect(s(C.at(0, 1))).toBe('-3');
    expect(s(C.at(1, 0))).toBe('1');
  });
});

describe('determinant', () => {
  const A = MatrixSymbol('A', 3, 3);
  it('Determinant and det', () => {
    expect(s(Determinant(A))).toBe('Determinant(A)');
    expect(s(Determinant(eye(3)).doit())).toBe('1');
    expect(s(det(A))).toBe('Determinant(A)');
    expect(s(det(eye(3)))).toBe('1');
    expect(L(Determinant(A))).toBe('\\left|{A}\\right|');
  });
  it('Permanent and per', () => {
    expect(s(Permanent(A))).toBe('Permanent(A)');
    expect(s(Permanent(ones(3, 3)).doit())).toBe('6');
    expect(s(per(A))).toBe('Permanent(A)');
    expect(s(per(ones(5, 5)))).toBe('120');
    expect(s(per(Matrix.col(1, 2, 5)))).toBe('8');
    expect(L(Permanent(A))).toBe('\\operatorname{Permanent}\\left(A\\right)');
  });
  it('refine_Determinant', () => {
    const X = MatrixSymbol('X', 2, 2);
    expect(s(det(X))).toBe('Determinant(X)');
    expect(s(refineMatrix(det(X), MatrixQ.orthogonal(X)))).toBe('1');
    expect(s(refineMatrix(det(X), MatrixQ.singular(X)))).toBe('0');
  });
});

describe('diagonal', () => {
  const n = symbol('n', { integer: true });
  const m = symbol('m', { integer: true });
  it('DiagonalMatrix', () => {
    const D = DiagonalMatrix(MatrixSymbol('x', 2, 3));
    expect(s(D.at(1, 2))).toBe('0');
    expect(s(D.at(1, 1))).toBe('x[1, 1]');
    expect(s(D.diagonalLength)).toBe('2');
    expect(s(DiagonalMatrix(MatrixSymbol('x', n.add(1), n)).diagonalLength)).toBe('n');
    const tall = DiagonalMatrix(MatrixSymbol('x', n, 3));
    expect(s(tall.diagonalLength)).toBe('3');
    expect(s(tall.at(10, 1))).toBe('0');
    // SymPy gives None; the length is Min(n, m)
    expect(s(DiagonalMatrix(MatrixSymbol('x', n, m)).diagonalLength)).toBe('Min(m, n)');
    const [i, j] = symbols('i j');
    const Xs = MatrixSymbol('X', n, n);
    expect(s(DiagonalMatrix(Xs).at(0, 0))).toBe('X[0, 0]');
    expect(s(DiagonalMatrix(Xs).at(i, j))).toBe('KroneckerDelta(i, j)*X[i, j]');
  });
  it('DiagonalOf', () => {
    const x = MatrixSymbol('x', 2, 3);
    const diag = DiagonalOf(x);
    expect(diag.shape.map(s)).toEqual(['2', '1']);
    expect(s(diag.at(1, 0))).toBe('x[1, 1]');
    expect(s(diag.at(1))).toBe('x[1, 1]');
    expect(s(diag.diagonalLength)).toBe('2');
    expect(s(DiagonalOf(MatrixSymbol('x', n.add(1), n)).diagonalLength)).toBe('n');
    expect(s(DiagonalOf(MatrixSymbol('x', n, 3)).diagonalLength)).toBe('3');
    expect(s(DiagonalOf(MatrixSymbol('x', n, m)).diagonalLength)).toBe('Min(m, n)');
    expect(s(DiagonalOf(MatrixSymbol('X', n, n)).at(symbol('i'), 0))).toBe('X[i, i]');
  });
  it('DiagMatrix and diagonalize_vector', () => {
    const k = symbol('k');
    const v = MatrixSymbol('v', k, 1);
    const w = MatrixSymbol('w', 1, k);
    expect(s(DiagMatrix(v).doit())).toBe('DiagMatrix(v)');
    expect(s(DiagMatrix(MatMul(2, v)).doit())).toBe('2*DiagMatrix(v)');
    expect(s(DiagMatrix(v.T).doit())).toBe('DiagMatrix(v)');
    expect(s(DiagMatrix(Matrix.col(1, 2)).doit())).toBe('Matrix([[1, 0], [0, 2]])');
    expect(s(diagonalizeVector(v))).toBe('DiagMatrix(v)');
    expect(s(DiagMatrix(v).at(0, 1))).toBe('0');
    expect(s(DiagMatrix(w).at(1, 1))).toBe('w[0, 1]');
    expect(String(DiagMatrix(Matrix.col(1, 2)).asExplicit())).toBe('Matrix([[1, 0], [0, 2]])');
    expect(s(DiagMatrix(v).T)).toBe('DiagMatrix(v)');
  });
});

describe('dotproduct', () => {
  it('DotProduct', () => {
    const A = MatrixSymbol('A', 1, 3);
    const B = MatrixSymbol('B', 1, 3);
    expect(s(DotProduct(A, B))).toBe('DotProduct(A, B)');
    expect(s(DotProduct(A, B).doit())).toBe('A[0, 0]*B[0, 0] + A[0, 1]*B[0, 1] + A[0, 2]*B[0, 2]');
    expect(s(DotProduct(MatrixSymbol('a', 3, 1), MatrixSymbol('b', 3, 1)).doit())).toBe('a[0, 0]*b[0, 0] + a[1, 0]*b[1, 0] + a[2, 0]*b[2, 0]');
    expect(s(DotProduct(MatrixSymbol('a', 1, 3), MatrixSymbol('b', 3, 1)).doit())).toBe('a[0, 0]*b[0, 0] + a[0, 1]*b[1, 0] + a[0, 2]*b[2, 0]');
    expect(s(DotProduct(Matrix.col(1, 2, 3), Matrix.col(4, 5, 6)).doit())).toBe('32');
    expect(L(DotProduct(MatrixSymbol('a', 1, 3), MatrixSymbol('b', 1, 3)))).toBe('a \\cdot b');
    expect(() => DotProduct(MatrixSymbol('a', 2, 3), B)).toThrow('Argument 1 of DotProduct is not a vector');
  });
});

describe('fourier', () => {
  it('DFT and IDFT', () => {
    const n = symbol('n');
    expect(s(DFT(3))).toBe('DFT(3)');
    expect(String(DFT(3).asExplicit())).toBe(
      'Matrix([[sqrt(3)/3, sqrt(3)/3, sqrt(3)/3], [sqrt(3)/3, sqrt(3)*exp(-2*I*pi/3)/3, sqrt(3)*exp(2*I*pi/3)/3], [sqrt(3)/3, sqrt(3)*exp(2*I*pi/3)/3, sqrt(3)*exp(-2*I*pi/3)/3]])',
    );
    expect(DFT(n).shape.map(s)).toEqual(['n', 'n']);
    expect(s(IDFT(3))).toBe('IDFT(3)');
    expect(s(IDFT(4).mul(DFT(4)))).toBe('I');
    expect(String(DFT(2).asExplicit())).toBe('Matrix([[sqrt(2)/2, sqrt(2)/2], [sqrt(2)/2, -sqrt(2)/2]])');
    expect(s(DFT(n).I)).toBe('IDFT(n)');
    expect(L(IDFT(3))).toBe('\\text{IDFT}_{3}');
    expect(s(DFT(4).at(3, 3))).toBe('-I/2');
  });
});

describe('funcmatrix', () => {
  const [i, j, n, m] = symbols('i j n m');
  it('FunctionMatrix', () => {
    expect(s(FunctionMatrix(n, m, Lambda([i, j], i.add(j))))).toBe('FunctionMatrix(n, m, Lambda((i, j), i + j))');
    const X = FunctionMatrix(3, 3, (a, b) => KroneckerDelta(a, b));
    expect(String(X.asExplicit())).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    const f = UFunction('f');
    const Xf = FunctionMatrix(3, 3, (a, b) => f(a, b));
    expect(String(Xf.asExplicit())).toBe('Matrix([[f(0, 0), f(0, 1), f(0, 2)], [f(1, 0), f(1, 1), f(1, 2)], [f(2, 0), f(2, 1), f(2, 2)]])');
    expect(s(Xf)).toBe('FunctionMatrix(3, 3, Lambda((_i, _j), f(_i, _j)))');
    expect(s(FunctionMatrix(n, m, 'lambda i, j: i + j'))).toBe('FunctionMatrix(n, m, Lambda((i, j), i + j))');
    const Y = FunctionMatrix(1000, 1000, Lambda([i, j], i.add(j)));
    expect(Y.mul(Y)).toBeInstanceOf(MatPow);
    expect(s(M(Y.pow(2)).at(10, 10))).toBe('342923500');
  });
  it('trace and entries', () => {
    expect(s(trace(FunctionMatrix(3, 3, Lambda([i, j], i.add(j)))))).toBe('6');
    expect(s(trace(FunctionMatrix(n, n, Lambda([i, j], i.mul(j)))))).toBe('n**3/3 - n**2/2 + n/6');
    expect(s(FunctionMatrix(2, 2, Lambda([i, j], i.add(j))).at(1, 1))).toBe('2');
    expect(s(FunctionMatrix(n, n, Lambda([i, j], i.mul(j))).T)).toBe('FunctionMatrix(n, n, Lambda((i, j), i*j)).T');
  });
});

describe('hadamard', () => {
  it('HadamardProduct and hadamard_product', () => {
    const A = MatrixSymbol('A', 5, 5);
    const B = MatrixSymbol('B', 5, 5);
    expect(hadamardProduct(A, B)).toBeInstanceOf(HadamardProduct);
    const A2 = MatrixSymbol('A', 2, 3);
    const B2 = MatrixSymbol('B', 2, 3);
    expect(s(hadamardProduct(A2))).toBe('A');
    expect(s(hadamardProduct(A2, B2))).toBe('HadamardProduct(A, B)');
    expect(s(M(hadamardProduct(A2, B2)).at(0, 1))).toBe('A[0, 1]*B[0, 1]');
    expect(() => hadamardProduct()).toThrow('Empty Hadamard product is undefined');
  });
  it('canonicalize', () => {
    const [A, B, C] = mats3(2, 2);
    let X = HadamardProduct(A, HadamardProduct(B, C));
    expect(s(X)).toBe('HadamardProduct(A, HadamardProduct(B, C))');
    expect(s(canonicalize(X))).toBe('HadamardProduct(A, B, C)');
    X = HadamardProduct(A, B);
    const Y = HadamardProduct(B, A);
    expect(s(X)).toBe('HadamardProduct(A, B)');
    expect(s(Y)).toBe('HadamardProduct(B, A)');
    expect(s(canonicalize(X))).toBe('HadamardProduct(A, B)');
    expect(s(canonicalize(Y))).toBe('HadamardProduct(A, B)');
    X = HadamardProduct(A, OneMatrix(2, 2));
    expect(s(X)).toBe('HadamardProduct(A, 1)');
    expect(s(canonicalize(X))).toBe('A');
    X = HadamardProduct(A, ZeroMatrix(2, 2));
    expect(s(X)).toBe('HadamardProduct(A, 0)');
    expect(s(canonicalize(X))).toBe('0');
    X = HadamardProduct(A, A, A);
    expect(s(X)).toBe('HadamardProduct(A, A, A)');
    expect(s(canonicalize(X))).toBe('HadamardPower(A, 3)');
  });
  it('printing and powers', () => {
    const n = symbol('n');
    const x = symbol('x');
    const [A, B, C] = mats3(n, n);
    expect(L(HadamardProduct(A, B))).toBe('A \\circ B');
    expect(L(HadamardProduct(A, HadamardProduct(B, C)))).toBe('A \\circ \\left(B \\circ C\\right)');
    expect(s(HadamardPower(A, 3))).toBe('HadamardPower(A, 3)');
    expect(L(HadamardPower(A, 3))).toBe('A^{\\circ {3}}');
    expect(L(HadamardPower(A, x.add(1)))).toBe('A^{\\circ \\left({x + 1}\\right)}');
    expect(s(HadamardProduct(A, B).mul(C))).toBe('(HadamardProduct(A, B))*C');
    expect(L(HadamardProduct(A, B).mul(C))).toBe('\\left(A \\circ B\\right) C');
    expect(s(MatMul(2, HadamardProduct(A, B)))).toBe('2*(HadamardProduct(A, B))');
    expect(s(MatPow(HadamardProduct(A, B), 2))).toBe('(HadamardProduct(A, B))**2');
    expect(s(hadamardPower(A, 1))).toBe('A');
    expect(s(M(HadamardPower(MatrixSymbol('P', 2, 2), 2)).at(0, 1))).toBe('P[0, 1]**2');
    expect(s(M(hadamardProduct(Matrix.of([[1, 2], [3, 4]]), Matrix.of([[5, 6], [7, 8]]))))).toBe('Matrix([[5, 12], [21, 32]])');
  });
});

describe('inverse', () => {
  it('Inverse', () => {
    const A = MatrixSymbol('A', 3, 3);
    const B = MatrixSymbol('B', 3, 3);
    expect(s(Inverse(A))).toBe('A**(-1)');
    expect(A.inverse().equals(Inverse(A))).toBe(true);
    expect(s(M(A.mul(B)).inverse())).toBe('B**(-1)*A**(-1)');
    expect(s(Inverse(A.mul(B)))).toBe('(A*B)**(-1)');
    expect(s(M(Inverse(A.mul(B))).doit())).toBe('B**(-1)*A**(-1)');
    expect(s(M(Inverse(A.mul(B))).doit({ invExpand: false }))).toBe('(A*B)**(-1)');
  });
  it('refine_Inverse', () => {
    const X = MatrixSymbol('X', 2, 2);
    expect(s(X.I)).toBe('X**(-1)');
    expect(s(refineMatrix(X.I, MatrixQ.orthogonal(X)))).toBe('X.T');
    // SymPy gives the conjugate Adjoint(X.T); the inverse of a unitary matrix is its adjoint
    expect(s(refineMatrix(X.I, MatrixQ.unitary(X)))).toBe('Adjoint(X)');
  });
});

describe('kronecker', () => {
  const [m, n] = symbols('m n', { integer: true });
  it('KroneckerProduct', () => {
    const A = MatrixSymbol('A', 5, 5);
    const B = MatrixSymbol('B', 5, 5);
    expect(KroneckerProduct(A, B)).toBeInstanceOf(KroneckerProduct);
  });
  it('has_matching_shape and structurally_equal', () => {
    const A = MatrixSymbol('A', m, n);
    const B = MatrixSymbol('B', n, m);
    const kab = KroneckerProduct(A, B) as KroneckerProduct;
    expect(kab.hasMatchingShape(KroneckerProduct(B, A))).toBe(true);
    expect(kab.hasMatchingShape(KroneckerProduct(A, B))).toBe(false);
    expect(kab.hasMatchingShape(A)).toBe(false);
    const A2 = MatrixSymbol('A', m, m);
    const B2 = MatrixSymbol('B', n, n);
    const C2 = MatrixSymbol('C', m, m);
    const D2 = MatrixSymbol('D', n, n);
    const k2 = KroneckerProduct(A2, B2) as KroneckerProduct;
    expect(k2.structurallyEqual(KroneckerProduct(C2, D2))).toBe(true);
    expect(k2.structurallyEqual(KroneckerProduct(D2, C2))).toBe(false);
    expect(k2.structurallyEqual(C2)).toBe(false);
  });
  it('combine_kronecker', () => {
    const A = MatrixSymbol('A', m, n);
    const B = MatrixSymbol('B', n, m);
    expect(s(combineKronecker(M(KroneckerProduct(A, B)).mul(KroneckerProduct(B, A))))).toBe('KroneckerProduct(A*B, B*A)');
    expect(s(combineKronecker(M(KroneckerProduct(A, B)).add(KroneckerProduct(B.T, A.T))))).toBe('KroneckerProduct(A + B.T, B + A.T)');
    const C = MatrixSymbol('C', n, n);
    const D = MatrixSymbol('D', m, m);
    expect(s(combineKronecker(M(KroneckerProduct(C, D)).pow(m)))).toBe('KroneckerProduct(C**m, D**m)');
  });
  it('kronecker_product', () => {
    const A = MatrixSymbol('A', 2, 2);
    const B = MatrixSymbol('B', 2, 2);
    expect(s(kroneckerProduct(A))).toBe('A');
    expect(s(kroneckerProduct(A, B))).toBe('KroneckerProduct(A, B)');
    expect(s(M(kroneckerProduct(A, B)).at(0, 1))).toBe('A[0, 0]*B[0, 1]');
    expect(String(M(kroneckerProduct(A, B)).asExplicit())).toBe(
      'Matrix([[A[0, 0]*B[0, 0], A[0, 0]*B[0, 1], A[0, 1]*B[0, 0], A[0, 1]*B[0, 1]], [A[0, 0]*B[1, 0], A[0, 0]*B[1, 1], A[0, 1]*B[1, 0], A[0, 1]*B[1, 1]], [A[1, 0]*B[0, 0], A[1, 0]*B[0, 1], A[1, 1]*B[0, 0], A[1, 1]*B[0, 1]], [A[1, 0]*B[1, 0], A[1, 0]*B[1, 1], A[1, 1]*B[1, 0], A[1, 1]*B[1, 1]]])',
    );
    const sigmaX = Matrix.of([
      [0, 1],
      [1, 0],
    ]);
    const isigmaY = Matrix.of([
      [0, 1],
      [-1, 0],
    ]);
    expect(s(kroneckerProduct(sigmaX, isigmaY))).toBe('Matrix([[0, 0, 0, 1], [0, 0, -1, 0], [0, 1, 0, 0], [-1, 0, 0, 0]])');
  });
  it('matrix_kronecker_product', () => {
    const m1 = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    const m2 = Matrix.of([
      [1, 0],
      [0, 1],
    ]);
    expect(String(matrixKroneckerProduct(m1, m2))).toBe('Matrix([[1, 0, 2, 0], [0, 1, 0, 2], [3, 0, 4, 0], [0, 3, 0, 4]])');
    expect(String(matrixKroneckerProduct(m2, m1))).toBe('Matrix([[1, 2, 0, 0], [3, 4, 0, 0], [0, 0, 1, 2], [0, 0, 3, 4]])');
  });
  it('printing and evaluation', () => {
    const k = symbol('k');
    const [A, B, C] = mats3(k, k);
    expect(L(KroneckerProduct(A, B))).toBe('A \\otimes B');
    expect(L(KroneckerProduct(A.add(B), C))).toBe('\\left(A + B\\right) \\otimes C');
    expect(s(KroneckerProduct(A, B).mul(C))).toBe('(KroneckerProduct(A, B))*C');
    expect(s(M(KroneckerProduct(A, B)).neg())).toBe('-(KroneckerProduct(A, B))');
    expect(L(M(KroneckerProduct(A, B)).neg())).toBe('- A \\otimes B');
    expect(s(kroneckerProduct(Identity(2), Identity(3)))).toBe('I');
    expect(s(M(KroneckerProduct(A, B)).T)).toBe('KroneckerProduct(A.T, B.T)');
    expect(s(trace(KroneckerProduct(A, B)))).toBe('Trace(A)*Trace(B)');
    expect(s(kroneckerProduct(MatMul(2, A), B))).toBe('2*(KroneckerProduct(A, B))');
    expect(s(M(KroneckerProduct(A, B)).I)).toBe('KroneckerProduct(A**(-1), B**(-1))');
  });
});

describe('matadd', () => {
  it('MatAdd', () => {
    const [A, B, C] = ['A', 'B', 'C'].map((x) => MatrixSymbol(x, 5, 5));
    expect(s(MatAdd(A!, B!, C!))).toBe('A + B + C');
  });
  it('merge_explicit', () => {
    const A = MatrixSymbol('A', 2, 2);
    const B = eye(2);
    const C = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    const X = MatAdd(A, B, C);
    expect(s(X)).toBe('Matrix([[1, 0], [0, 1]]) + Matrix([[1, 2], [3, 4]]) + A');
    expect(s(mergeExplicitMatAdd(X))).toBe('Matrix([[2, 2], [3, 5]]) + A');
    expect(s(M(X).doit())).toBe('Matrix([[2, 2], [3, 5]]) + A');
    expect(s(A.add(B))).toBe('Matrix([[1, 0], [0, 1]]) + A');
    expect(s(MatAdd(Identity(2), C))).toBe('I + Matrix([[1, 2], [3, 4]])');
    expect(s(M(M(A.add(C)).add(A)))).toBe('Matrix([[1, 2], [3, 4]]) + 2*A');
  });
});

describe('matexpr', () => {
  it('MatrixExpr', () => {
    const A = MatrixSymbol('A', 3, 3);
    const y = MatrixSymbol('y', 3, 1);
    const x = M(M(M(M(A.T).mul(A)).I).mul(A)).mul(y);
    expect(s(x)).toBe('A**(-1)*A.T**(-1)*A*y');
    expect(L(x)).toBe('A^{-1} \\left(A^{T}\\right)^{-1} A y');
  });
  it('as_explicit, as_mutable, equals', () => {
    const I3 = Identity(3);
    expect(s(I3)).toBe('I');
    expect(String(I3.asExplicit())).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    expect(I3.shape.map(s)).toEqual(['3', '3']);
    expect(String(I3.asMutable())).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    expect(Identity(3).equalsExplicit(eye(3))).toBe(true);
    expect(Identity(3).equals(ImmutableMatrix(eye(3)))).toBe(false);
    expect(MatrixSymbol('A', 2, 2).equalsExplicit(MatrixSymbol('Z', 2, 2))).toBe(false);
    expect(() => Identity(symbol('n')).asExplicit()).toThrow('Matrix with symbolic shape cannot be represented explicitly.');
  });
  it('from_index_summation', () => {
    const [i, j, k, l, N] = symbols('i j k l N');
    const A = MatrixSymbol('A', N, N);
    const B = MatrixSymbol('B', N, N);
    const Nm1 = N.sub(1);
    expect(s(fromIndexSummation(Sum(mul(A.at(i, j), B.at(j, k)), [j, 0, Nm1])))).toBe('A*B');
    expect(s(fromIndexSummation(Sum(mul(A.at(j, i), B.at(j, k)), [j, 0, Nm1])))).toBe('A.T*B');
    expect(s(fromIndexSummation(Sum(A.at(i, i), [i, 0, Nm1])))).toBe('Trace(A)');
    expect(s(fromIndexSummation(Sum(mul(A.at(i, j), B.at(k, j), A.at(l, k)), [j, 0, Nm1], [k, 0, Nm1])))).toBe('A*B.T*A.T');
    expect(s(fromIndexSummation(Sum(mul(A.at(i, j), B.at(j, i)), [i, 0, Nm1], [j, 0, Nm1])))).toBe('Trace(A*B)');
  });
  it('MatrixSymbol', () => {
    const A = MatrixSymbol('A', 3, 4);
    const B = MatrixSymbol('B', 4, 3);
    expect(A.shape.map(s)).toEqual(['3', '4']);
    expect(s(M(MatMul(2, A).mul(B)).add(Identity(3)))).toBe('I + 2*A*B');
    expect(s(M(A.rmul(2)).mul(B))).toBe('2*A*B');
    expect(new MatrixSymbol('A', 3, 4).symbolName).toBe('A');
    expect(L(MatrixSymbol('alpha', 2, 2))).toBe('\\alpha');
  });
  it('matrix_symbols', () => {
    const n = symbol('n');
    const A = MatrixSymbol('A', n, n);
    const B = MatrixSymbol('B', n, n);
    expect(matrixSymbols(MatMul(Trace(B), A)).map(s)).toEqual(['B', 'A']);
  });
  it('MatrixElement', () => {
    const n = symbol('n');
    const A = MatrixSymbol('A', n, n);
    expect(s(MatrixElement(A, 0, 1))).toBe('A[0, 1]');
    expect(s(MatrixElement(Matrix.of([[1, 2]]), 0, 1))).toBe('2');
    expect(L(MatrixElement(A.T, 0, 1))).toBe('{\\left(A^{T}\\right)}_{0,1}');
    expect(s(MatrixElement(A.mul(MatrixSymbol('B', n, n)), 0, 1))).toBe('(A*B)[0, 1]');
  });
});

describe('matmul', () => {
  it('MatMul', () => {
    const A = MatrixSymbol('A', 5, 4);
    const B = MatrixSymbol('B', 4, 3);
    const C = MatrixSymbol('C', 3, 6);
    expect(s(MatMul(A, B, C))).toBe('A*B*C');
  });
  it('merge_explicit', () => {
    const A = MatrixSymbol('A', 2, 2);
    const B = Matrix.of([
      [1, 1],
      [1, 1],
    ]);
    const C = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    let X = MatMul(A, B, C);
    expect(s(X)).toBe('A*Matrix([[1, 1], [1, 1]])*Matrix([[1, 2], [3, 4]])');
    expect(s(mergeExplicitMatMul(X))).toBe('A*Matrix([[4, 6], [4, 6]])');
    X = MatMul(B, A, C);
    expect(s(X)).toBe('Matrix([[1, 1], [1, 1]])*A*Matrix([[1, 2], [3, 4]])');
    expect(s(mergeExplicitMatMul(X))).toBe('Matrix([[1, 1], [1, 1]])*A*Matrix([[1, 2], [3, 4]])');
    expect(L(MatMul(A, B))).toBe('A \\left[\\begin{matrix}1 & 1\\\\1 & 1\\end{matrix}\\right]');
    expect(s(M(MatMul(2, A)).mul(C))).toBe('2*A*Matrix([[1, 2], [3, 4]])');
    expect(s(M(MatMul(2, C, A)).doit())).toBe('Matrix([[2, 4], [6, 8]])*A');
    expect(s(MatMul(C, 2, A))).toBe('Matrix([[1, 2], [3, 4]])*2*A');
    expect(s(A.mul(eye(2)))).toBe('A');
  });
  it('refine_MatMul', () => {
    const X = MatrixSymbol('X', 2, 2);
    const expr = X.mul(X.T);
    expect(s(expr)).toBe('X*X.T');
    expect(s(refineMatrix(expr, MatrixQ.orthogonal(X)))).toBe('I');
    expect(s(refineMatrix(X.mul(X.conjugate()), MatrixQ.unitary(X)))).toBe('X*Adjoint(X.T)');
    expect(s(refineMatrix(X.mul(X.adjoint()), MatrixQ.unitary(X)))).toBe('I');
  });
  it('entries', () => {
    const A = MatrixSymbol('A', 2, 2);
    const Z = MatrixSymbol('Z', 2, 2);
    const C = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    expect(s(M(A.mul(Z)).at(0, 1))).toBe('A[0, 0]*Z[0, 1] + A[0, 1]*Z[1, 1]');
    expect(s(M(A.mul(C)).at(0, 1))).toBe('2*A[0, 0] + 4*A[0, 1]');
    expect(s(M(A.add(C)).at(0, 1))).toBe('A[0, 1] + 2');
    expect(s(M(MatMul(2, A)).at(0, 1))).toBe('2*A[0, 1]');
    expect(s(M(A.pow(2)).at(0, 1))).toBe('A[0, 0]*A[0, 1] + A[0, 1]*A[1, 1]');
    expect(s(M(A.I).at(0, 1))).toBe('-A[0, 1]/(A[0, 0]*A[1, 1] - A[0, 1]*A[1, 0])');
  });
});

describe('permutation', () => {
  const p = PermutationNode.fromCycles([[1, 2, 0]]);
  it('MatrixPermute', () => {
    const A = Matrix.of([
      [1, 2, 3],
      [4, 5, 6],
      [7, 8, 9],
    ]);
    expect(String(MatrixPermute(A, p, 0).asExplicit())).toBe('Matrix([[4, 5, 6], [7, 8, 9], [1, 2, 3]])');
    expect(String(MatrixPermute(A, p, 1).asExplicit())).toBe('Matrix([[2, 3, 1], [5, 6, 4], [8, 9, 7]])');
    expect(s(MatrixPermute(A, p, 0))).toBe('MatrixPermute(Matrix([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), (0 1 2), 0)');
    expect(s(MatrixPermute(MatrixSymbol('X', 3, 3), p, 1))).toBe('MatrixPermute(X, (0 1 2), 1)');
    expect(s(MatrixPermute(Identity(3), p, 0).doit())).toBe('PermutationMatrix((0 1 2))');
  });
  it('PermutationMatrix', () => {
    const P = PermutationMatrix(p);
    const Pe = P.asExplicit();
    expect(String(Pe)).toBe('Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])');
    const Mv = Matrix.col(0, 1, 2);
    expect(String(Pe.mul(Mv))).toBe('Matrix([[1], [2], [0]])');
    expect(String(Mv.T.mul(Pe))).toBe('Matrix([[2, 0, 1]])');
    expect(String(M(P.mul(Mv)).asExplicit())).toBe('Matrix([[1], [2], [0]])');
    expect(s(P)).toBe('PermutationMatrix((0 1 2))');
    expect(L(P)).toBe('P_{\\left( 0\\; 1\\; 2\\right)}');
    expect(s(P.T)).toBe('PermutationMatrix((0 2 1))');
    expect(s(P.I)).toBe('PermutationMatrix((0 2 1))');
    expect(s(P.pow(2))).toBe('PermutationMatrix((0 2 1))');
    expect(s(P.mul(P))).toBe('PermutationMatrix((0 2 1))');
    expect(s(det(P))).toBe('1');
    expect(s(det(PermutationMatrix([1, 0])))).toBe('-1');
    expect(s(PermutationMatrix([0, 1, 2]).doit())).toBe('I');
    expect(s(PermutationMatrix([1, 0, 3, 2]).rewriteAsBlockDiagMatrix())).toBe('Matrix([[PermutationMatrix((0 1)), 0], [0, PermutationMatrix((0 1))]])');
  });
});

describe('sets', () => {
  it('MatrixSet', () => {
    const Ms = MatrixSet(2, 2, Reals);
    expect(Ms.contains(Matrix.of([[1, 2], [3, 4]]))).toBe(true);
    expect(Ms.contains(Matrix.of([[1, 2], [S.I, 4]]))).toBe(false);
    expect(s(Ms)).toBe('MatrixSet(2, 2, Reals)');
    expect(MatrixSet(symbol('n'), 2, Reals).contains(Matrix.of([[1, 2]]))).toBe('unknown');
    expect(Ms.contains(MatrixSymbol('Y', 2, 2))).toBe('unknown');
  });
});

describe('slice', () => {
  it('MatrixSlice', () => {
    const Mx = ImmutableMatrix(4, 4, Array.from({ length: 16 }, (_, k) => k));
    expect(s(Mx)).toBe('Matrix([[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]])');
    const B = MatrixSlice(Mx, [0, 2], [2, 4]);
    expect(String(M(B).asExplicit())).toBe('Matrix([[2, 3], [6, 7]])');
  });
  it('mat_slice_of_slice', () => {
    const X = MatrixSymbol('X', 10, 10);
    expect(s(M(X.slice([null, null], [1, 5])).slice([5, 8], [null, null]))).toBe('X[5:8, 1:5]');
    expect(s(M(X.slice([1, 9, 2], [2, 6])).slice([1, 3], 2))).toBe('X[3:7:2, 4:5]');
  });
  it('printing', () => {
    const n = symbol('n');
    const A = MatrixSymbol('A', n, n);
    expect(s(A.slice([1, 3], 2))).toBe('A[1:3, 2:3]');
    expect(L(A.slice([1, 3], 2))).toBe('A\\left[1:3, 2:3\\right]');
    expect(s(M(A.mul(MatrixSymbol('B', n, n))).slice([null, null], 1))).toBe('(A*B)[:, 1:2]');
    expect(M(A.slice([0, 2], [0, 3])).shape.map(s)).toEqual(['2', '3']);
  });
});

describe('special', () => {
  it('Identity', () => {
    const A = MatrixSymbol('A', 3, 5);
    expect(s(Identity(3).mul(A))).toBe('A');
    expect(L(Identity(3))).toBe('\\mathbb{I}');
    expect(s(Identity(3).at(1, 1))).toBe('1');
    const [i, j] = symbols('i j');
    // SymPy: KroneckerDelta(i, j, (0, 2)); the base module's KroneckerDelta has no range argument
    expect(s(Identity(3).at(i, j))).toBe('KroneckerDelta(i, j)');
  });
  it('ZeroMatrix', () => {
    const A = MatrixSymbol('A', 3, 5);
    const Z = ZeroMatrix(3, 5);
    expect(s(A.add(Z))).toBe('A');
    expect(s(Z.mul(A.T))).toBe('0');
    expect(() => ZeroMatrix(2, 2).I).toThrow('Matrix det == 0; not invertible.');
  });
  it('OneMatrix', () => {
    const [n, m] = symbols('n m');
    expect(s(OneMatrix(n, m))).toBe('1');
    expect(s(M(OneMatrix(1, 1)).doit())).toBe('I');
    expect(s(M(OneMatrix(n, n)).pow(3))).toBe('n**2*1');
    expect(s(M(OneMatrix(n, m)).mul(OneMatrix(m, n)))).toBe('m*1');
    expect(s(trace(OneMatrix(n, n)))).toBe('n');
    expect(s(det(OneMatrix(2, 2)))).toBe('0');
  });
});

describe('trace', () => {
  it('Trace', () => {
    const A = MatrixSymbol('A', 3, 3);
    expect(s(Trace(A))).toBe('Trace(A)');
    expect(s(Trace(eye(3)))).toBe('Trace(Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]]))');
    expect(s(Trace(eye(3)).simplify())).toBe('3');
    expect(L(Trace(A))).toBe('\\operatorname{tr}\\left(A \\right)');
  });
  it('trace', () => {
    const n = symbol('n');
    const X = MatrixSymbol('X', n, n);
    expect(s(trace(MatMul(2, X)))).toBe('2*Trace(X)');
    expect(s(trace(eye(3)))).toBe('3');
    expect(s(trace(X.T))).toBe('Trace(X)');
    expect(s(trace(Identity(n)))).toBe('n');
    expect(s(trace(M(X.add(X)).add(MatrixSymbol('Y', n, n))))).toBe('2*Trace(X) + Trace(Y)');
    expect(s(trace(Adjoint(X)))).toBe('conjugate(Trace(X))');
    expect(s(Trace(X.add(X)).simplify())).toBe('2*Trace(X)');
  });
});

describe('transpose', () => {
  it('Transpose and transpose', () => {
    const A = MatrixSymbol('A', 3, 5);
    const B = MatrixSymbol('B', 5, 3);
    expect(s(Transpose(A))).toBe('A.T');
    expect(A.T.equals(transpose(A))).toBe(true);
    expect(transpose(A).equals(Transpose(A))).toBe(true);
    expect(s(Transpose(A.mul(B)))).toBe('(A*B).T');
    expect(s(transpose(A.mul(B)))).toBe('B.T*A.T');
  });
  it('refine_Transpose', () => {
    const X = MatrixSymbol('X', 2, 2);
    expect(s(X.T)).toBe('X.T');
    expect(s(refineMatrix(X.T, MatrixQ.symmetric(X)))).toBe('X');
    expect(askMatrix(MatrixQ.symmetric(X.mul(X.T)))).toBe(true);
    expect(askMatrix(MatrixQ.invertible(X), MatrixQ.orthogonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.invertible(ZeroMatrix(2, 2)))).toBe(false);
    expect(askMatrix(MatrixQ.invertible(X))).toBe('unknown');
  });
});

describe('factorizations', () => {
  it('lu, qr, eig, svd', () => {
    const n = symbol('n');
    const X = MatrixSymbol('X', n, n);
    expect(lu(X).map(s)).toEqual(['LofLU(X)', 'UofLU(X)']);
    expect(qr(X).map(s)).toEqual(['QofQR(X)', 'RofQR(X)']);
    expect(eig(X).map(s)).toEqual(['EigenValues(X)', 'EigenVectors(X)']);
    expect(svd(X).map(s)).toEqual(['UofSVD(X)', 'SofSVD(X)', 'VofSVD(X)']);
    expect(lu(X)[0].predicates).toEqual(['lower_triangular']);
    expect(lu(X)[0].shape.map(s)).toEqual(['n', 'n']);
  });
});

describe('printing like SymPy', () => {
  const [n, x] = symbols('n x');
  const A = MatrixSymbol('A', n, n);
  const B = MatrixSymbol('B', n, n);
  const C = MatrixSymbol('C', n, n);
  const cases: [() => unknown, string, string][] = [
    [() => A.add(B), 'A + B', 'A + B'],
    [() => B.add(A), 'A + B', 'A + B'],
    [() => M(A.T).add(B), 'B + A.T', 'B + A^{T}'],
    [() => M(MatMul(2, A)).add(B), '2*A + B', '2 A + B'],
    [() => B.sub(A), '-A + B', '- A + B'],
    [() => A.sub(B), 'A - B', 'A - B'],
    [() => M(A.neg()).sub(B), '-A - B', '- A - B'],
    [() => M(A.mul(B)).add(C), 'A*B + C', 'A B + C'],
    [() => Identity(n).add(A), 'I + A', '\\mathbb{I} + A'],
    [() => A.add(ZeroMatrix(n, n)), 'A', 'A'],
    [() => M(A.pow(2)).add(A), 'A**2 + A', 'A^{2} + A'],
    [() => M(A.I).add(B), 'A**(-1) + B', 'A^{-1} + B'],
    [() => M(MatMul(Trace(A), B)).add(A), 'Trace(A)*B + A', '\\operatorname{tr}\\left(A \\right) B + A'],
    [() => M(A.mul(B)).sub(B.mul(A)), 'A*B - B*A', 'A B - B A'],
    [() => M(A.mul(x)).add(B), 'x*A + B', 'x A + B'],
    [() => MatMul(x.add(1), A), '(x + 1)*A', '\\left(x + 1\\right) A'],
    [() => MatMul(-2, A, B), '-2*A*B', '- 2 A B'],
    [() => MatMul(S.I, A), 'I*A', 'i A'],
    [() => MatMul(S.I.neg(), A), '-I*A', '- i A'],
    [() => M(A.T).mul(B), 'A.T*B', 'A^{T} B'],
    [() => M(A.mul(B)).T, 'B.T*A.T', 'B^{T} A^{T}'],
    [() => Transpose(A.mul(B)), '(A*B).T', '\\left(A B\\right)^{T}'],
    [() => Inverse(A.mul(B)), '(A*B)**(-1)', '\\left(A B\\right)^{-1}'],
    [() => M(A.add(B)).T, 'A.T + B.T', 'A^{T} + B^{T}'],
    [() => Transpose(A.add(B)), '(A + B).T', '\\left(A + B\\right)^{T}'],
    [() => Transpose(MatMul(2, A)), '(2*A).T', '\\left(2 A\\right)^{T}'],
    [() => MatPow(A, 2), 'A**2', 'A^{2}'],
    [() => MatPow(A.T, 2), 'A.T**2', '\\left(A^{T}\\right)^{2}'],
    [() => MatPow(A.mul(B), 2), '(A*B)**2', '\\left(A B\\right)^{2}'],
    [() => MatPow(A, x.add(1)), 'A**(x + 1)', 'A^{x + 1}'],
    [() => MatPow(A, -2), 'A**(-2)', 'A^{-2}'],
    [() => Adjoint(A.T), 'Adjoint(A.T)', '\\left(A^{T}\\right)^{\\dagger}'],
    [() => A.conjugate(), 'Adjoint(A.T)', '\\left(A^{T}\\right)^{\\dagger}'],
    [() => M(A.mul(B)).conjugate(), 'Adjoint((A*B).T)', '\\left(\\left(A B\\right)^{T}\\right)^{\\dagger}'],
    [() => A.at(0, 1), 'A[0, 1]', '{A}_{0,1}'],
    [() => M(A.mul(B)).at(0, 1), 'Sum(A[0, _i_1]*B[_i_1, 1], (_i_1, 0, n - 1))', ''],
    [() => M(A.add(B)).at(0, 1), 'A[0, 1] + B[0, 1]', '{A}_{0,1} + {B}_{0,1}'],
    [() => M(A.T).at(0, 1), 'A[1, 0]', '{A}_{1,0}'],
    [() => A.slice([0, 2], [1, 3]), 'A[:2, 1:3]', 'A\\left[:2, 1:3\\right]'],
    [() => M(A.I).T, 'A.T**(-1)', '\\left(A^{T}\\right)^{-1}'],
    [() => M(A.T).I, 'A.T**(-1)', '\\left(A^{T}\\right)^{-1}'],
    [() => Trace(A.mul(B)), 'Trace(A*B)', '\\operatorname{tr}\\left(A B \\right)'],
    [() => trace(A.add(B)), 'Trace(A) + Trace(B)', '\\operatorname{tr}\\left(A \\right) + \\operatorname{tr}\\left(B \\right)'],
    [() => trace(A.mul(B)), 'Trace(A*B)', '\\operatorname{tr}\\left(A B \\right)'],
    [() => det(A.mul(B)), 'Determinant(A)*Determinant(B)', '\\left|{A}\\right| \\left|{B}\\right|'],
    [() => det(MatMul(2, A)), '2**n*Determinant(A)', '2^{n} \\left|{A}\\right|'],
    [() => A.mul(Identity(n)), 'A', 'A'],
    [() => ZeroMatrix(n, n).mul(A), '0', '0'],
    [() => MatMul(x.neg(), A), '(-x)*A', '- x A'],
    [() => MatMul(mul(-2, x), A), '(-2*x)*A', '- 2 x A'],
    [() => MatMul(mul(x, symbol('y')), A), '(x*y)*A', 'x y A'],
    [() => A.div(2), '(1/2)*A', '\\left(\\frac{1}{2}\\right) A'],
    [() => M(A.neg()).div(2), '-(1/2)*A', '- \\frac{1}{2} A'],
    [() => MatMul(Rational.of(-3, 2), A, B), '-(3/2)*A*B', '- \\frac{3}{2} A B'],
    [() => MatMul(A, 2, B), 'A*2*B', 'A 2 B'],
    [() => MatMul(A, x, B, 3), 'A*x*B*3', 'A x B 3'],
    [() => M(MatMul(A, x, B, 3)).doit(), '(3*x)*A*B', '3 x A B'],
    [() => MatMul(S.I.add(1), A), '(1 + I)*A', '\\left(1 + i\\right) A'],
    [() => MatMul(S.I.add(1).neg(), A), '(-1 - I)*A', '\\left(-1 - i\\right) A'],
    [() => A.sub(MatMul(2, B)), 'A - 2*B', 'A - 2 B'],
    [() => A.sub(MatMul(x, B)), '(-x)*B + A', '- x B + A'],
    [() => M(MatMul(x, A)).sub(B), 'x*A - B', 'x A - B'],
    [() => A.sub(B.mul(C)), 'A - B*C', 'A - B C'],
    [() => M(M(A.mul(B)).neg()).sub(C), '-A*B - C', '- A B - C'],
    [() => MatMul(A, -1), '-A', 'A \\left(-1\\right)'],
    [() => M(MatMul(A, -1)).doit(), '-A', '- A'],
    [() => M(A.pow(-1)).mul(B), 'A**(-1)*B', 'A^{-1} B'],
    [() => M(A.T).neg(), '-A.T', '- A^{T}'],
    [() => M(A.pow(2)).neg(), '-A**2', '- A^{2}'],
    [() => M(MatMul(mul(-1, Trace(A)), B)), '(-Trace(A))*B', '- \\operatorname{tr}\\left(A \\right) B'],
    [() => M(MatMul(Trace(A), B)).sub(A), 'Trace(A)*B - A', '\\operatorname{tr}\\left(A \\right) B - A'],
    [() => M(A.add(B)).neg(), '-A - B', '- A - B'],
    [() => MatMul(-1, A.add(B)), '-(A + B)', '- \\left(A + B\\right)'],
    [() => M(MatMul(2, A.add(B))).doit(), '2*A + 2*B', '2 A + 2 B'],
    [() => M(MatMul(x, A.add(B))).doit(), 'x*(A + B)', 'x \\left(A + B\\right)'],
    [() => M(MatMul(Rational.of(1, 2), A.add(B))).doit(), '(1/2)*A + (1/2)*B', '\\left(\\frac{1}{2}\\right) A + \\left(\\frac{1}{2}\\right) B'],
    [() => MatAdd(MatrixSymbol('P', 2, 2), eye(2), Matrix.of([[1, 2], [3, 4]])), 'Matrix([[1, 0], [0, 1]]) + Matrix([[1, 2], [3, 4]]) + P', '\\left[\\begin{matrix}1 & 0\\\\0 & 1\\end{matrix}\\right] + \\left[\\begin{matrix}1 & 2\\\\3 & 4\\end{matrix}\\right] + P'],
    [() => Trace(eye(2)), 'Trace(Matrix([[1, 0], [0, 1]]))', '\\operatorname{tr}\\left(\\left[\\begin{matrix}1 & 0\\\\0 & 1\\end{matrix}\\right] \\right)'],
    [() => Determinant(eye(2)), 'Determinant(Matrix([[1, 0], [0, 1]]))', '\\left|{\\begin{matrix}1 & 0\\\\0 & 1\\end{matrix}}\\right|'],
    [() => Adjoint(A.add(B)), 'Adjoint(A + B)', '\\left(A + B\\right)^{\\dagger}'],
    [() => MatrixElement(A.mul(B), 0, 1), '(A*B)[0, 1]', '{\\left(A B\\right)}_{0,1}'],
    [() => OneMatrix(n, n), '1', '1'],
  ];
  it.each(cases.map((c, k) => [k, ...c] as const))('case %i', (_k, f, str0, tex) => {
    const e = f();
    expect(s(e)).toBe(str0);
    if (tex) expect(L(e)).toBe(tex);
  });
});

describe('evaluation like SymPy', () => {
  const [n, x] = symbols('n x');
  const A = MatrixSymbol('A', n, n);
  const B = MatrixSymbol('B', n, n);
  it('canonical products and powers', () => {
    expect(s(A.mul(A))).toBe('A**2');
    expect(s(M(A.mul(A)).mul(A))).toBe('A**3');
    expect(s(M(A.I).mul(A))).toBe('I');
    expect(s(A.mul(A.I))).toBe('I');
    expect(s(M(A.mul(B)).mul(Inverse(A.mul(B))))).toBe('I');
    expect(s(M(MatPow(A, 2)).pow(3))).toBe('A**6');
    expect(s(M(MatPow(A, 0)).doit())).toBe('I');
    expect(s(M(A.I).I)).toBe('A');
    expect(s(M(A.T).T)).toBe('A');
    expect(s(MatMul(0, A))).toBe('0*A');
    expect(s(M(MatMul(0, A)).doit())).toBe('0');
    expect(s(M(A.mul(2)).mul(3))).toBe('6*A');
    expect(s(M(MatAdd(A, A)).doit())).toBe('2*A');
    expect(s(M(A.add(B)).sub(A))).toBe('B');
  });
  it('expand, simplify and diff', () => {
    expect(s(M(MatMul(A.add(B), A)).expand())).toBe('A**2 + B*A');
    expect(s(M(MatMul(A.add(B), A.sub(B))).expand())).toBe('A**2 - B**2 - A*B + B*A');
    expect(s(M(MatMul(x, A.add(B))).expand())).toBe('x*A + x*B');
    expect(s(M(MatAdd(A, A)).simplify())).toBe('A + A');
    expect(s(M(MatMul(x, A)).diff(x))).toBe('A');
    expect(s(M(MatMul(x.pow(2), A)).diff(x))).toBe('(2*x)*A');
    expect(s(M(MatMul(x, A, B)).diff(x))).toBe('A*B');
    expect(s(A.diff(x))).toBe('0');
    expect(s(Trace(MatMul(x, A)).diff(x))).toBe('Trace(A)');
    expect(s(M(M(MatMul(x, A)).add(B)).diff(x))).toBe('A');
    expect(s(M(MatMul(x, A)).T.diff(x))).toBe('A.T');
    expect(s(mul(x, A.at(0, 1)).diff(A.at(0, 1) as never))).toBe('x');
    expect(s(A.at(0, 1).diff(A.at(1, 1) as never))).toBe('0');
    expect(s(A.at(0, 1).diff(A.at(0, 1) as never))).toBe('1');
  });
  it('substitution and dimensions', () => {
    const k = new Dummy('k');
    expect(s(A.subs(n, 3))).toBe('A');
    expect(M(A.subs(n, 3)).shape.map(s)).toEqual(['3', '3']);
    expect(M(Identity(n).subs(n, 2)).asExplicit().toString()).toBe('Matrix([[1, 0], [0, 1]])');
    expect(s(Eq(k, k))).toBe('True');
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
  it('kronecker, hadamard and applyfunc details', () => {
    expect(s(det(KroneckerProduct(P, Q)))).toBe('Determinant(P)**k*Determinant(Q)**k');
    expect(s(kroneckerProduct(P, Matrix.of([[1, 2]])))).toBe('KroneckerProduct(P, Matrix([[1, 2]]))');
    expect(s(combineKronecker(M(KroneckerProduct(P, Q)).add(R)))).toBe('KroneckerProduct(P, Q) + R');
    expect(s(HadamardPower(2, 3))).toBe('8');
    expect(s(hadamardPower(P, 2))).toBe('HadamardPower(P, 2)');
    expect(s(M(HadamardPower(P, 2)).T)).toBe('HadamardPower(P.T, 2)');
    expect(s(ElementwiseApplyFunction(sin, MatrixSymbol('Y', 1, 1)))).toBe('Lambda(_d, sin(_d)).(Y)');
    expect(s(M(ElementwiseApplyFunction(sin, Matrix.of([[1, 2]]))).doit())).toBe('Matrix([[sin(1), sin(2)]])');
    const [i, j] = symbols('i j');
    expect(String(FunctionMatrix(2, 2, Lambda([i, j], i.mul(2))).asExplicit())).toBe('Matrix([[0, 0], [2, 2]])');
  });
  it('special matrices', () => {
    expect([OneMatrix(n, n).I, OneMatrix(2, 2).T, OneMatrix(n, m).T, ZeroMatrix(n, m).T, Identity(n).T, Identity(n).I, M(ZeroMatrix(n, n)).pow(2), Identity(n).pow(5)].map(s)).toEqual(['1**(-1)', '1', '1', '0', 'I', 'I', '0', 'I']);
    expect([Inverse(Identity(n)), Transpose(Identity(n)), MatPow(Identity(n), 2)].map(L)).toEqual(['\\left(\\mathbb{I}\\right)^{-1}', '\\left(\\mathbb{I}\\right)^{T}', '\\left(\\mathbb{I}\\right)^{2}']);
  });
  it('powers, inverses, transposes and adjoints', () => {
    expect(s(A.pow(Rational.of(1, 2)))).toBe('A**(1/2)');
    expect(L(A.pow(Rational.of(1, 2)))).toBe('A^{\\frac{1}{2}}');
    expect([MatPow(A, 2).T, MatPow(A, 2).I, Adjoint(MatPow(A, 2)).doit(), MatPow(A, 2).conjugate()].map(s)).toEqual(['A.T**2', 'A**(-2)', 'Adjoint(A)**2', 'Adjoint(A.T)**2']);
    expect([Inverse(A).T, Inverse(A).conjugate(), Adjoint(Inverse(A)).doit(), det(Inverse(A)), det(A.T), Transpose(A).conjugate(), Adjoint(A.T).doit(), trace(Inverse(A))].map(s)).toEqual([
      'A.T**(-1)',
      'Adjoint(A.T)**(-1)',
      'Adjoint(A)**(-1)',
      '1/Determinant(A)',
      'Determinant(A)',
      'Adjoint(A)',
      'Adjoint(A.T)',
      'Trace(A**(-1))',
    ]);
    expect(s(Trace(A).rewriteAsSum())).toBe('Sum(A[i, i], (i, 0, n - 1))');
  });
  it('permutations', () => {
    const p = PermutationNode.fromCycles([[1, 2, 0]]);
    const X = MatrixSymbol('X', 3, 3);
    expect(s(MatrixPermute(MatrixPermute(X, p, 0), p, 0).doit())).toBe('MatrixPermute(X, (0 2 1), 0)');
    expect(s(MatrixPermute(X, p, 0).rewriteAsMatMul())).toBe('PermutationMatrix((0 1 2))*X');
    expect(s(MatrixPermute(X, p, 1).rewriteAsMatMul())).toBe('X*PermutationMatrix((0 2 1))');
    expect(s(MatrixPermute(ZeroMatrix(3, 3), p).doit())).toBe('0');
    expect(s(p)).toBe('(0 1 2)');
    expect(s(PermutationNode.from([1, 0, 2]))).toBe('(2)(0 1)');
    expect(s(PermutationNode.from([0, 1, 2]))).toBe('(2)');
    expect(L(PermutationMatrix([1, 0, 2]))).toBe('P_{\\left( 0\\; 1\\right)\\left( 2\\right)}');
  });
  it('DFT LaTeX', () => {
    expect(L(DFT(n))).toBe('\\text{DFT}_{n}');
  });
});
