// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/indexsum.ts.
//
// from_index_summation: matrix expressions recovered from index summations. Expected values are SymPy
// 1.14 results.

import { describe, expect, it } from 'vitest';
import { type Expr, mul, sstr, Sum, symbol, symbols } from '../../../src';
import { fromIndexSummation, MatrixSymbol } from '../../../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const [, i, j, k] = symbols('n i j k', { integer: true });

describe('matexpr', () => {
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
});

describe('from_index_summation', () => {
  const N = symbol('N', { integer: true });
  const [l] = symbols('l', { integer: true });
  const An = MatrixSymbol('A', N, N);
  const Bn = MatrixSymbol('B', N, N);
  const Cn = MatrixSymbol('C', N, N);
  const Nm1 = N.sub(1);
  const ab = mul(An.at(i, j), Bn.at(j, k));
  it('errors', () => {
    // SymPy gives j*A*B, which drops the dependence of the coefficient on the summation index
    expect(() => fromIndexSummation(Sum(mul(j, ab), [j, 0, Nm1]))).toThrow('cannot convert j');
    expect(() => fromIndexSummation(Sum(ab, [j, 0, N.sub(2)]))).toThrow('summation index and array dimension mismatch: j');
    expect(() => fromIndexSummation(Sum(ab, [j, 1, Nm1]))).toThrow('summation index and array dimension mismatch: j');
    // SymPy gives the array expressions ArrayDiagonal(ArrayTensorProduct(A, B), (1, 2)) and ArrayTensorProduct(A, B)
    expect(() => fromIndexSummation(ab)).toThrow('an index appears twice without summation');
    expect(() => fromIndexSummation(mul(An.at(i, j), Bn.at(k, l)))).toThrow('unsupported index structure');
  });
  it('first and last indices', () => {
    // SymPy gives A*B for last_index=i and B.T*A.T for last_index=k, the transposes of
    // the matrices whose row index is the other free index
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), undefined, i))).toBe('B.T*A.T');
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), undefined, k))).toBe('A*B');
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), k, i))).toBe('B.T*A.T');
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), k))).toBe('B.T*A.T');
  });
  it('sums', () => {
    // SymPy raises TypeError (Mix of Matrix and Scalar symbols)
    expect(s(fromIndexSummation(Sum(An.at(i, i).add(Bn.at(i, i)), [i, 0, Nm1])))).toBe('Trace(A) + Trace(B)');
    // SymPy raises IndexError; the constant is summed N times
    expect(s(fromIndexSummation(Sum(An.at(i, i).add(2), [i, 0, Nm1])))).toBe('2*N + Trace(A)');
    // SymPy gives A*B + C; C[i, k] does not depend on j and is summed N times
    expect(s(fromIndexSummation(Sum(ab.add(Cn.at(i, k)), [j, 0, Nm1])))).toBe('N*C + A*B');
    expect(s(fromIndexSummation(Sum(mul(3, An.at(i, i)), [i, 0, Nm1])))).toBe('3*Trace(A)');
  });
});

describe('remaining branches (SymPy 1.14)', () => {
  it('from_index_summation of an open chain of indices', () => {
    const N = symbol('N', { integer: true });
    const An = MatrixSymbol('A', N, N);
    const Bn = MatrixSymbol('B', N, N);
    // SymPy raises IndexError
    expect(() => fromIndexSummation(Sum(mul(An.at(i, j), Bn.at(j, j)), [i, 0, N.sub(1)], [j, 0, N.sub(1)]))).toThrow('unsupported index structure');
  });
});
