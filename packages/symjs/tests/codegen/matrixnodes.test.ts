// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { diff, Matrix, MatrixSolve, MatrixSymbol, symbol } from '../../src';

it('represents and rebuilds a symbolic linear solve', () => {
  const A = MatrixSymbol('A', 2, 2), b = MatrixSymbol('b', 2, 1);
  const solve = MatrixSolve(A, b);
  expect(solve.shape.map(String)).toEqual(['2', '1']);
  expect(String(solve)).toBe('MatrixSolve(A, vector=b)');
  expect(solve.withArgs([A, b])).toEqual(solve);
  const x = symbol('x');
  const explicit = MatrixSolve(Matrix.of([[x]]), Matrix.of([[1]]));
  expect(explicit.printRepr()).toContain("ImmutableDenseMatrix([[Symbol('x')]])");
  expect(String(diff(explicit, x))).toBe('MatrixSolve(Matrix([[x]]), vector=-MatrixSolve(Matrix([[x]]), vector=Matrix([[1]])))');
});
