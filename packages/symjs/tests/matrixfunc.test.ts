// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Matrix, analyticFunc, log, matrixLog, symbols } from '../src';

const [x] = symbols('x');

describe('matrix functions (SymPy Matrix.log / analytic_func)', () => {
  it('log of a non-diagonalizable matrix', () => {
    expect(String(matrixLog(Matrix.of([[1, 1], [0, 1]])))).toBe('Matrix([[0, 1], [0, 0]])');
  });
  it('log of a symmetric matrix', () => {
    expect(String(matrixLog(Matrix.of([[5, 3], [3, 5]])))).toBe('Matrix([[0, log(2)], [log(2), 0]])');
    expect(String(matrixLog(Matrix.of([[3, 5], [5, 3]])))).toBe('Matrix([[I*pi/2, log(2) - I*pi/2], [log(2) - I*pi/2, I*pi/2]])');
  });
  it('analytic_func with an explicit function', () => {
    expect(String(analyticFunc(Matrix.of([[5, 3], [3, 5]]), log(x), x))).toBe('Matrix([[0, log(2)], [log(2), 0]])');
  });
});
