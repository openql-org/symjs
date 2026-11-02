// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Matrix, Rational, analyticFunc, log, matrixLog, symbols } from '../src';

const q = (n: number) => Rational.of(n, 4);

const [x] = symbols('x');

describe('matrix functions (SymPy Matrix.log / analytic_func)', () => {
  it('log of a non-diagonalizable matrix', () => {
    expect(String(matrixLog(Matrix.of([[1, 1], [0, 1]])))).toBe('Matrix([[0, 1], [0, 0]])');
  });
  it('log of a symmetric matrix', () => {
    expect(String(matrixLog(Matrix.of([[q(5), q(3)], [q(3), q(5)]])))).toBe('Matrix([[0, log(2)], [log(2), 0]])');
    expect(String(matrixLog(Matrix.of([[q(3), q(5)], [q(5), q(3)]])))).toBe('Matrix([[I*pi/2, log(2) - I*pi/2], [log(2) - I*pi/2, I*pi/2]])');
  });
  it('analytic_func with an explicit function', () => {
    expect(String(analyticFunc(Matrix.of([[q(5), q(3)], [q(3), q(5)]]), log(x), x))).toBe('Matrix([[0, log(2)], [log(2), 0]])');
  });
});
