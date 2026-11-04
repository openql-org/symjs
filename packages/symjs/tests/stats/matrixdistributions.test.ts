// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/matrixdistributions.ts (SymPy
// sympy/stats/matrix_distributions.py, its doctests and
// sympy/stats/tests/test_matrix_distributions.py). Expected values are
// those of SymPy 1.14; SymPy prints explicit matrices on several lines,
// they are written here on one line as symjs prints them.

import { describe, expect, it } from 'vitest';
import { Matrix, MatrixSet, MatrixSymbol, Reals, Sym, doit, str } from '../../src';
import type { Expr } from '../../src';
import { density } from '../../src/stats';
import { RandomMatrixSymbol } from '../../src/stats/rv';
import {
  MatrixGamma,
  MatrixGammaDistribution,
  MatrixNormal,
  MatrixPSpace,
  MatrixStudentT,
  Wishart,
  WishartDistribution,
  toMatrixArg,
} from '../../src/stats/matrixdistributions';
import type { MatrixDistribution, MatrixInput } from '../../src/stats/matrixdistributions';

const dens = (X: Expr): MatrixDistribution => density(X) as MatrixDistribution;
const at = (X: Expr, x: MatrixInput): string => str(doit(dens(X).call(x)));
const pspaceOf = (X: Expr): MatrixPSpace => (X as RandomMatrixSymbol).pspace as MatrixPSpace;

describe('MatrixPSpace', () => {
  it('space, domain and value', () => {
    const M = new MatrixGammaDistribution([toMatrixArg(1), toMatrixArg(2), toMatrixArg([[2, 1], [1, 2]])]);
    const MP = new MatrixPSpace([new Sym('M'), M, toMatrixArg(2), toMatrixArg(2)]);
    expect(MP.distribution).toBe(M);
    expect(str(MP)).toBe('MatrixPSpace(M, MatrixGammaDistribution(1, 2, Matrix([[2, 1], [1, 2]])), 2, 2)');
    expect(str(MP.domain)).toBe('Domain: {M} in MatrixSet(2, 2, Reals)');
    expect(str(MP.value)).toBe('M');
    expect(() => new MatrixPSpace([new Sym('M'), M, toMatrixArg(1.2), toMatrixArg(2)])).toThrow('Dimensions should be integers');
    expect(() => new MatrixPSpace([new Sym('M'), M, toMatrixArg(2), toMatrixArg(1.2)])).toThrow('Dimensions should be integers');
  });
  it('densities of expressions', () => {
    const M = MatrixGamma('M', 1, 2, [[1, 0], [0, 1]]);
    const M3 = MatrixGamma('M3', 2, 3, [[2, 1], [1, 2]]);
    // SymPy: NotImplementedError for a sum of random matrices and for an expression of one
    expect(() => density(M.add(M3))).toThrow('multiple matrix distributions');
    expect(() => density(M.mul(2))).toThrow('multiple matrix distributions');
    expect(str(doit(pspaceOf(M).computeDensity(M) as Expr))).toBe(str(doit(dens(M).call(M))));
  });
  it('undecided checks pass (SymPy _value_check of None)', () => {
    const [x, n, m] = [new Sym('x'), new Sym('n', { integer: true }), new Sym('m', { integer: true })];
    expect(str(MatrixGamma('M', 1, 2, [[x, 0], [0, 1]]))).toBe('M');
    expect(str(MatrixGamma('M', 1, 2, MatrixSymbol('S', n, m)))).toBe('M');
  });
  it('matrix arguments', () => {
    expect(str(toMatrixArg([4]))).toBe('Matrix([[4]])');
    expect(str(toMatrixArg(Matrix.of([[1, 2]])))).toBe('Matrix([[1, 2]])');
    expect(() => toMatrixArg([[1, 0], [0]])).toThrow('mismatched dimensions');
  });
});

describe('MatrixGamma', () => {
  it('density (test_MatrixGamma)', () => {
    const M = MatrixGamma('M', 1, 2, [[1, 0], [0, 1]]);
    expect(pspaceOf(M).distribution.set.key).toBe(MatrixSet(2, 2, Reals).key);
    expect(density(M)).toBeInstanceOf(MatrixGammaDistribution);
    const X = MatrixSymbol('X', 2, 2);
    expect(str(dens(M).call(X))).toBe('exp(Trace(Matrix([[-1/2, 0], [0, -1/2]])*X))/(4*pi*Determinant(Matrix([[1, 0], [0, 1]]))*sqrt(Determinant(X)))');
    expect(at(M, X)).toBe('exp(Trace(Matrix([[-1/2, 0], [0, -1/2]])*X))/(4*pi*sqrt(Determinant(X)))');
    expect(at(M, [[2, 1], [1, 2]])).toBe('sqrt(3)*exp(-2)/(12*pi)');
    const X1 = MatrixSymbol('X', 1, 2);
    const Y1 = MatrixSymbol('Y', 1, 2);
    expect(at(M, [X1, Y1])).toBe('exp(-X[0, 0]/2 - Y[0, 1]/2)/(4*pi*sqrt(X[0, 0]*Y[0, 1] - X[0, 1]*Y[0, 0]))');
    expect(() => dens(M).call(1)).toThrow('1 should be an isinstance of Matrix or MatrixSymbol');
  });
  it('symbolic', () => {
    const [a, b] = [new Sym('a', { positive: true }), new Sym('b', { positive: true })];
    const d = new Sym('d', { positive: true, integer: true });
    const Y = MatrixSymbol('Y', d, d);
    const SM = MatrixSymbol('SM', d, d);
    const M2 = MatrixGamma('M2', a, b, SM);
    expect(str(dens(M2).call(Y))).toBe(
      'exp(Trace((-1/b)*SM**(-1)*Y))*Determinant(Y)**(a - d/2 - 1/2)/(pi**(d*(d - 1)/4)*b**(a*d)*Determinant(SM)**a*Product(gamma(-_k/2 + a + 1/2), (_k, 1, d)))',
    );
  });
  it('doctest', () => {
    const [a, b] = [new Sym('a', { positive: true }), new Sym('b', { positive: true })];
    const M = MatrixGamma('M', a, b, [[2, 1], [1, 2]]);
    const X = MatrixSymbol('X', 2, 2);
    expect(at(M, X)).toBe('exp(Trace(Matrix([[-2/3, 1/3], [1/3, -2/3]])*X)/b)*Determinant(X)**(a - 3/2)/(3**a*sqrt(pi)*b**(2*a)*gamma(a)*gamma(a - 1/2))');
    expect(at(M, [[1, 0], [0, 1]])).toBe('exp(-4/(3*b))/(3**a*sqrt(pi)*b**(2*a)*gamma(a)*gamma(a - 1/2))');
  });
  it('parameter checks', () => {
    expect(() => MatrixGamma('M', -1, 2, [[1, 0], [0, 1]])).toThrow('Shape parameter should be positive.');
    expect(() => MatrixGamma('M', 1, -2, [[1, 0], [0, 1]])).toThrow('Scale parameter should be positive.');
    expect(() => MatrixGamma('M', -1, 2, [[1, 0], [2, 1]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixGamma('M', -1, 2, [[1, 0], [0]])).toThrow('mismatched dimensions');
    expect(() => MatrixGamma('M', 1, 2, MatrixSymbol('S', 2, 3))).toThrow('Should be square matrix');
  });
});

describe('Wishart', () => {
  it('density (test_Wishart)', () => {
    const W = Wishart('W', 5, [[1, 0], [0, 1]]);
    expect(str(pspaceOf(W).distribution.set)).toBe('MatrixSet(2, 2, Reals)');
    const X = MatrixSymbol('X', 2, 2);
    expect(at(W, X)).toBe('exp(Trace(Matrix([[-1/2, 0], [0, -1/2]])*X))*Determinant(X)/(24*pi)');
    expect(at(W, [[2, 1], [1, 2]])).toBe('exp(-2)/(8*pi)');
    expect((density(W) as WishartDistribution).dof.toString()).toBe('5');
    const n = new Sym('n', { positive: true });
    const d = new Sym('d', { positive: true, integer: true });
    const W2 = Wishart('W', n, MatrixSymbol('SM', d, d));
    expect(str(dens(W2).call(MatrixSymbol('Y', d, d)))).toBe(
      'exp(Trace(-(1/2)*SM**(-1)*Y))*Determinant(Y)**(-d/2 + n/2 - 1/2)/(2**(d*n/2)*pi**(d*(d - 1)/4)*Determinant(SM)**(n/2)*Product(gamma(-_k/2 + n/2 + 1/2), (_k, 1, d)))',
    );
    expect(() => dens(W2).call(1)).toThrow('should be an isinstance of Matrix or MatrixSymbol');
    expect(() => Wishart('W', -1, [[1, 0], [0, 1]])).toThrow('Shape parameter should be positive.');
    expect(() => Wishart('W', -1, [[1, 0], [2, 1]])).toThrow('positive definite');
    expect(() => Wishart('W', 2, [[1, 0], [0]])).toThrow('mismatched dimensions');
    expect(() => Wishart('W', 2, MatrixSymbol('S', 2, 3))).toThrow('Should be square matrix');
  });
  it('doctest', () => {
    const n = new Sym('n', { positive: true });
    const W = Wishart('W', n, [[2, 1], [1, 2]]);
    const X = MatrixSymbol('X', 2, 2);
    expect(at(W, X)).toBe('exp(Trace(Matrix([[-1/3, 1/6], [1/6, -1/3]])*X))*Determinant(X)**(n/2 - 3/2)/(2**n*3**(n/2)*sqrt(pi)*gamma(n/2)*gamma(n/2 - 1/2))');
    expect(at(W, [[1, 0], [0, 1]])).toBe('exp(-2/3)/(2**n*3**(n/2)*sqrt(pi)*gamma(n/2)*gamma(n/2 - 1/2))');
  });
});

describe('MatrixNormal', () => {
  it('density (test_MatrixNormal)', () => {
    const M = MatrixNormal('M', [[5, 6]], [4], [[2, 1], [1, 2]]);
    expect(str(pspaceOf(M).distribution.set)).toBe('MatrixSet(1, 2, Reals)');
    const X = MatrixSymbol('X', 1, 2);
    expect(at(M, X)).toBe('sqrt(3)*exp(-Trace(Matrix([[2/3, -1/3], [-1/3, 2/3]])*(Matrix([[-5], [-6]]) + X.T)*Matrix([[1/4]])*(Matrix([[-5, -6]]) + X))/2)/(24*pi)');
    expect(at(M, [[7, 8]])).toBe('sqrt(3)*exp(-1/3)/(24*pi)');
    const [d, n] = [new Sym('d', { positive: true, integer: true }), new Sym('n', { positive: true, integer: true })];
    const M2 = MatrixNormal('M', MatrixSymbol('LM', n, d), MatrixSymbol('SM1', n, n), MatrixSymbol('SM2', d, d));
    expect(at(M2, MatrixSymbol('Y', n, d))).toBe('exp(-Trace(SM2**(-1)*(-LM.T + Y.T)*SM1**(-1)*(-LM + Y))/2)/((2*pi)**(d*n/2)*Determinant(SM1)**(d/2)*Determinant(SM2)**(n/2))');
    expect(() => dens(M2).call(1)).toThrow('should be an isinstance of Matrix or MatrixSymbol');
  });
  it('parameter checks', () => {
    expect(() => MatrixNormal('M', [1, 2], [[1, 0], [0, 1]], [[1, 0], [2, 1]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixNormal('M', [1, 2], [[1, 0], [2, 1]], [[1, 0], [0, 1]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixNormal('M', [1, 2], [[1, 0], [0, 1]], [[1, 0], [0, 1]])).toThrow('Scale matrix 2 should be of shape 1 x 1');
    expect(() => MatrixNormal('M', [1, 2], [[1, 0], [2]], [[1, 0], [0, 1]])).toThrow('mismatched dimensions');
    expect(() => MatrixNormal('M', [[1, 2]], [[1, 0], [0, 1]], [[1, 0]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixNormal('M', [[1, 2]], [1], [[1, 0]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixNormal('M', [[1, 2]], [[1, 0], [0, 1]], [1])).toThrow('Scale matrix 1 should be of shape 1 x 1');
    expect(() => MatrixNormal('M', [[1, 2]], [1], MatrixSymbol('V', 2, 1))).toThrow('Scale matrix 2 should be be square matrix');
    expect(() => MatrixNormal('M', [[1, 2]], MatrixSymbol('U', 1, 2), [[1, 0], [0, 1]])).toThrow('Scale matrix 1 should be be square matrix');
  });
  it('doctest', () => {
    const M = MatrixNormal('M', [[1, 2]], [1], [[1, 0], [0, 1]]);
    const X = MatrixSymbol('X', 1, 2);
    expect(at(M, X)).toBe('exp(-Trace((Matrix([[-1], [-2]]) + X.T)*(Matrix([[-1, -2]]) + X))/2)/(2*pi)');
    expect(at(M, [[3, 4]])).toBe('exp(-4)/(2*pi)');
  });
});

describe('MatrixStudentT', () => {
  it('density (test_MatrixStudentT)', () => {
    const M = MatrixStudentT('M', 2, [[5, 6]], [[2, 1], [1, 2]], [4]);
    expect(str(pspaceOf(M).distribution.set)).toBe('MatrixSet(1, 2, Reals)');
    const X = MatrixSymbol('X', 1, 2);
    // SymPy's exponents n*p/2, -n/2 and -p/2 are Python float divisions of the shape of an explicit matrix
    expect(str(dens(M).call(X))).toBe(
      '1/(pi**1.0*Determinant(Matrix([[1/4]])*(Matrix([[-5, -6]]) + X)*Matrix([[2/3, -1/3], [-1/3, 2/3]])*(Matrix([[-5], [-6]]) + X.T) + Matrix([[1]]))**2*Determinant(Matrix([[4]]))**1.0*Determinant(Matrix([[2, 1], [1, 2]]))**0.5)',
    );
    const v = new Sym('v', { positive: true });
    const M2 = MatrixStudentT('M', v, MatrixSymbol('Location', 1, 2), MatrixSymbol('Omega', 2, 2), MatrixSymbol('Sigma', 1, 1));
    expect(str(dens(M2).call(MatrixSymbol('Y', 1, 2)))).toBe(
      'gamma(v/2 + 1)*Determinant(Matrix([[1]]) + Sigma**(-1)*(-Location + Y)*Omega**(-1)*(-Location.T + Y.T))**(-v/2 - 1)/(pi*gamma(v/2)*sqrt(Determinant(Omega))*Determinant(Sigma))',
    );
    expect(() => dens(M2).call(1)).toThrow('should be an isinstance of Matrix or MatrixSymbol');
  });
  it('parameter checks', () => {
    expect(() => MatrixStudentT('M', 1, [1, 2], [[1, 0], [0, 1]], [[1, 0], [2, 1]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixStudentT('M', 1, [1, 2], [[1, 0], [2, 1]], [[1, 0], [0, 1]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixStudentT('M', 1, [1, 2], [[1, 0], [0, 1]], [[1, 0], [0, 1]])).toThrow('Scale matrix 1 should be of shape 1 x 1');
    expect(() => MatrixStudentT('M', 1, [1, 2], [[1, 0], [2]], [[1, 0], [0, 1]])).toThrow('mismatched dimensions');
    expect(() => MatrixStudentT('M', 1, [[1, 2]], [[1, 0], [0, 1]], [[1, 0]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixStudentT('M', 1, [[1, 2]], [1], [[1, 0]])).toThrow('The shape matrix must be positive definite.');
    expect(() => MatrixStudentT('M', 1, [[1, 2]], [[1, 0], [0, 1]], MatrixSymbol('S', 1, 2))).toThrow('Scale matrix 2 should be be square matrix');
    expect(() => MatrixStudentT('M', 1, [[1, 2]], MatrixSymbol('O', 2, 1), [1])).toThrow('Scale matrix 1 should be be square matrix');
    expect(() => MatrixStudentT('M', 1, [[1, 2]], [[1, 0], [0, 1]], [[1, 0], [0, 1]])).toThrow('Scale matrix 2 should be of shape 1 x 1');
    expect(() => MatrixStudentT('M', -1, [1, 2], [[1]], [[1, 0], [0, 1]])).toThrow('Degrees of freedom must be positive');
  });
  it('doctest', () => {
    const v = new Sym('v', { positive: true });
    const M = MatrixStudentT('M', v, [[1, 2]], [[1, 0], [0, 1]], [1]);
    const X = MatrixSymbol('X', 1, 2);
    expect(str(dens(M).call(X))).toBe(
      'gamma(v/2 + 1)*Determinant((Matrix([[-1, -2]]) + X)*(Matrix([[-1], [-2]]) + X.T) + Matrix([[1]]))**(-v/2 - 1)/(pi**1.0*gamma(v/2)*Determinant(Matrix([[1]]))**1.0*Determinant(Matrix([[1, 0], [0, 1]]))**0.5)',
    );
  });
});

void RandomMatrixSymbol;
