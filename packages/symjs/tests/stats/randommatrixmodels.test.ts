// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/randommatrixmodels.ts (SymPy
// sympy/stats/random_matrix_models.py, its doctests and
// sympy/stats/tests/test_random_matrix.py). Expected values are those of
// SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Matrix, MatrixSymbol, Sym, doit, str, sympify as toExpr, xreplace } from '../../src';
import { ImmutableMatrixNode } from '../../src/matrices/expressions/matexpr';
import type { Expr } from '../../src';
import { Beta, Normal, density } from '../../src/stats';
import { RandomMatrixSymbol } from '../../src/stats/rv';
import { RandomMatrixPSpace } from '../../src/stats/randommatrix';
import {
  CircularEnsemble,
  CircularOrthogonalEnsemble,
  CircularSymplecticEnsemble,
  CircularUnitaryEnsemble,
  GaussianEnsemble,
  GaussianEnsembleModel,
  GaussianOrthogonalEnsemble,
  GaussianSymplecticEnsemble,
  GaussianUnitaryEnsemble,
  JointEigenDistribution,
  RandomMatrixEnsembleModel,
  jointEigenDistribution,
  levelSpacingDistribution,
} from '../../src/stats/randommatrixmodels';

const call = (d: unknown, x: Expr): Expr => (d as { call(x: Expr): Expr }).call(x);

describe('Gaussian ensembles (SymPy doctests and test_random_matrix)', () => {
  it('densities', () => {
    const X = MatrixSymbol('X', 2, 2);
    expect(str(call(density(GaussianUnitaryEnsemble('U', 2)), X))).toBe('exp(-Trace(X**2))/(2*pi**2)');
    expect(str(call(density(GaussianOrthogonalEnsemble('U', 2)), X))).toBe('exp(-Trace(X**2)/2)/Integral(exp(-Trace(_H**2)/2), _H)');
    expect(str(call(density(GaussianSymplecticEnsemble('U', 2)), X))).toBe('exp(-2*Trace(X**2))/Integral(exp(-2*Trace(_H**2)), _H)');
    const H = new RandomMatrixSymbol('H', 3, 3);
    expect(str(call(density(GaussianUnitaryEnsemble('U', 3)), H))).toBe('sqrt(2)*exp(-3*Trace(H**2)/2)/(4*pi**(9/2))');
    expect(str(call(density(GaussianOrthogonalEnsemble('O', 3)), H))).toBe('exp(-3*Trace(H**2)/4)/Integral(exp(-3*Trace(_H**2)/4), _H)');
    expect(str(call(density(GaussianSymplecticEnsemble('O', 3)), H))).toBe('exp(-3*Trace(H**2))/Integral(exp(-3*Trace(_H**2)), _H)');
  });
  it('joint eigenvalue and level spacing distributions', () => {
    const U = GaussianUnitaryEnsemble('U', 2);
    expect(str(jointEigenDistribution(U))).toBe('Lambda((l[1], l[2]), exp(-l[1]**2 - l[2]**2)*Product(Abs(l[_i] - l[_j])**2, (_j, _i + 1, 2), (_i, 1, 1))/pi)');
    expect(str(levelSpacingDistribution(U))).toBe('Lambda(_s, 32*_s**2*exp(-4*_s**2/pi)/pi**2)');
    expect(str(jointEigenDistribution(GaussianUnitaryEnsemble('U', 3)))).toBe(
      'Lambda((l[1], l[2], l[3]), 27*sqrt(6)*exp(-3*l[1]**2/2 - 3*l[2]**2/2 - 3*l[3]**2/2)*Product(Abs(l[_i] - l[_j])**2, (_j, _i + 1, 3), (_i, 1, 2))/(16*pi**(3/2)))',
    );
    expect(str(jointEigenDistribution(GaussianOrthogonalEnsemble('U', 3)))).toBe(
      'Lambda((l[1], l[2], l[3]), 9*sqrt(2)*exp(-3*l[1]**2/2 - 3*l[2]**2/2 - 3*l[3]**2/2)*Product(Abs(l[_i] - l[_j]), (_j, _i + 1, 3), (_i, 1, 2))/(32*pi))',
    );
    expect(str(levelSpacingDistribution(GaussianOrthogonalEnsemble('U', 3)))).toBe('Lambda(_s, _s*pi*exp(-_s**2*pi/4)/2)');
    expect(str(jointEigenDistribution(GaussianSymplecticEnsemble('U', 3)))).toBe(
      'Lambda((l[1], l[2], l[3]), 162*sqrt(3)*exp(-3*l[1]**2/2 - 3*l[2]**2/2 - 3*l[3]**2/2)*Product(Abs(l[_i] - l[_j])**4, (_j, _i + 1, 3), (_i, 1, 2))/(5*pi**(3/2)))',
    );
    expect(str(levelSpacingDistribution(GaussianSymplecticEnsemble('U', 3)))).toBe('Lambda(_s, 262144*_s**4*exp(-64*_s**2/(9*pi))/(729*pi**3))');
  });
});

describe('circular ensembles', () => {
  it('joint eigenvalue distributions', () => {
    expect(str(jointEigenDistribution(CircularUnitaryEnsemble('U', 1)))).toBe('Lambda(t[1], Product(Abs(exp(I*t[_j]) - exp(I*t[_k]))**2, (_j, _k + 1, 1), (_k, 1, 0))/(2*pi))');
    expect(str(jointEigenDistribution(CircularOrthogonalEnsemble('O', 1)))).toBe('Lambda(t[1], Product(Abs(exp(I*t[_j]) - exp(I*t[_k])), (_j, _k + 1, 1), (_k, 1, 0))/(2*pi))');
    expect(str(jointEigenDistribution(CircularSymplecticEnsemble('S', 1)))).toBe('Lambda(t[1], Product(Abs(exp(I*t[_j]) - exp(I*t[_k]))**4, (_j, _k + 1, 1), (_k, 1, 0))/(2*pi))');
    expect(str(jointEigenDistribution(CircularUnitaryEnsemble('U', 3)))).toBe('Lambda((t[1], t[2], t[3]), Product(Abs(exp(I*t[_j]) - exp(I*t[_k]))**2, (_j, _k + 1, 3), (_k, 1, 2))/(48*pi**3))');
    expect(str(jointEigenDistribution(CircularOrthogonalEnsemble('U', 3)))).toBe('Lambda((t[1], t[2], t[3]), Product(Abs(exp(I*t[_j]) - exp(I*t[_k])), (_j, _k + 1, 3), (_k, 1, 2))/(48*pi**2))');
    expect(str(jointEigenDistribution(CircularSymplecticEnsemble('U', 3)))).toBe('Lambda((t[1], t[2], t[3]), Product(Abs(exp(I*t[_j]) - exp(I*t[_k]))**4, (_j, _k + 1, 3), (_k, 1, 2))/(720*pi**3))');
  });
});

describe('JointEigenDistribution', () => {
  it('of a matrix of random symbols', () => {
    const A = Matrix.of([
      [Normal('A00', 0, 1), Normal('A01', 0, 1)],
      [Beta('A10', 1, 1), Beta('A11', 1, 1)],
    ]);
    expect(str(JointEigenDistribution(A))).toBe(
      'JointDistributionHandmade(-sqrt(A00**2 - 2*A00*A11 + 4*A01*A10 + A11**2)/2 + A00/2 + A11/2, sqrt(A00**2 - 2*A00*A11 + 4*A01*A10 + A11**2)/2 + A00/2 + A11/2)',
    );
  });
});

describe('ensembles and models', () => {
  it('GaussianEnsemble (test_GaussianEnsemble)', () => {
    const G = GaussianEnsemble('G', 3);
    const ps = G.pspace as RandomMatrixPSpace;
    expect(density(G)).toBe(ps.model);
    expect(str(ps)).toBe('RandomMatrixPSpace(G, GaussianEnsembleModel(G, 3))');
    expect(ps.symbol.name).toBe('G');
    const model = ps.model as GaussianEnsembleModel;
    expect(model.symbol.name).toBe('G');
    expect(str(model.dimension)).toBe('3');
    expect(str(model.call(MatrixSymbol('X', 3, 3)))).toBe('Density(X)');
    expect(() => model.jointEigenDistribution()).toThrow('GaussianEnsembleModel has no joint eigenvalue distribution');
    expect(() => levelSpacingDistribution(CircularEnsemble('C', 2))).toThrow('CircularEnsembleModel has no level spacing distribution');
    expect(() => GaussianEnsemble('G', 3.5)).toThrow('Dimension of the random matrices must be integers, received 3.50000000000000 instead.');
    expect(str(model.withArgs([new Sym('H'), model.dimension]))).toBe('GaussianEnsembleModel(H, 3)');
    expect(new RandomMatrixEnsembleModel([new Sym('R'), model.dimension]).name).toBe('RandomMatrixEnsembleModel');
  });
  it('spaces and normalization constants', () => {
    expect(str(GaussianUnitaryEnsemble('U', 2).pspace)).toBe('RandomMatrixPSpace(U, GaussianUnitaryEnsembleModel(U, 2))');
    expect(str(CircularUnitaryEnsemble('C', 2).pspace)).toBe('RandomMatrixPSpace(C, CircularUnitaryEnsembleModel(C, 2))');
    const n = new Sym('n', { integer: true, positive: true });
    const model = (GaussianUnitaryEnsemble('U', n).pspace as RandomMatrixPSpace).model as unknown as { normalizationConstant: Expr };
    expect(str(model.normalizationConstant)).toBe('2**(n/2)*pi**(n**2/2)');
  });
  it('errors', () => {
    const X = MatrixSymbol('X', 2, 2);
    // SymPy: NotImplementedError (the Haar measure is not implemented)
    expect(() => call(density(CircularUnitaryEnsemble('C', 2)), X)).toThrow(
      "Support for Haar measure hasn't been implemented yet, therefore the density of CircularUnitaryEnsembleModel(C, 2) cannot be computed.",
    );
    const n = new Sym('n', { integer: true, positive: true });
    // SymPy: TypeError, the ArrayComprehension of a symbolic dimension cannot be iterated
    expect(() => jointEigenDistribution(GaussianUnitaryEnsemble('U', n))).toThrow("'ArrayComprehension' object is not iterable");
    expect(() => jointEigenDistribution(CircularUnitaryEnsemble('C', n))).toThrow("'ArrayComprehension' object is not iterable");
    expect(() => jointEigenDistribution(X)).toThrow('X is not of type, RandomMatrixSymbol.');
    expect(() => JointEigenDistribution(Matrix.of([[1, 0], [2, 1]]))).toThrow('Eigen values do not have any random expression, joint distribution cannot be generated.');
    expect(str(call(density(GaussianUnitaryEnsemble('U', 2)), GaussianUnitaryEnsemble('V', 2)))).toBe('exp(-Trace(V**2))/(2*pi**2)');
    // SymPy: NotImplementedError for an expression of random matrices
    expect(() => density(GaussianUnitaryEnsemble('U', 2).add(GaussianUnitaryEnsemble('V', 2)))).toThrow('multiple random matrices');
  });
  it('JointEigenDistribution of a matrix expression', () => {
    const A = new ImmutableMatrixNode(Matrix.of([[Normal('A00', 0, 1), 0], [0, Normal('A11', 0, 1)]]));
    expect(str(JointEigenDistribution(A))).toBe('JointDistributionHandmade(A00, A11)');
  });
  it('issue 19841', () => {
    const G1 = GaussianUnitaryEnsemble('U', 2);
    expect(xreplace(G1, [[toExpr(2), toExpr(2)]]).key).toBe(G1.key);
    const X = MatrixSymbol('X', 2, 2);
    const G = GaussianSymplecticEnsemble('U', 2);
    const hPspace = new RandomMatrixPSpace([new Sym('P'), density(G) as Expr]);
    const H = new RandomMatrixSymbol('H', 2, 2, hPspace);
    const H2 = new RandomMatrixSymbol('H', 2, 2);
    expect(doit(H).key).toBe(H.key);
    expect(str(xreplace(H.mul(2), [[H, X]]))).toBe('2*X');
    expect(xreplace(H.mul(2), [[H2, X]]).key).toBe(H.mul(2).key);
    expect(xreplace(H2.mul(2), [[H, X]]).key).toBe(H2.mul(2).key);
    expect(str(xreplace(H2.mul(2), [[H2, X]]))).toBe('2*X');
  });
});
