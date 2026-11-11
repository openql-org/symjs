// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { describe, expect, it } from 'vitest';
import { domEigenvects, domEigenvectsToSympy, DomainMatrix, QQ, symbols, Matrix, parse, Poly, FiniteExtension } from '../../../src';
import { at } from '../../../src/core/guard';

describe('domain eigenvectors', () => {
  it('computes rational eigenspaces, including defective and repeated eigenvalues', () => {
    for (const rows of [[[1, 2], [1, 2]], [[2, 1], [0, 2]], [[2, 0], [0, 2]], [[0, 0], [0, 0]]]) {
      const A = DomainMatrix.fromList(rows, QQ);
      const [rational, algebraic] = domEigenvects(A);
      expect(algebraic).toEqual([]);
      for (const [eigenvalue, , vectors] of domEigenvectsToSympy(rational, algebraic, (entries) => Matrix.col(...entries))) {
        for (const v of vectors) expect(A.toMatrix().mul(v).equals(v.mul(eigenvalue))).toBe(true);
      }
    }
    expect(domEigenvects(new DomainMatrix([], [0, 0], QQ))).toEqual([[], []]);
    expect(() => domEigenvects(DomainMatrix.fromList([[1, 2]], QQ))).toThrow('square');
  });
  it('computes exact quadratic extension eigenvectors and substitutes both roots', () => {
    const lambda = at(symbols('lambda'), 0);
    const A = DomainMatrix.fromList([[1, 2], [3, 4]], QQ);
    const [rational, algebraic] = domEigenvects(A, lambda);
    expect(rational).toEqual([]);
    const [K, polynomial, mult, basis] = at(algebraic, 0);
    expect(K).toBeInstanceOf(FiniteExtension);
    expect(String(polynomial.asExpr())).toBe('lambda**2 - 5*lambda - 2');
    expect(mult).toBe(1);
    expect(basis.shape).toEqual([1, 2]);
    const values = domEigenvectsToSympy(rational, algebraic);
    expect(values.map(([value]) => String(value))).toEqual(['5/2 - sqrt(33)/2', '5/2 + sqrt(33)/2']);
    for (const [v, , vectors] of values) for (const vector of vectors) expect(A.toMatrix().mul(vector).sub(vector.mul(v)).simplify().isZeroMatrix).toBe(true);
  });
  it('respects radical options and accepts the Matrix class as a factory', () => {
    const lambda = at(symbols('lambda'), 0);
    for (const [degree, options] of [[3, { cubics: false }], [4, { quartics: false }]] as const) {
      const polynomial = Poly.from(lambda.pow(degree).sub(lambda).add(1), [lambda], { domain: 'QQ' });
      const K = new FiniteExtension(polynomial);
      const basis = DomainMatrix.fromList([[1]], K.toDomain());
      const result = domEigenvectsToSympy([], [[K, polynomial, 1, basis]], Matrix, options);
      expect(result).toHaveLength(degree);
      expect(String(at(result, 0)[0])).toContain('CRootOf');
      const binomial = Poly.from(lambda.pow(degree).sub(2), [lambda], { domain: 'QQ' });
      const field = new FiniteExtension(binomial);
      const radicals = domEigenvectsToSympy([], [[field, binomial, 1, DomainMatrix.fromList([[1]], field.toDomain())]]);
      expect(radicals).toHaveLength(degree);
      expect(radicals.every(([value]) => !String(value).includes('CRootOf'))).toBe(true);
    }
    const A = DomainMatrix.fromList([[0, 2], [1, 0]], QQ);
    expect(domEigenvectsToSympy(...domEigenvects(A), Matrix, { quintics: true })).toHaveLength(2);
  });
  it('falls back to indexed roots for an irreducible quintic', () => {
    const lambda = at(symbols('lambda'), 0);
    const companion = DomainMatrix.fromList([[0, 0, 0, 0, -1], [1, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]], QQ);
    const [rational, algebraic] = domEigenvects(companion, lambda);
    expect(rational).toEqual([]);
    expect(at(algebraic, 0)[3].toList().map((row) => row.map(String))).toEqual([['lambda**4 - 1', 'lambda**3', 'lambda**2', 'lambda', '1']]);
    const polynomial = Poly.from(parse('lambda**5-lambda+1'), [lambda], { domain: 'QQ' });
    const K = new FiniteExtension(polynomial);
    const basis = DomainMatrix.fromList([[1, lambda]], K.toDomain());
    const result = domEigenvectsToSympy([], [[K, polynomial, 1, basis]]);
    expect(result).toHaveLength(5);
    expect(String(at(result, 0)[0])).toContain('CRootOf');
    for (const [value, , vectors] of result) expect(at(vectors, 0).get(1, 0).equals(value)).toBe(true);
  });
});
