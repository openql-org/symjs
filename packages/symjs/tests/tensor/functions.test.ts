// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/functions.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

describe('shape', () => {
  it('shapes of arrays, matrices and integrals of them', () => {
    const x = sj.symbol('x');
    const A = sj.ImmutableDenseNDimArray([1, 2]);
    const M = sj.Matrix.of([[x], [x]]);
    expect(sj.shape(A)).toEqual([2]);
    expect(sj.shape(M)).toEqual([2, 1]);
    expect(sj.shape(new sj.Integral([A, x]))).toEqual([2]);
    expect(sj.shape(sj.MatrixSymbol('X', 2, 3)).map(String)).toEqual(['2', '3']);
    expect(() => sj.shape(x)).toThrow(sj.NoShapeError);
    expect(() => sj.shape(x)).toThrow('x does not have shape, or its type is not registered to shape().');
    expect(() => sj.shape(3)).toThrow('3 does not have shape');
  });
});

it('infers indexed shapes from complete index ranges', () => {
  const m = sj.symbol('m', {integer:true});
  const A = new sj.IndexedBase('A');
  expect(sj.shape(A.at(sj.Idx('i',m),sj.Idx('j',[2,4]))).map(String)).toEqual(['m','3']);
  expect(() => sj.shape(A.at(1))).toThrow(sj.NoShapeError);
  expect(() => sj.shape(A.at(sj.Idx('i')))).toThrow(sj.NoShapeError);
});

it('uses explicit indexed shapes before index ranges', () => {
  const n = sj.symbol('n', { integer: true });
  const base = new sj.IndexedBase('A', { shape: [n, 5] });
  expect(sj.shape(base)).toEqual([n, sj.Rational.of(5)]);
  expect(sj.shape(base.at(sj.Idx('i', 3), 2))).toEqual([n, sj.Rational.of(5)]);
  const unshaped = new sj.IndexedBase('A');
  expect(() => sj.shape(unshaped)).toThrow(sj.NoShapeError);
  expect(sj.shape(new sj.Indexed([unshaped, sj.Idx('i', 3)]))).toEqual([sj.Rational.of(3)]);
});

it('evaluates generic tensor products and preserves symbolic factors', () => {
  const M = sj.MatrixSymbol('M', 2, 3), N = sj.MatrixSymbol('N', 3, 2);
  expect(String(sj.TensorProduct())).toBe('1');
  expect(String(sj.TensorProduct(2, 3))).toBe('6');
  expect(String(sj.TensorProduct([1, 2], [3, 4]))).toBe('[[3, 4], [6, 8]]');
  expect(String(sj.TensorProduct(sj.Matrix.of([[1, 2]]), 2))).toBe('[[2, 4]]');
  const product = sj.TensorProduct(2, M, sj.TensorProduct(N));
  expect(product).toBeInstanceOf(sj.TensorProduct);
  if (!(product instanceof sj.TensorProductNode)) throw new TypeError('tensor product expected');
  expect(product.shape.map(String)).toEqual(['2', '3', '3', '2']);
  expect(product.rank()).toBe(4);
  expect(String(product.at(0, 1, 2, 0))).toBe('2*M[0, 1]*N[2, 0]');
  expect(() => product.at(0)).toThrow(RangeError);
  expect(String(product.withArgs([M]))).toBe('TensorProduct(M)');
  const raw = sj.TensorProduct(2, 3, { evaluate: false });
  expect(String(raw)).toBe('TensorProduct(2, 3)');
  expect(() => sj.TensorProduct({evaluate: false}, 2)).toThrow(TypeError);
  const arrayProduct = sj.TensorProduct([1, 2], M);
  if (!(arrayProduct instanceof sj.TensorProductNode)) throw new TypeError('tensor product expected');
  expect(String(arrayProduct.at(1, 0, 2))).toBe('2*M[0, 2]');
});

it('retains nested unevaluated product shapes and flattens evaluated products', () => {
  const inner = sj.TensorProduct([1, 2], [3, 4], { evaluate: false });
  const nested = sj.TensorProduct(inner, inner, { evaluate: false });
  if (!(nested instanceof sj.TensorProductNode)) throw new TypeError('tensor product expected');
  expect(nested.shape).toEqual([2, 2, 2, 2]);
  expect(nested.rank()).toBe(4);
  expect(String(nested.at(1, 0, 0, 1))).toBe('24');
  const M = sj.MatrixSymbol('M', 2, 2);
  const raw = sj.TensorProduct(sj.TensorProduct(M, M, { evaluate: false }), M, { evaluate: false });
  expect(String(sj.TensorProduct(raw, M))).toBe('TensorProduct(M, M, M, M)');
  const A = new sj.ArraySymbol('A', [2]);
  const symbolic = sj.TensorProduct(A, M);
  if (!(symbolic instanceof sj.TensorProductNode)) throw new TypeError('tensor product expected');
  expect(symbolic.shape.map(String)).toEqual(['2', '2', '2']);
  expect(String(symbolic.at(1, 0, 1))).toBe('A[1]*M[0, 1]');
});
