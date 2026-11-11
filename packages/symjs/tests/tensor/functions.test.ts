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
