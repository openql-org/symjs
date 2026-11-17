// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { ArraySymbol, ArrayElement, MatrixSymbol, Sum, Sym, S, add, mul, sin, pow, str, convertIndexedToArray } from '../../../../src/index';
import { NotImplementedError } from '../../../../src/core/errors';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const A = new ArraySymbol('A', [2, 2]), B = new ArraySymbol('B', [2, 2]);
const M = MatrixSymbol('M', 2, 2), N = MatrixSymbol('N', 2, 2), i = new Sym('i'), j = new Sym('j'), k = new Sym('k');
const cases = [
  ['indexed', A.at(i, j), [i, j]], ['indexed_transpose', A.at(i, j), [j, i]],
  ['indexed_add', add(A.at(i, j), B.at(j, i)), [i, j]], ['indexed_diagonal', A.at(i, i), []],
  ['indexed_trace', Sum(A.at(i, i), [i, 0, 1]), []],
  ['indexed_product', Sum(mul(A.at(i, j), B.at(j, k)), [j, 0, 1]), []],
  ['indexed_reversed', Sum(mul(M.at(i, j), N.at(j, k)), [j, 0, 1]), [k]],
] as const;
for (const [name, value, indices] of cases) it(name, () => expect(str(convertIndexedToArray(value, indices))).toBe(refs[name]));
it('checks summation ranges and unsupported indexed operations', () => {
  expect(() => convertIndexedToArray(A.at(i, j), [i, i])).toThrow(RangeError);
  expect(str(convertIndexedToArray(A.at(0, j)))).toBe('A[0, j]');
  const shifted = A.at(add(i, 1), j);
  expect(convertIndexedToArray(shifted)).toBe(shifted);
  const shiftedSum = Sum(shifted, [i, 0, 0]);
  expect(convertIndexedToArray(shiftedSum)).toBe(shiftedSum);
  expect(() => convertIndexedToArray(new ArrayElement(new Sym('Q'), [i, j]))).toThrow(NotImplementedError);
  expect(() => convertIndexedToArray(add(A.at(i, j), B.at(i, k)))).toThrow(RangeError);
  expect(() => convertIndexedToArray(Sum(A.at(i, j), [i, 1, 1]))).toThrow(NotImplementedError);
  expect(() => convertIndexedToArray(Sum(A.at(i, j), [i, 0, 2]))).toThrow(NotImplementedError);
  expect(str(convertIndexedToArray(Sum(mul(i, A.at(i, j)), [i, 0, 1])))).toContain('ArrayContraction');
  expect(str(convertIndexedToArray(sin(A.at(i, j))))).toContain('ArrayElementwiseApplyFunc');
  expect(() => convertIndexedToArray(pow(A.at(i, j), 2))).toThrow(NotImplementedError);
  expect(convertIndexedToArray(S.One)).toBe(S.One);
  const scalar = Sum(i, [i, 0, 1]);
  expect(convertIndexedToArray(scalar)).toBe(scalar);
  expect(() => convertIndexedToArray(Sum(A.at(i, j), [k, 0, 1]))).toThrow(RangeError); // SymPy raises IndexError.
});

it('keeps index-dependent weights inside their summation', async () => {
  const { explicitArray } = await import('../../../../src/tensor/array/expressions/arrayexpressions');
  const freeWeighted = convertIndexedToArray(mul(i, A.at(i, j)), [i, j]);
  expect(str(explicitArray(freeWeighted))).toBe('[[0, 0], [A[1, 0], A[1, 1]]]');
  const weighted = convertIndexedToArray(Sum(mul(i, A.at(i, j)), [i, 0, 1]));
  expect(str(explicitArray(weighted))).toBe('[A[1, 0], A[1, 1]]');
  const shiftedWeight = convertIndexedToArray(Sum(mul(add(i, 1), A.at(i, j)), [i, 0, 1]));
  expect(str(explicitArray(shiftedWeight))).toBe('[A[0, 0] + 2*A[1, 0], A[0, 1] + 2*A[1, 1]]');
});
