// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { PartialDerivative, TensorIndexType, TensorHead, TensorIndex, Sym, S, ExprMap, ImmutableDenseNDimArray, parseExpr as p, doit, NotImplementedError } from '../../src';
const L = TensorIndexType('L', { dim: 2 }), A = TensorHead('A', [L]), B = TensorHead('B', [L]);
const i = TensorIndex('i', L), j = TensorIndex('j', L), k = TensorIndex('k', L), x = new Sym('x'), y = new Sym('y');
it('tracks opposite derivative variance, canonical contractions and nested derivatives', () => {
  const derivative = PartialDerivative(A.at(i), A.at(j));
  expect(String(derivative)).toBe('PartialDerivative(A(i), A(j))');
  expect(derivative.getIndices().map(String)).toEqual(['i', '-j']);
  expect(derivative.getFreeIndices().map(String)).toEqual(['i', '-j']);
  expect(derivative.coeff).toBe(S.One); expect(derivative.nocoeff).toBe(derivative);
  expect(derivative.isCommutative).toBe(false);
  expect(String(doit(derivative))).toBe(String(derivative));
  expect(String(derivative.canonBp())).toBe(String(derivative));
  const contraction = new PartialDerivative(A.at(i), A.at(i));
  expect(String(contraction)).toBe('PartialDerivative(A(L_0), A(L_0))');
  expect(contraction.getFreeIndices()).toEqual([]);
  expect(contraction.getIndices().map(String)).toEqual(['L_0', '-L_0']);
  expect(String(PartialDerivative(derivative, A.at(k)))).toBe('PartialDerivative(A(i), A(j), A(k))');
  expect(String(derivative.substituteIndices([j, k]))).toBe('PartialDerivative(A(i), A(k))');
  expect(String(derivative.substituteIndices([i, k]))).toBe('PartialDerivative(A(k), A(j))');
  expect(() => derivative.contractMetric(L.metric)).toThrow(NotImplementedError);
  expect(() => PartialDerivative(A.at(i), S.One)).toThrow(TypeError);
  expect(() => PartialDerivative(A.at(i), A.at(i.neg()))).toThrow('Repeated index');
});
it('differentiates component arrays with derivand axes first', () => {
  const derivative = PartialDerivative(A.at(i), B.at(j));
  const replacements = new Map([[A.at(i), [p('sin(x)'), p('log(x)*y**3')]], [B.at(i), [x, y]]]);
  expect(String(derivative.replaceWithArrays(replacements))).toBe('[[cos(x), 0], [y**3/x, 3*y**2*log(x)]]');
  const contraction = PartialDerivative(A.at(i), B.at(i));
  expect(String(contraction.replaceWithArrays(replacements))).toBe('3*y**2*log(x) + cos(x)');
  const scaled = new Map([[A.at(i), [x.pow(2), y.pow(2)]], [B.at(i), [x.mul(2), y.mul(3)]]]);
  expect(String(derivative.replaceWithArrays(scaled))).toBe('[[x, 0], [0, 2*y/3]]');
  expect(String(PartialDerivative(A.at(i), x).replaceWithArrays(replacements))).toBe('[cos(x), y**3/x]');
  expect(String(PartialDerivative(x.pow(2), x).extractData(new ExprMap())[1])).toBe('2*x');
  expect(String(PartialDerivative(x, B.at(j)).extractData(new ExprMap([[B.at(j), new ImmutableDenseNDimArray([x, y])]]))[1])).toBe('[1, 0]');
  expect(String(PartialDerivative(x, x).substituteIndices([i,j]))).toBe('PartialDerivative(x, x)');
});
it('rebuilds with doit and reads component matrices', () => {
  const derivative = PartialDerivative(A.at(i), B.at(j));
  expect(String(derivative.doit())).toBe('PartialDerivative(A(i), B(j))');
  expect(String(derivative.funEval([j, k]))).toBe('PartialDerivative(A(i), B(k))');
  const replacements = new Map([[A.at(i), [p('sin(x)'), p('log(x)*y**3')]], [B.at(i), [x, y]]]);
  expect(String(derivative.getMatrix(replacements))).toBe('Matrix([[cos(x), 0], [y**3/x, 3*y**2*log(x)]])');
  expect(String(PartialDerivative(A.at(i), x).getMatrix(replacements))).toBe('Matrix([[cos(x)], [y**3/x]])');
  expect(() => PartialDerivative(A.at(i), B.at(i)).getMatrix(replacements)).toThrow(NotImplementedError);
  const C = TensorHead('C', [L, L]);
  const cube = new Map([[A.at(i), [x, y]], [C.at(j, k), [[x, y], [y, x]]]]);
  expect(() => PartialDerivative(A.at(i), C.at(j, k)).getMatrix(cube)).toThrow(NotImplementedError);
});
