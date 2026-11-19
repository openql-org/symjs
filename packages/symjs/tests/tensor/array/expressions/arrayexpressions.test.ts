// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { passingModuleCases, runTestCase } from '../../../../../../tools/sympy-corpus/unittest-harness';
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { ArraySymbol, ArrayElement, ArrayTensorProduct as TP, ArrayContraction as C, ArrayDiagonal as D, ArrayAdd, PermuteDims as P, Reshape, ZeroArray, getShape, getRank, SymArray, MatrixSymbol, Sym, S, str, latex, tensorproduct, tensorcontraction, tensordiagonal, permutedims, parse, diff, expand, sub } from '../../../../src/index';
import { at, cast, first } from '../../../../src/core/guard';
import { NotImplementedError } from '../../../../src/core/errors';
import { ArrayExpr, explicitArray } from '../../../../src/tensor/array/expressions/arrayexpressions';
import { doit } from '../../../../src/calculus/doit';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const A = new ArraySymbol('A', [2, 2]), B = new ArraySymbol('B', [2, 2]), T = new ArraySymbol('T', [2, 2, 2]);
const M = MatrixSymbol('M', 2, 2), N = MatrixSymbol('N', 2, 2), n = new Sym('n');
const nodes: Record<string, ArrayExpr> = {
  symbol: A, rank3: T, empty: new ArraySymbol('E', [0, 2]), product: new TP(A, B), scaled: new TP(parse('3'), A),
  trace: new C(A, [0, 1]), chain: new C(new TP(M, N), [1, 2]), diagonal: new D(A, [0, 1]),
  double_diagonal: new D(new TP(A, B), [0, 2], [1, 3]), permuted: new P(T, [2, 0, 1]), reshape: new Reshape(A, [4]),
  sum: new ArrayAdd(A, B), zero: new ZeroArray(2, 2), nested_contraction: new C(new C(new TP(M, N), [1, 2]), [0, 1]), single_axis: new C(T, [1]),
};
describe('SymPy array expressions', () => {
  for (const [name, value] of Object.entries(nodes)) it(name, () => {
    expect(str(value)).toBe(refs[name]);
    expect(str(value.asExplicit())).toBe(refs[`${name}_explicit`]);
    expect(str(value.doit())).toBe(refs[`${name}_doit`]);
    expect(latex(value)).toBe(refs[`${name}_latex`]);
    expect(value.withArgs(value.args).key).toBe(value.key);
    expect(value.rank()).toBe(getRank(value));
    expect(getShape(value)).toEqual(value.shape);
  });
  it('checks array entry dimensions and differentiates entries', () => {
    const i = new Sym('i'), j = new Sym('j'), k = new Sym('k');
    const a = A.at(i, j);
    expect(str(a)).toBe('A[i, j]');
    expect(latex(a)).toBe('{{A}_{i, j}}'); // SymPy 1.14.0
    expect(a.withArgs(a.args).key).toBe(a.key);
    expect(str(diff(a, a))).toBe('1');
    expect(str(a.diffSelf(A.at(i, k)))).toBe('KroneckerDelta(j, k)');
    expect(a.diffSelf(B.at(i, j))).toBe(S.Zero);
    expect(a.diffSelf(n)).toBe(S.Zero);
    expect(() => A.at(0)).toThrow(RangeError);
    for (const i of [-1, 2, -0.5, 2.5]) expect(() => A.at(i, 0)).toThrow(RangeError);
    expect(str(A.at(parse('1/2'), 0))).toBe(refs['fractional_index']);
    expect(str(new ArrayElement(new Sym('Q'), [i, j]))).toBe('Q[i, j]');
    expect(() => new ArrayElement(new Sym('Q'), [-1])).toThrow(RangeError);
    expect(str(new ArraySymbol('X', [n]).at(100))).toBe('X[100]');
    expect(() => new ArraySymbol('X', [n]).asExplicit()).toThrow(RangeError);
    expect(() => new ArraySymbol('a', []).asExplicit()).toThrow(TypeError); // SymPy 1.14.0
    expect(() => new ArraySymbol('X', [parse('3/2')])).toThrow(RangeError);
    expect(() => new ArraySymbol('X', [9007199254740992n]).asExplicit()).toThrow(RangeError);
    expect(str(new ArrayElement(A, [0, 1]))).toBe('A[0, 1]');
    expect(str(doit(new C(new C(new TP(M, N), [1, 2]), [0, 1])))).toBe(refs['nested_contraction_doit']);
  });
  it('rejects inconsistent axes, permutations and shapes', () => {
    for (const axes of [[-1], [2], [0, 0], [0.5], []]) expect(() => new C(A, axes)).toThrow(RangeError);
    expect(() => new C(new ArraySymbol('R', [2, 3]), [0, 1])).toThrow(RangeError);
    expect(() => new D(A, [0])).toThrow(RangeError);
    expect(() => new C(A, [0], [0])).toThrow(RangeError);
    for (const p of [[0], [0, 0], [0, 2], [0, -1], [0, 0.5]]) expect(() => new P(A, p)).toThrow(RangeError);
    expect(() => new Reshape(A, [3])).toThrow(RangeError);
    expect(() => new ArrayAdd()).toThrow(RangeError);
    expect(() => new ArrayAdd(A, T)).toThrow(RangeError);
    expect(() => new ZeroArray(1000000000, 1000000000).asExplicit()).toThrow(NotImplementedError);
  });
  it('evaluates empty operations and explicit scalar arguments', () => {
    expect(new TP().doit()).toBe(S.One);
    expect(new TP(A).doit()).toBe(A);
    expect(str(new TP(new TP(A, B), T).doit())).toBe(str(new TP(A, B, T)));
    expect(new C(A).doit()).toBe(A);
    expect(str(new C(A).asExplicit())).toBe(str(A.asExplicit()));
    expect(str(new D(A).asExplicit())).toBe(str(A.asExplicit()));
    expect(() => new ArrayAdd(S.One, S.One)).toThrow(TypeError);
    expect(str(new ArrayAdd(new C(A, [0, 1]), new C(B, [0, 1])).asExplicit())).toBe('A[0, 0] + A[1, 1] + B[0, 0] + B[1, 1]');
    expect(new P(A, [0, 1]).doit()).toBe(A);
    expect(new P(new P(A, [1, 0]), [1, 0]).doit()).toBe(A);
    expect(new C(A, [0, 1]).sortArgsByName().key).toBe(new C(A, [0, 1]).key);
    expect(new P(T, [2, 1, 0]).doit()).toBeInstanceOf(P);
    expect(getShape(S.One)).toEqual([]);
    expect(getShape(new SymArray([1, 2])).map(str)).toEqual(['2']);
    expect(explicitArray(S.One)).toBe(S.One);
    expect(str(new ZeroArray(0, 2).asExplicit())).toBe(refs['empty_explicit']);
  });
  it('preserves values when flattening products, contractions and diagonal axes', () => {
    const exprs = [
      new TP(new C(new TP(M, N), [1, 2]), A),
      new C(new D(new TP(A, B), [0, 2]), [2]),
      new C(new D(new TP(A, B), [0, 2], [1, 3]), [0]),
      new P(new TP(A, B), [2, 3, 0, 1]),
      new P(new TP(A, B), [3, 2, 1, 0]),
      new P(new C(new TP(A, B), [1, 2]), [1, 0]),
      new P(new C(new TP(A, B, T), [0, 1]), [3, 2, 1, 0, 4]),
    ];
    for (const expr of exprs) {
      const a = cast(explicitArray(expr.doit()), SymArray), b = cast(expr.asExplicit(), SymArray);
      expect(a.shape).toEqual(b.shape);
      a.flatElements().forEach((value, i) => {
        const residual = expand(sub(value, at(b.flatElements(), i)));
        expect(str(residual)).toBe('0');
      });
    }
    const sorted = new C(new TP(N, M, A), [0, 1]).sortArgsByName();
    expect(str(sorted)).toContain('ArrayContraction');
  });
  it('routes public array operations to symbolic nodes', () => {
    expect(str(tensorproduct(M, N))).toBe(str(new TP(M, N)));
    expect(str(tensorcontraction(A, [0, 1]))).toBe(str(new C(A, [0, 1])));
    expect(str(tensordiagonal(A, [0, 1]))).toBe(str(new D(A, [0, 1])));
    expect(str(permutedims(A, [1, 0]))).toBe(str(new P(A, [1, 0])));
    expect(str(permutedims(A, { indexOrderOld: 'ij', indexOrderNew: 'ji' }))).toBe(str(new P(A, [1, 0])));
    expect(str(permutedims(A, undefined, { indexOrderOld: 'ij', indexOrderNew: 'ji' }))).toBe(str(new P(A, [1, 0])));
    const explicit = cast(A.asExplicit(), SymArray);
    expect(str(tensorcontraction(explicit, [0, 1]))).toBe(refs['trace_explicit']);
    expect(str(permutedims(explicit, [1, 0]))).toBe(str(new P(A, [1, 0]).asExplicit()));
    expect(str(first(cast(new Reshape(A, [4]).asExplicit(), SymArray).flatElements()))).toBe('A[0, 0]');
  });
});

it('retains the ranks of tensor factors under contractions', async () => {
  const a = await import('../../../../src');
  const x = new a.MatrixSymbol('X',3,3);
  const tp = new a.ArrayTensorProduct(x,x,x);
  expect(tp.subranks).toEqual([2,2,2]);
  expect(new a.ArrayContraction(tp,[1,2]).subranks).toEqual([2,2,2]);
  expect(new a.ArrayContraction(x,[0,1]).subranks).toEqual([2]);
});

it('permutations can be specified by old and new index order strings', async () => {
  const { Permutation } = await import('../../../../src');
  const m = new ArraySymbol('M',[1,2,3,4,5]);
  const p = new P(m,undefined,{indexOrderOld:'ijklm',indexOrderNew:'kijml'});
  expect(p.permutation.arrayForm).toEqual([2,0,1,4,3]);
  expect(p.shape.map(String)).toEqual(['3','1','2','5','4']);
  expect(new P(m, new Permutation([2,0,1,4,3])).key).toBe(p.key);
  expect(() => new P(m)).toThrow(RangeError);
  expect(() => new P(m,undefined,{indexOrderOld:'ijklm'})).toThrow(RangeError);
  expect(() => new P(m,undefined,{indexOrderOld:'ijklm',indexOrderNew:'ij'})).toThrow(RangeError);
  expect(() => new P(m,undefined,{indexOrderOld:'iiklm',indexOrderNew:'ijklm'})).toThrow(RangeError);
  expect(() => new P(m,undefined,{indexOrderOld:'ijklm',indexOrderNew:'ijklz'})).toThrow(RangeError);
});

it('constructs constant-one and elementwise arrays, including scalar shapes', async () => {
  const { OneArray, ArrayElementwiseApplyFunc, Lambda, sin, cos, rebuild } = await import('../../../../src');
  const one = new OneArray(2, 3);
  expect(str(one.asExplicit())).toBe('[[1, 1, 1], [1, 1, 1]]');
  expect(rebuild(one).key).toBe(one.key);
  expect(str(new OneArray().asExplicit())).toBe('1');
  expect(() => new OneArray(Number.MAX_SAFE_INTEGER, 2).asExplicit()).toThrow(NotImplementedError);
  const x = new Sym('x'), y = new Sym('y');
  const e = new ArrayElementwiseApplyFunc(sin, SymArray([x, y]));
  expect(str(e.asExplicit())).toBe('[sin(x), sin(y)]');
  expect(rebuild(e).key).toBe(e.key);
  expect(str(new ArrayElementwiseApplyFunc(Lambda(x, cos(x)), y).asExplicit())).toBe('cos(y)');
  expect(() => new ArrayElementwiseApplyFunc(Lambda([x, y], x), A)).toThrow(RangeError);
});

it('recognizes shapes on derivatives and IndexedBase objects', async () => {
  const { ArrayDerivative, IndexedBase, TensorProduct } = await import('../../../../src');
  expect(getShape(ArrayDerivative(M, N)).map(String)).toEqual(['2', '2', '2', '2']);
  expect(getShape(new IndexedBase('X', { shape: [2, 3] })).map(String)).toEqual(['2', '3']);
  expect(getShape(new IndexedBase('X'))).toEqual([]);
  expect(getShape(TensorProduct([1, 2], M)).map(String)).toEqual(['2', '2', '2']);
});

it('normalizes nested diagonals and diagonals of permutations', () => {
  const A = new ArraySymbol('Q', [2, 2, 2, 2]);
  const nested = new D(new D(A, [0, 2]), [0, 2]);
  expect(str(explicitArray(nested.doit()))).toBe(str(nested.asExplicit()));
  const permuted = new D(new P(A, [3, 2, 1, 0]), [0, 2]);
  expect(str(explicitArray(permuted.doit()))).toBe(str(permuted.asExplicit()));
  const bare = new D(A, [0, 1]);
  expect(bare.doit()).toBe(bare);
  expect(new D(A).doit()).toBe(A);
});

it('contracts permuted diagonals while preserving the remaining axes', () => {
  const A = new ArraySymbol('R', [2, 2, 2, 2, 2, 2]);
  const expr = new C(new P(new D(A, [0, 3]), [2, 4, 0, 3, 1]), [0, 3]);
  expect(str(explicitArray(expr.doit()))).toBe(str(expr.asExplicit()));
  const nested = new D(new D(new D(A, [0, 1]), [0, 1]), [0, 1]);
  expect(str(explicitArray(nested.doit()))).toBe(str(nested.asExplicit()));

});

it('normalizes diagonals beneath outer permutations', () => {
  const Q = new ArraySymbol('Q', [2, 2, 2]);
  const inner = new D(new P(Q, [1, 2, 0]), [0, 2]);
  const expr = new P(inner, [1, 0]);
  expect(str(expr.doit())).toBe(refs['permuted_nested_diagonal_doit']);
  expect(str(explicitArray(expr.doit()))).toBe(str(expr.asExplicit()));
  const stable = new P(new D(Q, [0, 1]), [1, 0]);
  expect(stable.doit()).toBe(stable);
  expect(str(new P(inner, [0, 1]).doit())).toBe('ArrayDiagonal(Q, (0, 1))');
});

it('normalizes array sums and evaluates explicit reshapes and constant entries', async () => {
  const { OneArray } = await import('../../../../src');
  expect(new ArrayAdd(A).doit()).toBe(A);
  expect(str(new ArrayAdd(A, new ArrayAdd(B, A)).doit())).toBe('ArrayAdd(A, B, A)');
  expect(str(new ArrayAdd(A, new ZeroArray(2, 2), B).doit())).toBe('ArrayAdd(A, B)');
  expect(str(new ArrayAdd(new ZeroArray(2, 2)).doit())).toBe('ZeroArray(2, 2)');
  expect(str(new Reshape(SymArray([1, 2, 3, 4]), [2, 2]).doit())).toBe('[[1, 2], [3, 4]]');
  const symbolic = new Reshape(A, [4]);
  expect(symbolic.doit()).toBe(symbolic);
  expect(new ZeroArray().doit()).toBe(S.Zero);
  expect(new OneArray().doit()).toBe(S.One);
  const zero = new ZeroArray(2, 3), one = new OneArray(2, 3);
  expect(zero.doit()).toBe(zero);
  expect(one.doit()).toBe(one);
  expect(zero.at(1, 2)).toBe(S.Zero);
  expect(one.at(1, 2)).toBe(S.One);
  expect(() => zero.at(2, 0)).toThrow(RangeError);
  expect(() => one.at(0)).toThrow(RangeError);
});

it('lifts local permutations and diagonals into outer tensor products', () => {
  const expressions = [
    new TP(new P(A, [1, 0]), B), new TP(A, new P(B, [1, 0])),
    new TP(new D(A, [0, 1]), B), new TP(A, new D(B, [0, 1])),
    new TP(new D(A, [0, 1]), new D(B, [0, 1])),
  ];
  for (const expression of expressions) {
    expect(str(explicitArray(expression.doit()))).toBe(str(expression.asExplicit()));
  }
  expect(str(at(expressions, 0).doit())).toBe('PermuteDims(ArrayTensorProduct(A, B), (3)(0 1))');
  expect(str(at(expressions, 2).doit())).toBe('PermuteDims(ArrayDiagonal(ArrayTensorProduct(A, B), (0, 1)), (0 2 1))');
});

it('nests permutations through array sums and normalizes block permutations', () => {
  const sum = new P(new ArrayAdd(A, B), [1, 0]).nestPermutation();
  expect(str(sum)).toBe('ArrayAdd(PermuteDims(A, (0 1)), PermuteDims(B, (0 1)))');
  expect(str(new P(new TP(A, B), [2, 3, 0, 1]).nestPermutation())).toBe('ArrayTensorProduct(B, A)');
  expect(str(explicitArray(sum))).toBe(str(new P(new ArrayAdd(A, B), [1, 0]).asExplicit()));
});

it('preserves symbolic reshape constraints until dimensions are known', () => {
  expect(new Reshape(A, [n, 2]).shape.map(str)).toEqual(['n', '2']);
});

it('distributes contractions and products over sums and lifts factor permutations', () => {
  const expressions = [
    new TP(new ArrayAdd(A, B), M),
    new C(new ArrayAdd(A, B), [0, 1]),
    new TP(new P(A, [1, 0]), B),
    new C(new TP(new P(A, [1, 0]), B), [1, 2]),
  ];
  for (const expression of expressions) {
    const result = explicitArray(expression.doit()), original = expression.asExplicit();
    if (!(result instanceof SymArray)) {
      expect(str(expand(sub(result, original)))).toBe('0');
      continue;
    }
    const actual = result;
    const expected = cast(original, SymArray);
    expect(actual.shape).toEqual(expected.shape);
    actual.flatElements().forEach((value, i) => expect(str(expand(sub(value, at(expected.flatElements(), i))))).toBe('0'));
  }
});

it('replays the upstream test_array_expressions assertions', () => {
  for (const c of passingModuleCases('tensor', 'sympy.tensor.array.expressions.tests.test_array_expressions')) {
    expect(['pass', 'equivalent'], c.src).toContain(runTestCase(c).status);
  }
});

it('retains contractions of a single array when splitting index links', () => {
  const expr = new C(M, [0, 1]);
  expect(expr.splitMultipleContractions()).toBe(expr);
});
