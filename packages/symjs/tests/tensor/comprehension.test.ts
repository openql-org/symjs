// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/comprehension.ts.
// ArrayComprehension. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, latex, mul, symbols } from '../../src';
import { ArrayComprehension, ArrayComprehensionMap } from '../../src/tensor';

// SymPy sympy.tensor.array (every doctest of its modules that implement
// sympy.tensor.array.__all__) and sympy.tensor.indexed.Idx; expected
// values from SymPy 1.14.

const [x, y] = symbols('x y z t');
const s = (v: unknown): string => String(v);

describe('sympy.tensor.array.array_comprehension', () => {
  const [i, j, k] = symbols('i j k');
  const f10ij = add(mul(10, i), j);

  it('ArrayComprehension', () => {
    const ac = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, 3]);
    expect(s(ac)).toBe('ArrayComprehension(10*i + j, (i, 1, 4), (j, 1, 3))');
    expect(s(ac.doit())).toBe('[[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]');
    const bc = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, k]);
    expect(s(bc.doit())).toBe('ArrayComprehension(10*i + j, (i, 1, 4), (j, 1, k))');
    expect(ac.length).toBe(12);
  });

  it('free_symbols, function, is_shape_numeric, limits, rank, shape', () => {
    const ac = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, 3]);
    const bc = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, add(k, 3)]);
    expect(ac.freeSymbols().size).toBe(0);
    expect([...bc.freeSymbols()].map(s)).toEqual(['k']);
    expect(s(ac.function)).toBe('10*i + j');
    expect(ac.isShapeNumeric).toBe(true);
    expect(bc.isShapeNumeric).toBe(false);
    expect(ac.limits.map((l) => `(${l.map(s).join(', ')})`)).toEqual(['(i, 1, 4)', '(j, 1, 3)']);
    expect(ac.rank()).toBe(2);
    expect(ac.shape.map(s)).toEqual(['4', '3']);
    expect(bc.shape.map(s)).toEqual(['4', 'k + 3']);
  });

  it('tolist, tomatrix, variables', () => {
    const ac = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, 3]);
    expect(s(ac.tolist())).toBe(s([[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]));
    expect(s(ac.tomatrix())).toBe('Matrix([[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]])');
    expect(ac.variables.map(s)).toEqual(['i', 'j']);
  });

  it('ArrayComprehensionMap', () => {
    expect(s(ArrayComprehensionMap(() => 1, [i, 1, 4]).doit())).toBe('[1, 1, 1, 1]');
    expect(s(ArrayComprehensionMap((n: number) => n + 1, [j, 1, 4]).doit())).toBe('[2, 3, 4, 5]');
  });
});

describe('array comprehensions: more cases', () => {
  const [i, j] = symbols('i j');
  it('evaluation and shape', () => {
    expect(s(ArrayComprehension(i, [i, 1, 4]).doit())).toBe('[1, 2, 3, 4]');
    const sym = ArrayComprehension(i, [i, 1, y]);
    expect(sym.doit()).toBe(sym);
    expect(sym.shape.map(s)).toEqual(['y']);
    expect(sym.rank()).toBe(1);
    expect(() => sym.length).toThrow('Symbolic length is not supported');
    expect(() => sym.tolist()).toThrow('A symbolic array cannot be expanded to a list');
    expect(() => sym.tomatrix()).toThrow('A symbolic array cannot be expanded to a matrix');
    expect(() => ArrayComprehension(i, [i, 1, 4]).tomatrix()).toThrow('Dimensions must be of size of 2');
    expect(s(ArrayComprehension(i, [i, 1, 2], [j, 1, 2]).doit())).toBe('[[1, 1], [2, 2]]');
    const yy = ArrayComprehension(i, [i, y, add(y, 2)]);
    expect(yy.shape.map(s)).toEqual(['3']);
    expect(yy.isShapeNumeric).toBe(false);
    expect(s(yy.doit())).toBe('ArrayComprehension(i, (i, y, y + 2))');
    expect(s(ArrayComprehension(mul(i, j), [i, 1, 2], [j, 2, 4]).doit())).toBe('[[2, 3, 4], [4, 6, 8]]');
    expect(s(ArrayComprehension(i, [i, -2, 2]).doit())).toBe('[-2, -1, 0, 1, 2]');
    expect(s(ArrayComprehension(i, [j, 1, 4]).doit())).toBe('[i, i, i, i]');
    expect(s(ArrayComprehension(i, [i, 1, 1]).doit())).toBe('[1]');
    expect(s(ArrayComprehension(mul(i, x), [i, 1, 4]).doitSelf())).toBe('[x, 2*x, 3*x, 4*x]');
  });

  it('substitution and free symbols', () => {
    expect(s(ArrayComprehension(i, [i, 1, 4]).subs(x, 2))).toBe('ArrayComprehension(i, (i, 1, 4))');
    expect(s(ArrayComprehension(mul(i, x), [i, 1, 4]).subs(x, 2))).toBe('ArrayComprehension(2*i, (i, 1, 4))');
    const r = ArrayComprehension(mul(i, x), [i, 1, y]).subs(y, 2);
    expect(s(r)).toBe('ArrayComprehension(i*x, (i, 1, 2))');
    expect(s((r as ArrayComprehension).doit())).toBe('[x, 2*x]');
    expect([...ArrayComprehension(mul(i, x), [i, 1, 4]).freeSymbols()].map(s)).toEqual(['x']);
    // the index variable is bound: substituting it changes nothing (SymPy substitutes it)
    expect(s(ArrayComprehension(i, [i, 1, 4]).subs(i, 2))).toBe('ArrayComprehension(i, (i, 1, 4))');
    expect(ArrayComprehension(i, [i, 1, 4]).equals(ArrayComprehension(i, [i, 1, 4]))).toBe(true);
  });

  it('errors', () => {
    expect(() => ArrayComprehension(i, [i, 3, 1])).toThrow('Lower bound should be inferior to upper bound');
    expect(() => ArrayComprehension(i, [i, 1, i])).toThrow('Variable should not be part of its bounds');
    expect(() => ArrayComprehension(i, [i, 1, add(x, 0.5)])).toThrow('Bounds should be an Expression(combination of Integer and Symbol)');
    expect(() => ArrayComprehension(i, [i, 1, [1, 2]] as never)).toThrow('Bounds should be an Expression(combination of Integer and Symbol)');
    expect(() => ArrayComprehension(i, [i, 1] as never)).toThrow('ArrayComprehension requires values lower and upper bound for the expression');
  });

  it('printing', () => {
    expect(latex(ArrayComprehension(add(mul(10, i), j), [i, 1, 4], [j, 1, 3]))).toBe(
      '\\operatorname{ArrayComprehension}\\left(10 i + j, \\left( i, \\  1, \\  4\\right), \\left( j, \\  1, \\  3\\right)\\right)',
    );
    expect(latex(ArrayComprehension(i, [i, 1, 4]))).toBe('\\operatorname{ArrayComprehension}\\left(i, \\left( i, \\  1, \\  4\\right)\\right)');
  });

  it('ArrayComprehensionMap', () => {
    const one = ArrayComprehensionMap(() => 1, [i, 1, 4]);
    expect(s(one)).toBe('ArrayComprehensionMap((i, 1, 4))');
    expect(latex(one)).toBe('\\operatorname{ArrayComprehensionMap}\\left(\\left( i, \\  1, \\  4\\right)\\right)');
    expect(one).toBeInstanceOf(ArrayComprehension);
    expect(s(ArrayComprehensionMap((n: number) => n + 1, [j, 1, 4], [i, 1, 2]).doit())).toBe('[[2, 3], [3, 5], [4, 7], [5, 9]]');
    expect(s(ArrayComprehensionMap((n: number) => n + 1, [j, 1, y]).doit())).toBe('ArrayComprehensionMap((j, 1, y))');
    const sub = ArrayComprehensionMap((n: number) => n * 2, [j, 1, y]).subs(y, 3);
    expect(s((sub as ArrayComprehension).doit())).toBe('[2, 4, 6]');
    expect(() => ArrayComprehensionMap(((p: number, q: number) => p + q) as never, [j, 1, 4])).toThrow(TypeError);
    expect(() => ArrayComprehensionMap(1 as never, [j, 1, 4])).toThrow('Data type not supported');
    expect(() => one.function).toThrow(TypeError);
    expect(one.lambda.length).toBe(0);
    expect(one.equals(ArrayComprehensionMap(() => 2, [i, 1, 4]))).toBe(false);
  });
});

// Edge cases of sympy.tensor.array (slicing, construction, assignment,
// sparse arrays, derivatives), ArrayComprehension and Idx; expected values
// from SymPy 1.14.

const [n] = symbols('n');

describe('ArrayComprehension and Idx', () => {
  it('rank 0 and symbolic shapes', () => {
    // SymPy len(Array(5)) == 1: a rank-0 array has one element (SymPy 1.14
    // fails on len(ArrayComprehension(x)) with AttributeError).
    expect(ArrayComprehension(x).length).toBe(1);
    expect(s(ArrayComprehension(x).doit())).toBe('x');
    expect(() => ArrayComprehension(x, [x, 1, n]).length).toThrow(RangeError);
    expect(ArrayComprehension(x, [x, 1, n]).doitSelf()).toBeUndefined();
    expect(s(ArrayComprehensionMap(() => 1, [x, 1, 2]).doit())).toBe('[1, 1]');
  });
});
