// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of combinatorics/permutations.ts; expected values are those of SymPy 1.14
// (sympy.combinatorics.Permutation).
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Rational } from '../src/core/nodes';
import { xreplace } from '../src/core/traverse';
import { AppliedPermutation, Permutation, afRmul } from '../src/combinatorics';

describe('Permutation', () => {
  it('integer arguments given as Integers and bigints', () => {
    expect(new Permutation(sj.sympify(3)).arrayForm).toEqual([0, 1, 2, 3]);
    // SymPy: TypeError 'Rational' object cannot be interpreted as an integer
    expect(() => new Permutation(Rational.of(1n, 2n))).toThrow(TypeError);
    // SymPy would build a list of 2**60 elements
    expect(() => new Permutation(2n ** 60n)).toThrow('value 1152921504606846976 is too large');
    // options without a size
    expect(new Permutation([1, 0], {}).arrayForm).toEqual([1, 0]);
  });

  it('subtraction below rank 0 wraps around', () => {
    expect(new Permutation([0, 1, 2]).sub(1).arrayForm).toEqual([2, 1, 0]);
  });

  it('powers with a non-integer exponent', () => {
    // SymPy truncates the exponent with int(): p**2.5 and p**Rational(1, 2) are p**2 and p**0;
    // symjs rejects them
    const p = new Permutation([1, 0, 2]);
    expect(() => p.pow(2.5)).toThrow(TypeError);
    expect(() => p.pow(Rational.of(1n, 2n))).toThrow(TypeError);
    expect(p.pow(sj.sympify(2)).arrayForm).toEqual([0, 1, 2]);
  });

  it('from_sequence with strings, lists and big keys', () => {
    expect(Permutation.fromSequence('aab').arrayForm).toEqual([0, 1, 2]);
    expect(Permutation.fromSequence('bab').arrayForm).toEqual([1, 0, 2]);
    expect(Permutation.fromSequence([[1, 2], [1], [0, 5], [1, 2]]).arrayForm).toEqual([2, 1, 0, 3]);
    expect(Permutation.fromSequence([3, 1, 2], (x) => -BigInt(x) * 10n ** 20n).arrayForm).toEqual([0, 2, 1]);
    expect(Permutation.fromSequence([3n, 1, 2]).arrayForm).toEqual([2, 0, 1]);
    // SymPy: TypeError '<' not supported between instances of 'str' and 'int'
    expect(() => Permutation.fromSequence<unknown>([1, 'a'])).toThrow(TypeError);
  });

  it('unrank_trotterjohnson', () => {
    expect([0, 1, 2, 3, 4, 5].map((r) => Permutation.unrankTrotterjohnson(3, r).arrayForm)).toEqual([
      [0, 1, 2],
      [0, 2, 1],
      [2, 0, 1],
      [2, 1, 0],
      [1, 2, 0],
      [1, 0, 2],
    ]);
    expect(Permutation.unrankTrotterjohnson(4, 5).arrayForm).toEqual([0, 3, 2, 1]);
    // SymPy gives [0, 0, 2] and [0, 2, 0] (not permutations) for the ranks -1 and 7, and IndexError for -5
    expect(() => Permutation.unrankTrotterjohnson(3, -1)).toThrow('rank must be in [0, 6), got -1');
    expect(() => Permutation.unrankTrotterjohnson(3, 7)).toThrow(RangeError);
  });

  it('_af_rmul with Python indexing', () => {
    expect(afRmul([0, 1, 2], [-1, 0, 1])).toEqual([2, 0, 1]);
    // SymPy: IndexError list index out of range
    expect(() => afRmul([0, 1], [2, 0])).toThrow('list index out of range');
  });

  it('rebuilding', () => {
    const p = new Permutation([1, 0, 2]);
    // a Permutation has no expression arguments: rebuilding gives itself
    expect(p.withArgs([])).toBe(p);
    const [x, y] = sj.symbols('x y');
    const a = AppliedPermutation.of(p, x);
    expect(String(xreplace(a, new Map([[x, sj.sympify(1)]])))).toBe('0');
    // SymPy: ValueError y must be a Permutation instance
    expect(() => xreplace(a, new Map([[p, y]]))).toThrow(TypeError);
  });
});
