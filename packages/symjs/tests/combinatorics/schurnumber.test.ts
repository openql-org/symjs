// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/schurnumber.ts.
// Schur numbers and sum-free partitions. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { SchurNumber, SchurNumberNode, schurPartition } from '../../src/combinatorics';

const x = sj.symbol('x');
const s = (e: sj.Expr): string => sj.str(e);

describe('SchurNumber', () => {
  it('known values and the unevaluated function', () => {
    expect([0, 1, 3, 5, 6].map((k) => s(SchurNumber(k)))).toEqual(['0', '1', '13', '160', 'SchurNumber(6)']);
    expect(s(SchurNumber(sj.S.Infinity))).toBe('oo');
    expect(s(SchurNumber(x))).toBe('SchurNumber(x)');
    for (const k of [-1, sj.Rational.of(1n, 2n), 2.5]) expect(() => SchurNumber(k)).toThrow(RangeError);
  });
  it('lower bounds', () => {
    const lb = (k: sj.ExprLike): string => s((SchurNumber(k) as SchurNumberNode).lowerBound());
    expect([6, 7, 8].map(lb)).toEqual(['536', '1680', '5039']);
    expect(lb(x)).toBe('3**x/2 - 1/2');
    const node = SchurNumber(6) as SchurNumberNode;
    expect(s(node.withArgs([sj.Rational.of(4n)]))).toBe('44');
  });
});

describe('schur_partition', () => {
  it('partitions into sum-free subsets', () => {
    const cases: [number, number[][]][] = [
      [1, [[1]]],
      [2, [[1, 2]]],
      [3, [[1, 2, 3]]],
      [4, [[1, 4], [2, 3]]],
      [5, [[3, 2], [5], [1, 4]]],
      [8, [[3, 2], [6, 5, 8], [1, 4, 7]]],
      [13, [[3, 12, 2, 11], [6, 9, 5, 8], [1, 4, 7, 10, 13]]],
      [14, [[9, 6, 8, 5], [14], [3, 12, 2, 11], [1, 4, 7, 10, 13]]],
      [45, [[27, 18, 24, 15, 26, 17, 23, 14], [45, 42, 44, 41], [9, 36, 6, 33, 8, 35, 5, 32], [3, 12, 21, 30, 39, 2, 11, 20, 29, 38], [1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, 37, 40, 43]]],
    ];
    for (const [n, p] of cases) expect(schurPartition(n)).toEqual(p);
  });
  it('rejects invalid input', () => {
    expect(() => schurPartition(sj.S.Infinity)).toThrow('Input must be finite');
    expect(() => schurPartition(0)).toThrow('n must be a non-zero positive integer.');
    expect(() => schurPartition(x)).toThrow('Input value must be a number');
  });
});
