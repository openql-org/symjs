// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/combinatorics/partitions.ts (SymPy sympy/combinatorics/partitions.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { IntegerPartition, Partition, RGSEnum, RGSGeneralized, RGSRank, RGSUnrank, finiteSet, latex, pretty, randomIntegerPartition, str, symbols, interval } from '../../src';

const [x] = symbols('x');

describe('Partition', () => {
  it('builds partitions from lists, sets and finite sets', () => {
    const a = new Partition([1, 2], [3]);
    expect(String(a)).toBe('Partition({3}, {1, 2})');
    expect(a.partition.map((p) => p.map(str))).toEqual([['1', '2'], ['3']]);
    expect(a.args.length).toBe(2);
    expect(a.members.map(str)).toEqual(['1', '2', '3']);
    expect(a.size).toBe(3);
    expect(String(new Partition(new Set([1, 2, 3]), new Set([4, 5])))).toBe('Partition({4, 5}, {1, 2, 3})');
    expect(String(new Partition(finiteSet(1, 2, 3), finiteSet(4, 5)))).toBe('Partition({4, 5}, {1, 2, 3})');
  });

  it('is an expression node printed like the set of its blocks (SymPy Partition is a FiniteSet)', () => {
    const [y] = symbols('y');
    const a = new Partition([1, 2], [3]);
    // SymPy latex(Partition([1, 2], [3])), pretty(...) with and without unicode
    expect(latex(a)).toBe('\\left\\{\\left\\{3\\right\\}, \\left\\{1, 2\\right\\}\\right\\}');
    expect(pretty(a)).toBe('{{3}, {1, 2}}');
    expect(pretty(a, { useUnicode: false })).toBe('{{3}, {1, 2}}');
    expect(latex(new Partition([x, y], [3]))).toBe('\\left\\{\\left\\{3\\right\\}, \\left\\{x, y\\right\\}\\right\\}');
    // SymPy latex(Partition([1, 2], [3]) + 1)
    expect(latex(a.add(1))).toBe('\\left\\{\\left\\{2\\right\\}, \\left\\{1, 3\\right\\}\\right\\}');
    // the blocks are in SymPy's order whatever the order of the arguments: Partition([3], [1, 2]) == Partition([1, 2], [3])
    expect(new Partition([3], [1, 2]).equals(a)).toBe(true);
    expect(a.args.map(str)).toEqual(['{3}', '{1, 2}']);
    // substitution rebuilds the partition (SymPy Partition([x, y], [3]).subs(x, 1))
    expect(String(new Partition([x, y], [3]).subs(x, 1))).toBe('Partition({3}, {1, y})');
  });

  it('ranks and orders partitions', () => {
    const a = new Partition([1, 2], [3]);
    expect(a.rank).toBe(1n);
    expect(a.add(1).rank).toBe(2n);
    expect(a.add(100).rank).toBe(1n);
    expect(a.sub(1).rank).toBe(0n);
    expect(String(a.add(1))).toBe('Partition({2}, {1, 3})');

    const p = new Partition([1, 2], [3, 4, 5]);
    const q = new Partition([1], [2, 3], [4], [5]);
    expect([p.rank, q.rank]).toEqual([9n, 34n]);
    expect([p.le(p), p.le(q), p.lt(q), q.lt(p)]).toEqual([true, true, true, false]);

    const b = new Partition([1, 2]);
    const l = [new Partition([0, 1, 2, 3]), new Partition([3, 4]), b.add(1), b, new Partition([1, x])];
    expect(l.sort((u, v) => u.compare(v)).map(String)).toEqual(['Partition({1, 2})', 'Partition({1}, {2})', 'Partition({1, x})', 'Partition({3, 4})', 'Partition({0, 1, 2, 3})']);

    const c = new Partition([1, 2], [3], [4, 5]);
    expect(c.rank).toBe(13n);
    expect(c.RGS).toEqual([0, 0, 1, 2, 2]);
    expect(String(c.add(1))).toBe('Partition({3}, {4}, {5}, {1, 2})');
    expect(c.add(1).RGS).toEqual([0, 0, 1, 2, 3]);
  });

  it('builds partitions from restricted growth strings', () => {
    expect(String(Partition.fromRgs([0, 1, 2, 0, 1], ['a', 'b', 'c', 'd', 'e']))).toBe('Partition({c}, {a, d}, {b, e})');
    expect(String(Partition.fromRgs([0, 1, 2, 0, 1], ['c', 'b', 'e', 'a', 'd']))).toBe('Partition({e}, {a, c}, {b, d})');
    const a = new Partition([1, 4], [2], [3, 5]);
    expect(String(Partition.fromRgs(a.RGS, a.members))).toBe('Partition({2}, {1, 4}, {3, 5})');
  });

  it('rejects invalid partitions', () => {
    expect(() => new Partition([1, 1])).toThrow('Partition contained duplicate elements.');
    expect(() => new Partition([1, 2], [2])).toThrow('Partition contained duplicate elements.');
    expect(() => new Partition([1, 2], [1, 2])).toThrow('Partition contained duplicate elements.');
    expect(() => new Partition(interval(0, 1))).toThrow('Each argument to Partition should be a list, set, or a FiniteSet');
    expect(() => new Partition([])).toThrow('Each argument to Partition should be a list, set, or a FiniteSet');
    expect(() => Partition.fromRgs([0, 2], [1, 2])).toThrow('some blocks of the partition were empty.');
    expect(() => Partition.fromRgs([0], [1, 2])).toThrow('mismatch in rgs and element lengths');
  });
});

describe('IntegerPartition', () => {
  it('builds integer partitions', () => {
    const a = new IntegerPartition([5, 4, 3, 1, 1]);
    expect(a.repr()).toBe('IntegerPartition(14, (5, 4, 3, 1, 1))');
    expect(String(a)).toBe('[5, 4, 3, 1, 1]');
    expect(a.integer).toBe(14);
    expect(new IntegerPartition(new Map([[1, 3], [2, 1]])).repr()).toBe('IntegerPartition(5, (2, 1, 1, 1))');
    expect(new IntegerPartition(new Map([[1, 3], [2, 0]])).repr()).toBe('IntegerPartition(3, (1, 1, 1))');
    expect(new IntegerPartition(7n, [7]).repr()).toBe('IntegerPartition(7, (7,))');
    expect(() => new IntegerPartition(10, [5, 4, 3, 1])).toThrow('Partition did not add to 10');
    expect(() => new IntegerPartition([0, 1])).toThrow('All integer summands must be greater than one');
    expect(() => new IntegerPartition([1.5])).toThrow('1.5 is not an integer');
    // @ts-expect-error an integer without the parts
    expect(() => new IntegerPartition(5)).toThrow(TypeError);
  });

  it('steps through partitions in lexical order', () => {
    expect(String(new IntegerPartition([4]).prevLex())).toBe('[3, 1]');
    const walk = (start: number[], n: number, step: (p: IntegerPartition) => IntegerPartition): string[] => {
      const out: string[] = [];
      let p = new IntegerPartition(start);
      for (let i = 0; i < n; i++) {
        out.push(String(p));
        p = step(p);
      }
      return out;
    };
    const next = (p: IntegerPartition) => p.nextLex();
    const prev = (p: IntegerPartition) => p.prevLex();
    expect(walk([1, 1, 1, 1, 1, 1], 12, next)).toEqual(['[1, 1, 1, 1, 1, 1]', '[2, 1, 1, 1, 1]', '[2, 2, 1, 1]', '[2, 2, 2]', '[3, 1, 1, 1]', '[3, 2, 1]', '[3, 3]', '[4, 1, 1]', '[4, 2]', '[5, 1]', '[6]', '[1, 1, 1, 1, 1, 1]']);
    expect(walk([6], 12, prev)).toEqual(['[6]', '[5, 1]', '[4, 2]', '[4, 1, 1]', '[3, 3]', '[3, 2, 1]', '[3, 1, 1, 1]', '[2, 2, 2]', '[2, 2, 1, 1]', '[2, 1, 1, 1, 1]', '[1, 1, 1, 1, 1, 1]', '[6]']);
    expect(walk([1, 1, 1, 1, 1, 1, 1, 1], 25, next)).toEqual([
      '[1, 1, 1, 1, 1, 1, 1, 1]', '[2, 1, 1, 1, 1, 1, 1]', '[2, 2, 1, 1, 1, 1]', '[2, 2, 2, 1, 1]', '[2, 2, 2, 2]', '[3, 1, 1, 1, 1, 1]', '[3, 2, 1, 1, 1]',
      '[3, 2, 2, 1]', '[3, 3, 1, 1]', '[3, 3, 2]', '[4, 1, 1, 1, 1]', '[4, 2, 1, 1]', '[4, 2, 2]', '[4, 3, 1]', '[4, 4]', '[5, 1, 1, 1]', '[5, 2, 1]', '[5, 3]',
      '[6, 1, 1]', '[6, 2]', '[7, 1]', '[8]', '[1, 1, 1, 1, 1, 1, 1, 1]', '[2, 1, 1, 1, 1, 1, 1]', '[2, 2, 1, 1, 1, 1]',
    ]);
    expect(walk([8], 25, prev)).toEqual([
      '[8]', '[7, 1]', '[6, 2]', '[6, 1, 1]', '[5, 3]', '[5, 2, 1]', '[5, 1, 1, 1]', '[4, 4]', '[4, 3, 1]', '[4, 2, 2]', '[4, 2, 1, 1]', '[4, 1, 1, 1, 1]',
      '[3, 3, 2]', '[3, 3, 1, 1]', '[3, 2, 2, 1]', '[3, 2, 1, 1, 1]', '[3, 1, 1, 1, 1, 1]', '[2, 2, 2, 2]', '[2, 2, 2, 1, 1]', '[2, 2, 1, 1, 1, 1]',
      '[2, 1, 1, 1, 1, 1, 1]', '[1, 1, 1, 1, 1, 1, 1, 1]', '[8]', '[7, 1]', '[6, 2]',
    ]);
  });

  it('has the dictionary, conjugate, order and Ferrers diagram', () => {
    expect([...new IntegerPartition([1, 1, 1, 2, 3, 3, 3, 3]).asDict()]).toEqual([
      [3, 4],
      [2, 1],
      [1, 3],
    ]);
    expect(new IntegerPartition([6, 3, 3, 2, 1]).conjugate).toEqual([5, 4, 3, 1, 1, 1]);
    const a = new IntegerPartition([3, 1]);
    const b = a.nextLex();
    expect([a.lt(a), a.lt(b), a.le(a), b.lt(a), b.le(a)]).toEqual([false, true, true, false, false]);
    expect(new IntegerPartition([2, 1, 1]).lt(new IntegerPartition([2, 1]))).toBe(true);
    expect(new IntegerPartition([1, 1, 1, 1]).lt(new IntegerPartition([1, 1, 1]))).toBe(false);
    expect(new IntegerPartition([1, 1, 5]).asFerrers()).toBe('#####\n#\n#');
    expect(new IntegerPartition([2, 2]).asFerrers('*')).toBe('**\n**');
  });
});

describe('restricted growth strings', () => {
  it('counts, ranks and unranks', () => {
    expect(RGSGeneralized(6).toArray().map((r) => r.map(str))).toEqual(
      [
        [1, 1, 1, 1, 1, 1, 1],
        [1, 2, 3, 4, 5, 6, 0],
        [2, 5, 10, 17, 26, 0, 0],
        [5, 15, 37, 77, 0, 0, 0],
        [15, 52, 151, 0, 0, 0, 0],
        [52, 203, 0, 0, 0, 0, 0],
        [203, 0, 0, 0, 0, 0, 0],
      ].map((r) => r.map(String)),
    );
    expect([RGSEnum(4), RGSEnum(5), RGSEnum(6), RGSEnum(0), RGSEnum(1)]).toEqual([15n, 52n, 203n, 0n, 1n]);
    expect(RGSUnrank(14, 4)).toEqual([0, 1, 2, 3]);
    expect(RGSUnrank(0, 4)).toEqual([0, 0, 0, 0]);
    expect(RGSUnrank(4n, 7)).toEqual([0, 0, 0, 0, 0, 1, 2]);
    expect(RGSUnrank(0, 1)).toEqual([0]);
    expect(RGSRank([0, 1, 2, 1, 3])).toBe(42n);
    expect(RGSRank(RGSUnrank(4, 7))).toBe(4n);
    expect([RGSRank([0]), RGSRank([])]).toEqual([0n, 0n]);
    expect(() => RGSUnrank(0, 0)).toThrow('The superset size must be >= 1');
    expect(() => RGSUnrank(15, 4)).toThrow('Invalid arguments');
    expect(() => RGSUnrank(-1, 4)).toThrow('Invalid arguments');
  });

  it('draws random integer partitions', () => {
    expect(randomIntegerPartition(100, [1, 1, 12, 1, 2, 1, 85, 1])).toEqual([85, 12, 2, 1]);
    expect(randomIntegerPartition(10, [1, 2, 3, 1, 5, 1])).toEqual([5, 3, 1, 1]);
    expect(randomIntegerPartition(1)).toEqual([1]);
    expect(randomIntegerPartition(4, [1, 1, 1, 1, 1, 1, 1, 1])).toEqual([1, 1, 1, 1]);
    const r = randomIntegerPartition(20n);
    expect(r.reduce((s, v) => s + v, 0)).toBe(20);
    expect(() => randomIntegerPartition(0)).toThrow('n must be a positive integer');
    expect(() => randomIntegerPartition(10, [1])).toThrow(RangeError);
    expect(() => randomIntegerPartition(10, [11])).toThrow(RangeError);
    expect(() => randomIntegerPartition(10, [0])).toThrow(RangeError);
  });
});
