// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of utilities/iterables.ts, enumerative.ts, values.ts and itertools.ts.
// Expected values are those of SymPy 1.14 (sympy.utilities.iterables, enumerative, ordered)
// and of Python's itertools; JavaScript-only cases say so.
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import * as I from '../src/utilities';
import { Rational } from '../src/core/nodes';
import { MultisetPartitionTraverser, PartComponent } from '../src/utilities/enumerative';
import { compareValues, defaultSortKeyOf, orderedValues } from '../src/utilities/values';
import { combinationsWithReplacement, permutations, product } from '../src/utilities/itertools';

const [x] = sj.symbols('x');
const str = (xs: Iterable<unknown>): string[] => [...xs].map(String);

describe('iterables', () => {
  it('type tests with Number, Boolean and BigInt', () => {
    // SymPy is_sequence(5, int) and is_sequence(True, bool) are True
    expect(I.isSequence(5, Number)).toBe(true);
    // oxlint-disable-next-line no-new-wrappers -- a boxed primitive is an instance of its wrapper class
    expect(I.isSequence(new Number(5), Number)).toBe(true);
    expect(I.isSequence(true, Boolean)).toBe(true);
    // oxlint-disable-next-line no-new-wrappers -- a boxed primitive is an instance of its wrapper class
    expect(I.isSequence(new Boolean(false), Boolean)).toBe(true);
    expect(I.isSequence(5n, BigInt)).toBe(true);
    expect(I.isSequence(5, BigInt)).toBe(false);
  });

  it('is_palindromic with integer arguments (sympy.ntheory.digits)', () => {
    expect(I.isPalindromic(sj.sympify(121))).toBe(true);
    // SymPy: ValueError 2.5 is not an integer / 1/2 is not an integer
    expect(() => I.isPalindromic(121, 2.5)).toThrow(TypeError);
    expect(() => I.isPalindromic(Rational.of(1n, 2n))).toThrow(TypeError);
  });

  it('flatten with levels=0 of a set, iproduct of one iterable, ibin', () => {
    // SymPy flatten({1, (2,)}, levels=0) returns the set itself
    expect(I.flatten(new Set([1, [2]]), { levels: 0 })).toEqual([1, [2]]);
    expect([...I.iproduct([1, 2])]).toEqual([[1], [2]]);
    // SymPy: ValueError `bits` must be >= 0
    expect(() => I.ibin(0, -1)).toThrow('`bits` must be >= 0');
    // SymPy as_int: ValueError
    expect(() => I.ibin(2.5)).toThrow(TypeError);
  });

  it('sift with binary keys given as Integers and booleans', () => {
    expect(I.sift([1, 2, 3], (v) => sj.sympify(v % 2), { binary: true })).toEqual([[1, 3], [2]]);
    // SymPy raises ValueError for S.true/S.false keys (not tuple indices); symjs reads them as True/False
    expect(I.sift([1, 2, 3], (v) => (v > 1 ? sj.S.true : sj.S.false), { binary: true })).toEqual([[2, 3], [1]]);
  });

  it('common_prefix, rotations of empty sequences', () => {
    // SymPy common_prefix() raises ValueError (min of an empty sequence)
    expect(I.commonPrefix()).toEqual([]);
    // SymPy common_suffix() raises ValueError too; common_suffix([1, 2], []) is []
    expect(I.commonSuffix()).toEqual([]);
    expect(I.commonSuffix([1, 2], [])).toEqual([]);
    // SymPy rotate_left('', 1) and rotate_right('', 1) give []; symjs keeps the string type
    expect(I.rotateLeft('', 1)).toBe('');
    expect(I.rotateRight('', 1)).toBe('');
    expect(I.rotateRight([], 1)).toEqual([]);
    expect(I.rotateRight('abc', 1)).toBe('cab');
  });

  it('topological_sort with equal keys', () => {
    expect(I.topologicalSort([[1, 2, 3], []], () => 0)).toEqual([3, 2, 1]);
    // (SymPy starts from a set of vertices: with vertices given out of order the ties follow Python's set order)
    expect(I.topologicalSort([[1, 2, 3], [[3, 1]]], () => 0)).toEqual([3, 1, 2]);
  });

  it('strongly connected components with an edge outside the graph', () => {
    // SymPy: KeyError 2
    expect(() => I.stronglyConnectedComponents([[1], [[1, 2]]])).toThrow('edge to a vertex not in the graph: 2');
    expect(() => I.stronglyConnectedComponents([[1], [[2, 1]]])).toThrow('edge from a vertex not in the graph: 2');
    expect(() => I.connectedComponents([[1], [[1, 2]]])).toThrow(RangeError);
  });

  it('multiset combinations, permutations and partitions', () => {
    expect([...I.multisetCombinations(new Map([['a', 1]]), 2)]).toEqual([]);
    expect([...I.multisetPermutations(new Map([['a', 2]]), 2)]).toEqual([['a', 'a']]);
    expect([...I.multisetPermutations([1, 1, 1], 2)]).toEqual([[1, 1]]);
    expect([...I.multisetPartitions(3, 1)]).toEqual([[[0, 1, 2]]]);
    expect([...I.multisetPartitions([1, 1], 1)]).toEqual([[[1, 1]]]);
    expect([...I.multisetPartitions([1, 1, 1], 2)]).toEqual([[[1], [1, 1]]]);
    expect([...I.multisetPartitions([1, 2], 3)]).toEqual([]);
  });

  it('derangements', () => {
    // SymPy multiset_derangements([]) raises ValueError (max of an empty sequence)
    expect([...I.multisetDerangements([])]).toEqual([]);
    expect([...I.multisetDerangements([1, 2])]).toEqual([[2, 1]]);
    expect([...I.multisetDerangements([1, 2, 3])]).toEqual([[2, 3, 1], [3, 1, 2]]);
    expect([...I.multisetDerangements([1, 2, 3, 4])].slice(0, 4)).toEqual([
      [2, 1, 4, 3],
      [2, 3, 4, 1],
      [2, 4, 1, 3],
      [3, 1, 4, 2],
    ]);
    expect([...I.generateDerangements([1])]).toEqual([]);
    expect([...I.generateDerangements([])]).toEqual([]);
    // not strict: as few elements as possible stay in place (the result depends on the random choice)
    for (const seed of [1, 2, 3]) {
      const t = 'aaaab'.split('');
      const d = I.randomDerangement(t, seed, { strict: false });
      expect([...d].sort()).toEqual([...t].sort());
      expect(d.filter((c, i) => c === t[i]).length).toBe(3);
    }
  });

  it('sequence_partitions_empty of a string, permute_signs, postorder_traversal with keys', () => {
    expect([...I.sequencePartitionsEmpty('ab', 2)]).toEqual([['', 'ab'], ['a', 'b'], ['ab', '']]);
    expect([...I.sequencePartitionsEmpty('ab', 1)]).toEqual([['ab']]);
    expect([...I.permuteSigns([x, 0])].map(str)).toEqual([['x', '0'], ['-x', '0']]);
    const e = sj.add(x, sj.mul(2, sj.pow(x, 2)));
    expect(str(I.postorderTraversal(e, defaultSortKeyOf))).toEqual(['x', '2', '2', 'x', 'x**2', '2*x**2', '2*x**2 + x']);
  });
});

describe('enumerative', () => {
  const mk = (c: number, u: number, v: number): PartComponent => {
    const p = new PartComponent();
    p.c = c;
    p.u = u;
    p.v = v;
    return p;
  };

  it('enum_range without a number of parts in range', () => {
    // SymPy raises IndexError for ub = 1 <= lb (symjs looped forever) and yields nothing for 1 < ub <= lb
    for (const [m, lb, ub] of [
      [[2], 1, 1],
      [[1, 1, 1], 2, 1],
      [[2, 2], 2, 2],
    ] as const) {
      const t = new MultisetPartitionTraverser();
      expect([...t.enumRange(m, lb, ub)]).toEqual([]);
    }
  });

  it('decrement_part, decrement_part_large and decrement_part_small (SymPy MultisetPartitionTraverser)', () => {
    const m = new MultisetPartitionTraverser();
    let part = [mk(0, 2, 2), mk(1, 2, 0)];
    expect(m.decrementPart(part)).toBe(true);
    expect(part.map(String)).toEqual(['c:0 u:2 v:1', 'c:1 u:2 v:2']);
    m.lpart = 0;
    part = [mk(0, 2, 2)];
    expect(m.decrementPartLarge(part, 0, 3)).toBe(false);
    expect(part.map(String)).toEqual(['c:0 u:2 v:2']);
    part = [mk(0, 3, 3), mk(1, 2, 2)];
    expect(m.decrementPartLarge(part, 0, 4)).toBe(true);
    expect(part.map(String)).toEqual(['c:0 u:3 v:1', 'c:1 u:2 v:0']);
    part = [mk(0, 3, 3), mk(1, 1, 1)];
    expect(m.decrementPartLarge(part, 0, 3)).toBe(true);
    expect(part.map(String)).toEqual(['c:0 u:3 v:1', 'c:1 u:1 v:0']);
    part = [mk(0, 1, 1), mk(1, 0, 0)];
    expect(m.decrementPartSmall(part, 3)).toBe(false);
    expect(part.map(String)).toEqual(['c:0 u:1 v:1', 'c:1 u:0 v:0']);
    part = [mk(0, 2, 2), mk(1, 1, 0)];
    expect(m.decrementPartSmall(part, 5)).toBe(true);
    expect(part.map(String)).toEqual(['c:0 u:2 v:1', 'c:1 u:1 v:1']);
    part = [mk(0, 2, 1)];
    expect(m.decrementPartSmall(part, 5)).toBe(false);
    expect(part.map(String)).toEqual(['c:0 u:2 v:1']);
  });
});

describe('values', () => {
  it('compareValues of mixed values (Python <)', () => {
    expect(compareValues(1, true)).toBe(0);
    expect(compareValues('a', 'a')).toBe(0);
    expect(compareValues(sj.sympify(2), sj.sympify(2))).toBe(0);
    expect(compareValues(sj.sympify(1), true)).toBe(0);
    expect(compareValues(sj.sympify(2), false)).toBe(1);
    // JavaScript only: an object without a constructor
    expect(() => compareValues(Object.create(null), 1)).toThrow("'<' not supported between object and number");
  });

  it('defaultSortKeyOf of other iterables and primitives (JavaScript only)', () => {
    const gen = (function* () {
      yield 1;
    })();
    expect(JSON.stringify(defaultSortKeyOf(gen)).startsWith('[[10,0,""]')).toBe(true);
    expect(JSON.stringify(defaultSortKeyOf(null))).toContain('"null"');
  });

  it('ordered with no keys', () => {
    // SymPy ordered([3, 1, 2], []) is [1, 2, 3]; with default=False: ValueError
    expect(orderedValues([3, 1, 2], [])).toEqual([1, 2, 3]);
    expect(() => orderedValues([3, 1, 2], [], false)).toThrow('if default=False then keys must be provided');
    expect(() => orderedValues([3, 1, 2], null, false)).toThrow(RangeError);
  });
});

describe('itertools', () => {
  it('empty results', () => {
    expect([...permutations([1, 2], 3)]).toEqual([]);
    expect([...permutations([1, 2], -1)]).toEqual([]);
    expect([...combinationsWithReplacement([], 2)]).toEqual([]);
    expect([...combinationsWithReplacement([1], -1)]).toEqual([]);
    expect([...product([[1], []])]).toEqual([]);
  });
});
