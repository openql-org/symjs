// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Coverage of the multiset partition traverser: expected values are
 * those of SymPy 1.14 `sympy.utilities.enumerative`
 * (`MultisetPartitionTraverser.enum_range` with `list_visitor`,
 * `decrement_part`, `decrement_part_large`).
 */

import { describe, expect, it } from 'vitest';
import { MultisetPartitionTraverser, PartComponent, listVisitor } from '../src/utilities/enumerative';

/** [multiplicities, lb, ub, list_visitor of each state, discarded]. */
const ENUM_RANGE: [number[], number, number, string[][][], number][] = [[[2, 2], 0, 2, [[["a", "a", "b", "b"]], [["a", "a", "b"], ["b"]], [["a", "a"], ["b", "b"]], [["a", "b", "b"], ["a"]], [["a", "b"], ["a", "b"]]], 0], [[2, 2], 1, 3, [[["a", "a", "b"], ["b"]], [["a", "a"], ["b", "b"]], [["a", "a"], ["b"], ["b"]], [["a", "b", "b"], ["a"]], [["a", "b"], ["a", "b"]], [["a", "b"], ["a"], ["b"]], [["a"], ["a"], ["b", "b"]]], 0], [[1, 1, 1, 1], 1, 3, [[["a", "b", "c"], ["d"]], [["a", "b", "d"], ["c"]], [["a", "b"], ["c", "d"]], [["a", "b"], ["c"], ["d"]], [["a", "c", "d"], ["b"]], [["a", "c"], ["b", "d"]], [["a", "c"], ["b"], ["d"]], [["a", "d"], ["b", "c"]], [["a", "d"], ["b"], ["c"]], [["a"], ["b", "c", "d"]], [["a"], ["b", "c"], ["d"]], [["a"], ["b", "d"], ["c"]], [["a"], ["b"], ["c", "d"]]], 0], [[3, 1], 0, 10, [[["a", "a", "a", "b"]], [["a", "a", "a"], ["b"]], [["a", "a", "b"], ["a"]], [["a", "a"], ["a", "b"]], [["a", "a"], ["a"], ["b"]], [["a", "b"], ["a"], ["a"]], [["a"], ["a"], ["a"], ["b"]]], 0], [[2, 1, 1], 2, 3, [[["a", "a"], ["b"], ["c"]], [["a", "b"], ["a"], ["c"]], [["a", "c"], ["a"], ["b"]], [["a"], ["a"], ["b", "c"]]], 0], [[2, 2, 1], 0, 1, [[["a", "a", "b", "b", "c"]]], 0], [[2], 5, 6, [], 0], [[2, 2], 0, 0, [], 0], [[3, 2, 1], 1, 2, [[["a", "a", "a", "b", "b"], ["c"]], [["a", "a", "a", "b", "c"], ["b"]], [["a", "a", "a", "b"], ["b", "c"]], [["a", "a", "a", "c"], ["b", "b"]], [["a", "a", "a"], ["b", "b", "c"]], [["a", "a", "b", "b", "c"], ["a"]], [["a", "a", "b", "b"], ["a", "c"]], [["a", "a", "b", "c"], ["a", "b"]], [["a", "a", "b"], ["a", "b", "c"]], [["a", "a", "c"], ["a", "b", "b"]], [["a", "a"], ["a", "b", "b", "c"]]], 0], [[4], 1, 3, [[["a", "a", "a"], ["a"]], [["a", "a"], ["a", "a"]], [["a", "a"], ["a"], ["a"]]], 0], [[1, 1, 1], 0, 2, [[["a", "b", "c"]], [["a", "b"], ["c"]], [["a", "c"], ["b"]], [["a"], ["b", "c"]]], 0]];

const mk = (c: number, u: number, v: number): PartComponent => {
  const p = new PartComponent();
  p.c = c;
  p.u = u;
  p.v = v;
  return p;
};

describe('MultisetPartitionTraverser', () => {
  for (const [mult, lb, ub, parts, discarded] of ENUM_RANGE) {
    it(`enum_range(${JSON.stringify(mult)}, ${lb}, ${ub})`, () => {
      const m = new MultisetPartitionTraverser();
      const letters = 'abcdefgh'.slice(0, mult.length).split('');
      // the state is reused: read each partition while iterating
      const got: string[][][] = [];
      for (const st of m.enumRange(mult, lb, ub)) got.push(listVisitor(st, letters));
      expect(got).toEqual(parts);
      expect(m.discarded).toBe(discarded);
    });
  }

  it('decrement_part', () => {
    const m = new MultisetPartitionTraverser();
    let part = [mk(0, 2, 2), mk(1, 2, 2)];
    expect(m.decrementPart(part)).toBe(true);
    expect(part.map(String)).toEqual(['c:0 u:2 v:2', 'c:1 u:2 v:1']);
    part = [mk(0, 1, 1), mk(1, 0, 0)];
    expect(m.decrementPart(part)).toBe(false);
    expect(part.map(String)).toEqual(['c:0 u:1 v:1', 'c:1 u:0 v:0']);
  });

  it('decrement_part_large with amt 1', () => {
    const m = new MultisetPartitionTraverser();
    m.lpart = 0;
    let part = [mk(0, 3, 3), mk(1, 2, 2)];
    expect(m.decrementPartLarge(part, 1, 2)).toBe(true);
    expect(part.map(String)).toEqual(['c:0 u:3 v:3', 'c:1 u:2 v:0']);
    part = [mk(0, 1, 1)];
    expect(m.decrementPartLarge(part, 1, 0)).toBe(false);
    expect(part.map(String)).toEqual(['c:0 u:1 v:1']);
  });
});
