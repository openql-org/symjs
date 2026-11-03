// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/sets.ts.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { S } from '../../src/core/nodes';
import type { Expr } from '../../src/core/nodes';
import { str } from '../../src/printing/str';
import * as Sets from '../../src/sets/sets';

const [x, y] = sj.symbols('x y');
const uni = (e: unknown): string => sj.pretty(e as Expr, { useUnicode: true });

/**
 * Coverage of the str printer and the printing sort keys: expected
 * values are SymPy 1.14 `str(expr)`, `latex(expr)` and
 * `expr.as_ordered_terms()` / `sorted(..., key=default_sort_key)`.
 */

describe('str of sets', () => {
  const I01 = Sets.interval(0, 1);
  const I23 = Sets.interval(2, 3);
  const cases: [string, () => sj.Expr, string][] = [
    ['S.Reals', () => Sets.Reals, 'Reals'],
    ['S.Integers', () => Sets.Integers, 'Integers'],
    ['S.Naturals', () => Sets.Naturals, 'Naturals'],
    ['S.Naturals0', () => Sets.Naturals0, 'Naturals0'],
    ['S.Complexes', () => Sets.Complexes, 'Complexes'],
    ['S.EmptySet', () => Sets.EmptySet, 'EmptySet'],
    ['S.UniversalSet', () => Sets.UniversalSet, 'UniversalSet'],
    ['Interval(0, 1)', () => I01, 'Interval(0, 1)'],
    ['Interval.open(0, 1)', () => Sets.openInterval(0, 1), 'Interval.open(0, 1)'],
    ['Interval.Lopen(0, x)', () => Sets.Lopen(0, x), 'Interval.Lopen(0, x)'],
    ['Interval.Ropen(-oo, 1)', () => Sets.Ropen(S.NegativeInfinity, 1), 'Interval.open(-oo, 1)'],
    ['Interval.Ropen(0, 1)', () => Sets.Ropen(0, 1), 'Interval.Ropen(0, 1)'],
    ['FiniteSet(y, 1, x)', () => Sets.finiteSet(y, 1, x), '{1, x, y}'],
    ['Union(Interval(2, 3), Interval(0, 1))', () => Sets.union(I23, I01), 'Union(Interval(0, 1), Interval(2, 3))'],
    ['Intersection(Interval(0, x), FiniteSet(y), evaluate=False)', () => new Sets.SetOp('Intersection', [Sets.interval(0, x), Sets.finiteSet(y)]), 'Intersection({y}, Interval(0, x))'],
    ['Complement(Interval(0, 1), FiniteSet(x), evaluate=False)', () => new Sets.SetOp('Complement', [I01, Sets.finiteSet(x)]), 'Complement(Interval(0, 1), {x})'],
    [
      'Intersection(Union(Interval(0, 1), Interval(2, 3)), Interval(x, y), evaluate=False)',
      () => new Sets.SetOp('Intersection', [new Sets.SetOp('Union', [I01, I23]), Sets.interval(x, y)]),
      'Intersection(Interval(x, y), Union(Interval(0, 1), Interval(2, 3)))',
    ],
    ['ImageSet(Lambda(x, x**2), S.Naturals)', () => new Sets.ImageSet(x, sj.pow(x, 2), Sets.Naturals), 'ImageSet(Lambda(x, x**2), Naturals)'],
    ['ConditionSet(x, x > 0, S.UniversalSet)', () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.UniversalSet), 'ConditionSet(x, x > 0)'],
    ['ConditionSet(x, x > 0, S.Reals)', () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals), 'ConditionSet(x, x > 0, Reals)'],
    ['Union(Interval(0, 1), FiniteSet(0, 5), evaluate=False)', () => new Sets.SetOp('Union', [I01, Sets.finiteSet(0, 5)]), 'Union({0, 5}, Interval(0, 1))'],
  ];
  for (const [label, build, want] of cases) it(label, () => expect(str(build())).toBe(want));
});

/**
 * Coverage of printing/sets.ts, sortkey.ts, str.ts and the pretty printer
 * (pretty.ts, stringpict.ts, symbology.ts). Expected strings from SymPy 1.14
 * (str, pretty with and without unicode, latex, default_sort_key).
 */

describe('sets: argument order of Union and Intersection', () => {
  const I = (a: sj.ExprLike, b: sj.ExprLike) => Sets.interval(a, b);
  const F = (...a: sj.ExprLike[]) => Sets.finiteSet(...a);
  it('orders by infimum, then by node count and sort key', () => {
    const cases: [Expr, string, string][] = [
      // SymPy str, pretty(use_unicode=True)
      [Sets.union(I(sj.mul(-1, sj.oo), 0), F(5)), 'Union({5}, Interval(-oo, 0))', '(-∞, 0] ∪ {5}'],
      [Sets.union(F(1, sj.oo), I(2, 3)), 'Union({1, oo}, Interval(2, 3))', '{1, ∞} ∪ [2, 3]'],
      [Sets.union(F(sj.zoo), I(0, 1)), 'Union({zoo}, Interval(0, 1))', '[0, 1] ∪ {zoo}'],
      [Sets.union(F(sj.I), I(0, 1)), 'Union({I}, Interval(0, 1))', '[0, 1] ∪ {ⅈ}'],
      [Sets.union(F(sj.nan), I(0, 1)), 'Union({nan}, Interval(0, 1))', '[0, 1] ∪ {nan}'],
      [Sets.intersection(Sets.union(I(0, 1), F(x)), I(y, 2)), 'Union(Intersection({x}, Interval(y, 2)), Intersection(Interval(0, 1), Interval(y, 2)))', '({x} ∩ [y, 2]) ∪ ([0, 1] ∩ [y, 2])'],
      // both infima unknown: SymPy's ordered() puts the one with fewer nodes first
      [
        Sets.intersection(Sets.union(I(0, 1), F(x)), Sets.union(I(5, 6), F(y))),
        'Union(Intersection({x}, Union({y}, Interval(5, 6))), Intersection({y}, Interval(0, 1)))',
        '([0, 1] ∩ {y}) ∪ ({x} ∩ ([5, 6] ∪ {y}))',
      ],
    ];
    for (const [e, s, p] of cases) expect([sj.str(e), uni(e)]).toEqual([s, p]);
    const last = Sets.intersection(Sets.union(I(0, 1), F(x)), Sets.union(I(5, 6), F(y)));
    expect(sj.latex(last)).toBe(
      '\\left(\\left[0, 1\\right] \\cap \\left\\{y\\right\\}\\right) \\cup \\left(\\left\\{x\\right\\} \\cap \\left(\\left[5, 6\\right] \\cup \\left\\{y\\right\\}\\right)\\right)',
    );
  });
});
