// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Coverage of the str printer and the printing sort keys: expected
 * values are SymPy 1.14 `str(expr)`, `latex(expr)` and
 * `expr.as_ordered_terms()` / `sorted(..., key=default_sort_key)`.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Add, Float, Limit, Mul, Pow, Rational, S } from '../src/core/nodes';
import { latex } from '../src/printing/latex';
import { asOrderedTerms, compareKeys, sortKey } from '../src/printing/sortkey';
import { str } from '../src/printing/str';
import * as Sets from '../src/sets/sets';

const [x, y, z] = sj.symbols('x y z');
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));

describe('str', () => {
  const cases: [string, () => sj.Expr, string][] = [
    ['Pow(-oo, x, evaluate=False)', () => new Pow(S.NegativeInfinity, x), '(-oo)**x'],
    ['Mul(2, 3, evaluate=False)', () => new Mul([R(2), R(3)]), '2*3'],
    ['Limit(x, x, 0)', () => new Limit([x, x, R(0)]), "Limit(x, x, 0, dir='+')"],
    ['ImageSet(Lambda(x, x**2), S.Naturals)', () => new Sets.ImageSet(x, sj.pow(x, 2), Sets.Naturals), 'ImageSet(Lambda(x, x**2), Naturals)'],
    ['ConditionSet(x, x > 0, S.Reals)', () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals), 'ConditionSet(x, x > 0, Reals)'],
    ['Mul(Float(-2.0), 1, evaluate=False)', () => new Mul([new Float(-2), R(1)]), '-2.0*1'],
    ['Mul(-2, Float(1.0), evaluate=False)', () => new Mul([R(-2), new Float(1)]), '-2*1.0'],
    ['Mul(-2, 1, evaluate=False)', () => new Mul([R(-2), R(1)]), '-2*1'],
    ['Mul(1, -2, evaluate=False)', () => new Mul([R(1), R(-2)]), '1*(-2)'],
    ['Mul(Float(2.0), -1, evaluate=False)', () => new Mul([new Float(2), R(-1)]), '2.0*(-1)'],
    ['Mul(Rational(-1, 2), 3, evaluate=False)', () => new Mul([R(-1, 2), R(3)]), '-1/2*3'],
    ['Mul(-1, 1, evaluate=False)', () => new Mul([R(-1), R(1)]), '-1*1'],
    // SymPy Mul(-2, evaluate=False) is -2 itself
    ['Mul(-2, evaluate=False)', () => new Mul([R(-2)]), '-2'],
    ['-oo*x', () => sj.mul(S.NegativeInfinity, x), '-oo*x'],
    ['-oo*x/y', () => sj.mul(S.NegativeInfinity, x, sj.pow(y, -1)), '-oo*x/y'],
    ['x - oo*y', () => sj.add(x, sj.mul(S.NegativeInfinity, y)), 'x - oo*y'],
    ['Pow(-oo*x, 2, evaluate=False)', () => new Pow(sj.mul(S.NegativeInfinity, x), R(2)), '(-oo*x)**2'],
    ['And(x < y, z)', () => sj.And(sj.Lt(x, y), z), 'z & (x < y)'],
    ['Or(Eq(x, y), z)', () => sj.Or(sj.Eq(x, y), z), 'z | Eq(x, y)'],
    ['Pow(Float(-1.5), x, evaluate=False)', () => new Pow(new Float(-1.5), x), '(-1.5)**x'],
  ];
  for (const [label, build, want] of cases) it(label, () => expect(str(build())).toBe(want));

  it('an expression class the printer does not know prints as its key', () => {
    // an Expr subclass outside the library's node classes
    class MyExpr extends sj.Expr {
      readonly kind = 'Extension' as const;
      readonly args: readonly sj.Expr[] = [];
      protected computeKey(): string {
        return 'MyExpr()';
      }
    }
    expect(str(new MyExpr())).toBe('MyExpr()');
  });
});

describe('latex of negative infinity terms', () => {
  it('x - oo', () => expect(latex(sj.add(x, S.NegativeInfinity))).toBe('x - \\infty'));
  it('Add(x, -oo, evaluate=False)', () => expect(latex(new Add([x, S.NegativeInfinity]))).toBe('x - \\infty'));
  it('Pow(-oo, x, evaluate=False)', () => expect(latex(new Pow(S.NegativeInfinity, x))).toBe('\\left(-\\infty\\right)^{x}'));
  it('-oo*x/y', () => expect(latex(sj.mul(S.NegativeInfinity, x, sj.pow(y, -1)))).toBe('- \\frac{\\infty x}{y}'));
  it('Pow(-oo*x, 2, evaluate=False)', () => expect(latex(new Pow(sj.mul(S.NegativeInfinity, x), R(2)))).toBe('\\left(- \\infty x\\right)^{2}'));
  it('-oo*x + y', () => expect(latex(sj.add(sj.mul(S.NegativeInfinity, x), y))).toBe('- \\infty x + y'));
  it('Mul(-oo, x, evaluate=False)', () => expect(latex(new Mul([S.NegativeInfinity, x]))).toBe('- \\infty x'));
});

describe('sort keys', () => {
  it('sorted([exp(x), x, sin(x), x**2, exp(2), 2**x], key=default_sort_key)', () => {
    const es = [sj.exp(x), x, sj.sin(x), sj.pow(x, 2), sj.exp(2), sj.pow(2, x)];
    expect(es.sort((a, b) => compareKeys(sortKey(a), sortKey(b))).map(str)).toEqual(['2**x', 'x', 'x**2', 'exp(2)', 'exp(x)', 'sin(x)']);
  });
  it('Add(exp(x), x, exp(y)).as_ordered_terms()', () => {
    expect(asOrderedTerms(new Add([sj.exp(x), x, sj.exp(y)])).map(str)).toEqual(['x', 'exp(x)', 'exp(y)']);
  });
  it('(x**2.0 + x**3 + x).as_ordered_terms()', () => {
    expect(asOrderedTerms(sj.add(sj.pow(x, new Float(2)), sj.pow(x, 3), x)).map(str)).toEqual(['x**3', 'x', 'x**2.0']);
  });
  it('(x**(I*y) + x**(2*y) + x**(-y) + x**(y/2)).as_ordered_terms()', () => {
    const e = sj.add(sj.pow(x, sj.mul(S.I, y)), sj.pow(x, sj.mul(2, y)), sj.pow(x, sj.neg(y)), sj.pow(x, sj.mul(R(1, 2), y)));
    expect(asOrderedTerms(e).map(str)).toEqual(['x**(y/2)', 'x**(2*y)', 'x**(I*y)', 'x**(-y)']);
  });
  it('keys of different kinds order by kind', () => {
    // not produced by well-formed expressions; numbers before strings before lists
    expect(compareKeys(1, 'a')).toBeLessThan(0);
    expect(compareKeys('a', [1])).toBeLessThan(0);
    expect(compareKeys([1], 1)).toBeGreaterThan(0);
  });
});

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
