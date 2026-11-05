// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/concrete.ts.
// The methods of SymPy ExprWithIntLimits on Sum and Product. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Concrete } from '../../src/core/concrete';

const [a, b, c, d, e, f, x, y, z, u, v, n] = sj.symbols('a b c d e f x y z u v n') as sj.Sym[];
const s = (q: sj.Expr): string => sj.str(q);
const sum = (fn: sj.ExprLike, ...l: [sj.Sym, sj.ExprLike, sj.ExprLike][]): Concrete => sj.Sum(fn, ...l) as Concrete;

describe('ExprWithIntLimits methods', () => {
  it('index', () => {
    const q = sum(sj.mul(x!, y!), [x!, a!, b!], [y!, c!, d!]);
    expect(q.index(x!)).toBe(0);
    expect(q.index(y!)).toBe(1);
    expect(() => sum(sj.pow(x!, 2), [x!, a!, b!], [x!, c!, d!]).index(x!)).toThrow('Number of instances of variable not equal to one');
  });
  it('reorder and reorder_limit', () => {
    const q = sum(sj.mul(x!, y!), [x!, a!, b!], [y!, c!, d!]);
    expect(s(q.reorder([x!, y!]))).toBe('Sum(x*y, (y, c, d), (x, a, b))');
    expect(s(q.reorder([y!, 0]))).toBe('Sum(x*y, (y, c, d), (x, a, b))');
    const q3 = sum(sj.mul(x!, y!, z!), [x!, a!, b!], [y!, c!, d!], [z!, e!, f!]);
    expect(s(q3.reorder([x!, y!], [x!, z!], [y!, z!]))).toBe('Sum(x*y*z, (z, e, f), (y, c, d), (x, a, b))');
    expect(s(q3.reorderLimit(0, 2))).toBe('Sum(x*y*z, (z, e, f), (y, c, d), (x, a, b))');
    expect(s(sum(sj.pow(x!, 2), [x!, a!, b!], [x!, c!, d!]).reorder([0, 1]))).toBe('Sum(x**2, (x, c, d), (x, a, b))');
    const p = sj.Product(sj.mul(x!, y!, z!), [x!, a!, b!], [y!, c!, d!], [z!, e!, f!]) as Concrete;
    expect(s(p.reorderLimit(0, 2))).toBe('Product(x*y*z, (z, e, f), (y, c, d), (x, a, b))');
    expect(() => sum(sj.mul(x!, y!), [x!, a!, y!], [y!, c!, d!]).reorderLimit(0, 1)).toThrow(sj.ReorderError);
    expect(() => sum(sj.mul(x!, y!), [x!, a!, y!], [y!, c!, d!]).reorderLimit(0, 1)).toThrow('Sum(x*y, (x, a, y), (y, c, d)) could not be reordered: could not interchange the two limits specified.');
    expect(() => q.reorder([0, 1, 2])).toThrow('Invalid number of arguments');
  });
  it('change_index', () => {
    const q = sum(x!, [x!, a!, b!]);
    expect(s(q.changeIndex(x!, sj.add(x!, 1), y!))).toBe('Sum(y - 1, (y, a + 1, b + 1))');
    expect(s(q.changeIndex(x!, sj.sub(sj.mul(-1, x!), 1)))).toBe('Sum(-x - 1, (x, -b - 1, -a - 1))');
    expect(s(q.changeIndex(x!, sj.mul(-1, x!), y!))).toBe('Sum(-y, (y, -b, -a))');
    expect(s(sum(sj.mul(x!, y!), [x!, a!, b!], [y!, c!, d!]).changeIndex(x!, sj.sub(x!, 1), z!))).toBe('Sum(y*(z + 1), (z, a - 1, b - 1), (y, c, d))');
    expect(s(q.changeIndex(x!, sj.add(sj.mul(u!, x!), v!), y!))).toBe('Sum((-v + y)/u, (y, b*u + v, a*u + v))');
    expect(s((sj.Product(x!, [x!, 1, n!]) as Concrete).changeIndex(x!, sj.add(x!, 2), y!))).toBe('Product(y - 2, (y, 3, n + 2))');
    expect(() => q.changeIndex(x!, sj.pow(x!, 2))).toThrow('Index transformation is not linear');
    expect(() => q.changeIndex(x!, 3)).toThrow('Index transformation is not linear');
    expect(() => q.changeIndex(x!, sj.mul(2, x!))).toThrow('Linear transformation results in non-linear summation stepsize');
  });
  it('has_empty_sequence', () => {
    expect(sum(x!, [x!, 1, 0]).hasEmptySequence).toBe(true);
    expect(sum(x!, [x!, 1, 1]).hasEmptySequence).toBe(false);
    expect(sum(x!, [x!, 1, n!]).hasEmptySequence).toBe('unknown');
    expect(sum(sj.mul(x!, y!), [x!, 1, 1], [y!, 5, 4]).hasEmptySequence).toBe(true);
    expect(sum(sj.mul(x!, y!), [x!, 1, n!], [y!, 2, 1]).hasEmptySequence).toBe(true);
  });
});
