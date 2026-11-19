// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/concrete.ts.
// The methods of SymPy ExprWithIntLimits on Sum and Product. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Concrete, concreteHooks } from '../../src/core/concrete';

const [a, b, c, d, e, f, x, y, z, u, v, n] = sj.symbols('a b c d e f x y z u v n') as sj.Sym[];
const s = (q: sj.Expr): string => sj.str(q);
const sum = (fn: sj.ExprLike, ...l: [sj.Sym, sj.ExprLike, sj.ExprLike][]): Concrete => sj.Sum(fn, ...l) as Concrete;

it('validates definite limits and accepts differentiable bound expressions', () => {
  const k = sj.symbol('k');
  expect(() => sj.Sum(1)).toThrow(RangeError);
  expect(() => sj.Product(1)).toThrow(RangeError);
  expect(() => sj.Sum(1, [sj.S.One, 0, 3])).toThrow('Invalid limit variable');
  const f = sj.SymFunction('f')(k);
  const derivative = new sj.Derivative([f, k, sj.S.One]);
  const indexed = new sj.IndexedBase('A').at(k);
  for (const variable of [f, derivative, indexed]) {
    expect(sj.Sum(variable, [variable, 1, 2])).toBeInstanceOf(Concrete);
  }
  const process = concreteHooks.processLimit;
  delete concreteHooks.processLimit;
  try {
    expect(() => sj.Sum(k, [k, k])).toThrow('Set limits require the calculus module');
  } finally {
    concreteHooks.processLimit = process;
  }
});

it('removes each bound variable from inner limits and preserves independent factors', () => {
  const [x, y, z] = sj.symbols('x y z');
  for (const ctor of [sj.Sum, sj.Product]) {
    expect([...sj.freeSymbols(ctor(x.mul(y), [x, 1, 2]))]).toEqual([y]);
    expect([...ctor(x, [x, 1, y], [y, 1, 2]).freeSymbols()]).toEqual([]);
    expect([...ctor(x, [x, 1, y], [y, 1, y]).freeSymbols()]).toEqual([y]);
    const f = sj.SymFunction('f')(x);
    expect([...ctor(f.mul(z), [f, 1, y]).freeSymbols()].map(String).sort()).toEqual(['y', 'z']);
  }
  expect(sum(x, [x, sj.oo, sj.oo]).hasEmptySequence).toBe(false);
});

it('recognizes numerical sums and products by their free symbols', () => {
  const k = sj.symbol('k'), n = sj.symbol('n');
  expect(sj.Sum(k, [k, 1, 3]).isNumber).toBe(true);
  expect(sj.Product(k, [k, 1, 3]).isNumber).toBe(true);
  expect(sj.Sum(k, [k, 1, n]).isNumber).toBe(false);
});

it('decides empty sequences using assumptions on both bounds', () => {
  const m = sj.symbol('m');
  const positive = sj.symbol('M', { positive: true, integer: true });
  const negative = sj.symbol('N', { negative: true, integer: true });
  expect(sum(m, [m, 1, positive]).hasEmptySequence).toBe(false);
  expect(sum(m, [m, negative, positive]).hasEmptySequence).toBe(false);
  expect(sum(m, [m, sj.symbol('N', { positive: true, integer: true }), positive]).hasEmptySequence).toBe('unknown');
  expect(sum(m, [m, positive.add(1), positive]).hasEmptySequence).toBe(true);
});

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

describe('Sum and Product heads', () => {
  const [k, n] = sj.symbols('k n');
  it('are Sum and Product; rebuild rebuilds the node from its flat arguments', () => {
    const p = sj.Product(k, [k, 1, n]);
    expect(sj.func(p)).toBe(sj.Product);
    expect(sj.func(sj.Sum(k, [k, 1, n]))).toBe(sj.Sum);
    expect(sj.str(sj.rebuild(p, [...p.args]))).toBe(sj.str(p));
  });
});

it('checks only decidable bounds on a ranged index', () => {
  const j = sj.Idx('j', [1, 3]), n = sj.symbol('n');
  for (const make of [sj.Sum, sj.Product]) {
    expect(() => make(j, [j, 0, 3])).toThrow(RangeError);
    expect(() => make(j, [j, 1, sj.oo])).toThrow(RangeError);
    expect(make(j, [j, 2, n])).toBeInstanceOf(Concrete);
    const unbounded = sj.Idx('j');
    expect(make(unbounded, [unbounded, -1, 3])).toBeInstanceOf(Concrete);
  }
});

it('factors nested sums in limit order and keeps additive summands together', () => {
  const [x, y, n] = sj.symbols('x y n');
  const sum = (f: sj.Expr) => sj.Sum(f, [x, 1, n]);
  expect(sj.factor(sum(x.add(1))).equals(sum(x.add(1)))).toBe(true);
  expect(sj.factor(sum(x.pow(2).add(x))).equals(sum(x.mul(x.add(1))))).toBe(true);
  expect(sj.factor(sj.log(sum(x.mul(2)))).equals(sj.log(sum(x.mul(2))))).toBe(true);
  expect(sj.factor(sj.Sum(x, [x, 1, n], [y, 1, n])).equals(n.mul(sum(x)))).toBe(true);
  expect(sj.factor(sj.Sum(x.mul(y), [x, 1, n], [y, 1, n])).equals(sum(x).mul(sj.Sum(y, [y, 1, n])))).toBe(true);
});
