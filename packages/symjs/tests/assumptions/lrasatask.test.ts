// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/lrasatask.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { UnhandledInput, extractPredFromOldAssum } from '../../src/logic';

describe('extract_pred_from_old_assum', () => {
  it('doctest', () => {
    const [x, y] = sj.symbols('x y', { positive: true });
    expect(extractPredFromOldAssum([x!, y!, 2]).map(String)).toEqual(['Q.positive(x)', 'Q.positive(y)']);
  });
  it('each predicate and the unhandled input', () => {
    const s = (name: string, a: sj.Assumptions) => sj.symbol(name, a);
    expect(extractPredFromOldAssum([s('n', { negative: true }), s('a', { real: true, zero: false }), s('b', { nonpositive: true }), s('c', { nonnegative: true }), s('r', { real: true })]).map(String)).toEqual([
      'Q.negative(n)',
      'Q.nonzero(a)',
      'Q.nonpositive(b)',
      'Q.nonnegative(c)',
    ]);
    expect(extractPredFromOldAssum([s('z', { zero: true })]).map(String)).toEqual(['Q.zero(z)']);
    expect(() => extractPredFromOldAssum([sj.symbol('w')])).toThrow(UnhandledInput);
    expect(() => extractPredFromOldAssum([s('k', { integer: true })])).toThrow('is an integer');
    expect(() => extractPredFromOldAssum([sj.add(s('n', { integer: true }), sj.Rational.of(1n, 2n))])).toThrow("can't be an integer");
  });
});

const x = sj.symbol('x', { real: true }), y = sj.symbol('y', { real: true }), z = sj.symbol('z', { real: true });
const { Q, lraSatask, ask } = sj;
it('decides strict and weak rational bounds, equality and Boolean branches', () => {
  expect(lraSatask(Q.gt(x, 0), Q.gt(x, 1))).toBe(true);
  expect(lraSatask(Q.eq(x, 1), sj.Not(Q.ne(x, 0)))).toBe(false);
  expect(lraSatask(Q.eq(x, x))).toBe(true);
  expect(lraSatask(Q.ne(x, x))).toBe(false);
  expect(lraSatask(Q.gt(x, 0))).toBe('unknown');
  expect(lraSatask(Q.eq(x, y), sj.Or(Q.lt(x, y), Q.gt(x, y)))).toBe(false);
  expect(lraSatask(sj.Or(Q.lt(x, 0), Q.ge(x, 0)))).toBe(true);
  expect(lraSatask(sj.And(Q.lt(x, 2), Q.gt(x, 3)))).toBe(false);
  expect(lraSatask(Q.lt(x, sj.Rational.of(1, 3)), Q.le(x, sj.Rational.of(1, 4)))).toBe(true);
  expect(lraSatask(true, [Q.gt(x, 0)])).toBe(true);
  expect(lraSatask(false)).toBe(false);
  expect(() => lraSatask(true, false)).toThrow('inconsistent assumptions');
  expect(() => lraSatask(true, sj.And(Q.lt(x, y), Q.le(y, x)))).toThrow('inconsistent assumptions');
  expect(ask(sj.Lt(x, z), sj.And(sj.Le(x, y), sj.Lt(y, z)))).toBe(true);
  expect(ask(Q.eq(z, x), sj.And(Q.eq(x, y), Q.eq(y, z)))).toBe(true);
});
it('uses old sign facts and rejects input outside real linear arithmetic', () => {
  for (const [assumptions, pred, expected] of [
    [{ positive: true }, 'positive', true], [{ negative: true }, 'positive', false],
    [{ zero: true }, 'zero', true], [{ real: true, zero: false }, 'zero', false],
    [{ nonpositive: true }, 'nonpositive', true], [{ nonnegative: true }, 'negative', false],
  ] as const) expect(lraSatask(sj.Predicate(pred)(sj.symbol('w', assumptions)))).toBe(expected);
  for (const predicate of [Q.prime, Q.composite, Q.odd, Q.even, Q.integer]) {
    expect(() => lraSatask(Q.gt(x, 0), sj.And(Q.gt(x, 2), predicate(x)))).toThrow(UnhandledInput);
  }
  expect(() => lraSatask(Q.lt(sj.mul(x, y), 2))).toThrow(UnhandledInput);
  expect(() => lraSatask(Q.gt(sj.symbol('u'), 0))).toThrow(UnhandledInput);
  expect(lraSatask(Q.extended_positive(x), sj.Gt(x, 2))).toBe(true);
  expect(lraSatask(Q.positive_infinite(x))).toBe(false);
  expect(lraSatask(Q.negative_infinite(x))).toBe(false);
  expect(lraSatask(Q.real(x))).toBe(true);
  expect(lraSatask(sj.Not(Q.finite(x)))).toBe(false);
  expect(() => lraSatask(sj.Xor(Q.lt(x, 0), Q.gt(x, 0)))).toThrow(UnhandledInput);
});
it('reports malformed or inconsistent theories and keeps unsupported ask queries undecided', () => {
  expect(() => lraSatask(x)).toThrow(UnhandledInput);
  expect(() => lraSatask(sj.Not(Q.prime(x)))).toThrow(UnhandledInput);
  expect(() => ask(Q.gt(x, 0), sj.And(Q.gt(x, 1), Q.lt(x, 0)))).toThrow(RangeError);
});
