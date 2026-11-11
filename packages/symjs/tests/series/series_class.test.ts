// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it, vi } from 'vitest';
import { SeriesBase, S, Sym, Rational, add, freeSymbols, interval, mul, subs } from '../../src';
import type { Expr, ExprLike, SetExpr } from '../../src';
import { SeriesBase as CalculusSeriesBase } from '../../src/calculus';

/** A concrete series to exercise the base protocol independently of its consumers. */
class Points extends SeriesBase {
  constructor(readonly first: ExprLike = 2, readonly last: ExprLike = 4, readonly count: ExprLike = 3) { super(); }
  override get interval(): SetExpr { return interval(this.first, this.last); }
  override get start(): Expr { return add(this.first); }
  override get stop(): Expr { return add(this.last); }
  override get length(): Expr { return add(this.count); }
  override evalTerm(pt: Expr): Expr { return mul(pt, pt); }
}

describe('SeriesBase', () => {
  it('exports one expression class and requires bounds and a term rule', () => {
    expect(SeriesBase).toBe(CalculusSeriesBase);
    const base = new SeriesBase();
    for (const property of ['interval', 'start', 'stop', 'length'] as const) {
      expect(() => base[property]).toThrow(`SeriesBase.${property}`);
    }
    class NoRule extends SeriesBase {
      override get start(): Expr { return S.Zero; }
      override get stop(): Expr { return S.One; }
    }
    expect(() => new NoRule().term(0)).toThrow('evalTerm must implement');
    expect(base.variables).toEqual([]);
  });

  it('collects symbols structurally and removes bound variables from every argument', () => {
    const x = new Sym('x');
    const y = new Sym('y');
    class Bound extends SeriesBase {
      override get variables(): Sym[] { return [new Sym('x')]; }
    }
    const base = new SeriesBase(x, add(x, y));
    expect([...freeSymbols(base)]).toEqual([x, y]);
    expect([...freeSymbols(new Bound(x, add(x, y)))]).toEqual([y]);
    expect([...freeSymbols(new SeriesBase(base, new Sym('x')))]).toEqual([x, y]);
    expect(subs(base, [[y, 3]]).equals(new SeriesBase(x, add(x, 3)))).toBe(true);
  });

  it('checks inclusive points and caches equivalent inputs independently for each series', () => {
    const series = new Points();
    const evaluator = vi.spyOn(Points.prototype, 'evalTerm');
    expect(String(series.term(2))).toBe('4');
    expect(series.term(2n)).toBe(series.term(Rational.of(2)));
    expect(evaluator).toHaveBeenCalledTimes(1);
    expect(String(new Points().term(2))).toBe('4');
    expect(evaluator).toHaveBeenCalledTimes(2);
    expect(String(series.term(4))).toBe('16');
    expect(String(series.term(Rational.of(5, 2)))).toBe('25/4');
    expect(() => series.term(1)).toThrow('Index 1 out of bounds Interval(2, 4)');
    expect(() => series.term(5)).toThrow('Index 5 out of bounds Interval(2, 4)');
    expect(() => series.term(new Sym('n'))).toThrow('Cannot determine truth value');
    expect(() => new Points(0, new Sym('n')).term(1)).toThrow('Cannot determine truth value');
    evaluator.mockRestore();
  });

  it('indexes from the start and slices without clipping or Python negative-index wrapping', () => {
    const series = new Points();
    expect(String(series.getItem(0))).toBe('4');
    expect(String(series.getItem(2))).toBe('16');
    expect(series.slice().map(String)).toEqual(['4', '9', '16']);
    expect(series.slice(0, 3, 2).map(String)).toEqual(['4', '16']);
    expect(series.slice(2, -1, -1).map(String)).toEqual(['16', '9', '4']);
    expect(series.slice(0, 3, 0).map(String)).toEqual(['4', '9', '16']);
    expect(series.slice(2, 0)).toEqual([]);
    expect(series.slice(0, 2, -1)).toEqual([]);
    for (const i of [-1, 3]) expect(() => series.getItem(i)).toThrow(RangeError);
    expect(() => series.slice(0, 4)).toThrow(RangeError);
    expect(() => series.slice(-1, 1)).toThrow(RangeError);
    for (const i of [0.5, Infinity, NaN, Number.MAX_SAFE_INTEGER + 1]) expect(() => series.getItem(i)).toThrow(TypeError);
    expect(() => series.slice(0.5, 2)).toThrow(TypeError);
    expect(() => series.slice(0, 2.5)).toThrow(TypeError);
    expect(() => series.slice(0, 2, 0.5)).toThrow(TypeError);
    expect(() => new Points(0, 2, Rational.of(3, 2)).slice()).toThrow('finite integer stop');
    expect(() => new Points(0, S.Infinity, S.Infinity).slice()).toThrow('finite integer stop');
  });

  it('iterates finite, empty, infinite and reverse infinite series lazily', () => {
    expect([...new Points()].map(String)).toEqual(['4', '9', '16']);
    expect([...new Points(1, 0, 0)]).toEqual([]);
    const infinite = new Points(2, S.Infinity, S.Infinity);
    const iter = infinite[Symbol.iterator]();
    expect([iter.next().value, iter.next().value, iter.next().value].map(String)).toEqual(['4', '9', '16']);
    const reverse = new Points(S.NegativeInfinity, -2, S.Infinity);
    expect(reverse.slice(0, 3).map(String)).toEqual(['4', '9', '16']);
    expect(String(reverse[Symbol.iterator]().next().value)).toBe('4');
    expect(() => reverse.getItem(-1)).toThrow(RangeError);
    expect(() => new Points(0, 1, new Sym('n'))[Symbol.iterator]().next()).toThrow(TypeError);
  });
});
