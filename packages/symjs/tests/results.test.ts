// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Result types of the public API (docs/api-policy.md): Truth, NoMatch, Unsolved, EmptySet, errors. */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];
const [p] = sj.symbols('p', { positive: true }) as [sj.Sym];
const n = new sj.Sym('n', { integer: true });

describe('Truth', () => {
  it('three-valued predicates', () => {
    expect(sj.isPositive(p)).toBe(true);
    expect(sj.isPositive(x)).toBe('unknown');
    expect(sj.isNegative(p)).toBe(false);
    expect(sj.isReal(p)).toBe(true);
    expect(sj.isZero(0)).toBe(true);
    expect(sj.isNonZero(p)).toBe(true);
    expect(sj.isNonNegative(p)).toBe(true);
    expect(sj.isIntegerValued(n)).toBe(true);
    expect(sj.isIntegerQ(x)).toBe('unknown');
    expect(sj.isMeromorphic(sj.pow(x, -1), x, 0)).toBe(true);
    expect(sj.isSubset(sj.interval(0, 1), sj.interval(0, 2))).toBe(true);
    expect(sj.containsQ(sj.interval(0, 1), x)).toBe('unknown');
    expect(sj.isIncreasing(sj.exp(x))).toBe(true);
    expect(sj.isMonotonic(sj.exp(x))).toBe(true);
  });
  it('helpers and three-valued logic', () => {
    expect([sj.isTrue(true), sj.isFalse(false), sj.isUnknown('unknown'), sj.isTrue('unknown')]).toEqual([true, true, true, false]);
    expect([sj.truthNot(true), sj.truthNot('unknown')]).toEqual([false, 'unknown']);
    expect([sj.truthAnd(true, 'unknown'), sj.truthAnd('unknown', false), sj.truthAnd(true, true)]).toEqual(['unknown', false, true]);
    expect([sj.truthOr(false, 'unknown'), sj.truthOr('unknown', true), sj.truthOr(false, false)]).toEqual(['unknown', true, false]);
  });
});

describe('NoMatch, Unsolved, EmptySet and errors', () => {
  it('a missing form is NoMatch', () => {
    const a = new sj.Wild('a', { exclude: [x] });
    expect(sj.match(sj.mul(2, x), sj.mul(a, y))).toBe(sj.NoMatch);
    expect(sj.match(sj.mul(2, x), sj.mul(a, x))).toBeInstanceOf(Map);
    expect(sj.extractAdditively(x, 2)).toBe(sj.NoMatch);
    expect(sj.str(sj.extractMultiplicatively(sj.mul(2, x), 2) as sj.Expr)).toBe('x');
    expect(sj.asCoefficient(sj.add(x, 1), x)).toBe(sj.NoMatch);
    expect(sj.periodicity(sj.exp(x), x)).toBe(sj.NoMatch);
    expect(sj.homogeneousOrder(sj.add(x, 1), x)).toBe(sj.NoMatch);
    expect(sj.Poly.from(sj.add(sj.pow(x, 2), x)).homogeneousOrder()).toBe(sj.NoMatch);
    expect(sj.isNoMatch(sj.getn(x))).toBe(true);
    expect(sj.polyCoefficients(sj.sin(x), x)).toBe(sj.NoMatch);
    expect(sj.separatevars(sj.add(x, y), { dict: true })).toBe(sj.NoMatch);
    expect(String(sj.NoMatch)).toBe('NoMatch');
  });
  it('no closed form is Unsolved; no solution is EmptySet', () => {
    const k = new sj.Sym('k', { integer: true });
    expect(sj.rsolvePoly([-1, 1], sj.pow(2, k), k)).toBe(sj.Unsolved);
    expect(sj.isUnsolved(sj.rsolveRatio([-1, 1], sj.pow(2, k), k))).toBe(true);
    expect(sj.rsolveHyper([-1, 1], sj.gamma(sj.pow(k, 2)), k)).toBe(sj.Unsolved);
    expect(String(sj.Unsolved)).toBe('Unsolved');
    expect(sj.linsolve([sj.add(x, y), sj.add(x, y, 1)], [x, y])).toBe(sj.EmptySet);
    expect(() => sj.linsolve([sj.mul(x, y)], [x, y])).toThrow(sj.NonlinearError);
    expect(() => sj.linearEqToMatrix([sj.pow(x, 2)], [x])).toThrow(sj.NonlinearError);
  });
  it('ask returns Truth', () => {
    expect(sj.ask(sj.Q.positive(x))).toBe('unknown');
    expect(sj.isConvergent(sj.Sum(sj.pow(n, -2), [n, 1, sj.oo]) as never)).toBe(true);
  });
});
