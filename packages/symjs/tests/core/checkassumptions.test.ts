// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/checkassumptions.ts. Expected values are SymPy 1.14's assumptions,
// check_assumptions, common_assumptions and failing_assumptions ('unknown' for None).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import type { Expr } from '../../src';

const x = new sj.Sym('x', { positive: true });
const y = new sj.Sym('y');
const z = new sj.Sym('z');
const { add, mul, pow } = sj;
const sorted = (m: Map<string, unknown>): [string, unknown][] => [...m].sort(([a], [b]) => (a < b ? -1 : 1));
const third = (e: Expr): Expr => sj.exp(mul(sj.I, sj.pi, sj.Rational.of(1n, 7n), e));

describe('assumptions', () => {
  it('a sum with one term that is not real (the doctest assumptions(x + I))', () => {
    const want = {
      finite: true, nonnegative: false, extended_nonpositive: false, positive: false, extended_positive: false, extended_real: false, negative: false,
      nonzero: false, extended_nonzero: false, extended_negative: false, noninteger: false, nonpositive: false, zero: false, complex: true, infinite: false,
      irrational: false, integer: false, real: false, prime: false, odd: false, commutative: true, composite: false, extended_nonnegative: false,
      imaginary: false, rational: false, even: false,
    };
    expect(sorted(sj.assumptions(add(x, sj.I)))).toEqual(sorted(new Map(Object.entries(want))));
  });
  it('a sum groups the core hermitian facts of its terms (SymPy Add._eval_is_hermitian)', () => {
    const facts = (e: Expr): unknown[] => { const m = sj.assumptions(e); return [m.get('hermitian'), m.get('antihermitian')]; };
    expect(facts(add(3, sj.I))).toEqual([undefined, undefined]);
    // ask leaves Q.extended_real(oo + I) open; the core group of the terms decides it
    expect(sj.assumptions(add(sj.oo, sj.I)).get('extended_real')).toBe(false);
    expect(facts(add(x, 3))).toEqual([true, undefined]);
    expect(facts(add(new sj.Sym('h', { hermitian: true }), new sj.Sym('n', { hermitian: false })))).toEqual([false, undefined]);
    expect(facts(add(new sj.Sym('a', { antihermitian: true }), mul(2, sj.I)))).toEqual([undefined, true]);
  });
  it('a symbol has the closure of its assumptions', () => {
    expect(sorted(sj.assumptions(y))).toEqual([['commutative', true]]);
    const a = sj.assumptions(x);
    expect([a.get('positive'), a.get('real'), a.get('finite'), a.get('zero'), a.get('integer')]).toEqual([true, true, true, false, undefined]);
    expect(sj.assumptions(new sj.Sym('c', { commutative: false })).get('commutative')).toBe(false);
  });
  it('numbers and polar values', () => {
    const two = sj.assumptions(2);
    expect([two.get('prime'), two.get('even'), two.get('composite'), two.get('rational')]).toEqual([true, true, false, true]);
    expect(sj.assumptions(sj.pi).get('transcendental')).toBe(true);
    expect(sj.assumptions(sj.expPolar(sj.I)).get('polar')).toBe(true);
  });
  it('exp of an imaginary number (SymPy exp._eval_is_extended_real)', () => {
    expect(sj.assumptions(third(sj.S.One)).get('real')).toBe(false);
    // exp(I*pi*x/7) is real only for some positive x
    expect(sj.assumptions(third(x)).get('real')).toBeUndefined();
    // two terms that are not real: the sum may be real
    expect(sj.assumptions(add(mul(2, sj.I), third(sj.S.One))).get('extended_real')).toBeUndefined();
  });
  it('contradicting deciders keep their facts', () => {
    const target = sj.SymFunction('contradiction')(y);
    const both: sj.PredicateHandler = (e) => (e.equals(target) ? true : 'unknown');
    sj.registerHandler('positive', both);
    sj.registerHandler('negative', both);
    try {
      const a = sj.assumptions(target);
      expect([a.get('positive'), a.get('negative')]).toEqual([true, true]);
    } finally {
      sj.removeHandler('positive', both);
      sj.removeHandler('negative', both);
    }
  });
});

describe('checkAssumptions', () => {
  it('the doctests of check_assumptions', () => {
    expect(sj.checkAssumptions(-5, { integer: true })).toBe(true);
    expect(sj.checkAssumptions(sj.pi, { real: true, integer: false })).toBe(true);
    expect(sj.checkAssumptions(sj.pi, { negative: true })).toBe(false);
    expect(sj.checkAssumptions(third(sj.S.One), { real: false })).toBe(true);
    expect(sj.checkAssumptions(add(mul(2, x), 1), { positive: true })).toBe(true);
    expect(sj.checkAssumptions(add(mul(-2, x), -5), { positive: true })).toBe(false);
    expect(sj.checkAssumptions(add(mul(2, x), 1), x)).toBe(true);
    expect(sj.checkAssumptions(x, 3)).toBe('unknown');
    expect(sj.checkAssumptions(3, x)).toBe(true);
    expect(sj.checkAssumptions(add(mul(2, x), -1), x)).toBe('unknown');
    expect(sj.checkAssumptions(z, { real: true })).toBe('unknown');
  });
  it('values that are not known and names that are not facts', () => {
    expect(sj.checkAssumptions(z, { real: null, positive: 'unknown' })).toBe(true);
    expect(sj.checkAssumptions(z, { foo: true })).toBe('unknown');
    expect(sj.checkAssumptions(z)).toBe(true);
  });
});

describe('commonAssumptions and failingAssumptions', () => {
  it('the doctests of common_assumptions', () => {
    const common = sj.commonAssumptions([-4, 0, sj.sqrt(2), 2, sj.pi, sj.oo]);
    expect(sorted(common)).toEqual([['commutative', true], ['composite', false], ['extended_real', true], ['imaginary', false], ['odd', false]]);
    expect(sorted(sj.commonAssumptions([0, 1, 2], ['positive', 'integer']))).toEqual([['integer', true]]);
    expect(sj.commonAssumptions([]).size).toBe(0);
  });
  it('the doctests of failing_assumptions', () => {
    expect(sorted(sj.failingAssumptions(add(mul(6, x), y), { positive: true }))).toEqual([['positive', 'unknown']]);
    expect(sorted(sj.failingAssumptions(add(pow(x, 2), -1), { positive: true }))).toEqual([['positive', 'unknown']]);
    expect(sj.failingAssumptions(pow(x, 2), { positive: true }).size).toBe(0);
    expect(sorted(sj.failingAssumptions(x, { negative: true, real: null, foo: true }))).toEqual([['foo', 'unknown'], ['negative', false], ['real', true]]);
  });
});


it('keeps cancellation of imaginary terms undecided and rejects irrational phases', () => {
  const [a, b] = sj.symbols('a b', { imaginary: true });
  const r = sj.symbol('r', { irrational: true });
  expect(sj.assumptions(sj.add(a, b)).get('real')).toBeUndefined();
  expect(sj.assumptions(sj.exp(sj.mul(sj.I, sj.pi, r))).get('extended_real')).toBe(false);
});
