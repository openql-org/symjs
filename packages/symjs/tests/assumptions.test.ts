// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const { Q, ask, refine } = sj;
const x = sj.symbol('x');
const y = sj.symbol('y');
const s = (e: unknown): string => String(e);

describe('assumptions (SymPy sympy.assumptions)', () => {
  it('asks the number-theoretic and algebraic predicates', () => {
    expect(ask(Q.rational(sj.pi))).toBe(false);
    expect(ask(Q.even(sj.mul(x, y)), Q.even(x).and(Q.integer(y)))).toBe(true);
    expect(ask(Q.prime(sj.mul(4, x)), Q.integer(x))).toBe(false);
    expect(ask(Q.prime(7))).toBe(true);
    expect(ask(Q.composite(9))).toBe(true);
    expect(ask(Q.irrational(sj.sqrt(2)))).toBe(true);
    expect(ask(Q.odd(sj.add(x, 1)), Q.even(x))).toBe(true);
    expect(ask(Q.algebraic(sj.add(sj.sqrt(2), 1)))).toBe(true);
    expect(ask(Q.transcendental(sj.mul(2, sj.pi)))).toBe(true);
    expect(ask(Q.imaginary(sj.mul(2, sj.I)))).toBe(true);
  });

  it('combines assumptions with And, Or and Not', () => {
    expect(ask(Q.positive(sj.add(x, y)), sj.and(Q.positive(x), Q.positive(y)))).toBe(true);
    expect(ask(Q.real(x), sj.or(Q.positive(x), Q.negative(x)))).toBe(true);
    expect(ask(Q.positive(x), sj.or(Q.positive(x), Q.negative(x)))).toBe('unknown');
    expect(ask(Q.negative(x), sj.and(sj.not(Q.positive(x)), Q.nonzero(x)))).toBe(true);
    expect(ask(Q.gt(x, 0), Q.positive(x))).toBe(true);
    expect(ask(sj.Gt(x, y), Q.gt(x, y))).toBe(true);
    expect(ask(Q.positive(x), sj.Gt(x, 0))).toBe('unknown');
    expect(() => ask(Q.positive(x), sj.and(Q.positive(x), Q.negative(x)))).toThrow(RangeError);
    expect(s(sj.not(Q.positive(x)))).toBe('~Q.positive(x)');
  });

  it('refines expressions and predicates', () => {
    expect(s(refine(sj.sqrt(sj.pow(x, 2)), Q.real(x)))).toBe('Abs(x)');
    expect(s(refine(sj.sqrt(sj.pow(x, 2)), Q.positive(x)))).toBe('x');
    expect(s(refine(Q.real(x), Q.positive(x)))).toBe('True');
    expect(s(refine(Q.positive(x), Q.real(x)))).toBe('Q.positive(x)');
    expect(s(refine(sj.pow(-1, sj.add(x, y)), Q.even(x)))).toBe('(-1)**y');
    expect(s(refine(sj.pow(-1, sj.add(x, y, 2)), Q.odd(x)))).toBe('(-1)**(y + 1)');
  });

  it('keeps global assumptions and user predicates', () => {
    expect(sj.assuming([Q.integer(x)], () => ask(Q.integer(sj.mul(2, x))))).toBe(true);
    expect(ask(Q.integer(sj.mul(2, x)))).toBe('unknown');
    sj.globalAssumptions.add(Q.real(x));
    expect(ask(Q.real(x))).toBe(true);
    sj.globalAssumptions.clear();
    expect(ask(Q.real(x))).toBe('unknown');
    const handler: sj.PredicateHandler = (e) => (e instanceof sj.Rational ? e.p % 3n === 0n : 'unknown');
    const div3 = sj.Predicate('div3', handler);
    expect(ask(div3(9))).toBe(true);
    expect(s(div3(x))).toBe('Q.div3(x)');
    sj.removeHandler('div3', handler);
    expect(ask(div3(9))).toBe('unknown');
  });
});
