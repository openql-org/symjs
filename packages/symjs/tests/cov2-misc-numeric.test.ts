// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of numeric/nfloat.ts (nsimplify), mpeval.ts and round.ts.
 * Expected values from SymPy 1.14 / mpmath 1.3.
 */

import { describe, expect, it } from 'vitest';
import { I, SymFunction, add, evalf, fn, nsimplify, parse, round, sstr } from '../src';
import { simpleRational } from '../src/numeric/nfloat';
import { Float } from '../src/core/nodes';

const p = (s: string) => parse(s);

describe('nsimplify', () => {
  it('identifies exact numbers', () => {
    const cases: [string, Parameters<typeof nsimplify>[1], string][] = [
      // SymPy: an undefined function has no value, the expression comes back
      ['f(1)', {}, 'f(1)'],
      // log(x) is not linear in the constants
      ['exp(1/3)', { constants: [p('pi')] }, 'exp(1/3)'],
      // 1/2 + 1.1e-7: no quadratic with a nonzero discriminant fits
      ['1/2 + exp(-16)', {}, 'exp(-16) + 1/2'],
      // 1/2 + 1.9e-12 fits (2x - 1)(x + 1) = 0: the rational root
      ['1/2 + exp(-27)', {}, '1/2'],
      ['sqrt(2) + exp(-25)', {}, 'sqrt(2)'],
      ['-5/3 + exp(-26)', {}, '-5/3'],
    ];
    for (const [e, o, want] of cases) expect([e, sstr(nsimplify(p(e), o))]).toEqual([e, want]);
    expect(sstr(nsimplify(SymFunction('f')(1)))).toBe('f(1)');
  });
  it('gives up on a convergent that never meets the tolerance', () => {
    // no convergent of the double is within 1e-30: 40 terms, or a fraction part 0
    expect(simpleRational(Math.sqrt(3) / 8, 1e-30)).toBeUndefined();
    expect(simpleRational(5.610306332244461e-14, 1e-30)).toBeUndefined();
    expect(sstr(simpleRational(0.75, 1e-14) ?? p('0'))).toBe('3/4');
  });
});

describe('evalMp', () => {
  it('evaluates a two-argument log', () => {
    // SymPy: log(8, 3, evaluate=False).evalf(20) = 1.8927892607143723113
    expect(sstr(evalf(fn('log', [8, 3], { evaluate: false }), 20))).toBe('1.8927892607143723113');
    // SymPy: N(log(I, 2 + I, evaluate=False), 20)
    expect(sstr(evalf(fn('log', [I, add(2, I)], { evaluate: false }), 20))).toBe('0.8443602876407569357 + 1.4654938711011811226*I');
  });
});

describe('round', () => {
  it('rounds to the first digit below a negative number', () => {
    // SymPy: Rational(-7, 100).round(1) = Float('-0.09375', precision=3), printed -0.e-1
    const r = round(p('-7/100'), 1);
    expect(r).toBeInstanceOf(Float);
    expect(sstr(r)).toBe('-0.e-1');
    expect(r instanceof Float ? r.prec : 0).toBe(3);
    expect(sstr(round(p('-pi/50'), 1))).toBe('-0.e-1');
  });
});
