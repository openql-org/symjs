// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpeval.ts.

import { afterAll, beforeAll, describe, expect, it } from 'vitest';
import { add, evalf, fn, I, Mul, mul, parse, pow, Rational, sstr } from '../../src';
import type { Expr } from '../../src';
import { at } from '../../src/core/guard';
import * as F from '../../src/numeric/mpf';
import { MpSpecialValue, evalMp, mpFns, mpSpecialFns, type MpPart } from '../../src/numeric/mpeval';
import { S } from '../../src/core/nodes';

/**
 * Coverage of numeric/nfloat.ts (nsimplify), mpeval.ts and round.ts.
 * Expected values from SymPy 1.14 / mpmath 1.3.
 */

describe('evalMp', () => {
  it('evaluates a two-argument log', () => {
    // SymPy: log(8, 3, evaluate=False).evalf(20) = 1.8927892607143723113
    expect(sstr(evalf(fn('log', [8, 3], { evaluate: false }), 20))).toBe('1.8927892607143723113');
    // SymPy: N(log(I, 2 + I, evaluate=False), 20)
    expect(sstr(evalf(fn('log', [I, add(2, I)], { evaluate: false }), 20))).toBe('0.8443602876407569357 + 1.4654938711011811226*I');
  });
});

describe('evalAdaptive: parts far below the other part', () => {
  // SymPy 1.14 N(...); SymPy tracks the accuracy of the real and imaginary parts separately
  const n = (s: string) => sstr(evalf(parse(s)));
  it('keeps a stable tiny part', () => {
    expect(n('1 + I*exp(-1000)')).toBe('5.07595889754946e-435*I + 1.0');
    expect(n('exp(-1000)')).toBe('5.07595889754946e-435');
    expect(n('1 + exp(-1000)')).toBe('1.00000000000000');
    expect(n('exp(-1000)*I + exp(-2000)')).toBe('2.57653587296115e-869 + 5.07595889754946e-435*I');
    expect(n('1 - exp(-1000)*I + exp(-2000)')).toBe('1.0 - 5.07595889754946e-435*I');
    expect(n('exp(-1000)*(1 + I)')).toBe('5.07595889754946e-435 + 5.07595889754946e-435*I');
    // negligible at the first working precision only
    expect(n('1 + I*exp(-70)')).toBe('1.0 + 3.97544973590865e-31*I');
  });
  it('keeps a tiny part that needs more working precision', () => {
    // zero at the first working precision
    expect(n('1 + I*(exp(-1000) - exp(-1000)*(1 + exp(-100)))')).toBe('1.0 - 1.88829527500429e-478*I');
    // inaccurate at the first working precision
    expect(n('1 + I*(exp(-1000)*(1 + exp(-40)) - exp(-1000))')).toBe('2.15644715820894e-452*I + 1.0');
  });
  it('is more accurate than SymPy where SymPy loses the tiny part', () => {
    // SymPy: 0.e-434*I + 1.0; the imaginary part is 2*exp(-1000)
    expect(n('(1 + exp(-1000)*I)**2')).toBe('1.01519177950989e-434*I + 1.0');
    // SymPy: 0.e-435 + 1.0*I; the real part is exp(-1000)/2
    expect(n('sqrt(-1 + exp(-1000)*I)')).toBe('2.53797944877473e-435 + 1.0*I');
  });
  it('drops the rounding noise of a cancellation', () => {
    // SymPy: -0.e-124, 1.0 - 0.e-71*I, -0.e-22 + 8.0*I, -0.e-127 - 0.e-127*I
    expect(n('sin(1)**2 + cos(1)**2 - 1')).toBe('0');
    expect(n('1 + I*(sin(1)**2 + cos(1)**2 - 1)')).toBe('1.00000000000000');
    expect(n('(sqrt(3) + I)**3')).toBe('8.0*I');
    expect(n('cos(pi/7) + I*sin(pi/7) - exp(I*pi/7)')).toBe('0');
  });
  it('keeps a tiny part next to floor, which is evaluated at the working precision', () => {
    // SymPy (floor(x) + I*exp(-1000)).evalf(subs={x: 5/2}) = 5.07595889754946e-435*I + 2.0
    expect(sstr(evalf(parse('floor(x) + I*exp(-1000)'), 15, { subs: { x: parse('5/2') } }))).toBe('5.07595889754946e-435*I + 2.0');
  });
});

describe("mpmath's inf and nan (MpSpecialValue)", () => {
  // A stand-in kernel: f(k) = mathieuc(k, 1, 1) is given the values of a SymPy function whose
  // _eval_evalf returns {1: -oo - oo*I, 2: oo + oo*I, 3: nan, 4: oo, 5: 1 + oo*I, 6: -oo}[k]; the
  // expected strings are SymPy 1.14's evalf of the same expressions.
  const parts: Record<number, [MpPart, MpPart]> = { 1: ['-inf', '-inf'], 2: ['inf', 'inf'], 3: ['-inf', 'nan'], 4: ['inf', F.ZERO], 5: [F.ONE, 'inf'], 6: ['-inf', F.ZERO] };
  const f = (k: number) => fn('mathieuc', [k, 1, 1]);
  const E = (e: Expr) => sstr(evalf(e));
  beforeAll(() => {
    mpFns['mathieuc'] = (args) => {
      const k = Number(F.toRational(at(args, 0)[0])[0]);
      if (k === 7) throw new TypeError('not evaluable');
      const [re, im] = parts[k] ?? ['nan', 'nan'];
      throw new MpSpecialValue(re, im);
    };
  });
  afterAll(() => {
    delete mpFns['mathieuc'];
  });
  it('values of the kernel (SymPy _from_mpmath)', () => {
    expect(E(f(1))).toBe('-oo - oo*I');
    expect(E(f(3))).toBe('nan');
    expect(E(f(4))).toBe('oo');
    expect(E(f(5))).toBe('1.0 + oo*I');
    expect(E(f(7))).toBe('mathieuc(7, 1, 1)');
  });
  it('sums (SymPy evalf_add, add_terms)', () => {
    expect(E(add(f(1), f(2)))).toBe('nan');
    expect(E(add(f(1), 1))).toBe('-oo - oo*I');
    expect(E(add(f(1), mul(2, I)))).toBe('-oo - oo*I');
    expect(E(add(f(3), 1))).toBe('nan');
    expect(E(add(f(5), 1))).toBe('2.0 + oo*I');
    expect(E(add(f(4), f(6)))).toBe('nan');
    expect(E(add(f(6), f(1)))).toBe('-oo - oo*I');
    expect(E(add(f(4), f(2)))).toBe('oo + oo*I');
    expect(E(add(f(5), f(4)))).toBe('oo + oo*I');
  });
  it('products (SymPy evalf_mul: only the infinite real parts count)', () => {
    expect(E(mul(2, f(1)))).toBe('-oo');
    expect(E(mul(-3, f(2)))).toBe('oo');
    expect(E(mul(f(1), f(2)))).toBe('-oo');
    expect(E(mul(2, f(3)))).toBe('nan');
    expect(E(mul(I, f(2)))).toBe('oo');
    expect(E(mul(add(2, I), f(2)))).toBe('oo');
    expect(E(mul(f(6), f(6)))).toBe('oo');
    expect(E(mul(f(5), f(6)))).toBe('-oo');
    expect(E(mul(f(5), 2))).toBe('nan');
    expect(E(new Mul([Rational.of(0), f(2)]))).toBe('nan');
  });
  it('powers and functions of a special value', () => {
    // a power is rebuilt from its evaluated parts (SymPy: (f(4)**2).evalf() = oo, sqrt(f(4)).evalf() = oo)
    expect(E(pow(f(4), 2))).toBe('oo');
    expect(E(pow(f(4), Rational.of(1, 2)))).toBe('oo');
    // a function of a special value is evaluated with mpmath's inf (SymPy: sin(f(2)).evalf() = nan)
    expect(E(fn('sin', [f(2)]))).toBe('nan');
  });
});

describe('functions of arguments with an infinite or undefined part (mpmath inf/nan arithmetic)', () => {
  const n = (x: string) => sstr(evalf(parse(x)));
  it('evaluates like SymPy evalf (mpmath sin, cos, sinh, cosh, exp of mpc with inf)', () => {
    // SymPy 1.14: sin(oo + oo*I).evalf() = nan, sin(1 + oo*I).evalf() = oo + oo*I, ...
    const cases: [string, string][] = [
      ['sin(oo+oo*I)', 'nan'],
      ['sin(oo+I)', 'nan'],
      ['sin(1+oo*I)', 'oo + oo*I'],
      ['sin(1-oo*I)', 'oo - oo*I'],
      ['sin(2+3*oo*I)', 'oo - oo*I'],
      ['cos(2+3*oo*I)', '-oo - oo*I'],
      ['cos(1-oo*I)', 'oo + oo*I'],
      ['cos(oo+2*I)', 'nan'],
      ['sinh(oo+I)', 'oo + oo*I'],
      ['sinh(oo+2*I)', '-oo + oo*I'],
      ['cosh(oo+I)', 'oo + oo*I'],
      ['cosh(-oo+I)', 'oo - oo*I'],
      ['sinh(1+oo*I)', 'nan'],
      ['exp(1+oo*I)', 'nan'],
      ['exp(2+3*oo*I)', 'nan'],
      ['tan(oo+I)', 'nan'],
      ['tanh(1+oo*I)', 'nan'],
      ['csc(oo+I)', 'nan'],
      ['log(oo+oo*I)', 'nan'],
      ['sin(nan+I)', 'nan'],
      ['2+oo*I', '2.0 + oo*I'],
      ['-oo*I', '-oo*I'],
      ['atan(oo*I + nan)', 'nan'],
    ];
    for (const [x, want] of cases) expect([x, n(x)]).toEqual([x, want]);
    // mpmath sinh(-inf + 1j) = (-inf + inf j); SymPy rewrites it as -sinh(oo - I) and its evalf_mul
    // keeps only the infinite real part (oo)
    expect(n('sinh(-oo+I)')).toBe('-oo + oo*I');
  });
  it('gives the limit where mpmath produces nan although the limit exists', () => {
    // SymPy prints nan for all of these (mpmath mpc_tan(1, inf) = 0 + nan j, atan(inf + inf j) =
    // nan, sign(inf + 1j) = nan + 0j, sec(1 + inf j) = nan); the limits are I, pi/2, 1 and 0:
    // tan(x + I*y) -> I and sec(x + I*y) -> 0 as y -> oo, atan(z) -> pi/2 as z -> oo with re z > 0
    const cases: [string, string][] = [
      ['tan(1+oo*I)', '1.0*I'],
      ['tan(1-oo*I)', '-1.0*I'],
      ['cot(1+oo*I)', '-1.0*I'],
      ['tanh(oo+I)', '1.00000000000000'],
      ['tanh(-oo+I)', '-1.00000000000000'],
      ['coth(oo+I)', '1.00000000000000'],
      ['sec(1+oo*I)', '0'],
      ['atan(oo+oo*I)', '1.57079632679490'],
      ['atan(-oo+I)', '-1.57079632679490'],
      ['atan(1-oo*I)', '1.57079632679490'],
      ['sign(oo+I)', '1.00000000000000'],
      ['sign(1-oo*I)', '-1.0*I'],
      ['sign(oo+oo*I)', 'nan'],
    ];
    for (const [x, want] of cases) expect([x, n(x)]).toEqual([x, want]);
  });
  it('keeps a function without a rule for special values', () => {
    // SymPy gamma(1 + oo*I).evalf() = nan (mpmath gamma(1 + inf j) = nan; the limit is 0)
    expect(n('gamma(1+oo*I)')).toBe('gamma(1 + oo*I)');
  });
  it('evaluates the kernels at mpmath special parts', () => {
    const one = F.ONE;
    const two = F.fromInt(2n);
    const p = 53;
    const show = (v: readonly [MpPart, MpPart]): string[] => v.map((x) => (typeof x === 'string' ? x : F.toStr(x, 15)));
    const k = (name: string, ...args: [MpPart, MpPart][]) => {
      const f = mpSpecialFns[name];
      if (!f) throw new TypeError(name);
      return show(f(args, p));
    };
    // mpmath exp(mpc(inf, 0)), exp(mpc(-inf, 1)), exp(nan + 1j)
    expect(k('exp', ['inf', F.ZERO])).toEqual(['inf', '0.0']);
    expect(k('exp', ['-inf', one])).toEqual(['0.0', '0.0']);
    expect(k('exp', ['nan', one])).toEqual(['nan', 'nan']);
    // mpmath sin(mpc(0, inf)) = (0 + inf j), cos(mpc(0, -inf)) = (inf + 0j), sin(mpc(inf, 0)) = nan
    expect(k('sin', [F.ZERO, 'inf'])).toEqual(['0.0', 'inf']);
    expect(k('cos', [F.ZERO, '-inf'])).toEqual(['inf', '0.0']);
    expect(k('cos', ['inf', F.ZERO])).toEqual(['nan', '0.0']);
    expect(k('sin', ['-inf', F.ZERO])).toEqual(['nan', '0.0']);
    expect(k('sin', [one, 'nan'])).toEqual(['nan', 'nan']);
    // 0 * inf = nan: sin(pi-ish 0 + i inf) along the axis is exact, cosh(nan) = nan
    expect(k('cosh', ['nan', one])).toEqual(['nan', 'nan']);
    // tan, cot on the real axis and with a nan part
    expect(k('tan', ['inf', F.ZERO])).toEqual(['nan', '0.0']);
    expect(k('cot', [one, 'nan'])).toEqual(['nan', 'nan']);
    expect(k('csc', [one, '-inf'])).toEqual(['0.0', '0.0']);
    // log = (log|z|, arg z) with mpmath atan2 at inf: atan2(1, inf) = 0, atan2(-1, -inf) = -pi,
    // atan2(inf, -1) = pi/2, atan2(-inf, 1) = -pi/2, atan2(1, -inf) = pi, atan2(inf, inf) = nan
    expect(k('log', ['inf', one])).toEqual(['inf', '0.0']);
    expect(k('log', ['-inf', F.neg(one)])).toEqual(['inf', '-3.14159265358979']);
    expect(k('log', [F.neg(one), 'inf'])).toEqual(['inf', '1.5707963267949']);
    expect(k('log', [one, '-inf'])).toEqual(['inf', '-1.5707963267949']);
    expect(k('log', ['-inf', one])).toEqual(['inf', '3.14159265358979']);
    expect(k('log', ['nan', one])).toEqual(['nan', 'nan']);
    expect(k('atan2', ['inf', F.ZERO], [one, F.ZERO])).toEqual(['1.5707963267949', '0.0']);
    expect(k('atan2', [one, F.ZERO], [two, F.ZERO])).toEqual(['0.463647609000806', '0.0']);
    expect(k('arg', ['inf', 'inf'])).toEqual(['nan', '0.0']);
    // atan on the imaginary axis takes the sign of the imaginary part (mpmath atan(-inf j) = -pi/2)
    expect(k('atan', [F.ZERO, '-inf'])).toEqual(['-1.5707963267949', '0.0']);
    expect(k('abs', ['-inf', one])).toEqual(['inf', '0.0']);
    expect(k('abs', ['nan', one])).toEqual(['nan', '0.0']);
    expect(k('re', ['-inf', one])).toEqual(['-inf', '0.0']);
    expect(k('im', [one, '-inf'])).toEqual(['-inf', '0.0']);
    expect(k('conjugate', [one, 'inf'])).toEqual(['1.0', '-inf']);
    expect(k('conjugate', [one, 'nan'])).toEqual(['1.0', 'nan']);
    expect(k('conjugate', [one, '-inf'])).toEqual(['1.0', 'inf']);
    expect(k('conjugate', ['inf', F.neg(one)])).toEqual(['inf', '1.0']);
    expect(k('sign', ['-inf', F.ZERO])).toEqual(['-1.0', '0.0']);
    expect(k('sign', ['nan', F.ZERO])).toEqual(['nan', 'nan']);
  });
  it('evaluates oo, -oo and nan as mpmath values; zoo has none', () => {
    expect(() => evalMp(S.Infinity, 53)).toThrow(MpSpecialValue);
    expect(() => evalMp(parse('x'), 53)).toThrow('no value for x');
    // a numeric coefficient belongs to SymPy's atom -oo (-1*oo, -2*oo); not to a special value of a function
    const E2 = (e: Expr) => sstr(evalf(e));
    expect(E2(new Mul([Rational.of(-2), S.Infinity, parse('pi')]))).toBe('-oo');
    expect(E2(new Mul([Rational.of(2), S.NegativeInfinity, parse('pi')]))).toBe('-oo');
    expect(E2(new Mul([Rational.of(-1), S.NaN, parse('pi')]))).toBe('nan');
    expect(E2(new Mul([parse('pi'), S.Infinity, parse('E')]))).toBe('oo');
    expect(() => evalMp(S.ComplexInfinity, 53)).toThrow('cannot evaluate Special');
    expect(n('exp(oo*I + 1)')).toBe('nan');
  });
});
