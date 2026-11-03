// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/evalf.ts.

import { afterEach, describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { add, exp, I, mul, sqrt, symbol, symbols } from '../../src';
import type { Expr } from '../../src';
import * as C from '../../src/numeric/mpconst';
import { sha256, SYMPY_1000 } from './mpconst.ref';

const [x, y] = symbols('x y');
const theta = symbol('theta', { real: true });
const { parse, sstr, evalf } = sj;
const p = (s: string) => parse(s);
const f = sj.SymFunction('f');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: { x, y }, functions: { f } } as never);

afterEach(() => C.clearConstantCache());

// The constants through the default method tables and the cache (mpfun mp*
// functions, evalf) against mpmath 1.3.0 / SymPy 1.14.0 (see mpconst.ref.ts).

describe('evalf at 1000 digits equals SymPy', () => {
  for (const [e, head, tail, hash] of SYMPY_1000) {
    it(e, () => {
      const s = sj.sstr(sj.evalf(sj.parse(e), 1000));
      expect(s.slice(0, 30)).toBe(head);
      expect(s.slice(-30)).toBe(tail);
      expect(sha256(s)).toBe(hash);
    });
  }
});

describe('numeric', () => {
  it('evaluates numerically', () => {
    expect(sqrt(2).toNumber()).toBeCloseTo(Math.SQRT2);
    const v = exp(mul(I, theta)).toComplex({ theta: Math.PI / 3 });
    expect(v.re).toBeCloseTo(0.5);
    expect(v.im).toBeCloseTo(Math.sqrt(3) / 2);
    expect(add(x, sqrt(2)).evalf().toString()).toBe('x + 1.4142135623731');
  });
});

// Expected values from SymPy 1.14 / mpmath 1.3 (evalf with subs, toComplex, lambdify).

describe('evalf with substituted values (mpmath functions)', () => {
  const z = p('2 + 3*I');
  const cases: [string, string][] = [
    ['Abs(x)', '3.6055512754639892931'],
    ['re(x)', '2.0000000000000000000'],
    ['im(x)', '3.0000000000000000000'],
    ['arg(x)', '0.98279372324732906799'],
    ['conjugate(x)', '2.0 - 3.0*I'],
    ['sign(x)', '0.55470019622522912202 + 0.83205029433784368303*I'],
    ['log(x, 2)', '1.8502198590705460802 + 1.4178716307457219966*I'],
  ];
  it('evaluates at a complex point', () => {
    for (const [e, want] of cases) expect([e, sstr(evalf(p(e), 20, { subs: { x: z } }))]).toEqual([e, want]);
  });
  it('real arguments and constants', () => {
    expect(sstr(evalf(p('sign(x)'), 20, { subs: { x: -3 } }))).toBe('-1.0000000000000000000');
    expect(sstr(evalf(p('atan2(x, 2)'), 20, { subs: { x: 1 } }))).toBe('0.46364760900080611621');
    expect(sstr(evalf(p('TribonacciConstant'), 20))).toBe('1.8392867552141611326');
    expect(sstr(evalf(p('log(3, 2)'), 20))).toBe('1.5849625007211561815');
    expect(sstr(evalf(p('x + pi'), 20, { subs: { x: p('sqrt(2)') } }))).toBe('4.5558062159628882873');
    expect(sstr(evalf(p('x + pi'), { x: 0.5 }))).toBe('3.64159265358979');
    expect(sstr(evalf(p('x + pi'), new Map<Expr | string, number>([[x, 0.5]])))).toBe('3.64159265358979');
    expect(sstr(evalf(p('x + pi'), new Map<Expr | string, number>([['x', 0.5]])))).toBe('3.64159265358979');
    expect(sstr(evalf(p('x*y'), new Map<Expr | string, number>([[p('x*y'), 0.5]])))).toBe('x*y');
    expect(sstr(evalf(p('x + y'), { x: { re: 1, im: 2 }, y: 1 }))).toBe('2.0 + 2.0*I');
  });
  it('functions without a dedicated arbitrary-precision routine', () => {
    const ev = (e: string, v: Expr) => sstr(evalf(p(e), 20, { subs: { x: v } }));
    expect(ev('floor(x)', p('5/2'))).toBe('2.0000000000000000000');
    expect(ev('ceiling(x)', p('5/2'))).toBe('3.0000000000000000000');
    expect(ev('Max(x, 1)', p('5/2'))).toBe('2.5000000000000000000');
    expect(ev('binomial(x, 2)', p('5/2'))).toBe('1.8750000000000000000');
    expect(ev('binomial(x, 3)', p('2 + I'))).toBe('-0.5 + 0.16666666666666666667*I');
    expect(sstr(evalf(p('binomial(x, y)'), 20, { subs: { x: p('5/2'), y: p('1/3') } }))).toBe('1.5870083613413584686');
    expect(ev('factorial2(x)', p('5'))).toBe('15.000000000000000000');
    // a pole stays unevaluated (SymPy returns yn(0, x) unchanged; symjs keeps the
    // substituted argument, yn(0, 0))
    expect(ev('yn(0, x)', p('0'))).toMatch(/^yn\(0, [x0]\)$/);
    // the double-precision value is infinite: SymPy gives oo, symjs leaves the function unevaluated
    expect(ev('expint(1, x)', p('0'))).toMatch(/^expint\(1(\.0)?, [x0]\)$/);
    expect(ev('Min(x, 2)', p('1/2'))).toBe('0.50000000000000000000');
    // SymPy leaves erf2inv(x, -1) and subfactorial(x) unevaluated; symjs keeps the
    // substituted arguments (erf2inv is infinite there in double precision)
    expect(sstr(evalf(p('erf2inv(x, y)'), 20, { subs: { x: p('-1'), y: p('-1') } }))).toMatch(/^erf2inv\(/);
    expect(ev('subfactorial(x)', p('1/2'))).toMatch(/^subfactorial\(/);
  });
  it('chops small parts', () => {
    // SymPy N(e, chop=...)
    const ch = (e: string, chop: boolean | number) => sstr(evalf(p(e), 15, { chop }));
    expect(ch('exp(-100)', true)).toBe('0');
    expect(ch('exp(-100) + I', true)).toBe('1.0*I');
    expect(ch('I*exp(-100) + 2', true)).toBe('2.00000000000000');
    expect(ch('exp(-100)*(1 + I)', true)).toBe('0');
    expect(ch('exp(-10)', 1e-3)).toBe('0');
    expect(ch('exp(-10) + I*exp(-2)', 1e-3)).toBe('0.135335283236613*I');
    expect(sstr(evalf(p('Catalan + EulerGamma'), 20))).toBe('1.4931812590787518757');
    expect(sstr(evalf(p('x*GoldenRatio'), 30, { subs: { x: 1 } }))).toBe('1.61803398874989484820458683437');
  });
  it('keeps unevaluable parts symbolic', () => {
    // SymPy: (-x**2 + pi).evalf() = 3.14159265358979 - x**2; (x**3).evalf() = x**3
    expect(sstr(evalf(p('-x**2*y + pi')))).toBe('-x**2*y + 3.14159265358979');
    expect(sstr(evalf(p('x**3')))).toBe('x**3');
  });
});

describe('toComplex', () => {
  it('evaluates in double precision', () => {
    const v = sj.toComplex(p('x**2 + sin(y)'), { x: 2, y: 0 });
    expect([v.re, v.im]).toEqual([4, 0]);
    const w = sj.toComplex(p('Abs(x) + re(x) + im(x) + arg(1) + conjugate(x)'), { x: { re: 3, im: 4 } });
    expect([w.re, w.im]).toEqual([5 + 3 + 4 + 3, -4]);
    expect(sj.toComplex(p('E + EulerGamma')).re).toBeCloseTo(3.29549749336058, 14);
    expect(sj.toComplex(p('arg(x)'), { x: { re: 0, im: 2 } }).re).toBeCloseTo(Math.PI / 2, 15);
    expect(sj.toComplex(p('x**2'), { x: p('sqrt(2)') }).re).toBeCloseTo(2, 14);
    expect(() => sj.toComplex(p('subfactorial(x)'), { x: 0.5 })).toThrow(TypeError);
    expect(sj.toComplex(p('oo')).re).toBe(Infinity);
    expect(() => sj.toComplex(p('x'))).toThrow(TypeError);
    expect(() => sj.toComplex(p('x'), { y: 1 })).toThrow(TypeError);
    expect(() => sj.toComplex(p('gamma(x)'), { x: 1 })).not.toThrow();
    expect(() => sj.toComplex(p('f(x)'), { x: 1 })).toThrow(TypeError);
    expect(() => sj.toComplex(sj.Eq(x, 1), { x: 1 })).toThrow(TypeError);
  });
  it('evaluates Piecewise conditions', () => {
    const pw = (cond: Expr) => sj.Piecewise([1, cond], [2, true]);
    const ev = (e: Expr, v: number) => sj.toComplex(e, { x: v }).re;
    // SymPy: Piecewise((1, cond), (2, True)).subs(x, v)
    expect([ev(pw(sj.Gt(x, 0)), 1), ev(pw(sj.Gt(x, 0)), 0)]).toEqual([1, 2]);
    expect([ev(pw(sj.Ge(x, 0)), 0), ev(pw(sj.Ge(x, 0)), -1)]).toEqual([1, 2]);
    expect([ev(pw(sj.Lt(x, 0)), -1), ev(pw(sj.Lt(x, 0)), 0)]).toEqual([1, 2]);
    expect([ev(pw(sj.Le(x, 0)), 0), ev(pw(sj.Le(x, 0)), 1)]).toEqual([1, 2]);
    expect([ev(pw(sj.Eq(x, 0)), 0), ev(pw(sj.Eq(x, 0)), 1)]).toEqual([1, 2]);
    expect([ev(pw(sj.Ne(x, 0)), 1), ev(pw(sj.Ne(x, 0)), 0)]).toEqual([1, 2]);
    expect(() => ev(sj.Piecewise([1, sj.Gt(x, 0)]), -1)).toThrow(RangeError);
    expect(() => ev(sj.Piecewise([1, sj.And(sj.Gt(x, 0), sj.Lt(x, 2))], [2, true]), 1)).toThrow(TypeError);
  });
});

describe('lambdify', () => {
  it('checks its arguments', () => {
    const f = sj.lambdify(p('x + y'), [x, y]);
    expect(f(1, 2).re).toBe(3);
    expect(() => f(1)).toThrow(RangeError);
    expect(() => sj.lambdify(p('x + z'), [x, y])).toThrow(TypeError);
    const X = new sj.DeferredVector('X');
    const g = sj.lambdify(sj.add(X.at(1), x), [X, x]);
    expect(() => g(1, 2)).toThrow(RangeError);
    expect(g([5, 7], 1).re).toBe(8);
    // a symbol named like an entry of a vector that is not a parameter
    expect(() => sj.lambdify(new sj.Sym('Y[0]'), [x])).toThrow(TypeError);
  });
});

describe('evalf keeps the arguments of undefined functions', () => {
  const cases: [string, string][] = [
    ['f(1)', 'f(1)'],
    ['f(x/3)', 'f(x/3)'],
    ['f(pi)', 'f(pi)'],
    ['f(1, x/3)', 'f(1, x/3)'],
    ['2*f(1) + pi', '2.0*f(1) + 3.14159265358979'],
  ];
  it.each(cases)('%s', (src, expected) => {
    expect(String(sj.evalf(P(src)))).toBe(expected);
  });
});

describe('evalf with values that do not give a number (SymPy evalf(subs=...))', () => {
  // SymPy 1.14: the substituted expression is evaluated part by part when it is a sum, product
  // or power; otherwise the expression is returned unchanged
  const ev = (s: string, v: Record<string, number | Expr | { re: number; im: number }>) => sstr(evalf(p(s), v as never));
  it('returns a function or symbol unchanged', () => {
    expect(ev('yn(x, y)', { x: 0, y: 0 })).toBe('yn(x, y)');
    expect(ev('yn(0, x)', { x: 0 })).toBe('yn(0, x)');
    expect(ev('f(x)', { x: 1 })).toBe('f(x)');
    expect(ev('besselj(x, y)', { x: 0.5 })).toBe('besselj(x, y)');
    expect(ev('sin(x + y)', { x: 1 })).toBe('sin(x + y)');
    expect(ev('Abs(x + y)', { x: 1 })).toBe('Abs(x + y)');
    expect(ev('exp(x + y)', { x: 1 })).toBe('exp(x + y)');
    expect(ev('x*y', { x: 1 })).toBe('x*y');
    expect(ev('x', { y: 1 })).toBe('x');
  });
  it('evaluates the parts of a sum, product or power', () => {
    expect(ev('x + yn(0, y)', { x: 1, y: 0 })).toBe('yn(0, 0) + 1.0');
    expect(ev('f(x) + x', { x: 1 })).toBe('f(1) + 1.0');
    expect(ev('f(x) + sin(x)', { x: 2 })).toBe('f(2) + 0.909297426825682');
    expect(ev('sin(x)*yn(0, y)', { x: 1, y: 0 })).toBe('0.841470984807897*yn(0, 0)');
    expect(ev('f(x)*y', { x: 1 })).toBe('y*f(1)');
    expect(ev('yn(0, x)**2', { x: 0 })).toBe('yn(0, 0)**2');
    expect(ev('x**2*y', { x: 2 })).toBe('4.0*y');
    expect(ev('2*sin(x*y) + 1', { x: 1 })).toBe('2.0*sin(y) + 1.0');
    expect(ev('x + y', { x: { re: 1, im: 2 } })).toBe('y + 1.0 + 2.0*I');
  });
  it('infinities', () => {
    expect(ev('log(x)', { x: 0 })).toBe('-oo');
    expect(ev('log(x) + 1', { x: 0 })).toBe('-oo');
    expect(ev('log(x)', { x: sj.float('0.0') })).toBe('-oo');
    expect(ev('1/x', { x: 0 })).toBe('zoo');
    expect(ev('x/y', { x: 1, y: 0 })).toBe('zoo');
    // a pole of a function: unchanged
    expect(ev('gamma(x)', { x: 0 })).toBe('gamma(x)');
    expect(ev('2*gamma(x)', { x: 0 })).toBe('2*gamma(x)');
    expect(ev('gamma(x) + y', { x: -1, y: 1 })).toBe('y + gamma(x)');
  });
  it('a substituted expression that is a number', () => {
    expect(ev('Piecewise((1, x > 0), (2, True))', { x: 1 })).toBe('1.00000000000000');
  });
  it('functions keep their arguments without values (SymPy Function._eval_evalf)', () => {
    expect(sstr(evalf(p('sin(x + 1)')))).toBe('sin(x + 1)');
    expect(sstr(evalf(p('exp(x + 1)')))).toBe('exp(x + 1)');
    expect(sstr(evalf(p('2*sin(2*x + 1)')))).toBe('2.0*sin(2*x + 1)');
    expect(sstr(evalf(p('besselj(1/2, x)')))).toBe('besselj(1/2, x)');
  });
});

describe('evalf with values: log of zero', () => {
  it('a two-argument log at 0', () => {
    // SymPy log(x, 2).evalf(subs={x: 0}) = -oo (log(x)/log(2))
    expect(sstr(evalf(p('log(x, 2)'), { x: 0 }))).toBe('-oo');
    // an unevaluated two-argument log (SymPy has none) has a pole there: unchanged
    expect(sstr(evalf(sj.fn('log', [x, 2], { evaluate: false }), { x: 0 }))).toBe('log(x, 2)');
  });
});
