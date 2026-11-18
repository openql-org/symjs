// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/puiseux.ts.
// Puiseux series expansion. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Rational, Sym, add, beta, hyper, mul, parse, pow, series, str } from '../../src';
import type { Expr } from '../../src';
import { Expander, SCALED_BESSELK, SCALED_BESSELI, SCALED_EI, SCALED_ERFC, SeriesError } from '../../src/series/puiseux';
import { ExtensionExpr, UndefFn } from '../../src/core/nodes';

// Remaining branches of the limit, series and summation code. Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y, z, n, k, a, b, c, m, t] = [V('x'), V('y'), V('z'), V('n'), V('k'), V('a'), V('b'), V('c'), V('m'), V('t')];
const [pp, qq, rr] = [V('p'), V('q'), V('r')];
const pw = (e: unknown): sj.Piecewise => {
  if (!(e instanceof sj.Piecewise)) throw new TypeError('a Piecewise expected');
  return e;
};
const conc = (e: unknown): sj.Concrete => {
  if (!(e instanceof sj.Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const conv = (e: unknown) => sj.isConvergent(conc(e));
const aconv = (e: unknown) => sj.isAbsolutelyConvergent(conc(e));
const moo = P('-oo');
void [x, y, z, n, k, a, b, c, m, t, pp, qq, rr, conv, aconv, moo, pw];

describe('the expansion in t (series/puiseux.ts)', () => {
  const tt = new Sym('_t', { positive: true });
  const E = () => new Expander(tt);
  const Q = (s: string) => parse(s, { symbols: [tt] });
  const ser = (s: string, order: number) => {
    const ps = E().ser(Q(s), Rational.of(order));
    return ps.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ') + ` | order ${ps.order.toString()}`;
  };
  it('expands the scaled Ei and erfc helpers only at positive infinity', () => {
    for (const name of [SCALED_EI, SCALED_ERFC]) {
      expect(() => E().ser(new UndefFn(name, [tt]), Rational.of(2))).toThrow(SeriesError);
      const ps = E().ser(new UndefFn(name, [pow(tt, -1)]), Rational.of(4));
      expect(ps.terms.map((t) => [String(t.e), String(t.c)])).toEqual(name === SCALED_EI ? [['1', '1'], ['2', '1'], ['3', '2']] : [['1', '1/sqrt(pi)'], ['3', '-1/(2*sqrt(pi))']]);
    }
  });

  it('to an order that is not positive gives the value at 0 (exact for the exponents below the order)', () => {
    expect(ser('sin(_t)', 0)).toBe(' | order 1000000');
    expect(ser('exp(_t)', 0)).toBe('1*t**0 | order 1000000');
    expect(ser('besselj(1, _t)', 0)).toBe(' | order 1000000');
  });

  it('expands cot(t)**2 with more precision for the pole (SymPy: 1/t**2 - 2/3 + t**2/15)', () => {
    expect(ser('cot(_t)**2', 3)).toBe('1*t**-2 + -2/3*t**0 + 1/15*t**2 | order 3');
  });

  it('raises when the leading term is 0 to every order it tries', () => {
    expect(() => E().ser(Q('((sin(a)**2 + cos(a)**2 - 1)*_t + _t**10)**(1/2)'), Rational.of(2))).toThrow(SeriesError);
    expect(() => E().ser(Q('log((sin(a)**2 + cos(a)**2 - 1)*_t)'), Rational.of(2))).toThrow(SeriesError);
    expect(() => E().ser(Q('sign((sin(a)**2 + cos(a)**2 - 1)*_t)'), Rational.of(2))).toThrow(SeriesError);
  });

  it('stops at a nesting depth of 200', () => {
    let e = '_t';
    for (let i = 0; i < 201; i++) e = `exp(${e})`;
    expect(() => E().ser(Q(e), Rational.of(1))).toThrow('recursion too deep');
  });
});

describe('expansions on branch cuts and at branch points (SymPy 1.14 series)', () => {
  it.each([
    ['acoth(x)', '-I*pi/2 + x + O(x**3)'],
    ['acoth(-x)', 'I*pi/2 - x + O(x**3)'],
    ['asech(x)', 'log(2) - log(x) - x**2/4 + O(x**3)'],
    ['asech(-x)', 'I*pi + log(2) - log(x) - x**2/4 + O(x**3)'],
    ['acsch(x)', 'log(2) - log(x) + x**2/4 + O(x**3)'],
    ['acsch(-x)', '-log(2) + log(x) - x**2/4 + O(x**3)'],
    ['sqrt(-1 + a*x)', 'I - I*a*x/2 - I*a**2*x**2/8 + O(x**3)'],
    ['sqrt(-1 + f(1)*x)', 'I - I*x*f(1)/2 - I*x**2*f(1)**2/8 + O(x**3)'],
    ['1/(f(a) + 1 + x)', '1/(f(a) + 1) - x/(f(a) + 1)**2 + x**2/(f(a) + 1)**3 + O(x**3)'],
    ['loggamma(x + 1)', '-EulerGamma*x + pi**2*x**2/12 + O(x**3)'],
    ['log(-1 - I*x)', '-I*pi + I*x + x**2/2 + O(x**3)'],
    ['sqrt(-1 - I*x**2)', '-I + x**2/2 + O(x**3)'],
  ])('series(%s, x, 0, 3) = %s', (e, expected) => {
    const [x] = sj.symbols('x');
    expect(String(sj.series(parse(e), x, 0, 3))).toBe(expected);
  });
  it('keeps acsch real for a small negative argument', () => {
    // SymPy 1.14 gives I*pi + log(2) - log(x) + x + 3*x**2/4 + O(x**3), which is wrong: acsch(-1/1000) = -7.6009...
    // is real (acsch is odd), and this series is -acsch(x - x**2)
    const [x] = sj.symbols('x');
    expect(String(sj.series(parse('acsch(x**2 - x)'), x, 0, 3))).toBe('-log(2) + log(x) - x - 3*x**2/4 + O(x**3)');
  });
  it('does not expand acoth at 0 along an unknown direction', () => {
    // SymPy 1.14: log(1/a)/2 - log(-1/a)/2 + a*x + O(x**3)
    const [x] = sj.symbols('x');
    expect(() => sj.series(parse('acoth(a*x)'), x, 0, 3)).toThrow();
  });
});

describe('Ei, frac and the Gruntz Bessel helpers (SymPy 1.14)', () => {
  const [u, w] = sj.symbols('u w');
  const S = (e: sj.Expr, d: '+' | '-' = '+', k = 6) => String(sj.series(e, u, 0, k, d));
  const Q = (s: string) => parse(s, { symbols: [u, w], locals: { frac: sj.frac } });
  it('expands Ei at 0 with log(g), or log(-g) on the negative real axis', () => {
    expect(S(Q('Ei(-u)'))).toBe('EulerGamma + log(u) - u + u**2/4 - u**3/18 + u**4/96 - u**5/600 + O(u**6)');
    expect(S(Q('Ei(-u)'), '-')).toBe('EulerGamma + log(-u) - u + u**2/4 - u**3/18 + u**4/96 - u**5/600 + O(u**6)');
    expect(S(Q('Ei(u**2)'), '-')).toBe('EulerGamma + 2*log(-u) + u**2 + u**4/4 + O(u**6)');
    expect(S(Q('Ei(I*u)'))).toBe('I*pi/2 + EulerGamma + log(u) + I*u - u**2/4 - I*u**3/18 + u**4/96 + I*u**5/600 + O(u**6)');
    expect(S(Q('Ei(u*w)'))).toBe('EulerGamma + log(w) + log(u) + u*w + u**2*w**2/4 + u**3*w**3/18 + u**4*w**4/96 + u**5*w**5/600 + O(u**6)');
    expect(S(Q('Ei(-log(2)*u)'), '+', 2)).toBe('EulerGamma + log(log(2)) + log(u) - u*log(2) + O(u**2)');
  });

  it('expands frac on either side of its jumps', () => {
    expect(S(Q('frac(u)'))).toBe('u');
    expect(S(Q('frac(u)'), '-')).toBe('u + 1');
    expect(S(Q('frac(-u)'))).toBe('1 - u');
    expect(S(Q('frac(u + 1/2)'), '-')).toBe('u + 1/2');
    expect(S(Q('frac(3 + u**2)'), '-', 3)).toBe('u**2');
    expect(S(Q('frac(w + u)'))).toBe('u + frac(w)');
    // the side is not known (SymPy: u*w), or w could be an integer (SymPy: -u + frac(w), wrong for an integer w)
    expect(() => S(Q('frac(u*w)'))).toThrow(SeriesError);
    expect(() => S(Q('frac(w - u)'))).toThrow(SeriesError);
    // (no power of u in the argument shows the side)
    expect(() => S(Q('frac(1 + exp(-1/u))'))).toThrow(SeriesError);
  });

  it('keeps exp(c/u) for a constant c of unknown sign', () => {
    expect(S(Q('exp(f(1)/u)'))).toBe('exp(f(1)/u)');
  });

  it('expands the scaled Bessel functions only at an argument tending to oo', () => {
    const t = new Sym('t', { positive: true });
    expect(() => new Expander(t).ser(new UndefFn(SCALED_BESSELI, [Rational.of(0), t]), Rational.of(1))).toThrow(SeriesError);
  });
});

describe('series of hyper and beta (sympy.stats moments from moment generating functions)', () => {
  const [t, a, b] = [new Sym('t'), new Sym('a'), new Sym('b')];
  const sr = (e: Expr, n: number): string => str(series(e, t, 0, n));
  it('hyper with an argument that vanishes at 0', () => {
    expect(sr(hyper([a], [b], t), 3)).toBe('1 + a*t/b + a*t**2*(a + 1)/(2*b*(b + 1)) + O(t**3)');
    expect(sr(hyper([1], [Rational.of(3, 2)], mul(Rational.of(1, 2), pow(t, 2))), 5)).toBe('1 + t**2/3 + t**4/15 + O(t**5)');
  });
  it('hyper with an argument that does not vanish at 0', () => {
    // SymPy: E - 1 + t + O(t**2) (by hyperexpand); symjs expands only about a vanishing argument
    expect(() => series(hyper([1], [2], add(1, t)), t, 0, 2)).toThrow('cannot expand');
  });
  it('beta as a quotient of gamma functions', () => {
    expect(sr(beta(add(1, mul(-1, t)), add(1, t)), 3)).toBe('1 + pi**2*t**2/6 + O(t**3)');
  });
});

describe('abs of a term with a negative leading coefficient', () => {
  it('Expander: abs(t**2 - t) = t - t**2 for t -> 0+', () => {
    const t = new Sym('_t', { positive: true });
    const ps = new Expander(t).ser(parse('Abs(_t**2 - _t)', { symbols: [t] }), Rational.of(3));
    expect(ps.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ')).toBe('1*t**1 + -1*t**2');
    const qs = new Expander(t).ser(parse('Abs(_t + b*_t**2)', { symbols: [t] }), Rational.of(3));
    expect(qs.terms.map((u) => `${u.c.toString()}*t**${u.e.toString()}`).join(' + ')).toBe('1*t**1 + b*t**2');
    // a symbolic leading coefficient: its sign is not known
    expect(() => new Expander(t).ser(parse('Abs(b*_t + _t**2)', { symbols: [t] }), Rational.of(3))).toThrow(SeriesError);
  });
});

/** A function application with a Taylor series and no tractable rewrite: f(u) = 1/u, f'(u) = -1/u**2. */
class Recip extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Recip', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Recip(args);
  }
  override get isTaylorExpandable(): boolean {
    return true;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const u = this.args[0] ?? x;
    return mul(-1, pow(u, -2), d(u, x));
  }
}

/** A function application whose derivative cannot be taken. */
class Broken extends Recip {
  override withArgs(): Expr {
    throw new TypeError('no rebuild');
  }
}

describe('Taylor series of extension function applications', () => {
  const x = new Sym('x');
  it('expands at a regular point and keeps the value there', () => {
    expect(str(series(new Recip([add(x, 1)]), x, 0, 3))).toBe('Recip(1) - x + x**2 + O(x**3)');
  });
  it('expands the argument to order one for a non-positive order', () => {
    const t = new Sym('_t');
    expect(new Expander(t).ser(new Recip([add(t, 1)]), Rational.of(0)).terms.map((term) => str(term.c))).toEqual(['Recip(1)']);
  });
  it('throws at a singular point without a tractable rewrite', () => {
    expect(() => series(new Recip([x]), x, 0, 3)).toThrow(SeriesError);
  });
  it('rethrows other errors', () => {
    expect(() => series(new Broken([add(x, 1)]), x, 0, 3)).toThrow('no rebuild');
  });
});

class TractableRecip extends Recip {
  override rewriteSelf(): Expr {
    return pow(this.args[0] ?? sj.S.One, -1);
  }
}

describe('singular and multivariate function arguments', () => {
  const t = new Sym('t', { positive: true });
  const e = new Expander(t);
  const p = (s: string) => parse(s, { symbols: [t] });
  const terms = (expression: Expr, n = 3) => e.ser(expression, Rational.of(n)).terms.map((term) => [str(term.c), str(term.e)]);
  it('expands extension applications and their tractable rewrites', () => {
    expect(terms(new Recip([add(t, 1), t]))).toEqual([['Recip(1, 0)', '0'], ['-1', '1'], ['1', '2']]);
    expect(terms(new Recip([add(t, 1), Rational.of(7)]))).toEqual([['Recip(1, 7)', '0'], ['-1', '1'], ['1', '2']]);
    expect(() => terms(new Recip([pow(t, -1)]))).toThrow(SeriesError);
    expect(terms(new TractableRecip([t]))).toEqual([['1', '-1']]);
  });
  it('rejects multivariate and singular ordinary function arguments', () => {
    expect(() => terms(new sj.Fn('atan2', [t, t]))).toThrow(SeriesError);
    expect(() => terms(new sj.Fn('atan2', [pow(t, -1), sj.S.One]))).toThrow(SeriesError);
  });
  it('keeps constant terms when the perturbation is smaller than all powers', () => {
    expect(terms(new sj.Fn('sign', [p('1 + exp(-1/t)')]))).toEqual([['1', '0']]);
    expect(terms(new sj.Fn('floor', [p('1 + exp(-1/t)')]))).toEqual([['1', '0']]);
  });
  it('uses the Taylor coefficients of elliptic integrals at zero', () => {
    expect(terms(p('elliptic_k(t)'), 2)).toEqual([['pi/2', '0'], ['pi/8', '1']]);
    expect(terms(p('elliptic_k(t + 2)'), 0)).toEqual([['elliptic_k(2)', '0']]);
    expect(terms(p('elliptic_k(t + a)'), 0)).toEqual([['elliptic_k(a)', '0']]);
  });
  it('expands inverse functions to non-positive order at regular and branch points', () => {
    expect(terms(p('asin(t)'), 0)).toEqual([]);
    expect(terms(p('acosh(1 + t)'), 2)).toEqual([['sqrt(2)', '1/2'], ['-sqrt(2)/12', '3/2']]);
    expect(terms(p('acosh(t)'), 1)).toEqual([['I*pi/2', '0']]);
  });
  it('expands loggamma and digamma at infinity using Bernoulli coefficients', () => {
    expect(terms(p('polygamma(0, 1/t)'))).toEqual([['-_L', '0'], ['-1/2', '1'], ['-1/12', '2']]);
    expect(terms(p('loggamma(1/t)'))).toEqual([['-_L - 1', '-1'], ['_L/2 + log(2*pi)/2', '0'], ['1/12', '1']]);
    expect(() => terms(p('loggamma(-1/t)'))).toThrow(SeriesError);
  });
  it('expands both scaled Bessel helpers at infinity', () => {
    expect(terms(new UndefFn(SCALED_BESSELI, [sj.S.Zero, pow(t, -1)]), 2)).toEqual([['sqrt(2)/(2*sqrt(pi))', '1/2'], ['sqrt(2)/(16*sqrt(pi))', '3/2']]);
    expect(terms(new UndefFn(SCALED_BESSELK, [sj.S.Zero, pow(t, -1)]), 2)).toEqual([['sqrt(2)*sqrt(pi)/2', '1/2'], ['-sqrt(2)*sqrt(pi)/16', '3/2']]);
    expect(() => terms(new UndefFn(SCALED_BESSELI, [sj.S.Zero, pow(mul(-1, t), -1)]))).toThrow(SeriesError);
  });
});

it('expands acot at its zero branch point through logarithms', () => {
  const t = new Sym('t', { positive: true });
  expect(str(series(new sj.Fn('acot', [t]), t, 0, 2))).toBe('pi/2 - t + O(t**2)');
});

it('expands the logarithmic coefficients of reciprocal inverse functions', () => {
  const x = new Sym('x');
  expect(sj.sstr(series(sj.asec(x), x, 0, 5))).toBe('I*log(2) - I*log(x) - I*x**2/4 - 3*I*x**4/32 + O(x**5)');
  expect(sj.sstr(series(sj.acsc(x), x, 0, 5))).toBe('-I*log(2) + pi/2 + I*log(x) + I*x**2/4 + 3*I*x**4/32 + O(x**5)');
});

it('expands smooth functions at finite arguments and real absolute-value displacements', () => {
  const t = new Sym('t', { positive: true });
  const f = sj.SymFunction('f');
  expect(() => sj.series(f(t.pow(-1)), t)).toThrow(SeriesError);
  expect(String(sj.series(f(t), t, 0, 0))).toContain('O(');
  expect(String(sj.series(sj.erfc(t.pow(-1)), t))).toBe('O(t**6)');
  const a = new Sym('a', { real: true });
  expect(() => new Expander(t).ser(sj.erf(a.mul(t.pow(-1))), sj.rational(3))).toThrow(SeriesError);
  const z = new Sym('z');
  const radius = sj.series(sj.abs(z.add(t)), t, 0, 3);
  expect(String(radius)).toContain('re(sign(z))');
});

it('handles signs and zero truncation at the edge of the expansion', () => {
  const t = new Sym('t', { positive: true }), r = new Sym('r', { real: true });
  const engine = new Expander(t,x);
  expect(engine.ser(new UndefFn('f',[t]),sj.S.Zero).coeff(sj.S.Zero).toString()).toBe('f(0)');
  expect(() => engine.ser(sj.erf(sj.mul(r,sj.pow(t,-1))),sj.S.One)).toThrow(SeriesError);
  expect(engine.ser(new sj.Fn('erfc', [sj.mul(-1,sj.pow(t,-1))]),sj.S.One).coeff(sj.S.Zero).equals(2)).toBe(true);
  expect(String(series(P('frac(-x**8)'),x,0,4))).toBe('1 + O(x**4)');
  expect(String(series(P('frac(x**8)'),x,0,4))).toBe('O(x**4)');
});
