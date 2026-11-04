// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/risch.ts (the construction of differential extensions and the Risch
// integration drivers), from SymPy's sympy/integrals/tests/test_risch.py and the doctests of
// sympy.integrals.risch. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Lambda, S, Sym, log, mul, parse, str, symbols } from '../../src';
import type { Expr } from '../../src/core/nodes';
import { Integral, Pow, Rational } from '../../src/core/nodes';
import { NotImplementedError } from '../../src/core/errors';
import { DifferentialExtension, NonElementaryIntegral, integerPowers, integratePrimitive, integrateHyperexponential, integrateHyperexponentialPolynomial, rischIntegrate } from '../../src/integrals/risch';
import { decrementLevel } from '../../src/integrals/rischbase';
import { KPoly } from '../../src/integrals/rischpoly';

const [x, y, t, t0, t1, z, a, b] = [new Sym('x'), new Sym('y'), new Sym('t'), new Sym('t0'), new Sym('t1'), new Sym('z'), new Sym('a'), new Sym('b')];
const i = new Sym('i');
const P = (s: string, g: Sym = t): KPoly => KPoly.of(parse(s), g);
const E = (e: Expr | KPoly): string => str(e instanceof KPoly ? e.asExpr() : e);
const attrs = (de: DifferentialExtension): string[] => [
  E(de.fa),
  E(de.fd),
  de.D.map((d) => `${E(d)}|${d.gen.name}`).join(', '),
  de.T.map((s) => s.name).join(','),
  de.Tfuncs.map(String).join(', '),
  de.backsubs.map(([p, q]) => `(${E(p)}, ${E(q)})`).join(', '),
  de.exts.join(','),
  de.extargs.map(E).join(', '),
];
const DEof = (e: string, opts: { handleFirst?: 'log' | 'exp'; v?: Sym } = {}): DifferentialExtension => new DifferentialExtension(parse(e), opts.v ?? x, { handleFirst: opts.handleFirst });

describe('DifferentialExtension', () => {
  it('indices (the doctests of DifferentialExtension.indices)', () => {
    const de = new DifferentialExtension(parse('log(x) + exp(x)'), x, { handleFirst: 'exp' });
    expect(de.indices('log')).toEqual([2]);
    expect(de.indices('exp')).toEqual([1]);
  });
  it('exponential monomials (SymPy test_DifferentialExtension_exp)', () => {
    expect(attrs(DEof('exp(x) + exp(x**2)'))).toEqual(['t0 + t1', '1', '1|x, t0|t0, 2*t1*x|t1', 'x,t0,t1', 'Lambda(i, exp(i)), Lambda(i, exp(i**2))', '', 'none,exp,exp', '0, x, x**2']);
    expect(attrs(DEof('exp(x) + exp(2*x)'))).toEqual(['t0**2 + t0', '1', '1|x, t0|t0', 'x,t0', 'Lambda(i, exp(i))', '', 'none,exp', '0, x']);
    expect(attrs(DEof('exp(x) + exp(x/2)'))).toEqual(['t0**2 + t0', '1', '1|x, t0/2|t0', 'x,t0', 'Lambda(i, exp(i/2))', '', 'none,exp', '0, x/2']);
    expect(attrs(DEof('exp(x) + exp(x**2) + exp(x + x**2)'))[0]).toBe('t0 + t1*(t0 + 1)');
    expect(attrs(DEof('exp(x) + exp(x**2) + exp(x + x**2 + 1)'))[0]).toBe('t0 + t1*(E*t0 + 1)');
    expect(attrs(DEof('exp(x) + exp(x**2) + exp(x/2 + x**2)'))).toEqual(['t0**2 + t1*(t0 + 1)', '1', '1|x, t0/2|t0, 2*t1*x|t1', 'x,t0,t1', 'Lambda(i, exp(i/2)), Lambda(i, exp(i**2))', '(exp(x/2), sqrt(exp(x)))', 'none,exp,exp', '0, x/2, x**2']);
    expect(attrs(DEof('exp(x) + exp(x**2) + exp(x/2 + x**2 + 3)'))[0]).toBe('t0**2 + t1*(t0*exp(3) + 1)');
    expect(attrs(DEof('sqrt(exp(x))'))).toEqual(['t0', '1', '1|x, t0/2|t0', 'x,t0', 'Lambda(i, exp(i/2))', '(exp(x/2), sqrt(exp(x)))', 'none,exp', '0, x/2']);
    expect(attrs(DEof('exp(x/2)'))[5]).toBe('');
  });
  it('logarithmic monomials (SymPy test_DifferentialExtension_log and _symlog)', () => {
    expect(attrs(DEof('log(x)*log(x + 1)*log(2*x**2 + 2*x)'))).toEqual(['t0*t1**2 + t1*(t0**2 + t0*log(2))', '1', '1|x, 1/x|t0, 1/(x + 1)|t1', 'x,t0,t1', 'Lambda(i, log(i)), Lambda(i, log(i + 1))', '', 'none,log,log', '0, x, x + 1']);
    expect(attrs(DEof('x**x*log(x)'))).toEqual(['t0*t1', '1', '1|x, 1/x|t0, t1*(t0 + 1)|t1', 'x,t0,t1', 'Lambda(i, log(i)), Lambda(i, exp(i*t0))', '(exp(x*log(x)), x**x)', 'none,log,exp', '0, x, t0*x']);
    expect(attrs(DEof('log(x**x)'))[0]).toBe('t0*x');
    expect(attrs(DEof('log(x**y)'))).toEqual(['t0*y', '1', '1|x, 1/x|t0', 'x,t0', 'Lambda(i, log(i))', '(y*log(x), log(x**y))', 'none,log', '0, x']);
    expect(attrs(DEof('log(sqrt(x))')).slice(0, 2)).toEqual(['t0', '2']);
  });
  it('handle_first (SymPy test_DifferentialExtension_handle_first)', () => {
    expect(attrs(DEof('exp(x)*log(x)', { handleFirst: 'log' })).slice(2, 5)).toEqual(['1|x, 1/x|t0, t1|t1', 'x,t0,t1', 'Lambda(i, log(i)), Lambda(i, exp(i))']);
    expect(attrs(DEof('exp(x)*log(x)', { handleFirst: 'exp' })).slice(2, 5)).toEqual(['1|x, t0|t0, 1/x|t1', 'x,t0,t1', 'Lambda(i, exp(i)), Lambda(i, log(i))']);
    const f = '-x**x*log(x)**2 + x**x - x**x/x';
    expect(attrs(DEof(f, { handleFirst: 'exp' }))).toEqual(attrs(DEof(f, { handleFirst: 'log' })));
    expect(attrs(DEof(f)).slice(0, 3)).toEqual(['t1*(-t0**2*x + x - 1)', 'x', '1|x, 1/x|t0, t1*(t0 + 1)|t1']);
  });
  it('levels (SymPy test_DifferentialExtension_all_attrs and test_DecrementLevel)', () => {
    const de = DEof('exp(x)*log(x)', { handleFirst: 'exp' });
    expect([E(de.f), E(de.newf), de.cases, de.case, de.level, de.t.name, E(de.d)]).toEqual(['exp(x)*log(x)', 't0*t1', ['base', 'exp', 'primitive'], 'primitive', -1, 't1', '1/x']);
    expect(() => de.incrementLevel()).toThrow(RangeError);
    de.decrementLevel();
    expect([de.level, de.t.name, E(de.d), de.case]).toEqual([-2, 't0', 't0', 'exp']);
    de.decrementLevel();
    expect([de.level, de.t.name, E(de.d), de.case]).toEqual([-3, 'x', '1', 'base']);
    expect(() => de.decrementLevel()).toThrow(RangeError);
    de.incrementLevel();
    de.incrementLevel();
    expect([de.level, de.case]).toEqual([-1, 'primitive']);
    const d2 = DEof('x*log(exp(x) + 1)');
    expect(() =>
      decrementLevel(d2, () => {
        throw new TypeError('inside');
      }),
    ).toThrow(TypeError);
    expect([d2.level, d2.t.name, E(d2.d), d2.case]).toEqual([-1, 't1', 't0/(t0 + 1)', 'primitive']);
    expect(String(d2)).toBe('DifferentialExtension({fa=Poly(t1*x, t1), fd=Poly(1, t1), D=[Poly(1, x), Poly(t0, t0), Poly(t0/(t0 + 1), t1)]})');
  });
  it('a manual extension (SymPy test_DifferentialExtension_extension_flag)', () => {
    const de = new DifferentialExtension({ D: [P('1', x), P('t')] });
    expect([E(de.d), de.t.name, de.level, de.cases, de.x.name, de.case]).toEqual(['t', 't', -1, ['base', 'exp'], 'x', 'exp']);
    expect(() => new DifferentialExtension(parse('x'))).toThrow();
  });
  it('miscellaneous (SymPy test_DifferentialExtension_misc and _Rothstein)', () => {
    expect(attrs(DEof('sin(y)*exp(x)')).slice(0, 3)).toEqual(['t0*sin(y)', '1', '1|x, t0|t0']);
    expect(() => DEof('sin(x)')).toThrow(NotImplementedError);
    expect(attrs(DEof('10**x'))).toEqual(['t0', '1', '1|x, t0*log(10)|t0', 'x,t0', 'Lambda(i, exp(i*log(10)))', '(exp(x*log(10)), 10**x)', 'none,exp', '0, x*log(10)']);
    expect(attrs(DEof('log(x) + log(x**2)')).slice(0, 3)).toEqual(['3*t0', '1', '1|x, 1/x|t0']);
    expect(attrs(DEof('0'))).toEqual(['0', '1', '1|x', 'x', '', '', 'none', '0']);
    const f = '(2581284541*exp(x) + 1757211400)/(39916800*exp(3*x) + 119750400*exp(x)**2 + 119750400*exp(x) + 39916800)*exp(1/(exp(x) + 1) - 10*x)';
    expect(attrs(DEof(f)).slice(0, 3)).toEqual(['t1*(2581284541*t0 + 1757211400)', '39916800*t0**3 + 119750400*t0**2 + 119750400*t0 + 39916800', '1|x, t0|t0, t1*(-10*t0**2 - 21*t0 - 10)/(t0**2 + 2*t0 + 1)|t1']);
  });
  it('rewrites trigonometric functions with complex exponentials and logarithms', () => {
    expect(attrs(new DifferentialExtension(parse('sin(x)'), x, { rewriteComplex: true })).slice(0, 3)).toEqual(['-I*t0**2 + I', '2*t0', '1|x, I*t0|t0']);
    expect(attrs(new DifferentialExtension(parse('tan(atan(x))'), x, { rewriteComplex: true }))[0]).toBe('x');
  });
  it('fails on algebraic and other non-transcendental integrands', () => {
    expect(() => DEof('sqrt(x)')).toThrow(NotImplementedError);
    expect(() => DEof('exp(sqrt(x))')).toThrow(NotImplementedError);
    // exp(log(x)/2) = sqrt(x): an algebraic radical
    expect(() => DEof('exp(x) + exp(x + log(x)/2)')).toThrow(NotImplementedError);
  });
  it('rewrites powers through existing logarithms (the structure theorems)', () => {
    // x**x with log(x) already a monomial
    expect(attrs(DEof('log(x)*x**x')).slice(2, 4)).toEqual(['1|x, 1/x|t0, t1*(t0 + 1)|t1', 'x,t0,t1']);
    // (2*x)**x: t0 = log(2*x), log(x) = t0 - log(2)
    expect(attrs(DEof('log(x) + (2*x)**x')).slice(0, 4)).toEqual(['t0 + t1 - log(2)', '1', '1|x, 1/x|t0, t1*(t0 + 1)|t1', 'x,t0,t1']);
    // exp(log(x) + x) = x*exp(x)
    expect(attrs(DEof('log(x) + exp(x + 2*log(x))', { handleFirst: 'log' })).slice(0, 4)).toEqual(['t0 + t1*x**2', '1', '1|x, 1/x|t0, t1|t1', 'x,t0,t1']);
    // exp(-log(x)) = 1/x
    expect(attrs(DEof('log(x)*exp(-log(x))')).slice(0, 2)).toEqual(['t0', 'x']);
    // exp(x/2 + log(x)/2)**2: a radical, restart
    expect(attrs(DEof('exp(x)*log(x) + exp(x/2 + log(x)/2)**2', { handleFirst: 'exp' }))[0]).toBe('t0*t1 + t0*x');
  });
});

describe('integer_powers', () => {
  it('groups rational multiples (SymPy test_integer_powers)', () => {
    const r = integerPowers(['x', 'x/2', 'x**2 + 1', '2*x/3'].map((s) => parse(s)));
    expect(r.map(([bse, l]) => [E(bse), l.map(([u, v]) => `${E(u)}:${E(v)}`)])).toEqual([
      ['x/6', ['x:6', 'x/2:3', '2*x/3:4']],
      ['x**2 + 1', ['x**2 + 1:1']],
    ]);
  });
});

describe('integrate_hyperexponential', () => {
  const lam = (e: string) => Lambda(i, parse(e, { symbols: [i] }));
  it('SymPy test_integrate_hyperexponential', () => {
    const de = new DifferentialExtension({ D: [P('1', x), P('t')], Tfuncs: [lam('exp(i)')] });
    expect(integrateHyperexponential(P('t'), P('1'), de).map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['exp(x)', '0', true]);
    const r = integrateHyperexponential(P('25*t**6 - 10*t**5 + 7*t**4 - 8*t**3 + 13*t**2 + 2*t - 1'), P('25*t**6 + 35*t**4 + 11*t**2 + 1'), de);
    expect(r.map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['(10*exp(x) - 11)/(25*exp(2*x) + 5) + log(exp(2*x) + 1)', '-1', true]);
    expect(integrateHyperexponential(P('x**2/2*t'), P('1'), de).map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['(x**2 - 2*x + 2)*exp(x)/2', '0', true]);
    expect(integrateHyperexponential(P('1 + t'), P('t'), de).map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['-exp(-x)', '1', true]);
    const ne = integrateHyperexponential(P('x'), P('t + 1'), de);
    expect([E(ne[0]), ne[1] instanceof NonElementaryIntegral, E(ne[1]), ne[2]]).toEqual(['0', true, 'Integral(x/(exp(x) + 1), x)', false]);
    const de2 = new DifferentialExtension({ D: [P('1', x), P('2*x*t')], Tfuncs: [lam('exp(i**2)')] });
    const ne2 = integrateHyperexponential(P('t'), P('1'), de2);
    expect([E(ne2[0]), E(ne2[1]), ne2[2]]).toEqual(['0', 'Integral(exp(x**2), x)', false]);
    const de3 = new DifferentialExtension({ D: [P('1', x), P('t0', t0), P('t0*t')], Tfuncs: [lam('exp(i)'), lam('exp(exp(i))')] });
    expect(E(integrateHyperexponential(P('2*t0*t**2'), P('1'), de3)[0])).toBe('exp(2*exp(x))');
  });
  it('returns a Piecewise for a symbolic rate (SymPy test_integrate_hyperexponential_returns_piecewise)', () => {
    const show = (de: DifferentialExtension) => integrateHyperexponential(de.fa, de.fd, de).map((v) => (typeof v === 'boolean' ? v : E(v)));
    expect(show(new DifferentialExtension(parse('a**x'), x))).toEqual(['Piecewise((exp(x*log(a))/log(a), Ne(log(a), 0)), (x, True))', '0', true]);
    expect(show(new DifferentialExtension(parse('exp(a*x)'), x))).toEqual(['Piecewise((exp(a*x)/a, Ne(a, 0)), (x, True))', '0', true]);
    expect(show(new DifferentialExtension(parse('x*exp(a*x)'), x))).toEqual(['Piecewise(((a*x - 1)*exp(a*x)/a**2, Ne(a**2, 0)), (x**2/2, True))', '0', true]);
    expect(show(new DifferentialExtension(parse('x**y + z'), y))).toEqual(['Piecewise((exp(y*log(x))/log(x), Ne(log(x), 0)), (y, True))', 'z', true]);
    const de = new DifferentialExtension(parse('exp(a*x)'), x);
    expect(E(integrateHyperexponential(de.fa, de.fd, de, undefined, 'none')[0])).toBe('exp(a*x)/a');
  });
  it('integrate_hyperexponential_polynomial with a zero polynomial', () => {
    const de = new DifferentialExtension({ D: [P('1', x), P('t0', t0)] });
    expect(integrateHyperexponentialPolynomial(P('0', t0), P('0', z), de).map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['0', '1', true]);
  });
  it('a nonelementary Laurent polynomial part', () => {
    // exp(x)/x + exp(-x)/x: neither term has an elementary integral
    const de = new DifferentialExtension({ D: [P('1', x), P('t')], Tfuncs: [lam('exp(i)')] });
    const r = integrateHyperexponential(P('t**2 + 1'), P('x*t'), de);
    expect([E(r[0]), E(r[1]), r[2]]).toEqual(['0', 'Integral((exp(2*x) + 1)*exp(-x)/x, x)', false]);
  });
});

describe('integrate_primitive', () => {
  const lam = (e: string) => Lambda(i, parse(e, { symbols: [i] }));
  it('SymPy test_integrate_primitive', () => {
    const de = new DifferentialExtension({ D: [P('1', x), P('1/x')], Tfuncs: [lam('log(i)')] });
    expect(integratePrimitive(P('t'), P('1'), de).map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['x*log(x)', '-1', true]);
    const r = integratePrimitive(P('x'), P('t'), de);
    expect([E(r[0]), E(r[1]), r[2]]).toEqual(['0', 'Integral(x/log(x), x)', false]);
    const de2 = new DifferentialExtension({ D: [P('1', x), P('1/x', t0)], Tfuncs: [lam('log(i)')] });
    const r2 = integratePrimitive(P('x**2*t0**3 + (3*x**2 + x)*t0**2 + (3*x**2 + 2*x)*t0 + x**2 + x', t0), P('x**2*t0**4 + 4*x**2*t0**3 + 6*x**2*t0**2 + 4*x**2*t0 + x**2', t0), de2);
    expect([E(r2[0]), E(r2[1]), r2[2]]).toEqual(['-1/(log(x) + 1)', 'Integral(1/(log(x) + 1), x)', false]);
  });
});

describe('risch_integrate', () => {
  const R = (e: string, v: Sym = x): string => E(rischIntegrate(parse(e), v));
  it('SymPy test_risch_integrate', () => {
    expect(R('t0*exp(x)')).toBe('t0*exp(x)');
    expect(E(rischIntegrate(parse('sin(x)'), x, { rewriteComplex: true }))).toBe('-exp(I*x)/2 - exp(-I*x)/2');
    // SymPy prints the same sum as exp(x**2)/(x**2 + 1) + Integral(exp(-x**2), x)
    expect(R('(1 + 2*x**2 + x**4 + 2*x**3*exp(2*x**2))/(x**4*exp(x**2) + 2*x**2*exp(x**2) + exp(x**2))')).toBe('Integral(exp(-x**2), x) + exp(x**2)/(x**2 + 1)');
    expect(R('0')).toBe('0');
    expect(R('log(x**x)')).toBe('x**2*log(x)/2 - x**2/4');
    // SymPy prints x*log(x**y) - x*y
    expect(R('log(x**y)')).toBe('-x*y + x*log(x**y)');
    expect(R('log(sqrt(x))')).toBe('x*log(sqrt(x)) - x/2');
  });
  it('the doctests and other integrals', () => {
    expect(R('exp(x)/(1 + exp(2*x))')).toBe('RootSum(4*_z**2 + 1, Lambda(_i, _i*log(2*_i + exp(x))))');
    expect(R('log(x)/x**3')).toBe('-log(x)/(2*x**2) - 1/(4*x**2)');
    expect(R('exp(2*x)*x**2')).toBe('(2*x**2 - 2*x + 1)*exp(2*x)/4');
    expect(R('1/(x*log(x))')).toBe('log(log(x))');
    expect(R('log(x)/(x*(log(x) + 1))')).toBe('log(x) - log(log(x) + 1)');
    expect(R('x**2*log(x)')).toBe('x**3*log(x)/3 - x**3/9');
  });
  it('nonelementary integrals (SymPy test_NonElementaryIntegral, test_xtothex)', () => {
    const r = rischIntegrate(parse('x**x'), x);
    expect([r instanceof NonElementaryIntegral, E(r)]).toEqual([true, 'Integral(x**x, x)']);
    expect(rischIntegrate(parse('exp(x**2)'), x)).toBeInstanceOf(NonElementaryIntegral);
    expect(rischIntegrate(parse('x**x*log(x)'), x)).toBeInstanceOf(Integral);
    const [res, ni] = rischIntegrate(parse('exp(x**2) + exp(x)'), x, { separateIntegral: true });
    expect([E(res), E(ni)]).toEqual(['0', 'Integral(exp(x) + exp(x**2), x)']);
    expect(rischIntegrate(parse('exp(x)'), x, { separateIntegral: true }).map(E)).toEqual(['exp(x)', '0']);
  });
  it('with a given extension and with the log case first', () => {
    const de = new DifferentialExtension(parse('exp(x)*log(x)'), x, { handleFirst: 'exp' });
    // SymPy 1.14 does not finish on this one (it is exp(x)*log(x) - Ei(x))
    expect(E(rischIntegrate(parse('exp(x)*log(x)'), x, { extension: de }))).toBe('exp(x)*log(x) + Integral(-exp(x)/x, x)');
    // the log case first: no elementary part (SymPy: Integral(exp(x)*log(x), x))
    expect(E(rischIntegrate(parse('exp(x)*log(x)'), x))).toBe('Integral(exp(x)*log(x), x)');
  });
  it('raises for the cases it does not support', () => {
    expect(() => rischIntegrate(parse('sqrt(x)'), x)).toThrow(NotImplementedError);
    const tan = new DifferentialExtension({ D: [P('1', x), P('t**2 + 1')] });
    tan.fa = P('t');
    tan.fd = P('1');
    expect(() => rischIntegrate(parse('tan(x)'), x, { extension: tan })).toThrow(NotImplementedError);
  });
  it('keeps unevaluated rational functions of the base case', () => {
    expect(R('1/(x**3 + x + 1)')).toBe('Integral(1/(x**3 + x + 1), x)');
  });
});

void [t1, a, b, log, symbols];

describe('more extensions and integrals', () => {
  it('powers whose base is a derivative of existing logarithms (SymPy agrees)', () => {
    expect(attrs(DEof('x**log(x)')).slice(0, 4)).toEqual(['t1', '1', '1|x, 1/x|t0, 2*t0*t1/x|t1', 'x,t0,t1']);
    expect(attrs(DEof('(exp(x) + 1)**x')).slice(0, 4)).toEqual(['t2', '1', '1|x, t0|t0, t0/(t0 + 1)|t1, t2*(t0*t1 + t0*x + t1)/(t0 + 1)|t2', 'x,t0,t1,t2']);
    expect(attrs(DEof('log(x + 1)*log(x + 2)')).slice(2, 4)).toEqual(['1|x, 1/(x + 1)|t0, 1/(x + 2)|t1', 'x,t0,t1']);
  });
  it('nonelementary results (SymPy agrees)', () => {
    const R = (e: string): string => E(rischIntegrate(parse(e), x));
    expect(R('log(x)/(x + 1)')).toBe('Integral(log(x)/(x + 1), x)');
    expect(R('x**log(x)')).toBe('Integral(exp(log(x)**2), x)');
    expect(R('(exp(x) + 1)**x')).toBe('Integral(exp(x*log(exp(x) + 1)), x)');
    expect(R('log(x + 1)*log(x + 2)')).toBe('(x*log(x + 1) - x + log(x + 1))*log(x + 2) + Integral((-x*log(x + 1) + x - log(x + 1))/(x + 2), x)');
  });
  it('a Laurent polynomial with only negative powers', () => {
    const de = new DifferentialExtension({ D: [P('1', x), P('t')], Tfuncs: [Lambda(i, parse('exp(i)', { symbols: [i] }))] });
    expect(integrateHyperexponential(P('1'), P('t'), de).map((v) => (typeof v === 'boolean' ? v : E(v)))).toEqual(['-exp(-x)', '0', true]);
  });
});

describe('algebraic exponentials', () => {
  it('exp(log(x)/2) is an algebraic extension (SymPy, with evaluate=False)', () => {
    // symjs evaluates exp(log(x)/2) to sqrt(x); the unevaluated power reaches the structure theorem
    expect(() => new DifferentialExtension(new Pow(S.E, mul(Rational.of(1, 2), log(x))), x)).toThrow('Cannot integrate over algebraic extensions.');
  });
});
