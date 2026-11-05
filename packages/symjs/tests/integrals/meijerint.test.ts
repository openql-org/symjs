// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/meijerint.ts.
// Definite integrals by Meijer G-functions (meijerint_definite) and the internal helpers. Expected values are
// those of SymPy 1.14's meijerint_definite; where symjs writes the value in another form, SymPy's result is
// quoted and the value is checked against the integral computed numerically (mpmath).

import { describe, expect, it } from 'vitest';
import { DiracDelta, Eq, Gt, Heaviside, I, Lt, Rational, Sym, abs, add, and, arg, exp, expPolar, hyper, meijerg, mul, parse, pi, pow, sqrt, sstr, tan, type Expr } from '../../src';
import { CoeffExpError, condsimp, findSplittingPoints, getCoeffExp, liftPolar, laplaceBesselProduct, meijerintDefinite, meijerintInversion, rewriteSingle, splitMul, unpolarifyExponents } from '../../src/integrals/meijerint';

const R = (p: number, q: number): Expr => Rational.of(BigInt(p), BigInt(q));

const [x, a, b, k, y] = [new Sym('x'), new Sym('a'), new Sym('b'), new Sym('k'), new Sym('y')];
const P = (q: string): Expr => parse(q.replace(/S\((\d+)\)\/(\d+)/g, '($1/$2)'), { symbols: [x, a, b, k, y], locals: { Heaviside, DiracDelta, G0: (z: Expr) => meijerg([], [], [0], [], z) } });
const run = (f: string, lo: string, hi: string): string[] | undefined => meijerintDefinite(P(f), x, P(lo), P(hi))?.map((e) => sstr(e));

describe('Laplace integrals of Bessel products', () => {
  it('handles unequal real frequencies and a constant multiplier', () => {
    expect(laplaceBesselProduct(P('3*exp(-2*x)*besselj(0,x)*besselj(0,2*x)'), x)?.map(sstr)).toEqual(['6*sqrt(5)*elliptic_k(-8/5)/(5*pi)', 'True']);
    expect(String(laplaceBesselProduct(P('exp(-a*x)*besselj(0,x)**2'), x)?.[1])).toBe('re(a) > 0');
  });
  it.each([
    'besselj(0,x)',
    'exp(-x)*besselj(0,x**2)**2',
    'exp(-x)*besselj(0,(1+I)*x)**2',
    'exp(-3*x)*besseli(0,x)**2',
    'exp(x)*besselj(0,x)**2',
    'exp(-x/2)*besseli(0,x)',
  ])('does not apply a formula outside its convergence domain: %s', (e) => {
    expect(laplaceBesselProduct(P(e), x)).toBeUndefined();
  });
});

describe('meijerint_definite: the results of SymPy', () => {
  const cases: [string, string, string, string[] | 'None'][] = [
    ["exp(-x**2)", "0", "oo", ["sqrt(pi)/2", "True"]],
    ["x**a*exp(-x)", "0", "oo", ["gamma(a + 1)", "re(a) > -1"]],
    ["sin(x)/x", "0", "oo", ["pi/2", "True"]],
    ["besselj(0,x)*exp(-x)", "0", "oo", ["sqrt(2)/2", "True"]],
    // SymPy writes elliptic_k(4*exp_polar(I*pi)); the negative argument is on the same branch.
    ["besselj(0,x)**2*exp(-x)", "0", "oo", ["2*elliptic_k(-4)/pi", "True"]],
    ["besseli(0,x)*exp(-2*x)", "0", "oo", ["sqrt(3)/3", "True"]],
    ["exp(-x)*sin(x)", "0", "oo", ["1/2", "True"]],
    ["exp(-x**2)*cos(x)", "0", "oo", ["sqrt(pi)*exp(-1/4)/2", "True"]],
    ["exp(-x)", "-oo", "0", "None"],
    ["exp(-x**2)", "-oo", "oo", ["sqrt(pi)", "True"]],
    ["exp(-abs(x))", "-oo", "oo", ["2", "True"]],
    ["x**2*exp(-x)", "1", "oo", ["5*exp(-1)", "True"]],
    ["exp(-x)", "1", "2", ["(1 - exp(-1))*exp(-1)", "True"]],
    ["exp(-x)", "0", "1", ["1 - exp(-1)", "True"]],
    ["sin(x)", "0", "pi", ["2", "True"]],
    ["exp(x)", "0", "oo", "None"],
    ["1/(x+1)**2", "0", "oo", ["1", "True"]],
    ["1/(x**2+1)", "0", "oo", ["pi/2", "True"]],
    ["x/(x**2+1)**2", "0", "oo", ["1/2", "True"]],
    ["log(x)*exp(-x)", "0", "oo", ["-EulerGamma", "True"]],
    ["log(x+1)/x**2", "0", "oo", "None"],
    ["Heaviside(x-1)*exp(-x)", "0", "oo", ["exp(-1)", "True"]],
    ["Heaviside(1-x)*x", "0", "oo", ["1/2", "True"]],
    ["besselj(1,x)/x", "0", "oo", ["1", "True"]],
    ["erfc(x)", "0", "oo", ["1/sqrt(pi)", "True"]],
    ["Si(x)*exp(-x)", "0", "oo", ["pi/4", "True"]],
    ["Ci(x)*exp(-x)", "0", "oo", ["-log(2)/2", "True"]],
    ["Ei(-x)*exp(-x)", "0", "oo", "None"],
    ["expint(2,x)", "0", "oo", ["1/2", "True"]],
    ["besselk(0,x)", "0", "oo", ["pi/2", "True"]],
    ["bessely(0,x)*exp(-x)", "0", "oo", ["-sqrt(2)*log(1 + sqrt(2))/pi", "True"]],
    ["sinh(x)*exp(-2*x)", "0", "oo", ["1/3", "True"]],
    ["cosh(x)*exp(-2*x)", "0", "oo", ["2/3", "True"]],
    ["erfi(x)*exp(-x**2*2)", "0", "oo", ["sqrt(2)*atanh(sqrt(2)/2)/(2*sqrt(pi))", "True"]],
    ["Chi(x)*exp(-2*x)", "0", "oo", ["-pi*(log(3/4)/(2*pi) + log(4)/(2*pi))/2", "True"]],
    ["sinc(x)", "0", "oo", ["pi/2", "True"]],
    ["abs(x-1)**(-S(1)/2)*exp(-x)", "0", "oo", ["sqrt(2)*sqrt(pi)*(pi*exp(-1)/(gamma(1/4)*gamma(3/4)) + I*pi*exp(-1)*erf(I)/(gamma(-1/4)*gamma(5/4)))", "True"]],
    ["log(x)**2*exp(-x)", "0", "oo", ["EulerGamma**2 + pi**2/6", "True"]],
    ["log(x)*Heaviside(1-x)", "0", "oo", ["-1", "True"]],
    ["exp(-x)*G0(x)", "0", "oo", ["1/2", "True"]],
    ["x**(S(1)/3)*exp(-x**(S(2)/3))", "0", "oo", ["3/2", "True"]],
    ["cos(k*x)/(x**2+b**2)", "0", "oo", ["sqrt(pi)*(-sqrt(pi)*sinh(b*k) + sqrt(pi)*cosh(b*k))/(2*b)", "Eq(Abs(arg(k)), 0) & (Abs(arg(b)) < pi/2)"]],
    ["x*exp(-x**2)*sin(x)", "-oo", "oo", ["sqrt(pi)*exp(-1/4)/2", "True"]],
    ["DiracDelta(x)", "0", "oo", "None"],
    ["exp(-x)*x**y", "0", "oo", ["gamma(y + 1)", "re(y) > -1"]],
    ["exp(-x**2)", "2", "2", ["0", "True"]],
    ["exp(-x**2)", "oo", "0", ["-sqrt(pi)/2", "True"]],
  ];
  it.each(cases)('%s over (%s, %s)', (f, lo, hi, want) => expect(run(f, lo, hi) ?? 'None').toEqual(want));
});

describe('meijerint_definite: the same values in other forms than SymPy', () => {
  // (the value of the G-function of exp(-x)/(x + 1) at 1, which symjs does not expand, is not checked)
  const cases: [string, string, string, string[], number | null][] = [
    // SymPy: exp(1/4)*erfc(1/2)
    ["erf(x)*exp(-x)", "0", "oo", ["(-pi*exp(1/4)*erf(1/2) + pi*exp(1/4))/pi", "True"], 0.615690344192926],
    // SymPy: ERR TimeoutError
    ["fresnels(x)*exp(-x)", "0", "oo", ["sqrt(2)*(-I*sqrt(pi)*(I*sin(1/(2*pi))*fresnels(1/pi) + I*cos(1/(2*pi))*fresnelc(1/pi))*gamma(-1/4)*gamma(1/4)/2 - sqrt(pi)*sin(1/(2*pi))*gamma(-1/4)*gamma(5/4) + sqrt(pi)*cos(1/(2*pi))*gamma(1/4)*gamma(3/4))/(4*pi**(3/2))", "True"], 0.256759485811119],
    // SymPy: ERR TimeoutError
    ["fresnelc(x)*exp(-x)", "0", "oo", ["sqrt(2)*(-sqrt(pi)*sin(1/(2*pi))*gamma(1/4)*gamma(3/4) + (-I*pi*(I*sin(1/(2*pi))*fresnels(1/pi) + I*cos(1/(2*pi))*fresnelc(1/pi))*(pi**2*(-3 + 3/pi**2) - 3 + 3*pi**2) + pi**2*(-3*cos(1/(2*pi))*fresnels(1/pi) + 3*sin(1/(2*pi))*fresnelc(1/pi)))*gamma(-3/4)*gamma(-1/4)/(8*pi**(3/2)) + sqrt(pi)*cos(1/(2*pi))*gamma(1/4)*gamma(3/4))/(4*pi**(3/2))", "True"], 0.448114895242443],
    // (SymPy's result)
    ["Shi(x)*exp(-2*x)", "0", "oo", ["acoth(2)/2", "True"], 0.274653072167027],
    // SymPy: log(-exp_polar(I*pi)) - Ei(exp_polar(I*pi)) + I*pi (symjs writes log(-exp_polar(I*pi)) = 0)
    ["log(x)*Heaviside(x-1)*exp(-x)", "0", "oo", ["-Ei(exp_polar(I*pi)) + I*pi", "True"], 0.21938393439552],
    // SymPy: (2*sqrt(3)*sqrt(pi)*gamma(-1/3)*gamma(1/3)*hyper((1/2, 1), (2/3, 4/3), -4/27)/9 + 2**(1/3)*sqrt(3)*exp(-2/27 + I*pi/3)*besseli(-1/3, 2*exp_polar(I*pi)/27)*gamma(1/6)*gamma(1/3)*gamma(2/3)**3/9 + 2*2**(2/3)*sqrt(3)*exp(-2/27 - I*pi/3)*besseli(1/3, 2*exp_polar(I*pi)/27)*gamma(-2/3)*gamma(-1/3)*gamma(5/6)*gamma(4/3)**2/9)/(4*pi**(3/2))
    ["exp(-x**2)*exp(-x**3)", "0", "oo", ["(2*sqrt(3)*sqrt(pi)*gamma(-1/3)*gamma(1/3)*hyper((1/2, 1), (2/3, 4/3), -4/27)/9 + 2**(1/3)*sqrt(3)*exp(-2/27)*exp(I*pi/3)*besseli(-1/3, 2*exp_polar(I*pi)/27)*gamma(1/6)*gamma(1/3)*gamma(2/3)**3/9 + 2*2**(2/3)*sqrt(3)*exp(-2/27)*exp(-I*pi/3)*besseli(1/3, 2*exp_polar(I*pi)/27)*gamma(-2/3)*gamma(-1/3)*gamma(5/6)*gamma(4/3)**2/9)/(4*pi**(3/2))", "True"], 0.663710570501134],
    // SymPy: E*expint(1, 1)
    ["exp(-x)/(x+1)", "0", "oo", ["meijerg(((0, 0), ()), ((0,), ()), 1)", "True"], null],
  ];
  it.each(cases)('%s over (%s, %s)', (f, lo, hi, want, value) => {
    const r = meijerintDefinite(P(f), x, P(lo), P(hi));
    expect(r?.map((e) => sstr(e))).toEqual(want);
    if (r && value !== null) expect(Math.abs(r[0].evalf(20).toNumber() - value)).toBeLessThan(1e-12);
  });
  const symbolic: [string, string, string, string[]][] = [
    // (SymPy's result)
    ["exp(-a*x)*sin(k*x)/x", "0", "oo", ["k*atan(sqrt(k**2/a**2))/(a*sqrt(k**2/a**2))", "(Eq(Abs(arg(k)), 0) & (Abs(arg(a)) < pi/2)) | (Eq(Abs(arg(k)), 0) & Eq(Abs(arg(a)), pi/2) & Ne(k**2/a**2, -1))"]],
    // SymPy: pi/(2*a) with (Abs(arg(a)) < pi/2) | (Ne(a**(-2), 0) & (Abs(arg(a)) < pi/2) & Ne(Abs(arg(a)), pi/2)), the same
    ["1/(x**2+a**2)", "0", "oo", ["pi/(2*a)", "(Abs(arg(a)) < pi/2) | (Ne(a**(-2), 0) & (Abs(arg(a)) < pi/2) & Ne(Abs(arg(a)), -pi/2) & Ne(Abs(arg(a)), pi/2))"]],
  ];
  it.each(symbolic)('%s over (%s, %s)', (f, lo, hi, want) => expect(run(f, lo, hi)).toEqual(want));
});

describe('meijerint_definite: more cases of the lookup table and the intervals', () => {
  const cases: [string, string, string, string[] | 'None'][] = [
    ["log(x)**2*Heaviside(1-x)", "0", "oo", ["2", "True"]],
    ["exp(-(x-1)**2)*Heaviside(x+1)", "-oo", "oo", ["sqrt(pi)*erf(2)/2 + sqrt(pi)/2", "True"]],
    ["Heaviside(x-2)*exp(-x)", "1", "oo", ["exp(-2)", "True"]],
    ["1/((x+1)*(x+2))", "1", "oo", ["log(3/2)", "True"]],
    ["Heaviside(x-1)/(x-1)", "0", "oo", "None"],
    ["Heaviside(x-1)*(x-1)**(S(1)/2)*exp(-x)", "0", "oo", ["sqrt(pi)*exp(-1)/2", "True"]],
    ["Heaviside(1-x)*(1-x)**(S(1)/2)", "0", "oo", ["2/3", "True"]],
    ["1/((x+1)*(x+2))", "0", "oo", ["meijerg(((0, 0), ()), ((0, 0), ()), 1/2)/2", "True"]],
    ["exp(-x**a)*sin(x)", "0", "oo", "None"],
    ["besselj(x,1)*exp(-x)", "0", "oo", "None"],
    ["Heaviside(x**x-1)*exp(-x)", "0", "oo", "None"],
    ["abs(sin(x)-1)**(-S(1)/2)*exp(-x)", "0", "oo", "None"],
    ["log(sin(x))**2*exp(-x)", "0", "oo", "None"],
    ["log(x)*Heaviside(2-x)", "0", "oo", ["-2 + 2*log(2)", "True"]],
    ["log(sin(x)+1)*exp(-x)", "0", "oo", "None"],
    ["tan(x)*exp(-x)", "0", "oo", "None"],
    ["polygamma(2,x)*exp(-x)", "0", "oo", "None"],
    ["exp(-x)+x**2", "0", "oo", "None"],
    ["exp(-x)", "-oo", "oo", "None"],
    ["exp(-(x-I)**2)", "-oo", "oo", ["sqrt(pi)*erfc(I)/2 + sqrt(pi)*(2 - erfc(I))/2", "True"]],
    ["sinh(x)*exp(x)", "0", "oo", "None"],
    ["exp(-x**2)*log(x)", "0", "oo", ["-sqrt(pi)*log(2)/2 - EulerGamma*sqrt(pi)/4", "True"]],
    ["x**2*exp(-x)", "1", "oo", ["5*exp(-1)", "True"]],
    ["exp(-x)*Heaviside(x-2)", "0", "oo", ["exp(-2)", "True"]],
    ["exp(-x-1)", "-oo", "-1", "None"],
  ];
  it.each(cases)('%s over (%s, %s)', (f, lo, hi, want) => expect(run(f, lo, hi) ?? 'None').toEqual(want));
  const others: [string, string, string, string[] | 'None'][] = [
    // SymPy: meijerg(((0, 1/2, 1/2), (1,)), ((), ()), 16) (the same G-function (the order of the parameters an))
    ["sin(1/x)*exp(-x)", "0", "oo", ["meijerg(((1/2, 0, 1/2), (1,)), ((), ()), 16)", "True"]],
    // SymPy: meijerg(((1/2, 1/2, 1), (1/2,)), ((), ()), 16)/sqrt(pi) (the same value, 0.0643107738265933 (mpmath))
    ["exp(-1/x)*besselj(0,x)", "0", "oo", ["meijerg(((), ()), ((0, -1/2, 0), (0,)), 1/16)/(4*sqrt(pi))", "True"]],
    // SymPy: ERR TypeError (SymPy raises TypeError)
    ["exp(x)", "oo", "0", "None"],
    // SymPy: E*(-log(2) + log(-2*exp_polar(I*pi)) - Ei(2*exp_polar(I*pi)) + I*pi) (the same value:
    // log(-2*exp_polar(I*pi)) + I*pi = log(2*exp_polar(I*pi)) = log(2) + I*pi)
    ["exp(-x)/(x+1)", "1", "oo", ["E*(-log(2) - Ei(2*exp_polar(I*pi)) + log(2*exp_polar(I*pi)))", "True"]],
    // SymPy: 4*2**(y - 2)*gamma(y/4 + 7/4)*gamma(y/2 + 1)*gamma(y/2 + 3/2)/(gamma(3/4 - y/4)*gamma(y/2 + 5/2)) (the same function)
    ["exp(-x)*x**y*sin(x)", "0", "oo", ["2*(1/2)**(1 - y)*gamma(y/4 + 7/4)*gamma(y/2 + 1)*gamma(y/2 + 3/2)/(gamma(3/4 - y/4)*gamma(y/2 + 5/2))", "(re(y) > -3) & (re(y) > -2)"]],
  ];
  it.each(others)('%s over (%s, %s)', (f, lo, hi, want) => expect(run(f, lo, hi) ?? 'None').toEqual(want));
});

describe('meijerint_definite: integrals symjs does not do', () => {
  const cases: [string, string, string][] = [
    // SymPy: None
    ['log(sin(x))**2', '0', 'oo'],
    ['log(sin(x))*Heaviside(1-x)', '0', 'oo'],
  ];
  it.each(cases)('%s over (%s, %s)', (f, lo, hi) => expect(run(f, lo, hi)).toBeUndefined());
});

describe('helpers', () => {
  it('getCoeffExp and its error', () => {
    expect(getCoeffExp(P('3*x**2'), x).map(sstr)).toEqual(['3', '2']);
    expect(() => getCoeffExp(P('x + 1'), x)).toThrow(CoeffExpError);
  });
  it('findSplittingPoints', () => {
    expect(findSplittingPoints(P('sin(x + 3)*x'), x).map(sstr).sort()).toEqual(['-3', '0']);
    // a sum whose terms in x cancel in the expansion is not linear; its terms give the points
    expect(findSplittingPoints(add(pow(add(x, 1), 2), mul(-1, pow(x, 2)), mul(-2, x)), x).map(sstr).sort()).toEqual(['-1', '0']);
  });
  it('splitMul', () => {
    expect(splitMul(P('(3*x)**s*sin(x**2)*x'), x).map(sstr)).toEqual(['3**s', 'x*x**s', 'sin(x**2)']);
  });
  it('condsimp evaluates numeric relations and simplifies arguments', () => {
    expect(sstr(condsimp(Lt(sqrt(2), pi)))).toBe('True');
    // a numeric relation the assumptions do not decide: re(exp(I*pi/4)) = sqrt(2)/2
    expect(sstr(condsimp(Lt(parse('re(exp(I*pi/4))'), 0)))).toBe('False');
    expect(sstr(condsimp(Gt(parse('re(exp(I*pi/4))'), 0)))).toBe('True');
    // besselj(1, 5) < 0 is not decided by is_negative (SymPy does not know it finite): its value is
    expect(sstr(condsimp(Lt(parse('besselj(1, 5)'), 0)))).toBe('True');
    expect(sstr(condsimp(Gt(parse('besselj(1, 5)'), 0)))).toBe('False');
    // complex and unevaluable numbers stay
    expect(sstr(condsimp(Lt(add(1, I), 2)))).toBe('I < 1');
    expect(sstr(condsimp(Gt(hyper([1, 2, 3], [4], 2), 0)))).toBe('hyper((1, 2, 3), (4,), 2) > 0');
    expect(sstr(condsimp(Eq(arg(y), 0)))).toBe('y > 0');
    expect(sstr(condsimp(Lt(abs(y), 0)))).toBe('False');
    expect(sstr(condsimp(and(Gt(y, 0), Lt(y, 0))))).toBe('False');
  });
  it('rewriteSingle of G-functions', () => {
    const r = rewriteSingle(meijerg([], [], [0], [], mul(2, x)), x);
    expect(r?.[0].map((t) => t.map(sstr).join(' '))).toEqual(['1 0 meijerg(((), ()), ((0,), ()), 2*x)']);
    expect(rewriteSingle(meijerg([], [], [0], [], add(x, 1)), x)).toBeUndefined();
    expect(rewriteSingle(meijerg([], [], [0], [], 2), x)).toBeUndefined();
    expect(rewriteSingle(meijerg([], [], [0], [], pow(x, y)), x)).toBeUndefined();
  });
  it('liftPolar and unpolarifyExponents', () => {
    expect(sstr(liftPolar(mul(-1, y)))).toBe('exp_polar(I*pi)*polar_lift(y)');
    expect(sstr(unpolarifyExponents(pow(x, mul(2, expPolar(0)))))).toBe('x**2');
  });
});

describe('meijerint_inversion', () => {
  const [s, t] = [new Sym('s'), new Sym('t')];
  const P2 = (q: string): Expr => parse(q, { symbols: [s, t] });
  it('factors it does not invert', () => {
    expect(meijerintInversion(mul(Heaviside(add(s, -1)), pow(s, -1)), s, t)).toBeUndefined();
    // (SymPy: DiracDelta(t - 2); the inverse Laplace transform has a rule for it)
    expect(meijerintInversion(exp(mul(-2, s)), s, t)).toBeUndefined();
    // an advance exp(2*s) is not a Laplace transform
    expect(meijerintInversion(mul(exp(mul(2, s)), pow(s, -1)), s, t)).toBeUndefined();
    expect(meijerintInversion(tan(s), s, t)).toBeUndefined();
    expect(meijerintInversion(pow(add(pow(s, y), 1), -1), s, t)).toBeUndefined();
  });
  it('results of SymPy', () => {
    const inv = (F: Expr) => meijerintInversion(F, s, t)?.map((e) => sstr(e));
    expect(inv(P2('exp(-1/s)/s'))).toEqual(['besselj(0, 2*sqrt(t))*Heaviside(t)', 'True']);
    expect(inv(P2('exp(-sqrt(s))'))).toEqual(['exp(-1/(4*t))*Heaviside(t)/(2*sqrt(pi)*t**(3/2))', 'True']);
    expect(inv(P2('1/s**2'))).toEqual(['t*Heaviside(t)', 'True']);
    // SymPy: 1 (for its positive t)
    expect(inv(mul(meijerg([], [1], [0], [], pow(s, -1)), pow(s, -1)))).toEqual(['Heaviside(t)', 'True']);
    // SymPy: None
    expect(inv(P2('(s + 1)**(-1/2)'))).toBeUndefined();
    expect(inv(P2('exp(-1/s)/sqrt(s)'))).toBeUndefined();
    // an upper parameter exceeding a lower one by an integer: not a G-function SymPy allows
    expect(inv(meijerg([2], [], [1], [], s))).toBeUndefined();
  });
  it('a delay', () => {
    const r = meijerintInversion(mul(exp(mul(-2, s)), pow(s, R(-3, 2))), s, t);
    expect(r?.map(sstr)).toEqual(['2*sqrt(t - 2)*Heaviside(t - 2)/sqrt(pi)', 'True']);
  });
});
