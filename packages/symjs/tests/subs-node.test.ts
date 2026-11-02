// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Derivative, Function, Subs, diff, doit, freeSymbols, latex, parse, sstr, symbols } from '../src';

const [x, y, z] = symbols('x y z');
const f = Function('f');

describe('Subs (SymPy Subs)', () => {
  it('derivative at a point', () => {
    const s = diff(f(x), x).subs(x, 0 as never);
    expect(s).toBeInstanceOf(Subs);
    expect(sstr(s)).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(latex(s)).toBe('\\left. \\frac{d}{d x} f{\\left(x \\right)} \\right|_{\\substack{ x=0 }}');
    expect(freeSymbols(s).size).toBe(0);
    expect(sstr(diff(s, x))).toBe('0');
    expect(sstr(doit(s))).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(sstr(diff(f(x), x).subs(x, y))).toBe('Derivative(f(y), y)');
    expect(sstr(Derivative(f(x, y), x).subs(x, parse('y + 1')))).toBe('Subs(Derivative(f(x, y), x), x, y + 1)');
  });

  it('several variables, substitution and evaluation', () => {
    const s = Subs(parse('f(x)*sin(y) + z'), [x, y], [0, 1]);
    expect(sstr(s)).toBe('Subs(z + f(x)*sin(y), (x, y), (0, 1))');
    expect(latex(s)).toBe('\\left. z + f{\\left(x \\right)} \\sin{\\left(y \\right)} \\right|_{\\substack{ x=0\\\\ y=1 }}');
    expect([...freeSymbols(s)].map(String)).toEqual(['z']);
    expect(sstr(s.subs(x, 3 as never))).toBe(sstr(s));
    expect(sstr(s.subs(z, 3 as never))).toBe('Subs(f(x)*sin(y) + 3, (x, y), (0, 1))');
    expect(sstr(doit(s))).toBe('z + f(0)*sin(1)');
    expect(sstr(diff(Subs(parse('x**2'), x, parse('y + 1')), y))).toBe('2*y + 2');
    expect(sstr(diff(Subs(f(x), x, y), y))).toBe('Derivative(f(y), y)');
  });
});

import { combsimp, gammasimp } from '../src';

describe('gammasimp and combsimp', () => {
  const n = symbols('n', { integer: true })[0];
  it('combine integer shifts', () => {
    expect(sstr(gammasimp(parse('gamma(x + 3)/gamma(x + 1)')))).toBe('(x + 1)*(x + 2)');
    expect(sstr(gammasimp(parse('gamma(x + 1)/gamma(x)/x')))).toBe('1');
    expect(sstr(combsimp(parse('factorial(n + 2)/factorial(n)', { symbols: { n } } as never)))).toBe('(n + 1)*(n + 2)');
    expect(sstr(combsimp(parse('binomial(n + 1, 2)/binomial(n, 2)', { symbols: { n } } as never)))).toBe('(n + 1)/(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)/factorial(n - 3)', { symbols: { n } } as never)))).toBe('n*(n - 2)*(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)*factorial(n + 1)', { symbols: { n } } as never)))).toBe('factorial(n)*factorial(n + 1)');
  });
});

describe('parser and assumptions', () => {
  it('repeating decimals', () => {
    expect(['.[3]', '1.2[3]', '0.[142857]', '-1.[3]'].map((s) => sstr(parse(s)))).toEqual(['1/3', '37/30', '1/7', '-4/3']);
  });
  it('zero=False splits powers', async () => {
    const { expandPowerExp, Symbol: Sym } = await import('../src');
    const xn = new Sym('x', { zero: false });
    expect(sstr(expandPowerExp(parse('x**(y + 2)', { symbols: { x: xn } } as never)))).toBe('x**2*x**y');
    expect(sstr(expandPowerExp(parse('x**(y + 2)')))).toBe('x**(y + 2)');
  });
});

describe('factor over GF(p)', () => {
  it('matches SymPy factor(f, modulus=p)', async () => {
    const { factor } = await import('../src');
    const cases: [string, number, string][] = [
      ['x**2 + 1', 2, '(x + 1)**2'],
      ['x**4 + 1', 3, '(x**2 - x - 1)*(x**2 + x - 1)'],
      ['x**6 - 1', 7, '(x - 3)*(x - 2)*(x - 1)*(x + 1)*(x + 2)*(x + 3)'],
      ['x**5 + x + 1', 2, '(x**2 + x + 1)*(x**3 + x**2 + 1)'],
      ['3*x**3 + 2*x + 1', 5, '-2*(x**3 - x + 2)'],
      ['x**8 + x**4', 2, 'x**4*(x + 1)**4'],
      ['x**9 - x', 3, 'x*(x - 1)*(x + 1)*(x**2 + 1)*(x**2 - x - 1)*(x**2 + x - 1)'],
    ];
    for (const [f, p, want] of cases) expect(sstr(factor(parse(f), { modulus: p }))).toBe(want);
  });
});

describe('solve with radicals', () => {
  it('isolates one radical and checks the candidates', async () => {
    const { solve } = await import('../src');
    const x = symbols('x')[0];
    const show = (s: string, opts = {}) => solve(parse(s), x, opts).map((e) => sstr(e));
    expect(show('sqrt(x + 1) - x + 1')).toEqual(['3']);
    expect(show('x**(2/3) - 4')).toEqual(['8']);
    expect(show('sqrt(x) + 1')).toEqual([]);
    expect(show('-x + (x**3 - 3*x**2)**(1/3) + 1')).toEqual([]);
    expect(show('-x + (x**3 - 3*x**2)**(1/3) + 1', { check: false })).toEqual(['1/3']);
  });
});

describe('roots of polynomials with algebraic coefficients', () => {
  it('uses the norm polynomial like SymPy', async () => {
    const { Poly } = await import('../src');
    const x = symbols('x')[0];
    expect(Poly.from(parse('x**2 + I*x - 1'), [x]).allRoots().map((e) => sstr(e))).toEqual(['CRootOf(x**4 - x**2 + 1, 0)', 'CRootOf(x**4 - x**2 + 1, 2)']);
    expect(Poly.from(parse('sqrt(2)*x**3 + x**2 - 1'), [x]).realRoots().map((e) => sstr(e))).toEqual(['sqrt(2)/2']);
  });
});

describe('Poly lift, eject and inject', () => {
  it('match SymPy', async () => {
    const { Poly, expand } = await import('../src');
    const [x, y] = symbols('x y');
    const show = (p: { asExpr(): unknown; gens: readonly unknown[]; domain: string }) => `${sstr(expand(p.asExpr() as never))} | ${p.gens.map((g) => sstr(g as never)).join(',')} | ${p.domain}`;
    expect(show(Poly.from(parse('x**2 + I*x - 1'), [x]).lift())).toBe('x**4 - x**2 + 1 | x | ZZ');
    const f = Poly.from(parse('x**2*y + x*y**3 + x*y + 1'), [x, y]);
    expect(show(f.eject(x))).toBe('x**2*y + x*y**3 + x*y + 1 | y | ZZ[x]');
    expect(show(f.eject(x).inject())).toBe('x**2*y + x*y**3 + x*y + 1 | y,x | ZZ');
    expect(show(f.eject(x).inject({ front: true }))).toBe('x**2*y + x*y**3 + x*y + 1 | x,y | ZZ');
  });
});

describe('multiple integrals', () => {
  it('print, differentiate and evaluate like SymPy', async () => {
    const { Integral, Rational, add, mul, pow, subs } = await import('../src');
    const [x, y] = symbols('x y');
    const i = new Integral([new Integral([add(x, y), y]), y, Rational.of(1), x]);
    expect(sstr(i)).toBe('Integral(x + y, y, (y, 1, x))');
    expect(latex(i)).toBe('\\int\\limits_{1}^{x}\\int \\left(x + y\\right)\\, dy\\, dy');
    expect(sstr(diff(i, x))).toBe('Integral(x + y, (y, x)) + Integral(1, y, (y, 1, x))');
    expect(sstr(diff(i, y))).toBe('0');
    expect(sstr(doit(i))).toBe('2*x**3/3 - x/2 - 1/6');
    expect(sstr(new Integral([new Integral([mul(x, y), x]), y]))).toBe('Integral(x*y, x, y)');
    expect(sstr(subs(new Integral([pow(x, 2), x]), [[x, Rational.of(1)]]))).toBe('Integral(x**2, (x, 1))');
  });
});

describe('powdenest and finite differences', () => {
  it('match SymPy', async () => {
    const { powdenest, asFiniteDifference, Derivative: D } = await import('../src');
    const [x, h] = symbols('x h');
    expect(sstr(powdenest(parse('(x**(2*i)*y**(4*i))**z'), { force: true }))).toBe('(x*y**2)**(2*i*z)');
    const f = Function('f');
    const dx = Function('dx');
    expect(sstr(asFiniteDifference(D(f(x), x) as never, dx(x), parse('x - h', { symbols: { x, h } } as never)))).toBe(
      '-f(-h + x - dx(-h + x)/2)/dx(-h + x) + f(-h + x + dx(-h + x)/2)/dx(-h + x)',
    );
  });
});
