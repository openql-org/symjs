// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/ratsimpmodprime.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { diff, parse, ratsimpmodprime, sstr, symbol, symbols } from '../../src';
import type { Expr } from '../../src';
import { particularSolution } from '../../src/simplify/ratsimpmodprime';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};
const [x, y] = [symbol('x'), symbol('y')];

describe('ratsimpmodprime and further ODE systems', () => {
  it('match SymPy (and correct where SymPy is not)', async () => {
    const { ratsimpmodprime, dsolve, sin: s, simplify: simp, sub } = await import('../../src');
    const [x, y, t] = symbols('x y t');
    const P = (e: string) => parse(e, { symbols: { x, y, t } } as never);
    expect(sstr(ratsimpmodprime(P('(x + y**5 + y)/(x - y)'), [P('x*y**5 - x - y')], [x, y], { order: 'lex' }))).toBe('(-x**2 - x*y - x - y)/(-x**2 + x*y)');
    expect(sstr(ratsimpmodprime(P('(x**2+y**2)/(x+y)'), [P('x**2+y**2-1')], [x, y]))).toBe('1/(x + y)');
    const lin = dsolve(['Eq(Derivative(x(t), t), 12*t*x(t) + 8*y(t))', 'Eq(Derivative(y(t), t), 21*x(t) + 7*t*y(t))'].map(P)) as never as { rhs: never }[];
    expect(sstr((lin[0] as never))).toBe('Eq(x(t), C1*x0(t) + C2*x0(t)*Integral(8*exp(Integral(7*t, t))*exp(Integral(12*t, t))/x0(t)**2, t))');
    // SymPy's answer to this system does not satisfy it (checkodesol False); ours does
    const [xs, ys] = (dsolve(['Eq(Derivative(x(t), t), x(t)*y(t)*sin(t))', 'Eq(Derivative(y(t), t), y(t)**2*sin(t))'].map(P)) as never as { rhs: never }[]).map((e) => e.rhs);
    expect(sstr(simp(sub(diff(xs!, t), parse('X*Y*sin(t)', { symbols: { X: xs, Y: ys, t } } as never))))).toBe('0');
    expect(sstr(simp(sub(diff(ys!, t), parse('Y**2*sin(t)', { symbols: { Y: ys, t } } as never))))).toBe('0');
    void s;
  });
});

describe("ratsimpmodprime, gammasimp, signsimp, cancel, ratsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(PA('(x + y**2 - 2)/(x + y**2 - y - 1)'), [PA('x*y - 1')], [x, y], { order: 'lex', quick: true }), "(-x + y + 1)/(-x + y)"],
    ["ratsimpmodprime(P('(5*x**3 + 21*x**2 + 4*x*y + 23*x + 12*y + 15)/(7*x**3 - y*x**2 + 31*x**2 + 2*x*y + 15*y + 37*x + 21)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(PA('(5*x**3 + 21*x**2 + 4*x*y + 23*x + 12*y + 15)/(7*x**3 - y*x**2 + 31*x**2 + 2*x*y + 15*y + 37*x + 21)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'lex', quick: true }), "(-5*x + 5*y + 1)/(-6*x + 8*y)"],
    ["ratsimpmodprime(P('(x*y - x - 2*y + 4)/(x + y**2 - 2*y)'), [P('x - 2'), P('y - 3')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(PA('(x*y - x - 2*y + 4)/(x + y**2 - 2*y)'), [PA('x - 2'), PA('y - 3')], [x, y], { order: 'lex', quick: true }), "2/5"],
    ["ratsimpmodprime(P('x'), [P('y - 2*x')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(PA('x'), [PA('y - 2*x')], [x, y], { order: 'lex', quick: true }), "y/2"],
    ["ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(PA('(x + y**2 - 2)/(x + y**2 - y - 1)'), [PA('x*y - 1')], [x, y], { order: 'grevlex', quick: false }), "(-x + y + 1)/(-x + y)"],
    ["ratsimpmodprime(P('(x**2 + y**2)/(x + y)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(PA('(x**2 + y**2)/(x + y)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false }), "1/(x + y)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x**3 + y)/(x*y + 1)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(-x*y**2 + x + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(PA('(x**3 + y)/(x*y + 1)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false }), "(-x*y**2 + x + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x + y)**2/(x**2 - y**2)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x + y)**2/(x**2 - y**2)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(x + y)/(x - y)"],
    ["ratsimpmodprime(P('1/(x + y)'), [P('x**2 - y**2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('1/(x + y)'), [PA('x**2 - y**2')], [x, y], { order: 'grevlex', quick: true }), "1/(x + y)"],
    ["ratsimpmodprime(P('(x + 1)/(y - 1)'), [P('x**2*y**2 - 2*x*y + 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x + 1)/(y - 1)'), [PA('x**2*y**2 - 2*x*y + 1')], [x, y], { order: 'grevlex', quick: true }), "(x + 1)/(y - 1)"],
    ["ratsimpmodprime(P('x/(2*(y + 1))'), [P('x*y - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('x/(2*(y + 1))'), [PA('x*y - 1')], [x, y], { order: 'grevlex', quick: true }), "x/(2*y + 2)"],
    ["ratsimpmodprime(P('(x/2 + y)/(x*y + 3)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x/2 + y)/(x*y + 3)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(x + 2*y)/(2*x*y + 6)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x**3 + y)/(x*y + 1)'), [PA('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: true }), "(-x*y**2 + x/2 + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(PA('(x**3 + y)/(x*y + 1)'), [PA('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: false }), "(-x*y**2 + x/2 + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1/3')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x + y**2 - 2)/(x + y**2 - y - 1)'), [PA('x*y - 1/3')], [x, y], { order: 'grevlex', quick: true }), "(x + y**2 - 2)/(x + y**2 - y - 1)"],
    ["ratsimpmodprime(P('(x/3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('(x/3 + y)/(x*y + 1)'), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(x + 3*y)/(3*x*y + 3)"],
    ["ratsimpmodprime(P('y/(-x)'), [P('x - y**2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('y/(-x)'), [PA('x - y**2')], [x, y], { order: 'grevlex', quick: true }), "-1/y"],
    ["ratsimpmodprime(P('y/(-x)'), [P('x - y**2')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(PA('y/(-x)'), [PA('x - y**2')], [x, y], { order: 'grevlex', quick: false }), "-1/y"],
    ["ratsimpmodprime(P('3*y/(x - y**2)'), [P('x*y - 2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(PA('3*y/(x - y**2)'), [PA('x*y - 2')], [x, y], { order: 'grevlex', quick: true }), "-6/(-x**2 + 2*y)"],
    ["ratsimpmodprime(P('3*y/(x - y**2)'), [P('x*y - 2')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(PA('3*y/(x - y**2)'), [PA('x*y - 2')], [x, y], { order: 'grevlex', quick: false }), "-6/(-x**2 + 2*y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('ratsimpmodprime (cov2): an ideal that is not prime', () => {
  // SymPy 1.14 raises ValueError('Ideal not prime?')
  it.each(['(x + y)/(x - y)', 'x/(x - y)'])('%s modulo x**2 - y**2', (src) => {
    expect(() => ratsimpmodprime(PA(src), [PA('x**2 - y**2')], [x, y])).toThrow(/ideal not prime/);
  });
});

describe('ratsimpmodprime quick=False: the minimal solution search', () => {
  it('finds the solution with the fewest terms (SymPy trigsimp_groebner test, sin/cos replaced by symbols)', () => {
    const [a, b, c, d] = symbols('a b c d');
    const P = (e: string) => parse(e, { symbols: { a, b, c, d } } as never);
    const ex = P('(4*d*b + 12*d + 5*b**3 + 21*b**2 + 23*b + 15)/(-d*b**2 + 2*d*b + 15*d + 7*b**3 + 31*b**2 + 37*b + 21)');
    const G = ['a**2 + c**2 - 1', '-d*c - d + a*b', 'd*a + b*c - b', '2*b**2 - c - 1', '2*d*b - a', '2*d**2 + c - 1'].map(P);
    expect(sstr(ratsimpmodprime(ex, G, [a, b, c, d], { order: 'grlex', quick: false }))).toBe('(-5*b + 5*d + 1)/(-6*b + 8*d)');
    expect(sstr(ratsimpmodprime(ex, G, [a, b, c, d], { order: 'grlex' }))).toBe('(12*b + 5*c + 8*d + 15)/(-a + 20*b + 7*c + 10*d + 21)');
  });
  it('agrees with the quick search where that is already minimal', () => {
    const cases: [string, string][] = [
      ['(x**4 + y**3 + x)/(x**2*y + x + y)', '(x + y**4 + y**3 - 2*y**2 + 1)/(x - y**3 + 2*y)'],
      ['(x**3 + 2*x*y + 1)/(x**2 + y + 2)', '(-x*y**2 + 2*x*y + x + 1)/(-y**2 + y + 3)'],
    ];
    for (const [e, r] of cases) expect(sstr(ratsimpmodprime(PA(e), [PA('x**2 + y**2 - 1')], [x, y], { order: 'grlex', quick: false }))).toBe(r);
  });
});

describe('minsolve_linear_system', () => {
  it('quick=False tries the subsets of fewer nonzero variables (SymPy minsolve_linear_system)', () => {
    const vs = symbols('a b c d e');
    const P = (e: string) => parse(e, { symbols: Object.fromEntries(vs.map((v) => [v.name, v])) } as never);
    const eqs = [P('-b + 2*c'), P('2*b - c + d - e')];
    // SymPy: {e: 0, d: 1, b: -2/3, c: -1/3} and {d: 1, a: 0, b: 0, c: 0, e: 1}
    // (the solution is keyed by the variables' keys)
    const byName = (m: Map<string, Expr>) => new Map([...m].map(([k, v]) => [vs.find((u) => u.key === k)?.name, v]));
    expect(showMap(byName(particularSolution(eqs, vs, true)))).toBe('{b: -2/3, c: -1/3, d: 1, e: 0}');
    expect(showMap(byName(particularSolution(eqs, vs, false)))).toBe('{a: 0, b: 0, c: 0, d: 1, e: 1}');
  });
});
