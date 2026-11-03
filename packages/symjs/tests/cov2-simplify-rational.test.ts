// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { Dummy, add, cancel, collect, combsimp, gammasimp, hypersimilar, hypersimp, parse, ratsimp, mul, pow, ratsimpmodprime, signsimp, symbol } from '../src';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const P = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

const show = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${show(k)}: ${show(w)}`).sort().join(', ')}}`;
  return String(v);
};

const [x, y] = [symbol('x'), symbol('y')];

describe("ratsimpmodprime, gammasimp, signsimp, cancel, ratsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1')], [x, y], { order: 'lex', quick: true }), "(-x + y + 1)/(-x + y)"],
    ["ratsimpmodprime(P('(5*x**3 + 21*x**2 + 4*x*y + 23*x + 12*y + 15)/(7*x**3 - y*x**2 + 31*x**2 + 2*x*y + 15*y + 37*x + 21)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(P('(5*x**3 + 21*x**2 + 4*x*y + 23*x + 12*y + 15)/(7*x**3 - y*x**2 + 31*x**2 + 2*x*y + 15*y + 37*x + 21)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'lex', quick: true }), "(-5*x + 5*y + 1)/(-6*x + 8*y)"],
    ["ratsimpmodprime(P('(x*y - x - 2*y + 4)/(x + y**2 - 2*y)'), [P('x - 2'), P('y - 3')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(P('(x*y - x - 2*y + 4)/(x + y**2 - 2*y)'), [P('x - 2'), P('y - 3')], [x, y], { order: 'lex', quick: true }), "2/5"],
    ["ratsimpmodprime(P('x'), [P('y - 2*x')], [x, y], { order: 'lex', quick: true })", () => ratsimpmodprime(P('x'), [P('y - 2*x')], [x, y], { order: 'lex', quick: true }), "y/2"],
    ["ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1')], [x, y], { order: 'grevlex', quick: false }), "(-x + y + 1)/(-x + y)"],
    ["ratsimpmodprime(P('(x**2 + y**2)/(x + y)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(P('(x**2 + y**2)/(x + y)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false }), "1/(x + y)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(-x*y**2 + x + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: false }), "(-x*y**2 + x + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x + y)**2/(x**2 - y**2)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x + y)**2/(x**2 - y**2)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(x + y)/(x - y)"],
    ["ratsimpmodprime(P('1/(x + y)'), [P('x**2 - y**2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('1/(x + y)'), [P('x**2 - y**2')], [x, y], { order: 'grevlex', quick: true }), "1/(x + y)"],
    ["ratsimpmodprime(P('(x + 1)/(y - 1)'), [P('x**2*y**2 - 2*x*y + 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x + 1)/(y - 1)'), [P('x**2*y**2 - 2*x*y + 1')], [x, y], { order: 'grevlex', quick: true }), "(x + 1)/(y - 1)"],
    ["ratsimpmodprime(P('x/(2*(y + 1))'), [P('x*y - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('x/(2*(y + 1))'), [P('x*y - 1')], [x, y], { order: 'grevlex', quick: true }), "x/(2*y + 2)"],
    ["ratsimpmodprime(P('(x/2 + y)/(x*y + 3)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x/2 + y)/(x*y + 3)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(x + 2*y)/(2*x*y + 6)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: true }), "(-x*y**2 + x/2 + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(P('(x**3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1/2')], [x, y], { order: 'grevlex', quick: false }), "(-x*y**2 + x/2 + y)/(x*y + 1)"],
    ["ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1/3')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x + y**2 - 2)/(x + y**2 - y - 1)'), [P('x*y - 1/3')], [x, y], { order: 'grevlex', quick: true }), "(x + y**2 - 2)/(x + y**2 - y - 1)"],
    ["ratsimpmodprime(P('(x/3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('(x/3 + y)/(x*y + 1)'), [P('x**2 + y**2 - 1')], [x, y], { order: 'grevlex', quick: true }), "(x + 3*y)/(3*x*y + 3)"],
    ["ratsimpmodprime(P('y/(-x)'), [P('x - y**2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('y/(-x)'), [P('x - y**2')], [x, y], { order: 'grevlex', quick: true }), "-1/y"],
    ["ratsimpmodprime(P('y/(-x)'), [P('x - y**2')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(P('y/(-x)'), [P('x - y**2')], [x, y], { order: 'grevlex', quick: false }), "-1/y"],
    ["ratsimpmodprime(P('3*y/(x - y**2)'), [P('x*y - 2')], [x, y], { order: 'grevlex', quick: true })", () => ratsimpmodprime(P('3*y/(x - y**2)'), [P('x*y - 2')], [x, y], { order: 'grevlex', quick: true }), "-6/(-x**2 + 2*y)"],
    ["ratsimpmodprime(P('3*y/(x - y**2)'), [P('x*y - 2')], [x, y], { order: 'grevlex', quick: false })", () => ratsimpmodprime(P('3*y/(x - y**2)'), [P('x*y - 2')], [x, y], { order: 'grevlex', quick: false }), "-6/(-x**2 + 2*y)"],
    ["gammasimp(P('ff(p, k)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(P('ff(p, k)', {p: {positive: true}, n: {negative: true}})), "gamma(p + 1)/gamma(-k + p + 1)"],
    ["gammasimp(P('ff(n, k)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(P('ff(n, k)', {p: {positive: true}, n: {negative: true}})), "(-1)**k*gamma(k - n)/gamma(-n)"],
    ["gammasimp(P('ff(-3, k)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(P('ff(-3, k)', {p: {positive: true}, n: {negative: true}})), "(-1)**k*gamma(k + 3)/2"],
    ["gammasimp(P('gamma(x)*gamma(x + 1)/gamma(x + 2)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(P('gamma(x)*gamma(x + 1)/gamma(x + 2)', {p: {positive: true}, n: {negative: true}})), "gamma(x)/(x + 1)"],
    ["gammasimp(P('gamma(x + 2)/(gamma(x)*x)', {p: {positive: true}, n: {negative: true}}))", () => gammasimp(P('gamma(x + 2)/(gamma(x)*x)', {p: {positive: true}, n: {negative: true}})), "x + 1"],
    // symjs factor raises for this noncommutative sum; gammasimp and combsimp then keep it, as SymPy does
    ["gammasimp(P('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}}))", () => gammasimp(P('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}})), "x*A + A*B - B*A"],
    // symjs factor raises for this noncommutative sum; gammasimp and combsimp then keep it, as SymPy does
    ["combsimp(P('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}}))", () => combsimp(P('A*B - B*A + x*A', {A: {commutative: false}, B: {commutative: false}})), "x*A + A*B - B*A"],
    ["signsimp(P('x*(-y - z) + 1'), false)", () => signsimp(P('x*(-y - z) + 1'), false), "-(x*(y + z) - 1)"],
    ["signsimp(P('x*(-y - z) + 1'))", () => signsimp(P('x*(-y - z) + 1')), "-x*(y + z) + 1"],
    ["signsimp(P('w + x*(-y - z)'), false)", () => signsimp(P('w + x*(-y - z)'), false), "w - x*(y + z)"],
    ["signsimp(P('w + x*(-y - z)'))", () => signsimp(P('w + x*(-y - z)')), "w - x*(y + z)"],
    ["signsimp(P('a*(-b - c) + d*(-u - v)'), false)", () => signsimp(P('a*(-b - c) + d*(-u - v)'), false), "-(a*(b + c) + d*(u + v))"],
    ["signsimp(P('a*(-b - c) + d*(-u - v)'))", () => signsimp(P('a*(-b - c) + d*(-u - v)')), "-a*(b + c) - d*(u + v)"],
    ["signsimp(P('x*(-y - z) + w*(-a - b) + 1'), false)", () => signsimp(P('x*(-y - z) + w*(-a - b) + 1'), false), "-(w*(a + b) + x*(y + z) - 1)"],
    ["signsimp(P('x*(-y - z) + w*(-a - b) + 1'))", () => signsimp(P('x*(-y - z) + w*(-a - b) + 1')), "-w*(a + b) - x*(y + z) + 1"],
    ["cancel(P('(sqrt(2) + sqrt(3)*x)/(x + 1)'))", () => cancel(P('(sqrt(2) + sqrt(3)*x)/(x + 1)')), "(sqrt(3)*x + sqrt(2))/(x + 1)"],
    ["cancel(P('(sqrt(3) + sqrt(15)*x)/(sqrt(2) + sqrt(10)*x)'))", () => cancel(P('(sqrt(3) + sqrt(15)*x)/(sqrt(2) + sqrt(10)*x)')), "sqrt(6)/2"],
    ["cancel(P('(sqrt(2)*x + sqrt(6))/(sqrt(3)*x + 3)'))", () => cancel(P('(sqrt(2)*x + sqrt(6))/(sqrt(3)*x + 3)')), "(sqrt(2)*x + sqrt(6))/(sqrt(3)*x + 3)"],
    ["ratsimp(P('(x**2 + y)/(x + y)'))", () => ratsimp(P('(x**2 + y)/(x + y)')), "x - y + (y**2 + y)/(x + y)"],
    ["ratsimp(P('(x**3 + 2*x*y + y**2)/(x - y)'))", () => ratsimp(P('(x**3 + 2*x*y + y**2)/(x - y)')), "x**2 + x*y + y**2 + 2*y + (y**3 + 3*y**2)/(x - y)"],
    ["ratsimp(P('(x**2 + 1)/2'))", () => ratsimp(P('(x**2 + 1)/2')), "x**2/2 + 1/2"],
    ["ratsimp(P('x/(x*y + y)'))", () => ratsimp(P('x/(x*y + y)')), "x/(x*y + y)"],
    ["collect(P('a*x'), P('x'), { exact: null })", () => collect(P('a*x'), P('x'), { exact: null }), "a*x"],
    ["collect(P('x**3*y**2 + 2*x**2*y**2'), P('x*y'))", () => collect(P('x**3*y**2 + 2*x**2*y**2'), P('x*y')), "x**2*y**2*(x + 2)"],
    ["collect(P('x**3*y**2 + 2*x**2*y**3'), P('x*y'))", () => collect(P('x**3*y**2 + 2*x**2*y**3'), P('x*y')), "x**2*y**2*(x + 2*y)"],
    ["collect(P('x**-3*y**-2 + 2*x**-2*y**-3'), P('x*y'))", () => collect(P('x**-3*y**-2 + 2*x**-2*y**-3'), P('x*y')), "(2/y + 1/x)/(x**2*y**2)"],
    ["collect(P('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), P('Derivative(f(x), x)'))", () => collect(P('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), P('Derivative(f(x), x)')), "(a + b)*Derivative(f(x), (x, 2))"],
    ["collect(P('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), P('f(x)'))", () => collect(P('a*Derivative(f(x), x, 2) + b*Derivative(f(x), x, 2)'), P('f(x)')), "(a + b)*Derivative(f(x), (x, 2))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe('ratsimpmodprime (cov2): an ideal that is not prime', () => {
  // SymPy 1.14 raises ValueError('Ideal not prime?')
  it.each(['(x + y)/(x - y)', 'x/(x - y)'])('%s modulo x**2 - y**2', (src) => {
    expect(() => ratsimpmodprime(P(src), [P('x**2 - y**2')], [x, y])).toThrow(/ideal not prime/);
  });
});

describe('ratsimp and cancel (cov2): a Dummy and a Symbol with the same name', () => {
  it('orders the generators by name and divides', () => {
    const d = new Dummy('x');
    // the value is that of (x**2 + d)/(x + d) for two different symbols named x
    const e = mul(add(pow(x, 2), d), pow(add(x, d), -1));
    const r = ratsimp(e);
    const at = (v: Expr) => v.subs([[x, 2], [d, 5]]).toNumber();
    expect(at(r)).toBeCloseTo(9 / 7, 12);
    expect(at(cancel(e))).toBeCloseTo(9 / 7, 12);
  });
});

describe('hypersimp and hypersimilar (cov2): a term index that is not a symbol', () => {
  const fx = P('f(x)');
  it.each([
    ['factorial(f(x))', 'f(x) + 1'],
  ])('hypersimp(%s, f(x)) = %s', (src, want) => {
    expect(String(hypersimp(P(src), fx))).toBe(want);
  });
  it('is NoMatch for a term ratio that is not rational (SymPy: None)', () => {
    expect(String(hypersimp(P('2**(f(x)**2)'), fx))).toBe('NoMatch');
  });
  it('hypersimilar(factorial(f(x)), factorial(f(x) + 1), f(x)) is true', () => {
    expect(hypersimilar(P('factorial(f(x))'), P('factorial(f(x) + 1)'), fx)).toBe(true);
  });
});
