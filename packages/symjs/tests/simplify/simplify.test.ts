// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/simplify.ts.

import { describe, expect, it } from 'vitest';
import { I, add, cancel, cos, countOps, exp, exptotrig, mul, parse, pow, rational, simplify, sin, symbol, symbols, together, trigsimp } from '../../src';
import type { Expr } from '../../src';

const [x, y] = symbols('x y');
const [a, b, theta] = symbols('a b theta', { real: true });
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe('simplify', () => {
  it('proves sin^2 + cos^2 = 1', () => {
    expect(simplify(add(pow(sin(x), 2), pow(cos(x), 2))).toString()).toBe('1');
    expect(simplify(add(pow(sin(mul(rational(1, 2), theta)), 2), pow(cos(mul(rational(1, 2), theta)), 2))).toString()).toBe('1');
  });

  it('collapses angle addition', () => {
    const e = add(mul(cos(a), cos(b)), mul(-1, sin(a), sin(b)));
    expect(simplify(e).toString()).toBe('cos(a + b)');
    const f = add(mul(sin(a), cos(b)), mul(cos(a), sin(b)));
    expect(simplify(f).toString()).toBe('sin(a + b)');
  });

  it('rewrites Euler form', () => {
    expect(simplify(add(cos(theta), mul(I, sin(theta)))).toString()).toBe('exp(I*theta)');
    expect(trigsimp(exp(mul(I, theta))).toString()).toBe('exp(I*theta)');
    expect(exptotrig(exp(mul(I, theta))).toString()).toBe('I*sin(theta) + cos(theta)');
  });

  it('keeps already simple expressions', () => {
    expect(simplify(pow(cos(x), 2)).toString()).toBe('cos(x)**2');
    expect(simplify(add(x, 1)).toString()).toBe('x + 1');
  });

  it('cancels rational functions', () => {
    const e = mul(add(pow(x, 2), -1), pow(add(x, -1), -1));
    expect(cancel(e).toString()).toBe('x + 1');
    expect(simplify(e).toString()).toBe('x + 1');
    expect(together(add(pow(x, -1), pow(y, -1))).toString()).toBe('(x + y)/(x*y)');
    // regression: denominators with non-rational exponents (found by fuzzing)
    const e2 = add(rational(1, 2), mul(2, exp(mul(-3, I))));
    expect(together(e2).toComplex().re).toBeCloseTo(e2.toComplex().re);
  });
});

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["simplify(P('log(x) + log(y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps })", () => simplify(PA('log(x) + log(y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps }), "log(x*y)"],
    ["simplify(P('2*log(x) + 3*log(y)', {x: {positive: true}, y: {positive: true}}), { measure: (e) => countOps(e) })", () => simplify(PA('2*log(x) + 3*log(y)', {x: {positive: true}, y: {positive: true}}), { measure: (e) => countOps(e) }), "log(x**2*y**3)"],
    ["simplify(P('log(x*y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps })", () => simplify(PA('log(x*y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps }), "log(x*y)"],
    ["simplify(P('log(x**2*y)'), { measure: countOps })", () => simplify(PA('log(x**2*y)'), { measure: countOps }), "log(x**2*y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('simplify ends with exptrigsimp (SymPy)', () => {
  // SymPy 1.14: simplify(Znm(1, 1, theta, phi).expand(func=True)), simplify(Znm(2, 1, theta, phi).expand(func=True))
  it('exp(I*phi) + exp(-I*phi) inside a product becomes 2*cos(phi)', () => {
    const [ph, th] = symbols('phi theta');
    const c1 = parse('-sqrt(3)/(4*sqrt(pi))');
    const e1 = add(mul(c1, exp(mul(I, ph)), sin(th)), mul(c1, exp(mul(-1, I, ph)), sin(th)));
    expect(String(simplify(e1))).toBe('-sqrt(3)*sin(theta)*cos(phi)/(2*sqrt(pi))');
    const c2 = parse('-sqrt(15)/(4*sqrt(pi))');
    const e2 = add(mul(c2, exp(mul(I, ph)), sin(th), cos(th)), mul(c2, exp(mul(-1, I, ph)), sin(th), cos(th)));
    expect(String(simplify(e2))).toBe('-sqrt(15)*sin(2*theta)*cos(phi)/(4*sqrt(pi))');
    // an exponential that exptrigsimp does not shorten is kept: simplify(exp(I*x)*y) = y*exp(I*x)
    expect(String(simplify(mul(exp(mul(I, ph)), th)))).toBe('theta*exp(I*phi)');
  });
});

describe('simplify keeps the numeric content of a quotient in front (SymPy factor_terms(expr, sign=False))', () => {
  it.each([
    ['(15 - 63*x)/((x - 1)*(5*x - 1))', '3*(5 - 21*x)/((x - 1)*(5*x - 1))'],
    ['(2*x + 2)/y', '2*(x + 1)/y'],
    ['2*x/(4*y + 6)', 'x/(2*y + 3)'],
    ['(x/2 + 1/2)/y', '(x + 1)/(2*y)'],
    // sums are not factored
    ['2*x + 2', '2*x + 2'],
    ['6*x + 4*y', '6*x + 4*y'],
  ])('simplify(%s)', (src, want) => {
    expect(String(simplify(parse(src)))).toBe(want);
  });
  it('the generating function of sequence(3*5**n + 12)', () => {
    // SymPy: sequence(3*5**n + 12).find_linear_recurrence(20, gfvar=x)[1]
    const e = mul(parse('-3*(21*x - 5)'), pow(parse('(x - 1)*(5*x - 1)'), -1));
    expect(String(simplify(e))).toBe('3*(5 - 21*x)/((x - 1)*(5*x - 1))');
  });
});

describe('simplify of holonomic to_expr results (SymPy holonomic tests)', () => {
  it('exp(-x**2/2) goes to the denominator of together and cancel', () => {
    const e = parse('-x**2*(2/x**2 - 2*exp(-x**2/2)/x**2)/2 + 1 - sqrt(2)*I*sqrt(pi)*exp(-x**2/2)*erf(sqrt(2)*I*x/2)/2');
    expect(String(together(e, { deep: true }))).toBe('(-sqrt(2)*I*sqrt(pi)*erf(sqrt(2)*I*x/2) + 2)*exp(-x**2/2)/2');
    expect(String(simplify(e))).toBe('(-sqrt(2)*I*sqrt(pi)*erf(sqrt(2)*I*x/2) + 2)*exp(-x**2/2)/2');
  });
  it('the product after trigsimp is expanded when that is shorter (SymPy expand_power_exp(expand_mul(short)))', () => {
    expect(String(simplify(parse('(-x**2*(Si(2*x)/x + cos(2*x)/(2*x**2) - 1/(2*x**2)) - 1)/x')))).toBe('-Si(2*x) - cos(x)**2/x');
  });
});

describe('fractions in sums, opposite bases of even powers and rationalized denominators (SymPy simplify)', () => {
  it('match SymPy', () => {
    // SymPy: (-x**2 - y**2)/y**3
    expect(String(simplify(parse('-(x**2/y**2 + 1)/y')))).toBe('-(x**2 + y**2)/y**3');
    expect(String(simplify(parse('sqrt((-u + v)**2) - sqrt((u - v)**2)')))).toBe('0');
    expect(String(simplify(parse('sqrt((-2*u/3 + 2*v/3)**2 + (-2*w/3 + 2*z/3)**2) + sqrt((u/3 - v/3)**2 + (w/3 - z/3)**2) - sqrt((u - v)**2 + (w - z)**2)')))).toBe('0');
    expect(String(simplify(parse('1/(1 + sqrt(2))')))).toBe('-1 + sqrt(2)');
    expect(String(simplify(parse('1/(2 + sqrt(2))')))).toBe('1 - sqrt(2)/2');
    expect(String(simplify(parse('1/(x + 1)')))).toBe('1/(x + 1)');
  });
});
