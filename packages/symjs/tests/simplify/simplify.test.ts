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
