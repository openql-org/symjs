// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { countOps, exptrigsimp, fraction, parse, powsimp, separatevars, simplify, symbol, together, trigsimp } from '../src';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const P = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

const show = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${show(k)}: ${show(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["simplify(P('log(x) + log(y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps })", () => simplify(P('log(x) + log(y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps }), "log(x*y)"],
    ["simplify(P('2*log(x) + 3*log(y)', {x: {positive: true}, y: {positive: true}}), { measure: (e) => countOps(e) })", () => simplify(P('2*log(x) + 3*log(y)', {x: {positive: true}, y: {positive: true}}), { measure: (e) => countOps(e) }), "log(x**2*y**3)"],
    ["simplify(P('log(x*y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps })", () => simplify(P('log(x*y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps }), "log(x*y)"],
    ["simplify(P('log(x**2*y)'), { measure: countOps })", () => simplify(P('log(x**2*y)'), { measure: countOps }), "log(x**2*y)"],
    ["trigsimp(P('sin(x)**2 + cos(x)**2'), { old: true })", () => trigsimp(P('sin(x)**2 + cos(x)**2'), { old: true }), "1"],
    ["trigsimp(P('log(sin(x)**2 + cos(x)**2)'), { old: true })", () => trigsimp(P('log(sin(x)**2 + cos(x)**2)'), { old: true }), "log(sin(x)**2 + cos(x)**2)"],
    ["trigsimp(P('log(sin(x)**2 + cos(x)**2)'), { old: true, deep: true })", () => trigsimp(P('log(sin(x)**2 + cos(x)**2)'), { old: true, deep: true }), "0"],
    ["trigsimp(P('1/cot(x)**2'), { old: true })", () => trigsimp(P('1/cot(x)**2'), { old: true }), "cot(x)**(-2)"],
    ["trigsimp(P('cot(x)**2'), { old: true })", () => trigsimp(P('cot(x)**2'), { old: true }), "cot(x)**2"],
    ["trigsimp(P('exp(sin(x)**2 + cos(x)**2) + sin(y)**2 + cos(y)**2'), { old: true })", () => trigsimp(P('exp(sin(x)**2 + cos(x)**2) + sin(y)**2 + cos(y)**2'), { old: true }), "1 + E"],
    ["trigsimp(P('x*cosh(y)**2 - x*sinh(y)**2'))", () => trigsimp(P('x*cosh(y)**2 - x*sinh(y)**2')), "x"],
    ["trigsimp(P('-x*sinh(y)**2 + x*cosh(y)**2 + 1'))", () => trigsimp(P('-x*sinh(y)**2 + x*cosh(y)**2 + 1')), "x + 1"],
    ["trigsimp(P('sinh(y)**2*x - cosh(y)**2*x'))", () => trigsimp(P('sinh(y)**2*x - cosh(y)**2*x')), "-x"],
    ["trigsimp(P('cosh(x)**2 - sinh(x)**2'))", () => trigsimp(P('cosh(x)**2 - sinh(x)**2')), "1"],
    ["trigsimp(P('sin(x)*cos(x)'))", () => trigsimp(P('sin(x)*cos(x)')), "sin(2*x)/2"],
    ["exptrigsimp(P('exp(x) + 2*exp(-x)'))", () => exptrigsimp(P('exp(x) + 2*exp(-x)')), "exp(x) + 2*exp(-x)"],
    ["separatevars(P('x*y/(x + y + 3) + x/(x + y + 3) + y/(x + y + 3) + 1/(x + y + 3)'))", () => separatevars(P('x*y/(x + y + 3) + x/(x + y + 3) + y/(x + y + 3) + 1/(x + y + 3)')), "(x + 1)*(y + 1)/(x + y + 3)"],
    ["separatevars(P('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)'))", () => separatevars(P('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)')), "z*(x + 1)*(y + 1)/(x + y + 3)"],
    ["separatevars(P('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)'), { force: true })", () => separatevars(P('x*y*z/(x + y + 3) + x*z/(x + y + 3) + y*z/(x + y + 3) + z/(x + y + 3)'), { force: true }), "z*(x + 1)*(y + 1)/(x + y + 3)"],
    ["separatevars(P('(2*x + 2)*y'), { dict: true, symbols: [] })", () => separatevars(P('(2*x + 2)*y'), { dict: true, symbols: [] }), "{coeff: 1, x: 2*x + 2, y: y}"],
    ["separatevars(P('2*x + y'), { dict: true })", () => separatevars(P('2*x + y'), { dict: true }), "NoMatch"],
    ["fraction(P('2*x**-2*y/3', {y: {positive: true}}), { exact: true })", () => fraction(P('2*x**-2*y/3', {y: {positive: true}}), { exact: true }), "[2*y, 3*x**2]"],
    ["fraction(P('x**-y', {y: {positive: true}}), { exact: true })", () => fraction(P('x**-y', {y: {positive: true}}), { exact: true }), "[x**(-y), 1]"],
    ["fraction(P('x**-y', {y: {positive: true}}))", () => fraction(P('x**-y', {y: {positive: true}})), "[1, x**y]"],
    ["fraction(P('x**(-sqrt(2))*y'), { exact: true })", () => fraction(P('x**(-sqrt(2))*y'), { exact: true }), "[y, x**(sqrt(2))]"],
    ["fraction(P('x'), { exact: true })", () => fraction(P('x'), { exact: true }), "[x, 1]"],
    ["fraction(P('1/x'), { exact: true })", () => fraction(P('1/x'), { exact: true }), "[1, x]"],
    ["fraction(P('x/3'), { exact: true })", () => fraction(P('x/3'), { exact: true }), "[x, 3]"],
    ["fraction(P('exp(-x)*x'), { exact: true })", () => fraction(P('exp(-x)*x'), { exact: true }), "[x*exp(-x), 1]"],
    ["fraction(P('3/(x*y)'), { exact: true })", () => fraction(P('3/(x*y)'), { exact: true }), "[3, x*y]"],
    ["fraction(P('x**(-1/2)'), { exact: true })", () => fraction(P('x**(-1/2)'), { exact: true }), "[1, sqrt(x)]"],
    ["together(P('(1/x + 1/y)**(1/z + 1)'), { deep: true })", () => together(P('(1/x + 1/y)**(1/z + 1)'), { deep: true }), "((x + y)/(x*y))**((z + 1)/z)"],
    ["together(P('exp(1/x + 1/y)'), { deep: true })", () => together(P('exp(1/x + 1/y)'), { deep: true }), "exp((x + y)/(x*y))"],
    ["powsimp(P('x*sqrt(x/y)/y**3'))", () => powsimp(P('x*sqrt(x/y)/y**3')), "x*sqrt(x/y)/y**3"],
    ["powsimp(P('x**2*sqrt(x/y)/y**3'))", () => powsimp(P('x**2*sqrt(x/y)/y**3')), "x**2*sqrt(x/y)/y**3"],
    ["powsimp(P('x**3*(x/y)**(1/3)*y**5'))", () => powsimp(P('x**3*(x/y)**(1/3)*y**5')), "x**3*y**5*(x/y)**(1/3)"],
    ["powsimp(P('x**3*(x*y**2)**(1/3)*y**5'))", () => powsimp(P('x**3*(x*y**2)**(1/3)*y**5')), "x*y*(x*y**2)**(7/3)"],
    ["powsimp(P('x**4*(x*y**2)**(1/3)*y**5*(x*y)**(1/2)'))", () => powsimp(P('x**4*(x*y**2)**(1/3)*y**5*(x*y)**(1/2)')), "x*(x*y)**(3/2)*(x*y**2)**(7/3)"],
    ["powsimp(P('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)'))", () => powsimp(P('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)')), "y**3*(x*sqrt(y))**(13/3)*sqrt(x*y)"],
    ["trigsimp(P('x/sin(x) + y/sin(x)'))", () => trigsimp(P('x/sin(x) + y/sin(x)')), "(x + y)/sin(x)"],
    ["trigsimp(P('1/sin(x) + 1/cos(x)'))", () => trigsimp(P('1/sin(x) + 1/cos(x)')), "1/cos(x) + 1/sin(x)"],
    ["trigsimp(P('sin(x)**2/(1+cos(x)) + cos(x)'))", () => trigsimp(P('sin(x)**2/(1+cos(x)) + cos(x)')), "1"],
    ["trigsimp(P('cos(x)/x + sin(x)/y'))", () => trigsimp(P('cos(x)/x + sin(x)/y')), "sin(x)/y + cos(x)/x"],
    ["trigsimp(P('tan(x)/x - sin(x)/(x*cos(x))'))", () => trigsimp(P('tan(x)/x - sin(x)/(x*cos(x))')), "0"],
    ["trigsimp(P('(sin(x)*cos(y) + cos(x)*sin(y))/z + 1/z'))", () => trigsimp(P('(sin(x)*cos(y) + cos(x)*sin(y))/z + 1/z')), "(sin(x + y) + 1)/z"],
    ["trigsimp(P('sin(x)*cos(y)/z + cos(x)*sin(y)/z'))", () => trigsimp(P('sin(x)*cos(y)/z + cos(x)*sin(y)/z')), "sin(x + y)/z"],
    ["trigsimp(P('sin(x)**2/x + cos(x)**2/x'))", () => trigsimp(P('sin(x)**2/x + cos(x)**2/x')), "1/x"],
    ["trigsimp(P('sin(x)**2/(1+cos(x)) + cos(x)'), { old: true, method: 'groebner' })", () => trigsimp(P('sin(x)**2/(1+cos(x)) + cos(x)'), { old: true, method: 'groebner' }), "1"],
    ["trigsimp(P('x/sin(x) + y/sin(x)'), { old: true, deep: true })", () => trigsimp(P('x/sin(x) + y/sin(x)'), { old: true, deep: true }), "x/sin(x) + y/sin(x)"],
    ["exptrigsimp(P('exp(x) + exp(-x)'))", () => exptrigsimp(P('exp(x) + exp(-x)')), "2*cosh(x)"],
    ["exptrigsimp(P('exp(x) - exp(-x)'))", () => exptrigsimp(P('exp(x) - exp(-x)')), "2*sinh(x)"],
    ["exptrigsimp(P('cosh(x) + sinh(x)'))", () => exptrigsimp(P('cosh(x) + sinh(x)')), "exp(x)"],
    ["trigsimp(P('exp(I*x)/cos(x)'))", () => trigsimp(P('exp(I*x)/cos(x)')), "exp(I*x)/cos(x)"],
    ["trigsimp(P('x*cos(x + 1) + (x + 1)*cos(x) + cosh(1/2)**2'))", () => trigsimp(P('x*cos(x + 1) + (x + 1)*cos(x) + cosh(1/2)**2')), "x*cos(x + 1) + (x + 1)*cos(x) + cosh(1/2)**2"],
    ["trigsimp(P('x*sin(x + 1) + exp(I*x)/cos(x) + sin(1/2)'))", () => trigsimp(P('x*sin(x + 1) + exp(I*x)/cos(x) + sin(1/2)')), "x*sin(x + 1) + exp(I*x)/cos(x) + sin(1/2)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
