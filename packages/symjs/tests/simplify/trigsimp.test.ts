// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/trigsimp.ts.

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Sym, exptrigsimp, parse, symbol, trigsimp } from '../../src';
import type { Expr } from '../../src';

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe('exptrigsimp', () => {
  it('recombines exponentials into hyperbolic functions and back', () => {
    expect(String(exptrigsimp(parse('exp(z) + exp(-z)')))).toBe('2*cosh(z)');
    expect(String(exptrigsimp(parse('exp(z) - exp(-z)')))).toBe('2*sinh(z)');
    expect(String(exptrigsimp(parse('cosh(z) - sinh(z)')))).toBe('exp(-z)');
  });
});

describe("simplify functions: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["trigsimp(P(\"tanh(x)\"))", () => trigsimp(P("tanh(x)")), "tanh(x)"],
    ["trigsimp(P(\"tan(x) - 1/cot(x)\"))", () => trigsimp(P("tan(x) - 1/cot(x)")), "0"],
    ["trigsimp(P(\"3*tanh(x)**7 - 2/coth(x)**7\"))", () => trigsimp(P("3*tanh(x)**7 - 2/coth(x)**7")), "tanh(x)**7"],
    ["trigsimp(P(\"sin(1/50)*sin(1/25) + cos(1/50)*cos(1/25)\"))", () => trigsimp(P("sin(1/50)*sin(1/25) + cos(1/50)*cos(1/25)")), "cos(1/50)"],
    ["trigsimp(P(\"sin(1/50)*cos(1/25) + sin(1/25)*cos(1/50)\"))", () => trigsimp(P("sin(1/50)*cos(1/25) + sin(1/25)*cos(1/50)")), "sin(3/50)"],
    ["trigsimp(P(\"sin(2)*cos(3) + sin(3)*cos(2)\"))", () => trigsimp(P("sin(2)*cos(3) + sin(3)*cos(2)")), "sin(5)"],
    ["trigsimp(P(\"-sin(2)*sin(3) + cos(2)*cos(3)\"))", () => trigsimp(P("-sin(2)*sin(3) + cos(2)*cos(3)")), "cos(5)"],
    ["trigsimp(P(\"sin(2)*cos(3) - sin(3)*cos(2)\"))", () => trigsimp(P("sin(2)*cos(3) - sin(3)*cos(2)")), "-sin(1)"],
    ["trigsimp(P(\"sin(2)*sin(3) + cos(2)*cos(3)\"))", () => trigsimp(P("sin(2)*sin(3) + cos(2)*cos(3)")), "cos(1)"],
    ["trigsimp(P(\"cos(2) + sin(2)*sin(3) + cos(2)*cos(3)\"))", () => trigsimp(P("cos(2) + sin(2)*sin(3) + cos(2)*cos(3)")), "cos(2) + cos(1)"],
    ["trigsimp(P(\"sin(x)**2*sin(y)**2 + sin(x)**2*cos(y)**2 + cos(x)**2\"))", () => trigsimp(P("sin(x)**2*sin(y)**2 + sin(x)**2*cos(y)**2 + cos(x)**2")), "1"],
    ["trigsimp(P(\"a**2*sin(x)**2 + a**2*sin(y)**2*cos(x)**2 + a**2*cos(x)**2*cos(y)**2\"))", () => trigsimp(P("a**2*sin(x)**2 + a**2*sin(y)**2*cos(x)**2 + a**2*cos(x)**2*cos(y)**2")), "a**2"],
    ["trigsimp(P(\"-4*sin(x)**4 + 4*cos(x)**4 - 8*cos(x)**2\"))", () => trigsimp(P("-4*sin(x)**4 + 4*cos(x)**4 - 8*cos(x)**2")), "-4"],
    ["trigsimp(P(\"-sin(x)**4 + cos(x)**4 - 2*cos(x)**2\"))", () => trigsimp(P("-sin(x)**4 + cos(x)**4 - 2*cos(x)**2")), "-1"],
    ["trigsimp(P(\"-sin(x)**3*cos(x)/4 + sin(x)*cos(x)**3/4 - sin(2*x)*cos(2*x)/8\"))", () => trigsimp(P("-sin(x)**3*cos(x)/4 + sin(x)*cos(x)**3/4 - sin(2*x)*cos(2*x)/8")), "0"],
    ["trigsimp(P(\"sin(x)*cos(y) + sin(y)*cos(x)\"))", () => trigsimp(P("sin(x)*cos(y) + sin(y)*cos(x)")), "sin(x + y)"],
    ["trigsimp(P(\"sin(x)*cos(y) + sin(y)*cos(x) + 3\"))", () => trigsimp(P("sin(x)*cos(y) + sin(y)*cos(x) + 3")), "sin(x + y) + 3"],
    ["trigsimp(P(\"cos(x)/sin(x)**7\"))", () => trigsimp(P("cos(x)/sin(x)**7")), "cos(x)/sin(x)**7"],
    ["trigsimp(P(\"xp*(-76*y*sin(x) + 20*y*sin(3*x) + 60*z*cos(2*x) - 84*z)/(9*cos(x) - 5*cos(3*x))\"))", () => trigsimp(P("xp*(-76*y*sin(x) + 20*y*sin(3*x) + 60*z*cos(2*x) - 84*z)/(9*cos(x) - 5*cos(3*x))")), "xp*(-76*y*sin(x) + 20*y*sin(3*x) + 60*z*cos(2*x) - 84*z)/(9*cos(x) - 5*cos(3*x))"],
    ["trigsimp(P(\"sin(x)**2 + cos(x)**2\"))", () => trigsimp(P("sin(x)**2 + cos(x)**2")), "1"],
    ["trigsimp(P(\"5*sin(x)**2 + 5*cos(x)**2\"))", () => trigsimp(P("5*sin(x)**2 + 5*cos(x)**2")), "5"],
    ["trigsimp(P(\"2*sin(x/2)**2 + 5*cos(x/2)**2\"))", () => trigsimp(P("2*sin(x/2)**2 + 5*cos(x/2)**2")), "3*cos(x)/2 + 7/2"],
    ["trigsimp(P(\"log(2*sin(x)**2 + 2*cos(x)**2)\"))", () => trigsimp(P("log(2*sin(x)**2 + 2*cos(x)**2)")), "log(2)"],
    ["trigsimp(P(\"exp(2)*cos(3)*tan(2)*cot(2)\"))", () => trigsimp(P("exp(2)*cos(3)*tan(2)*cot(2)")), "exp(2)*cos(3)"],
    ["trigsimp(P(\"exp(2)*cos(3)*tanh(2)*coth(2)\"))", () => trigsimp(P("exp(2)*cos(3)*tanh(2)*coth(2)")), "exp(2)*cos(3)"],
    ["trigsimp(P(\"Subs(x, x, sin(y)**2 + cos(y)**2)\"))", () => trigsimp(P("Subs(x, x, sin(y)**2 + cos(y)**2)")), "Subs(x, x, 1)"],
    ["trigsimp(P(\"tan(x)\"))", () => trigsimp(P("tan(x)")), "tan(x)"],
    ["trigsimp(P(\"-sin(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)\"))", () => trigsimp(P("-sin(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)")), "-sin(alpha)"],
    ["trigsimp(P(\"-cos(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)\"))", () => trigsimp(P("-cos(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)")), "-cos(alpha)"],
    ["trigsimp(P(\"cos(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)\"))", () => trigsimp(P("cos(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)")), "cos(alpha)"],
    ["trigsimp(P(\"sin(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)\"))", () => trigsimp(P("sin(alpha)/sqrt(sin(alpha)**2 + cos(alpha)**2)")), "sin(alpha)"],
    ["trigsimp(P(\"cosh(pi/4)\"))", () => trigsimp(P("cosh(pi/4)")), "cosh(pi/4)"],
    ["trigsimp(P(\"sin(x)**3 + sin(x)*cos(x)**2\"))", () => trigsimp(P("sin(x)**3 + sin(x)*cos(x)**2")), "sin(x)"],
    ["trigsimp(P(\"cos(x)/sin(x)**3\"))", () => trigsimp(P("cos(x)/sin(x)**3")), "cos(x)/sin(x)**3"],
    ["trigsimp(P(\"sin(x)/cos(x)**3\"))", () => trigsimp(P("sin(x)/cos(x)**3")), "sin(x)/cos(x)**3"],
    ["trigsimp(P(\"sin(x)**y/cos(x)**y\"))", () => trigsimp(P("sin(x)**y/cos(x)**y")), "sin(x)**y/cos(x)**y"],
    ["trigsimp(P(\"(cos(3) + 1)**2*cos(2)/(-1 + cos(3))**2\"))", () => trigsimp(P("(cos(3) + 1)**2*cos(2)/(-1 + cos(3))**2")), "(cos(3) + 1)**2*cos(2)/(-1 + cos(3))**2"],
    ["trigsimp(1)", () => trigsimp(1), "1"],
    ["trigsimp(P(\"-sin(x)**4 - 2*sin(x)**2*cos(x)**2 - cos(x)**4\"))", () => trigsimp(P("-sin(x)**4 - 2*sin(x)**2*cos(x)**2 - cos(x)**4")), "-1"],
    ["trigsimp(Qs(\"sin(x)**2*A + cos(x)**2*A\", [symbol(\"A\", { commutative: false })]))", () => trigsimp(Qs("sin(x)**2*A + cos(x)**2*A", [symbol("A", { commutative: false })])), "A"],
    ["trigsimp(Qs(\"y*sin(x)**2*A + y*cos(x)**2*A\", [symbol(\"A\", { commutative: false })]))", () => trigsimp(Qs("y*sin(x)**2*A + y*cos(x)**2*A", [symbol("A", { commutative: false })])), "y*A"],
    ["exptrigsimp(P(\"exp(x) + exp(-x)\"))", () => exptrigsimp(P("exp(x) + exp(-x)")), "2*cosh(x)"],
    ["exptrigsimp(P(\"exp(x) - exp(-x)\"))", () => exptrigsimp(P("exp(x) - exp(-x)")), "2*sinh(x)"],
    ["exptrigsimp(P(\"I*sin(x) + cos(x)\"))", () => exptrigsimp(P("I*sin(x) + cos(x)")), "exp(I*x)"],
    ["exptrigsimp(P(\"-I*sin(x) + cos(x)\"))", () => exptrigsimp(P("-I*sin(x) + cos(x)")), "exp(-I*x)"],
    ["exptrigsimp(P(\"-sinh(x) + cosh(x)\"))", () => exptrigsimp(P("-sinh(x) + cosh(x)")), "exp(-x)"],
    ["exptrigsimp(P(\"sinh(x) + cosh(x)\"))", () => exptrigsimp(P("sinh(x) + cosh(x)")), "exp(x)"],
    ["exptrigsimp(P(\"sin(x) + cos(x)\"))", () => exptrigsimp(P("sin(x) + cos(x)")), "sin(x) + cos(x)"],
    ["exptrigsimp(P(\"-sin(x) + cos(x)\"))", () => exptrigsimp(P("-sin(x) + cos(x)")), "-sin(x) + cos(x)"],
    ["exptrigsimp(P(\"I*sinh(x) + cosh(x)\"))", () => exptrigsimp(P("I*sinh(x) + cosh(x)")), "I*sinh(x) + cosh(x)"],
    ["exptrigsimp(P(\"-I*sinh(x) + cosh(x)\"))", () => exptrigsimp(P("-I*sinh(x) + cosh(x)")), "-I*sinh(x) + cosh(x)"],
    ["exptrigsimp(P(\"exp(-2) + exp(2)\"))", () => exptrigsimp(P("exp(-2) + exp(2)")), "2*cosh(2)"],
    ["exptrigsimp(P(\"-exp(-2) + exp(2)\"))", () => exptrigsimp(P("-exp(-2) + exp(2)")), "2*sinh(2)"],
    ["exptrigsimp(Qs(\"exp(a)*exp(b) - exp(b)*exp(a)\", [symbol(\"b\", { commutative: false }), symbol(\"a\", { commutative: false })]))", () => exptrigsimp(Qs("exp(a)*exp(b) - exp(b)*exp(a)", [symbol("b", { commutative: false }), symbol("a", { commutative: false })])), "exp(a)*exp(b) - exp(b)*exp(a)"],
    ["exptrigsimp(P(\"exp(-1/2) + E\"))", () => exptrigsimp(P("exp(-1/2) + E")), "exp(-1/2) + E"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["trigsimp(P('sin(x)**2 + cos(x)**2'), { old: true })", () => trigsimp(PA('sin(x)**2 + cos(x)**2'), { old: true }), "1"],
    ["trigsimp(P('log(sin(x)**2 + cos(x)**2)'), { old: true })", () => trigsimp(PA('log(sin(x)**2 + cos(x)**2)'), { old: true }), "log(sin(x)**2 + cos(x)**2)"],
    ["trigsimp(P('log(sin(x)**2 + cos(x)**2)'), { old: true, deep: true })", () => trigsimp(PA('log(sin(x)**2 + cos(x)**2)'), { old: true, deep: true }), "0"],
    ["trigsimp(P('1/cot(x)**2'), { old: true })", () => trigsimp(PA('1/cot(x)**2'), { old: true }), "cot(x)**(-2)"],
    ["trigsimp(P('cot(x)**2'), { old: true })", () => trigsimp(PA('cot(x)**2'), { old: true }), "cot(x)**2"],
    ["trigsimp(P('exp(sin(x)**2 + cos(x)**2) + sin(y)**2 + cos(y)**2'), { old: true })", () => trigsimp(PA('exp(sin(x)**2 + cos(x)**2) + sin(y)**2 + cos(y)**2'), { old: true }), "1 + E"],
    ["trigsimp(P('x*cosh(y)**2 - x*sinh(y)**2'))", () => trigsimp(PA('x*cosh(y)**2 - x*sinh(y)**2')), "x"],
    ["trigsimp(P('-x*sinh(y)**2 + x*cosh(y)**2 + 1'))", () => trigsimp(PA('-x*sinh(y)**2 + x*cosh(y)**2 + 1')), "x + 1"],
    ["trigsimp(P('sinh(y)**2*x - cosh(y)**2*x'))", () => trigsimp(PA('sinh(y)**2*x - cosh(y)**2*x')), "-x"],
    ["trigsimp(P('cosh(x)**2 - sinh(x)**2'))", () => trigsimp(PA('cosh(x)**2 - sinh(x)**2')), "1"],
    ["trigsimp(P('sin(x)*cos(x)'))", () => trigsimp(PA('sin(x)*cos(x)')), "sin(2*x)/2"],
    ["exptrigsimp(P('exp(x) + 2*exp(-x)'))", () => exptrigsimp(PA('exp(x) + 2*exp(-x)')), "exp(x) + 2*exp(-x)"],
    ["trigsimp(P('x/sin(x) + y/sin(x)'))", () => trigsimp(PA('x/sin(x) + y/sin(x)')), "(x + y)/sin(x)"],
    ["trigsimp(P('1/sin(x) + 1/cos(x)'))", () => trigsimp(PA('1/sin(x) + 1/cos(x)')), "1/cos(x) + 1/sin(x)"],
    ["trigsimp(P('sin(x)**2/(1+cos(x)) + cos(x)'))", () => trigsimp(PA('sin(x)**2/(1+cos(x)) + cos(x)')), "1"],
    ["trigsimp(P('cos(x)/x + sin(x)/y'))", () => trigsimp(PA('cos(x)/x + sin(x)/y')), "sin(x)/y + cos(x)/x"],
    ["trigsimp(P('tan(x)/x - sin(x)/(x*cos(x))'))", () => trigsimp(PA('tan(x)/x - sin(x)/(x*cos(x))')), "0"],
    ["trigsimp(P('(sin(x)*cos(y) + cos(x)*sin(y))/z + 1/z'))", () => trigsimp(PA('(sin(x)*cos(y) + cos(x)*sin(y))/z + 1/z')), "(sin(x + y) + 1)/z"],
    ["trigsimp(P('sin(x)*cos(y)/z + cos(x)*sin(y)/z'))", () => trigsimp(PA('sin(x)*cos(y)/z + cos(x)*sin(y)/z')), "sin(x + y)/z"],
    ["trigsimp(P('sin(x)**2/x + cos(x)**2/x'))", () => trigsimp(PA('sin(x)**2/x + cos(x)**2/x')), "1/x"],
    ["trigsimp(P('sin(x)**2/(1+cos(x)) + cos(x)'), { old: true, method: 'groebner' })", () => trigsimp(PA('sin(x)**2/(1+cos(x)) + cos(x)'), { old: true, method: 'groebner' }), "1"],
    ["trigsimp(P('x/sin(x) + y/sin(x)'), { old: true, deep: true })", () => trigsimp(PA('x/sin(x) + y/sin(x)'), { old: true, deep: true }), "x/sin(x) + y/sin(x)"],
    ["exptrigsimp(P('exp(x) + exp(-x)'))", () => exptrigsimp(PA('exp(x) + exp(-x)')), "2*cosh(x)"],
    ["exptrigsimp(P('exp(x) - exp(-x)'))", () => exptrigsimp(PA('exp(x) - exp(-x)')), "2*sinh(x)"],
    ["exptrigsimp(P('cosh(x) + sinh(x)'))", () => exptrigsimp(PA('cosh(x) + sinh(x)')), "exp(x)"],
    ["trigsimp(P('exp(I*x)/cos(x)'))", () => trigsimp(PA('exp(I*x)/cos(x)')), "exp(I*x)/cos(x)"],
    ["trigsimp(P('x*cos(x + 1) + (x + 1)*cos(x) + cosh(1/2)**2'))", () => trigsimp(PA('x*cos(x + 1) + (x + 1)*cos(x) + cosh(1/2)**2')), "x*cos(x + 1) + (x + 1)*cos(x) + cosh(1/2)**2"],
    ["trigsimp(P('x*sin(x + 1) + exp(I*x)/cos(x) + sin(1/2)'))", () => trigsimp(PA('x*sin(x + 1) + exp(I*x)/cos(x) + sin(1/2)')), "x*sin(x + 1) + exp(I*x)/cos(x) + sin(1/2)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});
