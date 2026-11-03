// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/besselsimp.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, Rational, besseli, besselj, besselsimp, expPolar, fn, mul, parse, polarLift, symbol, symbols } from '../../src';
import type { Expr } from '../../src';

const [z, nu] = symbols('z nu x');
const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PPolar = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { locals: { exp_polar: expPolar, polar_lift: polarLift }, symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

// expected values from SymPy 1.14
describe('Bessel and Airy functions', () => {
  it('besselsimp', () => {
    expect(String(besselsimp(besselj(nu, mul(z, fn('polar_lift', [-1])))))).toBe('exp(I*pi*nu)*besselj(nu, z)');
    expect(String(besselsimp(besseli(Rational.of(-1, 2), z)))).toBe('sqrt(2)*cosh(z)/(sqrt(pi)*sqrt(z))');
    expect(String(besselsimp(besselj(Rational.of(3, 2), z)))).toBe('-sqrt(2)*(z*cos(z) - sin(z))/(sqrt(pi)*z**(3/2))');
    expect(String(besselsimp(parse('z*besseli(0, z) + z*besseli(2, z)/2 + besseli(1, z)')))).toBe('3*z*besseli(0, z)/2');
    expect(String(besselsimp(parse('besselj(2, z) + besselj(0, z)')))).toBe('2*besselj(1, z)/z');
  });
});

describe("simplify functions: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["besselsimp(P(\"besseli(-1/2, z)\"))", () => besselsimp(P("besseli(-1/2, z)")), "sqrt(2)*cosh(z)/(sqrt(pi)*sqrt(z))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("besselsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["besselsimp(P('besselj(a, polar_lift(-1)*z)'))", () => besselsimp(PPolar('besselj(a, polar_lift(-1)*z)')), "exp(I*pi*a)*besselj(a, z)"],
    ["besselsimp(P('besseli(a, polar_lift(I)*z)'))", () => besselsimp(PPolar('besseli(a, polar_lift(I)*z)')), "exp(I*pi*a/2)*besselj(a, z)"],
    ["besselsimp(P('besselj(a, polar_lift(-I)*z)'))", () => besselsimp(PPolar('besselj(a, polar_lift(-I)*z)')), "exp(-I*pi*a/2)*besseli(a, z)"],
    ["besselsimp(P('besseli(a, polar_lift(2)*z)'))", () => besselsimp(PPolar('besseli(a, polar_lift(2)*z)')), "besseli(a, 2*z*exp_polar(0))"],
    ["besselsimp(P('besselk(a, exp_polar(I*pi)*z)'))", () => besselsimp(PPolar('besselk(a, exp_polar(I*pi)*z)')), "besselk(a, z*exp_polar(I*pi))"],
    ["besselsimp(P('bessely(a, exp_polar(I*pi/2)*z)'))", () => besselsimp(PPolar('bessely(a, exp_polar(I*pi/2)*z)')), "bessely(a, z*exp_polar(I*pi/2))"],
    ["besselsimp(P('besselj(a, exp_polar(I*pi/3)*z)'))", () => besselsimp(PPolar('besselj(a, exp_polar(I*pi/3)*z)')), "besselj(a, z*exp_polar(I*pi/3))"],
    ["besselsimp(P('besselj(a, exp_polar(x)*z)'))", () => besselsimp(PPolar('besselj(a, exp_polar(x)*z)')), "besselj(a, z*exp_polar(x))"],
    ["besselsimp(P('besselj(-5/2, z)'))", () => besselsimp(PPolar('besselj(-5/2, z)')), "-sqrt(2)*(z**2*cos(z) - 3*z*sin(z) - 3*cos(z))/(sqrt(pi)*z**(5/2))"],
    ["besselsimp(P('bessely(-3/2, z)'))", () => besselsimp(PPolar('bessely(-3/2, z)')), "sqrt(2)*(z*cos(z) - sin(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besseli(-5/2, z)'))", () => besselsimp(PPolar('besseli(-5/2, z)')), "sqrt(2)*(z**2*cosh(z) - 3*z*sinh(z) + 3*cosh(z))/(sqrt(pi)*z**(5/2))"],
    ["besselsimp(P('besselk(-5/2, z)'))", () => besselsimp(PPolar('besselk(-5/2, z)')), "sqrt(2)*sqrt(pi)*(z**2 + 3*z + 3)*exp(-z)/(2*z**(5/2))"],
    ["besselsimp(P('bessely(-5/2, z)'))", () => besselsimp(PPolar('bessely(-5/2, z)')), "-sqrt(2)*(z**2*sin(z) + 3*z*cos(z) - 3*sin(z))/(sqrt(pi)*z**(5/2))"],
    ["besselsimp(P('besselj(-3/2, z)'))", () => besselsimp(PPolar('besselj(-3/2, z)')), "-sqrt(2)*(z*sin(z) + cos(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besselk(3, z)'))", () => besselsimp(PPolar('besselk(3, z)')), "(z**2*besselk(1, z) + 4*z*besselk(0, z) + 8*besselk(1, z))/z**2"],
    ["besselsimp(P('bessely(2, z)'))", () => besselsimp(PPolar('bessely(2, z)')), "-(z*bessely(0, z) - 2*bessely(1, z))/z"],
    ["besselsimp(P('besseli(3, z)'))", () => besselsimp(PPolar('besseli(3, z)')), "(z**2*besseli(1, z) - 4*z*besseli(0, z) + 8*besseli(1, z))/z**2"],
    ["besselsimp(P('besselj(a, z)'))", () => besselsimp(PPolar('besselj(a, z)')), "besselj(a, z)"],
    ["besselsimp(P('besselk(5/2, z)'))", () => besselsimp(PPolar('besselk(5/2, z)')), "sqrt(2)*sqrt(pi)*(z**2 + 3*z + 3)*exp(-z)/(2*z**(5/2))"],
    ["besselsimp(P('besselj(1/2, z)*x + 1'))", () => besselsimp(PPolar('besselj(1/2, z)*x + 1')), "(sqrt(2)*x*sin(z) + sqrt(pi)*sqrt(z))/(sqrt(pi)*sqrt(z))"],
    ["besselsimp(P('besseli(3/2, z)'))", () => besselsimp(PPolar('besseli(3/2, z)')), "sqrt(2)*(z*cosh(z) - sinh(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('bessely(3/2, z)'))", () => besselsimp(PPolar('bessely(3/2, z)')), "-sqrt(2)*(z*sin(z) + cos(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besseli(-3/2, z)'))", () => besselsimp(PPolar('besseli(-3/2, z)')), "sqrt(2)*(z*sinh(z) - cosh(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besselj(2, z) + besselj(0, z)'))", () => besselsimp(PPolar('besselj(2, z) + besselj(0, z)')), "2*besselj(1, z)/z"],
    ["besselsimp(P('besselj(1/2, z)'))", () => besselsimp(PPolar('besselj(1/2, z)')), "sqrt(2)*sin(z)/(sqrt(pi)*sqrt(z))"],
    ["besselsimp(P('besselj(3, z)'))", () => besselsimp(PPolar('besselj(3, z)')), "-(z**2*besselj(1, z) + 4*z*besselj(0, z) - 8*besselj(1, z))/z**2"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});
