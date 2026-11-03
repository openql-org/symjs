// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { besselsimp, expPolar, parse, polarLift, symbol } from '../src';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const P = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { locals: { exp_polar: expPolar, polar_lift: polarLift }, symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

const show = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${show(k)}: ${show(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("besselsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["besselsimp(P('besselj(a, polar_lift(-1)*z)'))", () => besselsimp(P('besselj(a, polar_lift(-1)*z)')), "exp(I*pi*a)*besselj(a, z)"],
    ["besselsimp(P('besseli(a, polar_lift(I)*z)'))", () => besselsimp(P('besseli(a, polar_lift(I)*z)')), "exp(I*pi*a/2)*besselj(a, z)"],
    ["besselsimp(P('besselj(a, polar_lift(-I)*z)'))", () => besselsimp(P('besselj(a, polar_lift(-I)*z)')), "exp(-I*pi*a/2)*besseli(a, z)"],
    ["besselsimp(P('besseli(a, polar_lift(2)*z)'))", () => besselsimp(P('besseli(a, polar_lift(2)*z)')), "besseli(a, 2*z*exp_polar(0))"],
    ["besselsimp(P('besselk(a, exp_polar(I*pi)*z)'))", () => besselsimp(P('besselk(a, exp_polar(I*pi)*z)')), "besselk(a, z*exp_polar(I*pi))"],
    ["besselsimp(P('bessely(a, exp_polar(I*pi/2)*z)'))", () => besselsimp(P('bessely(a, exp_polar(I*pi/2)*z)')), "bessely(a, z*exp_polar(I*pi/2))"],
    ["besselsimp(P('besselj(a, exp_polar(I*pi/3)*z)'))", () => besselsimp(P('besselj(a, exp_polar(I*pi/3)*z)')), "besselj(a, z*exp_polar(I*pi/3))"],
    ["besselsimp(P('besselj(a, exp_polar(x)*z)'))", () => besselsimp(P('besselj(a, exp_polar(x)*z)')), "besselj(a, z*exp_polar(x))"],
    ["besselsimp(P('besselj(-5/2, z)'))", () => besselsimp(P('besselj(-5/2, z)')), "-sqrt(2)*(z**2*cos(z) - 3*z*sin(z) - 3*cos(z))/(sqrt(pi)*z**(5/2))"],
    ["besselsimp(P('bessely(-3/2, z)'))", () => besselsimp(P('bessely(-3/2, z)')), "sqrt(2)*(z*cos(z) - sin(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besseli(-5/2, z)'))", () => besselsimp(P('besseli(-5/2, z)')), "sqrt(2)*(z**2*cosh(z) - 3*z*sinh(z) + 3*cosh(z))/(sqrt(pi)*z**(5/2))"],
    ["besselsimp(P('besselk(-5/2, z)'))", () => besselsimp(P('besselk(-5/2, z)')), "sqrt(2)*sqrt(pi)*(z**2 + 3*z + 3)*exp(-z)/(2*z**(5/2))"],
    ["besselsimp(P('bessely(-5/2, z)'))", () => besselsimp(P('bessely(-5/2, z)')), "-sqrt(2)*(z**2*sin(z) + 3*z*cos(z) - 3*sin(z))/(sqrt(pi)*z**(5/2))"],
    ["besselsimp(P('besselj(-3/2, z)'))", () => besselsimp(P('besselj(-3/2, z)')), "-sqrt(2)*(z*sin(z) + cos(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besselk(3, z)'))", () => besselsimp(P('besselk(3, z)')), "(z**2*besselk(1, z) + 4*z*besselk(0, z) + 8*besselk(1, z))/z**2"],
    ["besselsimp(P('bessely(2, z)'))", () => besselsimp(P('bessely(2, z)')), "-(z*bessely(0, z) - 2*bessely(1, z))/z"],
    ["besselsimp(P('besseli(3, z)'))", () => besselsimp(P('besseli(3, z)')), "(z**2*besseli(1, z) - 4*z*besseli(0, z) + 8*besseli(1, z))/z**2"],
    ["besselsimp(P('besselj(a, z)'))", () => besselsimp(P('besselj(a, z)')), "besselj(a, z)"],
    ["besselsimp(P('besselk(5/2, z)'))", () => besselsimp(P('besselk(5/2, z)')), "sqrt(2)*sqrt(pi)*(z**2 + 3*z + 3)*exp(-z)/(2*z**(5/2))"],
    ["besselsimp(P('besselj(1/2, z)*x + 1'))", () => besselsimp(P('besselj(1/2, z)*x + 1')), "(sqrt(2)*x*sin(z) + sqrt(pi)*sqrt(z))/(sqrt(pi)*sqrt(z))"],
    ["besselsimp(P('besseli(3/2, z)'))", () => besselsimp(P('besseli(3/2, z)')), "sqrt(2)*(z*cosh(z) - sinh(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('bessely(3/2, z)'))", () => besselsimp(P('bessely(3/2, z)')), "-sqrt(2)*(z*sin(z) + cos(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besseli(-3/2, z)'))", () => besselsimp(P('besseli(-3/2, z)')), "sqrt(2)*(z*sinh(z) - cosh(z))/(sqrt(pi)*z**(3/2))"],
    ["besselsimp(P('besselj(2, z) + besselj(0, z)'))", () => besselsimp(P('besselj(2, z) + besselj(0, z)')), "2*besselj(1, z)/z"],
    ["besselsimp(P('besselj(1/2, z)'))", () => besselsimp(P('besselj(1/2, z)')), "sqrt(2)*sin(z)/(sqrt(pi)*sqrt(z))"],
    ["besselsimp(P('besselj(3, z)'))", () => besselsimp(P('besselj(3, z)')), "-(z**2*besselj(1, z) + 4*z*besselj(0, z) - 8*besselj(1, z))/z**2"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
