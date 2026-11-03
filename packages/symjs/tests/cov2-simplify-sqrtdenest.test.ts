// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { parse, radsimp, sqrtdenest, symbol } from '../src';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const P = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

const show = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${show(k)}: ${show(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("radsimp, sqrtdenest (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["radsimp(P('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + x*sqrt(7))'))", () => radsimp(P('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + x*sqrt(7))')), "1/(sqrt(7)*x + 1 + sqrt(2) + sqrt(3) + sqrt(5))"],
    ["radsimp(P('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7))'))", () => radsimp(P('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7))')), "(-1173*sqrt(6) - 447*sqrt(35) - 261*sqrt(70) - 652*sqrt(3) - 133*sqrt(30) - 135*sqrt(15) - 117*sqrt(14) - 96*sqrt(7) - 3*sqrt(105) + 789*sqrt(2) + 363*sqrt(10) + 277*sqrt(21) + 243*sqrt(42) + 1734 + 154*sqrt(210) + 1074*sqrt(5))/6054"],
    ["radsimp(P('1/(sqrt(2)*x + sqrt(3)*y + sqrt(5)*z + sqrt(7) + 1)'))", () => radsimp(P('1/(sqrt(2)*x + sqrt(3)*y + sqrt(5)*z + sqrt(7) + 1)')), "1/(sqrt(2)*x + sqrt(3)*y + sqrt(5)*z + 1 + sqrt(7))"],
    ["radsimp(P('1/(x - sqrt(y))'))", () => radsimp(P('1/(x - sqrt(y))')), "(x + sqrt(y))/(x**2 - y)"],
    ["sqrtdenest(P('sqrt(3 + 2*sqrt(3))'))", () => sqrtdenest(P('sqrt(3 + 2*sqrt(3))')), "3**(3/4)*(sqrt(6)/2 + 3*sqrt(2)/2)/3"],
    ["sqrtdenest(P('sqrt(sqrt(2*sqrt(6) + 5) + sqrt(2*sqrt(7) + 8))'))", () => sqrtdenest(P('sqrt(sqrt(2*sqrt(6) + 5) + sqrt(2*sqrt(7) + 8))')), "sqrt(1 + sqrt(2) + sqrt(3) + sqrt(7))"],
    ["sqrtdenest(P('sqrt(x*y)'))", () => sqrtdenest(P('sqrt(x*y)')), "sqrt(x*y)"],
    ["sqrtdenest(P('sqrt(2*(1 + sqrt(2))**3)'))", () => sqrtdenest(P('sqrt(2*(1 + sqrt(2))**3)')), "sqrt(2)*(1 + sqrt(2))**(3/2)"],
    ["sqrtdenest(P('sqrt(2**(1/3) + sqrt(2))'))", () => sqrtdenest(P('sqrt(2**(1/3) + sqrt(2))')), "sqrt(2**(1/3) + sqrt(2))"],
    ["sqrtdenest(P('sqrt(1 + sqrt(2) + 3**(1/3))'))", () => sqrtdenest(P('sqrt(1 + sqrt(2) + 3**(1/3))')), "sqrt(1 + sqrt(2) + 3**(1/3))"],
    ["radsimp(P('1/(1 + 2**sqrt(2))'), { symbolic: false })", () => radsimp(P('1/(1 + 2**sqrt(2))'), { symbolic: false }), "1/(1 + 2**(sqrt(2)))"],
    ["radsimp(P('1/(x + zoo*sqrt(y))'))", () => radsimp(P('1/(x + zoo*sqrt(y))')), "1/(x + zoo*sqrt(y))"],
    ["radsimp(P('1/(sqrt(2) + zoo*sqrt(3))'))", () => radsimp(P('1/(sqrt(2) + zoo*sqrt(3))')), "0"],
    ["sqrtdenest(P('sqrt(1 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(P('sqrt(1 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))')), "sqrt(1 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))"],
    ["sqrtdenest(P('sqrt(5 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(P('sqrt(5 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))')), "sqrt(sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)) + 5)"],
    ["sqrtdenest(P('sqrt(-3 + 2*sqrt(2))'))", () => sqrtdenest(P('sqrt(-3 + 2*sqrt(2))')), "-I + sqrt(2)*I"],
    ["sqrtdenest(P('sqrt(1 - 2*sqrt(2))'))", () => sqrtdenest(P('sqrt(1 - 2*sqrt(2))')), "sqrt(1 - 2*sqrt(2))"],
    ["sqrtdenest(P('sqrt(2*sqrt(3) - 3)'))", () => sqrtdenest(P('sqrt(2*sqrt(3) - 3)')), "3**(3/4)*(-sqrt(6)/2 + 3*sqrt(2)/2)/3"],
    ["sqrtdenest(P('sqrt(sqrt(3) - 1)'))", () => sqrtdenest(P('sqrt(sqrt(3) - 1)')), "sqrt(-1 + sqrt(3))"],
    ["sqrtdenest(P('sqrt(2 - sqrt(3))'))", () => sqrtdenest(P('sqrt(2 - sqrt(3))')), "-sqrt(2)/2 + sqrt(6)/2"],
    ["sqrtdenest(P('sqrt(sqrt(2) - 1)'))", () => sqrtdenest(P('sqrt(sqrt(2) - 1)')), "sqrt(-1 + sqrt(2))"],
    ["sqrtdenest(P('sqrt(4*sqrt(3) - 6)'))", () => sqrtdenest(P('sqrt(4*sqrt(3) - 6)')), "3**(3/4)*(3 - sqrt(3))/3"],
    ["sqrtdenest(P('sqrt(sqrt(5) - 2)'))", () => sqrtdenest(P('sqrt(sqrt(5) - 2)')), "sqrt(-2 + sqrt(5))"],
    ["sqrtdenest(P('sqrt(3*sqrt(2) - 4)'))", () => sqrtdenest(P('sqrt(3*sqrt(2) - 4)')), "2**(3/4)*(2 - sqrt(2))/2"],
    ["sqrtdenest(P('sqrt(2*sqrt(2) - 2)'))", () => sqrtdenest(P('sqrt(2*sqrt(2) - 2)')), "sqrt(-2 + 2*sqrt(2))"],
    ["sqrtdenest(P('sqrt(5 - 2*sqrt(6) + 2*sqrt(2) - 2*sqrt(3))'))", () => sqrtdenest(P('sqrt(5 - 2*sqrt(6) + 2*sqrt(2) - 2*sqrt(3))')), "sqrt(-2*sqrt(6) - 2*sqrt(3) + 2*sqrt(2) + 5)"],
    ["sqrtdenest(P('sqrt(10 - 2*sqrt(5) - 2*sqrt(10) + 2*sqrt(2))'))", () => sqrtdenest(P('sqrt(10 - 2*sqrt(5) - 2*sqrt(10) + 2*sqrt(2))')), "sqrt(-2*sqrt(10) - 2*sqrt(5) + 2*sqrt(2) + 10)"],
    ["sqrtdenest(P('sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6))'))", () => sqrtdenest(P('sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6))')), "sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6))"],
    ["sqrtdenest(P('sqrt(2*sqrt(2) + 3 - sqrt(5 + 2*sqrt(6)))'))", () => sqrtdenest(P('sqrt(2*sqrt(2) + 3 - sqrt(5 + 2*sqrt(6)))')), "sqrt(-sqrt(3) + sqrt(2) + 3)"],
    ["sqrtdenest(P('sqrt(9 - 4*sqrt(2) - 2*sqrt(3) + 2*sqrt(6))'))", () => sqrtdenest(P('sqrt(9 - 4*sqrt(2) - 2*sqrt(3) + 2*sqrt(6))')), "sqrt(-4*sqrt(2) - 2*sqrt(3) + 2*sqrt(6) + 9)"],
    ["sqrtdenest(P('sqrt(1 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) + sqrt(3)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))'))", () => sqrtdenest(P('sqrt(1 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) + sqrt(3)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))')), "sqrt(1 + sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6)) + sqrt(3)*sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6)))"],
    ["sqrtdenest(P('sqrt(2 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) - sqrt(5)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))'))", () => sqrtdenest(P('sqrt(2 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) - sqrt(5)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))')), "sqrt(-sqrt(5)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) + 2 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))"],
    ["sqrtdenest(P('sqrt(2*sqrt(3) + 2*sqrt(5) + 2*sqrt(15) + 20*sqrt(2) + 20*sqrt(6) + 20*sqrt(10) + 209)'))", () => sqrtdenest(P('sqrt(2*sqrt(3) + 2*sqrt(5) + 2*sqrt(15) + 20*sqrt(2) + 20*sqrt(6) + 20*sqrt(10) + 209)')), "1 + sqrt(3) + sqrt(5) + 10*sqrt(2)"],
    ["sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 40*sqrt(2) + 40*sqrt(3) + 40*sqrt(5) + 410)'))", () => sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 40*sqrt(2) + 40*sqrt(3) + 40*sqrt(5) + 410)')), "sqrt(2) + sqrt(3) + sqrt(5) + 20"],
    ["sqrtdenest(P('sqrt(2*sqrt(2) + 2*sqrt(7) + 2*sqrt(14) + 10*sqrt(3) + 10*sqrt(6) + 10*sqrt(21) + 85)'))", () => sqrtdenest(P('sqrt(2*sqrt(2) + 2*sqrt(7) + 2*sqrt(14) + 10*sqrt(3) + 10*sqrt(6) + 10*sqrt(21) + 85)')), "1 + sqrt(2) + sqrt(7) + 5*sqrt(3)"],
    ["sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(14) + 6*sqrt(2) + 2*sqrt(21) + 6*sqrt(3) + 6*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 8*sqrt(35) + 24*sqrt(5) + 101)'))", () => sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(14) + 6*sqrt(2) + 2*sqrt(21) + 6*sqrt(3) + 6*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 8*sqrt(35) + 24*sqrt(5) + 101)')), "sqrt(2) + sqrt(3) + sqrt(7) + 3 + 4*sqrt(5)"],
    ["sqrtdenest(P('sqrt(-2*sqrt(5) - 2*sqrt(3) - 2*sqrt(2) + 2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 11)'))", () => sqrtdenest(P('sqrt(-2*sqrt(5) - 2*sqrt(3) - 2*sqrt(2) + 2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 11)')), "-1 + sqrt(2) + sqrt(3) + sqrt(5)"],
    ["sqrtdenest(P('sqrt(-2*sqrt(21) - 2*sqrt(15) - 2*sqrt(6) - 2*sqrt(3) + 2*sqrt(2) + 2*sqrt(5) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(35) + 18)'))", () => sqrtdenest(P('sqrt(-2*sqrt(21) - 2*sqrt(15) - 2*sqrt(6) - 2*sqrt(3) + 2*sqrt(2) + 2*sqrt(5) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(35) + 18)')), "-sqrt(3) + 1 + sqrt(2) + sqrt(5) + sqrt(7)"],
    ["sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 17)'))", () => sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 17)')), "sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7)"],
    ["sqrtdenest(P('sqrt(4*sqrt(3) + 2*sqrt(33) + 4*sqrt(11) + 6*sqrt(6) + 12*sqrt(2) + 6*sqrt(22) + 36)'))", () => sqrtdenest(P('sqrt(4*sqrt(3) + 2*sqrt(33) + 4*sqrt(11) + 6*sqrt(6) + 12*sqrt(2) + 6*sqrt(22) + 36)')), "sqrt(3) + 2 + sqrt(11) + 3*sqrt(2)"],
    ["sqrtdenest(P('sqrt(-7*sqrt(10) - 3*sqrt(21) - 3*sqrt(7) - 3*sqrt(5) + 18)'))", () => sqrtdenest(P('sqrt(-7*sqrt(10) - 3*sqrt(21) - 3*sqrt(7) - 3*sqrt(5) + 18)')), "sqrt(-7*sqrt(10) - 3*sqrt(21) - 3*sqrt(7) - 3*sqrt(5) + 18)"],
    ["sqrtdenest(P('sqrt(-sqrt(15) + 2*sqrt(21) + 9*sqrt(7) + 27)'))", () => sqrtdenest(P('sqrt(-sqrt(15) + 2*sqrt(21) + 9*sqrt(7) + 27)')), "sqrt(-sqrt(15) + 2*sqrt(21) + 9*sqrt(7) + 27)"],
    ["sqrtdenest(P('sqrt(-3*sqrt(35) - 3*sqrt(7) + 9*sqrt(2) + 36)'))", () => sqrtdenest(P('sqrt(-3*sqrt(35) - 3*sqrt(7) + 9*sqrt(2) + 36)')), "sqrt(-3*sqrt(35) - 3*sqrt(7) + 9*sqrt(2) + 36)"],
    ["sqrtdenest(P('sqrt(-7*sqrt(6) - sqrt(21) + 9 + 5*sqrt(10) + 9*sqrt(14) + 9*sqrt(15))'))", () => sqrtdenest(P('sqrt(-7*sqrt(6) - sqrt(21) + 9 + 5*sqrt(10) + 9*sqrt(14) + 9*sqrt(15))')), "sqrt(-7*sqrt(6) - sqrt(21) + 9 + 5*sqrt(10) + 9*sqrt(14) + 9*sqrt(15))"],
    ["sqrtdenest(P('sqrt(-3*sqrt(10) - 6 + 2*sqrt(6) + 2*sqrt(15))'))", () => sqrtdenest(P('sqrt(-3*sqrt(10) - 6 + 2*sqrt(6) + 2*sqrt(15))')), "sqrt(-3*sqrt(10) - 6 + 2*sqrt(6) + 2*sqrt(15))"],
    ["sqrtdenest(P('sqrt(10 - 4*sqrt(-1 + sqrt(7)))'))", () => sqrtdenest(P('sqrt(10 - 4*sqrt(-1 + sqrt(7)))')), "-sqrt(14)*sqrt(-1 + sqrt(7))*sqrt(8 + 4*sqrt(7))/6 + sqrt(2)*sqrt(-1 + sqrt(7))*sqrt(8 + 4*sqrt(7))/3 + sqrt(2)*sqrt(8 + 4*sqrt(7))/2"],
    ["sqrtdenest(P('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) - 12*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(P('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) - 12*sqrt(1 + sqrt(2)))')), "-sqrt(7) + 1 + sqrt(1 + sqrt(2)) + sqrt(7)*sqrt(1 + sqrt(2))"],
    ["sqrtdenest(P('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) + 12*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(P('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) + 12*sqrt(1 + sqrt(2)))')), "-1 + sqrt(1 + sqrt(2)) + sqrt(7) + sqrt(7)*sqrt(1 + sqrt(2))"],
    ["sqrtdenest(P('sqrt(-4*sqrt(70)*sqrt(2 + sqrt(6)) - 8*sqrt(10)*sqrt(2 + sqrt(6)) - 2*sqrt(7)*sqrt(2 + sqrt(6)) - 4*sqrt(2 + sqrt(6)) + 4*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 93 + 41*sqrt(6))'))", () => sqrtdenest(P('sqrt(-4*sqrt(70)*sqrt(2 + sqrt(6)) - 8*sqrt(10)*sqrt(2 + sqrt(6)) - 2*sqrt(7)*sqrt(2 + sqrt(6)) - 4*sqrt(2 + sqrt(6)) + 4*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 93 + 41*sqrt(6))')), "-sqrt(7) - 2 + sqrt(2 + sqrt(6)) + 2*sqrt(10)*sqrt(2 + sqrt(6))"],
    ["sqrtdenest(P('sqrt(-126*sqrt(3) - 12*sqrt(6)*sqrt(-2 + 3*sqrt(6)) - 38 - 10*sqrt(-2 + 3*sqrt(6)) + 4*sqrt(2)*sqrt(-2 + 3*sqrt(6)) + 40*sqrt(2) + 30*sqrt(3)*sqrt(-2 + 3*sqrt(6)) + 99*sqrt(6))'))", () => sqrtdenest(P('sqrt(-126*sqrt(3) - 12*sqrt(6)*sqrt(-2 + 3*sqrt(6)) - 38 - 10*sqrt(-2 + 3*sqrt(6)) + 4*sqrt(2)*sqrt(-2 + 3*sqrt(6)) + 40*sqrt(2) + 30*sqrt(3)*sqrt(-2 + 3*sqrt(6)) + 99*sqrt(6))')), "-2*sqrt(2)*sqrt(-2 + 3*sqrt(6)) - 1 + 3*sqrt(3) + 5*sqrt(-2 + 3*sqrt(6))"],
    ["sqrtdenest(P('sqrt(-188*sqrt(15) - 40*sqrt(15)*sqrt(2 + 3*sqrt(6)) - 20*sqrt(6)*sqrt(2 + 3*sqrt(6)) + 4*sqrt(10) + 33*sqrt(6) + 10*sqrt(10)*sqrt(2 + 3*sqrt(6)) + 100*sqrt(2 + 3*sqrt(6)) + 872)'))", () => sqrtdenest(P('sqrt(-188*sqrt(15) - 40*sqrt(15)*sqrt(2 + 3*sqrt(6)) - 20*sqrt(6)*sqrt(2 + 3*sqrt(6)) + 4*sqrt(10) + 33*sqrt(6) + 10*sqrt(10)*sqrt(2 + 3*sqrt(6)) + 100*sqrt(2 + 3*sqrt(6)) + 872)')), "-10*sqrt(6) + sqrt(2 + 3*sqrt(6)) + sqrt(10)*sqrt(2 + 3*sqrt(6)) + 5*sqrt(10)"],
    ["sqrtdenest(P('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) + 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))'))", () => sqrtdenest(P('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) + 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))')), "-2**(1/4) + 2**(3/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2))/2 + 2**(1/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2)) + 2**(3/4)"],
    ["sqrtdenest(P('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) - 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))'))", () => sqrtdenest(P('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) - 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))')), "-2**(1/4) - 2**(1/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2)) - 2**(3/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2))/2 + 2**(3/4)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});
