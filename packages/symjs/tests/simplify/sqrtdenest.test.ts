// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/sqrtdenest.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { parse, radsimp, sqrtdenest, sstr, symbol } from '../../src';
import type { Expr } from '../../src';

const P = parse;
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe('sqrtdenest and radsimp (SymPy ports)', () => {
  it('denest and rationalize like SymPy', async () => {
    const { sqrtdenest, radsimp, sqrt: rt, expand: ex } = await import('../../src');
    const sd = (s: string) => sstr(sqrtdenest(parse(s)));
    expect(sd('sqrt(1+sqrt(3)) + sqrt(3+3*sqrt(3)) - sqrt(10+6*sqrt(3))')).toBe('0');
    expect(sstr(sqrtdenest(rt(ex(parse('(1 + sqrt(2) + sqrt(1+sqrt(1+sqrt(3))))**2')))))).toBe('1 + sqrt(2) + sqrt(1 + sqrt(1 + sqrt(3)))');
    expect(['sqrt(5 + 2*sqrt(6))', 'sqrt(3 + 2*sqrt(2))', 'sqrt(x + 2*sqrt(x - 1))', 'sqrt(4 + 2*sqrt(3)) / 2'].map(sd)).toEqual(['sqrt(2) + sqrt(3)', '1 + sqrt(2)', 'sqrt(x + 2*sqrt(x - 1))', '1/2 + sqrt(3)/2']);
    const rs = (s: string, o = {}) => sstr(radsimp(parse(s), o));
    expect(['1/(sqrt(2) + sqrt(3))', '1/(1 + sqrt(2) + sqrt(3))', '1/(a + b*sqrt(c))', '1/(2 + sqrt(2))'].map((s) => rs(s))).toEqual([
      '-sqrt(2) + sqrt(3)', '(-sqrt(6) + sqrt(2) + 2)/4', '(a - b*sqrt(c))/(a**2 - b**2*c)', '(2 - sqrt(2))/2',
    ]);
    expect(rs('1/(a + b*sqrt(c))', { symbolic: false })).toBe('1/(a + b*sqrt(c))');
  });
});

describe("radsimp: SymPy 1.14 test_radsimp cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["radsimp(P(\"1/(x + sqrt(x**2))\"))", () => radsimp(P("1/(x + sqrt(x**2))")), "1/(x + sqrt(x**2))"],
    ["radsimp(P(\"1/(x - sqrt(x**2))\"))", () => radsimp(P("1/(x - sqrt(x**2))")), "1/(x - sqrt(x**2))"],
    ["radsimp(P(\"0\"))", () => radsimp(P("0")), "0"],
    ["radsimp(P(\"sqrt(2)/2\"))", () => radsimp(P("sqrt(2)/2")), "sqrt(2)/2"],
    ["radsimp(P(\"1/(1 + sqrt(2))\"))", () => radsimp(P("1/(1 + sqrt(2))")), "-1 + sqrt(2)"],
    ["radsimp(P(\"1/(sqrt(2) + sqrt(3))\"))", () => radsimp(P("1/(sqrt(2) + sqrt(3))")), "-sqrt(2) + sqrt(3)"],
    ["radsimp(P(\"1/(1 + sqrt(2) + sqrt(3))\"))", () => radsimp(P("1/(1 + sqrt(2) + sqrt(3))")), "(-sqrt(6) + sqrt(2) + 2)/4"],
    ["radsimp(P(\"1/(sqrt(2) + sqrt(3) + sqrt(5))\"))", () => radsimp(P("1/(sqrt(2) + sqrt(3) + sqrt(5))")), "(-sqrt(30) + 2*sqrt(3) + 3*sqrt(2))/12"],
    ["radsimp(P(\"1/(1 + sqrt(2) + sqrt(3) + sqrt(5))\"))", () => radsimp(P("1/(1 + sqrt(2) + sqrt(3) + sqrt(5))")), "(-34*sqrt(10) - 26*sqrt(15) - 55*sqrt(3) - 61*sqrt(2) + 14*sqrt(30) + 93 + 46*sqrt(6) + 53*sqrt(5))/71"],
    ["radsimp(P(\"1/(sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7))\"))", () => radsimp(P("1/(sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7))")), "(-50*sqrt(42) - 133*sqrt(5) - 34*sqrt(70) - 145*sqrt(3) + 22*sqrt(105) + 185*sqrt(2) + 62*sqrt(30) + 135*sqrt(7))/215"],
    ["radsimp(P(\"1/(sqrt(3)/5 + sqrt(2)/3 + 1 + sqrt(5) + sqrt(7))\"))", () => radsimp(P("1/(sqrt(3)/5 + sqrt(2)/3 + 1 + sqrt(5) + sqrt(7))")), "(-326496380596051503375*sqrt(30) - 341088259408534978875*sqrt(21) - 603619879047466953375*sqrt(6) - 341184673220817886875*sqrt(14) - 107675381124879253875*sqrt(105) - 145120979312871316875*sqrt(35) - 85727228358129136875*sqrt(70) - 198657819486933406650*sqrt(5) + 447825030704717632575*sqrt(2) + 692178787976537795850 + 601005529137115927080*sqrt(3) + 465535513046818367100*sqrt(7) + 414382669322128363125*sqrt(10) + 101504820046292943750*sqrt(210) + 410117956365126533625*sqrt(15) + 278028799929677471625*sqrt(42))/3616791619821680643598"],
    ["radsimp(P(\"3616791619821680643598/(-326496380596051503375*sqrt(30) - 341088259408534978875*sqrt(21) - 603619879047466953375*sqrt(6) - 341184673220817886875*sqrt(14) - 107675381124879253875*sqrt(105) - 145120979312871316875*sqrt(35) - 85727228358129136875*sqrt(70) - 198657819486933406650*sqrt(5) + 447825030704717632575*sqrt(2) + 692178787976537795850 + 601005529137115927080*sqrt(3) + 465535513046818367100*sqrt(7) + 414382669322128363125*sqrt(10) + 101504820046292943750*sqrt(210) + 410117956365126533625*sqrt(15) + 278028799929677471625*sqrt(42))\"))", () => radsimp(P("3616791619821680643598/(-326496380596051503375*sqrt(30) - 341088259408534978875*sqrt(21) - 603619879047466953375*sqrt(6) - 341184673220817886875*sqrt(14) - 107675381124879253875*sqrt(105) - 145120979312871316875*sqrt(35) - 85727228358129136875*sqrt(70) - 198657819486933406650*sqrt(5) + 447825030704717632575*sqrt(2) + 692178787976537795850 + 601005529137115927080*sqrt(3) + 465535513046818367100*sqrt(7) + 414382669322128363125*sqrt(10) + 101504820046292943750*sqrt(210) + 410117956365126533625*sqrt(15) + 278028799929677471625*sqrt(42))")), "3616791619821680643598/(-326496380596051503375*sqrt(30) - 341088259408534978875*sqrt(21) - 603619879047466953375*sqrt(6) - 341184673220817886875*sqrt(14) - 107675381124879253875*sqrt(105) - 145120979312871316875*sqrt(35) - 85727228358129136875*sqrt(70) - 198657819486933406650*sqrt(5) + 447825030704717632575*sqrt(2) + 692178787976537795850 + 601005529137115927080*sqrt(3) + 465535513046818367100*sqrt(7) + 414382669322128363125*sqrt(10) + 101504820046292943750*sqrt(210) + 410117956365126533625*sqrt(15) + 278028799929677471625*sqrt(42))"],
    ["radsimp(P(\"3616791619821680643598/(-326496380596051503375*sqrt(30) - 341088259408534978875*sqrt(21) - 603619879047466953375*sqrt(6) - 341184673220817886875*sqrt(14) - 107675381124879253875*sqrt(105) - 145120979312871316875*sqrt(35) - 85727228358129136875*sqrt(70) - 198657819486933406650*sqrt(5) + 447825030704717632575*sqrt(2) + 692178787976537795850 + 601005529137115927080*sqrt(3) + 465535513046818367100*sqrt(7) + 414382669322128363125*sqrt(10) + 101504820046292943750*sqrt(210) + 410117956365126533625*sqrt(15) + 278028799929677471625*sqrt(42))\"), { maxTerms: 20 })", () => radsimp(P("3616791619821680643598/(-326496380596051503375*sqrt(30) - 341088259408534978875*sqrt(21) - 603619879047466953375*sqrt(6) - 341184673220817886875*sqrt(14) - 107675381124879253875*sqrt(105) - 145120979312871316875*sqrt(35) - 85727228358129136875*sqrt(70) - 198657819486933406650*sqrt(5) + 447825030704717632575*sqrt(2) + 692178787976537795850 + 601005529137115927080*sqrt(3) + 465535513046818367100*sqrt(7) + 414382669322128363125*sqrt(10) + 101504820046292943750*sqrt(210) + 410117956365126533625*sqrt(15) + 278028799929677471625*sqrt(42))"), { maxTerms: 20 }), "(3*sqrt(3) + 5*sqrt(2) + 15 + 15*sqrt(5) + 15*sqrt(7))/15"],
    ["radsimp(P(\"sqrt(2)/6\"))", () => radsimp(P("sqrt(2)/6")), "sqrt(2)/6"],
    ["radsimp(P(\"1/(sqrt(2)*a + sqrt(2)*b + sqrt(2)*c + sqrt(2)*d)\"))", () => radsimp(P("1/(sqrt(2)*a + sqrt(2)*b + sqrt(2)*c + sqrt(2)*d)")), "sqrt(2)/(2*a + 2*b + 2*c + 2*d)"],
    ["radsimp(P(\"(-x + y**2)/(-sqrt(x) + y)\"))", () => radsimp(P("(-x + y**2)/(-sqrt(x) + y)")), "sqrt(x) + y"],
    ["radsimp(P(\"x*(3 + 3*sqrt(2))*(3*x - 3*sqrt(y))\"))", () => radsimp(P("x*(3 + 3*sqrt(2))*(3*x - 3*sqrt(y))")), "x*(3 + 3*sqrt(2))*(3*x - 3*sqrt(y))"],
    ["radsimp(P(\"1/(1 + sqrt(3)) + 1\"))", () => radsimp(P("1/(1 + sqrt(3)) + 1")), "(-1 + sqrt(3))/2 + 1"],
    ["radsimp(P(\"1/sqrt(2*sqrt(6) + 5)\"))", () => radsimp(P("1/sqrt(2*sqrt(6) + 5)")), "-sqrt(2) + sqrt(3)"],
    ["radsimp(P(\"(-4*2**(1/4) - 2*sqrt(2) - 2)/(1 + 2**(3/4) + 3*2**(1/4) + 3*sqrt(2))\"))", () => radsimp(P("(-4*2**(1/4) - 2*sqrt(2) - 2)/(1 + 2**(3/4) + 3*2**(1/4) + 3*sqrt(2))")), "-2*2**(3/4) - 2*2**(1/4) + 2 + 2*sqrt(2)"],
    ["radsimp(P(\"1/(-sqrt(5)/2 - 1/2 + (-sqrt(5)/2 - 1/2)**2)\"))", () => radsimp(P("1/(-sqrt(5)/2 - 1/2 + (-sqrt(5)/2 - 1/2)**2)")), "1"],
    ["radsimp(P(\"(-sqrt(3) + sqrt(2))**(-x)\"))", () => radsimp(P("(-sqrt(3) + sqrt(2))**(-x)")), "(-sqrt(3) + sqrt(2))**(-x)"],
    ["radsimp(P(\"x/(y + 1 + sqrt(2))\"), { symbolic: false })", () => radsimp(P("x/(y + 1 + sqrt(2))"), { symbolic: false }), "x/(y + 1 + sqrt(2))"],
    ["radsimp(P(\"sqrt(x)/sqrt(y)\"), { symbolic: false })", () => radsimp(P("sqrt(x)/sqrt(y)"), { symbolic: false }), "sqrt(x)/sqrt(y)"],
    ["radsimp(P(\"sqrt(x)/y**(3/2)\"))", () => radsimp(P("sqrt(x)/y**(3/2)")), "sqrt(x)*sqrt(y**3)/y**3"],
    ["radsimp(P(\"sqrt(x)/y**2\"))", () => radsimp(P("sqrt(x)/y**2")), "sqrt(x)/y**2"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe('radsimp: a denominator that vanishes when rationalized', () => {
  it('keeps the input (SymPy 1.14 returns it unchanged)', () => {
    // (x + sqrt(x**2))*(x - sqrt(x**2)) = 0: multiplying through would give zoo
    expect(radsimp(P('1/(x + sqrt(x**2))')).toString()).toBe('1/(x + sqrt(x**2))');
    expect(radsimp(P('1/(x - sqrt(x**2))')).toString()).toBe('1/(x - sqrt(x**2))');
  });
});

describe("sqrtdenest: SymPy 1.14 test_sqrtdenest cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["sqrtdenest(P(\"I\"))", () => sqrtdenest(P("I")), "I"],
    ["sqrtdenest(P(\"3 - sqrt(2)*sqrt(4 + I) + 3*I\"))", () => sqrtdenest(P("3 - sqrt(2)*sqrt(4 + I) + 3*I")), "3 - sqrt(2)*sqrt(4 + I) + 3*I"],
    ["sqrtdenest(P(\"-sqrt(-2 + 2*sqrt(3)*I)\"))", () => sqrtdenest(P("-sqrt(-2 + 2*sqrt(3)*I)")), "-1 - sqrt(3)*I"],
    ["sqrtdenest(P(\"sqrt(-8 - 3*sqrt(7))\"))", () => sqrtdenest(P("sqrt(-8 - 3*sqrt(7))")), "sqrt(14)*I/2 + 3*sqrt(2)*I/2"],
    ["sqrtdenest(P(\"sqrt(sqrt(sqrt(2) + 2) + 2)\"))", () => sqrtdenest(P("sqrt(sqrt(sqrt(2) + 2) + 2)")), "sqrt(sqrt(sqrt(2) + 2) + 2)"],
    ["sqrtdenest(P(\"x + sqrt(y)\"))", () => sqrtdenest(P("x + sqrt(y)")), "x + sqrt(y)"],
    ["sqrtdenest(P(\"sqrt(-320 + 32*sqrt(5) + 64*sqrt(15))\"))", () => sqrtdenest(P("sqrt(-320 + 32*sqrt(5) + 64*sqrt(15))")), "sqrt(-320 + 32*sqrt(5) + 64*sqrt(15))"],
    ["sqrtdenest(P(\"-sqrt(10 + 6*sqrt(3)) + sqrt(1 + sqrt(3)) + sqrt(3 + 3*sqrt(3))\"))", () => sqrtdenest(P("-sqrt(10 + 6*sqrt(3)) + sqrt(1 + sqrt(3)) + sqrt(3 + 3*sqrt(3))")), "0"],
    ["sqrtdenest(P(\"sqrt(sqrt(x + 2) + 2*sqrt(sqrt(x + 2) + 3) + 4)\"))", () => sqrtdenest(P("sqrt(sqrt(x + 2) + 2*sqrt(sqrt(x + 2) + 3) + 4)")), "sqrt((sqrt(sqrt(x + 2) + 3) + 1)**2)"],
    ["sqrtdenest(P(\"4*cos(2) + 4*cos(2)**3 + cos(2)**4 + 6*cos(2)**2 + 2\"))", () => sqrtdenest(P("4*cos(2) + 4*cos(2)**3 + cos(2)**4 + 6*cos(2)**2 + 2")), "4*cos(2) + 4*cos(2)**3 + cos(2)**4 + 6*cos(2)**2 + 2"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(sqrt(cos(3*x) + 2) + 3) + sqrt(cos(3*x) + 2) + 5)\"))", () => sqrtdenest(P("sqrt(2*sqrt(sqrt(cos(3*x) + 2) + 3) + sqrt(cos(3*x) + 2) + 5)")), "sqrt(2*sqrt(sqrt(cos(3*x) + 2) + 3) + sqrt(cos(3*x) + 2) + 5)"],
    ["sqrtdenest(P(\"sqrt(20*sqrt(1 + sqrt(3))*sqrt(3 + 3*sqrt(3)) + 12*sqrt(3)*sqrt(1 + sqrt(3))*sqrt(3 + 3*sqrt(3)) + 64*sqrt(3) + 112)\"))", () => sqrtdenest(P("sqrt(20*sqrt(1 + sqrt(3))*sqrt(3 + 3*sqrt(3)) + 12*sqrt(3)*sqrt(1 + sqrt(3))*sqrt(3 + 3*sqrt(3)) + 64*sqrt(3) + 112)")), "sqrt(20*sqrt(1 + sqrt(3))*sqrt(3 + 3*sqrt(3)) + 12*sqrt(3)*sqrt(1 + sqrt(3))*sqrt(3 + 3*sqrt(3)) + 64*sqrt(3) + 112)"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(6) + 5)\"))", () => sqrtdenest(P("sqrt(2*sqrt(6) + 5)")), "sqrt(2) + sqrt(3)"],
    ["sqrtdenest(P(\"2**(1/4)\"))", () => sqrtdenest(P("2**(1/4)")), "2**(1/4)"],
    ["sqrtdenest(P(\"sqrt(sqrt(7) + 5)\"))", () => sqrtdenest(P("sqrt(sqrt(7) + 5)")), "sqrt(sqrt(7) + 5)"],
    ["sqrtdenest(P(\"sqrt(3 + sqrt(5 + 2*sqrt(7)))\"))", () => sqrtdenest(P("sqrt(3 + sqrt(5 + 2*sqrt(7)))")), "3*sqrt(2)*(5 + 2*sqrt(7))**(1/4)/(2*sqrt(6 + 3*sqrt(7))) + sqrt(2)*sqrt(6 + 3*sqrt(7))/(2*(5 + 2*sqrt(7))**(1/4))"],
    ["sqrtdenest(P(\"sqrt(3 + 2*sqrt(3))\"))", () => sqrtdenest(P("sqrt(3 + 2*sqrt(3))")), "3**(3/4)*(sqrt(6)/2 + 3*sqrt(2)/2)/3"],
    ["sqrtdenest(P(\"sqrt(1 + sqrt(1 + sqrt(7)))\"))", () => sqrtdenest(P("sqrt(1 + sqrt(1 + sqrt(7)))")), "sqrt(1 + sqrt(1 + sqrt(7)))"],
    ["sqrtdenest(P(\"sqrt(2 + 2*sqrt(1 + 2*sqrt(sqrt(2) + sqrt(5) + 3)) + 2*sqrt(sqrt(2) + sqrt(5) + 3))\"))", () => sqrtdenest(P("sqrt(2 + 2*sqrt(1 + 2*sqrt(sqrt(2) + sqrt(5) + 3)) + 2*sqrt(sqrt(2) + sqrt(5) + 3))")), "1 + sqrt(1 + 2*sqrt(sqrt(2) + sqrt(5) + 3))"],
    ["sqrtdenest(P(\"sqrt(6*sqrt(2) + 5*sqrt(3))\"))", () => sqrtdenest(P("sqrt(6*sqrt(2) + 5*sqrt(3))")), "sqrt(2)*3**(1/4) + 3**(3/4)"],
    ["sqrtdenest(P(\"sqrt(sqrt(3) + 2*sqrt(1 + sqrt(3)) + 2*sqrt(5) + 7 + 2*sqrt(5)*sqrt(1 + sqrt(3)))\"))", () => sqrtdenest(P("sqrt(sqrt(3) + 2*sqrt(1 + sqrt(3)) + 2*sqrt(5) + 7 + 2*sqrt(5)*sqrt(1 + sqrt(3)))")), "1 + sqrt(1 + sqrt(3)) + sqrt(5)"],
    ["sqrtdenest(P(\"sqrt(sqrt(3) + 2*sqrt(1 + sqrt(3)) + 2*sqrt(5) + 2*sqrt(7) + 2*sqrt(5)*sqrt(1 + sqrt(3)) + 2*sqrt(7)*sqrt(1 + sqrt(3)) + 2*sqrt(35) + 14)\"))", () => sqrtdenest(P("sqrt(sqrt(3) + 2*sqrt(1 + sqrt(3)) + 2*sqrt(5) + 2*sqrt(7) + 2*sqrt(5)*sqrt(1 + sqrt(3)) + 2*sqrt(7)*sqrt(1 + sqrt(3)) + 2*sqrt(35) + 14)")), "1 + sqrt(1 + sqrt(3)) + sqrt(5) + sqrt(7)"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(1 + sqrt(3))*cos(3) + 2*cos(3) + 2*sqrt(1 + sqrt(3))*cos(2) + 2*cos(2) + cos(2)**2 + 2*cos(2)*cos(3) + cos(3)**2 + sqrt(3) + 2 + 2*sqrt(1 + sqrt(3)))\"))", () => sqrtdenest(P("sqrt(2*sqrt(1 + sqrt(3))*cos(3) + 2*cos(3) + 2*sqrt(1 + sqrt(3))*cos(2) + 2*cos(2) + cos(2)**2 + 2*cos(2)*cos(3) + cos(3)**2 + sqrt(3) + 2 + 2*sqrt(1 + sqrt(3)))")), "cos(3) + cos(2) + 1 + sqrt(1 + sqrt(3))"],
    ["sqrtdenest(P(\"sqrt(-2*sqrt(10) + 2*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 14)\"))", () => sqrtdenest(P("sqrt(-2*sqrt(10) + 2*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 14)")), "sqrt(-2*sqrt(10) - 2*sqrt(2) + 4*sqrt(5) + 14)"],
    ["sqrtdenest(P(\"sqrt(-2*sqrt(29) + cos(2) + 2*sqrt(55 - 10*sqrt(29)) + 16)\"))", () => sqrtdenest(P("sqrt(-2*sqrt(29) + cos(2) + 2*sqrt(55 - 10*sqrt(29)) + 16)")), "sqrt(-2*sqrt(29) + cos(2) + 2*sqrt(55 - 10*sqrt(29)) + 16)"],
    ["sqrtdenest(P(\"sqrt(sqrt(6) + sqrt(15))\"))", () => sqrtdenest(P("sqrt(sqrt(6) + sqrt(15))")), "sqrt(sqrt(6) + sqrt(15))"],
    ["sqrtdenest(P(\"sqrt(-2*sqrt(31) + 2*sqrt(55 - 10*sqrt(29)) + 15)\"))", () => sqrtdenest(P("sqrt(-2*sqrt(31) + 2*sqrt(55 - 10*sqrt(29)) + 15)")), "sqrt(-2*sqrt(31) + 2*sqrt(55 - 10*sqrt(29)) + 15)"],
    ["sqrtdenest(P(\"sqrt(-2*sqrt(10) + 2*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 13)\"))", () => sqrtdenest(P("sqrt(-2*sqrt(10) + 2*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 13)")), "-1 + sqrt(2) + sqrt(10)"],
    ["sqrtdenest(P(\"sqrt(-2*sqrt(10) + 2*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 13)\"), 1)", () => sqrtdenest(P("sqrt(-2*sqrt(10) + 2*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 13)"), 1), "-1 + sqrt(2) + sqrt(10)"],
    ["sqrtdenest(P(\"sqrt(-2*sqrt(10) + 4*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 20)\"))", () => sqrtdenest(P("sqrt(-2*sqrt(10) + 4*sqrt(2)*sqrt(11 - 2*sqrt(10)) + 20)")), "sqrt(-2*sqrt(10) - 4*sqrt(2) + 8*sqrt(5) + 20)"],
    ["sqrtdenest(P(\"sqrt(70*sqrt(2) + 112 + sqrt(5)*(46 + 34*sqrt(2)))\"))", () => sqrtdenest(P("sqrt(70*sqrt(2) + 112 + sqrt(5)*(46 + 34*sqrt(2)))")), "sqrt(10) + 5 + 4*sqrt(2) + 3*sqrt(5)"],
    ["sqrtdenest(P(\"sqrt(-sqrt(3)*(1 + sqrt(5)) - sqrt(2)*sqrt(5 - sqrt(5)) + 8)\"))", () => sqrtdenest(P("sqrt(-sqrt(3)*(1 + sqrt(5)) - sqrt(2)*sqrt(5 - sqrt(5)) + 8)")), "-sqrt(15)*sqrt(5 - sqrt(5))/4 - sqrt(3)*sqrt(5 - sqrt(5))/4 - sqrt(6)/4 - sqrt(2)/4 + sqrt(5 - sqrt(5))/4 + sqrt(10)/4 + sqrt(5)*sqrt(5 - sqrt(5))/4 + sqrt(30)/4"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(2)*sqrt(sqrt(2) + 2) + 5*sqrt(2) + 4*sqrt(sqrt(2) + 2) + 8)\"))", () => sqrtdenest(P("sqrt(2*sqrt(2)*sqrt(sqrt(2) + 2) + 5*sqrt(2) + 4*sqrt(sqrt(2) + 2) + 8)")), "sqrt(2) + sqrt(sqrt(2) + 2) + 2"],
    ["sqrtdenest(P(\"sqrt(4*sqrt(6) + 2*sqrt(2)*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 8*sqrt(2) + 2*sqrt(6)*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 10*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 6*sqrt(3)*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 47 + 28*sqrt(3))\"))", () => sqrtdenest(P("sqrt(4*sqrt(6) + 2*sqrt(2)*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 8*sqrt(2) + 2*sqrt(6)*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 10*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 6*sqrt(3)*sqrt(sqrt(2) + 2 + 5*sqrt(3)) + 47 + 28*sqrt(3))")), "sqrt(2) + sqrt(3) + 2 + sqrt(sqrt(2) + 2 + 5*sqrt(3)) + sqrt(3)*sqrt(sqrt(2) + 2 + 5*sqrt(3))"],
    ["sqrtdenest(P(\"sqrt(-4*sqrt(14) - 2*sqrt(6) + 4*sqrt(21) + 33)\"))", () => sqrtdenest(P("sqrt(-4*sqrt(14) - 2*sqrt(6) + 4*sqrt(21) + 33)")), "-sqrt(2) + sqrt(3) + 2*sqrt(7)"],
    ["sqrtdenest(P(\"sqrt(-28*sqrt(7) - 14*sqrt(5) + 4*sqrt(35) + 82)\"))", () => sqrtdenest(P("sqrt(-28*sqrt(7) - 14*sqrt(5) + 4*sqrt(35) + 82)")), "-7 + sqrt(5) + 2*sqrt(7)"],
    ["sqrtdenest(P(\"sqrt(468*sqrt(3) + 3024*sqrt(2) + 2912*sqrt(6) + 19735)\"))", () => sqrtdenest(P("sqrt(468*sqrt(3) + 3024*sqrt(2) + 2912*sqrt(6) + 19735)")), "9*sqrt(3) + 26 + 56*sqrt(6)"],
    ["sqrtdenest(P(\"sqrt(-2107 - 98*sqrt(345) - 98*sqrt(115) - 490*sqrt(3))\"))", () => sqrtdenest(P("sqrt(-2107 - 98*sqrt(345) - 98*sqrt(115) - 490*sqrt(3))")), "I*(7*sqrt(5) + 7*sqrt(15) + 7*sqrt(23))"],
    ["sqrtdenest(P(\"sqrt(-4*sqrt(14) - 2*sqrt(6) + 4*sqrt(21) + 34)\"))", () => sqrtdenest(P("sqrt(-4*sqrt(14) - 2*sqrt(6) + 4*sqrt(21) + 34)")), "sqrt(-4*sqrt(14) - 2*sqrt(6) + 4*sqrt(21) + 34)"],
    ["sqrtdenest(P(\"sqrt(-8*sqrt(2) - 2*sqrt(5) + 18)\"))", () => sqrtdenest(P("sqrt(-8*sqrt(2) - 2*sqrt(5) + 18)")), "-sqrt(10) + 1 + sqrt(2) + sqrt(5)"],
    ["sqrtdenest(P(\"sqrt(-18 + 2*sqrt(5) + 8*sqrt(2))\"))", () => sqrtdenest(P("sqrt(-18 + 2*sqrt(5) + 8*sqrt(2))")), "I*(-sqrt(10) + 1 + sqrt(2) + sqrt(5))"],
    ["sqrtdenest(P(\"sqrt(8*sqrt(2)/3 + 14*sqrt(5)/3 + 154/9)\"))", () => sqrtdenest(P("sqrt(8*sqrt(2)/3 + 14*sqrt(5)/3 + 154/9)")), "-sqrt(10)/3 + sqrt(2) + sqrt(5) + 3"],
    ["sqrtdenest(P(\"sqrt(sqrt(2*sqrt(6) + 5) + sqrt(2*sqrt(7) + 8))\"))", () => sqrtdenest(P("sqrt(sqrt(2*sqrt(6) + 5) + sqrt(2*sqrt(7) + 8))")), "sqrt(1 + sqrt(2) + sqrt(3) + sqrt(7))"],
    ["sqrtdenest(P(\"sqrt(4*sqrt(15) + 8*sqrt(5) + 12*sqrt(3) + 24)\"))", () => sqrtdenest(P("sqrt(4*sqrt(15) + 8*sqrt(5) + 12*sqrt(3) + 24)")), "1 + sqrt(3) + sqrt(5) + sqrt(15)"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(2) + 2*sqrt(3) + 2*sqrt(5) + 2*sqrt(6) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 18)\"))", () => sqrtdenest(P("sqrt(2*sqrt(2) + 2*sqrt(3) + 2*sqrt(5) + 2*sqrt(6) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 18)")), "1 + sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7)"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(2) + 2*sqrt(3) + 2*sqrt(5) + 2*sqrt(6) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 19)\"))", () => sqrtdenest(P("sqrt(2*sqrt(2) + 2*sqrt(3) + 2*sqrt(5) + 2*sqrt(6) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 19)")), "sqrt(2*sqrt(2) + 2*sqrt(3) + 2*sqrt(5) + 2*sqrt(6) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 19)"],
    ["sqrtdenest(P(\"sqrt(2*sqrt(10) + 6*sqrt(2) + 4*sqrt(5) + 12 + 10*sqrt(15) + 30*sqrt(3))\"))", () => sqrtdenest(P("sqrt(2*sqrt(10) + 6*sqrt(2) + 4*sqrt(5) + 12 + 10*sqrt(15) + 30*sqrt(3))")), "sqrt(2*sqrt(10) + 6*sqrt(2) + 4*sqrt(5) + 12 + 10*sqrt(15) + 30*sqrt(3))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("radsimp, sqrtdenest (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["radsimp(P('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + x*sqrt(7))'))", () => radsimp(PA('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + x*sqrt(7))')), "1/(sqrt(7)*x + 1 + sqrt(2) + sqrt(3) + sqrt(5))"],
    ["radsimp(P('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7))'))", () => radsimp(PA('1/(1 + sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7))')), "(-1173*sqrt(6) - 447*sqrt(35) - 261*sqrt(70) - 652*sqrt(3) - 133*sqrt(30) - 135*sqrt(15) - 117*sqrt(14) - 96*sqrt(7) - 3*sqrt(105) + 789*sqrt(2) + 363*sqrt(10) + 277*sqrt(21) + 243*sqrt(42) + 1734 + 154*sqrt(210) + 1074*sqrt(5))/6054"],
    ["radsimp(P('1/(sqrt(2)*x + sqrt(3)*y + sqrt(5)*z + sqrt(7) + 1)'))", () => radsimp(PA('1/(sqrt(2)*x + sqrt(3)*y + sqrt(5)*z + sqrt(7) + 1)')), "1/(sqrt(2)*x + sqrt(3)*y + sqrt(5)*z + 1 + sqrt(7))"],
    ["radsimp(P('1/(x - sqrt(y))'))", () => radsimp(PA('1/(x - sqrt(y))')), "(x + sqrt(y))/(x**2 - y)"],
    ["sqrtdenest(P('sqrt(3 + 2*sqrt(3))'))", () => sqrtdenest(PA('sqrt(3 + 2*sqrt(3))')), "3**(3/4)*(sqrt(6)/2 + 3*sqrt(2)/2)/3"],
    ["sqrtdenest(P('sqrt(sqrt(2*sqrt(6) + 5) + sqrt(2*sqrt(7) + 8))'))", () => sqrtdenest(PA('sqrt(sqrt(2*sqrt(6) + 5) + sqrt(2*sqrt(7) + 8))')), "sqrt(1 + sqrt(2) + sqrt(3) + sqrt(7))"],
    ["sqrtdenest(P('sqrt(x*y)'))", () => sqrtdenest(PA('sqrt(x*y)')), "sqrt(x*y)"],
    ["sqrtdenest(P('sqrt(2*(1 + sqrt(2))**3)'))", () => sqrtdenest(PA('sqrt(2*(1 + sqrt(2))**3)')), "sqrt(2)*(1 + sqrt(2))**(3/2)"],
    ["sqrtdenest(P('sqrt(2**(1/3) + sqrt(2))'))", () => sqrtdenest(PA('sqrt(2**(1/3) + sqrt(2))')), "sqrt(2**(1/3) + sqrt(2))"],
    ["sqrtdenest(P('sqrt(1 + sqrt(2) + 3**(1/3))'))", () => sqrtdenest(PA('sqrt(1 + sqrt(2) + 3**(1/3))')), "sqrt(1 + sqrt(2) + 3**(1/3))"],
    ["radsimp(P('1/(1 + 2**sqrt(2))'), { symbolic: false })", () => radsimp(PA('1/(1 + 2**sqrt(2))'), { symbolic: false }), "1/(1 + 2**(sqrt(2)))"],
    ["radsimp(P('1/(x + zoo*sqrt(y))'))", () => radsimp(PA('1/(x + zoo*sqrt(y))')), "1/(x + zoo*sqrt(y))"],
    ["radsimp(P('1/(sqrt(2) + zoo*sqrt(3))'))", () => radsimp(PA('1/(sqrt(2) + zoo*sqrt(3))')), "0"],
    ["sqrtdenest(P('sqrt(1 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(PA('sqrt(1 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))')), "sqrt(1 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))"],
    ["sqrtdenest(P('sqrt(5 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(PA('sqrt(5 + sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)))')), "sqrt(sqrt(1 + sqrt(2)) + sqrt(3)*sqrt(1 + sqrt(2)) + 5)"],
    ["sqrtdenest(P('sqrt(-3 + 2*sqrt(2))'))", () => sqrtdenest(PA('sqrt(-3 + 2*sqrt(2))')), "-I + sqrt(2)*I"],
    ["sqrtdenest(P('sqrt(1 - 2*sqrt(2))'))", () => sqrtdenest(PA('sqrt(1 - 2*sqrt(2))')), "sqrt(1 - 2*sqrt(2))"],
    ["sqrtdenest(P('sqrt(2*sqrt(3) - 3)'))", () => sqrtdenest(PA('sqrt(2*sqrt(3) - 3)')), "3**(3/4)*(-sqrt(6)/2 + 3*sqrt(2)/2)/3"],
    ["sqrtdenest(P('sqrt(sqrt(3) - 1)'))", () => sqrtdenest(PA('sqrt(sqrt(3) - 1)')), "sqrt(-1 + sqrt(3))"],
    ["sqrtdenest(P('sqrt(2 - sqrt(3))'))", () => sqrtdenest(PA('sqrt(2 - sqrt(3))')), "-sqrt(2)/2 + sqrt(6)/2"],
    ["sqrtdenest(P('sqrt(sqrt(2) - 1)'))", () => sqrtdenest(PA('sqrt(sqrt(2) - 1)')), "sqrt(-1 + sqrt(2))"],
    ["sqrtdenest(P('sqrt(4*sqrt(3) - 6)'))", () => sqrtdenest(PA('sqrt(4*sqrt(3) - 6)')), "3**(3/4)*(3 - sqrt(3))/3"],
    ["sqrtdenest(P('sqrt(sqrt(5) - 2)'))", () => sqrtdenest(PA('sqrt(sqrt(5) - 2)')), "sqrt(-2 + sqrt(5))"],
    ["sqrtdenest(P('sqrt(3*sqrt(2) - 4)'))", () => sqrtdenest(PA('sqrt(3*sqrt(2) - 4)')), "2**(3/4)*(2 - sqrt(2))/2"],
    ["sqrtdenest(P('sqrt(2*sqrt(2) - 2)'))", () => sqrtdenest(PA('sqrt(2*sqrt(2) - 2)')), "sqrt(-2 + 2*sqrt(2))"],
    ["sqrtdenest(P('sqrt(5 - 2*sqrt(6) + 2*sqrt(2) - 2*sqrt(3))'))", () => sqrtdenest(PA('sqrt(5 - 2*sqrt(6) + 2*sqrt(2) - 2*sqrt(3))')), "sqrt(-2*sqrt(6) - 2*sqrt(3) + 2*sqrt(2) + 5)"],
    ["sqrtdenest(P('sqrt(10 - 2*sqrt(5) - 2*sqrt(10) + 2*sqrt(2))'))", () => sqrtdenest(PA('sqrt(10 - 2*sqrt(5) - 2*sqrt(10) + 2*sqrt(2))')), "sqrt(-2*sqrt(10) - 2*sqrt(5) + 2*sqrt(2) + 10)"],
    ["sqrtdenest(P('sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6))'))", () => sqrtdenest(PA('sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6))')), "sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6))"],
    ["sqrtdenest(P('sqrt(2*sqrt(2) + 3 - sqrt(5 + 2*sqrt(6)))'))", () => sqrtdenest(PA('sqrt(2*sqrt(2) + 3 - sqrt(5 + 2*sqrt(6)))')), "sqrt(-sqrt(3) + sqrt(2) + 3)"],
    ["sqrtdenest(P('sqrt(9 - 4*sqrt(2) - 2*sqrt(3) + 2*sqrt(6))'))", () => sqrtdenest(PA('sqrt(9 - 4*sqrt(2) - 2*sqrt(3) + 2*sqrt(6))')), "sqrt(-4*sqrt(2) - 2*sqrt(3) + 2*sqrt(6) + 9)"],
    ["sqrtdenest(P('sqrt(1 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) + sqrt(3)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))'))", () => sqrtdenest(PA('sqrt(1 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) + sqrt(3)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))')), "sqrt(1 + sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6)) + sqrt(3)*sqrt(1 + sqrt(2) + sqrt(3) + sqrt(6)))"],
    ["sqrtdenest(P('sqrt(2 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) - sqrt(5)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))'))", () => sqrtdenest(PA('sqrt(2 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) - sqrt(5)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))')), "sqrt(-sqrt(5)*sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)) + 2 + sqrt(1 + sqrt(2))*sqrt(1 + sqrt(3)))"],
    ["sqrtdenest(P('sqrt(2*sqrt(3) + 2*sqrt(5) + 2*sqrt(15) + 20*sqrt(2) + 20*sqrt(6) + 20*sqrt(10) + 209)'))", () => sqrtdenest(PA('sqrt(2*sqrt(3) + 2*sqrt(5) + 2*sqrt(15) + 20*sqrt(2) + 20*sqrt(6) + 20*sqrt(10) + 209)')), "1 + sqrt(3) + sqrt(5) + 10*sqrt(2)"],
    ["sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 40*sqrt(2) + 40*sqrt(3) + 40*sqrt(5) + 410)'))", () => sqrtdenest(PA('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 40*sqrt(2) + 40*sqrt(3) + 40*sqrt(5) + 410)')), "sqrt(2) + sqrt(3) + sqrt(5) + 20"],
    ["sqrtdenest(P('sqrt(2*sqrt(2) + 2*sqrt(7) + 2*sqrt(14) + 10*sqrt(3) + 10*sqrt(6) + 10*sqrt(21) + 85)'))", () => sqrtdenest(PA('sqrt(2*sqrt(2) + 2*sqrt(7) + 2*sqrt(14) + 10*sqrt(3) + 10*sqrt(6) + 10*sqrt(21) + 85)')), "1 + sqrt(2) + sqrt(7) + 5*sqrt(3)"],
    ["sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(14) + 6*sqrt(2) + 2*sqrt(21) + 6*sqrt(3) + 6*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 8*sqrt(35) + 24*sqrt(5) + 101)'))", () => sqrtdenest(PA('sqrt(2*sqrt(6) + 2*sqrt(14) + 6*sqrt(2) + 2*sqrt(21) + 6*sqrt(3) + 6*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 8*sqrt(35) + 24*sqrt(5) + 101)')), "sqrt(2) + sqrt(3) + sqrt(7) + 3 + 4*sqrt(5)"],
    ["sqrtdenest(P('sqrt(-2*sqrt(5) - 2*sqrt(3) - 2*sqrt(2) + 2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 11)'))", () => sqrtdenest(PA('sqrt(-2*sqrt(5) - 2*sqrt(3) - 2*sqrt(2) + 2*sqrt(6) + 2*sqrt(10) + 2*sqrt(15) + 11)')), "-1 + sqrt(2) + sqrt(3) + sqrt(5)"],
    ["sqrtdenest(P('sqrt(-2*sqrt(21) - 2*sqrt(15) - 2*sqrt(6) - 2*sqrt(3) + 2*sqrt(2) + 2*sqrt(5) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(35) + 18)'))", () => sqrtdenest(PA('sqrt(-2*sqrt(21) - 2*sqrt(15) - 2*sqrt(6) - 2*sqrt(3) + 2*sqrt(2) + 2*sqrt(5) + 2*sqrt(7) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(35) + 18)')), "-sqrt(3) + 1 + sqrt(2) + sqrt(5) + sqrt(7)"],
    ["sqrtdenest(P('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 17)'))", () => sqrtdenest(PA('sqrt(2*sqrt(6) + 2*sqrt(10) + 2*sqrt(14) + 2*sqrt(15) + 2*sqrt(21) + 2*sqrt(35) + 17)')), "sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7)"],
    ["sqrtdenest(P('sqrt(4*sqrt(3) + 2*sqrt(33) + 4*sqrt(11) + 6*sqrt(6) + 12*sqrt(2) + 6*sqrt(22) + 36)'))", () => sqrtdenest(PA('sqrt(4*sqrt(3) + 2*sqrt(33) + 4*sqrt(11) + 6*sqrt(6) + 12*sqrt(2) + 6*sqrt(22) + 36)')), "sqrt(3) + 2 + sqrt(11) + 3*sqrt(2)"],
    ["sqrtdenest(P('sqrt(-7*sqrt(10) - 3*sqrt(21) - 3*sqrt(7) - 3*sqrt(5) + 18)'))", () => sqrtdenest(PA('sqrt(-7*sqrt(10) - 3*sqrt(21) - 3*sqrt(7) - 3*sqrt(5) + 18)')), "sqrt(-7*sqrt(10) - 3*sqrt(21) - 3*sqrt(7) - 3*sqrt(5) + 18)"],
    ["sqrtdenest(P('sqrt(-sqrt(15) + 2*sqrt(21) + 9*sqrt(7) + 27)'))", () => sqrtdenest(PA('sqrt(-sqrt(15) + 2*sqrt(21) + 9*sqrt(7) + 27)')), "sqrt(-sqrt(15) + 2*sqrt(21) + 9*sqrt(7) + 27)"],
    ["sqrtdenest(P('sqrt(-3*sqrt(35) - 3*sqrt(7) + 9*sqrt(2) + 36)'))", () => sqrtdenest(PA('sqrt(-3*sqrt(35) - 3*sqrt(7) + 9*sqrt(2) + 36)')), "sqrt(-3*sqrt(35) - 3*sqrt(7) + 9*sqrt(2) + 36)"],
    ["sqrtdenest(P('sqrt(-7*sqrt(6) - sqrt(21) + 9 + 5*sqrt(10) + 9*sqrt(14) + 9*sqrt(15))'))", () => sqrtdenest(PA('sqrt(-7*sqrt(6) - sqrt(21) + 9 + 5*sqrt(10) + 9*sqrt(14) + 9*sqrt(15))')), "sqrt(-7*sqrt(6) - sqrt(21) + 9 + 5*sqrt(10) + 9*sqrt(14) + 9*sqrt(15))"],
    ["sqrtdenest(P('sqrt(-3*sqrt(10) - 6 + 2*sqrt(6) + 2*sqrt(15))'))", () => sqrtdenest(PA('sqrt(-3*sqrt(10) - 6 + 2*sqrt(6) + 2*sqrt(15))')), "sqrt(-3*sqrt(10) - 6 + 2*sqrt(6) + 2*sqrt(15))"],
    ["sqrtdenest(P('sqrt(10 - 4*sqrt(-1 + sqrt(7)))'))", () => sqrtdenest(PA('sqrt(10 - 4*sqrt(-1 + sqrt(7)))')), "-sqrt(14)*sqrt(-1 + sqrt(7))*sqrt(8 + 4*sqrt(7))/6 + sqrt(2)*sqrt(-1 + sqrt(7))*sqrt(8 + 4*sqrt(7))/3 + sqrt(2)*sqrt(8 + 4*sqrt(7))/2"],
    ["sqrtdenest(P('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) - 12*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(PA('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) - 12*sqrt(1 + sqrt(2)))')), "-sqrt(7) + 1 + sqrt(1 + sqrt(2)) + sqrt(7)*sqrt(1 + sqrt(2))"],
    ["sqrtdenest(P('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) + 12*sqrt(1 + sqrt(2)))'))", () => sqrtdenest(PA('sqrt(16 + 8*sqrt(2) + 2*sqrt(14) + 12*sqrt(1 + sqrt(2)))')), "-1 + sqrt(1 + sqrt(2)) + sqrt(7) + sqrt(7)*sqrt(1 + sqrt(2))"],
    ["sqrtdenest(P('sqrt(-4*sqrt(70)*sqrt(2 + sqrt(6)) - 8*sqrt(10)*sqrt(2 + sqrt(6)) - 2*sqrt(7)*sqrt(2 + sqrt(6)) - 4*sqrt(2 + sqrt(6)) + 4*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 93 + 41*sqrt(6))'))", () => sqrtdenest(PA('sqrt(-4*sqrt(70)*sqrt(2 + sqrt(6)) - 8*sqrt(10)*sqrt(2 + sqrt(6)) - 2*sqrt(7)*sqrt(2 + sqrt(6)) - 4*sqrt(2 + sqrt(6)) + 4*sqrt(7) + 8*sqrt(10) + 8*sqrt(15) + 93 + 41*sqrt(6))')), "-sqrt(7) - 2 + sqrt(2 + sqrt(6)) + 2*sqrt(10)*sqrt(2 + sqrt(6))"],
    ["sqrtdenest(P('sqrt(-126*sqrt(3) - 12*sqrt(6)*sqrt(-2 + 3*sqrt(6)) - 38 - 10*sqrt(-2 + 3*sqrt(6)) + 4*sqrt(2)*sqrt(-2 + 3*sqrt(6)) + 40*sqrt(2) + 30*sqrt(3)*sqrt(-2 + 3*sqrt(6)) + 99*sqrt(6))'))", () => sqrtdenest(PA('sqrt(-126*sqrt(3) - 12*sqrt(6)*sqrt(-2 + 3*sqrt(6)) - 38 - 10*sqrt(-2 + 3*sqrt(6)) + 4*sqrt(2)*sqrt(-2 + 3*sqrt(6)) + 40*sqrt(2) + 30*sqrt(3)*sqrt(-2 + 3*sqrt(6)) + 99*sqrt(6))')), "-2*sqrt(2)*sqrt(-2 + 3*sqrt(6)) - 1 + 3*sqrt(3) + 5*sqrt(-2 + 3*sqrt(6))"],
    ["sqrtdenest(P('sqrt(-188*sqrt(15) - 40*sqrt(15)*sqrt(2 + 3*sqrt(6)) - 20*sqrt(6)*sqrt(2 + 3*sqrt(6)) + 4*sqrt(10) + 33*sqrt(6) + 10*sqrt(10)*sqrt(2 + 3*sqrt(6)) + 100*sqrt(2 + 3*sqrt(6)) + 872)'))", () => sqrtdenest(PA('sqrt(-188*sqrt(15) - 40*sqrt(15)*sqrt(2 + 3*sqrt(6)) - 20*sqrt(6)*sqrt(2 + 3*sqrt(6)) + 4*sqrt(10) + 33*sqrt(6) + 10*sqrt(10)*sqrt(2 + 3*sqrt(6)) + 100*sqrt(2 + 3*sqrt(6)) + 872)')), "-10*sqrt(6) + sqrt(2 + 3*sqrt(6)) + sqrt(10)*sqrt(2 + 3*sqrt(6)) + 5*sqrt(10)"],
    ["sqrtdenest(P('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) + 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))'))", () => sqrtdenest(PA('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) + 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))')), "-2**(1/4) + 2**(3/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2))/2 + 2**(1/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2)) + 2**(3/4)"],
    ["sqrtdenest(P('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) - 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))'))", () => sqrtdenest(PA('sqrt(1 + 3*sqrt(2) - 2*sqrt(6) - 2*sqrt(15*sqrt(2) - 12*sqrt(3) - 20 + 8*sqrt(6)))')), "-2**(1/4) - 2**(1/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2)) - 2**(3/4)*sqrt(-12*sqrt(3) - 20 + 8*sqrt(6) + 15*sqrt(2))/2 + 2**(3/4)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});
