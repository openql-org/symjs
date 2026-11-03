// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { parse, sqrtdenest } from '../src';

const P = parse;

const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

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
