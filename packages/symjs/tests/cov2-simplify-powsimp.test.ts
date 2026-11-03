// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { expandLog, float, logcombine, parse, powdenest, powsimp, symbol } from '../src';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const P = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

const show = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${show(k)}: ${show(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("powsimp, powdenest, logcombine, expand_log (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["powsimp(P('((w**(-1)*w**(2)*w)**(-3/2)*w**(1/2))**(1/4)*w**(5/2)*(w**(-1)*w**(2)*w)**(1/2)*w**(1/2)', {n: {integer: true}}))", () => powsimp(P('((w**(-1)*w**(2)*w)**(-3/2)*w**(1/2))**(1/4)*w**(5/2)*(w**(-1)*w**(2)*w)**(1/2)*w**(1/2)', {n: {integer: true}})), "sqrt(w**2)/(w**2*(sqrt(w)/(w**2)**(3/2))**(7/4))"],
    ["powsimp(P('(x*y**(-1))**(1/2)*x**(1)*y**(4)', {n: {integer: true}}))", () => powsimp(P('(x*y**(-1))**(1/2)*x**(1)*y**(4)', {n: {integer: true}})), "x*y**4*sqrt(x/y)"],
    ["powsimp(P('(y**(-1/2)*w**(1/2))**(1/4)*y**(-1)*w**(3)', {n: {integer: true}}))", () => powsimp(P('(y**(-1/2)*w**(1/2))**(1/4)*y**(-1)*w**(3)', {n: {integer: true}})), "w**2*(sqrt(w)/sqrt(y))**(9/4)"],
    ["powsimp(P('((z**(2)*y**(1/2))**(5/2)*z)**(2/3)*z**(5/2)*y**(5/2)*z**(1)', {n: {integer: true}}))", () => powsimp(P('((z**(2)*y**(1/2))**(5/2)*z)**(2/3)*z**(5/2)*y**(5/2)*z**(1)', {n: {integer: true}})), "y**(5/2)*z**(7/2)*(z*(sqrt(y)*z**2)**(5/2))**(2/3)"],
    ["powsimp(P('(w*x**(n))**(-3/2)*w**(3/2)', {n: {integer: true}}))", () => powsimp(P('(w*x**(n))**(-3/2)*w**(3/2)', {n: {integer: true}})), "w**(3/2)/(w*x**n)**(3/2)"],
    ["powsimp(P('(w**(-1/2)*(w**(n)*x**(-1/2))**(1/2))**(3/2)*w**(-1/2)*x**(-2)*(w**(n)*x**(-1/2))**(1/2)', {n: {integer: true}}))", () => powsimp(P('(w**(-1/2)*(w**(n)*x**(-1/2))**(1/2))**(3/2)*w**(-1/2)*x**(-2)*(w**(n)*x**(-1/2))**(1/2)', {n: {integer: true}})), "(sqrt(w**n/sqrt(x))/sqrt(w))**(5/2)/x**2"],
    ["powsimp(P('sqrt(z*sqrt(x*sqrt(y)))*z*(x*sqrt(y))**(3/2)', {n: {integer: true}}))", () => powsimp(P('sqrt(z*sqrt(x*sqrt(y)))*z*(x*sqrt(y))**(3/2)', {n: {integer: true}})), "x*sqrt(y)*(z*sqrt(x*sqrt(y)))**(3/2)"],
    ["powsimp(P('sqrt(z*sqrt(x*y**(1/3)))*z*(x*y**(1/3))**(3/2)', {n: {integer: true}}))", () => powsimp(P('sqrt(z*sqrt(x*y**(1/3)))*z*(x*y**(1/3))**(3/2)', {n: {integer: true}})), "x*y**(1/3)*(z*sqrt(x*y**(1/3)))**(3/2)"],
    ["powsimp(P('(y*x**(t/2)*y**(t/2))**(5/2)', {n: {integer: true}}))", () => powsimp(P('(y*x**(t/2)*y**(t/2))**(5/2)', {n: {integer: true}})), "(x**(t/2)*y*y**(t/2))**(5/2)"],
    ["powsimp(P('x*sqrt(x/y)/y**3', {n: {integer: true}}))", () => powsimp(P('x*sqrt(x/y)/y**3', {n: {integer: true}})), "x*sqrt(x/y)/y**3"],
    ["powsimp(P('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)', {n: {integer: true}}))", () => powsimp(P('x**4*(x*sqrt(y))**(1/3)*y**5*(x*y)**(1/2)', {n: {integer: true}})), "y**3*(x*sqrt(y))**(13/3)*sqrt(x*y)"],
    ["powsimp(P('n**(1/3)*x**(1/3)*y**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(P('n**(1/3)*x**(1/3)*y**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "(-1)**(1/3)*x**(1/3)*y**(1/3)*(-n)**(1/3)"],
    ["powsimp(P('n**(j/3)*x**(j/3)*y**(j/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(P('n**(j/3)*x**(j/3)*y**(j/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "(-1)**(j/3)*x**(j/3)*y**(j/3)*(-n)**(j/3)"],
    ["powsimp(P('n**(1/3)*x**(1/3)*y**(1/3)*p**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(P('n**(1/3)*x**(1/3)*y**(1/3)*p**(1/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "(-1)**(1/3)*p**(1/3)*x**(1/3)*y**(1/3)*(-n)**(1/3)"],
    ["powsimp(P('n**(x/3)*x**(x/3)*y**(x/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' })", () => powsimp(P('n**(x/3)*x**(x/3)*y**(x/3)', {n: {negative: true}, k: {negative: true}, j: {integer: true}, p: {positive: true}}), { combine: 'base' }), "n**(x/3)*x**(x/3)*y**(x/3)"],
    ["powdenest(P('8**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('8**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2**(3*x)"],
    ["powdenest(P('4**x*3', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('4**x*3', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3*2**(2*x)"],
    ["powdenest(P('sqrt(8)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('sqrt(8)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(2*sqrt(2))**x"],
    ["powdenest(P('(p**(1/2)*q**sqrt(2))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(p**(1/2)*q**sqrt(2))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(sqrt(p)*q**(sqrt(2)))**z"],
    ["powdenest(P('(p**x*q**(2*x))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(p**x*q**(2*x))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(p**x*q**(2*x))**z"],
    ["powdenest(P('(p**pi*q**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(p**pi*q**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(p**pi*q**2)**z"],
    ["powdenest(P('(n**2)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => powdenest(P('(n**2)**x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "(-n)**(2*x)"],
    // SymPy 1.14 gives (p**2.5*q**3.0)**(1.0*z), the same value: its gcd of the coefficients 2.5 and 3 of the logarithms is 1.0, symjs keeps exact exponents
    ["powdenest(P('(p**2.5*q**3)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(p**2.5*q**3)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(p**2.5*q**3)**z"],
    ["logcombine(P('2*log(p)*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(P('2*log(p)*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(q**log(p**2))"],
    ["logcombine(P('log(2)*log(3)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(P('log(2)*log(3)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(3**log(sqrt(2)))"],
    ["logcombine(P('log(4)*log(9)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(P('log(4)*log(9)/2', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(9**log(2))"],
    ["logcombine(P('log(p)*log(q)*x', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(P('log(p)*log(q)*x', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "x*log(q**log(p))"],
    ["expandLog(P('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3*log(2)"],
    ["expandLog(P('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "3*log(2)"],
    ["expandLog(P('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2*log(2)"],
    ["expandLog(P('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(2)"],
    ["expandLog(P('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2*log(6)"],
    ["expandLog(P('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(6)"],
    ["expandLog(P('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(12)"],
    ["expandLog(P('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(12)"],
    ["expandLog(P('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-2*log(2) + log(3)"],
    ["expandLog(P('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-2*log(2) + log(3)"],
    ["expandLog(P('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-2*log(3) + 3*log(2)"],
    ["expandLog(P('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-2*log(3) + 3*log(2)"],
    ["expandLog(P('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-3*log(2)"],
    ["expandLog(P('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-3*log(2)"],
    ["expandLog(P('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "100*log(2)"],
    ["expandLog(P('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "100*log(2)"],
    ["expandLog(P('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x) + 10*log(2)"],
    ["expandLog(P('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x) + 10*log(2)"],
    ["expandLog(P('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3*log(2) + I*pi"],
    ["expandLog(P('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "3*log(2) + I*pi"],
    ["expandLog(P('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-2*log(2) + log(3) + I*pi"],
    ["expandLog(P('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-2*log(2) + log(3) + I*pi"],
    ["expandLog(P('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "4"],
    ["expandLog(P('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "4"],
    ["expandLog(P('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x)/2"],
    ["expandLog(P('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x)/2"],
    ["expandLog(P('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x)/3"],
    ["expandLog(P('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x)/3"],
    ["expandLog(P('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x**2)"],
    ["expandLog(P('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(x)"],
    ["expandLog(P('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(1/x)"],
    ["expandLog(P('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-log(x)"],
    ["expandLog(P('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-log(x)/2"],
    ["expandLog(P('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-log(x)/2"],
    ["expandLog(P('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x**y)"],
    ["expandLog(P('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "y*log(x)"],
    ["expandLog(P('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(p**y)"],
    ["expandLog(P('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "y*log(p)"],
    ["expandLog(P('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(exp(x))"],
    ["expandLog(P('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "x"],
    ["expandLog(P('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(-y) + log(2)"],
    ["expandLog(P('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(y) + log(2) + I*pi"],
    ["expandLog(P('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x) - log(2)"],
    ["expandLog(P('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x) - log(2)"],
    ["expandLog(P('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(-n) + log(-x)"],
    ["expandLog(P('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(n) + log(x)"],
    ["expandLog(P('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(p) + log(x*y)"],
    ["expandLog(P('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(p) + log(x) + log(y)"],
    ["expandLog(P('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2*log(p) + log(x)"],
    ["expandLog(P('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(p) + log(x)"],
    ["expandLog(P('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(p) + log(x)/2 + log(2)"],
    ["expandLog(P('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(p) + log(x)/2 + log(2)"],
    ["expandLog(P('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(P('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x**(2*I))"],
    ["expandLog(P('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(P('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*I*log(x)"],
    ["powdenest(P('(1/(p**2*q**3))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(1/(p**2*q**3))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(1/(p**2*q**3))**z"],
    ["powdenest(P('(q**3/p**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(q**3/p**2)**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(q**3/p**2)**z"],
    ["powdenest(P('(p**(-2)*q**(-4))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(p**(-2)*q**(-4))**z', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(1/(p*q**2))**(2*z)"],
    ["logcombine(P('x*log(p) - x*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(P('x*log(p) - x*log(q)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "x*log(p/q)"],
    ["logcombine(P('x*log(p) - x*log(q) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('x*log(p) - x*log(q) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(p**x*y/q**x)"],
    ["logcombine(P('f(1)*log(x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('f(1)*log(x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(x**f(1))"],
    ["logcombine(P('I*log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('I*log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "I*log(y)"],
    ["logcombine(P('pi*log(x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('pi*log(x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log((x*y)**pi)"],
    ["logcombine(P('log(x) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('log(x) + log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(x*y)"],
    ["logcombine(P('log(x) + log(n)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('log(x) + log(n)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(n*x)"],
    ["logcombine(P('2*log(x) - log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true })", () => logcombine(P('2*log(x) - log(y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), { force: true }), "log(x**2/y)"],
    ["logcombine(P('-log(p) + 2*x*log(q) - x*log(p)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => logcombine(P('-log(p) + 2*x*log(q) - x*log(p)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "x*log(q**2/p) - log(p)"],
    ["powdenest(P('3**x*y', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('3**x*y', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3**x*y"],
    ["powdenest(P('6**x*12**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('6**x*12**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "12**y*6**x"],
    ["powdenest(P('(3*x)**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => powdenest(P('(3*x)**y', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "(3*x)**y"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe('powsimp (cov2): an exponent that becomes symbolic while bases are combined', () => {
  it('keeps the value where SymPy 1.14 raises TypeError (cannot determine truth value of Relational: 2*n < 2)', () => {
    // sqrt(s*sqrt(s**n*y))*s*(s**n*y)**(5/2) = y**2*s**(2*n)*(s*sqrt(s**n*y))**(3/2) for an integer n
    const e = P('sqrt(sin(x)*sqrt(sin(x)**n*y))*sin(x)*(sin(x)**n*y)**(5/2)', { n: { integer: true } });
    const r = powsimp(e);
    expect(String(r)).toBe('y**2*(sqrt(y*sin(x)**n)*sin(x))**(3/2)*(sin(x)**2)**n');
    const at = (v: Expr) => v.subs([[symbol('n', { integer: true }), 3], [symbol('x'), float(0.7)], [symbol('y'), float(1.3)]]).toNumber();
    expect(at(r)).toBeCloseTo(at(e), 12);
  });
});
