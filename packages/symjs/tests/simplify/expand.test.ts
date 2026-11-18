// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/expand.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import * as sj from '../../src';
import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, I, Sym, abs, add, expPolar, expand, expandComplex, expandLog, expandMultinomial, expandPowerBase, expandTrig, fn, mul, parse, pow, sstr, symbol, symbols } from '../../src';
import type { Expr } from '../../src';
import { expandMulRounds } from '../../src/simplify/expand';

const [x, y] = symbols('x y');
const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

it('factors integer logarithms when requested and cancels common log bases', () => {
  expect(sstr(expandLog(P('log(12)'), { factor: true }))).toBe('log(3) + 2*log(2)');
  expect(sstr(expandLog(P('log(21)/log(7)')))).toBe('log(3)/log(7) + 1');
  expect(sstr(expandLog(P('log(6)/log(35)')))).toBe('log(6)/log(35)');
  expect(sstr(expandLog(fn('log', [-2], { evaluate: false })))).toBe('log(2) + I*pi');
  expect(sstr(expandLog(fn('log', [1], { evaluate: false })))).toBe('0');
});

it('expands a complex modulus and retains a hyperbolic function of an extended real', () => {
  const t = symbol('t', { extendedReal: true });
  expect(sstr(expandComplex(abs(x)))).toBe('sqrt(re(x)**2 + im(x)**2)');
  expect(sstr(expandComplex(fn('cosh', [t], { evaluate: false })))).toBe('cosh(t)');
});
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PPolar = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { locals: { exp_polar: expPolar }, symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

describe('expand', () => {
  it('expands products and powers', () => {
    expect(expand(pow(add(x, 1), 2)).toString()).toBe('x**2 + 2*x + 1');
    expect(expand(mul(add(x, y), add(x, mul(-1, y)))).toString()).toBe('x**2 - y**2');
    expect(expand(pow(add(1, I), 2)).toString()).toBe('2*I');
  });
});

describe('parser and assumptions', () => {
  it('zero=False splits powers', async () => {
    const { expandPowerExp, Symbol: Sym } = await import('../../src');
    const xn = new Sym('x', { zero: false });
    expect(sstr(expandPowerExp(parse('x**(y + 2)', { symbols: { x: xn } } as never)))).toBe('x**2*x**y');
    expect(sstr(expandPowerExp(parse('x**(y + 2)')))).toBe('x**(y + 2)');
  });
});

describe("simplify functions: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["expandPowerBase(P(\"x**4*y**4*z**4\"))", () => expandPowerBase(P("x**4*y**4*z**4")), "x**4*y**4*z**4"],
    ["expandPowerBase(P(\"(x*y*z)**x\"))", () => expandPowerBase(P("(x*y*z)**x")), "(x*y*z)**x"],
    ["expandPowerBase(P(\"(x*y*z)**x\"), { force: true })", () => expandPowerBase(P("(x*y*z)**x"), { force: true }), "x**x*y**x*z**x"],
    ["expandPowerBase(P(\"x**3*y**6*z**6\"))", () => expandPowerBase(P("x**3*y**6*z**6")), "x**3*y**6*z**6"],
    ["expandPowerBase(P(\"(y*sin(x**2*y**2))**z\"))", () => expandPowerBase(P("(y*sin(x**2*y**2))**z")), "(y*sin(x**2*y**2))**z"],
    ["expandPowerBase(P(\"(y*sin(x**2*y**2))**z\"), { force: true })", () => expandPowerBase(P("(y*sin(x**2*y**2))**z"), { force: true }), "y**z*sin(x**2*y**2)**z"],
    ["expandPowerBase(P(\"exp(2*x)\"))", () => expandPowerBase(P("exp(2*x)")), "exp(2*x)"],
    ["expandPowerBase(P(\"exp(2*x)*exp(2*y)\"))", () => expandPowerBase(P("exp(2*x)*exp(2*y)")), "exp(2*x)*exp(2*y)"],
    ["expandPowerBase(P(\"exp(2*y)*exp(2*(x*y)**z)\"))", () => expandPowerBase(P("exp(2*y)*exp(2*(x*y)**z)")), "exp(2*y)*exp(2*(x*y)**z)"],
    ["expandPowerBase(P(\"(exp(x)*exp(y))**z\"))", () => expandPowerBase(P("(exp(x)*exp(y))**z")), "(exp(x)*exp(y))**z"],
    ["expandPowerBase(P(\"(exp(x)*exp(y))**z\"), { force: true })", () => expandPowerBase(P("(exp(x)*exp(y))**z"), { force: true }), "exp(x)**z*exp(y)**z"],
    ["expandMultinomial(P(\"(x*(x + 1)**2 + 1)**2\"))", () => expandMultinomial(P("(x*(x + 1)**2 + 1)**2")), "x**2*(x**4 + 4*x**3 + 6*x**2 + 4*x + 1) + 2*x*(x**2 + 2*x + 1) + 1"],
    ["expandMultinomial(P(\"((x + 1)**2*(x + y) + 1)**2\"))", () => expandMultinomial(P("((x + 1)**2*(x + y) + 1)**2")), "2*(x + y)*(x**2 + 2*x + 1) + (x**2 + 2*x*y + y**2)*(x**4 + 4*x**3 + 6*x**2 + 4*x + 1) + 1"],
    ["expandMultinomial(Qs(\"(x*(1 + A)**2 + 1)**2\", [symbol(\"A\", { commutative: false })]))", () => expandMultinomial(Qs("(x*(1 + A)**2 + 1)**2", [symbol("A", { commutative: false })])), "x**2*(1 + 4*A + 6*A**2 + 4*A**3 + A**4) + 2*x*(1 + 2*A + A**2) + 1"],
    ["expandMultinomial(Qs(\"((x + y)*(1 + A)**2 + 1)**2\", [symbol(\"A\", { commutative: false })]))", () => expandMultinomial(Qs("((x + y)*(1 + A)**2 + 1)**2", [symbol("A", { commutative: false })])), "2*(x + y)*(1 + 2*A + A**2) + (x**2 + 2*x*y + y**2)*(1 + 4*A + 6*A**2 + 4*A**3 + A**4) + 1"],
    ["expandMultinomial(Qs(\"((x + y)*(1 + A)**2 + 1)**3\", [symbol(\"A\", { commutative: false })]))", () => expandMultinomial(Qs("((x + y)*(1 + A)**2 + 1)**3", [symbol("A", { commutative: false })])), "3*(x + y)*(1 + 2*A + A**2) + 3*(x**2 + 2*x*y + y**2)*(1 + 4*A + 6*A**2 + 4*A**3 + A**4) + (x**3 + 3*x**2*y + 3*x*y**2 + y**3)*(1 + 6*A + 15*A**2 + 20*A**3 + 15*A**4 + 6*A**5 + A**6) + 1"],
    ["expandMultinomial(Qs(\"((1 + A)**2)**2\", [symbol(\"A\", { commutative: false })]))", () => expandMultinomial(Qs("((1 + A)**2)**2", [symbol("A", { commutative: false })])), "1 + 4*A + 6*A**2 + 4*A**3 + A**4"],
    ["expandMultinomial(P(\"(2 + 3*I)**2\"))", () => expandMultinomial(P("(2 + 3*I)**2")), "-5 + 12*I"],
    ["expandMultinomial(P(\"(2 + 3*I)**3\"))", () => expandMultinomial(P("(2 + 3*I)**3")), "-46 + 9*I"],
    ["expandMultinomial(P(\"(2 + 3*I)**4\"))", () => expandMultinomial(P("(2 + 3*I)**4")), "-119 - 120*I"],
    ["expandMultinomial(P(\"(2 + 3*I)**5\"))", () => expandMultinomial(P("(2 + 3*I)**5")), "122 - 597*I"],
    ["expandMultinomial(P(\"(2 + I/3)**2\"))", () => expandMultinomial(P("(2 + I/3)**2")), "35/9 + 4*I/3"],
    ["expandMultinomial(P(\"(2 + I/3)**3\"))", () => expandMultinomial(P("(2 + I/3)**3")), "22/3 + 107*I/27"],
    ["expandMultinomial(P(\"(2 + I/3)**4\"))", () => expandMultinomial(P("(2 + I/3)**4")), "1081/81 + 280*I/27"],
    ["expandMultinomial(P(\"(2 + I/3)**5\"))", () => expandMultinomial(P("(2 + I/3)**5")), "1882/81 + 6121*I/243"],
    ["expandMultinomial(P(\"(1/2 + 3*I)**2\"))", () => expandMultinomial(P("(1/2 + 3*I)**2")), "-35/4 + 3*I"],
    ["expandMultinomial(P(\"(1/2 + 3*I)**3\"))", () => expandMultinomial(P("(1/2 + 3*I)**3")), "-107/8 - 99*I/4"],
    ["expandMultinomial(P(\"(1/2 + 3*I)**4\"))", () => expandMultinomial(P("(1/2 + 3*I)**4")), "1081/16 - 105*I/2"],
    ["expandMultinomial(P(\"(1/2 + 3*I)**5\"))", () => expandMultinomial(P("(1/2 + 3*I)**5")), "6121/32 + 2823*I/16"],
    ["expandMultinomial(P(\"(1/2 + I/3)**2\"))", () => expandMultinomial(P("(1/2 + I/3)**2")), "5/36 + I/3"],
    ["expandMultinomial(P(\"(1/2 + I/3)**3\"))", () => expandMultinomial(P("(1/2 + I/3)**3")), "-1/24 + 23*I/108"],
    ["expandMultinomial(P(\"(1/2 + I/3)**4\"))", () => expandMultinomial(P("(1/2 + I/3)**4")), "-119/1296 + 5*I/54"],
    ["expandMultinomial(P(\"(1/2 + I/3)**5\"))", () => expandMultinomial(P("(1/2 + I/3)**5")), "-199/2592 + 61*I/3888"],
    ["expandMultinomial(P(\"(x + 1)**2\"))", () => expandMultinomial(P("(x + 1)**2")), "x**2 + 2*x + 1"],
    ["expandMultinomial(P(\"(x + 1)**3\"))", () => expandMultinomial(P("(x + 1)**3")), "x**3 + 3*x**2 + 3*x + 1"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("expand (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["expandPowerBase(P('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "A*B*A*B"],
    ["expandPowerBase(P('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "A*B*A*B"],
    ["expandPowerBase(P('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "B**(-1)*A**(-1)*B**(-1)*A**(-1)"],
    ["expandPowerBase(P('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "B**(-1)*A**(-1)*B**(-1)*A**(-1)"],
    ["expandPowerBase(P('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "4*A*B*A*B"],
    ["expandPowerBase(P('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "4*A*B*A*B"],
    ["expandPowerBase(P('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "x**3*A*B*A*B*A*B"],
    ["expandPowerBase(P('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "x**3*A*B*A*B*A*B"],
    ["expandPowerBase(P('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(A*B)**x"],
    ["expandPowerBase(P('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(A*B)**x"],
    ["expandPowerBase(P('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**x*(A*B)**x"],
    ["expandPowerBase(P('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2**x*(A*B)**x"],
    ["expandPowerBase(P('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "p**x*(A*B)**x"],
    ["expandPowerBase(P('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "p**x*(A*B)**x"],
    ["expandPowerBase(P('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(A**2*B)**x"],
    ["expandPowerBase(P('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(A**2*B)**x"],
    ["expandPowerBase(P('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(x*y)**z"],
    ["expandPowerBase(P('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "x**z*y**z"],
    ["expandPowerBase(P('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "p**z*x**z"],
    ["expandPowerBase(P('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "p**z*x**z"],
    ["expandPowerBase(P('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**z*(-x)**z"],
    ["expandPowerBase(P('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*x**z"],
    ["expandPowerBase(P('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(I*x)**z"],
    ["expandPowerBase(P('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "I**z*x**z"],
    ["expandPowerBase(P('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(n*x)**z"],
    ["expandPowerBase(P('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "n**z*x**z"],
    ["expandPowerBase(P('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(-k)**z*(-n)**z"],
    ["expandPowerBase(P('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "k**z*n**z"],
    ["expandPowerBase(P('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**z*x**z*(-n)**z"],
    ["expandPowerBase(P('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*n**z*x**z"],
    ["expandPowerBase(P('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "x**z*(-n)**z"],
    ["expandPowerBase(P('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-1)**z*n**z*x**z"],
    ["expandPowerBase(P('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(n*x*y)**z"],
    ["expandPowerBase(P('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "n**z*x**z*y**z"],
    ["expandPowerBase(P('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(-2)**z*(-k)**z*(-n)**z"],
    ["expandPowerBase(P('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*k**z*n**z"],
    ["expandPowerBase(P('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**z*(-k)**z*(-n)**z*(-x)**z"],
    ["expandPowerBase(P('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*k**z*n**z*x**z"],
    ["expandPowerBase(P('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "I**z*p**z"],
    ["expandPowerBase(P('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "I**z*p**z"],
    ["expandPowerBase(P('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(-x)**z"],
    ["expandPowerBase(P('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-1)**z*x**z"],
    ["expandPowerBase(P('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2*sqrt(x*y)"],
    ["expandPowerBase(P('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2*sqrt(x)*sqrt(y)"],
    ["expandPowerBase(P('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2*sqrt(-x)"],
    ["expandPowerBase(P('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2*I*sqrt(x)"],
    ["expandPowerBase(P('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**(1/6)*sqrt(x)"],
    ["expandPowerBase(P('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2**(1/6)*sqrt(x)"],
    ["expandPowerBase(P('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "q**z*x**z"],
    ["expandPowerBase(P('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "q**z*x**z"],
    ["expandPowerBase(P('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "x**z*exp_polar(2*z)"],
    ["expandPowerBase(P('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "x**z*exp_polar(2*z)"],
    ["expandPowerBase(P('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "p**z*exp_polar(x*z)"],
    ["expandPowerBase(P('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "p**z*exp_polar(x*z)"],
    ["expandPowerBase(P('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(n*x)**j"],
    ["expandPowerBase(P('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "n**j*x**j"],
    ["expandPowerBase(P('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(PPolar('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2.5**z*x**z*(-n)**z"],
    ["expandPowerBase(P('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(PPolar('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2.5)**z*n**z*x**z"],
    ["expandTrig(P('sin(x+y)'))", () => expandTrig(PPolar('sin(x+y)')), "sin(x)*cos(y) + sin(y)*cos(x)"],
    ["expandTrig(P('cos(x+y)'))", () => expandTrig(PPolar('cos(x+y)')), "-sin(x)*sin(y) + cos(x)*cos(y)"],
    ["expandTrig(P('tan(x+y)'))", () => expandTrig(PPolar('tan(x+y)')), "(tan(x) + tan(y))/(-tan(x)*tan(y) + 1)"],
    ["expandTrig(P('sin(x+y+z)'))", () => expandTrig(PPolar('sin(x+y+z)')), "(-sin(y)*sin(z) + cos(y)*cos(z))*sin(x) + (sin(y)*cos(z) + sin(z)*cos(y))*cos(x)"],
    ["expandTrig(P('sin(2*x)'))", () => expandTrig(PPolar('sin(2*x)')), "2*sin(x)*cos(x)"],
    ["expandTrig(P('cos(3*x)'))", () => expandTrig(PPolar('cos(3*x)')), "4*cos(x)**3 - 3*cos(x)"],
    ["expandTrig(P('tan(2*x)'))", () => expandTrig(PPolar('tan(2*x)')), "2*tan(x)/(1 - tan(x)**2)"],
    ["expandTrig(P('tan(3*x)'))", () => expandTrig(PPolar('tan(3*x)')), "(-tan(x)**3 + 3*tan(x))/(1 - 3*tan(x)**2)"],
    ["expandTrig(P('sin(2*x+y)'))", () => expandTrig(PPolar('sin(2*x+y)')), "(2*cos(x)**2 - 1)*sin(y) + 2*sin(x)*cos(x)*cos(y)"],
    ["expandTrig(P('cos(2*x)*sin(x)'))", () => expandTrig(PPolar('cos(2*x)*sin(x)')), "(2*cos(x)**2 - 1)*sin(x)"],
    ["expandTrig(P('sin(x/2)'))", () => expandTrig(PPolar('sin(x/2)')), "sin(x/2)"],
    ["expandTrig(P('sin(2)'))", () => expandTrig(PPolar('sin(2)')), "sin(2)"],
    ["expandTrig(P('sin(2*x)**2'))", () => expandTrig(PPolar('sin(2*x)**2')), "4*sin(x)**2*cos(x)**2"],
    ["expandTrig(P('cosh(2*x)'))", () => expandTrig(PPolar('cosh(2*x)')), "sinh(x)**2 + cosh(x)**2"],
    ["expandTrig(P('sin(I*x)'))", () => expandTrig(PPolar('sin(I*x)')), "I*sinh(x)"],
    ["expandTrig(P('sin(4*x)'))", () => expandTrig(PPolar('sin(4*x)')), "-8*sin(x)**3*cos(x) + 4*sin(x)*cos(x)"],
    ["expandTrig(P('cos(4*x)'))", () => expandTrig(PPolar('cos(4*x)')), "8*cos(x)**4 - 8*cos(x)**2 + 1"],
    ["expandTrig(P('sin(5*x)'))", () => expandTrig(PPolar('sin(5*x)')), "16*sin(x)**5 - 20*sin(x)**3 + 5*sin(x)"],
    ["expandTrig(P('sin(6*x)'))", () => expandTrig(PPolar('sin(6*x)')), "32*sin(x)**5*cos(x) - 32*sin(x)**3*cos(x) + 6*sin(x)*cos(x)"],
    ["expandTrig(P('tan(x+y+z)'))", () => expandTrig(PPolar('tan(x+y+z)')), "(-tan(x)*tan(y)*tan(z) + tan(x) + tan(y) + tan(z))/(-tan(x)*tan(y) - tan(x)*tan(z) - tan(y)*tan(z) + 1)"],
    ["expandTrig(P('tan(x+y+z+w)'))", () => expandTrig(PPolar('tan(x+y+z+w)')), "(-tan(w)*tan(x)*tan(y) - tan(w)*tan(x)*tan(z) - tan(w)*tan(y)*tan(z) + tan(w) - tan(x)*tan(y)*tan(z) + tan(x) + tan(y) + tan(z))/(tan(w)*tan(x)*tan(y)*tan(z) - tan(w)*tan(x) - tan(w)*tan(y) - tan(w)*tan(z) - tan(x)*tan(y) - tan(x)*tan(z) - tan(y)*tan(z) + 1)"],
    ["expandTrig(P('tanh(x+y)'))", () => expandTrig(PPolar('tanh(x+y)')), "(tanh(x) + tanh(y))/(tanh(x)*tanh(y) + 1)"],
    ["expandTrig(P('tanh(x+y+z)'))", () => expandTrig(PPolar('tanh(x+y+z)')), "(tanh(x)*tanh(y)*tanh(z) + tanh(x) + tanh(y) + tanh(z))/(tanh(x)*tanh(y) + tanh(x)*tanh(z) + tanh(y)*tanh(z) + 1)"],
    ["expandTrig(P('tanh(3*x)'))", () => expandTrig(PPolar('tanh(3*x)')), "(tanh(x)**3 + 3*tanh(x))/(3*tanh(x)**2 + 1)"],
    ["expandTrig(P('sinh(x+y)'))", () => expandTrig(PPolar('sinh(x+y)')), "sinh(x)*cosh(y) + sinh(y)*cosh(x)"],
    ["expandTrig(P('sinh(3*x)'))", () => expandTrig(PPolar('sinh(3*x)')), "sinh(x)**3 + 3*sinh(x)*cosh(x)**2"],
    ["expandTrig(P('cosh(x+y)'))", () => expandTrig(PPolar('cosh(x+y)')), "sinh(x)*sinh(y) + cosh(x)*cosh(y)"],
    ["expandTrig(P('tanh(2*x)'))", () => expandTrig(PPolar('tanh(2*x)')), "2*tanh(x)/(tanh(x)**2 + 1)"],
    ["expandTrig(P('sin(x*y)'))", () => expandTrig(PPolar('sin(x*y)')), "sin(x*y)"],
    ["expandTrig(P('cos(x+1)'))", () => expandTrig(PPolar('cos(x+1)')), "-sin(1)*sin(x) + cos(1)*cos(x)"],
    ["expandTrig(P('tan(2*x+y)'))", () => expandTrig(PPolar('tan(2*x+y)')), "(tan(y) + 2*tan(x)/(1 - tan(x)**2))/(1 - 2*tan(x)*tan(y)/(1 - tan(x)**2))"],
    ["expandTrig(P('tan(x/2)'))", () => expandTrig(PPolar('tan(x/2)')), "tan(x/2)"],
    ["expandTrig(P('tanh(x/3)'))", () => expandTrig(PPolar('tanh(x/3)')), "tanh(x/3)"],
    ["expandTrig(P('sinh(x/2)'))", () => expandTrig(PPolar('sinh(x/2)')), "sinh(x/2)"],
    ["expandTrig(P('cot(2*x)'))", () => expandTrig(PPolar('cot(2*x)')), "(cot(x)**2 - 1)/(2*cot(x))"],
    ["expandTrig(P('cos(7*x)'))", () => expandTrig(PPolar('cos(7*x)')), "64*cos(x)**7 - 112*cos(x)**5 + 56*cos(x)**3 - 7*cos(x)"],
    ["expandTrig(P('cot(3*x)'))", () => expandTrig(PPolar('cot(3*x)')), "(cot(x)**3 - 3*cot(x))/(3*cot(x)**2 - 1)"],
    ["expandTrig(P('cot(x+y)'))", () => expandTrig(PPolar('cot(x+y)')), "(cot(x)*cot(y) - 1)/(cot(x) + cot(y))"],
    ["expandTrig(P('cot(x+y+z)'))", () => expandTrig(PPolar('cot(x+y+z)')), "(cot(x)*cot(y)*cot(z) - cot(x) - cot(y) - cot(z))/(cot(x)*cot(y) + cot(x)*cot(z) + cot(y)*cot(z) - 1)"],
    ["expandTrig(P('coth(2*x)'))", () => expandTrig(PPolar('coth(2*x)')), "(coth(x)**2 + 1)/(2*coth(x))"],
    ["expandTrig(P('coth(3*x)'))", () => expandTrig(PPolar('coth(3*x)')), "(coth(x)**3 + 3*coth(x))/(3*coth(x)**2 + 1)"],
    ["expandTrig(P('coth(x+y)'))", () => expandTrig(PPolar('coth(x+y)')), "(coth(x)*coth(y) + 1)/(coth(x) + coth(y))"],
    ["expandTrig(P('coth(x+y+z)'))", () => expandTrig(PPolar('coth(x+y+z)')), "(coth(x)*coth(y)*coth(z) + coth(x) + coth(y) + coth(z))/(coth(x)*coth(y) + coth(x)*coth(z) + coth(y)*coth(z) + 1)"],
    ["expandTrig(P('cot(x/2)'))", () => expandTrig(PPolar('cot(x/2)')), "cot(x/2)"],
    ["expandTrig(P('coth(x)'))", () => expandTrig(PPolar('coth(x)')), "coth(x)"],
    ["expandTrig(P('csc(2*x)'))", () => expandTrig(PPolar('csc(2*x)')), "1/(2*sin(x)*cos(x))"],
    ["expandTrig(P('csc(x)'))", () => expandTrig(PPolar('csc(x)')), "1/sin(x)"],
    ["expandTrig(P('sec(x+y)'))", () => expandTrig(PPolar('sec(x+y)')), "1/(-sin(x)*sin(y) + cos(x)*cos(y))"],
    ["expandTrig(P('sech(2*x)'))", () => expandTrig(PPolar('sech(2*x)')), "1/(sinh(x)**2 + cosh(x)**2)"],
    ["expandTrig(P('csch(x)'))", () => expandTrig(PPolar('csch(x)')), "1/sinh(x)"],
    ["expandTrig(P('sec(2*x)'))", () => expandTrig(PPolar('sec(2*x)')), "1/(2*cos(x)**2 - 1)"],
    ["expandTrig(P('sin(3*x)'))", () => expandTrig(PPolar('sin(3*x)')), "-4*sin(x)**3 + 3*sin(x)"],
    ["expandTrig(P('sin(7*x)'))", () => expandTrig(PPolar('sin(7*x)')), "-64*sin(x)**7 + 112*sin(x)**5 - 56*sin(x)**3 + 7*sin(x)"],
    ["expandTrig(P('log(x+1)'))", () => expandTrig(PPolar('log(x+1)')), "log(x + 1)"],
    ["expandComplex(P('exp(x+I*y)'))", () => expandComplex(PPolar('exp(x+I*y)')), "I*exp(re(x) - im(y))*sin(re(y) + im(x)) + exp(re(x) - im(y))*cos(re(y) + im(x))"],
    ["expandComplex(P('sin(x+I*y)'))", () => expandComplex(PPolar('sin(x+I*y)')), "sin(re(x) - im(y))*cosh(re(y) + im(x)) + I*cos(re(x) - im(y))*sinh(re(y) + im(x))"],
    ["expandComplex(P('cos(x+I*y)'))", () => expandComplex(PPolar('cos(x+I*y)')), "-I*sin(re(x) - im(y))*sinh(re(y) + im(x)) + cos(re(x) - im(y))*cosh(re(y) + im(x))"],
    ["expandComplex(P('exp(I*x)'))", () => expandComplex(PPolar('exp(I*x)')), "I*exp(-im(x))*sin(re(x)) + exp(-im(x))*cos(re(x))"],
    ["expandComplex(P('sin(x)'))", () => expandComplex(PPolar('sin(x)')), "sin(re(x))*cosh(im(x)) + I*cos(re(x))*sinh(im(x))"],
    ["expandComplex(P('tan(x)'))", () => expandComplex(PPolar('tan(x)')), "sin(2*re(x))/(cos(2*re(x)) + cosh(2*im(x))) + I*sinh(2*im(x))/(cos(2*re(x)) + cosh(2*im(x)))"],
    ["expandComplex(P('re(x)'))", () => expandComplex(PPolar('re(x)')), "re(x)"],
    ["expandComplex(P('im(x)'))", () => expandComplex(PPolar('im(x)')), "im(x)"],
    ["expandComplex(P('tan(r)', {r: {real: true}}))", () => expandComplex(PPolar('tan(r)', {r: {real: true}})), "tan(r)"],
    ["expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { frac: true })", () => expand(PPolar('(x+1)*(x+2)/((x-1)*(x+3))'), { frac: true }), "(x**2 + 3*x + 2)/(x**2 + 2*x - 3)"],
    ["expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { numer: true })", () => expand(PPolar('(x+1)*(x+2)/((x-1)*(x+3))'), { numer: true }), "(x**2 + 3*x + 2)/((x - 1)*(x + 3))"],
    ["expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { denom: true })", () => expand(PPolar('(x+1)*(x+2)/((x-1)*(x+3))'), { denom: true }), "(x + 1)*(x + 2)/(x**2 + 2*x - 3)"],
    ["expand(P('gamma(x+2)'), { func: true })", () => expand(PPolar('gamma(x+2)'), { func: true }), "x**2*gamma(x) + x*gamma(x)"],
    ["expand(P('x*(y+1)'), { mul: false })", () => expand(PPolar('x*(y+1)'), { mul: false }), "x*(y + 1)"],
    ["expand(P('(x+1)**2*(y+1)'), { deep: false })", () => expand(PPolar('(x+1)**2*(y+1)'), { deep: false }), "y*(x + 1)**2 + (x + 1)**2"],
    ["expand(P('(x+y)**2'), { mul: false })", () => expand(PPolar('(x+y)**2'), { mul: false }), "x**2 + 2*x*y + y**2"],
    ["expand(P('(x+y)**2*(x+1)'), { mul: false, deep: false })", () => expand(PPolar('(x+y)**2*(x+1)'), { mul: false, deep: false }), "(x + 1)*(x + y)**2"],
    ["expand(P('exp(x+y)*(x+1)'), { power_exp: false })", () => expand(PPolar('exp(x+y)*(x+1)'), { power_exp: false }), "x*exp(x + y) + exp(x + y)"],
    ["expand(P('2**(x+y)'))", () => expand(PPolar('2**(x+y)')), "2**x*2**y"],
    ["expand(P('x**(y+z)'))", () => expand(PPolar('x**(y+z)')), "x**(y + z)"],
    ["expand(P('x**(y+z)'), { force: true })", () => expand(PPolar('x**(y+z)'), { force: true }), "x**y*x**z"],
    ["expand(P('x**(-y-z)'))", () => expand(PPolar('x**(-y-z)')), "x**(-y - z)"],
    ["expand(P('sin(x+y)'), { trig: true })", () => expand(PPolar('sin(x+y)'), { trig: true }), "sin(x)*cos(y) + sin(y)*cos(x)"],
    ["expand(P('log(x*y)'), { log: true, force: true, mul: false })", () => expand(PPolar('log(x*y)'), { log: true, force: true, mul: false }), "log(x) + log(y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('expand_complex (cov2): products and powers', () => {
  // SymPy 1.14 writes these with its Mul/Pow as_real_imag (not ported): (x + I*y)**2 is
  // (re(x) - im(y))**2 + 2*I*(re(x) - im(y))*(re(y) + im(x)) - (re(y) + im(x))**2 and x*(y + I) is
  // I*((im(y) + 1)*re(x) + re(y)*im(x)) - (im(y) + 1)*im(x) + re(x)*re(y); symjs expands first and takes
  // re and im of the expanded form, which has the same value
  const at = (e: Expr): [number, number] => {
    const v = e.subs([[symbol('x'), PPolar('3/10 + 7*I/10')], [symbol('y'), PPolar('-11/10 + 2*I/5')]]).toComplex();
    return [v.re, v.im];
  };
  it.each([
    ['(x+I*y)**2', '(re(x) - im(y))**2 + 2*I*(re(x) - im(y))*(re(y) + im(x)) - (re(y) + im(x))**2'],
    ['x*(y + I)', 'I*((im(y) + 1)*re(x) + re(y)*im(x)) - (im(y) + 1)*im(x) + re(x)*re(y)'],
  ])('%s', (src, sympyForm) => {
    const got = expandComplex(PPolar(src));
    const [r1, i1] = at(got);
    const [r2, i2] = at(PPolar(sympyForm));
    expect(r1).toBeCloseTo(r2, 12);
    expect(i1).toBeCloseTo(i2, 12);
    expect(String(got)).not.toContain('**2*(');
  });
});

describe('expandMul (cov2): the round limit', () => {
  it('returns the result of the passes made when the limit is reached', () => {
    // one pass of (x + 1)**2*(y + 1) distributes completely; the second pass would only confirm it
    expect(String(expandMulRounds(PPolar('(x + 1)**2*(y + 1)'), 1))).toBe('x**2*y + x**2 + 2*x*y + 2*x + y + 1');
  });
});

describe("powsimp, powdenest, logcombine, expand_log (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    // SymPy 1.14 gives (p**2.5*q**3.0)**(1.0*z), the same value: its gcd of the coefficients 2.5 and 3 of the logarithms is 1.0, symjs keeps exact exponents
    ["expandLog(P('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3*log(2)"],
    ["expandLog(P('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "3*log(2)"],
    ["expandLog(P('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2*log(2)"],
    ["expandLog(P('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(2)"],
    ["expandLog(P('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2*log(6)"],
    ["expandLog(P('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(36)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(6)"],
    ["expandLog(P('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(12)"],
    ["expandLog(P('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(12)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(12)"],
    ["expandLog(P('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-2*log(2) + log(3)"],
    ["expandLog(P('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-2*log(2) + log(3)"],
    ["expandLog(P('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-2*log(3) + 3*log(2)"],
    ["expandLog(P('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(8/9)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-2*log(3) + 3*log(2)"],
    ["expandLog(P('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-3*log(2)"],
    ["expandLog(P('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(1/8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-3*log(2)"],
    ["expandLog(P('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "100*log(2)"],
    ["expandLog(P('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(2**100)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "100*log(2)"],
    ["expandLog(P('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x) + 10*log(2)"],
    ["expandLog(P('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(1024*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x) + 10*log(2)"],
    ["expandLog(P('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "3*log(2) + I*pi"],
    ["expandLog(P('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(-8)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "3*log(2) + I*pi"],
    ["expandLog(P('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-2*log(2) + log(3) + I*pi"],
    ["expandLog(P('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(-3/4)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-2*log(2) + log(3) + I*pi"],
    ["expandLog(P('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "4"],
    ["expandLog(P('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(16)/log(2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "4"],
    ["expandLog(P('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x)/2"],
    ["expandLog(P('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x)/2"],
    ["expandLog(P('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x)/3"],
    ["expandLog(P('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(x**(1/3))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x)/3"],
    ["expandLog(P('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x**2)"],
    ["expandLog(P('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(x**2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(x)"],
    ["expandLog(P('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(1/x)"],
    ["expandLog(P('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(1/x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-log(x)"],
    ["expandLog(P('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "-log(x)/2"],
    ["expandLog(P('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(x**(-1/2))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "-log(x)/2"],
    ["expandLog(P('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x**y)"],
    ["expandLog(P('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(x**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "y*log(x)"],
    ["expandLog(P('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(p**y)"],
    ["expandLog(P('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(p**y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "y*log(p)"],
    ["expandLog(P('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(exp(x))"],
    ["expandLog(P('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(exp(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "x"],
    ["expandLog(P('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(-y) + log(2)"],
    ["expandLog(P('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(-2*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(y) + log(2) + I*pi"],
    ["expandLog(P('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x) - log(2)"],
    ["expandLog(P('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(x/2)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(x) - log(2)"],
    ["expandLog(P('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(-n) + log(-x)"],
    ["expandLog(P('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(n*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(n) + log(x)"],
    ["expandLog(P('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(p) + log(x*y)"],
    ["expandLog(P('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(p*x*y)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(p) + log(x) + log(y)"],
    ["expandLog(P('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "2*log(p) + log(x)"],
    ["expandLog(P('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(p**2*x)', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*log(p) + log(x)"],
    ["expandLog(P('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(p) + log(x)/2 + log(2)"],
    ["expandLog(P('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(2*p*sqrt(x))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "log(p) + log(x)/2 + log(2)"],
    ["expandLog(P('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}))", () => expandLog(PA('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}})), "log(x**(2*I))"],
    ["expandLog(P('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true)", () => expandLog(PA('log(x**(2*I))', {p: {positive: true}, q: {positive: true}, n: {negative: true}}), true), "2*I*log(x)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('expand_mul leaves integer powers of sums (SymPy 1.14)', () => {
  it('distributes products only', async () => {
    const { expand_mul: em, parse: p } = await import('../../src');
    expect(String(em(p('(x + 1)**2*(y + 1)')))).toBe('y*(x + 1)**2 + (x + 1)**2');
    expect(String(em(p('x*(x + (y + 1)**2*(x + 2))')))).toBe('x**2*(y + 1)**2 + x**2 + 2*x*(y + 1)**2');
  });
});

describe('multinomial expansion of rational powers of sums (SymPy Pow._eval_expand_multinomial)', () => {
  it('splits off the integer part of the exponent', () => {
    // SymPy 1.14
    expect(String(expand(parse('(y - 1)**(3/2)')))).toBe('y*sqrt(y - 1) - sqrt(y - 1)');
    expect(String(expand(parse('(x + y)**(5/2)')))).toBe('x**2*sqrt(x + y) + 2*x*y*sqrt(x + y) + y**2*sqrt(x + y)');
    expect(String(expand(parse('(x + 1)**(-3/2)')))).toBe('1/(x*sqrt(x + 1) + sqrt(x + 1))');
    expect(String(expand(parse('(x + 1)**(4/3)')))).toBe('x*(x + 1)**(1/3) + (x + 1)**(1/3)');
    expect(String(expand(parse('sqrt(x + 1)')))).toBe('sqrt(x + 1)');
    expect(String(expandMultinomial(parse('(x + 1)**(5/2)')))).toBe('x**2*sqrt(x + 1) + 2*x*sqrt(x + 1) + sqrt(x + 1)');
    expect(String(expandMultinomial(parse('(x + 1)**(-5/2)')))).toBe('1/(x**2*sqrt(x + 1) + 2*x*sqrt(x + 1) + sqrt(x + 1))');
    expect(String(expandMultinomial(parse('(x + 1)**(-2)')))).toBe('1/(x**2 + 2*x + 1)');
    expect(String(expandMultinomial(parse('(x + 1)**(-1/2)')))).toBe('1/sqrt(x + 1)');
  });
});

describe('core expansion gaps', () => {
  it('reduces each numeric coefficient modulo a positive integer', () => {
    expect(String(expand(P('(x+y)**11'), { modulus: 11 }))).toBe('x**11 + y**11');
    expect(String(expand(P('(x+sqrt(2)*y)**11'), { modulus: 11 }))).toBe('x**11 + 10*sqrt(2)*y**11');
    expect(String(expand(P('x+y/2'), { modulus: 1 }))).toBe('y/2');
    expect(String(expand(P('1.5*x+y'), { modulus: 2 }))).toBe('1.5*x + y');
    for (const modulus of [0, -1, x, P('1/2')]) expect(() => expand(x, { modulus })).toThrow(RangeError);
  });
  it('keeps noncommutative exponents together', () => {
    const A = new Sym('A', { commutative: false });
    const B = new Sym('B', { commutative: false });
    expect(String(expand(pow(2, add(A, B))))).toBe('2**(A + B)');
  });
  it('expands hyperbolic functions into real and imaginary parts', () => {
    const locals = { symbols: [new Sym('x', { real: true }), new Sym('y', { real: true })] };
    expect(String(expand(parse('sinh(x+I*y)', locals), { complex: true }))).toBe('I*sin(y)*cosh(x) + cos(y)*sinh(x)');
    expect(String(expand(parse('cosh(x+I*y)', locals), { complex: true }))).toBe('I*sin(y)*sinh(x) + cos(y)*cosh(x)');
  });
});

it('dispatches expansion hints and top level expansion through extension nodes', async () => {
  const { ExtensionExpr, S } = await import('../../src');
  const { impl } = await import('../../src/core/nodes');
  class Expandable extends ExtensionExpr {
    constructor(readonly top = false) { super('Expandable', [x]); }
    withArgs(): Expr { return this; }
    override expandTop(): Expr | undefined { return this.top ? S.One : undefined; }
    override expandSelf(hint: string): Expr | undefined { return hint === 'double' ? mul(2, x) : undefined; }
  }
  expect(String(expand(new Expandable(true)))).toBe('1');
  expect(String(expand(new Expandable(), { double: true }))).toBe('2*x');
  expect(String(expand(new Expandable(), { other: true }))).toBe('Expandable(x)');
  expect(String(expand(add(x, y), { other: true }))).toBe('x + y');
  expect(String(impl.expand?.(pow(add(x, 1), 2)))).toBe('x**2 + 2*x + 1');
  expect(impl.asRealImagExpand?.(x).map(String)).toEqual(['re(x)', 'im(x)']);
});

it('expands exact numerators, reciprocal products, numeric powers, and logarithm ratios', () => {
  expect(String(expand(parse('x*(x+1)/y'), { numer: true, exact: true }))).toBe('(x**2 + x)/y');
  expect(String(expand(parse('1/(y*(x+1))')))).toBe('1/(x*y + y)');
  expect(String(expandMultinomial(parse('3**(x+y+3)')))).toBe('27*3**(x + y)');
  expect(String(expandLog(parse('log(42)/log(6)')))).toBe('1 + log(7)/log(6)');
  expect(String(expandLog(parse('log(42)'), false, { factor: true }))).toBe('log(2) + log(3) + log(7)');
});

it('expands a principal square root with exact real and imaginary parts', () => {
  expect(String(expand(parse('sqrt(-527/15625 - 336*I/15625)')))).toBe('7/125 - 24*I/125');
  expect(String(expand(parse('sqrt(3 + 4*I)')))).toBe('2 + I');
  expect(String(expand(parse('sqrt(1 + I)')))).toBe('sqrt(1 + I)');
  expect(String(expandLog(parse('log(7)/log(3)')))).toBe('log(7)/log(3)');
});

it('keeps nonrational roots and expands a positive imaginary component exactly', () => {
  expect(String(expand(parse('sqrt(3+4*I)')))).toBe('2 + I');
  expect(String(expand(parse('sqrt(2+I)')))).toBe('sqrt(2 + I)');
  expect(String(expandLog(parse('log(1)'), false, { factor: true }))).toBe('0');
});

it('retains an irreducible complex square root and handles unevaluated special cases', async () => {
  const s = await import('../../src');
  const p = new s.Pow(add(6, mul(8, I)), s.S.Half);
  expect(expandMultinomial(p).key).toBe(p.key);
  const zeroPower = new s.Pow(s.S.Zero, new s.Add([s.S.Two, s.S.One]));
  expect(expandMultinomial(zeroPower)).toBe(s.S.Zero);
  expect(expandLog(new s.Fn('log', [s.S.One])).key).toBe(s.S.Zero.key);
});

it('expands the base of an unevaluated logarithm', async () => {
  const { fn } = await import('../../src');
  expect(String(expandLog(fn('log', [x, 10], { evaluate: false })))).toBe('log(x)/log(10)');
});

describe('product denominators (SymPy Mul._eval_expand_mul)', () => {
  const [a, b, c] = symbols('a b c');
  const P = (s: string) => parse(s, { symbols: { a, b, c } });
  it('multiplies out a denominator that is a product', () => {
    expect(sstr(expand(P('1/(a*(b + c))')))).toBe('1/(a*b + a*c)');
    expect(sstr(expand(P('2*a/(b*(c + 1))')))).toBe('2*a/(b*c + b)');
    expect(sstr(expand(P('(a + b)/(c*(a + 1))')))).toBe('a/(a*c + c) + b/(a*c + c)');
    expect(sstr(expand(P('1/(2*(b + c))')))).toBe('1/(2*b + 2*c)');
    expect(sstr(expand(P('a/(b + c)**2')))).toBe('a/(b**2 + 2*b*c + c**2)');
  });
  it('does so for the mul hint alone and without deep', () => {
    expect(sstr(expand(P('1/(a*(b + c))'), { power_exp: false, power_base: false, log: false, multinomial: false }))).toBe('1/(a*b + a*c)');
    expect(sstr(expand(P('1/(a*(b + c))'), { deep: false }))).toBe('1/(a*b + a*c)');
  });
  it('leaves other denominators as they are', () => {
    expect(sstr(expand(P('1/(a*sqrt(b + c))')))).toBe('1/(a*sqrt(b + c))');
    expect(sstr(expand(P('1/(a*b)')))).toBe('1/(a*b)');
    expect(sstr(expand(P('1/(b + c)')))).toBe('1/(b + c)');
  });
});

it('allows scoped callers to keep product denominators factored', async () => {
  const sj = await import('../../src');
  const { withFactoredDenominators } = await import('../../src/simplify/expand');
  const input = parse('1/(y*(x + 1))');
  expect(String(withFactoredDenominators(() => {
    expect(String(withFactoredDenominators(() => expand(input)))).toBe('1/(y*(x + 1))');
    return expand(input);
  }))).toBe('1/(y*(x + 1))');
  expect(String(expand(input))).toBe('1/(x*y + y)');
  expect(String(withFactoredDenominators(() => expand(parse('1/((x+1)*(y+2))'))))).toBe('1/((x + 1)*(y + 2))');
  const a = new sj.Add([x, sj.neg(x), sj.S.Two]);
  const b = new sj.Add([y, sj.neg(y), sj.Rational.of(3)]);
  const raw = new sj.Mul([new sj.Pow(a, sj.S.NegOne), new sj.Pow(b, sj.S.NegOne), x]);
  expect(String(withFactoredDenominators(() => expand(raw, {
    deep: false, power_exp: false, power_base: false, log: false, multinomial: false,
  })))).toBe('x/6');
});

it('expands exponential sums, logarithmic products and complex hyperbolic functions', async () => {
  const sj = await import('../../src');
  const n = symbol('n');
  const p = symbol('p', { positive: true });
  const a = symbol('a', { commutative: false });
  expect(String(sj.expandPowerExp(sj.exp(sj.Sum(x, [x, 1, n]))))).toBe('Product(exp(x), (x, 1, n))');
  expect(String(sj.expandPowerExp(sj.exp(sj.Sum(a, [x, 1, n]))))).toBe('exp(Sum(a, (x, 1, n)))');
  const product = (f: Expr): Expr => sj.fn('log', [sj.Product(f, [x, 1, n])], { evaluate: false });
  expect(String(expandLog(product(x), true))).toBe('Sum(log(x), (x, 1, n))');
  expect(String(expandLog(product(p.mul(x.pow(2)).add(1))))).toBe('log(Product(p*x**2 + 1, (x, 1, n)))');
  expect(String(expandLog(product(p.pow(x))))).toBe('log(Product(p**x, (x, 1, n)))');
  expect(String(expandLog(product(p)))).toBe('Sum(log(p), (x, 1, n))');
  const [r, i] = sj.symbols('r i', { real: true });
  for (const name of ['tanh', 'coth', 'sech', 'csch'] as const) {
    const e = sj.fn(name, [r.add(sj.I.mul(i))]);
    const atPoint = new Map([[r, sj.S.One], [i, sj.S.Half]]);
    const before = sj.evalf(e.subs(atPoint)).toComplex();
    const after = sj.evalf(sj.expandComplex(e).subs(atPoint)).toComplex();
    expect(after.re).toBeCloseTo(before.re);
    expect(after.im).toBeCloseTo(before.im);
  }
});

it('expands a logarithm into the logarithm of the modulus and the argument (SymPy log.as_real_imag)', () => {
  const x = new sj.Sym('x');
  const p = new sj.Sym('p', { positive: true });
  const c = (e: sj.Expr) => String(sj.expand(e, { complex: true }));
  expect(c(sj.log(sj.add(3, sj.mul(4, sj.I))))).toBe('log(5) + I*atan(4/3)');
  expect(c(sj.log(x))).toBe('log(re(x)**2 + im(x)**2)/2 + I*arg(re(x) + I*im(x))');
  expect(c(sj.log(p))).toBe('log(p)');
  expect(c(sj.log(sj.mul(-1, p)))).toBe('log(p) + I*pi');
  expect(c(sj.log(sj.add(1, sj.I)))).toBe('log(2)/2 + I*pi/4');
  // the log of a nonnegative argument is its own real part
  const u = sj.add(sj.pow(sj.re(x), 2), sj.pow(sj.im(x), 2));
  expect(String(sj.re(sj.log(u)))).toBe('log(re(x)**2 + im(x)**2)');
  expect(String(sj.im(sj.log(u)))).toBe('0');
});
