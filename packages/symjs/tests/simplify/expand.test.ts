// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/expand.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, I, Sym, add, expPolar, expand, expandComplex, expandLog, expandMultinomial, expandPowerBase, expandTrig, mul, parse, pow, sstr, symbol, symbols } from '../../src';
import type { Expr } from '../../src';
import { expandMulRounds } from '../../src/simplify/expand';

const [x, y] = symbols('x y');
const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
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
