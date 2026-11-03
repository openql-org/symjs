// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { expPolar, expand, expandComplex, expandPowerBase, expandTrig, parse, symbol } from '../src';
import { expandMulRounds } from '../src/simplify/expand';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const P = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { locals: { exp_polar: expPolar }, symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });

const show = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(show).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${show(k)}: ${show(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe("expand (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["expandPowerBase(P('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "A*B*A*B"],
    ["expandPowerBase(P('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "A*B*A*B"],
    ["expandPowerBase(P('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "B**(-1)*A**(-1)*B**(-1)*A**(-1)"],
    ["expandPowerBase(P('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(A*B)**(-2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "B**(-1)*A**(-1)*B**(-1)*A**(-1)"],
    ["expandPowerBase(P('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "4*A*B*A*B"],
    ["expandPowerBase(P('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(2*A*B)**2', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "4*A*B*A*B"],
    ["expandPowerBase(P('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "x**3*A*B*A*B*A*B"],
    ["expandPowerBase(P('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(x*A*B)**3', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "x**3*A*B*A*B*A*B"],
    ["expandPowerBase(P('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(A*B)**x"],
    ["expandPowerBase(P('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(A*B)**x"],
    ["expandPowerBase(P('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**x*(A*B)**x"],
    ["expandPowerBase(P('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(2*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2**x*(A*B)**x"],
    ["expandPowerBase(P('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "p**x*(A*B)**x"],
    ["expandPowerBase(P('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(p*A*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "p**x*(A*B)**x"],
    ["expandPowerBase(P('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(A**2*B)**x"],
    ["expandPowerBase(P('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(A**2*B)**x', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(A**2*B)**x"],
    ["expandPowerBase(P('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(x*y)**z"],
    ["expandPowerBase(P('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "x**z*y**z"],
    ["expandPowerBase(P('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "p**z*x**z"],
    ["expandPowerBase(P('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(p*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "p**z*x**z"],
    ["expandPowerBase(P('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**z*(-x)**z"],
    ["expandPowerBase(P('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-2*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*x**z"],
    ["expandPowerBase(P('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(I*x)**z"],
    ["expandPowerBase(P('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(I*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "I**z*x**z"],
    ["expandPowerBase(P('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(n*x)**z"],
    ["expandPowerBase(P('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "n**z*x**z"],
    ["expandPowerBase(P('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(-k)**z*(-n)**z"],
    ["expandPowerBase(P('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "k**z*n**z"],
    ["expandPowerBase(P('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**z*x**z*(-n)**z"],
    ["expandPowerBase(P('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-2*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*n**z*x**z"],
    ["expandPowerBase(P('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "x**z*(-n)**z"],
    ["expandPowerBase(P('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-1)**z*n**z*x**z"],
    ["expandPowerBase(P('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(n*x*y)**z"],
    ["expandPowerBase(P('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(n*x*y)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "n**z*x**z*y**z"],
    ["expandPowerBase(P('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(-2)**z*(-k)**z*(-n)**z"],
    ["expandPowerBase(P('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-2*n*k)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*k**z*n**z"],
    ["expandPowerBase(P('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**z*(-k)**z*(-n)**z*(-x)**z"],
    ["expandPowerBase(P('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-2*n*k*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2)**z*k**z*n**z*x**z"],
    ["expandPowerBase(P('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "I**z*p**z"],
    ["expandPowerBase(P('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(I*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "I**z*p**z"],
    ["expandPowerBase(P('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(-x)**z"],
    ["expandPowerBase(P('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-1)**z*x**z"],
    ["expandPowerBase(P('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2*sqrt(x*y)"],
    ["expandPowerBase(P('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(4*x*y)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2*sqrt(x)*sqrt(y)"],
    ["expandPowerBase(P('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2*sqrt(-x)"],
    ["expandPowerBase(P('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-4*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2*I*sqrt(x)"],
    ["expandPowerBase(P('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2**(1/6)*sqrt(x)"],
    ["expandPowerBase(P('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(2**(1/3)*x)**(1/2)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "2**(1/6)*sqrt(x)"],
    ["expandPowerBase(P('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "q**z*x**z"],
    ["expandPowerBase(P('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(q*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "q**z*x**z"],
    ["expandPowerBase(P('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "x**z*exp_polar(2*z)"],
    ["expandPowerBase(P('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(exp_polar(2)*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "x**z*exp_polar(2*z)"],
    ["expandPowerBase(P('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "p**z*exp_polar(x*z)"],
    ["expandPowerBase(P('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(exp_polar(x)*p)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "p**z*exp_polar(x*z)"],
    ["expandPowerBase(P('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "(n*x)**j"],
    ["expandPowerBase(P('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(n*x)**(j)', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "n**j*x**j"],
    ["expandPowerBase(P('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}))", () => expandPowerBase(P('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}})), "2.5**z*x**z*(-n)**z"],
    ["expandPowerBase(P('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true })", () => expandPowerBase(P('(-2.5*n*x)**z', {A: {commutative: false}, B: {commutative: false}, p: {positive: true}, n: {negative: true}, k: {negative: true}, q: {polar: true}}), { force: true }), "(-2.5)**z*n**z*x**z"],
    ["expandTrig(P('sin(x+y)'))", () => expandTrig(P('sin(x+y)')), "sin(x)*cos(y) + sin(y)*cos(x)"],
    ["expandTrig(P('cos(x+y)'))", () => expandTrig(P('cos(x+y)')), "-sin(x)*sin(y) + cos(x)*cos(y)"],
    ["expandTrig(P('tan(x+y)'))", () => expandTrig(P('tan(x+y)')), "(tan(x) + tan(y))/(-tan(x)*tan(y) + 1)"],
    ["expandTrig(P('sin(x+y+z)'))", () => expandTrig(P('sin(x+y+z)')), "(-sin(y)*sin(z) + cos(y)*cos(z))*sin(x) + (sin(y)*cos(z) + sin(z)*cos(y))*cos(x)"],
    ["expandTrig(P('sin(2*x)'))", () => expandTrig(P('sin(2*x)')), "2*sin(x)*cos(x)"],
    ["expandTrig(P('cos(3*x)'))", () => expandTrig(P('cos(3*x)')), "4*cos(x)**3 - 3*cos(x)"],
    ["expandTrig(P('tan(2*x)'))", () => expandTrig(P('tan(2*x)')), "2*tan(x)/(1 - tan(x)**2)"],
    ["expandTrig(P('tan(3*x)'))", () => expandTrig(P('tan(3*x)')), "(-tan(x)**3 + 3*tan(x))/(1 - 3*tan(x)**2)"],
    ["expandTrig(P('sin(2*x+y)'))", () => expandTrig(P('sin(2*x+y)')), "(2*cos(x)**2 - 1)*sin(y) + 2*sin(x)*cos(x)*cos(y)"],
    ["expandTrig(P('cos(2*x)*sin(x)'))", () => expandTrig(P('cos(2*x)*sin(x)')), "(2*cos(x)**2 - 1)*sin(x)"],
    ["expandTrig(P('sin(x/2)'))", () => expandTrig(P('sin(x/2)')), "sin(x/2)"],
    ["expandTrig(P('sin(2)'))", () => expandTrig(P('sin(2)')), "sin(2)"],
    ["expandTrig(P('sin(2*x)**2'))", () => expandTrig(P('sin(2*x)**2')), "4*sin(x)**2*cos(x)**2"],
    ["expandTrig(P('cosh(2*x)'))", () => expandTrig(P('cosh(2*x)')), "sinh(x)**2 + cosh(x)**2"],
    ["expandTrig(P('sin(I*x)'))", () => expandTrig(P('sin(I*x)')), "I*sinh(x)"],
    ["expandTrig(P('sin(4*x)'))", () => expandTrig(P('sin(4*x)')), "-8*sin(x)**3*cos(x) + 4*sin(x)*cos(x)"],
    ["expandTrig(P('cos(4*x)'))", () => expandTrig(P('cos(4*x)')), "8*cos(x)**4 - 8*cos(x)**2 + 1"],
    ["expandTrig(P('sin(5*x)'))", () => expandTrig(P('sin(5*x)')), "16*sin(x)**5 - 20*sin(x)**3 + 5*sin(x)"],
    ["expandTrig(P('sin(6*x)'))", () => expandTrig(P('sin(6*x)')), "32*sin(x)**5*cos(x) - 32*sin(x)**3*cos(x) + 6*sin(x)*cos(x)"],
    ["expandTrig(P('tan(x+y+z)'))", () => expandTrig(P('tan(x+y+z)')), "(-tan(x)*tan(y)*tan(z) + tan(x) + tan(y) + tan(z))/(-tan(x)*tan(y) - tan(x)*tan(z) - tan(y)*tan(z) + 1)"],
    ["expandTrig(P('tan(x+y+z+w)'))", () => expandTrig(P('tan(x+y+z+w)')), "(-tan(w)*tan(x)*tan(y) - tan(w)*tan(x)*tan(z) - tan(w)*tan(y)*tan(z) + tan(w) - tan(x)*tan(y)*tan(z) + tan(x) + tan(y) + tan(z))/(tan(w)*tan(x)*tan(y)*tan(z) - tan(w)*tan(x) - tan(w)*tan(y) - tan(w)*tan(z) - tan(x)*tan(y) - tan(x)*tan(z) - tan(y)*tan(z) + 1)"],
    ["expandTrig(P('tanh(x+y)'))", () => expandTrig(P('tanh(x+y)')), "(tanh(x) + tanh(y))/(tanh(x)*tanh(y) + 1)"],
    ["expandTrig(P('tanh(x+y+z)'))", () => expandTrig(P('tanh(x+y+z)')), "(tanh(x)*tanh(y)*tanh(z) + tanh(x) + tanh(y) + tanh(z))/(tanh(x)*tanh(y) + tanh(x)*tanh(z) + tanh(y)*tanh(z) + 1)"],
    ["expandTrig(P('tanh(3*x)'))", () => expandTrig(P('tanh(3*x)')), "(tanh(x)**3 + 3*tanh(x))/(3*tanh(x)**2 + 1)"],
    ["expandTrig(P('sinh(x+y)'))", () => expandTrig(P('sinh(x+y)')), "sinh(x)*cosh(y) + sinh(y)*cosh(x)"],
    ["expandTrig(P('sinh(3*x)'))", () => expandTrig(P('sinh(3*x)')), "sinh(x)**3 + 3*sinh(x)*cosh(x)**2"],
    ["expandTrig(P('cosh(x+y)'))", () => expandTrig(P('cosh(x+y)')), "sinh(x)*sinh(y) + cosh(x)*cosh(y)"],
    ["expandTrig(P('tanh(2*x)'))", () => expandTrig(P('tanh(2*x)')), "2*tanh(x)/(tanh(x)**2 + 1)"],
    ["expandTrig(P('sin(x*y)'))", () => expandTrig(P('sin(x*y)')), "sin(x*y)"],
    ["expandTrig(P('cos(x+1)'))", () => expandTrig(P('cos(x+1)')), "-sin(1)*sin(x) + cos(1)*cos(x)"],
    ["expandTrig(P('tan(2*x+y)'))", () => expandTrig(P('tan(2*x+y)')), "(tan(y) + 2*tan(x)/(1 - tan(x)**2))/(1 - 2*tan(x)*tan(y)/(1 - tan(x)**2))"],
    ["expandTrig(P('tan(x/2)'))", () => expandTrig(P('tan(x/2)')), "tan(x/2)"],
    ["expandTrig(P('tanh(x/3)'))", () => expandTrig(P('tanh(x/3)')), "tanh(x/3)"],
    ["expandTrig(P('sinh(x/2)'))", () => expandTrig(P('sinh(x/2)')), "sinh(x/2)"],
    ["expandTrig(P('cot(2*x)'))", () => expandTrig(P('cot(2*x)')), "(cot(x)**2 - 1)/(2*cot(x))"],
    ["expandTrig(P('cos(7*x)'))", () => expandTrig(P('cos(7*x)')), "64*cos(x)**7 - 112*cos(x)**5 + 56*cos(x)**3 - 7*cos(x)"],
    ["expandTrig(P('cot(3*x)'))", () => expandTrig(P('cot(3*x)')), "(cot(x)**3 - 3*cot(x))/(3*cot(x)**2 - 1)"],
    ["expandTrig(P('cot(x+y)'))", () => expandTrig(P('cot(x+y)')), "(cot(x)*cot(y) - 1)/(cot(x) + cot(y))"],
    ["expandTrig(P('cot(x+y+z)'))", () => expandTrig(P('cot(x+y+z)')), "(cot(x)*cot(y)*cot(z) - cot(x) - cot(y) - cot(z))/(cot(x)*cot(y) + cot(x)*cot(z) + cot(y)*cot(z) - 1)"],
    ["expandTrig(P('coth(2*x)'))", () => expandTrig(P('coth(2*x)')), "(coth(x)**2 + 1)/(2*coth(x))"],
    ["expandTrig(P('coth(3*x)'))", () => expandTrig(P('coth(3*x)')), "(coth(x)**3 + 3*coth(x))/(3*coth(x)**2 + 1)"],
    ["expandTrig(P('coth(x+y)'))", () => expandTrig(P('coth(x+y)')), "(coth(x)*coth(y) + 1)/(coth(x) + coth(y))"],
    ["expandTrig(P('coth(x+y+z)'))", () => expandTrig(P('coth(x+y+z)')), "(coth(x)*coth(y)*coth(z) + coth(x) + coth(y) + coth(z))/(coth(x)*coth(y) + coth(x)*coth(z) + coth(y)*coth(z) + 1)"],
    ["expandTrig(P('cot(x/2)'))", () => expandTrig(P('cot(x/2)')), "cot(x/2)"],
    ["expandTrig(P('coth(x)'))", () => expandTrig(P('coth(x)')), "coth(x)"],
    ["expandTrig(P('csc(2*x)'))", () => expandTrig(P('csc(2*x)')), "1/(2*sin(x)*cos(x))"],
    ["expandTrig(P('csc(x)'))", () => expandTrig(P('csc(x)')), "1/sin(x)"],
    ["expandTrig(P('sec(x+y)'))", () => expandTrig(P('sec(x+y)')), "1/(-sin(x)*sin(y) + cos(x)*cos(y))"],
    ["expandTrig(P('sech(2*x)'))", () => expandTrig(P('sech(2*x)')), "1/(sinh(x)**2 + cosh(x)**2)"],
    ["expandTrig(P('csch(x)'))", () => expandTrig(P('csch(x)')), "1/sinh(x)"],
    ["expandTrig(P('sec(2*x)'))", () => expandTrig(P('sec(2*x)')), "1/(2*cos(x)**2 - 1)"],
    ["expandTrig(P('sin(3*x)'))", () => expandTrig(P('sin(3*x)')), "-4*sin(x)**3 + 3*sin(x)"],
    ["expandTrig(P('sin(7*x)'))", () => expandTrig(P('sin(7*x)')), "-64*sin(x)**7 + 112*sin(x)**5 - 56*sin(x)**3 + 7*sin(x)"],
    ["expandTrig(P('log(x+1)'))", () => expandTrig(P('log(x+1)')), "log(x + 1)"],
    ["expandComplex(P('exp(x+I*y)'))", () => expandComplex(P('exp(x+I*y)')), "I*exp(re(x) - im(y))*sin(re(y) + im(x)) + exp(re(x) - im(y))*cos(re(y) + im(x))"],
    ["expandComplex(P('sin(x+I*y)'))", () => expandComplex(P('sin(x+I*y)')), "sin(re(x) - im(y))*cosh(re(y) + im(x)) + I*cos(re(x) - im(y))*sinh(re(y) + im(x))"],
    ["expandComplex(P('cos(x+I*y)'))", () => expandComplex(P('cos(x+I*y)')), "-I*sin(re(x) - im(y))*sinh(re(y) + im(x)) + cos(re(x) - im(y))*cosh(re(y) + im(x))"],
    ["expandComplex(P('exp(I*x)'))", () => expandComplex(P('exp(I*x)')), "I*exp(-im(x))*sin(re(x)) + exp(-im(x))*cos(re(x))"],
    ["expandComplex(P('sin(x)'))", () => expandComplex(P('sin(x)')), "sin(re(x))*cosh(im(x)) + I*cos(re(x))*sinh(im(x))"],
    ["expandComplex(P('tan(x)'))", () => expandComplex(P('tan(x)')), "sin(2*re(x))/(cos(2*re(x)) + cosh(2*im(x))) + I*sinh(2*im(x))/(cos(2*re(x)) + cosh(2*im(x)))"],
    ["expandComplex(P('re(x)'))", () => expandComplex(P('re(x)')), "re(x)"],
    ["expandComplex(P('im(x)'))", () => expandComplex(P('im(x)')), "im(x)"],
    ["expandComplex(P('tan(r)', {r: {real: true}}))", () => expandComplex(P('tan(r)', {r: {real: true}})), "tan(r)"],
    ["expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { frac: true })", () => expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { frac: true }), "(x**2 + 3*x + 2)/(x**2 + 2*x - 3)"],
    ["expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { numer: true })", () => expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { numer: true }), "(x**2 + 3*x + 2)/((x - 1)*(x + 3))"],
    ["expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { denom: true })", () => expand(P('(x+1)*(x+2)/((x-1)*(x+3))'), { denom: true }), "(x + 1)*(x + 2)/(x**2 + 2*x - 3)"],
    ["expand(P('gamma(x+2)'), { func: true })", () => expand(P('gamma(x+2)'), { func: true }), "x**2*gamma(x) + x*gamma(x)"],
    ["expand(P('x*(y+1)'), { mul: false })", () => expand(P('x*(y+1)'), { mul: false }), "x*(y + 1)"],
    ["expand(P('(x+1)**2*(y+1)'), { deep: false })", () => expand(P('(x+1)**2*(y+1)'), { deep: false }), "y*(x + 1)**2 + (x + 1)**2"],
    ["expand(P('(x+y)**2'), { mul: false })", () => expand(P('(x+y)**2'), { mul: false }), "x**2 + 2*x*y + y**2"],
    ["expand(P('(x+y)**2*(x+1)'), { mul: false, deep: false })", () => expand(P('(x+y)**2*(x+1)'), { mul: false, deep: false }), "(x + 1)*(x + y)**2"],
    ["expand(P('exp(x+y)*(x+1)'), { power_exp: false })", () => expand(P('exp(x+y)*(x+1)'), { power_exp: false }), "x*exp(x + y) + exp(x + y)"],
    ["expand(P('2**(x+y)'))", () => expand(P('2**(x+y)')), "2**x*2**y"],
    ["expand(P('x**(y+z)'))", () => expand(P('x**(y+z)')), "x**(y + z)"],
    ["expand(P('x**(y+z)'), { force: true })", () => expand(P('x**(y+z)'), { force: true }), "x**y*x**z"],
    ["expand(P('x**(-y-z)'))", () => expand(P('x**(-y-z)')), "x**(-y - z)"],
    ["expand(P('sin(x+y)'), { trig: true })", () => expand(P('sin(x+y)'), { trig: true }), "sin(x)*cos(y) + sin(y)*cos(x)"],
    ["expand(P('log(x*y)'), { log: true, force: true, mul: false })", () => expand(P('log(x*y)'), { log: true, force: true, mul: false }), "log(x) + log(y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe('expand_complex (cov2): products and powers', () => {
  // SymPy 1.14 writes these with its Mul/Pow as_real_imag (not ported): (x + I*y)**2 is
  // (re(x) - im(y))**2 + 2*I*(re(x) - im(y))*(re(y) + im(x)) - (re(y) + im(x))**2 and x*(y + I) is
  // I*((im(y) + 1)*re(x) + re(y)*im(x)) - (im(y) + 1)*im(x) + re(x)*re(y); symjs expands first and takes
  // re and im of the expanded form, which has the same value
  const at = (e: Expr): [number, number] => {
    const v = e.subs([[symbol('x'), P('3/10 + 7*I/10')], [symbol('y'), P('-11/10 + 2*I/5')]]).toComplex();
    return [v.re, v.im];
  };
  it.each([
    ['(x+I*y)**2', '(re(x) - im(y))**2 + 2*I*(re(x) - im(y))*(re(y) + im(x)) - (re(y) + im(x))**2'],
    ['x*(y + I)', 'I*((im(y) + 1)*re(x) + re(y)*im(x)) - (im(y) + 1)*im(x) + re(x)*re(y)'],
  ])('%s', (src, sympyForm) => {
    const got = expandComplex(P(src));
    const [r1, i1] = at(got);
    const [r2, i2] = at(P(sympyForm));
    expect(r1).toBeCloseTo(r2, 12);
    expect(i1).toBeCloseTo(i2, 12);
    expect(String(got)).not.toContain('**2*(');
  });
});

describe('expandMul (cov2): the round limit', () => {
  it('returns the result of the passes made when the limit is reached', () => {
    // one pass of (x + 1)**2*(y + 1) distributes completely; the second pass would only confirm it
    expect(String(expandMulRounds(P('(x + 1)**2*(y + 1)'), 1))).toBe('x**2*y + x**2 + 2*x*y + 2*x + y + 1');
  });
});
