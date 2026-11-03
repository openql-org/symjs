// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/polar.ts. Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { S, Sym, add, expPolar, expint, extractBranchFactor, mul, periodicArgument, polarLift, polarify, principalBranch, sin, sqrt } from '../src';

const x = new Sym('x');
const y = new Sym('y');
const I = S.I;
const pi = S.Pi;
const str = (v: unknown): string => (Array.isArray(v) ? `(${v.map(str).join(', ')})` : String(v));

describe('polar numbers', () => {
  it('extract_branch_factor', () => {
    // SymPy exp_polar(...).extract_branch_factor()
    expect(str(extractBranchFactor(expPolar(mul(I, pi, x))))).toBe('(exp_polar(I*pi*x), 0)');
    expect(str(extractBranchFactor(expPolar(mul(I, pi, add(1, I)))))).toBe('(exp_polar(I*pi*(1 - I)), I)');
    expect(str(extractBranchFactor(expPolar(mul(I, pi, add(sqrt(2), I)))))).toBe('(exp_polar(I*pi*(-2 + sqrt(2) - I)), 1 + I)');
    expect(str(extractBranchFactor(expPolar(mul(I, pi, sqrt(7)))))).toBe('(exp_polar(I*pi*(-2 + sqrt(7))), 1)');
  });
  it('periodic_argument and principal_branch that stay unevaluated', () => {
    const p = new Sym('p', { polar: true });
    expect(String(periodicArgument(p, mul(2, pi)))).toBe('periodic_argument(p, 2*pi)');
    expect(String(principalBranch(add(1, mul(2, I)), mul(2, pi)))).toBe('principal_branch(1 + 2*I, 2*pi)');
  });
  it('numeric value of polar_lift', () => {
    // SymPy N(polar_lift(1 + I))
    expect(String(polarLift(add(1, I)).evalf())).toBe('1.0 + 1.0*I');
  });
  it('polarify', () => {
    // SymPy polarify(polar_lift(x), subs=False) and polarify(x*y + 1)
    expect(String(polarify(polarLift(x), { subs: false }))).toBe('polar_lift(x)');
    expect(str(polarify(add(mul(x, y), 1)))).toBe('(_x*_y + 1, ((_x, x), (_y, y)))');
    // SymPy polarify(b + sin(a)) = (_b + sin(_a), {_b: b, _a: a}); symjs lists the pairs by name
    const a = new Sym('a');
    const b = new Sym('b');
    expect(str(polarify(add(b, sin(a))))).toBe('(_b + sin(_a), ((_a, a), (_b, b)))');
  });
  it('expint of a non-positive order on another branch', () => {
    // SymPy expint(-1, x*exp_polar(2*I*pi)), expint(0, x*exp_polar(2*I*pi))
    const z = mul(x, expPolar(mul(2, I, pi)));
    expect(String(expint(-1, z))).toBe('exp(-x)/x + exp(-x)/x**2');
    expect(String(expint(0, z))).toBe('exp(-x)/x');
  });
});
