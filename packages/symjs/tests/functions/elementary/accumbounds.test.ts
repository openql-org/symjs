// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/elementary/accumbounds.ts.
//
// AccumBounds (SymPy AccumulationBounds). Expected values are SymPy 1.14 output
// (sympy.calculus.tests.test_accumulationbounds); deviations are explained where they occur.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { Expr } from '../../../src/core/nodes';
import { mul } from '../../../src/core/ops';

const A = sj.AccumBounds;
const x = new sj.Sym('x');
const s = (e: unknown) => sj.str(e as sj.Expr);
const R = (p: number, q: number) => sj.Rational.of(BigInt(p), BigInt(q));
const { oo } = sj;
const toStr = (e: Expr): string => e.toString();
const negOo = mul(-1, oo);

describe('AccumBounds', () => {
  it('functions and substitution', () => {
    expect(s(sj.sin(A(0, sj.pi)))).toBe('AccumBounds(0, 1)');
    expect(s(sj.cos(A(0, sj.pi)))).toBe('AccumBounds(-1, 1)');
    expect(s(sj.sin(A(sj.mul(sj.pi, R(1, 6)), sj.mul(sj.pi, R(1, 3)))))).toBe('AccumBounds(1/2, sqrt(3)/2)');
    expect(s(sj.sin(A(0, sj.mul(4, sj.pi))))).toBe('AccumBounds(-1, 1)');
    expect(s(sj.exp(A(0, 1)))).toBe('AccumBounds(1, E)');
    expect(s(sj.log(A(1, sj.E)))).toBe('AccumBounds(0, 1)');
    expect(s(sj.tan(A(0, 1)))).toBe('AccumBounds(0, tan(1))');
    expect(s(sj.subs(sj.parse('x**2 + 2*x + 1'), [[x, A(-1, 1)]]))).toBe('AccumBounds(-1, 4)');
    expect(s(sj.subs(sj.parse('(x + 1)**2'), [[x, A(-1, 1)]]))).toBe('AccumBounds(0, 4)');
    expect(sj.latex(A(-1, 1))).toBe('\\left\\langle -1, 1\\right\\rangle');
  });
});

describe('functions of an AccumBounds argument', () => {
  it('maps monotone and periodic functions', () => {
    // SymPy: tan(AccumBounds(0, 1)) = AccumBounds(0, tan(1)), tan(AccumBounds(1, 2)) = AccumBounds(-oo, oo)
    expect(toStr(sj.tan(A(0, 1)))).toBe('AccumBounds(0, tan(1))');
    expect(toStr(sj.tan(A(1, 2)))).toBe('AccumBounds(-oo, oo)');
    // SymPy: sin(AccumBounds(0, 3)) = AccumBounds(0, 1), cos(AccumBounds(1, 2)) = AccumBounds(cos(2), cos(1))
    expect(toStr(sj.sin(A(0, 3)))).toBe('AccumBounds(0, 1)');
    expect(toStr(sj.cos(A(1, 2)))).toBe('AccumBounds(cos(2), cos(1))');
    expect(toStr(sj.sin(A(negOo, 1)))).toBe('AccumBounds(-1, 1)');
  });
  it('evaluates sec, csc and cot through cos, sin and tan', () => {
    // SymPy: sec(AccumBounds(1, 2)) = AccumBounds(-oo, oo), csc(...) = AccumBounds(1, 1/sin(1)),
    // cot(...) = AccumBounds(cot(2), cot(1))
    expect(toStr(sj.sec(A(1, 2)))).toBe('AccumBounds(-oo, oo)');
    expect(toStr(sj.csc(A(1, 2)))).toBe('AccumBounds(1, 1/sin(1))');
    expect(toStr(sj.cot(A(1, 2)))).toBe('AccumBounds(cot(2), cot(1))');
  });
  it('leaves the other monotone functions unevaluated, as SymPy', () => {
    expect(toStr(sj.acos(A(0, 1)))).toBe('acos(AccumBounds(0, 1))');
    expect(toStr(sj.acot(A(1, 2)))).toBe('acot(AccumBounds(1, 2))');
    expect(toStr(sj.atan(A(0, 1)))).toBe('atan(AccumBounds(0, 1))');
    expect(toStr(sj.sinh(A(0, 1)))).toBe('sinh(AccumBounds(0, 1))');
    expect(toStr(sj.erf(A(0, 1)))).toBe('erf(AccumBounds(0, 1))');
  });
  it('leaves other functions unevaluated', () => {
    // SymPy: cosh(AccumBounds(1, 2)) stays
    expect(toStr(sj.cosh(A(1, 2)))).toBe('cosh(AccumBounds(1, 2))');
  });
});
