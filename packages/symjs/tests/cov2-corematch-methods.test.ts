// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Structural Expr methods (core/methods.ts). Expected values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import {
  Expr,
  Float,
  SymFunction,
  abs,
  add,
  asCoefficientsDict,
  asContentPrimitive,
  asNumerDenom,
  coeff,
  extractAdditively,
  extractMultiplicatively,
  isConstant,
  isMeromorphic,
  log,
  mul,
  pi,
  pow,
  rational,
  sqrt,
  str,
  symbols,
} from '../src';

const [x, y, z] = symbols('x y z');
const [A, B, C] = symbols('A B C', { commutative: false });
const f = SymFunction('f');
const s = (e: unknown): string => (e instanceof Expr ? str(e) : 'None');
const pairStr = (p: readonly unknown[]): string => `(${p.map(s).join(', ')})`;

describe('coeff', () => {
  it('takes the independent part of a sum with right', () => {
    const e = add(mul(z, add(x, 1)), 3);
    expect(s(coeff(e, add(x, 1), 0, true))).toBe('3');
    expect(s(coeff(e, add(x, 1), 0))).toBe('3');
  });
  it('finds no coefficient of a noncommutative factor that is absent', () => {
    expect(s(coeff(mul(A, B), mul(2, C)))).toBe('0');
    expect(s(coeff(add(mul(A, B), 2), C))).toBe('0');
    expect(s(coeff(add(mul(A, B), x), C))).toBe('0');
    // (A*B + 2).coeff(C, 1, False, False): the term 2 has no noncommutative part
    expect(s(coeff(add(mul(A, B), 2), C, 1, false, false))).toBe('0');
  });
});

describe('asContentPrimitive of powers', () => {
  it('takes the content out of a power of a sum', () => {
    expect(pairStr(asContentPrimitive(sqrt(add(mul(4, x), mul(4, y)))))).toBe('(2, sqrt(x + y))');
    // 4**(3/4) = 2*sqrt(2) is not a power with the exponent 3/4: the power stays as it is
    expect(pairStr(asContentPrimitive(pow(add(mul(4, x), mul(4, y)), rational(3, 4))))).toBe('(1, 2*sqrt(2)*(x + y)**(3/4))');
    expect(pairStr(asContentPrimitive(pow(add(mul(2, x), mul(2, y)), rational(3, 2))))).toBe('(1, 2*sqrt(2)*(x + y)**(3/2))');
    expect(pairStr(asContentPrimitive(pow(add(mul(2, x), mul(2, y)), rational(1, 3))))).toBe('(1, 2**(1/3)*(x + y)**(1/3))');
  });
  it('takes the integer part of a rational exponent of a number', () => {
    expect(pairStr(asContentPrimitive(pow(2, add(x, rational(3, 2)))))).toBe('(2, 2**((2*x + 1)/2))');
    expect(pairStr(asContentPrimitive(pow(4, add(x, rational(1, 2)))))).toBe('(2, 4**x)');
    expect(pairStr(asContentPrimitive(pow(2, add(x, rational(-3, 2)))))).toBe('(1/4, 2**((2*x + 1)/2))');
  });
});

describe('extractMultiplicatively', () => {
  it('extracts from symbols, constants and powers', () => {
    expect(s(extractMultiplicatively(x, rational(1, 2)))).toBe('2*x');
    expect(s(extractMultiplicatively(pi, mul(pi, rational(1, 2))))).toBe('2');
    expect(s(extractMultiplicatively(pi, 3))).toBe('None');
    expect(s(extractMultiplicatively(pow(pow(x, y), add(z, 1)), pow(x, y)))).toBe('(x**y)**z');
  });
});

describe('extractAdditively', () => {
  it('extracts from numbers', () => {
    expect(s(extractAdditively(3, 1))).toBe('2');
    expect(s(extractAdditively(3, -1))).toBe('None');
    expect(s(extractAdditively(-3, -1))).toBe('-2');
    expect(s(extractAdditively(-3, 1))).toBe('None');
    expect(s(extractAdditively(3, 4))).toBe('None');
    expect(s(extractAdditively(new Float(2.5), 1))).toBe('1.50000000000000');
  });
  it('takes c off once when the rest contains it', () => {
    // e - (x + 1) = z + (x + 1)*(y + 2); SymPy 1.14 answers z + (x + 1)*(y + 1), which is e - 2*(x + 1)
    const e = add(mul(add(y, 2), add(x, 1)), x, 1, z);
    expect(s(extractAdditively(e, add(x, 1)))).toBe('x + z + (x + 1)*(y + 1) + 1');
    // SymPy: x + y + (x + y)*(z + 1)
    expect(s(extractAdditively(add(mul(add(z, 2), add(x, y)), x, y), add(x, y)))).toBe('x + y + (x + y)*(z + 1)');
  });
});

describe('other methods', () => {
  it('isConstant is false when the derivative is not known', () => {
    expect(isConstant(abs(x))).toBe(false);
  });
  it('asNumerDenom of a sum', () => {
    expect(pairStr(asNumerDenom(add(mul(x, rational(1, 2)), mul(y, rational(1, 3)))))).toBe('(3*x + 2*y, 6)');
  });
  it('asCoefficientsDict of a sum', () => {
    const d = asCoefficientsDict(add(mul(2, x), mul(3, y), 4));
    expect([...d].map(([k, v]) => `${s(k)}: ${s(v)}`).sort()).toEqual(['1: 4', 'x: 2', 'y: 3']);
  });
  it('isMeromorphic is unknown for undefined functions and unknown zeros', () => {
    // SymPy None
    expect(isMeromorphic(f(x), x, 0)).toBe('unknown');
    // log(4) - 2*log(2) is zero, but its is_zero is None in SymPy
    expect(isMeromorphic(log(x), x, add(log(4), mul(-2, log(2))))).toBe('unknown');
  });
});
