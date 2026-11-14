// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.domains.complexfield).

import { describe, expect, it } from 'vitest';
import { parseExpr as P } from '../../../src/index';
import { DomainError } from '../../../src/core/errors';
import { CoercionFailed, QQ } from '../../../src/polys/domains';
import { CC, ComplexField } from '../../../src/polys/domains/complexfield';
import { QQ_I } from '../../../src/polys/domains/gaussiandomains';

describe('CC', () => {
  it('names and elements', () => {
    expect([String(CC), String(new ComplexField(100)), CC.dps, CC.isField, CC.equals(new ComplexField()), CC.equals(QQ)]).toEqual(['CC', 'CC_100', 15, true, true, false]);
    // SymPy CC.to_sympy(CC.from_sympy(1 + 2*I)): 1.0 + 2.0*I
    expect([CC.fromSympy(P('1 + 2*I')), CC.canon(P('3')), CC.canon(P('I'))].map(String)).toEqual(['1.0 + 2.0*I', '3.00000000000000', '1.0*I']);
    expect(() => CC.canon(P('x'))).toThrow(CoercionFailed);
    expect(() => CC.canon(P('x*I'))).toThrow(CoercionFailed);
  });
  it('domain methods', () => {
    expect([CC.getField() === CC, CC.getExact() === QQ_I, CC.isNegative(1), CC.isPositive(1), CC.isNonnegative(1), CC.isNonpositive(1)]).toEqual([true, true, false, false, false, false]);
    expect(() => CC.getRing()).toThrow(DomainError);
    // SymPy returns mpc values (1.0 + 0.0j, 6.0 + 0.0j); symjs elements are float expressions
    expect([CC.gcd(2, 3), CC.lcm(2, 3)].map(String)).toEqual(['1.00000000000000', '6.00000000000000']);
  });
});

it('ComplexField elements keep their domain and precision', () => {
  const field = new ComplexField(100);
  const element = field.dtype('1.000000000000000001', 2);
  expect(element.parent()).toBe(field);
  expect(element.real.context.prec).toBe(100);
  expect(field.dtype().isZero).toBe(true);
  expect(field.dtype(1).imag.isZero).toBe(true);
  expect(field.toSympy(element)).toEqual(element.toSympy());
});

describe('CC exactness, square roots and unification (SymPy test_domains)', () => {
  it('is inexact with principal square roots', () => {
    expect(CC.isExact).toBe(false);
    expect(CC.hasCharacteristicZero).toBe(true);
    expect(CC.isSquare(-1)).toBe(true);
    expect(String(CC.exsqrt(P('-3 - 4*I')))).toBe('1.0 - 2.0*I');
    expect(String(CC.unify(QQ))).toBe('CC');
    expect(String(QQ_I.unify(CC))).toBe('CC');
  });
});
