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
