// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected matrices printed by SymPy 1.14 (str of the equivalent sympy Matrix).

import { describe, expect, it } from 'vitest';
import { I, Matrix, sqrt, sstr, symbols } from '@symjs/symjs';
import { gates } from '../src';

const [theta] = symbols('theta', { real: true });
const s = (m: Matrix) => m.toString();

describe('gates and states', () => {
  it('constant gates', () => {
    expect(s(gates.I2())).toBe('Matrix([[1, 0], [0, 1]])');
    expect(s(gates.Sdg())).toBe('Matrix([[1, 0], [0, -I]])');
    expect(s(gates.Tdg())).toBe('Matrix([[1, 0], [0, exp(-I*pi/4)]])');
    expect(s(gates.P(theta))).toBe('Matrix([[1, 0], [0, exp(I*theta)]])');
    expect(s(gates.CZ())).toBe('Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]])');
    const ccx = gates.CCX();
    expect([ccx.rows, sstr(ccx.get(6, 7)), sstr(ccx.get(7, 6)), sstr(ccx.get(7, 7)), sstr(ccx.get(5, 5))]).toEqual([8, '1', '1', '0', '1']);
  });
  it('rejects bad arguments', () => {
    expect(() => gates.onQubit(gates.CZ(), 0, 2)).toThrow(RangeError);
    expect(() => gates.onQubit(gates.X(), 2, 2)).toThrow(RangeError);
    expect(() => gates.onQubit(gates.X(), -1, 2)).toThrow(RangeError);
    expect(() => gates.onQubits(gates.X(), [0, 1], 2)).toThrow(RangeError);
    expect(() => gates.onQubits(gates.CZ(), [0, 0], 2)).toThrow(RangeError);
    expect(() => gates.onQubits(gates.CZ(), [0, 2], 2)).toThrow(RangeError);
    expect(() => gates.ket('012')).toThrow(SyntaxError);
  });
  it('bras, states, outer products and density matrices', () => {
    expect(s(gates.bra('01'))).toBe('Matrix([[0, 1, 0, 0]])');
    expect(s(gates.state(1, I))).toBe('Matrix([[1], [I]])');
    expect(s(gates.outer(gates.ket('0'), gates.ket('1')))).toBe('Matrix([[0, 1], [0, 0]])');
    const psi = gates.state(1, I).scale(sqrt(2).pow(-1));
    expect(s(gates.densityMatrix(psi))).toBe('Matrix([[1/2, -I/2], [I/2, 1/2]])');
  });
});
