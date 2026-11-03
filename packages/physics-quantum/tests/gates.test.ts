// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/gates.ts.
// Quantum gates, their matrices and their representation on qubits. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { I, Matrix, Rational, add, mul, pi, symbols, sqrt, sstr } from '@symjs/symjs';
import { gates } from '../src';

const [theta, phi] = symbols('theta phi', { real: true });

describe('quantum gates', () => {
  it('Pauli algebra', () => {
    const { X, Y, Z } = gates;
    expect(X().mul(Y()).equals(Z().scale(I))).toBe(true);
    expect(X().commutator(Y()).equals(Z().scale(mul(2, I)))).toBe(true);
    expect(X().mul(X()).equals(Matrix.eye(2))).toBe(true);
  });

  it('H is unitary and Hermitian; HZH = X', () => {
    const { H, X, Z } = gates;
    expect(H().isUnitary()).toBe(true);
    expect(H().isHermitian()).toBe(true);
    expect(H().mul(Z()).mul(H()).equals(X())).toBe(true);
  });

  it('rotations compose', () => {
    const { Rx, Ry, Rz } = gates;
    expect(Rz(theta).mul(Rz(phi)).equalsSimplified(Rz(add(theta, phi)))).toBe(true);
    expect(Ry(theta).mul(Ry(phi)).simplify().equals(Ry(add(theta, phi)))).toBe(true);
    expect(Rx(theta).mul(Rx(phi)).simplify().equals(Rx(add(theta, phi)))).toBe(true);
    expect(Rx(theta).isUnitary()).toBe(true);
    expect(gates.U(theta, phi, Rational.of(1, 3)).isUnitary()).toBe(true);
  });

  it('T^2 = S, S^2 = Z', () => {
    const { T, S_, Z } = gates;
    expect(T().pow(2).equals(S_())).toBe(true);
    expect(S_().pow(2).equals(Z())).toBe(true);
    expect(gates.SX().pow(2).equals(gates.X())).toBe(true);
    expect(gates.Rz(pi).equals(Matrix.diag(mul(-1, I), I))).toBe(true);
  });

  it('Bell state', () => {
    const { H, CX, ket, onQubit } = gates;
    // |q1 q0> = |00>, H on qubit 1 (control of CX), then CX
    const psi = CX().mul(onQubit(H(), 1, 2)).mul(ket('00'));
    expect(psi.toString()).toBe('Matrix([[sqrt(2)/2], [0], [0], [sqrt(2)/2]])');
    expect(gates.inner(psi, psi).toString()).toBe('1');
  });

  it('onQubits matches kron ordering', () => {
    const { CX, onQubits, SWAP } = gates;
    // CX with control qubit 0, target qubit 1 == SWAP CX SWAP
    const cx01 = onQubits(CX(), [1, 0], 2); // local LSB(target)=qubit 1, local MSB(control)=qubit 0
    expect(cx01.equals(SWAP().mul(CX()).mul(SWAP()))).toBe(true);
    expect(onQubits(CX(), [0, 1], 2).equals(CX())).toBe(true);
  });

  it('expectation value of Z in Ry(theta)|0>', () => {
    const { Ry, Z, ket, expectation } = gates;
    const psi = Ry(theta).mul(ket('0'));
    expect(expectation(Z(), psi).simplify().toString()).toBe('cos(theta)');
  });

  it('lambdify a parametric gate', () => {
    const f = gates.Rz(theta).lambdify([theta]);
    const m = f(Math.PI);
    expect(m[0]![0]!.im).toBeCloseTo(-1);
    expect(m[1]![1]!.im).toBeCloseTo(1);
  });
});

// Expected matrices printed by SymPy 1.14 (str of the equivalent sympy Matrix).

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

// Expected matrices: SymPy 1.14 represent(gate, nqubits=n) (qubit 0 is the least significant).

describe('onQubits on part of the register', () => {
  it('leaves the other qubits alone', () => {
    // represent(XGate(1), nqubits=2)
    expect(s(gates.onQubits(gates.X(), [1], 2))).toBe('Matrix([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]])');
    // represent(CNOT(2, 0), nqubits=3): control 2, target 0
    expect(s(gates.onQubits(gates.CX(), [0, 2], 3))).toBe(
      'Matrix([[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1, 0]])',
    );
  });
});
