// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected matrices: SymPy 1.14 represent(gate, nqubits=n) (qubit 0 is the least significant).

import { describe, expect, it } from 'vitest';
import type { Matrix } from '@symjs/symjs';
import { gates } from '../src';

const s = (m: Matrix) => m.toString();

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
