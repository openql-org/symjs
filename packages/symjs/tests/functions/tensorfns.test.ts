// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/tensorfns.ts.
// The Levi-Civita symbol. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Eijk, LeviCivita, latex, symbols } from '../../src';

describe('LeviCivita', () => {
  const [i, j, k, x, y, a] = symbols('i j k x y a');
  it('evaluates integer arguments to the sign of the permutation', () => {
    expect(String(LeviCivita(1, 2, 3))).toBe('1');
    expect(String(LeviCivita(1, 3, 2))).toBe('-1');
    expect(String(LeviCivita(1, 2, 2))).toBe('0');
    expect(String(LeviCivita(3, 1, 2))).toBe('1');
    expect(String(LeviCivita(1, 2, 3, 4))).toBe('1');
    expect(String(LeviCivita(2, 1, 3, 4))).toBe('-1');
    // SymPy's product formula also for arguments that are not a permutation
    expect(String(LeviCivita(0, 2))).toBe('2');
    expect(String(LeviCivita(5))).toBe('1');
    expect(String(LeviCivita())).toBe('1');
  });
  it('is 0 for a repeated index and unevaluated otherwise', () => {
    expect(String(LeviCivita(i, j, k))).toBe('LeviCivita(i, j, k)');
    expect(String(LeviCivita(i, j, i))).toBe('0');
    expect(String(LeviCivita(1, x, x))).toBe('0');
    expect(String(LeviCivita(x, 1, 2))).toBe('LeviCivita(x, 1, 2)');
    expect(latex(LeviCivita(x, y, a))).toBe('\\varepsilon_{x y a}');
  });
  it('Eijk is LeviCivita', () => {
    expect(String(Eijk(1, 3, 2))).toBe('-1');
    expect(String(Eijk(i, j, k))).toBe('LeviCivita(i, j, k)');
  });
});
