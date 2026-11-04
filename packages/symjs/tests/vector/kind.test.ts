// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/kind.ts (SymPy sympy/vector/kind.py). Expected values
// are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { BooleanKind, NumberKind, add, kindOf, mul } from '../../src';
import { CoordSys3D, VectorKind } from '../../src/vector';

describe('VectorKind', () => {
  it('is the kind of vectors', () => {
    const Sys = CoordSys3D('Sys');
    expect(String(kindOf(Sys.i))).toBe('VectorKind(NumberKind)');
    expect(kindOf(add(mul(Sys.i, 2), mul(Sys.j, 3)))).toBe(VectorKind());
    expect(VectorKind(NumberKind)).toBe(VectorKind());
    expect(VectorKind(BooleanKind)).not.toBe(VectorKind());
    expect(VectorKind(BooleanKind).elementKind).toBe(BooleanKind);
    expect(String(VectorKind(BooleanKind))).toBe('VectorKind(BooleanKind)');
  });
});
