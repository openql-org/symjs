// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/hyper.ts. Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Float, KroneckerDelta } from '../src';

describe('KroneckerDelta', () => {
  it('arguments that differ structurally but not in value', () => {
    // SymPy KroneckerDelta(1, 1.0)
    expect(String(KroneckerDelta(1, new Float(1)))).toBe('1');
  });
});
