// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpeval.ts.

import { describe, expect, it } from 'vitest';
import { add, evalf, fn, I, sstr } from '../../src';

/**
 * Coverage of numeric/nfloat.ts (nsimplify), mpeval.ts and round.ts.
 * Expected values from SymPy 1.14 / mpmath 1.3.
 */

describe('evalMp', () => {
  it('evaluates a two-argument log', () => {
    // SymPy: log(8, 3, evaluate=False).evalf(20) = 1.8927892607143723113
    expect(sstr(evalf(fn('log', [8, 3], { evaluate: false }), 20))).toBe('1.8927892607143723113');
    // SymPy: N(log(I, 2 + I, evaluate=False), 20)
    expect(sstr(evalf(fn('log', [I, add(2, I)], { evaluate: false }), 20))).toBe('0.8443602876407569357 + 1.4654938711011811226*I');
  });
});
