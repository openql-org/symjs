// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/bbppi.ts.
// Hexadecimal digits of pi. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { piHexDigits } from '../../src/ntheory/bbppi';

describe('pi_hex_digits', () => {
  it('gives the digits from any position', () => {
    expect(piHexDigits(0)).toBe('3243f6a8885a30');
    expect(piHexDigits(0, 3)).toBe('324');
    expect(piHexDigits(1, 10)).toBe('243f6a8885');
    expect(piHexDigits(100, 20)).toBe('c29b7c97c50dd3f84d5b');
    expect(piHexDigits(1000n)).toBe('349f1c09b07537');
    expect(piHexDigits(12345, 5)).toBe('4bc61');
    expect(piHexDigits(1, 1)).toBe('2');
    expect(piHexDigits(13, 1)).toBe('0');
    expect(piHexDigits(5, 0)).toBe('');
  });
  it('rejects negative or non-integer arguments', () => {
    expect(() => piHexDigits(-1)).toThrow(RangeError);
    expect(() => piHexDigits(0, -1)).toThrow(RangeError);
    expect(() => piHexDigits(0.5)).toThrow(TypeError);
  });
});
