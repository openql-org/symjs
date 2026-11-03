// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/pretty/symbology.ts.

import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { centerPad, isSubscriptableInUnicode, prettySymbol, prettyUseUnicode, splitSuperSub, xobj, xsym } from '../../../src/printing/pretty';
import { isCombining } from '../../../src/printing/pretty/symbology';

let prev = false;

beforeEach(() => {
  prev = prettyUseUnicode(false);
});
afterEach(() => {
  prettyUseUnicode(prev);
});

describe('stringPict / prettyForm (SymPy stringpict.py doctests)', () => {
  it('is_subscriptable_in_unicode', () => {
    expect(isSubscriptableInUnicode('abc')).toBe(false);
    expect(isSubscriptableInUnicode('123')).toBe(true);
  });
  it('pretty_symbol', () => {
    const prev = prettyUseUnicode(true);
    try {
      expect(prettySymbol('alpha_1')).toBe('α₁');
      expect(prettySymbol('x_1')).toBe('x₁');
    } finally {
      prettyUseUnicode(prev);
    }
  });
});

/**
 * Coverage of the picture classes and the symbology helpers: expected
 * values are those of SymPy 1.14 `stringPict`, `prettyForm` and
 * `pretty_symbology` (ASCII unless stated).
 */

describe('pretty_symbology', () => {
  it('bold symbol names (unicode)', () => {
    prettyUseUnicode(true);
    const cases: [string, string][] = [
      ['x', '𝐱'],
      ['X', '𝐗'],
      ['alpha', 'α'],
      ['varsigma', '𝛓'],
      ['xhat', '𝐱̂'],
      ['x_1', '𝐱₁'],
      ['x__2', '𝐱²'],
      ['x_ab', '𝐱_𝐚𝐛'],
      ['x1', '𝐱₁'],
      ['x_a1', '𝐱ₐ₁'],
    ];
    for (const [name, want] of cases) expect(prettySymbol(name, true)).toBe(want);
    // SymPy raises KeyError: there is no bold digit
    expect(() => prettySymbol('x2y', true)).toThrow(RangeError);
  });
  it('errors of xobj, xsym and center_pad', () => {
    expect(() => xobj('(', 0)).toThrow('Length should be greater than 0');
    expect(() => xobj('@', 1)).toThrow(RangeError);
    expect(() => xsym('@')).toThrow(RangeError);
    expect(() => centerPad(5, 3)).toThrow('not enough space for string');
  });
  it('split_super_sub and is_combining', () => {
    expect(splitSuperSub('')).toEqual(['', [], []]);
    expect(isCombining('́')).toBe(true);
    expect(isCombining('a')).toBe(false);
    expect(isCombining('⃗')).toBe(true);
    // JavaScript only: an empty string has no combining character
    expect(isCombining('')).toBe(false);
  });
});
