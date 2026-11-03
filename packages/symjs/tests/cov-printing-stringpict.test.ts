// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Coverage of the picture classes and the symbology helpers: expected
 * values are those of SymPy 1.14 `stringPict`, `prettyForm` and
 * `pretty_symbology` (ASCII unless stated).
 */

import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { Binding, PrettyForm, StringPict, centerPad, prettySymbol, prettyUseUnicode, splitSuperSub, xobj, xsym } from '../src/printing/pretty';
import { isCombining } from '../src/printing/pretty/symbology';

let prev = false;
beforeEach(() => {
  prev = prettyUseUnicode(false);
});
afterEach(() => {
  prettyUseUnicode(prev);
});

describe('stringPict and prettyForm', () => {
  it('leftslash', () => {
    expect(new StringPict('a\nb\nc', 1).leftslash()).toEqual(['  /a\n / b\n/  c', 1]);
  });
  it('render with a non-positive column count uses 80 columns', () => {
    const want = `${'x'.repeat(78)} >\n\n> ${'x'.repeat(22)}`;
    expect(new StringPict('x'.repeat(100)).render({ numColumns: 0 })).toBe(want);
    expect(new StringPict('x'.repeat(100)).render({ numColumns: -5 })).toBe(want);
  });
  it('equals is false for other values', () => {
    expect(new StringPict('x').equals(3)).toBe(false);
    expect(new StringPict('x').equals(new StringPict('x'))).toBe(true);
    expect(new StringPict('x').equals('x')).toBe(true);
  });
  it('a fraction over a fraction parenthesizes the denominator', () => {
    const den = new PrettyForm('b').div(new PrettyForm('c'));
    expect(new PrettyForm('a').div(den).toString()).toBe(' a \n---\n/b\\\n|-|\n\\c/');
  });
  it('a product with the degree sign has no multiplication sign', () => {
    expect(PrettyForm.mul(new PrettyForm('x'), new PrettyForm('°')).toString()).toBe('x°');
  });
  it('-1 times a negative factor', () => {
    expect(PrettyForm.mul(new PrettyForm('-1'), new PrettyForm('-x', 0, Binding.NEG)).toString()).toBe('- -x');
  });
  it('powers of function and sum bindings', () => {
    expect(new PrettyForm('x', 0, Binding.FUNC).pow(new PrettyForm('a\nb', 1)).toString()).toBe('   a\n   b\n(x) ');
    expect(new PrettyForm('x', 0, Binding.ADD).pow(new PrettyForm('2')).toString()).toBe('   2\n(x) ');
  });
});

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
