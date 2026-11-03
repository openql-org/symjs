// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/pretty/stringpict.ts.

import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { Binding, LINE, PrettyForm, prettyUseUnicode, StringPict } from '../../../src/printing/pretty';

let prev = false;

beforeEach(() => {
  prev = prettyUseUnicode(false);
});
afterEach(() => {
  prettyUseUnicode(prev);
});

describe('stringPict / prettyForm (SymPy stringpict.py doctests)', () => {
  it('right', () => {
    expect(new StringPict('10').right(' + ', new StringPict('1\r-\r2', 1))[0]).toBe('     1\n10 + -\n     2');
  });
  it('below', () => {
    expect(new StringPict('x+3').below(LINE, '3')[0]).toBe('x+3\n---\n 3 ');
  });
  it('arithmetic of prettyForms', () => {
    const prev = prettyUseUnicode(false);
    try {
      const x = new PrettyForm('x');
      const two = new PrettyForm('2');
      expect(PrettyForm.mul(x, two).toString()).toBe('x*2');
      expect(PrettyForm.add(x, two).toString()).toBe('x + 2');
      expect(x.div(two).toString()).toBe('x\n-\n2');
      expect(x.pow(two).toString()).toBe(' 2\nx ');
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

/**
 * Coverage of printing/sets.ts, sortkey.ts, str.ts and the pretty printer
 * (pretty.ts, stringpict.ts, symbology.ts). Expected strings from SymPy 1.14
 * (str, pretty with and without unicode, latex, default_sort_key).
 */

describe('stringPict', () => {
  it('renders with the default of 80 columns', () => {
    expect(new StringPict('abc').render()).toBe('abc');
  });
  it('parenthesizes a fraction over a fraction', () => {
    // SymPy (ASCII): (prettyForm('1')/prettyForm('2'))/prettyForm('x')
    const half = new PrettyForm('1').div(new PrettyForm('2'));
    expect(half.div(new PrettyForm('x')).render({ wrapLine: false })).toBe('/1\\\n|-|\n\\2/\n---\n x ');
  });
});
