// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/utilities/misc.ts. Expected values are SymPy 1.14's filldedent (Python 3.12 textwrap).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { dedent, fill } from '../../src/utilities/misc';

describe('filldedent, dedent and fill', () => {
  it('filldedent', () => {
    expect(sj.filldedent('\n    hello   world this is a test of filldedent with a long line of text that should wrap around at seventy characters ok\n')).toBe(
      '\nhello   world this is a test of filldedent with a long line of text\nthat should wrap around at seventy characters ok',
    );
    expect(sj.filldedent('  a b c d e f g h', 5)).toBe('\na b c\nd e f\ng h');
    expect(sj.filldedent('abcdefghij klm', 4)).toBe('\nabcd\nefgh\nij\nklm');
    expect(sj.filldedent('well-known self-evident truths', 12)).toBe('\nwell-known\nself-evident\ntruths');
    expect(sj.filldedent('x\n\n  y')).toBe('\nx    y');
    expect(sj.filldedent('')).toBe('\n');
  });
  it('dedent and fill', () => {
    expect(dedent('    a\n      b\n   \n    c')).toBe('a\n  b\n\nc');
    expect(dedent('  a\n\tb')).toBe('  a\n\tb');
    expect(dedent('')).toBe('');
    // Python keeps the space before a word broken at the line end
    expect(fill('aaaa bbbbbbb', 5)).toBe('aaaa \nbbbbb\nbb');
    expect(fill('a bbbbbbb', 5)).toBe('a bbb\nbbbb');
    expect(fill('ab cd', 1)).toBe('a\nb\nc\nd');
    expect(() => fill('abc', 0)).toThrow(RangeError);
    expect(fill('', 5)).toBe('');
    expect([fill('aaaaa ', 5), fill(' ', 5)]).toEqual(['aaaaa', '']);
  });
});
