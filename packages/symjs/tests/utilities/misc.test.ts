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

// Expected values of the following are SymPy 1.14's rawlines, strlines, translate, replace, as_int and func_name.
describe('rawlines and strlines', () => {
  it('rawlines', () => {
    expect(sj.rawlines('one line')).toBe("'one line'");
    expect(sj.rawlines("it's")).toBe('"it\'s"');
    expect(sj.rawlines('say "hi"')).toBe('\'say "hi"\'');
    expect(sj.rawlines('a\tb\\c\r')).toBe("'a\\tb\\\\c\\r'");
    expect(sj.rawlines('x\x01y\x7f')).toBe("'x\\x01y\\x7f'");
    expect(sj.rawlines('a\nb')).toBe("dedent('''\\\n    a\n    b''')");
    expect(sj.rawlines('a\\b\nc')).toBe("(\n    'a\\\\b\\n'\n    'c'\n)");
    expect(sj.rawlines("tri '''\nq")).toBe('dedent("""\\\n    tri \'\'\'\n    q""")');
    expect(sj.rawlines('tri """\nq')).toBe("dedent('''\\\n    tri \"\"\"\n    q''')");
    expect(sj.rawlines('both \'\'\' and """\nx')).toBe("(\n    'both \\'\\'\\' and \"\"\"\\n'\n    'x'\n)");
    expect(sj.rawlines('a\nb\n')).toBe("dedent('''\\\n    a\n    b\n    ''')");
    expect(sj.rawlines('a \nb')).toBe("(\n    'a \\n'\n    'b'\n)");
    // the doctests of sympy.utilities.misc
    expect(sj.rawlines('this\nthat\n    ')).toBe("(\n    'this\\n'\n    'that\\n'\n    '    '\n)");
  });
  it('strlines', () => {
    expect(sj.strlines('this is a long string that should be broken into shorter lines', 40)).toBe("(\n'this is a long string that should be b'\n'roken into shorter lines'\n)");
    expect(sj.strlines('abc')).toBe("(\n'abc'\n)");
    expect(sj.strlines('a\\bcdefg', 5)).toBe("(\nr'a\\'\nr'bc'\nr'de'\nr'fg'\n)");
    expect(sj.strlines('abc', 64, true)).toBe("'abc'");
    expect(sj.strlines('a\\b', 64, true)).toBe("r'a\\b'");
    expect(sj.strlines("it's long", 4)).toBe('(\n"it"\n"\'s"\n" l"\n"on"\n"g"\n)');
    expect(sj.strlines('a\nb')).toBe("dedent('''\\\n    a\n    b''')");
    // SymPy loops forever when no character fits on a line
    expect(() => sj.strlines('abc', 2)).toThrow(RangeError);
  });
});

describe('translate and replaceString', () => {
  it('translate', () => {
    expect(sj.translate('abc', null, 'a')).toBe('bc');
    expect(sj.translate('abc', new Map([['a', 'x']]), 'c')).toBe('xb');
    expect(sj.translate('abc', new Map([['abc', 'x'], ['a', 'y']]))).toBe('x');
    expect(sj.translate('abcd', 'ac', 'AC', 'd')).toBe('AbC');
    expect(sj.translate('abc')).toBe('abc');
    expect(sj.translate('alphahatdotprime', null)).toBe('alphahatdotprime');
    expect(sj.translate('abc', new Map(), 'b')).toBe('ac');
    expect(sj.translate('abc', 'ab', 'xy')).toBe('xyc');
    expect(sj.translate('abc', '')).toBe('abc');
    expect(sj.translate('aabcabc', new Map([['ab', 'Q'], ['c', 'Z'], ['b', 'yy']]))).toBe('aQZQZ');
    expect(() => sj.translate('abc', null, 'a', 'b')).toThrow(TypeError);
    expect(() => sj.translate('abc', 'ab', 'x')).toThrow(RangeError);
  });
  it('replaceString (SymPy replace of sympy.utilities.misc)', () => {
    expect(sj.replaceString('foo', new Map([['oo', 'ar'], ['f', 'b']]))).toBe('bar');
    expect(sj.replaceString('spamham sha', ['spam', 'eggs'], ['sha', 'md5'])).toBe('eggsham md5');
    expect(sj.replaceString('abab', ['a', 'x'])).toBe('xbxb');
    expect(sj.replaceString('abc', new Map())).toBe('abc');
    expect(sj.replaceString('a.b*c', new Map([['.', '!'], ['*', '+']]))).toBe('a!b+c');
  });
});

describe('asInt and funcName', () => {
  it('asInt', () => {
    expect([sj.asInt(5), sj.asInt(5n), sj.asInt(sj.Rational.of(-7)), sj.asInt(new sj.Float(2), false), sj.asInt(true, false), sj.asInt(new sj.Float(1024), false)]).toEqual([5n, 5n, -7n, 2n, 1n, 1024n]);
    expect(sj.asInt(new sj.Float(1e23), false)).toBe(99999999999999991611392n);
    expect(sj.asInt(false, false)).toBe(0n);
    for (const bad of [() => sj.asInt(2.5), () => sj.asInt(new sj.Float(2)), () => sj.asInt(new sj.Float(2.5), false), () => sj.asInt(true), () => sj.asInt(sj.sqrt(2), false)]) expect(bad).toThrow(TypeError);
  });
  it('funcName', () => {
    const x = new sj.Sym('x');
    const f = sj.SymFunction('f');
    const values = [sj.add(x, 1), sj.mul(x, 2), sj.pow(x, 2), sj.sin(x), sj.Rational.of(3), x, sj.Eq(x, 1), sj.Ne(x, 1), sj.Ge(x, 1), sj.Gt(x, 1), sj.Le(x, 1), f(x), 3, 'a', [1], new Map([[1, 2]]), new Set([1]), 2.5, true, null, sj.Abs(x)];
    expect(values.map((e) => sj.funcName(e))).toEqual(['Add', 'Mul', 'Pow', 'sin', 'Integer', 'Symbol', 'Equality', 'Unequality', 'GreaterThan', 'StrictGreaterThan', 'LessThan', 'f', 'int', 'str', 'list', 'dict', 'set', 'float', 'bool', 'NoneType', 'Abs']);
    const rels = [sj.Eq(x, 1), sj.Ne(x, 1), sj.Ge(x, 1), sj.Gt(x, 1), sj.Le(x, 1), sj.Lt(x, 1), sj.add(x, 1)];
    expect(rels.map((e) => sj.funcName(e, true))).toEqual(['Eq', 'Ne', 'Ge', 'Gt', 'Le', 'Lt', 'Add']);
    // JavaScript values: a bigint is an int, a matrix SymPy's Matrix, a named function its name
    function g(): number {
      return 1;
    }
    const anonymous = [(): number => 1][0];
    expect([sj.funcName(1n), sj.funcName(sj.Matrix.eye(3)), sj.funcName(g), sj.funcName(anonymous), sj.funcName(undefined), sj.funcName({})]).toEqual(['int', 'MutableDenseMatrix', 'g', 'function', 'NoneType', 'object']);
  });
});

it('translates a lone LaTeX symbol name using the printing convention', () => {
  expect(sj.translate('alphahatdotprime')).toBe("{\\dot{\\hat{\\alpha}}}'");
});
