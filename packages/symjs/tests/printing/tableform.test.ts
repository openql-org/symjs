// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/tableform.ts. Expected values from SymPy 1.14 TableForm.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { TableForm } from '../../src';
import { Rational, Sym } from '../../src/core/nodes';

const x = sj.symbol('x');

describe('TableForm (SymPy doctests)', () => {
  it('str, as_latex and as_matrix', () => {
    const t = new TableForm([[5, 7], [4, 2], [10, 3]]);
    expect(String(t)).toBe('5  7\n4  2\n10 3');
    expect(t.asStr()).toBe('5  7\n4  2\n10 3');
    expect(t.asLatex()).toBe('\\begin{tabular}{l l}\n$5$ & $7$ \\\\\n$4$ & $2$ \\\\\n$10$ & $3$ \\\\\n\\end{tabular}');
    expect(t.asMatrix().toString()).toBe('Matrix([[5, 7], [4, 2], [10, 3]])');
    expect(String(new TableForm([[5, 7], [4, 2], [10, 3]], { headings: 'automatic' }))).toBe('  | 1  2\n--------\n1 | 5  7\n2 | 4  2\n3 | 10 3');
  });
  it('automatic headings, short rows and text entries', () => {
    const rows = [1, 2, 3].map((i) => Array.from({ length: i }, () => '.'));
    expect(String(new TableForm(rows, { headings: 'automatic' }))).toBe('  | 1 2 3\n---------\n1 | .    \n2 | . .  \n3 | . . .');
  });
  it('alignments, one per column', () => {
    // SymPy's doctest has Symbol('') where j = 0; a symbol has a name here, and a blank prints the same
    const rows = [0, 1, 2, 3].map((j) => [0, 1, 2].map((i) => new Sym('.'.repeat(i % 2 ? 1 : j) || ' ')));
    expect(String(new TableForm(rows, { alignments: 'rcl' }))).toBe('    .    \n  . . .  \n .. . .. \n... . ...');
  });
});

describe('TableForm options (SymPy 1.14)', () => {
  it('headings and their alignment', () => {
    expect(String(new TableForm([[1, 2]], { headings: [null, ['long', 'b']], alignments: '>' }))).toBe('long b\n------\n   1 2');
    expect(String(new TableForm([[1, 2]], { headings: [['r'], 'automatic'], alignments: '^' }))).toBe('  | 1 2\n-------\nr | 1 2');
    expect(String(new TableForm([[1, 2]], { headings: ['automatic', null], alignments: 'center' }))).toBe('1 | 1 2');
    expect(String(new TableForm([[1, 0], [30, 4]], { headings: [['a', 'bbb'], null], alignments: 'clr' }))).toBe(' a  | 1   \nbbb | 30 4');
    expect(String(new TableForm([[1, 0], [30, 4]], { headings: [['a', 'bbb'], null], alignments: 'cl' }))).toBe('  a | 1   \nbbb | 30 4');
    expect(String(new TableForm([[1, 2], [3, 4]], { headings: [['a', 'bbbb'], null], alignments: 'ccc' }))).toBe(' a   | 1 2\nbbbb | 3 4');
    expect(String(new TableForm([[1, 0], [30, 4]], { headings: 'automatic', alignments: 'c' }))).toBe('  |  1 2\n--------\n1 | 1   \n2 | 30 4');
    expect(String(new TableForm([[1, 2]], { headings: [[x], [sj.pow(x, 2), 3n]] }))).toBe('  | x**2 3\n----------\nx | 1    2');
    expect(String(new TableForm([[1, 2]], { headings: [[], null] }))).toBe('1 2');
  });
  it('zeros, None, the pad and text that is not an expression', () => {
    expect(String(new TableForm([[1, 0]], { wipeZeros: false }))).toBe('1 0');
    expect(new TableForm([[1, 0]], { wipeZeros: false }).asLatex()).toBe('\\begin{tabular}{l l}\n$1$ & $0$ \\\\\n\\end{tabular}');
    expect(String(new TableForm([[1, null], [3]]))).toBe('1 None\n3     ');
    expect(String(new TableForm([[1, null], [3]], { pad: '-' }))).toBe('1 -\n3 -');
    expect(new TableForm([[1, null]]).asLatex()).toBe('\\begin{tabular}{l l}\n$1$ & $\\text{None}$ \\\\\n\\end{tabular}');
    expect(String(new TableForm([['a b', '.'], [sj.pow(x, 2), 4]]))).toBe('a b  .\nx**2 4');
    expect(String(new TableForm(sj.Matrix.of([[1, 2]])))).toBe('1 2');
  });
  it('as_latex with headings and column formats', () => {
    expect(new TableForm([[1, 0], [30, 4]], { headings: [['a', 'bbb'], ['p', 'q']] }).asLatex()).toBe('\\begin{tabular}{r l l}\n & p & q \\\\\n\\hline\na & $1$ &   \\\\\nbbb & $30$ & $4$ \\\\\n\\end{tabular}');
    expect(new TableForm([[1, 2]], { headings: 'automatic' }).asLatex()).toBe('\\begin{tabular}{r l l}\n & 1 & 2 \\\\\n\\hline\n1 & $1$ & $2$ \\\\\n\\end{tabular}');
    const t = new TableForm([[1, x], [Rational.of(1n, 2n), 4]], { wipeZeros: false, formats: [(_v, i) => (i === 0 ? 'V' : undefined), null] });
    expect(t.asLatex()).toBe('\\begin{tabular}{l l}\nV & $x$ \\\\\n\\frac{1}{2} & $4$ \\\\\n\\end{tabular}');
  });
  it('as_latex with column headings only', () => {
    expect(new TableForm([[1, 2]], { headings: [null, ['p', 'q']] }).asLatex()).toBe('\\begin{tabular}{l l}\np & q \\\\\n\\hline\n$1$ & $2$ \\\\\n\\end{tabular}');
  });
  it('invalid alignments and a None entry in a matrix', () => {
    expect(() => new TableForm([[1, 2]], { alignments: 'xy' })).toThrow('alignment "xy" unrecognized');
    expect(() => new TableForm([[1, 2]], { alignments: 'lrc' })).toThrow('wrong number of alignments: expected 2 but got 3');
    expect(() => new TableForm([[1, null]]).asMatrix()).toThrow(TypeError);
  });
});
