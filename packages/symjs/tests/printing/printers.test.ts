// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/printers.ts. Expected values are SymPy 1.14's StrPrinter, sstrrepr and multiline_latex.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const x = sj.symbol('x');

describe('StrPrinter, sstrrepr, printLatex and multilineLatex', () => {
  it('StrPrinter and sstrrepr', () => {
    expect(new sj.StrPrinter().doprint(sj.add(x, 1))).toBe('x + 1');
    expect(new sj.StrPrinter({ order: 'lex' }).doprint([x, 'a', null])).toBe('[x, a, None]');
    expect(sj.sstrrepr('a')).toBe("'a'");
    expect(sj.sstrrepr([x, "it's", new Map([[1, 'a']]), new Set(), true, false, 2n, 3])).toBe(`[x, "it's", {1: 'a'}, set(), True, False, 2, 3]`);
    expect(sj.sstrrepr(new Set([1, 2]))).toBe('{1, 2}');
    expect(sj.sstrrepr('a\\b\n')).toBe("'a\\\\b\\n'");
    expect(sj.sstrrepr(`x'y"z`)).toBe(`'x\\'y"z'`);
  });
  it('printLatex', () => {
    expect(sj.printLatex(sj.pow(x, 2))).toBe('x^{2}\n');
  });
  it('multilineLatex (SymPy multiline_latex)', () => {
    const e = sj.parse('sin(x) - 2*cos(x) + 3*exp(x) + log(x)');
    expect(sj.multilineLatex(x, e, { termsPerLine: 2 })).toBe(
      '\\begin{align*}\nx = & 3 e^{x} + \\log{\\left(x \\right)} \\\\\n& + \\sin{\\left(x \\right)} - 2 \\cos{\\left(x \\right)} \n\\end{align*}',
    );
    expect(sj.multilineLatex(x, e, { environment: 'eqnarray', useDots: true })).toBe(
      '\\begin{eqnarray}\nx & = & 3 e^{x} \\dots\\nonumber\\\\\n& & + \\log{\\left(x \\right)} \\dots\\nonumber\\\\\n& & + \\sin{\\left(x \\right)} \\dots\\nonumber\\\\\n& & - 2 \\cos{\\left(x \\right)} \n\\end{eqnarray}',
    );
    expect(sj.multilineLatex(x, sj.parse('-sin(x) + cos(x)'), { environment: 'IEEEeqnarray' })).toBe(
      '\\begin{IEEEeqnarray}{rCl}\nx & = &- \\sin{\\left(x \\right)} \\nonumber\\\\\n& & + \\cos{\\left(x \\right)} \n\\end{IEEEeqnarray}',
    );
    expect(sj.multilineLatex(x, sj.parse('-x - y'))).toBe('\\begin{align*}\nx = &- x \\\\\n& - y \n\\end{align*}');
    expect(sj.multilineLatex(x, x)).toBe('\\begin{align*}\nx = & x \n\\end{align*}');
    expect(sj.multilineLatex(x, sj.parse('x + y + 1'), { termsPerLine: 3 })).toBe('\\begin{align*}\nx = & x + y + 1 \n\\end{align*}');
  });
});
