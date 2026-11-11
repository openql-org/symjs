// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { describe, expect, it } from 'vitest';
import { parseLatex, LaTeXParsingError } from '../../../src/parsing';
import { cases, normalize, shape } from './oracle';

describe('SymPy 1.14 test_latex.py', () => {
  for (const c of cases('antlr')) it(`${c.group}[${c.index}] strict=${c.strict ?? false}: ${c.src}`, () => {
    if (c.error) expect(() => parseLatex(c.src, { strict: c.strict })).toThrow(LaTeXParsingError);
    else expect(normalize(shape(parseLatex(c.src, { strict: c.strict })))).toEqual(normalize(c.expected));
  });
});

it('parses evaluation scripts, balanced bra labels and equation alignment', () => {
  for (const src of ['x=&y', 'x^{y}_z', String.raw`\langle (x+y)|`, String.raw`\lfloor (x+y)\rfloor`]) expect(parseLatex(src)).toBeDefined();
});
it('rejects incomplete delimiters and invalid limit subscripts', () => {
  for (const src of [String.raw`\lfloor x`, String.raw`\langle |`, String.raw`\lim_{1\to0}x`, String.raw`\lim_{x=0}x`, String.raw`\lim_{x\to0^{*}}x`]) expect(() => parseLatex(src)).toThrow(LaTeXParsingError);
});
