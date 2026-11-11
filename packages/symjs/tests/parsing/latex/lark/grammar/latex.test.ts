// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { describe, expect, it } from 'vitest';
import { parseLatexLark } from '../../../../../src/parsing';
import { evaluate } from '../../../../../src/core/parameters';
import { cases, normalize, shape } from '../../oracle';

describe('SymPy 1.14 test_latex_lark.py', () => {
  for (const c of cases('lark')) it(`${c.group}[${c.index}] evaluate=${c.evaluate}: ${c.src}${c.difference ? ` — ${c.difference}` : ''}`, () => {
    if (c.error && !c.difference) expect(() => evaluate(c.evaluate, () => parseLatexLark(c.src))).toThrow();
    else expect(normalize(shape(evaluate(c.evaluate, () => parseLatexLark(c.src))))).toEqual(normalize(c.correctExpected ?? c.expected));
  });
});

it('rejects Greek names absent from greek_symbols.lark', () => {
  expect(() => parseLatexLark(String.raw`a_{\unknown}`)).toThrow();
});
