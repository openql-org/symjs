// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { parseLatex } from '../../../src/parsing';
import { Float } from '../../../src/core/nodes';
import { str } from '../../../src/printing/str';
import { latex } from '../../../src/printing/latex';
import { cases, normalize, shape } from './oracle';

const extra = JSON.parse(readFileSync(new URL('./fixtures/extra.json', import.meta.url), 'utf8')) as { backend: 'antlr' | 'lark'; src: string; index: number; precision?: number; str?: string; expected?: unknown; correctExpected?: unknown; correctError?: string; difference?: string; error?: string }[];
describe('additional grammar productions', () => {
  for (const c of extra) it(`${c.backend}[${c.index}]: ${c.src}${c.difference ? ` — ${c.difference}` : ''}`, () => {
    if (c.correctError || c.error && !c.difference) expect(() => parseLatex(c.src, { backend: c.backend })).toThrow();
    else {
      const result = parseLatex(c.src, { backend: c.backend });
      expect(normalize(shape(result))).toEqual(normalize(c.correctExpected ?? c.expected));
      if (c.precision) {
        expect(result).toBeInstanceOf(Float);
        expect((result as Float).prec).toBe(c.precision);
        expect(str(result as Float)).toBe(c.str);
      }
    }
  });
});
describe('printing parsed expressions matches SymPy latex(parse_latex(s))', () => {
  const indices = new Set([0, 2, 4, 5, 6, 8, 13, 15, 16, 18, 38, 40, 41, 42, 44, 48, 58, 60, 68, 71, 78, 85, 88, 100, 116, 122, 139, 145, 149, 150, 151, 152, 155]);
  for (const c of cases('antlr').filter(c => c.group === 'GOOD_PAIRS' && indices.has(c.index))) it(c.src, () => {
    expect(latex(parseLatex(c.src))).toBe(c.latex);
  });
});

it('reports missing matrix delimiters and unsupported backends', () => {
  expect(() => parseLatex(String.raw`(\begin{matrix}1\end{matrix}`)).toThrow();
  expect(() => parseLatex('x', { backend: 'other' as 'antlr' })).toThrow('not supported');
});
