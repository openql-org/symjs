// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { LarkLaTeXParser, TransformToSymPyExpr, parseLatexLark, LatexTree } from '../../../../src/parsing';
import type { Expr } from '../../../../src/core/nodes';
import { normalize, shape } from '../oracle';

class DecimalCommaTransformer extends TransformToSymPyExpr {
  override number(tokens: readonly string[]): Expr { return super.number(tokens.map(t => t.replace(',', '.'))); }
}
const custom = JSON.parse(readFileSync(new URL('../fixtures/custom.json', import.meta.url), 'utf8')) as { mode: string; src: string; expected?: unknown; error?: string }[];
describe('SymPy 1.14 test_custom_latex.py', () => {
  for (const c of custom) it(`${c.mode}: ${c.src}`, () => {
    const parser = c.mode === 'operators' ? new LarkLaTeXParser({ grammar: { divisionSymbols: ['/'], multiplicationSymbols: ['*', String.raw`\times`] } }) : c.mode === 'decimal' ? new LarkLaTeXParser({ grammar: { decimalSeparator: ',' }, transformer: DecimalCommaTransformer }) : new LarkLaTeXParser();
    if (c.error) expect(() => parser.doparse(c.src)).toThrow();
    else expect(normalize(shape(parser.doparse(c.src)))).toEqual(normalize(c.expected));
  });
});
it('returns grammar trees before transformation and sends them to the debug callback', () => {
  const seen: LatexTree[] = [];
  const parser = new LarkLaTeXParser({ transform: false, debug: tree => seen.push(tree) });
  const tree = parser.doparse('x+1');
  expect(tree).toBeInstanceOf(LatexTree);
  expect(seen).toEqual([tree]);
  expect(shape(new TransformToSymPyExpr().transform(tree as LatexTree))).toEqual(shape(parseLatexLark('x+1')));
});
