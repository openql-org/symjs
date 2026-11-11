// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Expr, ExtensionExpr, Sym, S } from '../../../../src/core/nodes';
import { str } from '../../../../src/printing/str';
import { latex } from '../../../../src/printing/latex';
import { parseLatexLark, TransformToSymPyExpr, LatexTree, LaTeXParsingError } from '../../../../src/parsing';

const tree = (name: string, ...children: (LatexTree | Expr | string)[]) => new LatexTree(name, children);
const x = tree('symbol', 'x');
const d = tree('symbol', 'd');
const one = tree('number', '1');
const operator = tree('derivative_operator', x);

it('validates custom transformer trees and rejects unapplied differential arithmetic', () => {
  const transformer = new TransformToSymPyExpr();
  for (const input of [
    tree('number', x), tree('missing_rule'), tree('sin_power', '', '^', one, x),
    tree('unknown_power', '', '^', one, x), tree('arcsin_power', '', '^', one, x),
    tree('fraction', d, tree('adjacent_expressions', d, operator)),
    tree('fraction', tree('adjacent_expressions', d, operator), tree('adjacent_expressions', d, x)),
    tree('limit', x, x, tree('limit_destination', one, 'left')),
  ]) {
    if (input.data === 'sin_power') expect(transformer.transform(input)).toBeInstanceOf(Expr);
    else expect(() => transformer.transform(input)).toThrow(LaTeXParsingError);
  }
  expect(() => parseLatexLark("(x)'" )).toThrow(LaTeXParsingError);
});

it('retains Dirac notation through traversal, noncommutative products, and both printers', () => {
  const bra = parseLatexLark(String.raw`\langle x|`);
  const ket = parseLatexLark(String.raw`|y\rangle`);
  const inner = parseLatexLark(String.raw`\langle x+y|z+w\rangle`);
  const outer = parseLatexLark(String.raw`|x\rangle\langle y|`);
  expect(str(bra as Expr)).toBe('<x|');
  expect(str(ket as Expr)).toBe('|y>');
  expect(str(inner as Expr)).toBe('<x + y|w + z>');
  expect(str(outer as Expr)).toBe('|x><y|');
  expect(latex(inner as Expr)).toContain('\\left\\langle');
  expect(latex(outer as Expr)).toContain('\\right\\rangle');
  expect((bra as Expr).isCommutative).toBe(false);
  expect((ket as Expr).isCommutative).toBe(false);
  expect((inner as Expr).isCommutative).toBe(true);
  expect((outer as Expr).isCommutative).toBe(false);
  const replaced = (bra as ExtensionExpr).withArgs([new Sym('z')]);
  expect(str(replaced)).toBe('<z|');
  expect(latex(replaced)).toBe(String.raw`{\left\langle z\right|}`);
});

it('keeps arbitrary matrix exponents symbolic and handles scalar function powers', () => {
  const m = String.raw`\begin{pmatrix}1\end{pmatrix}`;
  expect(str(parseLatexLark(`${m}^q`) as Expr)).toContain('q');
  expect(parseLatexLark(String.raw`\cos^{-1}x`)).toBeInstanceOf(Expr);
  expect(new TransformToSymPyExpr().transform(tree('expression_value', S.One))).toBe(S.One);
});

it('respects the global evaluation flag for numerical relations', async () => {
  const { evaluate } = await import('../../../../src/core/parameters');
  const { parseLatex } = await import('../../../../src/parsing');
  for (const backend of ['antlr', 'lark'] as const) {
    expect(str(evaluate(false, () => parseLatex('1=1', { backend })) as Expr)).toBe('Eq(1, 1)');
    expect(str(evaluate(false, () => parseLatex('2<3', { backend })) as Expr)).toBe('2 < 3');
  }
});
