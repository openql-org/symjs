// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 parsing/latex/__init__.py (BSD-3-Clause).

import { at } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { NotImplementedError } from '../../core/errors';
import { LaTeXParsingError } from './errors';
import { parseLatexAntlr } from './_parse_latex_antlr';
import { parseLatexLark } from './lark/latex_parser';
import type { LatexResult } from './tree';

/** Options of SymPy parse_latex. The ANTLR grammar is the default. */
export interface ParseLatexOptions {
  /** Require the ANTLR backend to consume the entire input. */
  readonly strict?: boolean;
  /** Select the ANTLR or Lark grammar. */
  readonly backend?: 'antlr' | 'lark';
}

/** Reject unmatched matrix environments and their enclosing delimiters before parsing. */
function checkMatrixDelimiters(source: string): void {
  const stack: { name: string; open: string; index: number }[] = [];
  for (const match of source.matchAll(/\\(begin|end)\{((?:[pbv])?matrix|array)\}(?:\{[^}]*\})?/g)) {
    const name = at(match, 2);
    if (match[1] === 'begin') {
      const prefix = source.slice(0, match.index);
      const open = /((?:\\left)?[([|])\s*\{*\s*$/.exec(prefix)?.[1] ?? '';
      stack.push({ name, open, index: match.index });
    } else {
      const begin = stack.pop();
      if (!begin || begin.name !== name) throw new LaTeXParsingError(`Unexpected matrix end at index ${match.index}`);
      if (name === 'matrix' || name === 'array') {
        const close = /^\s*\}*\s*((?:\\right)?[)\]|])/.exec(source.slice(match.index + match[0].length))?.[1] ?? '';
        const expected = begin.open.replace('\\left', '\\right').replace('(', ')').replace('[', ']');
        if (close !== expected) throw new LaTeXParsingError(`Mismatched matrix delimiters at index ${begin.index}`);
      }
    }
  }
  if (stack.length) throw new LaTeXParsingError('Missing matrix end delimiter');
}

/**
 * Convert LaTeX to an expression; Lark preserves ambiguous inputs as explicit trees.
 *
 * @param source - The source text to parse.
 * @param options - The backend and parsing settings in {@link ParseLatexOptions}.
 * @returns The parsed expression or a tree retaining ambiguous parses when using Lark.
 * @throws LaTeXParsingError when the input cannot be parsed or transformed into a mathematical expression.
 * @see SymPy `sympy.parsing.latex.parse_latex`
 * @example
 * ```ts
 * import { parseLatex } from '@symjs/symjs/parsing';
 *
 * parseLatex('\\frac {1 + \\sqrt {\\a}} {\\b}'); // => (sqrt(a) + 1)/b
 * ```
 */
export function parseLatex(source: string, options?: ParseLatexOptions & { backend?: 'antlr' }): Expr;
export function parseLatex(source: string, options: ParseLatexOptions): LatexResult;
export function parseLatex(source: string, options: ParseLatexOptions = {}): LatexResult {
  checkMatrixDelimiters(source);
  const backend: string = options.backend ?? 'antlr';
  if (backend === 'antlr') return parseLatexAntlr(source, options.strict);
  if (backend === 'lark') return parseLatexLark(source);
  throw new NotImplementedError(`Using the '${backend}' backend in the LaTeX parser is not supported`);
}
