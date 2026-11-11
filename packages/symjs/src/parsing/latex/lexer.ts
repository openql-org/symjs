// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Grammar terminals ported from SymPy 1.14, parsing/latex (BSD-3-Clause).

import { LaTeXParsingError } from './errors';

export interface LatexToken {
  readonly text: string;
  readonly start: number;
  readonly end: number;
}

const SPACING = new Set(['thinspace', 'medspace', 'thickspace', 'quad', 'qquad', 'negthinspace', 'negmedspace', 'negthickspace', 'left', 'right', 'vrule', 'vcenter', 'vbox', 'vskip', 'vspace']);

/** Keep digit boundaries for DIGIT fractions, and source offsets for greedy NUMBER terminals. */
export function tokenizeLatex(source: string, backend: 'antlr' | 'lark'): LatexToken[] {
  const tokens: LatexToken[] = [];
  const pattern = backend === 'antlr' ? /\\[A-Za-z]+|\\[^A-Za-z]|'+|[^\s]/g : /\\(?:text|mathrm)\{d\}|\\(?:begin|end)\{(?:p|b|v)?matrix\}|\\(?:begin|end)\{array\}(?:\{[^}]*\})?|\\[A-Za-z]+|\\[^A-Za-z]|'+|[^\s]/g;
  for (const match of source.matchAll(pattern)) {
    const text = match[0];
    const command = text.slice(1);
    // Negative spacing commands are whitespace; interpreting their \\ne prefix
    // as an inequality creates a mathematically unrelated expression.
    if (SPACING.has(command) && text.startsWith('\\')) continue;
    if (/^\\[,\x3a;!*\-./(=]$/.test(text)) continue;
    if (backend === 'lark' && ['\\limits', '\\nolimits', '\\displaystyle', '\\hfill'].includes(text)) continue;
    if (backend === 'antlr' && ['\\hfil', '\\"'].includes(text)) continue;
    if (backend === 'antlr' && text === '\\limits' && tokens.at(-1)?.text === '\\int' && tokens.at(-1)?.end === match.index) continue;
    if (/^[#$%~@]$/.test(text) || text === '\\' || backend === 'antlr' && text.startsWith('\\') && !/^\\[a-zA-Z]+$/.test(text) && !['\\{', '\\}'].includes(text)) throw new LaTeXParsingError(`Unexpected ${text} at index ${match.index}`);
    tokens.push({ text, start: match.index, end: match.index + text.length });
  }
  return tokens;
}

/**
 * Lark's dynamic lexer can match command prefixes: \\sinh x has both the
 * FUNC_SIN + h and FUNC_SINH tokenizations. Preserve each lexical path.
 */
export function larkTokenizations(source: string, commands: ReadonlySet<string>, terminalGroups: readonly ReadonlySet<string>[]): LatexToken[][] {
  let paths: LatexToken[][] = [[]];
  for (const token of tokenizeLatex(source, 'lark')) {
    const alternatives: LatexToken[][] = [];
    if (/^\\[a-zA-Z]+$/.test(token.text)) {
      for (const command of commands) if (token.text.startsWith(command) && !terminalGroups.some(group => group.has(command) && [...group].some(other => other.length > command.length && token.text.startsWith(other)))) {
        const end = token.start + command.length;
        alternatives.push([{ text: command, start: token.start, end }, ...Array.from(token.text.slice(command.length), (text, i) => ({ text, start: end + i, end: end + i + 1 }))]);
      }
      for (const command of SPACING) if (token.text.startsWith('\\' + command)) {
        const end = token.start + command.length + 1;
        alternatives.push(Array.from(token.text.slice(command.length + 1), (text, i) => ({ text, start: end + i, end: end + i + 1 })));
      }
    }
    if (!alternatives.length) alternatives.push([token]);
    paths = paths.flatMap(path => alternatives.map(tail => [...path, ...tail]));
  }
  return paths;
}
