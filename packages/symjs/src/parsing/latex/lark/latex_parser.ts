// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 parsing/latex/lark/latex_parser.py (BSD-3-Clause).

import type { LatexTree } from '../tree';
import type { LatexResult } from '../tree';
import { LarkLatexGrammar } from './grammar/latex';
import type { LatexGrammarOptions } from './grammar/latex';
import { TransformToSymPyExpr } from './transformer';

/** Options for the hand-written Lark grammar and its expression transformer. */
export interface LarkLaTeXParserOptions {
  /** Convert the parse tree to an expression automatically. */
  readonly transform?: boolean;
  /** The class used to transform grammar nodes into expressions. */
  readonly transformer?: new () => TransformToSymPyExpr;
  /** Terminal overrides replace Python's grammar_file customization without file I/O. */
  readonly grammar?: LatexGrammarOptions;
  /** Receives the untransformed tree, including explicit ambiguity branches. */
  readonly debug?: (tree: LatexTree) => void;
}

/**
 * A reusable parser with the grammar and transformation behavior of SymPy's Lark backend.
 *
 * @see SymPy `sympy.parsing.latex.lark.latex_parser.LarkLaTeXParser`
 */
export class LarkLaTeXParser {
  /** The transformer that converts parse trees into expressions. */
  readonly transformer: TransformToSymPyExpr;
  /**
   * Creates a `LarkLaTeXParser`.
   *
   * @param options - The grammar and transformation settings in {@link LarkLaTeXParserOptions}.
   */
  constructor(private readonly options: LarkLaTeXParserOptions = {}) {
    this.transformer = new (options.transformer ?? TransformToSymPyExpr)();
  }
  /**
   * Parses LaTeX using this parser's grammar and transformer.
   *
   * @param source - The source text to parse.
   * @returns The expression or an explicit ambiguity tree.
   * @throws LaTeXParsingError when the input cannot be parsed or transformed into a mathematical expression.
   * @see SymPy `sympy.parsing.latex.lark.latex_parser.LarkLaTeXParser.doparse`
   */
  doparse(source: string): LatexResult {
    const tree = new LarkLatexGrammar(source, this.options.grammar).parse();
    this.options.debug?.(tree);
    if (this.options.transform === false) return tree;
    return this.transformer.transform(tree);
  }
}

/**
 * Experimental LaTeX parser with SymPy's Lark grammar, evaluation and explicit ambiguities.
 *
 * @experimental
 * @param source - The source text to parse.
 * @returns The parsed expression or a tree retaining ambiguous parses when using Lark.
 * @throws LaTeXParsingError when the input cannot be parsed or transformed into a mathematical expression.
 * @see SymPy `sympy.parsing.latex.lark.latex_parser.parse_latex_lark`
 */
export function parseLatexLark(source: string): LatexResult { return new LarkLaTeXParser().doparse(source); }
