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
  readonly transform?: boolean;
  readonly transformer?: new () => TransformToSymPyExpr;
  /** Terminal overrides replace Python's grammar_file customization without file I/O. */
  readonly grammar?: LatexGrammarOptions;
  /** Receives the untransformed tree, including explicit ambiguity branches. */
  readonly debug?: (tree: LatexTree) => void;
}

/** A reusable parser with the grammar and transformation behavior of SymPy's Lark backend. */
export class LarkLaTeXParser {
  readonly transformer: TransformToSymPyExpr;
  constructor(private readonly options: LarkLaTeXParserOptions = {}) {
    this.transformer = new (options.transformer ?? TransformToSymPyExpr)();
  }
  doparse(source: string): LatexResult {
    const tree = new LarkLatexGrammar(source, this.options.grammar).parse();
    this.options.debug?.(tree);
    if (this.options.transform === false) return tree;
    return this.transformer.transform(tree);
  }
}

/** Experimental LaTeX parser with SymPy's Lark grammar, evaluation and explicit ambiguities. @experimental */
export function parseLatexLark(source: string): LatexResult { return new LarkLaTeXParser().doparse(source); }
