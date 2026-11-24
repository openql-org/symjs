// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { Expr } from '../../core/nodes';

/** A grammar rule and its children; `_ambig` retains all possible interpretations. */
export class LatexTree {
  /**
   * Creates a `LatexTree`.
   *
   * @param data - The grammar rule represented by this node.
   * @param children - The tokens and subtrees matched by the rule.
   */
  constructor(
    /** The grammar rule represented by this node. */
    readonly data: string,
    /** The tokens and subtrees matched by the rule. */
    readonly children: readonly (LatexTree | Expr | string)[]) {}
}

/** An expression, or the explicit ambiguity tree returned by the Lark grammar. */
export type LatexResult = Expr | LatexTree;
