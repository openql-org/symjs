// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/branch/tools.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/** @file SymPy sympy.strategies.branch.tools: branching canonicalization. */

import type { Expr } from '../../core/nodes';
import type { BranchRule } from './core';
import { exhaust, multiplex } from './core';
import { topDown } from './traverse';

/**
 * Builds a rule that traverses the expression tree top down with each branching rule and repeats
 * across the resulting branches until no rule changes the tree.
 *
 * @see SymPy `sympy.strategies.branch.tools.canon`
 */
export function canon(...rules: BranchRule<Expr>[]): BranchRule<Expr> {
  return exhaust(multiplex(...rules.map((r) => topDown(r))));
}
