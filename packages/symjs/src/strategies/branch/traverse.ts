// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/branch/traverse.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/** @file SymPy sympy.strategies.branch.traverse: branching strategies that traverse an expression tree. */

import type { Expr } from '../../core/nodes';
import { product } from '../../utilities/itertools';
import type { TreeFns } from '../util';
import { basicFns } from '../util';
import type { BranchRule } from './core';
import { chain, doOne, identity } from './core';

/** SymPy `top_down(brule, fns=basic_fns)`: apply a branching rule down a tree, on the top nodes first. */
export function topDown(brule: BranchRule<Expr>, fns: TreeFns = basicFns): BranchRule<Expr> {
  return chain(doOne(brule, identity), (expr) => sall(topDown(brule, fns), fns)(expr));
}

/** SymPy `sall(brule, fns=basic_fns)`: strategic all, apply a branching rule to the arguments (every combination). */
export function sall(brule: BranchRule<Expr>, fns: TreeFns = basicFns): BranchRule<Expr> {
  return function* allRl(expr: Expr): Generator<Expr, void, undefined> {
    if (fns.leaf(expr)) {
      yield expr;
      return;
    }
    const myop = fns.op(expr);
    for (const args of product(fns.children(expr).map((c) => [...brule(c)]))) yield fns.new(myop, args);
  };
}
