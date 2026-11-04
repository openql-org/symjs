// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/tools.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.tools: conglomerate strategies on
 * expression trees (simultaneous exact substitution, canonicalization,
 * rules by node class).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { sympify } from '../core/ops';
import type { Rule } from './core';
import { doOne, exhaust, identity, switch as switchRule } from './core';
import { subs as subsRl } from './rl';
import { topDown } from './traverse';
import type { TreeFns } from './util';
import { basicFns, funcName } from './util';

/**
 * SymPy `subs(d, **kwargs)`: full simultaneous exact substitution of the
 * keys of `d` by its values, top down (without evaluation by default).
 */
export function subs(d: ReadonlyMap<Expr, ExprLike> | readonly (readonly [Expr, ExprLike])[], fns: TreeFns = basicFns): Rule<Expr> {
  const pairs = [...d];
  if (!pairs.length) return identity;
  return topDown(doOne(...pairs.map(([k, v]) => subsRl(k, sympify(v)))), fns);
}

/**
 * SymPy `canon(*rules, **kwargs)`: canonicalization; each rule is applied
 * top down through the tree, one after the other, until nothing changes.
 * The tree functions can be given after the rules as `{ fns }`.
 */
export function canon(...rulesAndOpts: (Rule<Expr> | { readonly fns: TreeFns })[]): Rule<Expr> {
  const rules: Rule<Expr>[] = [];
  let fns = basicFns;
  for (const r of rulesAndOpts) {
    if (typeof r === 'function') rules.push(r);
    else fns = r.fns;
  }
  return exhaust(topDown(exhaust(doOne(...rules)), fns));
}

/**
 * SymPy `typed(ruletypes)`: apply the rule of the class of the node
 * (`{ Add: rmZeros, Mul: rmOnes }`, keyed by SymPy class names, see
 * {@link funcName}); a node of another class is left unchanged.
 */
export function typed(ruletypes: ReadonlyMap<string, Rule<Expr>> | Readonly<Record<string, Rule<Expr>>>): Rule<Expr> {
  return switchRule(funcName, ruletypes);
}
