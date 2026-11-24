// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/rl.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.rl: generic rules on expression trees
 * (removing identities, gathering equal arguments, sorting, flattening,
 * distributing, ...). They assume nothing about a node beyond its
 * arguments; new nodes are built without evaluation ({@link basicNew})
 * unless stated otherwise.
 */

import { BasicNode } from '../core/basic';
import { and, or } from '../core/boolalg';
import { at, pair } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { rebuild } from '../core/traverse';
import { flatten, sift } from '../utilities/iterables';
import { compareValues, valueEquals, valueKey } from '../utilities/values';
import type { Rule } from './core';
import { basicNew, funcName } from './util';

/** Rebuilds a node from a template expression and an ordered list of replacement arguments. */
export type NewFn = (op: Expr, args: readonly Expr[]) => Expr;

/**
 * A rule that removes the arguments that are
 * identities (`isid`); when all are identities, the first one is kept.
 *
 * @param isid - The predicate identifying neutral arguments.
 * @param newFn - The function that rebuilds a node from its operator and arguments.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.rl.rm_id`
 * @example
 * ```ts
 * import { SymFunction, arg, ex, rmId, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * rmId(arg => arg.equals(ex`0`))(SymFunction('f')(0, x)); // => f(x)
 * ```
 */
export function rmId(isid: (x: Expr) => boolean, newFn: NewFn = basicNew): Rule<Expr> {
  return function identRemove(expr: Expr): Expr {
    const ids = expr.args.map(isid);
    const count = ids.filter(Boolean).length;
    if (count === 0) return expr;
    if (count !== ids.length) return newFn(expr, expr.args.filter((_, i) => !ids[i]));
    return newFn(expr, expr.args.slice(0, 1));
  };
}

/**
 * A rule that gathers the arguments with
 * the same `key`, adding their `count`s, and replaces them with
 * `combine(total, key)` (`x + x -> 2*x`).
 *
 * @param key - The grouping key for a term.
 * @param count - The coefficient contributed by a term.
 * @param combine - The function rebuilding a term from its total coefficient and key.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.rl.glom`
 * @example
 * ```ts
 * import { SymFunction, arg, count, glom, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * glom(arg => arg, () => 1, (count, arg) => count.mul(arg))(SymFunction('f')(x, x, y)); // => f(2*x, y)
 * ```
 */
export function glom<K>(key: (x: Expr) => K, count: (x: Expr) => ExprLike, combine: (cnt: Expr, arg: K) => Expr): Rule<Expr> {
  return function conglomerate(expr: Expr): Expr {
    const groups = sift(expr.args, key);
    const newargs = [...groups].map(([mat, args]) => combine(add(...args.map(count)), mat));
    const keys = (xs: readonly Expr[]) => [...new Set(xs.map(valueKey))].sort().join('\u0000');
    return keys(newargs) !== keys(expr.args) ? basicNew(expr, newargs) : expr;
  };
}

/**
 * A rule that sorts the arguments by `key` (stable, Python ordering).
 *
 * @param key - The function or functions producing comparison or grouping keys.
 * @param newFn - The function that rebuilds a node from its operator and arguments.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.rl.sort`
 * @example
 * ```ts
 * import { SymFunction, arg, sstr, symbols } from '@symjs/symjs';
 * import { sort } from '@symjs/symjs/strategies';
 *
 * const [x, y] = symbols('x y');
 * sort(arg => sstr(arg))(SymFunction('f')(y, x)); // => f(x, y)
 * ```
 */
export function sort(key: (x: Expr) => unknown, newFn: NewFn = basicNew): Rule<Expr> {
  return function sortRl(expr: Expr): Expr {
    const keyed = expr.args.map((a) => [key(a), a] as const);
    keyed.sort((p, q) => compareValues(p[0], q[0]));
    return newFn(
      expr,
      keyed.map((p) => p[1]),
    );
  };
}

/**
 * A node class for {@link distribute}: a SymPy class name ({@link funcName}),
 * or a name with the constructor of the class.
 */
export type NodeClass = string | { readonly name: string; readonly construct: (args: readonly Expr[]) => Expr };

const BUILTIN: Readonly<Record<string, (args: readonly Expr[]) => Expr>> = {
  Add: (args) => add(...args),
  Mul: (args) => mul(...args),
  Pow: (args) => pow(...pair(args)),
  And: (args) => and(...args),
  Or: (args) => or(...args),
};

/**
 * Calling a class (SymPy `A(*args)`, with evaluation): the class of
 * `template` when it is one, else the given constructor, the core class of
 * that name (Add, Mul, Pow, And, Or), or a subclass of Basic of that name.
 */
function construct(cls: NodeClass, template: Expr, args: readonly Expr[]): Expr {
  const name = typeof cls === 'string' ? cls : cls.name;
  if (funcName(template) === name) return rebuild(template, args);
  if (typeof cls !== 'string') return cls.construct(args);
  return (BUILTIN[name] ?? ((xs: readonly Expr[]) => new BasicNode(xs, name)))(args);
}

/**
 * A rule that turns an `A` containing a `B` into a
 * `B` of `A`s (`2*(x + y) -> 2*x + 2*y`). The new nodes are built with
 * evaluation, like calling the classes in SymPy.
 *
 * @param A - The outer operator to distribute.
 * @param B - The inner operator over which to distribute.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.rl.distribute`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { distribute } from '@symjs/symjs/strategies';
 * distribute('Mul', 'Add')(ex`2*(x + y)`); // => 2*x + 2*y
 * ```
 */
export function distribute(A: NodeClass, B: NodeClass): Rule<Expr> {
  const bName = typeof B === 'string' ? B : B.name;
  return function distributeRl(expr: Expr): Expr {
    const i = expr.args.findIndex((arg) => funcName(arg) === bName);
    if (i < 0) return expr;
    const head = expr.args.slice(0, i);
    const tail = expr.args.slice(i + 1);
    const b = at(expr.args, i);
    return construct(
      B,
      b,
      b.args.map((arg) => construct(A, expr, [...head, arg, ...tail])),
    );
  };
}

/**
 * A rule that replaces `a` (exactly) with `b`.
 *
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.rl.subs`
 */
export function subs<T>(a: T, b: T): Rule<T> {
  return function subsRl(expr: T): T {
    return valueEquals(expr, a) ? b : expr;
  };
}

/**
 * Returns the argument of a node with a single argument, else the node.
 *
 * @param expr - The expression whose sole operand should be extracted.
 * @returns The argument of a node with a single argument, else the node.
 * @see SymPy `sympy.strategies.rl.unpack`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { unpack } from '@symjs/symjs/strategies';
 * unpack(ex`sin(x)`); // => x
 * ```
 */
export function unpack(expr: Expr): Expr {
  return expr.args.length === 1 ? at(expr.args, 0) : expr;
}

export { flatten, rebuild };
