// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/util.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.util: building a node without evaluation
 * (`Basic.__new__`) and the functions that tell the traversals how to take
 * a tree apart and put it together.
 *
 * SymPy passes the class of a node (`type(expr)`) as the operator; symjs
 * nodes of one class differ in their name (`sin`, `f`, `Basic`, ...), so the
 * operator is the node itself, used as a template for the new node.
 */

import { BoolOp } from '../core/boolalg';
import { Concrete } from '../core/concrete';
import type { Expr } from '../core/nodes';
import { Add, Derivative, Dummy, ExtensionExpr, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rational, Rel, Sym, UndefFn, Wild } from '../core/nodes';
import { rebuild } from '../core/traverse';
import { setClass } from '../printing/sets';

/** How a traversal takes a tree apart and puts it together (SymPy `basic_fns`, `expr_fns`). */
export interface TreeFns {
  /** The operator of a node (the node itself, as the template of `new`). */
  readonly op: (e: Expr) => Expr;
  /** A node of the operator's class with the given arguments. */
  readonly new: (op: Expr, args: readonly Expr[]) => Expr;
  /** Whether the node is a leaf (its arguments are not visited). */
  readonly leaf: (e: Expr) => boolean;
  /** The arguments of a node. */
  readonly children: (e: Expr) => readonly Expr[];
}

function two(args: readonly Expr[], name: string): [Expr, Expr] {
  const [a, b] = args;
  if (args.length !== 2 || a === undefined || b === undefined) throw new TypeError(`${name} takes 2 arguments (${args.length} given)`);
  return [a, b];
}

/**
 * SymPy `Basic.__new__(type(op), *args)`: a node of the class of `op` with
 * the given arguments, without evaluation (`Add` keeps `1 + 2`). Sets, whose
 * classes belong to a higher layer, are rebuilt with evaluation; an atom is
 * returned as it is.
 */
export function basicNew(op: Expr, args: readonly Expr[]): Expr {
  if (op instanceof ExtensionExpr) return op.withArgs(args);
  if (op instanceof Add) return new Add(args);
  if (op instanceof Mul) return new Mul(args);
  if (op instanceof Pow) return new Pow(...two(args, 'Pow'));
  if (op instanceof Fn) return new Fn(op.name, args);
  if (op instanceof UndefFn) return new UndefFn(op.name, args);
  if (op instanceof Rel) return new Rel(op.op, ...two(args, op.op));
  if (op instanceof BoolOp) return new BoolOp(op.op, args);
  if (op instanceof Piecewise) return new Piecewise(args);
  if (op instanceof Integral) return new Integral(args);
  if (op instanceof Derivative) return new Derivative(args);
  if (op instanceof Order) return new Order(args);
  if (op instanceof Limit) return new Limit(args, op.dir);
  if (op instanceof Concrete) return new Concrete(op.kind2, args);
  return rebuild(op, args);
}

const REL_CLASS: Readonly<Record<Rel['op'], string>> = {
  Eq: 'Equality',
  Ne: 'Unequality',
  Lt: 'StrictLessThan',
  Le: 'LessThan',
  Gt: 'StrictGreaterThan',
  Ge: 'GreaterThan',
};

/**
 * The SymPy class name of a node (`type(expr).__name__`): `Add`, `Mul`,
 * `Pow`, the name of a function (`sin`, `f`), `Basic` (or the head of a
 * {@link BasicNode}), `And`, `StrictLessThan`, `FiniteSet`, `Symbol`,
 * `Integer`, ...
 */
export function funcName(e: Expr): string {
  if (e instanceof ExtensionExpr) return e.name;
  if (e instanceof Fn) return e.name === 'abs' ? 'Abs' : e.name;
  if (e instanceof UndefFn) return e.name;
  if (e instanceof BoolOp) return e.className;
  if (e instanceof Rel) return REL_CLASS[e.op];
  if (e instanceof Concrete) return e.kind2;
  if (e instanceof Wild) return 'Wild';
  if (e instanceof Dummy) return 'Dummy';
  if (e instanceof Sym) return 'Symbol';
  if (e instanceof Rational) return e.q === 1n ? 'Integer' : 'Rational';
  return setClass(e) ?? e.kind;
}

/** SymPy `assoc(d, k, v)`: a copy of the map `d` with `k` associated to `v`. */
export function assoc<K, V>(d: ReadonlyMap<K, V>, k: K, v: V): Map<K, V> {
  const copy = new Map(d);
  copy.set(k, v);
  return copy;
}

/** SymPy `basic_fns`: nodes are rebuilt without evaluation ({@link basicNew}). */
export const basicFns: TreeFns = {
  op: (e) => e,
  new: basicNew,
  leaf: (e) => e.isAtom,
  children: (e) => e.args,
};

/** SymPy `expr_fns`: like {@link basicFns}, but nodes are rebuilt with evaluation. */
export const exprFns: TreeFns = { ...basicFns, new: (op, args) => rebuild(op, args) };

export { basicNew as new };
