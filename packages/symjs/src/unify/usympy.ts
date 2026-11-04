// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/unify/usympy.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.unify.usympy: the interface of the unification engine
 * ({@link import('./core')}) to expressions. An expression is turned into
 * a tree of {@link Compound}s whose operators are {@link ExprOp}s (the class
 * of a node), unified, and turned back.
 */

import { BoolOp } from '../core/boolalg';
import { ExprMap } from '../core/exprmap';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Expr as ExprClass, ExtensionExpr, Fn, Limit, Mul, Pow } from '../core/nodes';
import { sympify } from '../core/ops';
import { rebuild as rebuildNode } from '../core/traverse';
import { setClass } from '../printing/sets';
import { basicNew, funcName } from '../strategies/util';
import type { Term } from './core';
import { Compound, CondVariable, Variable, unify as unifyTerms } from './core';

/**
 * The operator of a deconstructed node: its SymPy class (`type(expr)`),
 * with the node as the template from which the class is rebuilt.
 */
export class ExprOp {
  readonly unifyKey: string;
  constructor(readonly template: Expr) {
    this.unifyKey = `${template.kind}:${funcName(template)}${template instanceof Limit ? template.dir : ''}`;
  }
  toString(): string {
    return funcName(this.template);
  }
}

const opOf = (x: Term): Expr | undefined => (x instanceof Compound && x.op instanceof ExprOp ? x.op.template : undefined);

/** SymPy `sympy_associative(op)`: AssocOp (Add, Mul, And, Or, Min, Max), MatAdd, MatMul, Union, Intersection, FiniteSet. */
export function sympyAssociative(op: Expr): boolean {
  if (op instanceof Add || op instanceof Mul) return true;
  if (op instanceof BoolOp) return op.op === 'And' || op.op === 'Or';
  if (op instanceof Fn) return op.name === 'Min' || op.name === 'Max';
  if (op instanceof ExtensionExpr) return op.name === 'MatAdd' || op.name === 'MatMul';
  const cls = setClass(op);
  return cls === 'Union' || cls === 'Intersection' || cls === 'FiniteSet';
}

/** SymPy `sympy_commutative(op)`: Add, MatAdd, Union, Intersection, FiniteSet. */
export function sympyCommutative(op: Expr): boolean {
  if (op instanceof Add) return true;
  if (op instanceof ExtensionExpr) return op.name === 'MatAdd';
  const cls = setClass(op);
  return cls === 'Union' || cls === 'Intersection' || cls === 'FiniteSet';
}

/** SymPy `is_associative(x)`: whether `x` is a Compound of an associative class. */
export function isAssociative(x: Term): boolean {
  const op = opOf(x);
  return op !== undefined && sympyAssociative(op);
}

/** SymPy `is_commutative(x)`: whether `x` is a Compound of a commutative class (a Mul of commutative factors). */
export function isCommutative(x: Term): boolean {
  const op = opOf(x);
  if (op === undefined || !(x instanceof Compound)) return false;
  if (sympyCommutative(op)) return true;
  return op instanceof Mul && x.args.every((arg) => constructExpr(arg).isCommutative);
}

/** SymPy `mk_matchtype(typ)`: a predicate for the terms of a SymPy class (a node or a Compound of that class). */
export function mkMatchtype(typ: string): (x: Term) => boolean {
  return function matchtype(x: Term): boolean {
    if (x instanceof ExprClass) return funcName(x) === typ;
    const op = opOf(x);
    return op !== undefined && funcName(op) === typ;
  };
}

/** SymPy `deconstruct(s, variables=())`: turn an expression into a tree of Compounds, the `variables` into Variables. */
export function deconstruct(s: Term, variables: readonly Expr[] = []): Term {
  if (s instanceof ExprClass && variables.some((v) => v.equals(s))) return new Variable(s);
  if (!(s instanceof ExprClass) || s.isAtom) return s;
  return new Compound(
    new ExprOp(s),
    s.args.map((arg) => deconstruct(arg, variables)),
  );
}

/** Whether nodes of this class are built without evaluation (SymPy `eval_false_legal`: AssocOp, Pow, FiniteSet). */
const evalFalseLegal = (op: Expr): boolean => op instanceof Pow || (sympyAssociative(op) && !(op instanceof ExtensionExpr) && setClass(op) === undefined);

/**
 * SymPy `construct(t)`: turn a tree of Compounds back into an expression.
 * Sums, products, powers, And/Or and Min/Max are built without evaluation,
 * other nodes are rebuilt with evaluation.
 */
export function construct(t: Term): Term {
  if (t instanceof Variable || t instanceof CondVariable) return t.arg;
  const op = opOf(t);
  if (op === undefined || !(t instanceof Compound)) return t;
  const args = t.args.map(constructExpr);
  return evalFalseLegal(op) ? basicNew(op, args) : rebuildNode(op, args);
}

/** {@link construct} of a tree that stands for an expression. */
function constructExpr(t: Term): Expr {
  const e = construct(t);
  if (!(e instanceof ExprClass)) throw new TypeError(`unify: ${String(e)} is not an expression`);
  return e;
}

/**
 * SymPy `unify(x, y, s=None, variables=())`: structural unification of two
 * expressions or patterns. The `variables` are wild: they match any
 * subexpression; other symbols match only themselves. Associative and
 * commutative classes (Add, Mul, Union, ...) match in every grouping and
 * order, so many substitutions can be generated. `s` gives initial bindings.
 */
export function* unify(x: ExprLike, y: ExprLike, s: ReadonlyMap<Expr, ExprLike> | null = null, variables: readonly Expr[] = []): Generator<ExprMap<Expr>, void, undefined> {
  const decons = (e: Term): Term => deconstruct(e, variables);
  const start = new Map<Term, Term>();
  for (const [k, v] of s ?? []) start.set(decons(k), decons(sympify(v)));
  for (const d of unifyTerms(decons(sympify(x)), decons(sympify(y)), start, { isAssociative, isCommutative })) {
    yield new ExprMap([...d].map(([k, v]) => [constructExpr(k), constructExpr(v)] as const));
  }
}

/**
 * SymPy `sympy.unify.rebuild(s)` (`construct(deconstruct(s))`): rebuild an
 * expression with the classes' own construction, keeping sums, products,
 * powers, And/Or and Min/Max unevaluated. (The core `rebuild` without
 * arguments rebuilds with evaluation, like `sympy.strategies.rebuild`.)
 */
export function rebuild(s: Expr): Expr {
  return constructExpr(deconstruct(s));
}
