// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/utilities/decorator.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's function decorators that have a meaning in JavaScript:
 * `threaded` and `xthreaded` (apply a function to the elements of
 * containers, the sides of relations and, for `threaded`, the terms of
 * sums) and `memoize_property` (compute a property once per object).
 */

import type { ExprLike } from '../core/nodes';
import { Add, Expr, Rel } from '../core/nodes';
import { sympify } from '../core/ops';
import { rebuild } from '../core/traverse';

/** A matrix as the threaded functions see it (the matrices layer is above this one). */
export interface ThreadableMatrix {
  map(f: (e: Expr) => Expr): unknown;
}

/** What a threaded function accepts: an expression, a matrix, or an array or set of them. */
export type Threadable = ExprLike | ThreadableMatrix | readonly Threadable[] | ReadonlySet<Threadable>;

const isMatrix = (v: unknown): v is ThreadableMatrix => typeof v === 'object' && v !== null && !(v instanceof Expr) && !Array.isArray(v) && !(v instanceof Set) && typeof Reflect.get(v, 'map') === 'function';

/**
 * A threaded function: an array or a set gives the results for its items,
 * an expression the result (a sum or relation rebuilt from the results for
 * its parts), a matrix the matrix of the results.
 */
export interface ThreadedFunction<R, A extends unknown[]> {
  (expr: readonly Threadable[], ...args: A): R[];
  (expr: ReadonlySet<Threadable>, ...args: A): Set<R>;
  (expr: ExprLike, ...args: A): R | Expr;
  (expr: ThreadableMatrix, ...args: A): unknown;
}

/** SymPy `threaded_factory(func, use_add)`. */
function threadedFactory<R, A extends unknown[]>(func: (expr: Expr, ...args: A) => R, useAdd: boolean): ThreadedFunction<R, A> {
  function threadedFunc(expr: readonly Threadable[], ...args: A): R[];
  function threadedFunc(expr: ReadonlySet<Threadable>, ...args: A): Set<R>;
  function threadedFunc(expr: ExprLike, ...args: A): R | Expr;
  function threadedFunc(expr: ThreadableMatrix, ...args: A): unknown;
  function threadedFunc(expr: Threadable, ...args: A): unknown {
    const f = (e: Expr): R => func(e, ...args);
    if (isMatrix(expr)) return expr.map((e) => expectExpr(f(e)));
    // an array or a set: the function applied to the items (themselves not threaded, as in SymPy)
    if (isList(expr)) return expr.map((e) => f(item(e)));
    if (expr instanceof Set) return new Set([...expr].map((e) => f(item(e))));
    const e = item(expr);
    if (useAdd && e instanceof Add) return rebuild(e, e.args.map((a) => expectExpr(f(a))));
    if (e instanceof Rel) return rebuild(e, [expectExpr(f(e.lhs)), expectExpr(f(e.rhs))]);
    return f(e);
  }
  return threadedFunc;
}

const isList = (v: Threadable): v is readonly Threadable[] => Array.isArray(v);
const isExprLike = (v: Threadable): v is ExprLike => typeof v !== 'object' || v instanceof Expr;

/** An item of a container, sympified (a nested container is not threaded). */
function item(v: Threadable): Expr {
  if (!isExprLike(v)) throw new TypeError('threaded: nested containers are not threaded');
  return sympify(v);
}

function expectExpr(v: unknown): Expr {
  if (!(v instanceof Expr)) throw new TypeError('threaded: the function must return an expression to rebuild a sum, a relation or a matrix');
  return v;
}

/**
 * SymPy `@threaded`: the function applied to the entries of a matrix, the
 * items of an array or set, the sides of a relation and the terms of a sum
 * (the sum and relation rebuilt), else to the expression itself.
 *
 * ```
 * const expandThreaded = threaded((e: Expr) => expand(e));
 * expandThreaded(Eq(pow(add(x, 1), 2), y)) // Eq(x**2 + 2*x + 1, y)
 * ```
 */
export function threaded<R, A extends unknown[]>(func: (expr: Expr, ...args: A) => R): ThreadedFunction<R, A> {
  return threadedFactory(func, true);
}

/**
 * SymPy `@xthreaded`: like {@link threaded}, but a sum is passed whole to the
 * function (not term by term).
 */
export function xthreaded<R, A extends unknown[]>(func: (expr: Expr, ...args: A) => R): ThreadedFunction<R, A> {
  return threadedFactory(func, false);
}

/**
 * SymPy `@memoize_property`: the getter of a property computed on its first
 * use for each object and then remembered (SymPy stores it in an attribute
 * `_name`).
 *
 * ```
 * const areaOf = memoizeProperty((s: Shape) => expensiveArea(s));
 * class Shape { get area() { return areaOf(this); } }
 * ```
 */
export function memoizeProperty<T extends object, V>(propfunc: (self: T) => V): (self: T) => V {
  const cache = new WeakMap<T, { readonly value: V }>();
  return (self: T): V => {
    const hit = cache.get(self);
    if (hit) return hit.value;
    const value = propfunc(self);
    cache.set(self, { value });
    return value;
  };
}

/** A function or a class (anything SymPy's `@public` accepts). */
export type PublicDefinition = ((...args: never[]) => unknown) | (abstract new (...args: never[]) => unknown);

/**
 * SymPy `@public`: appends the name of a function or a class to the list of
 * the public names of its module and returns it unchanged. SymPy appends to
 * the `__all__` of the module that defines it; a JavaScript module's exports
 * are static, so the list the name goes to is passed (`all`).
 *
 * Exported as `public` (a reserved word, which is valid as an export name):
 * `import { public as markPublic } from '@symjs/symjs/utilities'` or
 * `sj.public`.
 *
 * ```
 * const all: string[] = [];
 * const someFunction = markPublic(function someFunction() {}, all);
 * all; // ['someFunction']
 * ```
 */
export function markPublic<T extends PublicDefinition>(obj: T, all: string[]): T {
  // the type admits functions and classes only (SymPy raises TypeError for other objects)
  if (obj.name === '') throw new TypeError('public: an anonymous function or class has no name to make public');
  all.push(obj.name);
  return obj;
}
