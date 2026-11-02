// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The public sympify: numbers to expressions, plus SymPy's hooks for
 * other objects (the _sympy_ method and the converter registry) and
 * containers converted element by element.
 */

import type { ExprLike } from './nodes';
import { Expr } from './nodes';
import { sympify as toExpr } from './ops';

/**
 * Key of the conversion method (SymPy _sympy_): an object with a method
 * under this key is converted by calling it.
 *
 * @example
 * class Pair { [sympifyMethod]() { return Matrix([[1], [2]]); } }
 *
 * @experimental May change in a minor release.
 */
export const sympifyMethod: unique symbol = Symbol.for('symjs.sympify') as never;

/** An object converted by its own method (SymPy _sympy_). *
 * @experimental May change in a minor release.
 */
export interface Sympifiable {
  [sympifyMethod](): unknown;
}

/**
 * Conversions for classes that cannot define the method themselves (SymPy
 * sympy.core.sympify.converter), looked up along the prototype chain.
 *
 * @experimental May change in a minor release.
 */
export const converter = new Map<Function, (x: never) => unknown>();

/**
 * SymPy sympify: an expression from a number or expression; objects
 * defining [sympifyMethod] or registered in `converter` are converted by
 * them, and arrays, Sets and Maps element by element.
 */
export function sympify(x: Sympifiable): unknown;
export function sympify<K, V>(x: ReadonlyMap<K, V>): Map<unknown, unknown>;
export function sympify<T>(x: ReadonlySet<T>): Set<unknown>;
export function sympify(x: readonly unknown[]): unknown[];
export function sympify(x: ExprLike): Expr;
export function sympify(x: unknown): unknown {
  if (x instanceof Expr || typeof x === 'number' || typeof x === 'bigint') return toExpr(x);
  if (x !== null && typeof x === 'object') {
    const own = (x as Partial<Sympifiable>)[sympifyMethod];
    if (typeof own === 'function') return own.call(x);
    for (let p = Object.getPrototypeOf(x); p; p = Object.getPrototypeOf(p)) {
      const conv = converter.get(p.constructor);
      if (conv) return conv(x as never);
    }
    const item = (v: unknown): unknown => (v instanceof Expr || typeof v === 'number' || typeof v === 'bigint' || (v !== null && typeof v === 'object') ? sympify(v as ExprLike) : v);
    if (Array.isArray(x)) return x.map(item);
    if (x instanceof Map) return new Map([...x].map(([k, v]) => [item(k), item(v)]));
    if (x instanceof Set) return new Set([...x].map(item));
  }
  return toExpr(x as ExprLike);
}
