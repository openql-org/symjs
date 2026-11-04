// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/branch/core.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.branch.core: generic branching strategies.
 * A branching rule maps a value to a lazy sequence of values (a generator
 * here, as in SymPy); values compare like Python's `==`.
 */

import { valueEquals, valueKey } from '../../utilities/values';
import type { Rule, Writer } from '../core';
import { stdout } from '../core';

/** A branching rule: a function from a value to the values it may become. */
export type BranchRule<T> = (x: T) => Iterable<T>;

/** SymPy `identity(x)`: the branching rule that yields its input. */
export function* identity<T>(x: T): Generator<T, void, undefined> {
  yield x;
}

/** SymPy `exhaust(brule)`: apply a branching rule repeatedly until it has no effect. */
export function exhaust<T>(brule: BranchRule<T>): BranchRule<T> {
  return function* exhaustBrl(expr: T): Generator<T, void, undefined> {
    const start = valueKey(expr);
    const seen = new Set([start]);
    for (const nexpr of brule(expr)) {
      const k = valueKey(nexpr);
      if (!seen.has(k)) {
        seen.add(k);
        yield* exhaustBrl(nexpr);
      }
    }
    if (seen.size === 1) yield expr;
  };
}

/** SymPy `onaction(brule, fn)`: call `fn(brule, expr, result)` for each result that differs from the input. */
export function onaction<T>(brule: BranchRule<T>, fn: (brule: BranchRule<T>, expr: T, result: T) => void): BranchRule<T> {
  return function* onactionBrl(expr: T): Generator<T, void, undefined> {
    for (const result of brule(expr)) {
      if (!valueEquals(result, expr)) fn(brule, expr, result);
      yield result;
    }
  };
}

/** SymPy `debug(brule, file=None)`: write the input and output expressions at each rule application. */
export function debug<T>(brule: BranchRule<T>, file: Writer = stdout()): BranchRule<T> {
  const write = (brl: BranchRule<T>, expr: T, result: T): void => {
    file.write(`Rule: ${brl.name}\n`);
    file.write(`In: ${String(expr)}\nOut: ${String(result)}\n\n`);
  };
  return onaction(brule, write);
}

/** SymPy `multiplex(*brules)`: multiplex many branching rules into one (each result once). */
export function multiplex<T>(...brules: BranchRule<T>[]): BranchRule<T> {
  return function* multiplexBrl(expr: T): Generator<T, void, undefined> {
    const seen = new Set<string>();
    for (const brl of brules) {
      for (const nexpr of brl(expr)) {
        const k = valueKey(nexpr);
        if (!seen.has(k)) {
          seen.add(k);
          yield nexpr;
        }
      }
    }
  };
}

/** SymPy `condition(cond, brule)`: only apply the branching rule if the condition is true. */
export function condition<T>(cond: (x: T) => boolean, brule: BranchRule<T>): BranchRule<T> {
  return function* conditionedBrl(expr: T): Generator<T, void, undefined> {
    if (cond(expr)) yield* brule(expr);
  };
}

/** SymPy `sfilter(pred, brule)`: yield only the results that satisfy the predicate. */
export function sfilter<T>(pred: (x: T) => boolean, brule: BranchRule<T>): BranchRule<T> {
  return function* filteredBrl(expr: T): Generator<T, void, undefined> {
    for (const x of brule(expr)) if (pred(x)) yield x;
  };
}

/** SymPy `notempty(brule)`: the input itself when the branching rule yields nothing. */
export function notempty<T>(brule: BranchRule<T>): BranchRule<T> {
  return function* notemptyBrl(expr: T): Generator<T, void, undefined> {
    let yielded = false;
    for (const nexpr of brule(expr)) {
      yielded = true;
      yield nexpr;
    }
    if (!yielded) yield expr;
  };
}

/** SymPy `do_one(*brules)`: the results of the first branching rule that yields any. */
export function doOne<T>(...brules: BranchRule<T>[]): BranchRule<T> {
  return function* doOneBrl(expr: T): Generator<T, void, undefined> {
    for (const brl of brules) {
      let yielded = false;
      for (const nexpr of brl(expr)) {
        yielded = true;
        yield nexpr;
      }
      if (yielded) return;
    }
  };
}

/** SymPy `chain(*brules)`: compose branching rules so that they apply one after the other. */
export function chain<T>(...brules: BranchRule<T>[]): BranchRule<T> {
  return function* chainBrl(expr: T): Generator<T, void, undefined> {
    const [head, ...tail] = brules;
    if (head === undefined) {
      yield expr;
      return;
    }
    for (const nexpr of head(expr)) yield* chain(...tail)(nexpr);
  };
}

/** SymPy `yieldify(rl)`: turn a rule into a branching rule. */
export function yieldify<T>(rl: Rule<T>): BranchRule<T> {
  return function* brl(expr: T): Generator<T, void, undefined> {
    yield rl(expr);
  };
}
