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

/**
 * Yields the input once.
 *
 * @see SymPy `sympy.strategies.branch.core.identity`
 */
export function* identity<T>(x: T): Generator<T, void, undefined> {
  yield x;
}

/**
 * Builds a branching rule that repeatedly applies the given rule and yields each branch's result
 * when no further change is possible.
 *
 * @see SymPy `sympy.strategies.branch.core.exhaust`
 */
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

/**
 * Wraps a branching rule to call `fn(brule, expr, result)` for each result that differs from its
 * input.
 *
 * @see SymPy `sympy.strategies.branch.core.onaction`
 */
export function onaction<T>(brule: BranchRule<T>, fn: (brule: BranchRule<T>, expr: T, result: T) => void): BranchRule<T> {
  return function* onactionBrl(expr: T): Generator<T, void, undefined> {
    for (const result of brule(expr)) {
      if (!valueEquals(result, expr)) fn(brule, expr, result);
      yield result;
    }
  };
}

/**
 * Wraps a branching rule to write the rule name, input, and result whenever the rule changes an
 * expression.
 *
 * @see SymPy `sympy.strategies.branch.core.debug`
 */
export function debug<T>(brule: BranchRule<T>, file: Writer = stdout()): BranchRule<T> {
  const write = (brl: BranchRule<T>, expr: T, result: T): void => {
    file.write(`Rule: ${brl.name}\n`);
    file.write(`In: ${String(expr)}\nOut: ${String(result)}\n\n`);
  };
  return onaction(brule, write);
}

/**
 * Combines branching rules into one rule that yields each distinct result once.
 *
 * @see SymPy `sympy.strategies.branch.core.multiplex`
 */
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

/**
 * Builds a branching rule that applies the given rule only to inputs satisfying the condition.
 *
 * @see SymPy `sympy.strategies.branch.core.condition`
 */
export function condition<T>(cond: (x: T) => boolean, brule: BranchRule<T>): BranchRule<T> {
  return function* conditionedBrl(expr: T): Generator<T, void, undefined> {
    if (cond(expr)) yield* brule(expr);
  };
}

/**
 * Filters the results of a branching rule through a predicate.
 *
 * @see SymPy `sympy.strategies.branch.core.sfilter`
 */
export function sfilter<T>(pred: (x: T) => boolean, brule: BranchRule<T>): BranchRule<T> {
  return function* filteredBrl(expr: T): Generator<T, void, undefined> {
    for (const x of brule(expr)) if (pred(x)) yield x;
  };
}

/**
 * Wraps a branching rule to yield its input when the rule produces no results.
 *
 * @see SymPy `sympy.strategies.branch.core.notempty`
 */
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

/**
 * Builds a rule that yields all results of the first branching rule that produces any.
 *
 * @see SymPy `sympy.strategies.branch.core.do_one`
 */
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

/**
 * Composes branching rules in order, passing each result of one rule to the next.
 *
 * @see SymPy `sympy.strategies.branch.core.chain`
 */
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

/**
 * Converts a rule into a branching rule that yields its result once.
 *
 * @see SymPy `sympy.strategies.branch.core.yieldify`
 */
export function yieldify<T>(rl: Rule<T>): BranchRule<T> {
  return function* brl(expr: T): Generator<T, void, undefined> {
    yield rl(expr);
  };
}
