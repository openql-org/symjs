// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/core.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.core: generic strategies, functions that
 * combine rules (`x -> x`) into new rules. They work on any values;
 * values compare like Python's `==` (expressions structurally).
 */

import { first } from '../core/guard';
import { ValueMap, compareValues, valueEquals } from '../utilities/values';

/** A rule: a function that transforms one value into another. */
export type Rule<T> = (x: T) => T;

/** Accepts diagnostic text from a rewriting strategy. */
export interface Writer {
  write(text: string): void;
}

/** Python's `sys.stdout`: the standard output of Node.js, or nothing where there is none. */
export function stdout(): Writer {
  const proc = (globalThis as { process?: { stdout?: Partial<Writer> } }).process;
  const write = proc?.stdout?.write;
  if (typeof write !== 'function') return { write: () => undefined };
  return { write: (text) => write.call(proc?.stdout, text) };
}

/** SymPy `identity(x)`: the rule that returns its input. */
export function identity<T>(x: T): T {
  return x;
}

/**
 * Applies a rule repeatedly until it has no effect.
 *
 * @param rule - The transformation to apply.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.exhaust`
 */
export function exhaust<T>(rule: Rule<T>): Rule<T> {
  return function exhaustiveRl(expr: T): T {
    let old = expr;
    let next = rule(expr);
    while (!valueEquals(next, old)) {
      old = next;
      next = rule(next);
    }
    return next;
  };
}

/**
 * Returns a rule that remembers its results (the cache is not bounded).
 *
 * @param rule - The transformation to apply.
 * @returns A rule that remembers its results (the cache is not bounded).
 * @see SymPy `sympy.strategies.core.memoize`
 */
export function memoize<S, T>(rule: (x: S) => T): (x: S) => T {
  const cache = new ValueMap<S, { value: T }>();
  return function memoizedRl(expr: S): T {
    const hit = cache.get(expr);
    if (hit) return hit.value;
    const value = rule(expr);
    cache.set(expr, { value });
    return value;
  };
}

/**
 * Builds a rule that applies a transformation only when the input satisfies a predicate.
 *
 * @param cond - The predicate controlling application of the rule.
 * @param rule - The transformation to apply.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.condition`
 */
export function condition<T>(cond: (x: T) => boolean, rule: Rule<T>): Rule<T> {
  return function conditionedRl(expr: T): T {
    return cond(expr) ? rule(expr) : expr;
  };
}

/**
 * Composes rules so that they apply to the input one after the other.
 *
 * @param rules - The rewrite rules in application order.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.chain`
 */
export function chain<T>(...rules: Rule<T>[]): Rule<T> {
  return function chainRl(expr: T): T {
    let e = expr;
    for (const rule of rules) e = rule(e);
    return e;
  };
}

/**
 * Writes the input and output each time the rule changes something.
 *
 * @param rule - The transformation to apply.
 * @param file - The writer receiving diagnostics for changes made by the rule.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.debug`
 */
export function debug<T>(rule: Rule<T>, file: Writer = stdout()): Rule<T> {
  return function debugRl(expr: T): T {
    const result = rule(expr);
    if (!valueEquals(result, expr)) {
      file.write(`Rule: ${rule.name}\n`);
      file.write(`In:   ${String(expr)}\nOut:  ${String(result)}\n\n`);
    }
    return result;
  };
}

/**
 * The original input when the rule returns
 * nothing (`None` in SymPy; `undefined` or `null` here).
 *
 * @param rule - The transformation to apply.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.null_safe`
 */
export function nullSafe<T>(rule: (x: T) => T | undefined | null): Rule<T> {
  return function nullSafeRl(expr: T): T {
    return rule(expr) ?? expr;
  };
}

/** Identifies the class of exceptions a strategy should catch. */
export type ErrorClass = abstract new (...args: never[]) => unknown;

/**
 * The original input when the rule throws an error of that class.
 *
 * @param rule - The transformation to apply.
 * @param exception - The class of errors for which the original input is returned.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.tryit`
 */
export function tryit<T>(rule: Rule<T>, exception: ErrorClass): Rule<T> {
  return function tryRl(expr: T): T {
    try {
      return rule(expr);
    } catch (err) {
      if (err instanceof exception) return expr;
      throw err;
    }
  };
}

/**
 * Tries each rule until one changes the input, then stop.
 *
 * @param rules - The rewrite rules in application order.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.do_one`
 */
export function doOne<T>(...rules: Rule<T>[]): Rule<T> {
  return function doOneRl(expr: T): T {
    for (const rl of rules) {
      const result = rl(expr);
      if (!valueEquals(result, expr)) return result;
    }
    return expr;
  };
}

/**
 * Selects a rule by the value of `key` on the
 * input (no rule for that value leaves the input unchanged). `ruledict` is a
 * `Map` (keys compare by value) or an object keyed by strings.
 *
 * @param key - The function or functions producing comparison or grouping keys.
 * @param ruledict - The rules indexed by the dispatch key.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.core.switch`
 */
function switchRule<S, K>(key: (x: S) => K, ruledict: ReadonlyMap<K, Rule<S>> | Readonly<Record<string, Rule<S>>>): Rule<S> {
  const rules = ruledict instanceof Map ? new ValueMap<unknown, Rule<S>>(ruledict) : new ValueMap<unknown, Rule<S>>(Object.entries(ruledict));
  return function switchRl(expr: S): S {
    const rl = rules.get(key(expr)) ?? identity;
    return rl(expr);
  };
}
export { switchRule as switch };

/**
 * The result of the rule that
 * minimizes the objective (the first such result on ties). Pass the
 * objective as `{ objective }` after the rules.
 *
 * @param rulesAndOpts - The rewrite rules followed by their optional settings.
 * @returns The result of the rule that minimizes the objective (the first such result on ties).
 * @see SymPy `sympy.strategies.core.minimize`
 * @example
 * ```ts
 * import { minimize } from '@symjs/symjs/strategies';
 * minimize(Math.floor, Math.ceil)(2.5); // => 2
 * ```
 */
export function minimize<S, T>(...rulesAndOpts: (((x: S) => T) | { readonly objective: (x: T) => unknown })[]): (x: S) => T {
  const rules: ((x: S) => T)[] = [];
  let objective: (x: T) => unknown = identity;
  for (const r of rulesAndOpts) {
    if (typeof r === 'function') rules.push(r);
    else objective = r.objective;
  }
  return function minrule(expr: S): T {
    return minBy(
      rules.map((rule) => rule(expr)),
      objective,
    );
  };
}

/** Python `min(xs, key=objective)`: the first element with the least objective (Python ordering). */
export function minBy<T>(xs: readonly T[], objective: (x: T) => unknown): T {
  if (!xs.length) throw new RangeError('min() arg is an empty sequence');
  let best = first(xs);
  let bestKey = objective(best);
  for (const r of xs.slice(1)) {
    const k = objective(r);
    if (compareValues(k, bestKey) < 0) {
      best = r;
      bestKey = k;
    }
  }
  return best;
}
