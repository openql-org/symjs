// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Result types of the public computation API (docs/api-policy.md):
 * results are never undefined or null. Three-valued answers are Truth,
 * an expression without the requested form is NoMatch, an equation the
 * methods cannot solve is Unsolved.
 */

/**
 * A three-valued answer (SymPy's True / False / None): 'unknown' when it
 * cannot be decided. 'unknown' is truthy, so test with isTrue/isFalse (the
 * lint rule strict-boolean-expressions rejects `if (truth)`).
 */
export type Truth = boolean | 'unknown';

/**
 * The answer is known to be true.
 *
 * @param t - The truth value to inspect.
 * @returns True only for a known true answer.
 */
export const isTrue = (t: Truth): t is true => t === true;
/**
 * The answer is known to be false.
 *
 * @param t - The truth value to inspect.
 * @returns True only for a known false answer.
 */
export const isFalse = (t: Truth): t is false => t === false;
/**
 * The answer cannot be decided.
 *
 * @param t - The truth value to inspect.
 * @returns True only for an undecidable answer.
 */
export const isUnknown = (t: Truth): t is 'unknown' => t === 'unknown';

/** @internal A Truth from the base module's boolean | undefined. */
export const toTruth = (v: boolean | undefined | null): Truth => (v ?? 'unknown');

/**
 * Negation (unknown stays unknown).
 *
 * @param t - The truth value to inspect.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 */
export const truthNot = (t: Truth): Truth => (t === 'unknown' ? t : !t);
/**
 * Conjunction: false if any is false, unknown if any is unknown, else true.
 *
 * @param ts - The truth values to combine.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 */
export const truthAnd = (...ts: Truth[]): Truth => (ts.includes(false) ? false : ts.includes('unknown') ? 'unknown' : true);
/**
 * Disjunction: true if any is true, unknown if any is unknown, else false.
 *
 * @param ts - The truth values to combine.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 */
export const truthOr = (...ts: Truth[]): Truth => (ts.includes(true) ? true : ts.includes('unknown') ? 'unknown' : false);

/**
 * A fuzzy truth value as SymPy's fuzzy functions take it: a Truth, or null
 * or undefined for SymPy's None (an answer that is not known).
 */
export type FuzzyLike = Truth | null | undefined;

/**
 * True or false for a boolean (or the numbers 1 and
 * 0, which equal Python's True and False), 'unknown' for anything else.
 *
 * @param x - The argument of the function.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.logic.fuzzy_bool`
 * @example
 * ```ts
 * import { fuzzyBool } from '@symjs/symjs';
 *
 * fuzzyBool(true); // => True
 * ```
 */
export function fuzzyBool(x: unknown): Truth {
  if (x === true || x === 1) return true;
  if (x === false || x === 0) return false;
  return 'unknown';
}

/**
 * False if any value is false, else 'unknown' if
 * any is not known, else true (also for no values).
 *
 * @param args - The truth values to combine.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.logic.fuzzy_and`
 * @example
 * ```ts
 * import { fuzzyAnd } from '@symjs/symjs';
 *
 * fuzzyAnd([false, true]); // => False
 * ```
 */
export function fuzzyAnd(args: Iterable<unknown>): Truth {
  let rv: Truth = true;
  for (const a of args) {
    const v = fuzzyBool(a);
    if (v === false) return false;
    if (rv === true) rv = v;
  }
  return rv;
}

/**
 * True if any value is true, else 'unknown' if any
 * is not known, else false (also for no values).
 *
 * @param args - The truth values to combine.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.logic.fuzzy_or`
 * @example
 * ```ts
 * import { fuzzyOr } from '@symjs/symjs';
 *
 * fuzzyOr([true, false]); // => True
 * fuzzyOr([false, false]); // => False
 * ```
 */
export function fuzzyOr(args: Iterable<unknown>): Truth {
  let rv: Truth = false;
  for (const a of args) {
    const v = fuzzyBool(a);
    if (v === true) return true;
    if (rv === false) rv = v;
  }
  return rv;
}

/**
 * The negation, 'unknown' for a value that is not known.
 *
 * @param v - The truth value to inspect.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.logic.fuzzy_not`
 * @example
 * ```ts
 * import { fuzzyNot } from '@symjs/symjs';
 *
 * fuzzyNot(true); // => False
 * fuzzyNot(false); // => True
 * ```
 */
export function fuzzyNot(v: FuzzyLike): Truth {
  return v === null || v === undefined || v === 'unknown' ? 'unknown' : !v;
}

/**
 * Whether an odd number of the values is true;
 * 'unknown' when a value is not known.
 *
 * @param args - The truth values to combine.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.logic.fuzzy_xor`
 */
export function fuzzyXor(args: Iterable<unknown>): Truth {
  let t = 0;
  for (const a of args) {
    const v = fuzzyBool(a);
    if (v === 'unknown') return v;
    if (v) t++;
  }
  return t % 2 === 1;
}

/**
 * The negation of {@link fuzzyAnd}.
 *
 * @param args - The truth values to combine.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.logic.fuzzy_nand`
 */
export const fuzzyNand = (args: Iterable<unknown>): Truth => fuzzyNot(fuzzyAnd(args));

/** The type of NoMatch. */
export class NoMatchResult {
  /** The node's discriminant. */
  readonly kind = 'NoMatch' as const;
  /**
   * Formats the object as a string.
   *
   * @returns The formatted string.
   */
  toString(): string {
    return 'NoMatch';
  }
}
/**
 * The expression does not have the requested form: a pattern that does
 * not match, a term that cannot be extracted, a function that is not
 * hypergeometric, homogeneous or periodic (SymPy returns None).
 */
export const NoMatch: NoMatchResult = new NoMatchResult();
/**
 * Tests whether the value is the `NoMatch` singleton.
 *
 * @param v - The value to examine.
 * @returns Whether the value is the `NoMatch` singleton.
 */
export const isNoMatch = (v: unknown): v is NoMatchResult => v === NoMatch;

/** The type of Unsolved. */
export class UnsolvedResult {
  /** The node's discriminant. */
  readonly kind = 'Unsolved' as const;
  /**
   * Formats the object as a string.
   *
   * @returns The formatted string.
   */
  toString(): string {
    return 'Unsolved';
  }
}
/**
 * The available methods found no solution in closed form (SymPy returns
 * None); this is not a proof that no solution exists (that is EmptySet).
 */
export const Unsolved: UnsolvedResult = new UnsolvedResult();
/**
 * Tests whether the value is the `Unsolved` singleton.
 *
 * @param v - The value to examine.
 * @returns Whether the value is the `Unsolved` singleton.
 */
export const isUnsolved = (v: unknown): v is UnsolvedResult => v === Unsolved;

/** @internal NoMatch for undefined. */
export const orNoMatch = <T>(v: T | undefined | null): T | NoMatchResult => (v ?? NoMatch);
/** @internal Unsolved for undefined. */
export const orUnsolved = <T>(v: T | undefined | null): T | UnsolvedResult => (v ?? Unsolved);
