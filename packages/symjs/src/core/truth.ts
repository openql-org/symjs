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

/** The answer is known to be true. */
export const isTrue = (t: Truth): t is true => t === true;
/** The answer is known to be false. */
export const isFalse = (t: Truth): t is false => t === false;
/** The answer cannot be decided. */
export const isUnknown = (t: Truth): t is 'unknown' => t === 'unknown';

/** @internal A Truth from the base module's boolean | undefined. */
export const toTruth = (v: boolean | undefined | null): Truth => (v ?? 'unknown');

/** Negation (unknown stays unknown). */
export const truthNot = (t: Truth): Truth => (t === 'unknown' ? t : !t);
/** Conjunction: false if any is false, unknown if any is unknown, else true. */
export const truthAnd = (...ts: Truth[]): Truth => (ts.includes(false) ? false : ts.includes('unknown') ? 'unknown' : true);
/** Disjunction: true if any is true, unknown if any is unknown, else false. */
export const truthOr = (...ts: Truth[]): Truth => (ts.includes(true) ? true : ts.includes('unknown') ? 'unknown' : false);

/** The type of NoMatch. */
export class NoMatchResult {
  readonly kind = 'NoMatch' as const;
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
/** v is NoMatch. */
export const isNoMatch = (v: unknown): v is NoMatchResult => v === NoMatch;

/** The type of Unsolved. */
export class UnsolvedResult {
  readonly kind = 'Unsolved' as const;
  toString(): string {
    return 'Unsolved';
  }
}
/**
 * The available methods found no solution in closed form (SymPy returns
 * None); this is not a proof that no solution exists (that is EmptySet).
 */
export const Unsolved: UnsolvedResult = new UnsolvedResult();
/** v is Unsolved. */
export const isUnsolved = (v: unknown): v is UnsolvedResult => v === Unsolved;

/** @internal NoMatch for undefined. */
export const orNoMatch = <T>(v: T | undefined | null): T | NoMatchResult => (v ?? NoMatch);
/** @internal Unsolved for undefined. */
export const orUnsolved = <T>(v: T | undefined | null): T | UnsolvedResult => (v ?? Unsolved);
