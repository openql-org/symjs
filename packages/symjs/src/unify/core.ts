// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/unify/core.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.unify.core: a generic unification algorithm for
 * expression trees whose interior nodes ({@link Compound}) have lists of
 * children, after Russell and Norvig, Artificial Intelligence: A Modern
 * Approach (2nd ed., section 9.2), extended to associative and commutative
 * operators and explored lazily (the substitutions are generated).
 *
 * Terms are leaves (any values, compared like Python's `==`), arrays
 * (Python tuples and lists), {@link Compound}s and wild tokens
 * ({@link Variable}, {@link CondVariable}).
 */

import { at } from '../core/guard';
import { kbins } from '../utilities/iterables';
import { valueKey } from '../utilities/values';

/** A term of a unification problem. */
export type Term = unknown;

/** An object that gives its own identity for unification (an operator such as the class of a node). */
export interface UnifyKeyed {
  readonly unifyKey: string;
}

const isKeyed = (x: unknown): x is UnifyKeyed => typeof x === 'object' && x !== null && 'unifyKey' in x && typeof x.unifyKey === 'string';

/** A string equal for two terms exactly when they are equal (Python `hash` plus `==`). */
export function termKey(x: Term): string {
  if (x instanceof Compound) return `C${JSON.stringify([termKey(x.op), ...x.args.map(termKey)])}`;
  if (x instanceof CondVariable) return `W${JSON.stringify([termKey(x.arg), valueKey(x.valid)])}`;
  if (x instanceof Variable) return `V${termKey(x.arg)}`;
  if (Array.isArray(x)) return `[${JSON.stringify(x.map(termKey))}`;
  if (isKeyed(x)) return `K${x.unifyKey}`;
  return valueKey(x);
}

/** Python `a == b` for terms. */
export function termEquals(a: Term, b: Term): boolean {
  return a === b || termKey(a) === termKey(b);
}

/** SymPy `Compound(op, args)`: an interior node of a tree (like a non-atomic Basic). */
export class Compound {
  constructor(
    readonly op: Term,
    readonly args: readonly Term[],
  ) {}
  equals(other: Term): boolean {
    return termEquals(this, other);
  }
  toString(): string {
    return `${String(this.op)}[${this.args.map((a) => String(a)).join(', ')}]`;
  }
}

/** SymPy `Variable(arg)`: a wild token. */
export class Variable {
  constructor(readonly arg: Term) {}
  equals(other: Term): boolean {
    return termEquals(this, other);
  }
  toString(): string {
    return `Variable(${String(this.arg)})`;
  }
}

/** SymPy `CondVariable(arg, valid)`: a wild token that matches only the terms accepted by `valid`. */
export class CondVariable {
  constructor(
    readonly arg: Term,
    readonly valid: (x: Term) => boolean,
  ) {}
  equals(other: Term): boolean {
    return termEquals(this, other);
  }
  toString(): string {
    return `CondVariable(${String(this.arg)})`;
  }
}

/**
 * A substitution: a `Map` from wild tokens to terms whose keys compare like
 * terms ({@link termKey}).
 */
export class TermMap extends Map<Term, Term> {
  #byKey = new Map<string, Term>();

  constructor(entries?: Iterable<readonly [Term, Term]> | null) {
    super();
    if (entries) for (const [k, v] of entries) this.set(k, v);
  }

  override get(k: Term): Term {
    const tk = termKey(k);
    return this.#byKey.has(tk) ? super.get(this.#byKey.get(tk)) : undefined;
  }

  override has(k: Term): boolean {
    return this.#byKey.has(termKey(k));
  }

  override set(k: Term, v: Term): this {
    const tk = termKey(k);
    if (this.#byKey.has(tk)) return super.set(this.#byKey.get(tk), v);
    this.#byKey.set(tk, k);
    return super.set(k, v);
  }

  override delete(k: Term): boolean {
    const tk = termKey(k);
    if (!this.#byKey.has(tk)) return false;
    const c = this.#byKey.get(tk);
    this.#byKey.delete(tk);
    return super.delete(c);
  }

  override clear(): void {
    this.#byKey.clear();
    super.clear();
  }
}

/** The properties of the operators of a unification problem. */
export interface UnifyFns {
  /** Whether a term is an associative Compound (false by default). */
  readonly isAssociative?: (x: Term) => boolean;
  /** Whether a term is a commutative Compound (false by default). */
  readonly isCommutative?: (x: Term) => boolean;
}

const isWild = (x: Term): x is Variable | CondVariable => x instanceof Variable || x instanceof CondVariable;

/**
 * SymPy `unify(x, y, s=None, **fns)`: unify two terms. Yields the
 * substitutions (maps from wild tokens to subterms) that make `x` and `y`
 * equal, extending `s`.
 */
export function* unify(x: Term, y: Term, s: ReadonlyMap<Term, Term> | null = null, fns: UnifyFns = {}): Generator<TermMap, void, undefined> {
  const sub = s instanceof TermMap ? s : new TermMap(s);
  if (termEquals(x, y)) {
    yield sub;
  } else if (isWild(x)) {
    yield* unifyVar(x, y, sub, fns);
  } else if (isWild(y)) {
    yield* unifyVar(y, x, sub, fns);
  } else if (x instanceof Compound && y instanceof Compound) {
    const isCommutative = fns.isCommutative ?? (() => false);
    const isAssociative = fns.isAssociative ?? (() => false);
    for (const sop of unify(x.op, y.op, sub, fns)) {
      if (isAssociative(x) && isAssociative(y)) {
        const [a, b] = x.args.length < y.args.length ? [x, y] : [y, x];
        const combs = allcombinations(a.args, b.args, isCommutative(x) && isCommutative(y) ? 'commutative' : 'associative');
        for (const [aaargs, bbargs] of combs) {
          const aa = aaargs.map((arg) => unpack(new Compound(a.op, arg)));
          const bb = bbargs.map((arg) => unpack(new Compound(b.op, arg)));
          yield* unify(aa, bb, sop, fns);
        }
      } else if (x.args.length === y.args.length) {
        yield* unify(x.args, y.args, sop, fns);
      }
    }
  } else if (isArgs(x) && isArgs(y) && x.length === y.length) {
    // two empty sequences are equal (handled above), so these are not empty
    const [xh, ...xt] = x;
    const [yh, ...yt] = y;
    for (const shead of unify(xh, yh, sub, fns)) yield* unify(xt, yt, shead, fns);
  }
}

/** SymPy `unify_var(var, x, s, **fns)`: unify a wild token with a term. */
export function* unifyVar(v: Variable | CondVariable, x: Term, s: TermMap, fns: UnifyFns = {}): Generator<TermMap, void, undefined> {
  if (s.has(v)) yield* unify(s.get(v), x, s, fns);
  else if (occurCheck(v, x)) return;
  else if (v instanceof CondVariable ? v.valid(x) : true) yield assoc(s, v, x);
}

/** SymPy `occur_check(var, x)`: whether `var` occurs in the subtree owned by `x`. */
export function occurCheck(v: Term, x: Term): boolean {
  if (termEquals(v, x)) return true;
  if (x instanceof Compound) return occurCheck(v, x.args);
  if (isArgs(x)) return x.some((xi) => occurCheck(v, xi));
  return false;
}

/** SymPy `assoc(d, key, val)`: a copy of `d` with `key` associated to `val`. */
export function assoc(d: ReadonlyMap<Term, Term>, key: Term, val: Term): TermMap {
  const copy = new TermMap(d);
  copy.set(key, val);
  return copy;
}

/** SymPy `is_args(x)`: whether `x` is a sequence of terms (an array). */
export function isArgs(x: Term): x is readonly Term[] {
  return Array.isArray(x);
}

/** SymPy `unpack(x)`: the argument of a Compound with a single argument, else `x`. */
export function unpack(x: Term): Term {
  return x instanceof Compound && x.args.length === 1 ? x.args[0] : x;
}

/**
 * SymPy `allcombinations(A, B, ordered)`: the ways to restructure `A` and
 * `B` into the same number of pieces, the longer one split into consecutive
 * sublists (`'associative'`) or into sublists of any of its permutations
 * (`'commutative'`).
 */
export function* allcombinations<T>(A: readonly T[], B: readonly T[], ordered: 'commutative' | 'associative'): Generator<[T[][], T[][]], void, undefined> {
  const [sm, bg] = A.length < B.length ? [A, B] : [B, A];
  const indices = Array.from({ length: bg.length }, (_, i) => i);
  for (const part of kbins(indices, sm.length, ordered === 'commutative' ? 11 : null)) {
    if (termEquals(bg, B)) yield [A.map((a) => [a]), partition(B, part)];
    else yield [partition(A, part), B.map((b) => [b])];
  }
}

/** SymPy `partition(it, part)`: the pieces of `it` given by the lists of indices `part`. */
export function partition<T>(it: readonly T[], part: readonly (readonly number[])[]): T[][] {
  return part.map((ind) => index(it, ind));
}

/** SymPy `index(it, ind)`: the elements of `it` at the indices `ind`. */
export function index<T>(it: readonly T[], ind: readonly number[]): T[] {
  return ind.map((i) => at(it, i));
}
