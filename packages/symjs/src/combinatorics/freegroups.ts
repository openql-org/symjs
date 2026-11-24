// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/combinatorics/free_groups.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.combinatorics.free_groups: free groups on a set of
 * symbols and their elements, the associative words (reduced words given by
 * their syllables, generator-exponent pairs).
 */

import { at } from '../core/guard';
import type { Expr } from '../core/nodes';
import { S, Sym } from '../core/nodes';
import { expandSymbolNames } from '../core/numberutils';
import { mul } from '../core/ops';

/** A syllable: the index of a generator and a nonzero exponent. */
type Syllable = readonly [number, number];

/** The symbols a free group is built from: a comma or space separated string, a symbol, or a list of either. */
export type FreeGroupSymbols = string | Expr | readonly (string | Expr)[];

const isSymbolList = (s: FreeGroupSymbols): s is readonly (string | Expr)[] => Array.isArray(s);

function parseSymbols(symbols: FreeGroupSymbols): Expr[] {
  if (typeof symbols === 'string') return symbols === '' ? [] : expandSymbolNames(symbols).map((n) => new Sym(n));
  if (!isSymbolList(symbols)) return [symbols];
  const names = symbols.filter((s): s is string => typeof s === 'string');
  if (names.length === symbols.length) return names.flatMap((s) => expandSymbolNames(s).map((n) => new Sym(n)));
  const exprs = symbols.filter((s): s is Expr => typeof s !== 'string');
  if (exprs.length === symbols.length) return exprs;
  throw new RangeError('The type of `symbols` must be one of the following: a str, Symbol/Expr or a sequence of one of these types');
}

const cache = new Map<string, FreeGroup>();

/** Python's slice letters[start:end] (negative bounds count from the end). */
function pySlice<T>(a: readonly T[], start: number, end: number): T[] {
  const n = a.length;
  const norm = (i: number): number => (i < 0 ? Math.max(n + i, 0) : Math.min(i, n));
  return a.slice(norm(start), norm(end));
}

/** Join two syllable lists, merging (and cancelling) at the junction (SymPy zero_mul_simp). */
function joinSyllables(left: readonly Syllable[], right: readonly Syllable[]): Syllable[] {
  const l: Syllable[] = [...left, ...right];
  let index = left.length - 1;
  while (index >= 0 && index < l.length - 1 && at(l, index)[0] === at(l, index + 1)[0]) {
    const e = at(l, index)[1] + at(l, index + 1)[1];
    l.splice(index, 2, [at(l, index)[0], e]);
    if (e === 0) {
      l.splice(index, 1);
      index--;
    }
  }
  return l;
}

/** The syllables of a word given letter by letter (+(i+1) for generator i, -(i+1) for its inverse). */
function lettersToSyllables(letters: readonly number[]): Syllable[] {
  const out: Syllable[] = [];
  for (const c of letters) {
    const g = Math.abs(c) - 1;
    const e = Math.sign(c);
    const last = out[out.length - 1];
    if (last?.[0] === g && Math.sign(last[1]) === e) out[out.length - 1] = [g, last[1] + e];
    else out.push([g, e]);
  }
  return out;
}

/**
 * The free group on the given symbols. Like
 * SymPy, groups on the same symbols are the same object.
 * @see SymPy `sympy.combinatorics.free_groups.FreeGroup`
 * @example
 * ```ts
 * import { freeGroup } from '@symjs/symjs';
 *
 * const [F, x, y] = freeGroup('x, y');
 * String(x.pow(2).mul(y.inverse())); // => x**2*y**-1
 * ```
 */
export class FreeGroup {
  /**
   * Indicates that the group operation is associative.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.is_associative`
   */
  readonly isAssociative = true;
  /**
   * Indicates whether the object represents a group.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.is_group`
   */
  readonly isGroup = true;
  /**
   * Indicates whether the group is free.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.is_FreeGroup`
   */
  readonly isFreeGroup = true;
  /**
   * Indicates whether the group acts by permutations.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.is_PermutationGroup`
   */
  readonly isPermutationGroup = false;
  /**
   * A free group has none.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.relators`
   */
  readonly relators: readonly FreeGroupElement[] = [];
  /** The symbols naming the free generators. */
  readonly symbols!: readonly Expr[];
  /**
   * The generators in their defining order.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup._generators`
   */
  readonly generators!: readonly FreeGroupElement[];
  /** The symbol keys, for the index of a symbol. @internal */
  readonly symbolIndex!: ReadonlyMap<string, number>;
  readonly #identity!: FreeGroupElement;

  /**
   * Constructs a `FreeGroup`.
   * @param symbols - The names or symbols of the free generators.
   */
  constructor(symbols: FreeGroupSymbols = []) {
    const syms = parseSymbols(symbols);
    const key = syms.map((s) => s.key).join('\u0000');
    const cached = cache.get(key);
    // SymPy caches the groups: FreeGroup('x, y') is FreeGroup('x, y')
    if (cached) return cached;
    this.symbols = syms;
    this.symbolIndex = new Map(syms.map((s, i) => [s.key, i]));
    this.#identity = new FreeGroupElement(this, []);
    this.generators = syms.map((_s, i) => new FreeGroupElement(this, [[i, 1]]));
    cache.set(key, this);
  }

  /**
   * The element with these (symbol, exponent) syllables.
   * @param arrayForm - The image of each point in order.
   * @returns The resulting group word.
   * @throws RangeError when the element is not one of the generators.
   */
  dtype(arrayForm: readonly (readonly [Expr, number | bigint])[] = []): FreeGroupElement {
    const syllables: Syllable[] = [];
    for (const [s, e] of arrayForm) {
      const i = this.symbolIndex.get(s.key);
      if (i === undefined) throw new RangeError(`${String(s)} is not a generator of ${String(this)}`);
      if (Number(e) !== 0) syllables.push([i, Number(e)]);
    }
    return new FreeGroupElement(this, lettersToSyllables(syllables.flatMap(([g, e]) => Array<number>(Math.abs(e)).fill(Math.sign(e) * (g + 1)))));
  }

  /**
   * Returns the free group on other symbols (or the same ones).
   * @param symbols - The names or symbols of the free generators.
   * @returns The free group on other symbols (or the same ones).
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.clone`
   */
  clone(symbols?: FreeGroupSymbols): FreeGroup {
    const empty = symbols === undefined || symbols === '' || (isSymbolList(symbols) && symbols.length === 0);
    return new FreeGroup(empty ? this.symbols : symbols);
  }

  /**
   * Gets the rank.
   * @returns The rank.
   */
  get length(): number {
    return this.rank;
  }

  /**
   * Returns the free group on the ith symbol.
   * @param i - The zero-based position in the sequence.
   * @returns The free group on the ith symbol.
   */
  getItem(i: number): FreeGroup {
    return this.clone([at(this.symbols, i < 0 ? this.symbols.length + i : i)]);
  }

  /**
   * Returns the free group on a slice of the symbols.
   * @param start - The starting position, inclusive.
   * @param end - The stopping position, exclusive.
   * @returns The free group on a slice of the symbols.
   */
  slice(start: number, end: number = this.symbols.length): FreeGroup {
    return this.clone(pySlice(this.symbols, start, end));
  }

  /**
   * Returns the position of a generator.
   * @param gen - The generator to locate or count.
   * @returns The position of a generator.
   * @throws RangeError when the element is not one of the generators.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.index`
   */
  index(gen: FreeGroupElement): number {
    const i = this.generators.findIndex((g) => g.equals(gen));
    if (gen.group !== this || i < 0) throw new RangeError(`expected a generator of Free Group ${String(this)}, got ${String(gen)}`);
    return i;
  }

  /**
   * Computes the cardinality of the free group.
   * @returns The cardinality of the free group.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.order`
   */
  order(): Expr {
    return this.rank === 0 ? S.One : S.Infinity;
  }

  /**
   * Gets the elements of the trivial group (other free groups are infinite).
   * @returns The elements of the trivial group (other free groups are infinite).
   * @throws RangeError when the group is infinite.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.elements`
   */
  get elements(): Set<FreeGroupElement> {
    if (this.rank === 0) return new Set([this.identity]);
    throw new RangeError('Group contains infinitely many elements, hence cannot be represented');
  }

  /**
   * Gets the number of generators.
   * @returns The number of generators.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.rank`
   */
  get rank(): number {
    return this.symbols.length;
  }

  /**
   * Only the free groups of rank 0 and 1.
   * @returns Whether the object is abelian.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.is_abelian`
   */
  get isAbelian(): boolean {
    return this.rank <= 1;
  }

  /**
   * Gets the empty word.
   * @returns The empty word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.identity`
   */
  get identity(): FreeGroupElement {
    return this.#identity;
  }

  /**
   * Whether g is an element of this group.
   * @param g - The element to test for membership.
   * @returns Whether the argument is an element of this free group.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.contains`
   */
  contains(g: unknown): boolean {
    return g instanceof FreeGroupElement && g.group === this;
  }

  /**
   * Returns the identity only.
   * @returns The identity only.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroup.center`
   */
  center(): Set<FreeGroupElement> {
    return new Set([this.identity]);
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    if (this.rank > 30) return `<free group with ${this.rank} generators>`;
    return `<free group on the generators ${tupleStr(this.generators)}>`;
  }
}

/** Python's str of a tuple of words. */
export const tupleStr = (items: readonly unknown[]): string => (items.length === 1 ? `(${String(items[0])},)` : `(${items.map(String).join(', ')})`);

/** Elements without repeats (Python set semantics, first occurrence kept). */
export function uniqueWords(words: Iterable<FreeGroupElement>): FreeGroupElement[] {
  const seen = new Map<string, FreeGroupElement>();
  for (const w of words) if (!seen.has(w.key)) seen.set(w.key, w);
  return [...seen.values()];
}

const isWordMap = (w: Iterable<FreeGroupElement> | ReadonlyMap<FreeGroupElement, FreeGroupElement>): w is ReadonlyMap<FreeGroupElement, FreeGroupElement> => w instanceof Map;

/**
 * An element of a free group, a reduced associative
 * word. Elements are immutable and compared by value (`equals`, `key`).
 * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement`
 */
export class FreeGroupElement {
  /**
   * Identifies a word in associative generators.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.is_assoc_word`
   */
  readonly isAssocWord = true;
  /** The group to which the words belong. */
  readonly group: FreeGroup;
  /** The syllables as (generator index, exponent). @internal */
  readonly syllables: readonly Syllable[];
  #letters: number[] | undefined;
  #key: string | undefined;

  /**
   * Constructs a `FreeGroupElement`.
   * @param group - The ambient group.
   * @param syllables - The generators and their exponents in word order.
   * @internal
   */
  constructor(group: FreeGroup, syllables: readonly Syllable[]) {
    this.group = group;
    this.syllables = syllables;
  }

  /**
   * Gets a string identifying the word within its group.
   * @returns A string identifying the word within its group.
   */
  get key(): string {
    return (this.#key ??= this.syllables.map(([g, e]) => `${g}^${e}`).join(' '));
  }

  /**
   * Gets the letters, +(i+1) for generator i and -(i+1) for its inverse.
   * @returns The letters, +(i+1) for generator i and -(i+1) for its inverse.
   * @internal
   */
  get letters(): readonly number[] {
    return (this.#letters ??= this.syllables.flatMap(([g, e]) => Array<number>(Math.abs(e)).fill(Math.sign(e) * (g + 1))));
  }

  /**
   * The word with these letters.
   * @param letters - The signed letters in word order.
   * @returns The resulting group word.
   * @internal
   */
  fromLetters(letters: readonly number[]): FreeGroupElement {
    return new FreeGroupElement(this.group, lettersToSyllables(letters));
  }

  #new(syllables: readonly Syllable[]): FreeGroupElement {
    return new FreeGroupElement(this.group, syllables);
  }

  #sym(g: number): Expr {
    return at(this.group.symbols, g);
  }

  /**
   * Constructs an element of the same free group from a sequence of syllables.
   * @param init - The initial terms, starting at index zero.
   * @returns An element of the same free group from a sequence of syllables.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.new`
   */
  new(init: readonly (readonly [Expr, number | bigint])[]): FreeGroupElement {
    return this.group.dtype(init);
  }

  /**
   * Creates a copy of this object.
   * @returns A copy of this object.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.copy`
   */
  copy(): FreeGroupElement {
    return this.#new(this.syllables);
  }

  /**
   * Tests whether the reduced word is empty.
   * @returns Whether the object is identity.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.is_identity`
   */
  get isIdentity(): boolean {
    return this.syllables.length === 0;
  }

  /**
   * Gets the (symbol, exponent) syllables.
   * @returns The (symbol, exponent) syllables.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.array_form`
   */
  get arrayForm(): [Expr, number][] {
    return this.syllables.map(([g, e]) => [this.#sym(g), e]);
  }

  /**
   * Gets the word letter by letter, an inverse letter as -symbol.
   * @returns The word letter by letter, an inverse letter as -symbol.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.letter_form`
   */
  get letterForm(): Expr[] {
    return this.letters.map((c) => (c > 0 ? this.#sym(c - 1) : mul(-1, this.#sym(-c - 1))));
  }

  /**
   * The ith letter as an element (negative i counts from the end).
   * @param i - The zero-based position in the sequence.
   * @returns The resulting group word.
   * @throws RangeError when an index is out of bounds.
   */
  getItem(i: number): FreeGroupElement {
    const ls = this.letters;
    const c = ls[i < 0 ? ls.length + i : i];
    if (c === undefined) throw new RangeError('tuple index out of range');
    return this.#new([[Math.abs(c) - 1, Math.sign(c)]]);
  }

  /**
   * Returns the position of the first occurrence of a letter.
   * @param gen - The generator to locate or count.
   * @returns The position of the first occurrence of a letter.
   * @throws RangeError when the element does not occur in the sequence.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.index`
   */
  index(gen: FreeGroupElement): number {
    if (gen.length !== 1) throw new RangeError('');
    const i = this.letters.indexOf(at(gen.letters, 0));
    if (i < 0) throw new RangeError('tuple.index(x): x not in tuple');
    return i;
  }

  /**
   * Gets the letters as elements.
   * @returns The letters as elements.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.letter_form_elm`
   */
  get letterFormElm(): FreeGroupElement[] {
    return this.letters.map((c) => this.#new([[Math.abs(c) - 1, Math.sign(c)]]));
  }

  /**
   * Gets the flattened array form.
   * @returns The flattened array form.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.ext_rep`
   */
  get extRep(): (Expr | number)[] {
    return this.syllables.flatMap(([g, e]) => [this.#sym(g), e]);
  }

  /**
   * Whether the generator of gen occurs in this word.
   * @param gen - The generator to locate or count.
   * @returns Whether the specified generator occurs with either sign.
   */
  has(gen: FreeGroupElement): boolean {
    const g = at(gen.syllables, 0)[0];
    return this.syllables.some((s) => s[0] === g);
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    if (this.isIdentity) return '<identity>';
    return this.syllables.map(([g, e]) => (e === 1 ? String(this.#sym(g)) : `${String(this.#sym(g))}**${e}`)).join('*');
  }

  /**
   * Raises this element to a power.
   * @param nIn - The integer exponent.
   * @returns The resulting group word.
   * @throws RangeError when the argument is not integral.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.__pow__`
   */
  pow(nIn: number | bigint | Expr): FreeGroupElement {
    let n = Number(typeof nIn === 'object' ? nIn.toString() : nIn);
    if (!Number.isInteger(n)) throw new RangeError(`${String(nIn)} is not an integer`);
    if (n === 0) return this.group.identity;
    if (n === 1) return this;
    if (n === -1) return this.inverse();
    let x: FreeGroupElement = this;
    if (n < 0) {
      n = -n;
      x = this.inverse();
    }
    // a single syllable is raised directly; SymPy's repeated squaring gives the same reduced word
    if (x.syllables.length === 1) {
      const [g, e] = at(x.syllables, 0);
      return this.#new([[g, e * n]]);
    }
    let result = this.group.identity;
    for (;;) {
      if (n % 2) result = result.mul(x);
      n = Math.floor(n / 2);
      if (!n) break;
      x = x.mul(x);
    }
    return result;
  }

  #check(other: unknown, what: string): FreeGroupElement {
    if (!(other instanceof FreeGroupElement) || other.group !== this.group) throw new TypeError(`only FreeGroup elements of same FreeGroup can be ${what}`);
    return other;
  }

  /**
   * Multiplies two words and cancels adjacent inverse letters.
   * @param other - The value to combine with or compare against.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.__mul__`
   */
  mul(other: FreeGroupElement): FreeGroupElement {
    const o = this.#check(other, 'multiplied');
    if (this.isIdentity) return o;
    if (o.isIdentity) return this;
    return this.#new(joinSyllables(this.syllables, o.syllables));
  }

  /**
   * Divides this element by the other operand.
   * @param other - The value to combine with or compare against.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.__truediv__`
   */
  div(other: FreeGroupElement): FreeGroupElement {
    return this.mul(this.#check(other, 'multiplied').inverse());
  }

  /**
   * Reverses the word and inverts each letter.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.inverse`
   */
  inverse(): FreeGroupElement {
    return this.#new([...this.syllables].reverse().map(([g, e]) => [g, -e]));
  }

  /**
   * Computes the order of this word in the free group.
   * @returns The order of this word in the free group.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.order`
   */
  order(): Expr {
    return this.isIdentity ? S.One : S.Infinity;
  }

  /**
   * Forms the commutator of this word with the other word.
   * @param other - The value to combine with or compare against.
   * @returns The commutator of this word with the other word.
   * @throws RangeError when the words belong to different free groups.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.commutator`
   */
  commutator(other: FreeGroupElement): FreeGroupElement {
    if (!(other instanceof FreeGroupElement) || other.group !== this.group) throw new RangeError('commutator of only FreeGroupElement of the same FreeGroup exists');
    return this.inverse().mul(other.inverse()).mul(this).mul(other);
  }

  /**
   * Replace each word of a list
   * by the identity, or each key of a Map by its value, until nothing changes.
   * @param words - The words to eliminate and their replacements.
   * @param all - Whether to repeat the replacement at all occurrences.
   * @param inverse - Whether to match the inverse word as well.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.eliminate_words`
   */
  eliminateWords(words: Iterable<FreeGroupElement> | ReadonlyMap<FreeGroupElement, FreeGroupElement>, all = false, inverse = true): FreeGroupElement {
    const pairs: [FreeGroupElement, FreeGroupElement | undefined][] = isWordMap(words) ? [...words] : [...words].map((w) => [w, undefined]);
    let again = true;
    let w: FreeGroupElement = this;
    while (again) {
      again = false;
      for (const [sub, by] of pairs) {
        const prev = w;
        w = w.eliminateWord(sub, by, all, inverse);
        if (!w.equals(prev)) again = true;
      }
    }
    return w;
  }

  /**
   * Replace the first
   * occurrence of gen (or of its inverse) by `by` (default the identity), or
   * every occurrence with `all`.
   * @param gen - The generator to locate or count.
   * @param byIn - The replacement word.
   * @param allIn - Whether to repeat the replacement at all occurrences.
   * @param inverse - Whether to match the inverse word as well.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.eliminate_word`
   */
  eliminateWord(gen: FreeGroupElement, byIn?: FreeGroupElement, allIn = false, inverse = true): FreeGroupElement {
    // SymPy recurses once per occurrence (and once per pass with _all); the same steps as loops
    const by = byIn ?? this.group.identity;
    let all = allIn;
    let w: FreeGroupElement = this;
    for (;;) {
      if (w.isIndependent(gen) || gen.equals(by)) return w;
      if (gen.equals(w)) return by;
      if (gen.inverse().equals(by)) all = false;
      let i = w.#find(gen.letters);
      let k = 1;
      if (i < 0) {
        if (!inverse) return w;
        // gen or its inverse occurs (the word is not independent of gen)
        i = w.#find(gen.inverse().letters);
        k = -1;
      }
      w = w.subword(0, i).mul(by.pow(k)).mul(w.subword(i + gen.length, w.length).#eliminateEach(gen, by));
      if (!all) return w;
    }
  }

  /** SymPy eliminate_word(gen, by) with the defaults: each occurrence of gen, or else of its inverse, from the left. */
  #eliminateEach(gen: FreeGroupElement, by: FreeGroupElement): FreeGroupElement {
    let result = this.group.identity;
    let w: FreeGroupElement = this;
    for (;;) {
      if (w.isIndependent(gen) || gen.equals(by)) return result.mul(w);
      if (gen.equals(w)) return result.mul(by);
      let i = w.#find(gen.letters);
      let k = 1;
      if (i < 0) {
        i = w.#find(gen.inverse().letters);
        k = -1;
      }
      result = result.mul(w.subword(0, i)).mul(by.pow(k));
      w = w.subword(i + gen.length, w.length);
    }
  }

  /**
   * Gets the number of letters.
   * @returns The number of letters.
   */
  get length(): number {
    return this.syllables.reduce((s, [, e]) => s + Math.abs(e), 0);
  }

  /**
   * The same word of the same group.
   * @param other - The value to combine with or compare against.
   * @returns The result of the comparison.
   */
  equals(other: unknown): boolean {
    return other instanceof FreeGroupElement && other.group === this.group && other.key === this.key;
  }

  /**
   * Shorter words first, then letter by letter (generator order, inverses first).
   * @param other - The value to combine with or compare against.
   * @returns The result of the comparison.
   */
  lt(other: FreeGroupElement): boolean {
    const o = this.#check(other, 'compared');
    const l = this.length;
    const m = o.length;
    if (l !== m) return l < m;
    const a = this.letters;
    const b = o.letters;
    for (let i = 0; i < l; i++) {
      const p = Math.abs(at(a, i));
      const q = Math.abs(at(b, i));
      if (p !== q) return p < q;
      if (at(a, i) !== at(b, i)) return at(a, i) < at(b, i);
    }
    return false;
  }

  /**
   * Compares the operands in nondecreasing order.
   * @param other - The value to combine with or compare against.
   * @returns The result of the comparison.
   */
  le(other: FreeGroupElement): boolean {
    return this.equals(other) || this.lt(other);
  }

  /**
   * Tests whether this operand follows the other.
   * @param other - The value to combine with or compare against.
   * @returns The result of the comparison.
   */
  gt(other: FreeGroupElement): boolean {
    this.#check(other, 'compared');
    return !this.le(other);
  }

  /**
   * Compares the operands in nonincreasing order.
   * @param other - The value to combine with or compare against.
   * @returns The result of the comparison.
   */
  ge(other: FreeGroupElement): boolean {
    return !this.lt(other);
  }

  /**
   * Compares two reduced words in the group’s ordering.
   * @param a - The first operand.
   * @param b - The second operand.
   * @returns The compare.
   * @internal
   */
  static compare(a: FreeGroupElement, b: FreeGroupElement): number {
    return a.lt(b) ? -1 : b.lt(a) ? 1 : 0;
  }

  /**
   * Returns the total exponent of a generator (negated for an inverse generator).
   * @param gen - The generator to locate or count.
   * @returns The total exponent of a generator (negated for an inverse generator).
   * @throws RangeError when the letter is neither a generator nor its inverse.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.exponent_sum`
   */
  exponentSum(gen: FreeGroupElement): number {
    if (gen.length !== 1) throw new RangeError('gen must be a generator or inverse of a generator');
    const [g, s] = at(gen.syllables, 0);
    const t = s * this.syllables.reduce((acc, [h, e]) => (h === g ? acc + e : acc), 0);
    return t === 0 ? 0 : t;
  }

  /**
   * Returns the number of letters of a generator or its inverse.
   * @param gen - The generator to locate or count.
   * @returns The number of letters of a generator or its inverse.
   * @throws RangeError when the element is not one of the generators.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.generator_count`
   */
  generatorCount(gen: FreeGroupElement): number {
    if (gen.length !== 1 || at(gen.syllables, 0)[1] < 0) throw new RangeError('gen must be a generator');
    const g = at(gen.syllables, 0)[0];
    return this.syllables.reduce((t, [h, e]) => (h === g ? t + Math.abs(e) : t), 0);
  }

  /**
   * The letters from_i .. to_j - 1.
   * @param fromIn - The index where the selected segment starts.
   * @param toIn - The exclusive end of the selected segment.
   * @param strict - Whether to reject bounds outside the word rather than clipping them.
   * @returns The letters from_i.
   * @throws RangeError when the word bounds are outside the permitted interval.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.subword`
   */
  subword(fromIn: number, toIn: number, strict = true): FreeGroupElement {
    let from = fromIn;
    let to = toIn;
    if (!strict) {
      from = Math.max(from, 0);
      to = Math.min(this.length, to);
    }
    if (from < 0 || to > this.length) throw new RangeError('`from_i`, `to_j` must be positive and no greater than the length of associative word');
    if (to <= from) return this.group.identity;
    return this.fromLetters(this.letters.slice(from, to));
  }

  #find(sub: readonly number[], start = 0): number {
    const s = this.letters;
    const l = sub.length;
    for (let i = start; i <= s.length - l; i++) {
      let ok = true;
      for (let j = 0; j < l && ok; j++) ok = s[i + j] === sub[j];
      if (ok) return i;
    }
    return -1;
  }

  /**
   * Where word first occurs as a subword.
   * @param word - The group word to examine.
   * @param start - The starting position, inclusive.
   * @returns The subword index.
   * @throws RangeError when the word does not occur as a subword.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.subword_index`
   */
  subwordIndex(word: FreeGroupElement, start = 0): number {
    const i = this.#find(word.letters, start);
    if (i < 0) throw new RangeError('The given word is not a subword of self');
    return i;
  }

  /**
   * Whether word or its inverse is a subword.
   * @param word - The group word to examine.
   * @returns Whether the object is dependent.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.is_dependent`
   */
  isDependent(word: FreeGroupElement): boolean {
    return this.#find(word.letters) >= 0 || this.#find(word.inverse().letters) >= 0;
  }

  /**
   * See Also ========.
   * @param word - The group word to examine.
   * @returns Whether the object is independent.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.is_independent`
   */
  isIndependent(word: FreeGroupElement): boolean {
    return !this.isDependent(word);
  }

  /**
   * Returns the generators occurring in the word.
   * @returns The generators occurring in the word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.contains_generators`
   */
  containsGenerators(): Set<FreeGroupElement> {
    return new Set(uniqueWords(this.syllables.map(([g]) => at(this.group.generators, g))));
  }

  /**
   * A subword of the word repeated cyclically.
   * @param fromIn - The index where the selected segment starts.
   * @param toIn - The exclusive end of the selected segment.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.cyclic_subword`
   */
  cyclicSubword(fromIn: number, toIn: number): FreeGroupElement {
    const l = this.length;
    const letters = this.letters;
    let from = fromIn;
    let to = toIn;
    const period1 = Math.trunc(from / l);
    if (from >= l) {
      from -= l * period1;
      to -= l * period1;
    }
    const diff = to - from;
    let word = pySlice(letters, from, to);
    const period2 = Math.trunc(to / l) - 1;
    for (let k = 0; k < period2; k++) word = word.concat(letters);
    word = word.concat(pySlice(letters, 0, diff - l + from - l * period2));
    return this.fromLetters(word);
  }

  /**
   * Returns the words obtained by rotating this one.
   * @returns The words obtained by rotating this one.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.cyclic_conjugates`
   */
  cyclicConjugates(): Set<FreeGroupElement> {
    return new Set(uniqueWords(Array.from({ length: this.length }, (_, i) => this.cyclicSubword(i, i + this.length))));
  }

  /**
   * Whether w is a rotation of this word (after cyclic reduction).
   * @param w - The group word to scan or rewrite.
   * @returns Whether the object is cyclic conjugate.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.is_cyclic_conjugate`
   */
  isCyclicConjugate(w: FreeGroupElement): boolean {
    if (this.length !== w.length) return false;
    // SymPy compares the printed letter forms ("x -y ..."): a substring of the doubled other word
    const s1 = this.#letterStr(this.identityCyclicReduction().letters);
    const s2 = this.#letterStr(w.identityCyclicReduction().letters);
    if (s1.length !== s2.length) return false;
    return `${s2} ${s2}`.includes(s1);
  }

  #letterStr(letters: readonly number[]): string {
    return letters.map((c) => (c > 0 ? String(this.#sym(c - 1)) : `-${String(this.#sym(-c - 1))}`)).join(' ');
  }

  /**
   * Returns the number of syllables of the associative word `self`.
   * @returns The number of syllables of the associative word `self`.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.number_syllables`
   */
  numberSyllables(): number {
    return this.syllables.length;
  }

  /**
   * Returns the exponent of the `i`-th syllable of the associative word `self`.
   * @param i - The zero-based position in the sequence.
   * @returns The exponent of the `i`-th syllable of the associative word `self`.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.exponent_syllable`
   */
  exponentSyllable(i: number): number {
    return at(this.syllables, i < 0 ? this.syllables.length + i : i)[1];
  }

  /**
   * Returns the symbol of the generator that is involved in the i-th syllable of the associative word `self`.
   * @param i - The zero-based position in the sequence.
   * @returns The symbol of the generator that is involved in the i-th syllable of the associative word `self`.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.generator_syllable`
   */
  generatorSyllable(i: number): Expr {
    return this.#sym(at(this.syllables, i < 0 ? this.syllables.length + i : i)[0]);
  }

  /**
   * The syllables from_i .. to_j - 1.
   * @param from - The index where the selected segment starts.
   * @param to - The exclusive end of the selected segment.
   * @returns The syllables from_i.
   * @throws RangeError when an argument is not an integer.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.sub_syllables`
   */
  subSyllables(from: number, to: number): FreeGroupElement {
    if (!Number.isInteger(from) || !Number.isInteger(to)) throw new RangeError('both arguments should be integers');
    if (to <= from) return this.group.identity;
    return this.#new(pySlice(this.syllables, from, to));
  }

  /**
   * The letters from_i .. to_j - 1 replaced by `by`.
   * @param from - The index where the selected segment starts.
   * @param to - The exclusive end of the selected segment.
   * @param by - The replacement word.
   * @returns The letters from_i.
   * @throws RangeError when a supplied value is outside the allowed interval.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.substituted_word`
   */
  substitutedWord(from: number, to: number, by: FreeGroupElement): FreeGroupElement {
    const lw = this.length;
    if (from >= to || from > lw || to > lw) throw new RangeError('values should be within bounds');
    if (from === 0 && to === lw) return by;
    if (from === 0) return by.mul(this.subword(to, lw));
    if (to === lw) return this.subword(0, from).mul(by);
    return this.subword(0, from).mul(by).mul(this.subword(to, lw));
  }

  /**
   * The first letter is not the inverse of the last.
   * @returns Whether the object is cyclically reduced.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.is_cyclically_reduced`
   */
  isCyclicallyReduced(): boolean {
    const ls = this.letters;
    return ls.length === 0 || at(ls, 0) !== -at(ls, ls.length - 1);
  }

  /**
   * Cancel the first and last syllables while they share a generator.
   * @returns The resulting group word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.identity_cyclic_reduction`
   */
  identityCyclicReduction(): FreeGroupElement {
    let syl = [...this.syllables];
    while (syl.length && !this.#new(syl).isCyclicallyReduced()) {
      const [g, e1] = at(syl, 0);
      const e2 = at(syl, syl.length - 1)[1];
      const r = e1 + e2;
      syl = r === 0 ? syl.slice(1, syl.length - 1) : [[g, r], ...syl.slice(1, syl.length - 1)];
    }
    return this.#new(syl);
  }

  /**
   * The cyclically reduced word w' with
   * this = g*w'*g**-1; with `removed`, the pair [w', g].
   * @param removed - Whether to include the conjugating word removed by reduction.
   * @returns The cyclically reduced word w' with this = g*w'*g**-1.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.cyclic_reduction`
   */
  cyclicReduction(removed: true): [FreeGroupElement, FreeGroupElement];
  cyclicReduction(removed?: false): FreeGroupElement;
  cyclicReduction(removed = false): FreeGroupElement | [FreeGroupElement, FreeGroupElement] {
    let word: FreeGroupElement = this;
    let g = this.group.identity;
    while (!word.isCyclicallyReduced()) {
      const exp = Math.min(Math.abs(word.exponentSyllable(0)), Math.abs(word.exponentSyllable(-1)));
      const start = word.getItem(0).pow(exp);
      const end = word.getItem(-1).pow(exp);
      word = start.inverse().mul(word).mul(end.inverse());
      g = g.mul(start);
    }
    return removed ? [word, g] : word;
  }

  /**
   * Whether this word is a power of other.
   * @param otherIn - The value to combine with or compare against.
   * @returns Whether an integral power of the other word equals this word.
   * @see SymPy `sympy.combinatorics.free_groups.FreeGroupElement.power_of`
   */
  powerOf(otherIn: FreeGroupElement): boolean {
    let other = otherIn;
    if (this.isIdentity) return true;
    const l = other.length;
    if (l === 1) {
      const gens = uniqueWords(this.syllables.map(([g]) => at(this.group.generators, g)));
      const s = gens.some((g) => g.equals(other) || g.equals(other.inverse()));
      return gens.length === 1 && s;
    }
    const [reduced, r1] = this.cyclicReduction(true);
    if (!r1.isIdentity) {
      const [o, r2] = other.cyclicReduction(true);
      other = o;
      if (r1.equals(r2)) return reduced.powerOf(other);
      return false;
    }
    if (this.length < l || this.length % l) return false;
    const prefix = this.subword(0, l);
    if (prefix.equals(other) || prefix.inverse().equals(other)) return this.subword(l, this.length).powerOf(other);
    return false;
  }
}

/**
 * Constructs the free group on the given generator symbols.
 * @param symbols - The names or symbols of the free generators.
 * @returns The group followed by its free generators.
 * @see SymPy `sympy.combinatorics.free_groups.free_group`
 * @example
 * ```ts
 * import { freeGroup } from '@symjs/symjs';
 *
 * const [, x, y] = freeGroup('x, y, z');
 * String(x.pow(2).mul(y.inverse())); // => x**2*y**-1
 * ```
 */
export function freeGroup(symbols: FreeGroupSymbols): [FreeGroup, ...FreeGroupElement[]] {
  const F = new FreeGroup(symbols);
  return [F, ...F.generators];
}

/**
 * Constructs a free group and collects its generators in a separate array.
 * @param symbols - The names or symbols of the free generators.
 * @returns The group and its array of free generators.
 * @see SymPy `sympy.combinatorics.free_groups.xfree_group`
 * @example
 * ```ts
 * import { xfreeGroup } from '@symjs/symjs';
 *
 * const [, [x, y]] = xfreeGroup('x, y, z');
 * String(y.pow(2).mul(x.pow(-2))); // => y**2*x**-2
 * ```
 */
export function xfreeGroup(symbols: FreeGroupSymbols): [FreeGroup, FreeGroupElement[]] {
  const F = new FreeGroup(symbols);
  return [F, [...F.generators]];
}

/**
 * Constructs a free group whose generators are accessible through `generators`.
 * @param symbols - The names or symbols of the free generators.
 * @returns The group on the named generators.
 * @see SymPy `sympy.combinatorics.free_groups.vfree_group`
 * @example
 * ```ts
 * import { vfreeGroup } from '@symjs/symjs';
 * vfreeGroup('x, y, z').rank; // => 3
 * ```
 */
export function vfreeGroup(symbols: FreeGroupSymbols): FreeGroup {
  return new FreeGroup(symbols);
}
