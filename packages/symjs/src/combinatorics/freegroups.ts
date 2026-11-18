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
 * SymPy FreeGroup(symbols): the free group on the given symbols. Like
 * SymPy, groups on the same symbols are the same object.
 *
 * @example
 * const [F, x, y] = freeGroup('x, y');
 * String(x.pow(2).mul(y.inverse())) // 'x**2*y**-1'
 */
export class FreeGroup {
  readonly isAssociative = true;
  readonly isGroup = true;
  readonly isFreeGroup = true;
  readonly isPermutationGroup = false;
  /** SymPy relators: a free group has none. */
  readonly relators: readonly FreeGroupElement[] = [];
  readonly symbols!: readonly Expr[];
  readonly generators!: readonly FreeGroupElement[];
  /** @internal The symbol keys, for the index of a symbol. */
  readonly symbolIndex!: ReadonlyMap<string, number>;
  readonly #identity!: FreeGroupElement;

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

  /** SymPy dtype(array_form): the element with these (symbol, exponent) syllables. */
  dtype(arrayForm: readonly (readonly [Expr, number | bigint])[] = []): FreeGroupElement {
    const syllables: Syllable[] = [];
    for (const [s, e] of arrayForm) {
      const i = this.symbolIndex.get(s.key);
      if (i === undefined) throw new RangeError(`${String(s)} is not a generator of ${String(this)}`);
      if (Number(e) !== 0) syllables.push([i, Number(e)]);
    }
    return new FreeGroupElement(this, lettersToSyllables(syllables.flatMap(([g, e]) => Array<number>(Math.abs(e)).fill(Math.sign(e) * (g + 1)))));
  }

  /** SymPy clone(symbols): the free group on other symbols (or the same ones). */
  clone(symbols?: FreeGroupSymbols): FreeGroup {
    const empty = symbols === undefined || symbols === '' || (isSymbolList(symbols) && symbols.length === 0);
    return new FreeGroup(empty ? this.symbols : symbols);
  }

  /** SymPy len(F): the rank. */
  get length(): number {
    return this.rank;
  }

  /** SymPy F[i]: the free group on the ith symbol. */
  getItem(i: number): FreeGroup {
    return this.clone([at(this.symbols, i < 0 ? this.symbols.length + i : i)]);
  }

  /** SymPy F[i:j]: the free group on a slice of the symbols. */
  slice(start: number, end: number = this.symbols.length): FreeGroup {
    return this.clone(pySlice(this.symbols, start, end));
  }

  /** SymPy index(gen): the position of a generator. */
  index(gen: FreeGroupElement): number {
    const i = this.generators.findIndex((g) => g.equals(gen));
    if (gen.group !== this || i < 0) throw new RangeError(`expected a generator of Free Group ${String(this)}, got ${String(gen)}`);
    return i;
  }

  /** SymPy order(): 1 for the trivial group, else infinity. */
  order(): Expr {
    return this.rank === 0 ? S.One : S.Infinity;
  }

  /** SymPy elements: the elements of the trivial group (other free groups are infinite). */
  get elements(): Set<FreeGroupElement> {
    if (this.rank === 0) return new Set([this.identity]);
    throw new RangeError('Group contains infinitely many elements, hence cannot be represented');
  }

  /** SymPy rank: the number of generators. */
  get rank(): number {
    return this.symbols.length;
  }

  /** SymPy is_abelian: only the free groups of rank 0 and 1. */
  get isAbelian(): boolean {
    return this.rank <= 1;
  }

  /** SymPy identity: the empty word. */
  get identity(): FreeGroupElement {
    return this.#identity;
  }

  /** SymPy contains(g) (and `g in F`): whether g is an element of this group. */
  contains(g: unknown): boolean {
    return g instanceof FreeGroupElement && g.group === this;
  }

  /** SymPy center(): the identity only. */
  center(): Set<FreeGroupElement> {
    return new Set([this.identity]);
  }

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
 * SymPy FreeGroupElement: an element of a free group, a reduced associative
 * word. Elements are immutable and compared by value (`equals`, `key`).
 */
export class FreeGroupElement {
  readonly isAssocWord = true;
  readonly group: FreeGroup;
  /** @internal The syllables as (generator index, exponent). */
  readonly syllables: readonly Syllable[];
  #letters: number[] | undefined;
  #key: string | undefined;

  /** @internal Use FreeGroup.dtype, the generators and the group operations. */
  constructor(group: FreeGroup, syllables: readonly Syllable[]) {
    this.group = group;
    this.syllables = syllables;
  }

  /** A string identifying the word within its group. */
  get key(): string {
    return (this.#key ??= this.syllables.map(([g, e]) => `${g}^${e}`).join(' '));
  }

  /** @internal The letters, +(i+1) for generator i and -(i+1) for its inverse. */
  get letters(): readonly number[] {
    return (this.#letters ??= this.syllables.flatMap(([g, e]) => Array<number>(Math.abs(e)).fill(Math.sign(e) * (g + 1))));
  }

  /** @internal The word with these letters. */
  fromLetters(letters: readonly number[]): FreeGroupElement {
    return new FreeGroupElement(this.group, lettersToSyllables(letters));
  }

  #new(syllables: readonly Syllable[]): FreeGroupElement {
    return new FreeGroupElement(this.group, syllables);
  }

  #sym(g: number): Expr {
    return at(this.group.symbols, g);
  }

  /** SymPy new(init): an element of the same group from (symbol, exponent) pairs. */
  new(init: readonly (readonly [Expr, number | bigint])[]): FreeGroupElement {
    return this.group.dtype(init);
  }

  /** SymPy copy(). */
  copy(): FreeGroupElement {
    return this.#new(this.syllables);
  }

  /** SymPy is_identity: the empty word. */
  get isIdentity(): boolean {
    return this.syllables.length === 0;
  }

  /** SymPy array_form: the (symbol, exponent) syllables. */
  get arrayForm(): [Expr, number][] {
    return this.syllables.map(([g, e]) => [this.#sym(g), e]);
  }

  /** SymPy letter_form: the word letter by letter, an inverse letter as -symbol. */
  get letterForm(): Expr[] {
    return this.letters.map((c) => (c > 0 ? this.#sym(c - 1) : mul(-1, this.#sym(-c - 1))));
  }

  /** SymPy w[i]: the ith letter as an element (negative i counts from the end). */
  getItem(i: number): FreeGroupElement {
    const ls = this.letters;
    const c = ls[i < 0 ? ls.length + i : i];
    if (c === undefined) throw new RangeError('tuple index out of range');
    return this.#new([[Math.abs(c) - 1, Math.sign(c)]]);
  }

  /** SymPy index(gen): the position of the first occurrence of a letter. */
  index(gen: FreeGroupElement): number {
    if (gen.length !== 1) throw new RangeError('');
    const i = this.letters.indexOf(at(gen.letters, 0));
    if (i < 0) throw new RangeError('tuple.index(x): x not in tuple');
    return i;
  }

  /** SymPy letter_form_elm: the letters as elements. */
  get letterFormElm(): FreeGroupElement[] {
    return this.letters.map((c) => this.#new([[Math.abs(c) - 1, Math.sign(c)]]));
  }

  /** SymPy ext_rep: the flattened array form. */
  get extRep(): (Expr | number)[] {
    return this.syllables.flatMap(([g, e]) => [this.#sym(g), e]);
  }

  /** SymPy `gen in w`: whether the generator of gen occurs in this word. */
  has(gen: FreeGroupElement): boolean {
    const g = at(gen.syllables, 0)[0];
    return this.syllables.some((s) => s[0] === g);
  }

  toString(): string {
    if (this.isIdentity) return '<identity>';
    return this.syllables.map(([g, e]) => (e === 1 ? String(this.#sym(g)) : `${String(this.#sym(g))}**${e}`)).join('*');
  }

  /** SymPy w**n. */
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

  /** SymPy w1*w2. */
  mul(other: FreeGroupElement): FreeGroupElement {
    const o = this.#check(other, 'multiplied');
    if (this.isIdentity) return o;
    if (o.isIdentity) return this;
    return this.#new(joinSyllables(this.syllables, o.syllables));
  }

  /** SymPy w1/w2 = w1*w2**-1. */
  div(other: FreeGroupElement): FreeGroupElement {
    return this.mul(this.#check(other, 'multiplied').inverse());
  }

  /** SymPy inverse(). */
  inverse(): FreeGroupElement {
    return this.#new([...this.syllables].reverse().map(([g, e]) => [g, -e]));
  }

  /** SymPy order(): 1 for the identity, else infinity. */
  order(): Expr {
    return this.isIdentity ? S.One : S.Infinity;
  }

  /** SymPy commutator(other): self**-1*other**-1*self*other. */
  commutator(other: FreeGroupElement): FreeGroupElement {
    if (!(other instanceof FreeGroupElement) || other.group !== this.group) throw new RangeError('commutator of only FreeGroupElement of the same FreeGroup exists');
    return this.inverse().mul(other.inverse()).mul(this).mul(other);
  }

  /**
   * SymPy eliminate_words(words, _all, inverse): replace each word of a list
   * by the identity, or each key of a Map by its value, until nothing changes.
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
   * SymPy eliminate_word(gen, by, _all, inverse): replace the first
   * occurrence of gen (or of its inverse) by `by` (default the identity), or
   * every occurrence with `all`.
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

  /** SymPy len(w): the number of letters. */
  get length(): number {
    return this.syllables.reduce((s, [, e]) => s + Math.abs(e), 0);
  }

  /** SymPy w1 == w2: the same word of the same group. */
  equals(other: unknown): boolean {
    return other instanceof FreeGroupElement && other.group === this.group && other.key === this.key;
  }

  /** SymPy w1 < w2: shorter words first, then letter by letter (generator order, inverses first). */
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

  /** SymPy w1 <= w2. */
  le(other: FreeGroupElement): boolean {
    return this.equals(other) || this.lt(other);
  }

  /** SymPy w1 > w2. */
  gt(other: FreeGroupElement): boolean {
    this.#check(other, 'compared');
    return !this.le(other);
  }

  /** SymPy w1 >= w2. */
  ge(other: FreeGroupElement): boolean {
    return !this.lt(other);
  }

  /** @internal A comparator for sorting (SymPy's order of words). */
  static compare(a: FreeGroupElement, b: FreeGroupElement): number {
    return a.lt(b) ? -1 : b.lt(a) ? 1 : 0;
  }

  /** SymPy exponent_sum(gen): the total exponent of a generator (negated for an inverse generator). */
  exponentSum(gen: FreeGroupElement): number {
    if (gen.length !== 1) throw new RangeError('gen must be a generator or inverse of a generator');
    const [g, s] = at(gen.syllables, 0);
    const t = s * this.syllables.reduce((acc, [h, e]) => (h === g ? acc + e : acc), 0);
    return t === 0 ? 0 : t;
  }

  /** SymPy generator_count(gen): the number of letters of a generator or its inverse. */
  generatorCount(gen: FreeGroupElement): number {
    if (gen.length !== 1 || at(gen.syllables, 0)[1] < 0) throw new RangeError('gen must be a generator');
    const g = at(gen.syllables, 0)[0];
    return this.syllables.reduce((t, [h, e]) => (h === g ? t + Math.abs(e) : t), 0);
  }

  /** SymPy subword(from_i, to_j, strict): the letters from_i .. to_j - 1. */
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

  /** SymPy subword_index(word, start): where word first occurs as a subword. */
  subwordIndex(word: FreeGroupElement, start = 0): number {
    const i = this.#find(word.letters, start);
    if (i < 0) throw new RangeError('The given word is not a subword of self');
    return i;
  }

  /** SymPy is_dependent(word): whether word or its inverse is a subword. */
  isDependent(word: FreeGroupElement): boolean {
    return this.#find(word.letters) >= 0 || this.#find(word.inverse().letters) >= 0;
  }

  /** SymPy is_independent(word). */
  isIndependent(word: FreeGroupElement): boolean {
    return !this.isDependent(word);
  }

  /** SymPy contains_generators(): the generators occurring in the word. */
  containsGenerators(): Set<FreeGroupElement> {
    return new Set(uniqueWords(this.syllables.map(([g]) => at(this.group.generators, g))));
  }

  /** SymPy cyclic_subword(from_i, to_j): a subword of the word repeated cyclically. */
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

  /** SymPy cyclic_conjugates(): the words obtained by rotating this one. */
  cyclicConjugates(): Set<FreeGroupElement> {
    return new Set(uniqueWords(Array.from({ length: this.length }, (_, i) => this.cyclicSubword(i, i + this.length))));
  }

  /** SymPy is_cyclic_conjugate(w): whether w is a rotation of this word (after cyclic reduction). */
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

  /** SymPy number_syllables(). */
  numberSyllables(): number {
    return this.syllables.length;
  }

  /** SymPy exponent_syllable(i) (negative i counts from the end). */
  exponentSyllable(i: number): number {
    return at(this.syllables, i < 0 ? this.syllables.length + i : i)[1];
  }

  /** SymPy generator_syllable(i) (negative i counts from the end). */
  generatorSyllable(i: number): Expr {
    return this.#sym(at(this.syllables, i < 0 ? this.syllables.length + i : i)[0]);
  }

  /** SymPy sub_syllables(from_i, to_j): the syllables from_i .. to_j - 1. */
  subSyllables(from: number, to: number): FreeGroupElement {
    if (!Number.isInteger(from) || !Number.isInteger(to)) throw new RangeError('both arguments should be integers');
    if (to <= from) return this.group.identity;
    return this.#new(pySlice(this.syllables, from, to));
  }

  /** SymPy substituted_word(from_i, to_j, by): the letters from_i .. to_j - 1 replaced by `by`. */
  substitutedWord(from: number, to: number, by: FreeGroupElement): FreeGroupElement {
    const lw = this.length;
    if (from >= to || from > lw || to > lw) throw new RangeError('values should be within bounds');
    if (from === 0 && to === lw) return by;
    if (from === 0) return by.mul(this.subword(to, lw));
    if (to === lw) return this.subword(0, from).mul(by);
    return this.subword(0, from).mul(by).mul(this.subword(to, lw));
  }

  /** SymPy is_cyclically_reduced(): the first letter is not the inverse of the last. */
  isCyclicallyReduced(): boolean {
    const ls = this.letters;
    return ls.length === 0 || at(ls, 0) !== -at(ls, ls.length - 1);
  }

  /** SymPy identity_cyclic_reduction(): cancel the first and last syllables while they share a generator. */
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
   * SymPy cyclic_reduction(removed): the cyclically reduced word w' with
   * this = g*w'*g**-1; with `removed`, the pair [w', g].
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

  /** SymPy power_of(other): whether this word is a power of other. */
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

/** SymPy free_group(symbols): the free group and its generators, [F, x, y, ...]. */
export function freeGroup(symbols: FreeGroupSymbols): [FreeGroup, ...FreeGroupElement[]] {
  const F = new FreeGroup(symbols);
  return [F, ...F.generators];
}

/** SymPy xfree_group(symbols): the free group and the tuple of its generators. */
export function xfreeGroup(symbols: FreeGroupSymbols): [FreeGroup, FreeGroupElement[]] {
  const F = new FreeGroup(symbols);
  return [F, [...F.generators]];
}

/**
 * SymPy vfree_group(symbols): the free group. SymPy also binds the
 * generators in the caller's namespace, which JavaScript has not; use
 * `F.generators`.
 */
export function vfreeGroup(symbols: FreeGroupSymbols): FreeGroup {
  return new FreeGroup(symbols);
}
