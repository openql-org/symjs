// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.combinatorics.permutations: Permutation, Cycle and
 * AppliedPermutation, with the array-form helpers (_af_rmul, _af_parity, ...).
 *
 * Permutations act on 0, 1, ..., n-1. The product p.mul(q) is SymPy's p*q:
 * first apply p, then q, so p.mul(q).call(i) === q.call(p.call(i)).
 */

import { isIntegerQ, isNegative, isNonNegative } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined, expectType, last } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import type { Substitution, Sym } from '../core/nodes';
import { Expr, ExtensionExpr, Rational } from '../core/nodes';
import { asContentPrimitive, dummyEq, hasFree, hasXfree, isSame } from '../core/methods';
import type { Query, Replacement } from '../core/match';
import { count, countOps, find, replace } from '../core/match';
import { match } from '../core/public';
import type { Assumption } from '../core/refine';
import { refine } from '../core/refine';
import { xreplace } from '../core/traverse';
import type { Key } from '../printing/sortkey';
import { sortKey } from '../printing/sortkey';
import { permCyclic } from '../printing/str';
import { add, couldExtractMinusSign, sympify } from '../core/ops';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { Matrix } from '../matrices/matrix';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const isExpr = (x: unknown): x is Expr => x instanceof Expr;
const isKeyList = (x: unknown): x is Key[] => Array.isArray(x);
const isUnknownArray = (x: unknown): x is readonly unknown[] => Array.isArray(x);

/** A Python int: a safe JavaScript integer (bigints are converted). */
function asInt(v: unknown, what = 'value'): number {
  if (typeof v === 'bigint') {
    const n = Number(v);
    if (!Number.isSafeInteger(n)) throw new RangeError(`${what} ${v} is too large`);
    return n;
  }
  if (typeof v === 'number' && Number.isInteger(v)) return v;
  if (v instanceof Rational && v.q === 1n) return asInt(v.p, what);
  throw new TypeError(`${String(v)} is not an integer`);
}

function toBig(v: number | bigint | Expr): bigint {
  if (typeof v === 'bigint') return v;
  if (typeof v === 'number') {
    if (!Number.isInteger(v)) throw new TypeError(`${v} is not an integer`);
    return BigInt(v);
  }
  if (v instanceof Rational && v.q === 1n) return v.p;
  throw new TypeError(`${v.toString()} is not an integer`);
}

/** n! as a bigint (mpmath ifac); 1 for n <= 0. */
function ifac(n: number): bigint {
  let r = 1n;
  for (let i = 2; i <= n; i++) r *= BigInt(i);
  return r;
}

/** Python's a % b for bigints (result has the sign of b). */
function pmod(a: bigint, b: bigint): bigint {
  const r = a % b;
  return r !== 0n && r < 0n !== b < 0n ? r + b : r;
}

/** gcd of two positive bigints (the lengths of cycles). */
function bgcd(a: bigint, b: bigint): bigint {
  let x = a;
  let y = b;
  while (y !== 0n) [x, y] = [y, x % y];
  return x;
}

/** Python list indexing (negative indices count from the end); IndexError otherwise. */
function pyIndex<T>(a: readonly T[], i: number): T {
  const j = i < 0 ? i + a.length : i;
  if (j < 0 || j >= a.length) throw new RangeError('list index out of range');
  return at(a, j);
}

/** Python's str of a list of ints: [0, 2, 1]. */
const listStr = (a: readonly number[]): string => `[${a.join(', ')}]`;

/** Python's default ordering of two values (numbers, strings, bigints). */
function pyCompare(a: unknown, b: unknown): number {
  if ((typeof a === 'number' || typeof a === 'bigint') && (typeof b === 'number' || typeof b === 'bigint')) {
    return a < b ? -1 : a > b ? 1 : 0;
  }
  if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
  if (Array.isArray(a) && Array.isArray(b)) {
    for (let i = 0; i < Math.min(a.length, b.length); i++) {
      const c = pyCompare(a[i], b[i]);
      if (c !== 0) return c;
    }
    return a.length - b.length;
  }
  throw new TypeError(`'<' not supported between ${typeof a} and ${typeof b}`);
}

/** A small seeded generator (mulberry32) of numbers in [0, 1). */
function seeded(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---------------------------------------------------------------------------
// Array-form helpers (SymPy's _af_* functions)
// ---------------------------------------------------------------------------

/**
 * The product b*a of array forms; the ith value is a[b[i]].
 * @param a - The images of successive points under the permutation.
 * @param b - The images of successive points under the second permutation.
 * @returns The images under the composition.
 * @see SymPy `sympy.combinatorics.permutations._af_rmul`
 * @example
 * ```ts
 * import { afRmul } from '@symjs/symjs';
 * afRmul([1, 0, 2], [0, 2, 1]); // => [1, 2, 0]
 * ```
 */
export function afRmul(a: readonly number[], b: readonly number[]): number[] {
  return b.map((i) => pyIndex(a, i));
}

/**
 * The product ...*c*b*a of array forms; the ith value is a[b[c[i]]].
 * @param abc - The permutations in composition order.
 * @returns The composite permutation in array form.
 * @throws RangeError when the string is empty.
 * @see SymPy `sympy.combinatorics.permutations._af_rmuln`
 * @example
 * ```ts
 * import { afRmuln } from '@symjs/symjs';
 * afRmuln([1, 0, 2], [0, 2, 1]); // => [1, 2, 0]
 * ```
 */
export function afRmuln(...abc: (readonly number[])[]): number[] {
  if (abc.length === 0) throw new RangeError('String must not be empty');
  let rv = [...last(abc)];
  for (let k = abc.length - 2; k >= 0; k--) rv = afRmul(at(abc, k), rv);
  return rv;
}

/**
 * The parity (0 or 1) of a permutation in array form.
 * @param pi - The images of successive points under the permutation.
 * @returns Zero for an even permutation, one for an odd one.
 * @see SymPy `sympy.combinatorics.permutations._af_parity`
 * @example
 * ```ts
 * import { afParity } from '@symjs/symjs';
 * afParity([0, 1, 2, 3]); // => 0
 * ```
 */
export function afParity(pi: readonly number[]): number {
  const n = pi.length;
  const seen = new Array<boolean>(n).fill(false);
  let c = 0;
  for (let j = 0; j < n; j++) {
    if (!seen[j]) {
      c++;
      seen[j] = true;
      let i = j;
      while (pi[i] !== j) {
        i = at(pi, i);
        seen[i] = true;
      }
    }
  }
  return (n - c) % 2;
}

/**
 * The inverse of a permutation in array form.
 * @param a - The images of successive points under the permutation.
 * @returns The preimage of each point in order.
 * @see SymPy `sympy.combinatorics.permutations._af_invert`
 * @example
 * ```ts
 * import { afInvert } from '@symjs/symjs';
 * afInvert([1, 2, 0, 3]); // => [2, 0, 1, 3]
 * ```
 */
export function afInvert(a: readonly number[]): number[] {
  const inv = new Array<number>(a.length).fill(0);
  a.forEach((ai, i) => {
    inv[ai] = i;
  });
  return inv;
}

/**
 * The nth power of a permutation in array form.
 * @param a - The images of successive points under the permutation.
 * @param n - The exponent.
 * @returns The powered permutation in array form.
 * @see SymPy `sympy.combinatorics.permutations._af_pow`
 * @example
 * ```ts
 * import { afPow } from '@symjs/symjs';
 * afPow([2, 0, 3, 1], 4); // => [0, 1, 2, 3]
 * ```
 */
export function afPow(a: readonly number[], n: number | bigint): number[] {
  let e = BigInt(n);
  let base = [...a];
  if (e < 0n) {
    base = afInvert(base);
    e = -e;
  }
  let b = Array.from({ length: a.length }, (_, i) => i);
  while (e > 0n) {
    if (e & 1n) b = b.map((i) => at(base, i));
    e >>= 1n;
    if (e > 0n) base = base.map((i) => at(base, i));
  }
  return b;
}

/**
 * Whether the permutations with array forms a and b commute.
 * @param a - The images of successive points under the permutation.
 * @param b - The images of successive points under the second permutation.
 * @returns Whether the two compositions agree.
 * @see SymPy `sympy.combinatorics.permutations._af_commutes_with`
 * @example
 * ```ts
 * import { afCommutesWith } from '@symjs/symjs';
 * afCommutesWith([1, 2, 0], [0, 2, 1]); // => False
 * ```
 */
export function afCommutesWith(a: readonly number[], b: readonly number[]): boolean {
  for (let i = 0; i < a.length - 1; i++) {
    if (pyIndex(a, pyIndex(b, i)) !== pyIndex(b, pyIndex(a, i))) return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Cycle
// ---------------------------------------------------------------------------

/** Arguments of Cycle(...) and Cycle.call(...): integers of one cycle, or a Permutation or Cycle. */
export type CycleArgs = readonly (number | bigint)[] | readonly [Permutation] | readonly [Cycle];

/**
 * A disjoint-cycle mapping (a dict whose missing keys map to
 * themselves). `new Cycle(1, 2).call(2, 3)` is SymPy's Cycle(1, 2)(2, 3);
 * cycles are applied from left to right.
 * @see SymPy `sympy.combinatorics.permutations.Cycle`
 * @example
 * ```ts
 * import { Cycle } from '@symjs/symjs';
 * new Cycle(1, 2).list(); // => [0, 2, 1]
 * ```
 */
export class Cycle implements Iterable<number> {
  readonly #map = new Map<number, number>();

  /**
   * Constructs a `Cycle`.
   * @param args - The operands in their defining order.
   * @throws RangeError when a cycle contains a negative point or a cycle contains a repeated point.
   */
  constructor(...args: CycleArgs) {
    if (args.length === 0) return;
    if (args.length === 1) {
      const a = args[0];
      if (a instanceof Permutation) {
        for (const c of a.cyclicForm) {
          const rv = this.call(...c);
          for (const [k, v] of rv.items()) this.#map.set(k, v);
        }
        return;
      }
      if (a instanceof Cycle) {
        for (const [k, v] of a.items()) this.#map.set(k, v);
        return;
      }
    }
    const ints = (args as readonly unknown[]).map((v) => asInt(v));
    if (ints.some((i) => i < 0)) throw new RangeError('negative integers are not allowed in a cycle.');
    if (new Set(ints).size !== ints.length) throw new RangeError('All elements must be unique in a cycle.');
    for (let i = 0; i < ints.length; i++) this.#map.set(at(ints, i), at(ints, (i + 1) % ints.length));
  }

  /**
   * Finds the image of a point, including points fixed by the cycle.
   * @param i - The zero-based position in the sequence.
   * @returns The image of a point, including points fixed by the cycle.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.get`
   */
  get(i: number | bigint): number {
    const k = asInt(i);
    return this.#map.get(k) ?? k;
  }

  /**
   * Returns the stored (key, value) pairs in insertion order.
   * @returns The stored (key, value) pairs in insertion order.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.items`
   */
  items(): [number, number][] {
    return [...this.#map.entries()];
  }

  /**
   * Returns the stored keys in insertion order.
   * @returns The stored keys in insertion order.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.keys`
   */
  keys(): number[] {
    return [...this.#map.keys()];
  }

  /**
   * Whether nothing is stored.
   * @returns Whether the object is empty.
   */
  get isEmpty(): boolean {
    return this.#map.size === 0;
  }

  /**
   * One more than the largest stored element (0 when empty).
   * @returns The size of the object.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.size`
   */
  get size(): number {
    return this.#map.size === 0 ? 0 : Math.max(...this.#map.keys()) + 1;
  }

  /**
   * Returns the product of this cycle followed by the cycle of `other`.
   * @param other - The value to combine with or compare against.
   * @returns The product of this cycle followed by the cycle of `other`.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.__call__`
   */
  call(...other: CycleArgs): Cycle {
    const rv = new Cycle(...other);
    const keys = this.keys();
    const vals = keys.map((k) => rv.get(this.get(k)));
    keys.forEach((k, i) => rv.#map.set(k, at(vals, i)));
    return rv;
  }

  /**
   * The array form from 0 up to the larger of the largest
   * moved element and size; size -1 trims trailing unmoved elements.
   * @param size - The number of positions.
   * @returns The array form from 0 up to the larger of the largest moved element and size.
   * @throws RangeError when an empty cycle is given without a size.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.list`
   */
  list(size?: number): number[] {
    let n: number;
    if (size === undefined) {
      if (this.isEmpty) throw new RangeError('must give size for empty Cycle');
      n = this.size;
    } else {
      let big = 0;
      for (const [k, v] of this.#map) if (k !== v && k > big) big = k;
      n = Math.max(size, big + 1);
    }
    return Array.from({ length: n }, (_, i) => this.get(i));
  }

  /**
   * Copies the cycle mapping.
   * @returns A separate cycle with the same point mapping.
   * @see SymPy `sympy.combinatorics.permutations.Cycle.copy`
   */
  copy(): Cycle {
    return new Cycle(this);
  }

  /**
   * Returns the array form (SymPy iter(cycle)).
   * @returns The array form (SymPy iter(cycle)).
   */
  [Symbol.iterator](): Iterator<number> {
    return this.list()[Symbol.iterator]();
  }

  #print(sep: string): string {
    const cycles = new Permutation(this).cyclicForm;
    const big = this.size - 1;
    let s = cycles.map((c) => `(${c.join(sep)})`).join('');
    if (!cycles.some((c) => c.includes(big))) s += `(${big})`;
    return s;
  }

  /**
   * Formats the object as plain text.
   * @returns The printable representation.
   */
  toString(): string {
    return this.isEmpty ? '()' : this.#print(' ');
  }

  /**
   * Cycle(1, 3, 2).
   * @returns The resulting text.
   */
  repr(): string {
    return this.isEmpty ? 'Cycle()' : `Cycle${this.#print(', ')}`;
  }

  /**
   * Formats the object in LaTeX.
   * @returns The resulting text.
   */
  toLatex(): string {
    return this.size === 0 ? '\\left( \\right)' : cycleLatex(new Permutation(this));
  }
}

// ---------------------------------------------------------------------------
// Permutation
// ---------------------------------------------------------------------------

/** The size keyword of Permutation(...). */
export interface PermutationOptions {
  /** The degree, including trailing fixed points. */
  size?: number;
}

/** A single argument of Permutation(...): array form, cyclic form, a Cycle or a Permutation. */
export type PermutationInput = Permutation | Cycle | readonly number[] | readonly (readonly number[])[];

/** Options of Permutation.random: a seed or a generator of numbers in [0, 1). */
export interface RandomOptions {
  /** The seed controlling random draws. */
  seed?: number;
  /** The function supplying random draws. */
  prng?: () => number;
}

/** Printer settings of the Permutation printers. */
export interface PermutationPrintOptions {
  /** Whether to print permutations in cycle notation. */
  permCyclic?: boolean;
}

/** The array form afNew hands to the next Permutation constructor call (taken before anything else runs). */
let pendingAf: number[] | undefined;

function isOptions(v: unknown): v is PermutationOptions {
  return typeof v === 'object' && v !== null && !Array.isArray(v) && !(v instanceof Expr) && !(v instanceof Cycle);
}

function parseArgs(input: readonly unknown[]): number[] {
  let args = input;
  let size: number | undefined;
  const o = args[args.length - 1];
  if (args.length > 0 && isOptions(o)) {
    if (o.size !== undefined) size = asInt(o.size, 'size');
    args = args.slice(0, -1);
  }
  if (args.length === 0) return Array.from({ length: size ?? 0 }, (_, i) => i);
  if (args.length > 1) return new Cycle(...args.map((v) => asInt(v))).list(size);
  const a = args[0];
  if (a instanceof Permutation) return size === undefined || size === a.size ? a.arrayForm : parseArgs([a.arrayForm, { size }]);
  if (a instanceof Cycle) return a.list(size);
  if (!Array.isArray(a)) {
    const m = asInt(a);
    if (size !== undefined && m + 1 > size) throw new RangeError(`size is too small when max is ${m}`);
    return Array.from({ length: Math.max(m + 1, 0) }, (_, i) => i);
  }
  const arr = a as readonly unknown[];
  const seqs = arr.map((x) => Array.isArray(x));
  if (seqs.some((s) => s) && seqs.some((s) => !s)) {
    throw new TypeError('Permutation argument must be a list of ints, a list of lists, Permutation or Cycle.');
  }
  const isCycle = seqs.length > 0 && at(seqs, 0);
  let aform: number[];
  if (isCycle) {
    let c = new Cycle();
    // every element is a list here (mixed lists were rejected above)
    for (const ci of arr) c = c.call(...expectType(ci, isUnknownArray, 'cycle').map((v) => asInt(v)));
    aform = c.list();
  } else {
    const ints = arr.map((v) => asInt(v));
    const set = new Set(ints);
    if (set.size !== ints.length) throw new RangeError('there were repeated elements.');
    const max = ints.length === 0 ? 0 : Math.max(...ints);
    for (let i = 0; i < ints.length; i++) {
      if (!set.has(i)) throw new RangeError(`Integers 0 through ${max} must be present.`);
    }
    if (size !== undefined && ints.length > 0 && max + 1 > size) {
      throw new RangeError(`max element should not exceed ${size - 1}`);
    }
    aform = ints;
  }
  if (size !== undefined && size > aform.length) for (let i = aform.length; i < size; i++) aform.push(i);
  return aform;
}

function cycleLatex(p: Permutation): string {
  const cycles = p.cyclicForm;
  const siz = p.size;
  if (p.arrayForm[siz - 1] === siz - 1) cycles.push([siz - 1]);
  return cycles.map((c) => `\\left( ${c.join('\\; ')}\\right)`).join('');
}

/** @internal Wrap an array form without validation (SymPy _af_new). */
export function afNew(perm: number[]): Permutation {
  pendingAf = perm;
  return new Permutation();
}

/**
 * A bijection of {0, ..., n-1}, built from its array
 * form (`new Permutation([0, 2, 1])`), its cyclic form
 * (`new Permutation([[1, 2]])`), the integers of one cycle
 * (`new Permutation(1, 2)`), a size (`new Permutation(3)` is the identity of
 * size 4), a Cycle or another Permutation, with an optional trailing
 * `{ size }`. It is an atomic expression that prints like SymPy's str,
 * e.g. `(1 2)`.
 * @throws RangeError when the images do not contain each point exactly once.
 * @see SymPy `sympy.combinatorics.permutations.Permutation`
 * @example
 * ```ts
 * import { Permutation } from '@symjs/symjs';
 * new Permutation([0, 2, 1]).arrayForm; // => [0, 2, 1]
 * ```
 */
export class Permutation extends ExtensionExpr implements Iterable<number> {
  readonly #af: number[];
  #cyclic: number[][] | undefined;
  #rank: bigint | undefined;

  /**
   * Constructs a `Permutation`.
   * @param cycle - The cycle to apply.
   * @param args - The operands in their defining order.
   * @param arg - The expression to operate on.
   * @param options - The settings described by {@link PermutationOptions}.
   */
  constructor(...cycle: (number | bigint | Expr)[]);
  /**
   * Constructs a permutation from the points of a single cycle. The trailing size option sets
   * the degree, including any additional fixed points.
   *
   * @see SymPy `sympy.combinatorics.permutations.Permutation`
   */
  constructor(...args: [...cycle: (number | bigint | Expr)[], options: PermutationOptions]);
  /**
   * Constructs a permutation from an array form, cycles, a `Cycle`, or another `Permutation`,
   * with an optional size.
   *
   * @see SymPy `sympy.combinatorics.permutations.Permutation`
   */
  constructor(arg: PermutationInput, options?: PermutationOptions);
  constructor(...input: readonly unknown[]) {
    const af = pendingAf;
    pendingAf = undefined;
    super('Permutation', []);
    this.#af = af ?? parseArgs(input);
  }

  /**
   * Rebuilds the expression with replacement operands.
   * @param _args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(_args: readonly Expr[]): Expr {
    return this;
  }

  /**
   * Identifies this permutation as an atom for expression ordering.
   * @returns Always `true` for permutations.
   */
  override get atomClass(): boolean {
    return true;
  }

  protected override computeKey(): string {
    return `Permutation(${this.#af.join(',')})`;
  }

  /**
   * Formats the expression as plain text.
   * @param _print - Formats a child expression.
   * @returns The plain-text representation.
   */
  override printStr(_print: (e: Expr) => string): string {
    return permutationStr(this, { permCyclic: permCyclic() });
  }

  /**
   * Formats the expression in LaTeX.
   * @param _print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(_print: (e: Expr) => string): string {
    return permutationLatex(this, { permCyclic: permCyclic() });
  }

  /**
   * Permutation(1, 2) with the printer setting perm_cyclic, else Permutation([0, 2, 1]).
   * @returns The resulting text.
   */
  printRepr(): string {
    return permutationRepr(this, { permCyclic: permCyclic() });
  }

  // ---- forms ----------------------------------------------------------------

  /**
   * Gets a copy of the array form.
   * @returns A copy of the array form.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.array_form`
   */
  get arrayForm(): number[] {
    return [...this.#af];
  }

  /**
   * The number of elements the permutation acts on.
   * @returns The size of the object.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.size`
   */
  get size(): number {
    return this.#af.length;
  }

  /**
   * The array form, extended to `size` when larger, or
   * with trailing unmoved elements trimmed otherwise (size -1 always trims).
   * @param size - The number of positions.
   * @returns The array form, extended to `size` when larger, or with trailing unmoved elements trimmed otherwise (size -1 always trims).
   * @see SymPy `sympy.combinatorics.permutations.Permutation.list`
   */
  list(size?: number): number[] {
    const rv = this.arrayForm;
    if (size === undefined) return rv;
    if (size > this.size) {
      for (let i = this.size; i < size; i++) rv.push(i);
    } else {
      let i = this.size - 1;
      while (rv.length > 0 && rv[rv.length - 1] === i) {
        rv.pop();
        i--;
      }
    }
    return rv;
  }

  /**
   * Gets the cycles without singletons, each starting with its smallest element, sorted.
   * @returns The cycles without singletons, each starting with its smallest element, sorted.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.cyclic_form`
   */
  get cyclicForm(): number[][] {
    if (this.#cyclic === undefined) {
      const af = this.#af;
      const unchecked = new Array<boolean>(af.length).fill(true);
      const cyclic: number[][] = [];
      for (let i = 0; i < af.length; i++) {
        if (!unchecked[i]) continue;
        const cycle = [i];
        unchecked[i] = false;
        let j = i;
        while (unchecked[at(af, j)]) {
          j = at(af, j);
          cycle.push(j);
          unchecked[j] = false;
        }
        if (cycle.length > 1) cyclic.push(cycle);
      }
      cyclic.sort(pyCompare);
      this.#cyclic = cyclic;
    }
    return this.#cyclic.map((c) => [...c]);
  }

  /**
   * Gets the cycles including singletons, sorted.
   * @returns The cycles including singletons, sorted.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.full_cyclic_form`
   */
  get fullCyclicForm(): number[][] {
    const cyc = this.cyclicForm;
    const moved = new Set(cyc.flat());
    for (let i = 0; i < this.size; i++) if (!moved.has(i)) cyc.push([i]);
    return cyc.sort(pyCompare);
  }

  /**
   * Returns the elements i with p(i) != i.
   * @returns The elements i with p(i) != i.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.support`
   */
  support(): number[] {
    const out: number[] = [];
    this.#af.forEach((e, i) => {
      if (e !== i) out.push(i);
    });
    return out;
  }

  /**
   * Gets the number of cycles, singletons included.
   * @returns The number of cycles, singletons included.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.cycles`
   */
  get cycles(): number {
    return this.fullCyclicForm.length;
  }

  /**
   * Gets a Map from cycle length to its multiplicity.
   * @returns A Map from cycle length to its multiplicity.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.cycle_structure`
   */
  get cycleStructure(): Map<number, number> {
    const rv = new Map<number, number>();
    let singletons = this.size;
    for (const c of this.cyclicForm) {
      rv.set(c.length, (rv.get(c.length) ?? 0) + 1);
      singletons -= c.length;
    }
    if (singletons) rv.set(1, singletons);
    return rv;
  }

  /**
   * Returns the set of elements of the array form.
   * @returns The set of elements of the array form.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.atoms`
   */
  atoms(): Set<number> {
    return new Set(this.#af);
  }

  /**
   * Creates a copy of this object.
   * @returns A copy of this object.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.copy`
   */
  copy(): Permutation {
    return afNew(this.arrayForm);
  }

  /**
   * Returns the array form (SymPy iter(p)).
   * @returns The array form (SymPy iter(p)).
   */
  [Symbol.iterator](): Iterator<number> {
    return this.arrayForm[Symbol.iterator]();
  }

  // ---- group operations -------------------------------------------------------

  /**
   * First apply p, then q; the ith value is q(p(i)). The shorter operand is padded.
   * @param other - The value to combine with or compare against.
   * @returns The resulting permutation.
   * @throws TypeError when the operand is not a permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__mul__`
   */
  override mul(other: ExprLike): Permutation {
    if (!(other instanceof Permutation)) throw new TypeError('a Permutation can only be multiplied by a Permutation');
    const a = this.arrayForm;
    const b = other.arrayForm;
    if (b.length === 0) return afNew(a);
    for (let i = b.length; i < a.length; i++) b.push(i);
    return afNew([...a.map((i) => at(b, i)), ...b.slice(a.length)]);
  }

  /**
   * The nth power (n may be negative).
   * @param n - The exponent.
   * @returns The resulting permutation.
   * @throws NotImplementedError when the exponent is a permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__pow__`
   */
  override pow(n: ExprLike): Permutation {
    if (n instanceof Permutation) throw new NotImplementedError('p**p is not defined; do you mean p^p (conjugate)?');
    return afNew(afPow(this.#af, toBig(n)));
  }

  /**
   * The inverse permutation.
   * @returns The resulting permutation.
   */
  inverse(): Permutation {
    return afNew(afInvert(this.#af));
  }

  /**
   * The conjugate ~h*p*h (sizes must agree), so that p^q^r is
   * p^(q*r).
   * @param h - The group element on which to operate.
   * @returns The resulting permutation.
   * @throws RangeError when the operand sizes differ.
   */
  xor(h: Permutation): Permutation {
    if (this.size !== h.size) throw new RangeError('The permutations must be of equal size.');
    const a = new Array<number>(this.size).fill(0);
    const hf = h.#af;
    const p = this.#af;
    for (let i = 0; i < this.size; i++) a[at(hf, i)] = at(hf, at(p, i));
    return afNew(a);
  }

  /**
   * Moves forward in lexicographic order by the given number of permutations.
   * @param k - The index of the selected element.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__add__`
   */
  override add(k: ExprLike): Permutation {
    const rank = pmod(this.rank() + toBig(k), this.cardinality);
    const rv = Permutation.unrankLex(this.size, rank);
    rv.#rank = rank;
    return rv;
  }

  /**
   * Moves backward in lexicographic order by the given number of permutations.
   * @param k - The index of the selected element.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__sub__`
   */
  override sub(k: ExprLike): Permutation {
    return this.add(-toBig(k));
  }

  /**
   * Reports that division is undefined for permutations.
   * @param _o - The other permutation.
   * @returns This operation always throws.
   * @throws TypeError when division of permutations is requested.
   */
  override div(_o: ExprLike): Expr {
    throw new TypeError('unsupported operand type for /: Permutation');
  }

  /**
   * Reports that arithmetic negation is undefined for a permutation.
   * @returns This operation always throws.
   * @throws TypeError when arithmetic negation of a permutation is requested.
   */
  override neg(): Expr {
    throw new TypeError('bad operand type for unary -: Permutation');
  }

  /**
   * The permutation whose ith value is
   * a(b(c(i))); items after the first may be array or cyclic forms.
   * @param first - The first permutation in the product.
   * @param rest - The remaining factors in order.
   * @returns The permutation whose ith value is a(b(c(i))).
   * @see SymPy `sympy.combinatorics.permutations.Permutation.rmul`
   */
  static rmul(first: Permutation, ...rest: PermutationInput[]): Permutation {
    let rv = first;
    for (const r of rest) rv = new Permutation(r).mul(rv);
    return rv;
  }

  /**
   * Rmul of Permutations through their array forms.
   * @param args - The operands in their defining order.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.rmul_with_af`
   */
  static rmulWithAf(...args: Permutation[]): Permutation {
    return afNew(afRmuln(...args.map((p) => p.#af)));
  }

  /**
   * Other*~self.
   * @param other - The value to combine with or compare against.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.mul_inv`
   */
  mulInv(other: Permutation): Permutation {
    return afNew(afRmul(afInvert(this.#af), other.#af));
  }

  /**
   * Tests whether multiplication by the two permutations is independent of their order.
   * @param other - The value to combine with or compare against.
   * @returns Whether both orders of composition give the same permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.commutes_with`
   */
  commutesWith(other: Permutation): boolean {
    return afCommutesWith(this.#af, other.#af);
  }

  /**
   * Forms the commutator of two permutations of the same degree.
   * @param x - The element to examine.
   * @returns The commutator of two permutations of the same degree.
   * @throws RangeError when the operand sizes differ.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.commutator`
   */
  commutator(x: Permutation): Permutation {
    const a = this.#af;
    const b = x.#af;
    const n = a.length;
    if (b.length !== n) throw new RangeError('The permutations must be of equal size.');
    const inva = afInvert(a);
    const invb = afInvert(b);
    return afNew(invb.map((i) => at(a, at(b, at(inva, i)))));
  }

  // ---- application -------------------------------------------------------------

  /**
   * Returns the image of the index i.
   * @param i - The zero-based position in the sequence.
   * @param seq - The sequence whose sorted order determines the images.
   * @param cycle - The cycle to apply.
   * @returns The image of the index i.
   * @throws TypeError when the operand sizes differ or the index is outside the permutation or is not an integer.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__call__`
   */
  call(i: number | bigint): number;
  /**
   * Rearranges a sequence by the permutation's array form. The item at position `i` in the
   * result is the input item at the image of `i`.
   *
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__call__`
   */
  call<T>(seq: readonly T[]): T[];
  /**
   * Returns the characters of a string in the order given by the permutation's array form.
   *
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__call__`
   */
  call(seq: string): string[];
  /**
   * Composes this permutation with the cycle through the supplied points, applying the cycle
   * second.
   *
   * @see SymPy `sympy.combinatorics.permutations.Permutation.__call__`
   */
  call(...cycle: (number | bigint)[]): Permutation;
  call(...i: readonly unknown[]): unknown {
    if (i.length === 1) {
      const x = i[0];
      if (typeof x === 'string' || Array.isArray(x)) {
        const seq: readonly unknown[] = typeof x === 'string' ? Array.from(x) : (x as readonly unknown[]);
        if (seq.length !== this.size) throw new TypeError(`${String(x)} should have the length ${this.size}.`);
        return this.#af.map((j) => seq[j]);
      }
      const k = asInt(x);
      if (k < 0 || k >= this.size) throw new TypeError(`${k} should be an integer between 0 and ${this.size - 1}`);
      return this.#af[k];
    }
    return this.mul(new Permutation(new Cycle(...i.map((v) => asInt(v))), { size: this.size }));
  }

  /**
   * The image of an integer i as an Integer, or an
   * unevaluated AppliedPermutation for a symbolic i.
   * @param i - The zero-based position in the sequence.
   * @returns The image of an integer i as an Integer.
   * @throws NotImplementedError when the index is not an integer or the index is outside the permutation or is not an integer.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.apply`
   */
  apply(i: ExprLike): Expr {
    const x = sympify(i);
    if (isIntegerQ(x) === false) throw new NotImplementedError(`${x.toString()} should be an integer.`);
    const n = this.size;
    if (isNegative(x) === true || isNonNegative(add(x, -n)) === true) {
      throw new NotImplementedError(`${x.toString()} should be an integer between 0 and ${n - 1}`);
    }
    if (x instanceof Rational) return Rational.of(at(this.#af, Number(x.p)));
    return new AppliedPermutation(this, x);
  }

  // ---- Basic methods ---------------------------------------------------------------
  // SymPy's Permutation is an Atom: these are the shared Basic implementations of the core.

  /**
   * A stub to allow Basic args (like Tuple) to be skipped when computing
   * the content and primitive components of an expression.
   * @param opts - The options controlling as content primitive.
   * @returns A stub to allow Basic args (like Tuple) to be skipped when computing the content and primitive components of an expression.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.as_content_primitive`
   */
  asContentPrimitive(opts: { radical?: boolean; clear?: boolean } = {}): [Rational, Expr] {
    return asContentPrimitive(this, opts);
  }

  /**
   * The permutation itself (it binds no symbols).
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.as_dummy`
   */
  asDummy(): Permutation {
    return this;
  }

  /**
   * Supplies the class key used to order permutation atoms.
   * @returns The ordering key `[2, 0, 'Permutation']`.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.class_key`
   */
  static classKey(): [number, number, string] {
    return [2, 0, 'Permutation'];
  }

  /**
   * The canonical sort key, with the class key of an Atom.
   * @returns The canonical sort key.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.sort_key`
   */
  sortKey(): Key[] {
    return [Permutation.classKey(), ...expectType(sortKey(this), isKeyList).slice(1)];
  }

  /**
   * Compares the expression classes and then the permutation arrays lexicographically.
   * @param other - The value to combine with or compare against.
   * @returns The compare.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.compare`
   */
  compare(other: Expr): number {
    // SymPy _cmp_name: a class missing from ordering_of_classes (Permutation, and the extension classes
    // here) sorts after the listed core classes and by name among the unlisted ones
    if (!(other instanceof Permutation)) return other instanceof ExtensionExpr ? Math.sign(pyCompare('Permutation', other.name)) : 1;
    const a = this.#af;
    const b = other.#af;
    // SymPy compares the hashable contents (the array forms) by length, then item by item
    if (a.length !== b.length) return a.length > b.length ? 1 : -1;
    const i = a.findIndex((x, k) => x !== b[k]);
    return i < 0 ? 0 : at(a, i) > at(b, i) ? 1 : -1;
  }

  /**
   * Tests whether a minus sign can be factored out of the permutation.
   * @returns Always `false` for a permutation atom.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.could_extract_minus_sign`
   */
  couldExtractMinusSign(): boolean {
    return couldExtractMinusSign(this);
  }

  /**
   * Returns the number of subexpressions matching the query (the permutation itself or nothing).
   * @param query - The pattern or predicate to match.
   * @returns The number of subexpressions matching the query (the permutation itself or nothing).
   * @see SymPy `sympy.combinatorics.permutations.Permutation.count`
   */
  count(query: Query): number {
    return count(this, query);
  }

  /**
   * Counts the symbolic operations in this atomic permutation.
   * @param opts - The options controlling count ops.
   * @returns Zero, as a symbolic integer when visual output is requested.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.count_ops`
   */
  countOps(opts: { visual?: boolean } = {}): number | Expr {
    return opts.visual ? countOps(this, { visual: true }) : countOps(this);
  }

  /**
   * The permutation itself.
   * @returns The evaluated expression.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.doit`
   */
  doit(): Permutation {
    return this;
  }

  /**
   * Structural equality up to dummy symbols.
   * @param other - The value to combine with or compare against.
   * @param symbol - The symbol to treat as a dummy for comparison.
   * @returns Whether both expressions agree up to the requested dummy-symbol substitution.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.dummy_eq`
   */
  dummyEq(other: ExprLike, symbol?: Expr): boolean {
    return dummyEq(this, other, symbol);
  }

  /**
   * The matching subexpressions.
   * @param query - The pattern or predicate to match.
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.find`
   */
  find(query: Query): Expr[] {
    return find(this, query);
  }

  /**
   * Permutation(*args).
   * @param args - The operands in their defining order.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.fromiter`
   */
  static fromiter(args: Iterable<number | bigint | Expr>): Permutation {
    return new Permutation(...args);
  }

  /**
   * Whether a pattern is the permutation or one of its free symbols (it has none).
   * @param patterns - The expressions to search for.
   * @returns Whether any of the supplied patterns occurs freely.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.has_free`
   */
  hasFree(...patterns: ExprLike[]): boolean {
    return hasFree(this, ...patterns);
  }

  /**
   * Whether an item of s is the permutation or one of its free symbols.
   * @param items - The candidate free subexpressions.
   * @returns Whether the iterable includes an exact free occurrence.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.has_xfree`
   */
  hasXfree(items: Iterable<Expr>): boolean {
    return hasXfree(this, [...items]);
  }

  /**
   * The term ratio p/p is not defined, so this throws TypeError as in SymPy.
   * @param _k - The index of the selected element.
   * @returns Whether the object is hypergeometric.
   * @throws TypeError when division of permutations is requested.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_hypergeometric`
   */
  isHypergeometric(_k: Expr): boolean {
    throw new TypeError("unsupported operand type(s) for /: 'Permutation' and 'Permutation'");
  }

  /**
   * Structural equality.
   * @param b - The second operand.
   * @param approx - An optional comparison for approximate numbers.
   * @returns Whether the object is same.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_same`
   */
  isSame(b: unknown, approx?: (x: Expr, y: Expr) => boolean): boolean {
    return isSame(this, b, approx);
  }

  /**
   * The Wild assignments making pattern equal to the permutation, NoMatch when none.
   * @param pattern - The pattern to match against this expression.
   * @param opts - The options controlling match.
   * @returns The matched value, or `NoMatch` if there is no match.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.match`
   */
  match(pattern: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
    return match(this, pattern, opts);
  }

  /**
   * The assignments making the permutation (a pattern without Wilds) equal to expr ({} or NoMatch).
   * @param expr - The expression to transform.
   * @param opts - The options controlling matches.
   * @returns The matched value, or `NoMatch` if there is no match.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.matches`
   */
  matches(expr: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
    return match(expr, this, opts);
  }

  /**
   * Applies the permutation to the supplied point.
   * @param args - The operands in their defining order.
   * @returns The image of the point, or this permutation when called without arguments.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.rcall`
   */
  rcall(...args: (number | bigint)[]): number | Permutation {
    return args.length === 1 ? this.call(at(args, 0)) : this.call(...args);
  }

  /**
   * The permutation itself.
   * @param assumptions - The assumptions to apply.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.refine`
   */
  refine(assumptions: Assumption = true): Expr {
    return refine(this, assumptions);
  }

  /**
   * The permutation with matching subexpressions replaced.
   * @param query - The pattern or predicate to match.
   * @param value - The value represented by this object.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.replace`
   */
  replace(query: Query, value: Replacement): Expr {
    return expectType(replace(this, query, value), isExpr);
  }

  /**
   * Exact structural replacement.
   * @param rule - The mapping from subexpressions to replacements.
   * @returns The resulting symbolic expression.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.xreplace`
   */
  xreplace(rule: Substitution): Expr {
    return xreplace(this, rule);
  }

  // ---- properties ----------------------------------------------------------------

  /**
   * Counts the permutations of this degree.
   * @returns The factorial of the permutation size as a bigint.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.cardinality`
   */
  get cardinality(): bigint {
    return ifac(this.size);
  }

  /**
   * Computes the parity of the number of transpositions in the permutation.
   * @returns The parity of the number of transpositions in the permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.parity`
   */
  parity(): number {
    return afParity(this.#af);
  }

  /**
   * Checks if a permutation is even.
   * @returns Whether the object is even.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_even`
   */
  get isEven(): boolean {
    return !this.isOdd;
  }

  /**
   * Checks if a permutation is odd.
   * @returns Whether the object is odd.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_odd`
   */
  get isOdd(): boolean {
    return this.parity() % 2 === 1;
  }

  /**
   * The size is 1.
   * @returns Whether the object is singleton.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_Singleton`
   */
  get isSingleton(): boolean {
    return this.size === 1;
  }

  /**
   * The size is 0.
   * @returns Whether the object is empty.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_Empty`
   */
  get isEmpty(): boolean {
    return this.size === 0;
  }

  /**
   * No element is moved.
   * @returns Whether the object is identity.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.is_Identity`
   */
  get isIdentity(): boolean {
    return this.#af.every((v, i) => v === i);
  }

  /**
   * Computes the sign of the permutation.
   * @returns The sign of the permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.signature`
   */
  signature(): number {
    return this.isEven ? 1 : -1;
  }

  /**
   * The smallest positive n with p**n the identity, as an Integer.
   * @returns The smallest positive n with p**n the identity.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.order`
   */
  order(): Rational {
    let l = 1n;
    for (const c of this.cyclicForm) {
      const k = BigInt(c.length);
      l = (l * k) / bgcd(l, k);
    }
    return Rational.of(l);
  }

  /**
   * Returns the number of moved elements.
   * @returns The number of moved elements.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.length`
   */
  length(): number {
    return this.support().length;
  }

  /**
   * Returns the positions i with p[i] < p[i+1].
   * @returns The positions i with p[i] < p[i+1].
   * @see SymPy `sympy.combinatorics.permutations.Permutation.ascents`
   */
  ascents(): number[] {
    const a = this.#af;
    const out: number[] = [];
    for (let i = 0; i < a.length - 1; i++) if (at(a, i) < at(a, i + 1)) out.push(i);
    return out;
  }

  /**
   * Returns the positions i with p[i] > p[i+1].
   * @returns The positions i with p[i] > p[i+1].
   * @see SymPy `sympy.combinatorics.permutations.Permutation.descents`
   */
  descents(): number[] {
    const a = this.#af;
    const out: number[] = [];
    for (let i = 0; i < a.length - 1; i++) if (at(a, i) > at(a, i + 1)) out.push(i);
    return out;
  }

  /**
   * Finds the largest point moved by the permutation.
   * @returns The largest moved point, or zero for the empty permutation.
   * @throws RangeError when the collection is empty.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.max`
   */
  max(): number {
    const a = this.#af;
    if (a.length === 0) return 0;
    const moved = a.filter((v, i) => v !== i);
    if (moved.length === 0) throw new RangeError('max() iterable argument is empty');
    return Math.max(...moved);
  }

  /**
   * Finds the smallest point moved by the permutation.
   * @returns The smallest moved point, or zero for the empty permutation.
   * @throws RangeError when the collection is empty.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.min`
   */
  min(): number {
    const a = this.#af;
    if (a.length === 0) return 0;
    const moved = a.filter((v, i) => v !== i);
    if (moved.length === 0) throw new RangeError('min() iterable argument is empty');
    return Math.min(...moved);
  }

  /**
   * Returns the number of pairs i < j with p[i] > p[j].
   * @returns The number of pairs i < j with p[i] > p[j].
   * @see SymPy `sympy.combinatorics.permutations.Permutation.inversions`
   */
  inversions(): number {
    const a = this.#af;
    const n = a.length;
    if (n < 130) {
      let inv = 0;
      for (let i = 0; i < n - 1; i++) for (let j = i + 1; j < n; j++) if (at(a, i) > at(a, j)) inv++;
      return inv;
    }
    // merge sort counting
    let arr = [...a];
    let tmp = new Array<number>(n).fill(0);
    let inv = 0;
    for (let w = 1; w < n; w *= 2) {
      for (let lo = 0; lo < n; lo += 2 * w) {
        const mid = Math.min(lo + w, n);
        const hi = Math.min(lo + 2 * w, n);
        let i = lo;
        let j = mid;
        let k = lo;
        while (i < mid && j < hi) {
          if (at(arr, i) < at(arr, j)) tmp[k++] = at(arr, i++);
          else {
            tmp[k++] = at(arr, j++);
            inv += mid - i;
          }
        }
        while (i < mid) tmp[k++] = at(arr, i++);
        while (j < hi) tmp[k++] = at(arr, j++);
      }
      [arr, tmp] = [tmp, arr];
    }
    return inv;
  }

  /**
   * Returns the Lehmer code without its last (always 0) entry.
   * @returns The Lehmer code without its last (always 0) entry.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.inversion_vector`
   */
  inversionVector(): number[] {
    const a = this.#af;
    const n = a.length;
    const out: number[] = [];
    for (let i = 0; i < n - 1; i++) {
      let v = 0;
      for (let j = i + 1; j < n; j++) if (at(a, j) < at(a, i)) v++;
      out.push(v);
    }
    return out;
  }

  /**
   * Returns the sum of the positions j with p[j] > p[j+1].
   * @returns The sum of the positions j with p[j] > p[j+1].
   * @see SymPy `sympy.combinatorics.permutations.Permutation.index`
   */
  index(): number {
    return this.descents().reduce((s, j) => s + j, 0);
  }

  /**
   * Returns the maximal ascending runs of the array form.
   * @returns The maximal ascending runs of the array form.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.runs`
   */
  runs(): number[][] {
    const a = this.#af;
    if (a.length === 0) return [];
    const out: number[][] = [];
    let run = [at(a, 0)];
    for (let i = 1; i < a.length; i++) {
      const e = at(a, i);
      if (e > last(run)) run.push(e);
      else {
        out.push(run);
        run = [e];
      }
    }
    out.push(run);
    return out;
  }

  /**
   * Returns the permutation as a product of transpositions.
   * @returns The permutation as a product of transpositions.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.transpositions`
   */
  transpositions(): [number, number][] {
    const res: [number, number][] = [];
    for (const x of this.cyclicForm) {
      const first = at(x, 0);
      if (x.length === 2) res.push([first, at(x, 1)]);
      else for (let k = x.length - 1; k > 0; k--) res.push([first, at(x, k)]);
    }
    return res;
  }

  /**
   * The same permutation on n elements; RangeError when a
   * cycle would be broken.
   * @param n - The number of positions.
   * @returns The same permutation on n elements.
   * @throws RangeError when truncation would split a nontrivial cycle.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.resize`
   */
  resize(n: number): Permutation {
    const l = this.size;
    if (n > l) return afNew([...this.arrayForm, ...Array.from({ length: n - l }, (_, i) => l + i)]);
    if (n < l) {
      const kept: number[][] = [];
      for (const cycle of this.fullCyclicForm) {
        const lo = Math.min(...cycle);
        const hi = Math.max(...cycle);
        if (lo <= n - 1) {
          if (hi > n - 1) {
            throw new RangeError(`The permutation cannot be resized to ${n} because the cycle (${cycle.join(', ')}) may break.`);
          }
          kept.push(cycle);
        }
      }
      return new Permutation(kept);
    }
    return this;
  }

  // ---- ranking --------------------------------------------------------------------

  /**
   * Returns the lexicographic rank (the identity has rank 0).
   * @returns The lexicographic rank (the identity has rank 0).
   * @see SymPy `sympy.combinatorics.permutations.Permutation.rank`
   */
  rank(): bigint {
    if (this.#rank !== undefined) return this.#rank;
    let rank = 0n;
    const rho = this.arrayForm;
    const size = this.size;
    let n = size - 1;
    let psize = ifac(n);
    for (let j = 0; j < size - 1; j++) {
      rank += BigInt(at(rho, j)) * psize;
      for (let i = j + 1; i < size; i++) if (at(rho, i) > at(rho, j)) rho[i] = at(rho, i) - 1;
      psize /= BigInt(n);
      n--;
    }
    this.#rank = rank;
    return rank;
  }

  /**
   * The permutation of the given lexicographic rank.
   * @param size - The number of positions.
   * @param rank - The zero-based position in the enumeration.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.unrank_lex`
   * @example
   * ```ts
   * import { Permutation } from '@symjs/symjs';
   * Permutation.unrankLex(3, 4).arrayForm; // => [2, 0, 1]
   * ```
   */
  static unrankLex(size: number, rank: number | bigint): Permutation {
    const perm = new Array<number>(size).fill(0);
    let r = BigInt(rank);
    let psize = 1n;
    for (let i = 0; i < size; i++) {
      const newPsize = psize * BigInt(i + 1);
      const d = pmod(r, newPsize) / psize;
      r -= d * psize;
      const dn = Number(d);
      perm[size - i - 1] = dn;
      for (let j = size - i; j < size; j++) if (at(perm, j) > dn - 1) perm[j] = at(perm, j) + 1;
      psize = newPsize;
    }
    return afNew(perm);
  }

  /**
   * The next permutation in lexicographic order, NoMatch after the last one.
   * @returns The matched value, or `NoMatch` if there is no match.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.next_lex`
   */
  nextLex(): Permutation | NoMatchResult {
    const perm = this.arrayForm;
    const n = perm.length;
    let i = n - 2;
    while (i >= 0 && at(perm, i + 1) < at(perm, i)) i--;
    if (i < 0) return NoMatch;
    let j = n - 1;
    while (at(perm, j) < at(perm, i)) j--;
    [perm[i], perm[j]] = [at(perm, j), at(perm, i)];
    i++;
    j = n - 1;
    while (i < j) {
      [perm[i], perm[j]] = [at(perm, j), at(perm, i)];
      i++;
      j--;
    }
    return afNew(perm);
  }

  /**
   * Myrvold-Ruskey unranking (r is taken modulo n!).
   * @param n - The number of positions.
   * @param r - The rank in Myrvold–Ruskey order.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.unrank_nonlex`
   */
  static unrankNonlex(n: number, r: number | bigint): Permutation {
    const a = Array.from({ length: n }, (_, i) => i);
    let rr = pmod(BigInt(r), ifac(n));
    for (let m = n; m > 0; m--) {
      const bm = BigInt(m);
      const k = Number(pmod(rr, bm));
      [a[m - 1], a[k]] = [at(a, k), at(a, m - 1)];
      rr /= bm;
    }
    return afNew(a);
  }

  /**
   * Returns the Myrvold-Ruskey rank.
   * @param invPerm - The inverse permutation in array form, if already available.
   * @returns The Myrvold-Ruskey rank.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.rank_nonlex`
   */
  rankNonlex(invPerm?: readonly number[]): bigint {
    const inv = invPerm ? [...invPerm] : afInvert(this.#af);
    if (inv.length === 0) return 0n;
    const perm = this.arrayForm;
    const rank1 = (n: number): bigint => {
      if (n === 1) return 0n;
      const s = at(perm, n - 1);
      const t = at(inv, n - 1);
      [perm[n - 1], perm[t]] = [at(perm, t), s];
      [inv[n - 1], inv[s]] = [at(inv, s), t];
      return BigInt(s) + BigInt(n) * rank1(n - 1);
    };
    return rank1(perm.length);
  }

  /**
   * The next permutation in Myrvold-Ruskey order, NoMatch after the last one.
   * @returns The matched value, or `NoMatch` if there is no match.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.next_nonlex`
   */
  nextNonlex(): Permutation | NoMatchResult {
    const r = this.rankNonlex();
    if (r === this.cardinality - 1n) return NoMatch;
    return Permutation.unrankNonlex(this.size, r + 1n);
  }

  /**
   * Returns the rank in Trotter-Johnson (minimal change) order.
   * @returns The rank in Trotter-Johnson (minimal change) order.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.rank_trotterjohnson`
   */
  rankTrotterjohnson(): bigint {
    const perm = this.#af;
    if (perm.length === 0 || this.isIdentity) return 0n;
    if (perm.length === 2 && perm[0] === 1 && perm[1] === 0) return 1n;
    const n = this.size;
    let rank = 0n;
    for (let j = 1; j < n; j++) {
      let k = 1;
      let i = 0;
      while (perm[i] !== j) {
        if (at(perm, i) < j) k++;
        i++;
      }
      const j1 = BigInt(j + 1);
      rank = rank % 2n === 0n ? j1 * rank + j1 - BigInt(k) : j1 * rank + BigInt(k) - 1n;
    }
    return rank;
  }

  /**
   * Trotter Johnson permutation unranking.
   * @param size - The number of positions.
   * @param rank - The zero-based position in the enumeration.
   * @returns The resulting permutation.
   * @throws RangeError when the rank is outside the enumeration.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.unrank_trotterjohnson`
   */
  static unrankTrotterjohnson(size: number, rank: number | bigint): Permutation {
    const perm = new Array<number>(size).fill(0);
    const r = BigInt(rank);
    let r2 = 0n;
    const nf = ifac(size);
    // SymPy gives a list that is not a permutation ([0, 0, 2] for size 3 and rank -1) or an IndexError
    if (r < 0n || r >= nf) throw new RangeError(`rank must be in [0, ${nf}), got ${r}`);
    let pj = 1n;
    for (let j = 2; j <= size; j++) {
      pj *= BigInt(j);
      const r1 = (r * pj) / nf;
      const k = Number(r1 - BigInt(j) * r2);
      if (r2 % 2n === 0n) {
        for (let i = j - 1; i > j - k - 1; i--) perm[i] = pyIndex(perm, i - 1);
        perm[j - k - 1] = j - 1;
      } else {
        for (let i = j - 1; i > k; i--) perm[i] = pyIndex(perm, i - 1);
        perm[k] = j - 1;
      }
      r2 = r1;
    }
    return afNew(perm);
  }

  /**
   * The next permutation in Trotter-Johnson order, NoMatch after the last one.
   * @returns The matched value, or `NoMatch` if there is no match.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.next_trotterjohnson`
   */
  nextTrotterjohnson(): Permutation | NoMatchResult {
    const pi = this.arrayForm;
    const n = pi.length;
    let st = 0;
    const rho = [...pi];
    let done = false;
    let m = n - 1;
    while (m > 0 && !done) {
      const d = rho.indexOf(m);
      for (let i = d; i < m; i++) rho[i] = at(rho, i + 1);
      const par = afParity(rho.slice(0, m));
      if (par === 1) {
        if (d === m) m--;
        else {
          [pi[st + d], pi[st + d + 1]] = [at(pi, st + d + 1), at(pi, st + d)];
          done = true;
        }
      } else if (d === 0) {
        m--;
        st++;
      } else {
        [pi[st + d], pi[st + d - 1]] = [at(pi, st + d - 1), at(pi, st + d)];
        done = true;
      }
    }
    if (m === 0) return NoMatch;
    return afNew(pi);
  }

  // ---- distances -------------------------------------------------------------------

  #precedence(): number[][] {
    const n = this.size;
    const m = Array.from({ length: n }, () => new Array<number>(n).fill(0));
    const perm = this.#af;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) at(m, at(perm, i))[at(perm, j)] = 1;
    return m;
  }

  #adjacency(): number[][] {
    const n = this.size;
    const m = Array.from({ length: n }, () => new Array<number>(n).fill(0));
    const perm = this.#af;
    for (let i = 0; i < n - 1; i++) at(m, at(perm, i))[at(perm, i + 1)] = 1;
    return m;
  }

  /**
   * M[i, j] = 1 when i precedes j in the array form.
   * @returns The resulting matrix.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.get_precedence_matrix`
   */
  getPrecedenceMatrix(): Matrix {
    return Matrix.of(this.#precedence());
  }

  /**
   * Computes the precedence distance between two permutations.
   * @param other - The value to combine with or compare against.
   * @returns The precedence distance between two permutations.
   * @throws RangeError when the operand sizes differ.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.get_precedence_distance`
   */
  getPrecedenceDistance(other: Permutation): number {
    if (this.size !== other.size) throw new RangeError('The permutations must be of equal size.');
    const a = this.#precedence();
    const b = other.#precedence();
    const n = this.size;
    let nPrec = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j && at(at(a, i), j) * at(at(b, i), j) === 1) nPrec++;
    return Math.floor((n * Math.max(n - 1, 0)) / 2) - nPrec;
  }

  /**
   * M[i, j] = 1 when j immediately follows i in the array form.
   * @returns The resulting matrix.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.get_adjacency_matrix`
   */
  getAdjacencyMatrix(): Matrix {
    return Matrix.of(this.#adjacency());
  }

  /**
   * Computes the adjacency distance between two permutations.
   * @param other - The value to combine with or compare against.
   * @returns The adjacency distance between two permutations.
   * @throws RangeError when the operand sizes differ.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.get_adjacency_distance`
   */
  getAdjacencyDistance(other: Permutation): number {
    if (this.size !== other.size) throw new RangeError('The permutations must be of the same size.');
    const a = this.#adjacency();
    const b = other.#adjacency();
    const n = this.size;
    let nAdj = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j && at(at(a, i), j) * at(at(b, i), j) === 1) nAdj++;
    return n - nAdj - 1;
  }

  /**
   * Returns the sum of |p[i] - q[i]|.
   * @param other - The value to combine with or compare against.
   * @returns The sum of |p[i] - q[i]|.
   * @throws RangeError when the operand sizes differ.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.get_positional_distance`
   */
  getPositionalDistance(other: Permutation): number {
    const a = this.#af;
    const b = other.#af;
    if (a.length !== b.length) throw new RangeError('The permutations must be of the same size.');
    return a.reduce((s, ai, i) => s + Math.abs(ai - at(b, i)), 0);
  }

  // ---- constructors --------------------------------------------------------------------

  /**
   * Range(n) in the order in which
   * every mth item is selected, the last s items taken in order.
   * @param m - The step between successive selections.
   * @param n - The number of positions.
   * @param s - The input sequence.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.josephus`
   */
  static josephus(m: number, n: number, s = 1): Permutation {
    const q = Array.from({ length: n }, (_, i) => i);
    const perm: number[] = [];
    while (q.length > Math.max(s, 1)) {
      for (let dp = 0; dp < m - 1; dp++) q.push(defined(q.shift()));
      perm.push(defined(q.shift()));
    }
    perm.push(...q);
    return new Permutation(perm);
  }

  /**
   * Calculates the permutation from the inversion vector.
   * @param inversion - The inversion counts in position order.
   * @returns The resulting permutation.
   * @throws RangeError when the inversion vector contains an invalid digit.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.from_inversion_vector`
   */
  static fromInversionVector(inversion: readonly number[]): Permutation {
    const size = inversion.length;
    const N = Array.from({ length: size + 1 }, (_, i) => i);
    const perm: number[] = [];
    for (let k = 0; k < size; k++) {
      let idx = at(inversion, k);
      if (idx < 0) idx += N.length;
      if (idx < 0 || idx >= N.length) throw new RangeError('The inversion vector is not valid.');
      perm.push(at(N, idx));
      N.splice(idx, 1);
    }
    perm.push(...N);
    return afNew(perm);
  }

  /**
   * The permutation that
   * arranges the sorted elements of i into i (a stable sort, ties by position).
   * @param seq - The sequence whose sorted order determines the images.
   * @param key - The ordering key used to sort the elements.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.from_sequence`
   */
  static fromSequence<T>(seq: readonly T[] | string, key?: (x: T) => unknown): Permutation {
    const items: readonly unknown[] = typeof seq === 'string' ? Array.from(seq) : seq;
    const ic = items.map((x, i) => [x, i] as const);
    if (key) {
      // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- items are seq's elements (or a string's characters, which the signature cannot tie to T)
      const keys = ic.map(([x]) => key(x as T));
      ic.sort((u, v) => pyCompare(keys[u[1]], keys[v[1]]) || u[1] - v[1]);
    } else ic.sort((u, v) => pyCompare(u[0], v[0]) || u[1] - v[1]);
    return new Permutation(ic.map(([, i]) => i)).inverse();
  }

  /**
   * A uniformly random permutation of size n
   * (Fisher-Yates), from Math.random, a seed or a given generator.
   * @param n - The number of positions.
   * @param opts - The settings described by {@link RandomOptions}.
   * @returns The resulting permutation.
   * @see SymPy `sympy.combinatorics.permutations.Permutation.random`
   */
  static random(n: number, opts: RandomOptions = {}): Permutation {
    const rnd = opts.prng ?? (opts.seed !== undefined ? seeded(opts.seed) : Math.random);
    const a = Array.from({ length: n }, (_, i) => i);
    for (let i = n - 1; i > 0; i--) {
      const j = Math.floor(rnd() * (i + 1));
      [a[i], a[j]] = [at(a, j), at(a, i)];
    }
    return afNew(a);
  }
}

/**
 * An alias of Permutation.
 * @see SymPy `sympy.combinatorics.permutations.Permutation`
 * @example
 * ```ts
 * import { Perm } from '@symjs/symjs';
 * new Perm(5); // => (5)
 * ```
 */
export const Perm = Permutation;

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

/**
 * Formats a permutation in cycle or array notation.
 * @param p - The permutation to examine.
 * @param opts - The settings described by {@link PermutationPrintOptions}.
 * @returns The resulting text.
 * @see SymPy `sympy.printing.str.StrPrinter._print_Permutation`
 * @example
 * ```ts
 * import { Permutation, permutationStr } from '@symjs/symjs';
 * permutationStr(new Permutation([0, 2, 1])); // => (1 2)
 * ```
 */
export function permutationStr(p: Permutation, opts: PermutationPrintOptions = {}): string {
  if (opts.permCyclic ?? true) {
    if (p.size === 0) return '()';
    return cyclicBody(p, ' ');
  }
  const s = p.support();
  const af = p.arrayForm;
  if (s.length === 0) return p.size < 5 ? `Permutation(${listStr(af)})` : `Permutation([], size=${p.size})`;
  const trim = `${listStr(af.slice(0, last(s) + 1))}, size=${p.size}`;
  const full = listStr(af);
  return `Permutation(${trim.length < full.length ? trim : full})`;
}

/**
 * Formats a permutation as a constructor expression.
 * @param p - The permutation to examine.
 * @param opts - The settings described by {@link PermutationPrintOptions}.
 * @returns The resulting text.
 * @see SymPy `sympy.printing.repr.ReprPrinter._print_Permutation`
 * @example
 * ```ts
 * import { Permutation, permutationRepr } from '@symjs/symjs';
 * permutationRepr(new Permutation([0, 2, 1])); // => Permutation(1, 2)
 * ```
 */
export function permutationRepr(p: Permutation, opts: PermutationPrintOptions = {}): string {
  if (!(opts.permCyclic ?? true)) return permutationStr(p, opts);
  if (p.size === 0) return 'Permutation()';
  return `Permutation${cyclicBody(p, ', ')}`;
}

/**
 * Formats the cycles or two-line array of a permutation in LaTeX.
 * @param p - The permutation to examine.
 * @param opts - The settings described by {@link PermutationPrintOptions}.
 * @returns The resulting text.
 * @see SymPy `sympy.printing.latex.LatexPrinter._print_Permutation`
 * @example
 * ```ts
 * import { Permutation, permutationLatex } from '@symjs/symjs';
 * permutationLatex(new Permutation([0, 2, 1])); // => \left( 1\; 2\right)
 * ```
 */
export function permutationLatex(p: Permutation, opts: PermutationPrintOptions = {}): string {
  if (p.size === 0) return '\\left( \\right)';
  if (opts.permCyclic ?? true) return cycleLatex(p);
  const lower = p.arrayForm.join(' & ');
  const upper = Array.from({ length: p.size }, (_, i) => i).join(' & ');
  return `\\begin{pmatrix} ${upper} \\\\ ${lower} \\end{pmatrix}`;
}

/** The cycles of p, with the largest element first as a singleton when it is fixed. */
function cyclicBody(p: Permutation, sep: string): string {
  const cycles = p.cyclicForm;
  const big = p.size - 1;
  const body = cycles.map((c) => `(${c.join(sep)})`).join('');
  return cycles.some((c) => c.includes(big)) ? body : `(${big})${body}`;
}

// ---------------------------------------------------------------------------
// AppliedPermutation
// ---------------------------------------------------------------------------

/**
 * A permutation applied to a symbolic
 * integer; it evaluates once x becomes an Integer (for example by subs).
 * @see SymPy `sympy.combinatorics.permutations.AppliedPermutation`
 * @example
 * ```ts
 * import { AppliedPermutation, Perm } from '@symjs/symjs';
 * AppliedPermutation.of(new Perm([1, 2, 0]), 1, { evaluate: true }); // => 2
 * ```
 */
export class AppliedPermutation extends ExtensionExpr {
  /**
   * Constructs an `AppliedPermutation`.
   * @param perm - The permutation to apply.
   * @param x - The element to examine.
   * @internal
   */
  constructor(perm: Permutation, x: Expr) {
    super('AppliedPermutation', [perm, x]);
  }

  /**
   * Evaluates to an Integer when x is one (unless evaluate is false).
   * @param perm - The permutation to apply.
   * @param x - The element to examine.
   * @param opts - The options controlling of.
   * @returns The resulting symbolic expression.
   */
  static of(perm: Permutation, x: ExprLike, opts: { evaluate?: boolean } = {}): Expr {
    const e = sympify(x);
    if ((opts.evaluate ?? true) && e instanceof Rational && e.q === 1n) return perm.apply(e);
    return new AppliedPermutation(perm, e);
  }

  /**
   * Gets the permutation.
   * @returns The permutation.
   */
  get perm(): Permutation {
    return cast(this.args[0], Permutation, 'AppliedPermutation perm');
  }

  /**
   * Gets the argument.
   * @returns The argument.
   */
  get x(): Expr {
    return at(this.args, 1);
  }

  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   * @throws TypeError when the operands do not specify a permutation and its argument.
   */
  withArgs(args: readonly Expr[]): Expr {
    const [perm, x] = args;
    if (!(perm instanceof Permutation) || x === undefined) throw new TypeError('AppliedPermutation needs a Permutation and an argument');
    return AppliedPermutation.of(perm, x);
  }

  /**
   * Formats the expression in LaTeX.
   * @param print - Formats a child expression.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\sigma_{${print(this.perm)}}(${print(this.x)})`;
  }
}
