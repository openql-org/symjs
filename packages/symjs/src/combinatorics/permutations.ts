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
import { Expr, ExtensionExpr, Rational } from '../core/nodes';
import { add, sympify } from '../core/ops';
import type { NoMatchResult } from '../core/truth';
import { NoMatch } from '../core/truth';
import { Matrix } from '../matrices/matrix';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

/** SymPy _af_rmul(a, b): the product b*a of array forms; the ith value is a[b[i]]. */
export function afRmul(a: readonly number[], b: readonly number[]): number[] {
  return b.map((i) => pyIndex(a, i));
}

/** SymPy _af_rmuln(a, b, c, ...): the product ...*c*b*a of array forms; the ith value is a[b[c[i]]]. */
export function afRmuln(...abc: (readonly number[])[]): number[] {
  if (abc.length === 0) throw new RangeError('String must not be empty');
  let rv = [...last(abc)];
  for (let k = abc.length - 2; k >= 0; k--) rv = afRmul(at(abc, k), rv);
  return rv;
}

/** SymPy _af_parity: the parity (0 or 1) of a permutation in array form. */
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

/** SymPy _af_invert: the inverse of a permutation in array form. */
export function afInvert(a: readonly number[]): number[] {
  const inv = new Array<number>(a.length).fill(0);
  a.forEach((ai, i) => {
    inv[ai] = i;
  });
  return inv;
}

/** SymPy _af_pow: the nth power of a permutation in array form. */
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

/** SymPy _af_commutes_with: whether the permutations with array forms a and b commute. */
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
 * SymPy Cycle: a disjoint-cycle mapping (a dict whose missing keys map to
 * themselves). `new Cycle(1, 2).call(2, 3)` is SymPy's Cycle(1, 2)(2, 3);
 * cycles are applied from left to right.
 */
export class Cycle implements Iterable<number> {
  readonly #map = new Map<number, number>();

  /** SymPy Cycle(*args): the cycle of the given integers, or a copy of a Permutation or Cycle. */
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

  /** SymPy cycle[i]: the image of i (i itself when i is not in the cycle). */
  get(i: number | bigint): number {
    const k = asInt(i);
    return this.#map.get(k) ?? k;
  }

  /** SymPy items(): the stored (key, value) pairs in insertion order. */
  items(): [number, number][] {
    return [...this.#map.entries()];
  }

  /** SymPy keys(): the stored keys in insertion order. */
  keys(): number[] {
    return [...this.#map.keys()];
  }

  /** Whether nothing is stored (SymPy `not cycle`). */
  get isEmpty(): boolean {
    return this.#map.size === 0;
  }

  /** SymPy size: one more than the largest stored element (0 when empty). */
  get size(): number {
    return this.#map.size === 0 ? 0 : Math.max(...this.#map.keys()) + 1;
  }

  /** SymPy cycle(*other): the product of this cycle followed by the cycle of `other`. */
  call(...other: CycleArgs): Cycle {
    const rv = new Cycle(...other);
    const keys = this.keys();
    const vals = keys.map((k) => rv.get(this.get(k)));
    keys.forEach((k, i) => rv.#map.set(k, at(vals, i)));
    return rv;
  }

  /**
   * SymPy list(size): the array form from 0 up to the larger of the largest
   * moved element and size; size -1 trims trailing unmoved elements.
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

  /** SymPy copy(). */
  copy(): Cycle {
    return new Cycle(this);
  }

  /** The array form (SymPy iter(cycle)). */
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

  /** SymPy str(cycle): (1 3 2), with the largest element shown as a singleton if needed. */
  toString(): string {
    return this.isEmpty ? '()' : this.#print(' ');
  }

  /** SymPy repr(cycle): Cycle(1, 3, 2). */
  repr(): string {
    return this.isEmpty ? 'Cycle()' : `Cycle${this.#print(', ')}`;
  }

  /** SymPy latex(cycle). */
  toLatex(): string {
    return this.size === 0 ? '\\left( \\right)' : cycleLatex(new Permutation(this));
  }
}

// ---------------------------------------------------------------------------
// Permutation
// ---------------------------------------------------------------------------

/** The size keyword of Permutation(...). */
export interface PermutationOptions {
  size?: number;
}

/** A single argument of Permutation(...): array form, cyclic form, a Cycle or a Permutation. */
export type PermutationInput = Permutation | Cycle | readonly number[] | readonly (readonly number[])[];

/** Options of Permutation.random: a seed or a generator of numbers in [0, 1). */
export interface RandomOptions {
  seed?: number;
  prng?: () => number;
}

/** Printer settings of the Permutation printers (SymPy perm_cyclic, default true). */
export interface PermutationPrintOptions {
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

/** Wrap an array form without validation (SymPy _af_new). */
function afNew(perm: number[]): Permutation {
  pendingAf = perm;
  return new Permutation();
}

/**
 * SymPy Permutation: a bijection of {0, ..., n-1}, built from its array
 * form (`new Permutation([0, 2, 1])`), its cyclic form
 * (`new Permutation([[1, 2]])`), the integers of one cycle
 * (`new Permutation(1, 2)`), a size (`new Permutation(3)` is the identity of
 * size 4), a Cycle or another Permutation, with an optional trailing
 * `{ size }`. It is an atomic expression that prints like SymPy's str,
 * e.g. `(1 2)`.
 */
export class Permutation extends ExtensionExpr implements Iterable<number> {
  readonly #af: number[];
  #cyclic: number[][] | undefined;
  #rank: bigint | undefined;

  /** SymPy Permutation(*cycle, size=...): the cycle of the integers, or the identity of size a + 1 for one integer. */
  constructor(...cycle: (number | bigint | Expr)[]);
  /** SymPy Permutation(*cycle, size=...). */
  constructor(...args: [...cycle: (number | bigint | Expr)[], options: PermutationOptions]);
  /** SymPy Permutation(arg, size=...) from an array form, cyclic form, Cycle or Permutation. */
  constructor(arg: PermutationInput, options?: PermutationOptions);
  constructor(...input: readonly unknown[]) {
    const af = pendingAf;
    pendingAf = undefined;
    super('Permutation', []);
    this.#af = af ?? parseArgs(input);
  }

  /** The node itself (a Permutation has no expression arguments). */
  withArgs(_args: readonly Expr[]): Expr {
    return this;
  }

  protected override computeKey(): string {
    return `Permutation(${this.#af.join(',')})`;
  }

  /** SymPy str(p) with perm_cyclic=True: (1 2), (3)(0 1), (). */
  override printStr(_print: (e: Expr) => string): string {
    return permutationStr(this);
  }

  /** SymPy latex(p): \left( 1\; 2\right). */
  override printLatex(_print: (e: Expr) => string): string {
    return permutationLatex(this);
  }

  // ---- forms ----------------------------------------------------------------

  /** SymPy array_form: a copy of the array form. */
  get arrayForm(): number[] {
    return [...this.#af];
  }

  /** SymPy size: the number of elements the permutation acts on. */
  get size(): number {
    return this.#af.length;
  }

  /**
   * SymPy list(size): the array form, extended to `size` when larger, or
   * with trailing unmoved elements trimmed otherwise (size -1 always trims).
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

  /** SymPy cyclic_form: the cycles without singletons, each starting with its smallest element, sorted. */
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

  /** SymPy full_cyclic_form: the cycles including singletons, sorted. */
  get fullCyclicForm(): number[][] {
    const cyc = this.cyclicForm;
    const moved = new Set(cyc.flat());
    for (let i = 0; i < this.size; i++) if (!moved.has(i)) cyc.push([i]);
    return cyc.sort(pyCompare);
  }

  /** SymPy support(): the elements i with p(i) != i. */
  support(): number[] {
    const out: number[] = [];
    this.#af.forEach((e, i) => {
      if (e !== i) out.push(i);
    });
    return out;
  }

  /** SymPy cycles: the number of cycles, singletons included. */
  get cycles(): number {
    return this.fullCyclicForm.length;
  }

  /** SymPy cycle_structure: a Map from cycle length to its multiplicity. */
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

  /** SymPy atoms(): the set of elements of the array form. */
  atoms(): Set<number> {
    return new Set(this.#af);
  }

  /** SymPy copy(). */
  copy(): Permutation {
    return afNew(this.arrayForm);
  }

  /** The array form (SymPy iter(p)). */
  [Symbol.iterator](): Iterator<number> {
    return this.arrayForm[Symbol.iterator]();
  }

  // ---- group operations -------------------------------------------------------

  /** SymPy p*q: first apply p, then q; the ith value is q(p(i)). The shorter operand is padded. */
  override mul(other: ExprLike): Permutation {
    if (!(other instanceof Permutation)) throw new TypeError('a Permutation can only be multiplied by a Permutation');
    const a = this.arrayForm;
    const b = other.arrayForm;
    if (b.length === 0) return afNew(a);
    for (let i = b.length; i < a.length; i++) b.push(i);
    return afNew([...a.map((i) => at(b, i)), ...b.slice(a.length)]);
  }

  /** SymPy p**n: the nth power (n may be negative). */
  override pow(n: ExprLike): Permutation {
    if (n instanceof Permutation) throw new NotImplementedError('p**p is not defined; do you mean p^p (conjugate)?');
    return afNew(afPow(this.#af, toBig(n)));
  }

  /** SymPy ~p: the inverse permutation. */
  inverse(): Permutation {
    return afNew(afInvert(this.#af));
  }

  /**
   * SymPy p^h: the conjugate ~h*p*h (sizes must agree), so that p^q^r is
   * p^(q*r).
   */
  xor(h: Permutation): Permutation {
    if (this.size !== h.size) throw new RangeError('The permutations must be of equal size.');
    const a = new Array<number>(this.size).fill(0);
    const hf = h.#af;
    const p = this.#af;
    for (let i = 0; i < this.size; i++) a[at(hf, i)] = at(hf, at(p, i));
    return afNew(a);
  }

  /** SymPy p + k: the permutation whose lexicographic rank is k higher (modulo the cardinality). */
  override add(k: ExprLike): Permutation {
    const rank = pmod(this.rank() + toBig(k), this.cardinality);
    const rv = Permutation.unrankLex(this.size, rank);
    rv.#rank = rank;
    return rv;
  }

  /** SymPy p - k: the permutation whose lexicographic rank is k lower. */
  override sub(k: ExprLike): Permutation {
    return this.add(-toBig(k));
  }

  /** Not defined for permutations (TypeError, as in SymPy). */
  override div(_o: ExprLike): Expr {
    throw new TypeError('unsupported operand type for /: Permutation');
  }

  /** Not defined for permutations (TypeError, as in SymPy). */
  override neg(): Expr {
    throw new TypeError('bad operand type for unary -: Permutation');
  }

  /**
   * SymPy Permutation.rmul(a, b, c, ...): the permutation whose ith value is
   * a(b(c(i))); items after the first may be array or cyclic forms.
   */
  static rmul(first: Permutation, ...rest: PermutationInput[]): Permutation {
    let rv = first;
    for (const r of rest) rv = new Permutation(r).mul(rv);
    return rv;
  }

  /** SymPy Permutation.rmul_with_af(*args): rmul of Permutations through their array forms. */
  static rmulWithAf(...args: Permutation[]): Permutation {
    return afNew(afRmuln(...args.map((p) => p.#af)));
  }

  /** SymPy mul_inv(other): other*~self. */
  mulInv(other: Permutation): Permutation {
    return afNew(afRmul(afInvert(this.#af), other.#af));
  }

  /** SymPy commutes_with(other): whether p*other == other*p. */
  commutesWith(other: Permutation): boolean {
    return afCommutesWith(this.#af, other.#af);
  }

  /** SymPy commutator(x): ~x*~p*x*p (sizes must agree). */
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

  /** SymPy p(i): the image of the index i. */
  call(i: number | bigint): number;
  /** SymPy p(seq): the items of seq rearranged, [seq[p(0)], seq[p(1)], ...]. */
  call<T>(seq: readonly T[]): T[];
  /** SymPy p(seq) for a string: the rearranged characters. */
  call(seq: string): string[];
  /** SymPy p(a, b, ...): p followed by the cycle (a b ...), i.e. p*Permutation(a, b, ..., size=p.size). */
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
   * SymPy apply(i): the image of an integer i as an Integer, or an
   * unevaluated AppliedPermutation for a symbolic i.
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

  // ---- properties ----------------------------------------------------------------

  /** SymPy cardinality: size! as a bigint. */
  get cardinality(): bigint {
    return ifac(this.size);
  }

  /** SymPy parity(): 0 for an even permutation, 1 for an odd one. */
  parity(): number {
    return afParity(this.#af);
  }

  /** SymPy is_even. */
  get isEven(): boolean {
    return !this.isOdd;
  }

  /** SymPy is_odd. */
  get isOdd(): boolean {
    return this.parity() % 2 === 1;
  }

  /** SymPy is_Singleton: the size is 1. */
  get isSingleton(): boolean {
    return this.size === 1;
  }

  /** SymPy is_Empty: the size is 0. */
  get isEmpty(): boolean {
    return this.size === 0;
  }

  /** SymPy is_Identity (and is_identity): no element is moved. */
  get isIdentity(): boolean {
    return this.#af.every((v, i) => v === i);
  }

  /** SymPy signature(): 1 for an even permutation, -1 for an odd one. */
  signature(): number {
    return this.isEven ? 1 : -1;
  }

  /** SymPy order(): the smallest positive n with p**n the identity, as an Integer. */
  order(): Rational {
    let l = 1n;
    for (const c of this.cyclicForm) {
      const k = BigInt(c.length);
      l = (l * k) / bgcd(l, k);
    }
    return Rational.of(l);
  }

  /** SymPy length(): the number of moved elements. */
  length(): number {
    return this.support().length;
  }

  /** SymPy ascents(): the positions i with p[i] < p[i+1]. */
  ascents(): number[] {
    const a = this.#af;
    const out: number[] = [];
    for (let i = 0; i < a.length - 1; i++) if (at(a, i) < at(a, i + 1)) out.push(i);
    return out;
  }

  /** SymPy descents(): the positions i with p[i] > p[i+1]. */
  descents(): number[] {
    const a = this.#af;
    const out: number[] = [];
    for (let i = 0; i < a.length - 1; i++) if (at(a, i) > at(a, i + 1)) out.push(i);
    return out;
  }

  /** SymPy max(): the largest element moved (0 for the empty permutation; RangeError when none moves). */
  max(): number {
    const a = this.#af;
    if (a.length === 0) return 0;
    const moved = a.filter((v, i) => v !== i);
    if (moved.length === 0) throw new RangeError('max() iterable argument is empty');
    return Math.max(...moved);
  }

  /** SymPy min(): the smallest element moved (0 for the empty permutation; RangeError when none moves). */
  min(): number {
    const a = this.#af;
    if (a.length === 0) return 0;
    const moved = a.filter((v, i) => v !== i);
    if (moved.length === 0) throw new RangeError('min() iterable argument is empty');
    return Math.min(...moved);
  }

  /** SymPy inversions(): the number of pairs i < j with p[i] > p[j]. */
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

  /** SymPy inversion_vector(): the Lehmer code without its last (always 0) entry. */
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

  /** SymPy index(): the sum of the positions j with p[j] > p[j+1]. */
  index(): number {
    return this.descents().reduce((s, j) => s + j, 0);
  }

  /** SymPy runs(): the maximal ascending runs of the array form. */
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

  /** SymPy transpositions(): the permutation as a product of transpositions. */
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
   * SymPy resize(n): the same permutation on n elements; RangeError when a
   * cycle would be broken.
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

  /** SymPy rank(): the lexicographic rank (the identity has rank 0). */
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

  /** SymPy Permutation.unrank_lex(size, rank): the permutation of the given lexicographic rank. */
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

  /** SymPy next_lex(): the next permutation in lexicographic order, NoMatch after the last one. */
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

  /** SymPy Permutation.unrank_nonlex(n, r): Myrvold-Ruskey unranking (r is taken modulo n!). */
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

  /** SymPy rank_nonlex(inv_perm=None): the Myrvold-Ruskey rank. */
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

  /** SymPy next_nonlex(): the next permutation in Myrvold-Ruskey order, NoMatch after the last one. */
  nextNonlex(): Permutation | NoMatchResult {
    const r = this.rankNonlex();
    if (r === this.cardinality - 1n) return NoMatch;
    return Permutation.unrankNonlex(this.size, r + 1n);
  }

  /** SymPy rank_trotterjohnson(): the rank in Trotter-Johnson (minimal change) order. */
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

  /** SymPy Permutation.unrank_trotterjohnson(size, rank), for 0 <= rank < size!. */
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

  /** SymPy next_trotterjohnson(): the next permutation in Trotter-Johnson order, NoMatch after the last one. */
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

  /** SymPy get_precedence_matrix(): m[i, j] = 1 when i precedes j in the array form. */
  getPrecedenceMatrix(): Matrix {
    return Matrix.of(this.#precedence());
  }

  /** SymPy get_precedence_distance(other). */
  getPrecedenceDistance(other: Permutation): number {
    if (this.size !== other.size) throw new RangeError('The permutations must be of equal size.');
    const a = this.#precedence();
    const b = other.#precedence();
    const n = this.size;
    let nPrec = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j && at(at(a, i), j) * at(at(b, i), j) === 1) nPrec++;
    return Math.floor((n * Math.max(n - 1, 0)) / 2) - nPrec;
  }

  /** SymPy get_adjacency_matrix(): m[i, j] = 1 when j immediately follows i in the array form. */
  getAdjacencyMatrix(): Matrix {
    return Matrix.of(this.#adjacency());
  }

  /** SymPy get_adjacency_distance(other). */
  getAdjacencyDistance(other: Permutation): number {
    if (this.size !== other.size) throw new RangeError('The permutations must be of the same size.');
    const a = this.#adjacency();
    const b = other.#adjacency();
    const n = this.size;
    let nAdj = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j && at(at(a, i), j) * at(at(b, i), j) === 1) nAdj++;
    return n - nAdj - 1;
  }

  /** SymPy get_positional_distance(other): the sum of |p[i] - q[i]|. */
  getPositionalDistance(other: Permutation): number {
    const a = this.#af;
    const b = other.#af;
    if (a.length !== b.length) throw new RangeError('The permutations must be of the same size.');
    return a.reduce((s, ai, i) => s + Math.abs(ai - at(b, i)), 0);
  }

  // ---- constructors --------------------------------------------------------------------

  /**
   * SymPy Permutation.josephus(m, n, s=1): range(n) in the order in which
   * every mth item is selected, the last s items taken in order.
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

  /** SymPy Permutation.from_inversion_vector(inversion). */
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
   * SymPy Permutation.from_sequence(i, key=None): the permutation that
   * arranges the sorted elements of i into i (a stable sort, ties by position).
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
   * SymPy Permutation.random(n): a uniformly random permutation of size n
   * (Fisher-Yates), from Math.random, a seed or a given generator.
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

/** SymPy Perm: an alias of Permutation. */
export const Perm = Permutation;

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

/**
 * SymPy sstr(p, perm_cyclic=...): `(1 2)`, `(3)(0 1)` and `()` in cyclic
 * notation (the default), `Permutation([1, 0, 2, 3])` or
 * `Permutation([1, 0], size=20)` in array notation.
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

/** SymPy srepr(p) / repr(p): `Permutation(1, 2)`, `Permutation(3)(0, 1)`, `Permutation()`. */
export function permutationRepr(p: Permutation, opts: PermutationPrintOptions = {}): string {
  if (!(opts.permCyclic ?? true)) return permutationStr(p, opts);
  if (p.size === 0) return 'Permutation()';
  return `Permutation${cyclicBody(p, ', ')}`;
}

/**
 * SymPy latex(p, perm_cyclic=...): `\left( 1\; 2\right)` in cyclic notation
 * (the default) or a two-line pmatrix in array notation.
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
 * SymPy AppliedPermutation(perm, x): a permutation applied to a symbolic
 * integer; it evaluates once x becomes an Integer (for example by subs).
 */
export class AppliedPermutation extends ExtensionExpr {
  /** @internal use AppliedPermutation.of or Permutation.apply */
  constructor(perm: Permutation, x: Expr) {
    super('AppliedPermutation', [perm, x]);
  }

  /** SymPy AppliedPermutation(perm, x, evaluate): evaluates to an Integer when x is one (unless evaluate is false). */
  static of(perm: Permutation, x: ExprLike, opts: { evaluate?: boolean } = {}): Expr {
    const e = sympify(x);
    if ((opts.evaluate ?? true) && e instanceof Rational && e.q === 1n) return perm.apply(e);
    return new AppliedPermutation(perm, e);
  }

  /** The permutation. */
  get perm(): Permutation {
    return cast(this.args[0], Permutation, 'AppliedPermutation perm');
  }

  /** The argument. */
  get x(): Expr {
    return at(this.args, 1);
  }

  /** Rebuilds the node, evaluating it when the argument is an Integer. */
  withArgs(args: readonly Expr[]): Expr {
    const [perm, x] = args;
    if (!(perm instanceof Permutation) || x === undefined) throw new TypeError('AppliedPermutation needs a Permutation and an argument');
    return AppliedPermutation.of(perm, x);
  }

  /** SymPy latex: \sigma_{perm}(x). */
  override printLatex(print: (e: Expr) => string): string {
    return `\\sigma_{${print(this.perm)}}(${print(this.x)})`;
  }
}
